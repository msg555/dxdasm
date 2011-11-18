#include <dxcut/cc.h>

#include <algorithm>
#include <vector>
#include <map>

#include <stdlib.h>
#include <stdio.h>
#include <string.h>

#include "dasmcl.h"

using namespace std;
using namespace dxcut;

map<string, int> mnemonicMp;

static void computeMnemonicMap() {
  for(int i = 0; i < sizeof(dex_opcode_formats) / sizeof(DexOpFormat); i++) {
    if(dex_opcode_formats[i].name) {
      mnemonicMp[dex_opcode_formats[i].name] = i;
    }
  }
}

DexValue* getParameter(DexAnnotation* annon, const char* name) {
  for(DexNameValuePair* param = annon->parameters;
      !dxc_is_sentinel_parameter(param); param++) {
    if(!strcmp(name, param->name->s)) {
      return &param->value;
    }
  }
  return NULL;
}

string strip(const string& s) {
  int a = 0;
  int b = s.size();
  while(a < b && isspace(s[a])) a++;
  while(a < b && isspace(s[b - 1])) b--;
  return s.substr(a, b - a);
}

DexCode* reassemble_code(DexClass* cl, DexMethod* method, DexAnnotation* annon,
    map<string, ref_method> method_map, map<string, ref_field> field_map) {
  DexCode* code = (DexCode*)calloc(1, sizeof(DexCode));
  code->registers_size = getParameter(annon, "registers")->value.val_int;
  code->outs_size = getParameter(annon, "outsSize")->value.val_int;

  // TODO: Could try and save debug information.
  code->debug_information = NULL;

  vector<DexAnnotation*> packedSwitchVals;
  vector<DexAnnotation*> sparseSwitchVals;
  vector<DexAnnotation*> dataVals;
  vector<DexAnnotation*> tryBlocks;
  for(DexValue* val = getParameter(annon, "packedSwitches")->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    packedSwitchVals.push_back(val->value.val_annotation);
  }
  for(DexValue* val = getParameter(annon, "sparseSwitches")->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    sparseSwitchVals.push_back(val->value.val_annotation);
  }
  for(DexValue* val = getParameter(annon, "dataArrays")->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    dataVals.push_back(val->value.val_annotation);
  }
  for(DexValue* val = getParameter(annon, "tryBlocks")->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    tryBlocks.push_back(val->value.val_annotation);
  }

  // Pass 1: Just figure out the opcodes and labels so we can do layout.
  int pos = 0;
  map<string, int> insnLayout;
  map<int, int> addrInsnLayout;
  vector<int> insnAddr;
  vector<string> strInsns;
  vector<DexInstruction> insns;
  DexValue* valInsns = getParameter(annon, "insns")->value.val_array;
  for(DexValue* val = valInsns; !dxc_is_sentinel_value(val); ++val) {
    DexInstruction in;
    memset(&in, 0, sizeof(in));
    string sin = val->value.val_str->s;

    // Find and strip label if present.
    int colonPos = sin.find(':');
    int atPos = sin.find('@');
    if(colonPos != -1 && (atPos == -1 || colonPos < atPos)) {
      insnLayout[strip(sin.substr(0, colonPos))] = pos;
      while(colonPos + 1 < sin.size() && isspace(sin[colonPos + 1])) colonPos++;
      sin = sin.substr(colonPos + 1);
    }
    addrInsnLayout[pos] = val - valInsns;
    insnAddr.push_back(pos);

    // Find and map mnemonic to opcode.
    int spacePos = 0;
    while(spacePos < sin.size() && !isspace(sin[spacePos])) spacePos++;
    string mnemonic = sin.substr(0, spacePos);
    while(spacePos < sin.size() && isspace(sin[spacePos])) spacePos++;
    sin = sin.substr(spacePos);

    if(mnemonicMp.find(mnemonic) == mnemonicMp.end()) {
      fprintf(stderr, "%s.%s:%d Unknown mnemonic %s\n", cl->name->s,
              method->name->s, val - valInsns, mnemonic.c_str());
      exit(1);
    }
    in.opcode = mnemonicMp[mnemonic];
    pos += dxc_insn_width(&in);
    strInsns.push_back(sin);
    insns.push_back(in);
  }

  int curPos = 0;
  for(int i = 0; i < strInsns.size(); i++) {
    string& sin = strInsns[i];
    bool isRange = *dex_opcode_formats[insns[i].opcode].format_id == 'r';
    bool isVariable = *dex_opcode_formats[insns[i].opcode].format_id == '5';

    // Parse in the registers.
    for(int j = 0; ((isVariable || isRange) && !sin.empty() && sin[0] == 'v') ||
                   j < dxc_num_registers(&insns[i]); j++) {
      dxc_set_num_registers(&insns[i], j + 1);

      int spacePos = 0;
      while(spacePos < sin.size() && !isspace(sin[spacePos])) spacePos++;
      string sreg = sin.substr(0, spacePos);
      while(spacePos < sin.size() && isspace(sin[spacePos])) spacePos++;
      sin = sin.substr(spacePos);

      bool ok = sreg.size() > 1 && sreg[0] == 'v';
      int reg = 0;
      for(int k = 1; ok && k < sreg.size(); k++) {
        char ch = sreg[k];
        reg *= 16;
        if('0' <= ch && ch <= '9') reg += ch - '0';
        else if('a' <= ch && ch <= 'f') reg += 10 + ch - 'a';
        else if('A' <= ch && ch <= 'F') reg += 10 + ch - 'A';
        else ok = false;
      }
      if(!ok) {
        fprintf(stderr, "%s.%s:%d Failed to find register %d\n", cl->name->s,
                method->name->s, i, j);
        exit(1);
      }
      if(isRange && j != 0) {
        if(reg != dxc_get_register(&insns[i], 0) + j) {
          fprintf(stderr, "%s.%s:%d Range registers must be consecutive\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
      } else if(dxc_set_register(&insns[i], j, reg) == -1) {
        fprintf(stderr, "%s.%s:%d Couldn't encode register v%X in slot %d\n",
                cl->name->s, method->name->s, i, reg, j);
        exit(1);
      }
    }

    // Handler special types.
    switch(dex_opcode_formats[insns[i].opcode].specialType) {
      case SPECIAL_CONSTANT: {
        unsigned long long x = 0;
        bool ok = sin.size() > 1 && sin[0] == '#';
        bool neg = ok && sin[1] == '-' && sin.size() > 2;
        for(int j = neg ? 2 : 1; ok && j < sin.size(); j++) {
          x *= 10;
          if('0' <= sin[j] && sin[j] <= '9') x += sin[j] - '0';
          else ok = false;
        }
        if(!ok) {
          fprintf(stderr, "%s.%s:%d Expected numeric literal\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
        insns[i].special.constant = neg ? -x : x;
      } break;
      case SPECIAL_TARGET: {
        if(insns[i].opcode == OP_FILL_ARRAY_DATA) {
          if(sin.size() < 6 || sin.substr(0, 5) != "data@") {
            fprintf(stderr, "%s.%s:%d Expected data\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          int x = 0;
          bool ok = true;
          for(int j = 5; j < sin.size(); j++) {
            x *= 10;
            if('0' <= sin[j] && sin[j] <= '9') x += sin[j] - '0';
            else ok = false;
          }
          if(!ok || x < 0 || x >= dataVals.size()) {
            fprintf(stderr, "%s.%s:%d Expected data\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          vector<dx_ulong> data;
          for(DexValue* val =
              getParameter(dataVals[x], "data")->value.val_array;
              !dxc_is_sentinel_value(val); ++val) {
            data.push_back(val->value.val_long);
          }
          DexInstruction tin;
          tin.opcode = OP_PSUEDO;
          tin.hi_byte = PSUEDO_OP_FILL_DATA_ARRAY;
          int elementWidth = tin.special.fill_data_array.element_width =
              getParameter(dataVals[x], "elementWidth")->value.val_int;
          tin.special.fill_data_array.size = data.size();
          dx_ubyte* arr = tin.special.fill_data_array.data = (dx_ubyte*)
              malloc(elementWidth * data.size());
          for(int j = 0; j < data.size(); j++) {
            switch(elementWidth) {
              case 1: *arr = (dx_ubyte)data[j]; break;
              case 2: *(dx_ushort*)arr = (dx_ushort)data[j]; break;
              case 4: *(dx_uint*)arr = (dx_uint)data[j]; break;
              case 8: *(dx_ulong*)arr = (dx_ulong)data[j]; break;
            }
            arr += elementWidth;
          }
          insns.push_back(tin);
          insns[i].special.target = pos - curPos;
          pos += dxc_insn_width(&tin);
        } else if(insns[i].opcode == OP_PACKED_SWITCH) {
          if(sin.size() < 8 || sin.substr(0, 7) != "packed@") {
            fprintf(stderr, "%s.%s:%d Expected packed\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          int x = 0;
          bool ok = true;
          for(int j = 7; j < sin.size(); j++) {
            x *= 10;
            if('0' <= sin[j] && sin[j] <= '9') x += sin[j] - '0';
            else ok = false;
          }
          if(!ok || x < 0 || x >= packedSwitchVals.size()) {
            fprintf(stderr, "%s.%s:%d Expected packed\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          vector<string> targets;
          for(DexValue* val =
              getParameter(packedSwitchVals[x], "targets")->value.val_array;
              !dxc_is_sentinel_value(val); ++val) {
            targets.push_back(val->value.val_str->s);
          }
          DexInstruction tin;
          tin.opcode = OP_PSUEDO;
          tin.hi_byte = PSUEDO_OP_PACKED_SWITCH;
          tin.special.packed_switch.size = targets.size();
          tin.special.packed_switch.first_key =
              getParameter(packedSwitchVals[x], "firstKey")->value.val_int;
          tin.special.packed_switch.targets =
              (dx_int*)malloc(targets.size() * sizeof(dx_int));
          for(int j = 0; j < targets.size(); j++) {
            typeof(insnLayout.begin()) it = insnLayout.find(targets[j]);
            if(it == insnLayout.end()) {
              fprintf(stderr, "%s.%s:%d Couldn't find label %s\n",
                      cl->name->s, method->name->s, i, targets[j].c_str());
              exit(1);
            }
            tin.special.packed_switch.targets[j] = it->second - curPos;
          }
          insns.push_back(tin);
          insns[i].special.target = pos - curPos;
          pos += dxc_insn_width(&tin);
        } else if(insns[i].opcode == OP_SPARSE_SWITCH) {
          if(sin.size() < 8 || sin.substr(0, 7) != "sparse@") {
            fprintf(stderr, "%s.%s:%d Expected sparse\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          int x = 0;
          bool ok = true;
          for(int j = 7; j < sin.size(); j++) {
            x *= 10;
            if('0' <= sin[j] && sin[j] <= '9') x += sin[j] - '0';
            else ok = false;
          }
          if(!ok || x < 0 || x >= sparseSwitchVals.size()) {
            fprintf(stderr, "%s.%s:%d Expected sparse\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          vector<int> keys;
          vector<string> targets;
          for(DexValue* val =
              getParameter(sparseSwitchVals[x], "keys")->value.val_array;
              !dxc_is_sentinel_value(val); ++val) {
            keys.push_back(val->value.val_int);
          }
          for(DexValue* val =
              getParameter(sparseSwitchVals[x], "targets")->value.val_array;
              !dxc_is_sentinel_value(val); ++val) {
            targets.push_back(val->value.val_str->s);
          }
          if(keys.size() != targets.size()) {
            fprintf(stderr, "%s.%s:%d Keys and targets of different length\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          DexInstruction tin;
          tin.opcode = OP_PSUEDO;
          tin.hi_byte = PSUEDO_OP_SPARSE_SWITCH;
          tin.special.sparse_switch.size = keys.size();
          tin.special.sparse_switch.keys =
              (dx_int*)malloc(keys.size() * sizeof(dx_int));
          tin.special.sparse_switch.targets =
              (dx_int*)malloc(targets.size() * sizeof(dx_int));
          for(int j = 0; j < keys.size(); j++) {
            tin.special.sparse_switch.keys[j] = keys[j];
            typeof(insnLayout.begin()) it = insnLayout.find(targets[j]);
            if(it == insnLayout.end()) {
              fprintf(stderr, "%s.%s:%d Couldn't find label %s\n",
                      cl->name->s, method->name->s, i, targets[j].c_str());
              exit(1);
            }
            tin.special.sparse_switch.targets[j] = it->second - curPos;
          }
          insns.push_back(tin);
          insns[i].special.target = pos - curPos;
          pos += dxc_insn_width(&tin);
        } else {
          if(sin.size() < 5 || sin.substr(0, 5) != "insn@") {
            fprintf(stderr, "%s.%s:%d Expected label\n",
                    cl->name->s, method->name->s, i);
            exit(1);
          }
          typeof(insnLayout.begin()) it = insnLayout.find(sin.substr(5));
          if(it == insnLayout.end()) {
            fprintf(stderr, "%s.%s:%d Couldn't find label %s\n",
                    cl->name->s, method->name->s, i, sin.substr(5).c_str());
            exit(1);
          }
          insns[i].special.target = it->second - curPos;
        }
      } break;
      case SPECIAL_STRING: {
        if(sin.size() < 7 || sin.substr(0, 7) != "string@") {
          fprintf(stderr, "%s.%s:%d Expected string literal\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
        insns[i].special.str = dxc_induct_str(sin.substr(7).c_str());
      } break;
      case SPECIAL_TYPE: {
        if(sin.size() < 5 || sin.substr(0, 5) != "type@") {
          fprintf(stderr, "%s.%s:%d Expected type literal\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
        insns[i].special.type =
            dxc_induct_str(dxc_type_name(sin.substr(5).c_str()));
      } break;
      case SPECIAL_FIELD: {
        if(sin.size() < 6 || sin.substr(0, 6) != "field@") {
          fprintf(stderr, "%s.%s:%d Expected field\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
        typeof(field_map.begin()) it = field_map.find(sin.substr(6));
        if(it == field_map.end()) {
          fprintf(stderr, "%s.%s:%d Couldn't find field alias %s\n",
                  cl->name->s, method->name->s, i, sin.substr(6).c_str());
          exit(1);
        }
        insns[i].special.field.defining_class =
            dxc_copy_str(it->second.defining_class);
        insns[i].special.field.name = dxc_copy_str(it->second.name);
        insns[i].special.field.type = dxc_copy_str(it->second.type);
      } break;
      case SPECIAL_METHOD: {
        if(sin.size() < 7 || sin.substr(0, 7) != "method@") {
          fprintf(stderr, "%s.%s:%d Expected method\n",
                  cl->name->s, method->name->s, i);
          exit(1);
        }
        typeof(method_map.begin()) it = method_map.find(sin.substr(7));
        if(it == method_map.end()) {
          fprintf(stderr, "%s.%s:%d Couldn't find method alias %s\n",
                  cl->name->s, method->name->s, i, sin.substr(7).c_str());
          exit(1);
        }
        insns[i].special.method.defining_class =
            dxc_copy_str(it->second.defining_class);
        insns[i].special.method.name = dxc_copy_str(it->second.name);
        insns[i].special.method.prototype =
            dxc_copy_strstr(it->second.prototype);
      } break;
    }
    curPos += dxc_insn_width(&insns[i]);
  }
  code->insns_count = insns.size();
  code->insns = (DexInstruction*)malloc(insns.size() * sizeof(DexInstruction));
  memcpy(code->insns, &insns[0], insns.size() * sizeof(DexInstruction));

  code->tries = (DexTryBlock*)calloc(tryBlocks.size() + 1, sizeof(DexTryBlock));
  for(int i = 0; i < tryBlocks.size(); i++) {
    DexAnnotation* tannon = tryBlocks[i];
    DexTryBlock* tryb = code->tries + i;
    string startInsn = getParameter(tannon, "startInsn")->value.val_str->s;
    typeof(insnLayout.begin()) it = insnLayout.find(startInsn);
    if(it == insnLayout.end()) {
      fprintf(stderr, "%s.%s:try:%d Couldn't find label %s\n",
              cl->name->s, method->name->s, i, startInsn.c_str());
      exit(1);
    }
    tryb->start_addr = it->second;

    int insnLength = getParameter(tannon, "insnLength")->value.val_int;
    if(insnLength <= 0) {
      fprintf(stderr, "%s.%s:try:%d Expected positive insnLength\n",
              cl->name->s, method->name->s, i);
      exit(1);
    }
    int lastIn = addrInsnLayout[tryb->start_addr] + insnLength - 1;
    tryb->insn_count = insnAddr[lastIn] + dxc_insn_width(&insns[lastIn]) -
                       tryb->start_addr;

    vector<DexAnnotation*> handlerVals;
    for(DexValue* val = getParameter(tannon, "handlers")->value.val_array;
        !dxc_is_sentinel_value(val); ++val) {
      handlerVals.push_back(val->value.val_annotation);
    }
    tryb->handlers = (DexHandler*)malloc(sizeof(DexHandler) *
                                         (handlerVals.size() + 1));
    for(int j = 0; j < handlerVals.size(); j++) {
      tryb->handlers[j].type = dxc_copy_str(
          getParameter(handlerVals[j], "catchType")->value.val_type);
      string target = getParameter(handlerVals[j], "target")->value.val_str->s;
      it = insnLayout.find(target);
      if(it == insnLayout.end()) {
        fprintf(stderr, "%s.%s:try:%d;handler:%d Couldn't find label %s\n",
                cl->name->s, method->name->s, i, j, target.c_str());
        exit(1);
      }
      tryb->handlers[j].addr = it->second;
    }
    dxc_make_sentinel_handler(tryb->handlers + handlerVals.size());

    string catchAllTarget =
        getParameter(tannon, "catchAllTarget")->value.val_str->s;
    if(!catchAllTarget.empty()) {
      it = insnLayout.find(catchAllTarget);
      if(it == insnLayout.end()) {
        fprintf(stderr, "%s.%s:try:%d Couldn't find label %s\n",
                cl->name->s, method->name->s, i, catchAllTarget.c_str());
        exit(1);
      }
      tryb->catch_all_handler = (DexHandler*)malloc(sizeof(DexHandler));
      tryb->catch_all_handler->type = NULL;
      tryb->catch_all_handler->addr = it->second;
    } else {
      tryb->catch_all_handler = NULL;
    }
  }
  dxc_make_sentinel_try_block(code->tries + tryBlocks.size());
  
  return code;
}

map<string, ref_method> build_method_alias_map(DexValue* valArray) {
  map<string, ref_method> ret;
  if(valArray)
  for(DexValue* val = valArray->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    DexValue* valAlias = getParameter(val->value.val_annotation, "alias");
    DexValue* valClazz = getParameter(val->value.val_annotation, "clazz");
    DexValue* valName = getParameter(val->value.val_annotation, "name");
    DexValue* valPrototype = getParameter(val->value.val_annotation,
                                          "prototype");

    string alias = valAlias->value.val_str->s;
    string clazz = valClazz->value.val_type->s;
    string name = valName->value.val_str->s;
    vector<string> prototype;
    for(DexValue* proto = valPrototype->value.val_array;
        !dxc_is_sentinel_value(proto); ++proto) {
      prototype.push_back(proto->value.val_type->s);
    }

    ref_method mtd;
    mtd.name = dxc_induct_str(name.c_str());
    mtd.defining_class = dxc_induct_str(clazz.c_str());
    mtd.prototype = dxc_create_strstr(prototype.size());
    for(int i = 0; i < prototype.size(); i++) {
      mtd.prototype->s[i] = dxc_induct_str(prototype[i].c_str());
    }
    ret[alias] = mtd;
  }
  return ret;
}

map<string, ref_field> build_field_alias_map(DexValue* valArray) {
  map<string, ref_field> ret;
  if(valArray)
  for(DexValue* val = valArray->value.val_array;
      !dxc_is_sentinel_value(val); ++val) {
    DexValue* valAlias = getParameter(val->value.val_annotation, "alias");
    DexValue* valClazz = getParameter(val->value.val_annotation, "clazz");
    DexValue* valName = getParameter(val->value.val_annotation, "name");
    DexValue* valType = getParameter(val->value.val_annotation, "type");

    string alias = valAlias->value.val_str->s;
    string clazz = valClazz->value.val_type->s;
    string name = valName->value.val_str->s;
    string type = valType->value.val_type->s;

    ref_field fld;
    fld.name = dxc_induct_str(name.c_str());
    fld.defining_class = dxc_induct_str(clazz.c_str());
    fld.type = dxc_induct_str(type.c_str());
    ret[alias] = fld;
  }
  return ret;
}

static void removeAnnotationAndDelete(DexAnnotation* annon) {
  dxc_free_annotation(annon);
  for(; !dxc_is_sentinel_annotation(annon); annon++) {
    *annon = annon[1];
  }
  dxc_make_sentinel_annotation(--annon);
}

void reassemble_class(DexClass* cl) {
  map<string, ref_method> method_alias_map;
  map<string, ref_field> field_alias_map;
  for(DexAnnotation* annon = cl->annotations;
      !dxc_is_sentinel_annotation(annon); ++annon) {
    if(!strcmp("Lorg/dxcut/dxdasm/DxdasmAliases;", annon->type->s)) {
      method_alias_map = build_method_alias_map(
          getParameter(annon, "methodAliases"));
      field_alias_map = build_field_alias_map(
          getParameter(annon, "fieldAliases"));
      removeAnnotationAndDelete(annon--);
    } else if(!strcmp("Lorg/dxcut/dxdasm/DxdasmAccess;", annon->type->s)) {
      cl->access_flags = (DexAccessFlags)
          getParameter(annon, "accessFlags")->value.val_int;
      removeAnnotationAndDelete(annon--);
    }
  }
  for(DexAnnotation* annon = cl->annotations;
      !dxc_is_sentinel_annotation(annon); ++annon) {
    if(!strcmp("Ldalvik/annotation/InnerClass;", annon->type->s)) {
      getParameter(annon, "accessFlags")->value.val_int =
          (dx_uint)cl->access_flags;
    }
  }

  for(int iter = 0; iter < 2; iter++)
  for(DexMethod* mtd = iter ? cl->virtual_methods : cl->direct_methods;
      !dxc_is_sentinel_method(mtd); ++mtd) {
    for(DexAnnotation* annon = mtd->annotations;
        !dxc_is_sentinel_annotation(annon); ++annon) {
      if(!strcmp("Lorg/dxcut/dxdasm/DxdasmMethod;", annon->type->s)) {
        DexCode* old_code = mtd->code_body;
        mtd->code_body = reassemble_code(cl, mtd, annon,
            method_alias_map, field_alias_map);
        mtd->code_body->ins_size = old_code->ins_size;
        dxc_free_code(old_code);
        removeAnnotationAndDelete(annon--);
      } else if(!strcmp("Lorg/dxcut/dxdasm/DxdasmAccess;", annon->type->s)) {
        mtd->access_flags = (DexAccessFlags)
            getParameter(annon, "accessFlags")->value.val_int;
        removeAnnotationAndDelete(annon--);
      }
    }
  }

  for(int iter = 0; iter < 2; iter++)
  for(DexField* fld = iter ? cl->static_fields : cl->instance_fields;
      !dxc_is_sentinel_field(fld); ++fld) {
    for(DexAnnotation* annon = fld->annotations;
        !dxc_is_sentinel_annotation(annon); ++annon) {
      if(!strcmp("Lorg/dxcut/dxdasm/DxdasmAccess;", annon->type->s)) {
        fld->access_flags = (DexAccessFlags)
            getParameter(annon, "accessFlags")->value.val_int;
        removeAnnotationAndDelete(annon--);
      }
    }
  }
}

int main(int argc, char** argv) {
  if(argc != 3) {
    fprintf(stderr, "Usage %s input.dex output.dex\n", *argv);
    return 1;
  }
  computeMnemonicMap();

  FILE* fin = fopen(argv[1], "r");
  DexFile* dx = dxc_read_file(fin);
  fclose(fin);
  if(!dx) {
    fprintf(stderr, "Failed to open dex file\n");
    return 1;
  }

  for(DexClass* cl = dx->classes; !dxc_is_sentinel_class(cl); ++cl) {
    reassemble_class(cl);
  }
  strip_classes(dx);

  FILE* fout = fopen(argv[2], "w");
  dxc_write_file(dx, fout);
  fclose(fout);
  dxc_free_file(dx);
  return 0;
}
