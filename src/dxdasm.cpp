#include <iostream>
#include <algorithm>
#include <vector>
#include <map>
#include <cstdio>
#include <cstring>
#include <errno.h>
#include <sys/stat.h>
#include <sys/types.h>

#include <dxcut/cc.h>

#include "dasmcl.h"
#include "annotations.h"
#include "mutf8.h"
#include "javarules.h"

using namespace std;
using namespace dxcut;

string get_zero_literal(char type) {
  switch(type) {
    case 'Z': return "false";
    case 'B': return "(byte)0";
    case 'C': return "(char)0";
    case 'S': return "(short)0";
    case 'I': return "0";
    case 'F': return "0f";
    case 'J': return "0l";
    case 'D': return "0.0";
    case '[': return "null";
    case 'L': return "null";
  }
  return "";
}

// The string is encoded in mutf8 so we need to actually extract out the code
// points.
string encode_string(const char* s) {
  string ret;
  while(*s) {
    int code_point = mutf8NextCodePoint(&s);
    switch(code_point) {
      case '\t':
        ret += "\\t";
        break;
      case '\r':
        ret += "\\r";
        break;
      case '\n':
        ret += "\\n";
        break;
      case '\v':
        ret += "\\v";
        break;
      case '\"':
        ret += "\\\"";
        break;
      case '\\':
        ret += "\\\\";
        break;
      default:
        if(32 <= code_point && code_point < 128) {
          ret += (char)code_point;
        } else {
          char buf[16];
          sprintf(buf, "\\u%04X", code_point);
          ret += buf;
        }
    }
  }
  return ret;
}

void dump_debug(DexDebugInfo* dbg, int depth) {
  string tabbing = string(depth * 2, ' ');
  dx_uint line = dbg->line_start;
  dx_uint addr = 0;
  map<dx_uint, pair<pair<string, string>, dx_uint> > reg_map;
  for(DexDebugInstruction* insn = dbg->insns;
      insn->opcode != DBG_END_SEQUENCE; insn++) {
    switch(insn->opcode) {
      case DBG_ADVANCE_PC:
        addr += insn->p.addr_diff;
        break;
      case DBG_ADVANCE_LINE:
        line += insn->p.line_diff;
        break;
      case DBG_START_LOCAL:
      case DBG_START_LOCAL_EXTENDED:
        reg_map[insn->p.start_local->register_num] = make_pair(
            make_pair(insn->p.start_local->name->s,
                      insn->p.start_local->type->s), addr);
        break;
      case DBG_END_LOCAL: {
        dx_uint reg = insn->p.register_num;
        printf("%s// %s %s > v%.4X [%.4x, %.4x)\n", tabbing.c_str(),
            reg_map[reg].first.second.empty() ? "unknown" :
            type_brief(reg_map[reg].first.second).c_str(),
            reg_map[reg].first.first.empty() ? "unknown" :
            reg_map[reg].first.first.c_str(), reg, reg_map[reg].second, addr);
        break;
      } case DBG_RESTART_LOCAL:
        reg_map[insn->p.register_num].second = addr;
        break;
      case DBG_SET_PROLOGUE_END:
        break;
      case DBG_SET_EPILOGUE_BEGIN:
        break;
      case DBG_SET_FILE:
        break;
      default:
        line += -4 + (insn->opcode - DBG_FIRST_SPECIAL) % 15;
        addr += (insn->opcode - DBG_FIRST_SPECIAL) / 15;
    }
  }
}

void decompile_dalvik(dasmcl* dcl, DexInstruction* insns, dx_uint count,
                      DexTryBlock* tries, int depth) {
  vector<int> ins_offset;
  vector<DexInstruction*> ins;
  vector<DexInstruction*> tables;
  map<int, int> offset_mp;

  int pos = 0;
  for(int i = 0; i < count; i++) {
    DexInstruction* in = insns + i;
    if(in->opcode == OP_PSUEDO &&
       in->hi_byte != PSUEDO_OP_NOP) {
      offset_mp[pos] = tables.size();
      tables.push_back(in);
    } else {
      offset_mp[pos] = ins.size();
      ins.push_back(in);
      ins_offset.push_back(pos);
    }
    pos += dxc_insn_width(in);
  }
  
  vector<DexInstruction*> fill_data_tables;
  vector<pair<int, DexInstruction*> > sparse_switch_tables;
  vector<pair<int, DexInstruction*> > packed_switch_tables;

  string tabbing = string(depth * 2, ' ');
  printf("%sinsns = {\n", tabbing.c_str());
  for(int i = 0; i < ins.size(); i++) {
    DexInstruction* in = ins[i];
    DexOpFormat fmt = dex_opcode_formats[in->opcode];

    printf("%s  ", tabbing.c_str());
    printf("\"L%02d: %s", i, fmt.name);

    for(int j = 0; j < dxc_num_registers(in); j++) {
      char format[] = " v%.?X";
      format[4] = '0' + dxc_register_width(in, j);
      printf(format, dxc_get_register(in, j));
    }

    switch(fmt.specialType) {
      case SPECIAL_CONSTANT:
        printf(" #%lld", in->special.constant);
        if(in->opcode == OP_CONST_WIDE) {
          double x = 0;
          memcpy(&x, &in->special.constant, 8);
          // printf(" #(double %.11g)", x);
        } else if(in->opcode == OP_CONST_WIDE_HIGH16) {
          double x = 0;
          dx_ulong v = in->special.constant << 48;
          memcpy(&x, &v, 8);
          // printf(" #(double %.11g)", x);
        }
        break;
      case SPECIAL_TARGET:
        if(in->opcode == OP_FILL_ARRAY_DATA) {
          DexInstruction* fill_data_table =
              tables[offset_mp[ins_offset[i] + in->special.target]];
          int ind = find(fill_data_tables.begin(), fill_data_tables.end(),
                         fill_data_table) - fill_data_tables.begin();
          if(ind == fill_data_tables.size()) {
            fill_data_tables.push_back(fill_data_table);
          }
          printf(" data@%d", ind);
        } else if(in->opcode == OP_PACKED_SWITCH) {
          printf(" packed@%d", packed_switch_tables.size());
          packed_switch_tables.push_back(make_pair(ins_offset[i],
              tables[offset_mp[ins_offset[i] + in->special.target]]));
        } else if(in->opcode == OP_SPARSE_SWITCH) {
          printf(" sparse@%d", sparse_switch_tables.size());
          sparse_switch_tables.push_back(make_pair(ins_offset[i],
              tables[offset_mp[ins_offset[i] + in->special.target]]));
        } else {
          printf(" insn@L%02d", offset_mp[ins_offset[i] + in->special.target]);
        }
        break;
      case SPECIAL_STRING: {
        printf(" string@%s", encode_string(in->special.str->s).c_str());
        break;
      } case SPECIAL_TYPE: {
        printf(" type@%s", dxc_type_nice(in->special.type->s));
        break;
      } case SPECIAL_FIELD: {
        printf(" field@%s", dcl->field_alias_map[&in->special.field].c_str());
        break;
      } case SPECIAL_METHOD: {
        printf(" method@%s",
               dcl->method_alias_map[&in->special.method].c_str());
        break;
      }
    }
    printf("\"%s\n", i + 1 < ins.size() ? "," : "");
  }
  
  printf("%s},\n", tabbing.c_str());

  // Output packed switch tables.
  printf("%spackedSwitches = {\n", tabbing.c_str());
  for(int i = 0; i < packed_switch_tables.size(); i++) {
    int off = packed_switch_tables[i].first;
    DexInstruction* in = packed_switch_tables[i].second;
    printf("%s  @%s(\n", tabbing.c_str(),
           get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmPacked;").c_str());
    printf("%s    firstKey = %d,\n", tabbing.c_str(),
           in->special.packed_switch.first_key);
    printf("%s    targets = {\n", tabbing.c_str());
    for(int j = 0; j < in->special.packed_switch.size; j++) {
      printf("%s      \"L%02d\"%s\n", tabbing.c_str(),
             offset_mp[off + in->special.packed_switch.targets[j]],
             j + 1 < in->special.packed_switch.size ? "," : "");
    }
    printf("%s    }\n", tabbing.c_str());
    printf("%s  )%s\n", tabbing.c_str(),
           i + 1 < packed_switch_tables.size() ? "," : "");
  }
  printf("%s},\n", tabbing.c_str());

  // Output sparse switch tables.
  printf("%ssparseSwitches = {\n", tabbing.c_str());
  for(int i = 0; i < sparse_switch_tables.size(); i++) {
    int off = sparse_switch_tables[i].first;
    DexInstruction* in = sparse_switch_tables[i].second;
    printf("%s  @%s(\n", tabbing.c_str(),
           get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmSparse;").c_str());
    printf("%s    keys = {\n", tabbing.c_str());
    for(int j = 0; j < in->special.sparse_switch.size; j++) {
      printf("%s      %d%s\n", tabbing.c_str(),
             in->special.sparse_switch.keys[j],
             j + 1 < in->special.sparse_switch.size ? "," : "");
    }
    printf("%s    },\n", tabbing.c_str());
    printf("%s    targets = {\n", tabbing.c_str());
    for(int j = 0; j < in->special.sparse_switch.size; j++) {
      printf("%s      \"L%02d\"%s\n", tabbing.c_str(),
             offset_mp[off + in->special.sparse_switch.targets[j]],
             j + 1 < in->special.sparse_switch.size ? "," : "");
    }
    printf("%s    }\n", tabbing.c_str());
    printf("%s  )%s\n", tabbing.c_str(),
           i + 1 < sparse_switch_tables.size() ? "," : "");
  }
  printf("%s},\n", tabbing.c_str());

  // Output fill data tables.
  printf("%sdataArrays = {\n", tabbing.c_str());
  for(int i = 0; i < fill_data_tables.size(); i++) {
    DexInstruction* in = fill_data_tables[i];
    printf("%s  @%s(\n", tabbing.c_str(),
           get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmData;").c_str());
    int width = in->special.fill_data_array.element_width;
    printf("%s    elementWidth = %d,\n", tabbing.c_str(), width);
    printf("%s    data = {\n", tabbing.c_str());
    char* array = (char*)in->special.fill_data_array.data;
    for(int j = 0; j < in->special.fill_data_array.size; j++) {
      unsigned long long val = 0;
      switch(width) {
        case 1: val = *(unsigned char*)array; break;
        case 2: val = *(unsigned short*)array; break;
        case 4: val = *(unsigned int*)array; break;
        case 8: val = *(unsigned long long*)array; break;
      }
      array += width;
      printf("%s      0x%llX%s%s\n", tabbing.c_str(), val,
             val > 0xFFFFFFFFU ? "L" : "",
             j + 1 < in->special.fill_data_array.size ? "," : "");
    }
    printf("%s    }\n", tabbing.c_str());
    printf("%s  )%s\n", tabbing.c_str(),
           i + 1 < fill_data_tables.size() ? "," : "");
  }
  printf("%s},\n", tabbing.c_str());

  printf("%stryBlocks = {\n", tabbing.c_str());
  for(DexTryBlock* try_block = tries; !dxc_is_sentinel_try_block(try_block);
      try_block++) {
    int startInsn = offset_mp[try_block->start_addr];
    int endInsn = (--offset_mp.lower_bound(
        try_block->start_addr + try_block->insn_count))->second;

    printf("%s  @%s(\n", tabbing.c_str(),
           get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmTry;").c_str());
    printf("%s    startInsn = \"L%02d\",\n", tabbing.c_str(), startInsn);
    printf("%s    insnLength = %d,\n", tabbing.c_str(),
           endInsn - startInsn + 1);
    printf("%s    handlers = {\n", tabbing.c_str());
    for(DexHandler* hndlr = try_block->handlers;
        !dxc_is_sentinel_handler(hndlr); hndlr++) {
      printf("%s      @%s(\n", tabbing.c_str(),
             get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmHandler;").c_str());
      printf("%s        catchType = %s.class,\n", tabbing.c_str(),
             get_import_name(dcl, hndlr->type->s).c_str());
      printf("%s        target = \"L%02d\"\n", tabbing.c_str(),
             offset_mp[hndlr->addr]);
      printf("%s      )%s\n", tabbing.c_str(),
             dxc_is_sentinel_handler(hndlr + 1) ? "" : ",");
    }
    printf("%s    },\n", tabbing.c_str());
    printf("%s    catchAllTarget = ", tabbing.c_str());
    if(try_block->catch_all_handler) {
      printf("\"L%02d\"\n", offset_mp[try_block->catch_all_handler->addr]);
    } else {
      printf("\"\" // No catch all handler.\n");
    }
    printf("%s  )%s\n", tabbing.c_str(),
           dxc_is_sentinel_try_block(try_block + 1) ? "" : ",");
  }
  printf("%s}\n", tabbing.c_str());
}

string convert_dollars(const string& s) {
  string ret = s;
  for(int i = 0; i < ret.size(); i++) {
    if(ret[i] == '$') {
      ret[i] = '.';
    }
  }
  return ret;
}

void write_alias_table(dasmcl* dcl, dx_uint depth) {
  string tabbing = string(depth * 2, ' ');
  printf("%s@%s(\n", tabbing.c_str(),
         get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmAliases;").c_str());
  printf("%s  methodAliases = {\n", tabbing.c_str());
  for(typeof(dcl->method_alias_map.begin()) it = dcl->method_alias_map.begin();
      it != dcl->method_alias_map.end(); ) {
    printf("%s    @%s(\n", tabbing.c_str(),
          get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmMethodAlias;").c_str());
    printf("%s      alias = \"%s\",\n", tabbing.c_str(), it->second.c_str());
    printf("%s      clazz = %s.class,\n", tabbing.c_str(),
           get_import_name(dcl, it->first->defining_class->s).c_str());
    printf("%s      name = \"%s\",\n", tabbing.c_str(), it->first->name->s);
    printf("%s      prototype = {\n", tabbing.c_str());
    for(ref_str** proto = it->first->prototype->s; *proto; ) {
      printf("%s        %s.class", tabbing.c_str(),
             get_import_name(dcl, (*proto)->s).c_str());
      if(*++proto) printf(",");
      printf("\n");
    }
    printf("%s      }\n", tabbing.c_str());
    printf("%s    )", tabbing.c_str());

    ++it;
    if(it != dcl->method_alias_map.end()) printf(",");
    printf("\n");
  }
  printf("%s  },\n", tabbing.c_str());
  printf("%s  fieldAliases = {\n", tabbing.c_str());
  for(typeof(dcl->field_alias_map.begin()) it = dcl->field_alias_map.begin();
      it != dcl->field_alias_map.end(); ) {
    printf("%s    @%s(\n", tabbing.c_str(),
          get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmFieldAlias;").c_str());
    printf("%s      alias = \"%s\",\n", tabbing.c_str(), it->second.c_str());
    printf("%s      clazz = %s.class,\n", tabbing.c_str(),
           get_import_name(dcl, it->first->defining_class->s).c_str());
    printf("%s      name = \"%s\",\n", tabbing.c_str(), it->first->name->s);
    printf("%s      type = %s.class\n", tabbing.c_str(),
           get_import_name(dcl, it->first->type->s).c_str());
    printf("%s    )", tabbing.c_str());

    ++it;
    if(it != dcl->field_alias_map.end()) printf(",");
    printf("\n");
  }
  printf("%s  }\n", tabbing.c_str());
  printf("%s)\n", tabbing.c_str());
}

void decompile_class(dasmcl* dcl, dx_uint depth) {
  DexClass* cl = dcl->cl;
  string name = dxc_type_nice(cl->name->s);
  string package_name = get_package_name(name);
  string tabbing = string(depth * 2, ' ');
  if(depth == 0 && !package_name.empty()) {
    printf("package %s;\n\n", package_name.c_str());
  }
  if(depth == 0) {
    bool has_imports = false;
    set<string>& imps = dcl->import_table;
    for(set<string>::iterator it = imps.begin(); it != imps.end(); ++it) {
      string import_package = get_package_name(dxc_type_nice(it->c_str()));
/*
      if(import_package == "java.lang" || import_package == package_name) {
        if(is_toplevel_class(it->c_str()) ||
           get_toplevel_class(cl->name->s) == get_toplevel_class(*it)) {
          continue;
        }
      }
*/
      printf("import %s;\n",
             convert_dollars(dxc_type_nice(it->c_str())).c_str());
      has_imports = true;
    }
    if(has_imports) {
      printf("\n");
    }
  }
  write_alias_table(dcl, depth);
  
  DexAccessFlags nflags = cl->access_flags & ACC_INTERFACE ?
      (DexAccessFlags)(cl->access_flags & ~ACC_ABSTRACT) : cl->access_flags;
  // HACK: Sometimes some weird things go on where a class can't access another
  // class' definition.  This is annoying and this is a simple work around.
  // Also it makes hacking around easier in the result.
  nflags = (DexAccessFlags)(nflags | ACC_PUBLIC);
  if(depth != 0) {
    // We need to check if this class is really static.  non-static classes
    // should have a this$0 variable.
    bool has_this0 = false;
/*
    for(DexField* fld = cl->instance_fields; !dxc_is_sentinel_field(fld);
        fld++) {
      if(!strcmp("this$0", fld->name->s)) {
        has_this0 = true;
      }
    }
*/
    if(!has_this0) {
      nflags = (DexAccessFlags)(nflags | ACC_STATIC);
    }
  }
  string flags = dxc_access_flags_nice(nflags);
  if(flags.empty()) {
    printf("%sclass %s ", tabbing.c_str(), type_brief(cl->name->s).c_str());
  } else {
    printf("%s%s %s%s ", tabbing.c_str(), flags.c_str(),
           cl->access_flags & ACC_INTERFACE ? "" : "class ",
           type_brief(cl->name->s).c_str());
  }
  if(cl->super_class && strcmp("Ljava/lang/Object;", cl->super_class->s)) {
    printf("extends %s ", type_brief(cl->super_class->s).c_str());
  }
  if(cl->interfaces->s[0]) {
    ref_str** str;
    printf(cl->access_flags & ACC_INTERFACE ? "extends " : "implements ");
    for(str = cl->interfaces->s; *str; ++str) {
      if(str != cl->interfaces->s) printf(", ");
      printf("%s", get_import_name(dcl, (*str)->s).c_str());
      //printf("%s", dxc_type_nice((*str)->s));
    }
    printf(" ");
  }
  printf("{\n");

  int feedLine = 0;
  for(int iter = 0; iter < 2; iter++) {
    if(feedLine) printf("\n");
    feedLine = 0;
    DexValue* svalue = iter ? NULL : cl->static_values;
    for(DexField* fld = iter ? cl->instance_fields : cl->static_fields;
        !dxc_is_sentinel_field(fld); fld++,
        svalue = svalue ? svalue + 1 : NULL) {
      if(svalue && dxc_is_sentinel_value(svalue)) svalue = NULL;
      DexAccessFlags nflags = fld->access_flags;

/*
      if((fld->access_flags & ACC_SYNTHETIC) ||
         (fld->access_flags & ACC_STATIC)) {
        nflags = (DexAccessFlags)(nflags & ~ACC_STATIC);
        printf("%s  @%s(\n", tabbing.c_str(),
            get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmSynthetic;").c_str());
        printf("%s    access_flags = 0x%08X\n", tabbing.c_str(),
               fld->access_flags);
        printf("%s  )\n", tabbing.c_str());
      }
*/

      feedLine = 1;
      flags = dxc_access_flags_nice(nflags);
      if(flags.empty()) {
        printf("%s  %s %s", tabbing.c_str(),
               get_import_name(dcl, fld->type->s).c_str(), fld->name->s);
      } else {
        printf("%s  %s %s %s", tabbing.c_str(), flags.c_str(),
               get_import_name(dcl, fld->type->s).c_str(), fld->name->s);
      }
      if(svalue) {
        if(svalue->type == VALUE_STRING) {
          printf(" = \"%s\";\n",
                 encode_string(svalue->value.val_str->s).c_str());
        } else {
          printf(" = %s;\n", dxc_value_nice(svalue));
        }
        fld->access_flags = (DexAccessFlags)(fld->access_flags | ACC_UNUSED);
      } else {
        printf(";\n");
      }
    }
  }

  for(int iter = 0; iter < 2; iter++)
  for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
      !dxc_is_sentinel_method(mtd); mtd++) {
    if(feedLine) printf("\n");
    feedLine = 1;

    if(mtd->code_body) {
      DexCode& code = *mtd->code_body;
      printf("%s  @%s(\n", tabbing.c_str(),
             get_import_name(dcl, "Lorg/dxcut/dxdasm/DxdasmMethod;").c_str());
      printf("%s    registers = %d,\n", tabbing.c_str(), code.registers_size);
      printf("%s    outsSize = %d,\n", tabbing.c_str(), code.outs_size);
      decompile_dalvik(dcl, mtd->code_body->insns, mtd->code_body->insns_count,
                       mtd->code_body->tries, depth + 2);
      printf("%s  )\n", tabbing.c_str());
    }

    string throwsString;
    vector<string> throwTypes;
    for(DexAnnotation* annon = mtd->annotations;
        !dxc_is_sentinel_annotation(annon); annon++) {
      if(!strcmp("Ldalvik/annotation/Throws;", annon->type->s)) {
        for(DexValue* val = annon->parameters->value.value.val_array;
            !dxc_is_sentinel_value(val); ++val) {
          if(throwsString.empty()) throwsString = " throws ";
          else throwsString += ", ";
          string type = get_import_name(dcl, val->value.val_type->s);
          throwsString += type;
          throwTypes.push_back(type);
        }
      }
    }

    bool isclinit = false;
    flags = dxc_access_flags_nice(
        (DexAccessFlags)(mtd->access_flags & ~(ACC_BRIDGE | ACC_VARARGS)));
    if(mtd->access_flags & ACC_CONSTRUCTOR) {
      if(mtd->access_flags & ACC_STATIC) {
        isclinit = true;
        printf("%s  static void dxdasm_static(", tabbing.c_str());
      } else if(flags.empty()) {
        printf("%s  %s(", tabbing.c_str(),
               type_brief(cl->name->s).c_str());
      } else {
        printf("%s  %s %s(", tabbing.c_str(), flags.c_str(),
               get_import_name(dcl, cl->name->s).c_str());
      }
    } else if(flags.empty()) {
      printf("%s  %s %s(", tabbing.c_str(),
             type_brief(mtd->prototype->s[0]->s).c_str(), mtd->name->s);
    } else {
      printf("%s  %s %s %s(", tabbing.c_str(), flags.c_str(),
             type_brief(mtd->prototype->s[0]->s).c_str(), mtd->name->s);
    }
    if(mtd->code_body && mtd->code_body->debug_information) {
      ref_str** para = mtd->code_body->debug_information->parameter_names->s;
      for(int i = 1; mtd->prototype->s[i]; i++) {
        if(i > 1) printf(", ");
        string type_str;
        if(!mtd->prototype->s[i + 1] && (mtd->access_flags & ACC_VARARGS)) {
          type_str = type_brief(mtd->prototype->s[i]->s + 1) + "...";
        } else {
          type_str = type_brief(mtd->prototype->s[i]->s);
        }

        if(*para && (*para)->s[0]) {
          printf("%s %s", type_str.c_str(),
                 (*para++)->s);
        } else {
          printf("%s arg%d", type_str.c_str(), i);
        }
      }
      printf(")%s {\n", throwsString.c_str());
      
      para = mtd->code_body->debug_information->parameter_names->s;
      dx_uint reg = mtd->code_body->registers_size - mtd->code_body->ins_size;
      if(!(mtd->access_flags & ACC_STATIC)) {
        printf("%s    // v%.4X -> this\n", tabbing.c_str(), reg++);
      }
      for(int i = 1; mtd->prototype->s[i]; i++) {
        if(*para && (*para)->s[0]) {
          if(!strcmp(mtd->prototype->s[i]->s, "J") ||
             !strcmp(mtd->prototype->s[i]->s, "D")) {
            printf("%s    // v%.4X -> %s_lo\n", tabbing.c_str(),
                   reg++, (*para)->s);
            printf("%s    // v%.4X -> %s_hi\n", tabbing.c_str(),
                   reg++, (*para)->s);
          } else {
            printf("%s    // v%.4X -> %s\n", tabbing.c_str(), reg++,
                   (*para)->s);
          }
          para++;
        } else {
          if(!strcmp(mtd->prototype->s[i]->s, "J") ||
             !strcmp(mtd->prototype->s[i]->s, "D")) {
            printf("%s    // v%.4X -> arg%d_lo\n", tabbing.c_str(), reg++, i);
            printf("%s    // v%.4X -> arg%d_hi\n", tabbing.c_str(), reg++, i);
          } else {
            printf("%s    // v%.4X -> arg%d\n", tabbing.c_str(), reg++, i);
          }
        }
      }
    } else {
      for(int i = 1; mtd->prototype->s[i]; i++) {
        if(i > 1) printf(", ");
        printf("%s arg%d", type_brief(mtd->prototype->s[i]->s).c_str(), i);
      }
      if(mtd->code_body) {
        printf(")%s {\n", throwsString.c_str());
      } else {
        printf(")%s;\n", throwsString.c_str());
      }
    }
    if(mtd->code_body) {
      if(mtd->code_body->debug_information) {
        dump_debug(mtd->code_body->debug_information, depth + 2);
      }
      bool callsThis = false;
      if(cl->super_class && (mtd->access_flags & ACC_CONSTRUCTOR) &&
                           !(mtd->access_flags & ACC_STATIC)) {
        // Need to find the super call if it's not the default.
        bool found = false;
        for(int i = 0; i < mtd->code_body->insns_count; i++) {
          DexInstruction* in = mtd->code_body->insns + i;
          if(dex_opcode_formats[in->opcode].flags & DEX_INSTR_FLAG_INVOKE) {
            if(dex_opcode_formats[in->opcode].specialType != SPECIAL_METHOD) {
              break;
            } else if(strcmp(in->special.method.name->s, "<init>")) {
              continue;
            } else {
              if(!strcmp(in->special.method.defining_class->s, cl->name->s)) {
                callsThis = true;
                printf("%s    this(", tabbing.c_str());
              } else if(!strcmp(in->special.method.defining_class->s,
                                cl->super_class->s)) {
                printf("%s    super(", tabbing.c_str());
              } else {
                continue;
              }
              bool first = true;
              for(ref_str** params = in->special.method.prototype->s + 1;
                  *params; params++) {
                if(!first) printf(", ");
                first = false;
                if((*params)->s[0] == 'L' || (*params)->s[0] == '[') {
                  printf("(%s)", get_import_name(dcl, (*params)->s).c_str());
                }
                printf("%s", get_zero_literal((*params)->s[0]).c_str());
              }
              printf(");\n");
            }
            found = true;
            break;
          }
        }
        if(!found) {
          printf("%s    // Couldn't find super call.\n", tabbing.c_str());
        }
      }
      if(isclinit) {
        printf("%s  }\n", tabbing.c_str());
        printf("%s  static {\n", tabbing.c_str());
        printf("%s    // Edit me!\n", tabbing.c_str());
      }
      if((mtd->access_flags & ACC_CONSTRUCTOR) && !callsThis) {
        for(DexField* fld = (mtd->access_flags & ACC_STATIC) ?
                            cl->static_fields : cl->instance_fields;
            !dxc_is_sentinel_field(fld); fld++) {
          if((fld->access_flags & ACC_FINAL) &&
             !(fld->access_flags & ACC_UNUSED)) {
            printf("%s    %s = %s;\n", tabbing.c_str(), fld->name->s,
                   get_zero_literal(fld->type->s[0]).c_str());
          }
        }
      }
      for(int i = 0; i < throwTypes.size(); i++) {
        printf("%s    if(0==0) throw (%s)null;\n", tabbing.c_str(),
               throwTypes[i].c_str());
      }
      if(mtd->prototype->s[0]->s[0] != 'V') {
        printf("%s    return %s;\n", tabbing.c_str(),
               get_zero_literal(mtd->prototype->s[0]->s[0]).c_str());
      }
      printf("%s  }\n", tabbing.c_str());
    }
  }

  vector<dasmcl*>& inner = dcl->inner_classes;
  for(int i = 0; i < inner.size(); i++) {
    if(feedLine) printf("\n");
    feedLine = 1;
    inner[i]->import_table = dcl->import_table;
    decompile_class(inner[i], depth + 1);
  }
  printf("%s}\n", tabbing.c_str());
}


int main(int argc, char** argv) {
  if(argc != 2 && argc != 3) {
    fprintf(stderr, "Usage %s classes.dex [output_dir=out]\n", *argv);
    return 1;
  }
  const char* output_dir = argc >= 3 ? argv[2] : "out";

  if(mkdir(output_dir, 0777) == -1 && errno != EEXIST) {
    fprintf(stderr, "Failed to create output directory %s\n", output_dir);
    return 1;
  }

  FILE* fin = fopen(argv[1], "r");
  DexFile* dx = dxc_read_file(fin);
  if(!dx) {
    fprintf(stderr, "Failed to open dex file\n");
    return 1;
  }
  add_dxdasm_annotations(dx);

  vector<dasmcl> clist;
  map<string, dasmcl*> clmap;
  prep_classes(dx, clist, clmap);

  for(int i = 0; i < clist.size(); i++) {
    if(clist[i].outer_class) continue;
    dasmcl* dcl = &clist[i];
    DexClass* cl = dcl->cl;
    char path[256];
    snprintf(path, sizeof(path), "%s/%s!java", output_dir,
             dxc_type_nice(cl->name->s));
    for(int j = 0; path[j]; j++) {
      if(path[j] == '.') {
        path[j] = 0;
        if(mkdir(path, 0777) == -1 && errno != EEXIST) {
          fprintf(stderr, "Failed to create directory %s\n", path);
          perror("mkdir");
          return 1;
        }
        path[j] = '/';
      } else if(path[j] == '!') {
        path[j] = '.';
      }
    }
    FILE* ign = freopen(path, "w", stdout);
    decompile_class(dcl, 0);
  }
}
