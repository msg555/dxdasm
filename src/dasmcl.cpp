#include <algorithm>
#include <stdio.h>
#include <string.h>
#include <assert.h>

#include "dasmcl.h"
#include "javarules.h"

using namespace std;

string get_package_name(const string& name) {
  int pos = name.find_last_of('.');
  if(pos == -1) return "";
  return name.substr(0, pos);
}

string type_brief(const string& type) {
  string ret = dxc_type_nice(type.c_str());
  int dot_pos = ret.find_last_of('.');
  int dollar_pos = ret.find_last_of('$');
  if(dot_pos == -1 && dollar_pos == -1) return ret;
  if(dot_pos == -1) return ret.substr(dollar_pos + 1);
  if(dollar_pos == -1) return ret.substr(dot_pos + 1);
  return ret.substr(max(dot_pos, dollar_pos) + 1);
}

static const char* strip_array(const char* s) {
  while(*s == '[') ++s;
  return s;
}

static
void build_import_table(dasmcl* dcl) {
  DexClass* cl = dcl->cl;

  vector<string> refdescs;
  refdescs.push_back("Lorg/dxcut/dxdasm/DxdasmMethod;");
  for(int i = 0; i < dcl->inner_classes.size(); i++) {
    build_import_table(dcl->inner_classes[i]);
    set<string>& descst = dcl->inner_classes[i]->import_table;
    for(set<string>::iterator it = descst.begin(); it != descst.end(); ++it) {
      refdescs.push_back(*it);
    }
  }

  if(cl->super_class) {
    refdescs.push_back(cl->super_class->s);
  }
  for(ref_str** interfaces = cl->interfaces->s; *interfaces; interfaces++) {
    refdescs.push_back((*interfaces)->s);
  }

  for(int iter = 0; iter < 2; iter++)
  for(DexField* fld = iter ? cl->instance_fields : cl->static_fields;
      !dxc_is_sentinel_field(fld); ++fld) {
    refdescs.push_back(strip_array(fld->type->s));
  }
  for(int iter = 0; iter < 2; iter++)
  for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
        !dxc_is_sentinel_method(mtd); ++mtd) {
    for(ref_str** proto = mtd->prototype->s; *proto; ++proto) {
      refdescs.push_back(strip_array((*proto)->s));
    }
  }

  sort(refdescs.begin(), refdescs.end());
  refdescs.resize(unique(refdescs.begin(), refdescs.end()) - refdescs.begin());

  map<string, string> import_map;
  for(int i = 0; i < refdescs.size(); i++) {
    if(refdescs[i][0] != 'L') continue;
    string brief = type_brief(refdescs[i]);
    string& name = import_map[brief];
    if(name.size() < refdescs[i].size()) {
      name = refdescs[i];
    }
  }
  string self_brief = type_brief(cl->name->s);
  import_map[self_brief] = cl->name->s;
  for(map<string, string>::iterator it = import_map.begin();
      it != import_map.end(); ++it) {
    dcl->import_table.insert(it->second);
  }
}

static void add_method_alias(set<string>& mtd_aliases, dasmcl* dcl,
                             ref_method* mtd) {
  if(dcl->method_alias_map.find(mtd) != dcl->method_alias_map.end()) return;
  for(int i = 0; ; i++) {
    string name = type_brief(mtd->defining_class->s) + "." + mtd->name->s;
    if(i) {
      char buf[20];
      sprintf(buf, "_%d", i);
      name += buf;
    }
    if(mtd_aliases.insert(name).second) {
      dcl->method_alias_map[mtd] = name;
      break;
    }
  }
}

static void add_field_alias(set<string>& fld_aliases, dasmcl* dcl,
                            ref_field* fld) {
  if(dcl->field_alias_map.find(fld) != dcl->field_alias_map.end()) return;
  for(int i = 0; ; i++) {
    string name = type_brief(fld->defining_class->s) + "." + fld->name->s;
    if(i) {
      char buf[20];
      sprintf(buf, "_%d", i);
      name += buf;
    }
    if(fld_aliases.insert(name).second) {
      dcl->field_alias_map[fld] = name;
      break;
    }
  }
}

static void build_alias_tables(dasmcl* dcl) {
  DexClass* cl = dcl->cl;
  set<string> mtd_aliases, fld_aliases;
  for(int iter = 0; iter < 2; iter++)
  for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
      !dxc_is_sentinel_method(mtd); ++mtd) {
    DexCode* code = mtd->code_body;
    if(!code) continue;
    for(int i = 0; i < code->insns_count; i++) {
      DexInstruction* in = code->insns + i;
      if(dex_opcode_formats[in->opcode].specialType == SPECIAL_METHOD) {
        add_method_alias(mtd_aliases, dcl, &in->special.method);
      } else if(dex_opcode_formats[in->opcode].specialType == SPECIAL_FIELD) {
        add_field_alias(fld_aliases, dcl, &in->special.field);
      }
    }
  }

  for(int i = 0; i < dcl->inner_classes.size(); i++) {
    dasmcl* idcl = dcl->inner_classes[i];
    build_alias_tables(idcl);
/* TODO: It might be nice to just have alias tables in outer classes but this
 * will requrie mroe work in the reassembler than I want to do right now.
    for(typeof(idcl->method_alias_map.begin()) it =
        idcl->method_alias_map.begin(); it != idcl->method_alias_map.end();
        it++) {
      add_method_alias(mtd_aliases, dcl, it->first);
    }
    for(typeof(idcl->field_alias_map.begin()) it =
        idcl->field_alias_map.begin(); it != idcl->field_alias_map.end();
        it++) {
      add_field_alias(fld_aliases, dcl, it->first);
    }
*/
  }
}

static
char* copy_str(const char* s) {
  char* ret = (char*)malloc(strlen(s) + 1);
  strcpy(ret, s);
  return ret;
}

static
string filter_name(const string& s) {
  string ret = s;
  for(int i = 0; i < ret.size(); i++) {
    if(ret[i] == '$') {
      ret[i] = '_';
    }
  }
  return ret;
}

void prep_classes(DexFile* dxfile, std::vector<dasmcl>& clist,
                  map<string, dasmcl*>& clmap) {
  vector<ref_field> source_fields; vector<ref_field> dest_fields;
  vector<ref_method> source_methods; vector<ref_method> dest_methods;
  vector<ref_str*> source_classes; vector<ref_str*> dest_classes;
  source_classes.push_back(dxc_induct_str("Ljava/lang/Enum;"));
  dest_classes.push_back(dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmEnum;"));
  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    string type = cl->name->s;
    string tbrief = type_brief(type);
    if(!is_java_identifier(tbrief.c_str())) {
      type.insert(type.size() - tbrief.size() - 1, "_dxdasm_");
      source_classes.push_back(dxc_copy_str(cl->name));
      dest_classes.push_back(dxc_induct_str(type.c_str()));
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexField* fld = iter ? cl->static_fields : cl->instance_fields;
        !dxc_is_sentinel_field(fld); ++fld) {
      if(!is_java_identifier(fld->name->s)) {
        ref_field rfld, dfld;
        rfld.defining_class = dxc_copy_str(cl->name);
        rfld.name = dxc_copy_str(fld->name);
        rfld.type = dxc_copy_str(fld->type);
        dfld.defining_class = dxc_copy_str(cl->name);
        dfld.name = dxc_induct_str((string("_dxdasm_") +
                                    filter_name(fld->name->s)).c_str());
        dfld.type = dxc_copy_str(fld->type);
        source_fields.push_back(rfld);
        dest_fields.push_back(dfld);
      }
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
        !dxc_is_sentinel_method(mtd); ++mtd) {
      if(!is_java_identifier(mtd->name->s) && strcmp("<init>", mtd->name->s) &&
         strcmp("<clinit>", mtd->name->s)) {
        ref_method rmtd, dmtd;
        rmtd.defining_class = dxc_copy_str(cl->name);
        rmtd.name = dxc_copy_str(mtd->name);
        rmtd.prototype = dxc_copy_strstr(mtd->prototype);
        dmtd.defining_class = dxc_copy_str(cl->name);
        dmtd.name = dxc_induct_str((string("_dxdasm_") +
                                    filter_name(mtd->name->s)).c_str());
        dmtd.prototype = dxc_copy_strstr(mtd->prototype);
        source_methods.push_back(rmtd);
        dest_methods.push_back(dmtd);
      }
    }
  }
  dxc_rename_identifiers(dxfile,
      source_fields.size(), &source_fields[0], &dest_fields[0],
      source_methods.size(), &source_methods[0], &dest_methods[0],
      source_classes.size(), &source_classes[0], &dest_classes[0]);
  for(int i = 0; i < source_classes.size(); i++) {
    dxc_free_str(source_classes[i]);
    dxc_free_str(dest_classes[i]);
  }
  for(int i = 0; i < source_fields.size(); i++) {
    dxc_free_str(source_fields[i].defining_class);
    dxc_free_str(source_fields[i].name);
    dxc_free_str(source_fields[i].type);
    dxc_free_str(dest_fields[i].defining_class);
    dxc_free_str(dest_fields[i].name);
    dxc_free_str(dest_fields[i].type);
  }
  for(int i = 0; i < source_methods.size(); i++) {
    dxc_free_str(source_methods[i].defining_class);
    dxc_free_str(source_methods[i].name);
    dxc_free_strstr(source_methods[i].prototype);
    dxc_free_str(dest_methods[i].defining_class);
    dxc_free_str(dest_methods[i].name);
    dxc_free_strstr(dest_methods[i].prototype);
  }

  // Create class mapping and table.
  clist.clear();
  clmap.clear();
  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    clist.push_back(dasmcl(cl));
  }
  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    clmap[cl->name->s] = &clist[cl - dxfile->classes];
  }

  // Compute outer classes and inner class lists.
  for(int i = 0; i < clist.size(); i++) {
    string name = clist[i].cl->name->s;
    int pos = name.find_last_of('$');
    if(pos != -1) {
      string outer_name = name.substr(0, pos) + ";";
      if(clmap.find(outer_name) == clmap.end()) {
        fprintf(stderr, "Failed to find outer class definition for %s\n",
                clist[i].cl->name->s);
      } else {
        clist[i].outer_class = clmap[outer_name];
        clist[i].outer_class->inner_classes.push_back(&clist[i]);
      }
    }
  }

  // Compute import tables.
  for(int i = 0; i < clist.size(); i++) {
    if(!clist[i].outer_class) {
      build_import_table(&clist[i]);
      build_alias_tables(&clist[i]);
    }
  }
}

string get_import_name(dasmcl* referer, const string& cldesc) {
  if(referer->import_table.find(strip_array(cldesc.c_str())) ==
     referer->import_table.end()) {
    string result = dxc_type_nice(cldesc.c_str());
    for(int i = 0; i < result.size(); i++) {
      if(result[i] == '$') {
        result[i] = '.';
      }
    }
    return result;
  } else {
    return type_brief(cldesc);
  }
}

bool is_dxdasm_identifier(const string& id) {
  return id.size() >= 8 && id.substr(0, 8) == "_dxdasm_";
}

string strip_dxdasm_identifier(const string& id) {
  assert(is_dxdasm_identifier(id));
  return id.substr(8);
}

void strip_classes(DexFile* dxfile) {
  vector<ref_field> source_fields; vector<ref_field> dest_fields;
  vector<ref_method> source_methods; vector<ref_method> dest_methods;
  vector<ref_str*> source_classes; vector<ref_str*> dest_classes;
  source_classes.push_back(dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmEnum;"));
  dest_classes.push_back(dxc_induct_str("Ljava/lang/Enum;"));
  DexClass* pos = dxfile->classes;
  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    string type = cl->name->s;
    string tbrief = type_brief(type);
    string package = get_package_name(dxc_type_nice(cl->name->s));
    
    if(strcmp("Lorg/dxcut/dxdasm/DxdasmEnum;", cl->name->s) &&
       package == "org.dxcut.dxdasm") {
      dxc_free_class(cl);
      continue;
    }

    if(is_dxdasm_identifier(tbrief)) {
      string stripped = strip_dxdasm_identifier(cl->name->s) + ";";
      type = type.substr(0, type.size() - stripped.size()) + stripped;
      source_classes.push_back(dxc_copy_str(cl->name));
      dest_classes.push_back(dxc_induct_str(type.c_str()));
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexField* fld = iter ? cl->static_fields : cl->instance_fields;
        !dxc_is_sentinel_field(fld); ++fld) {
      if(is_dxdasm_identifier(fld->name->s)) {
        ref_field rfld, dfld;
        rfld.defining_class = dxc_copy_str(cl->name);
        rfld.name = dxc_copy_str(fld->name);
        rfld.type = dxc_copy_str(fld->type);
        dfld.defining_class = dxc_copy_str(cl->name);
        dfld.name = dxc_induct_str(
            strip_dxdasm_identifier(fld->name->s).c_str());
        dfld.type = dxc_copy_str(fld->type);
        source_fields.push_back(rfld);
        dest_fields.push_back(dfld);
      }
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
        !dxc_is_sentinel_method(mtd); ++mtd) {
      if(!is_java_identifier(mtd->name->s) && strcmp("<init>", mtd->name->s) &&
         strcmp("<clinit>", mtd->name->s)) {
        ref_method rmtd, dmtd;
        rmtd.defining_class = dxc_copy_str(cl->name);
        rmtd.name = dxc_copy_str(mtd->name);
        rmtd.prototype = dxc_copy_strstr(mtd->prototype);
        dmtd.defining_class = dxc_copy_str(cl->name);
        dmtd.name = dxc_induct_str(
            strip_dxdasm_identifier(mtd->name->s).c_str());
        dmtd.prototype = dxc_copy_strstr(mtd->prototype);
        source_methods.push_back(rmtd);
        dest_methods.push_back(dmtd);
      }
    }
    *(pos++) = *cl;
  }
  dxc_make_sentinel_class(pos);

  dxc_rename_identifiers(dxfile,
      source_fields.size(), &source_fields[0], &dest_fields[0],
      source_methods.size(), &source_methods[0], &dest_methods[0],
      source_classes.size(), &source_classes[0], &dest_classes[0]);
  for(int i = 0; i < source_classes.size(); i++) {
    dxc_free_str(source_classes[i]);
    dxc_free_str(dest_classes[i]);
  }
  for(int i = 0; i < source_fields.size(); i++) {
    dxc_free_str(source_fields[i].defining_class);
    dxc_free_str(source_fields[i].name);
    dxc_free_str(source_fields[i].type);
    dxc_free_str(dest_fields[i].defining_class);
    dxc_free_str(dest_fields[i].name);
    dxc_free_str(dest_fields[i].type);
  }
  for(int i = 0; i < source_methods.size(); i++) {
    dxc_free_str(source_methods[i].defining_class);
    dxc_free_str(source_methods[i].name);
    dxc_free_strstr(source_methods[i].prototype);
    dxc_free_str(dest_methods[i].defining_class);
    dxc_free_str(dest_methods[i].name);
    dxc_free_strstr(dest_methods[i].prototype);
  }
}

