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

static
string sanitize_identifier(string id, int token = -1) {
  if(token < -1 || !is_java_identifier(id.c_str())) {
    if(token == -1) {
      return string("_dxdasm_") + id;
    } else {
      char buf[32];
      sprintf(buf, "%s%d", token < 0 ? "x" : "",
                           token < 0 ? -token - 2 : token);
      return string("_dxdasm") + buf + "_" + id;
    }
  }
  return id;
}

static
string desanitize_identifier(string id) {
  if(id.size() > 8 && id.substr(0, 7) == "_dxdasm") {
    return id.substr(id.find('_', 7) + 1);
  }
  return id;
}

static
string sanitize_type(string type) {
  /* Sanitize all of the tokens.  Additionally make sure all the non-namespace
   * tokens are unique. */
  int last = 1;
  set<string> toks;
  for(int i = 1; i < type.size(); i++) {
    if(type[i] == '/' || type[i] == '$' || type[i] == ';') {
      string ntok = sanitize_identifier(type.substr(last, i - last), i);
      for(int j = -2; !toks.insert(ntok).second; j--) {
        ntok = sanitize_identifier(type.substr(last, i - last), j);
fprintf(stderr, "%s\n", ntok.c_str());
      }
      type.replace(last, i - last, ntok);
      i += ntok.size() - (i - last);
      last = i + 1;
    }
  }

  if(type.find('/') == string::npos) {
    /* I want to put everything in a package to make things simpler.  We'll
     * strip it out of the package later or reassembly. */
    type = string("Ldxdasm_default/") + type.substr(1);
  }
  return type;
}

static
string desanitize_type(string type) {
  int last = type.size() - 1;
  for(int i = type.size() - 2; i >= 1; i--) {
    if(i == 1 || type[i - 1] == '/' || type[i - 1] == '$') {
      type.replace(i, last - i,
                   desanitize_identifier(type.substr(i, last - i)));
      last = i - 1;
    }
  }
  string prefix = "Ldxdasm_default/";
  if(type.size() > prefix.size() && prefix == type.substr(0, prefix.size())) {
    type = string("L") + type.substr(prefix.size());
  }
  return type;
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
    string stype = sanitize_type(type);
    string tbrief = type_brief(type);
    if(type != stype) {
      source_classes.push_back(dxc_copy_str(cl->name));
      dest_classes.push_back(dxc_induct_str(stype.c_str()));
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexField* fld = iter ? cl->static_fields : cl->instance_fields;
        !dxc_is_sentinel_field(fld); ++fld) {
      string sfield = sanitize_identifier(fld->name->s);
      if(sfield != fld->name->s) {
        ref_field rfld, dfld;
        rfld.defining_class = dxc_copy_str(cl->name);
        rfld.name = dxc_copy_str(fld->name);
        rfld.type = dxc_copy_str(fld->type);
        dfld.defining_class = dxc_copy_str(cl->name);
        dfld.name = dxc_induct_str(sfield.c_str());
        dfld.type = dxc_copy_str(fld->type);
        source_fields.push_back(rfld);
        dest_fields.push_back(dfld);
      }
    }
    set<string> method_names;
    for(int iter = 0; iter < 2; iter++)
    for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
        !dxc_is_sentinel_method(mtd); ++mtd) {
      string smethod = sanitize_identifier(mtd->name->s);

      /* This isn't 100% correct.  I'm trying to deal with synthetic methods
       * that get inserted by javac in relation to varargs methods.  Really I
       * should be checking the SYNTHETIC flag. */
      string params;
      for(ref_str** para = mtd->prototype->s + 1; *para; ++para) {
        params += (*para)->s[0];
      }
      if(!params.empty() && params[params.size() - 1] == '[') {
        for(int i = 0; !method_names.insert(smethod + params).second; i++) {
          smethod = sanitize_identifier(mtd->name->s, -i - 2);
        }
      }

      if(smethod != mtd->name->s && strcmp("<init>", mtd->name->s) &&
         strcmp("<clinit>", mtd->name->s)) {
        ref_method rmtd, dmtd;
        rmtd.defining_class = dxc_copy_str(cl->name);
        rmtd.name = dxc_copy_str(mtd->name);
        rmtd.prototype = dxc_copy_strstr(mtd->prototype);
        dmtd.defining_class = dxc_copy_str(cl->name);
        dmtd.name = dxc_induct_str(smethod.c_str());
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

void strip_classes(DexFile* dxfile) {
  vector<ref_field> source_fields; vector<ref_field> dest_fields;
  vector<ref_method> source_methods; vector<ref_method> dest_methods;
  vector<ref_str*> source_classes; vector<ref_str*> dest_classes;
  source_classes.push_back(dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmEnum;"));
  dest_classes.push_back(dxc_induct_str("Ljava/lang/Enum;"));
  DexClass* pos = dxfile->classes;

  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    string type = cl->name->s;
    string stype = desanitize_type(type);
    string tbrief = type_brief(type);
    string package = get_package_name(dxc_type_nice(cl->name->s));
    
    if(package == "org.dxcut.dxdasm") {
      dxc_free_class(cl);
      continue;
    }

    if(type != stype) {
      source_classes.push_back(dxc_copy_str(cl->name));
      dest_classes.push_back(dxc_induct_str(stype.c_str()));
    }
    for(int iter = 0; iter < 2; iter++)
    for(DexField* fld = iter ? cl->static_fields : cl->instance_fields;
        !dxc_is_sentinel_field(fld); ++fld) {
      string sfield = desanitize_identifier(fld->name->s);
      if(sfield != fld->name->s) {
        ref_field rfld, dfld;
        rfld.defining_class = dxc_copy_str(cl->name);
        rfld.name = dxc_copy_str(fld->name);
        rfld.type = dxc_copy_str(fld->type);
        dfld.defining_class = dxc_copy_str(cl->name);
        dfld.name = dxc_induct_str(sfield.c_str());
        dfld.type = dxc_copy_str(fld->type);
        source_fields.push_back(rfld);
        dest_fields.push_back(dfld);
      }
    }

    map<ref_method, DexMethod*, RefMethodCompare> clobber_map;
    for(int iter = 0; iter < 2; iter++) {
      DexMethod* mtdpos = iter ? cl->direct_methods : cl->virtual_methods;
      for(DexMethod* mtd = iter ? cl->direct_methods : cl->virtual_methods;
          !dxc_is_sentinel_method(mtd); ++mtd) {
        ref_method rmtd, dmtd;
        bool name_change = false;
        string smethod = desanitize_identifier(mtd->name->s);
        if(string("dxdasm_static") == mtd->name->s) {
          smethod = "<clinit>";
          mtd->access_flags =
              (DexAccessFlags)(mtd->access_flags | ACC_CONSTRUCTOR);
        }
        if(smethod != mtd->name->s && strcmp("<init>", mtd->name->s)) {
          name_change = true;
          rmtd.defining_class = dxc_copy_str(cl->name);
          rmtd.name = dxc_copy_str(mtd->name);
          rmtd.prototype = dxc_copy_strstr(mtd->prototype);
          dmtd.defining_class = dxc_copy_str(cl->name);
          dmtd.name = dxc_induct_str(smethod.c_str());
          dmtd.prototype = dxc_copy_strstr(mtd->prototype);
        } else {
          dmtd.defining_class = cl->name;
          dmtd.name = mtd->name;
          dmtd.prototype = mtd->prototype;
        }

        /* Sometimes javac inserts methods that were already present and
         * handled.  If two function names collide we take the one that wasn't
         * synthetic.  This also happens with static initializers which we
         * rename dxdasm_static. */
        DexMethod*& clobber = clobber_map[dmtd];
        if(clobber) {
          if(!strcmp(mtd->name->s, "<clinit>") ||
             (smethod != "<clinit>" && (mtd->access_flags & ACC_SYNTHETIC))) {
            continue;
          } else {
            *clobber = *mtd;
          }
        } else {
          clobber = mtdpos;
          (*mtdpos++) = *mtd;
        }

        if(name_change) {
          source_methods.push_back(rmtd);
          dest_methods.push_back(dmtd);
        }
      }
      dxc_make_sentinel_method(mtdpos);
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

