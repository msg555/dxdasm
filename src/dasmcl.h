#ifndef DASMCL_H
#define DASMCL_H

#include <map>
#include <set>
#include <string>
#include <vector>

#include <dxcut/dxcut.h>

typedef struct RefMethodCompare {
  bool operator()(ref_method* a, ref_method* b) const {
    int r = strcmp(a->name->s, b->name->s);
    if(!r) r = strcmp(a->defining_class->s, b->defining_class->s);
    ref_str** pa = a->prototype->s;
    ref_str** pb = b->prototype->s;
    for(; !r && *pa && *pb; ++pa, ++pb)  {
      r = strcmp((*pa)->s, (*pb)->s);
    }
    if(!r) r = pa - pb;
    return r < 0;
  }
} RefMethodCompare;

typedef struct RefFieldCompare {
  bool operator()(ref_field* a, ref_field* b) const {
    int r = strcmp(a->name->s, b->name->s);
    if(!r) r = strcmp(a->defining_class->s, b->defining_class->s);
    if(!r) r = strcmp(a->type->s, b->type->s);
    return r < 0;
  }
} RefFieldCompare;

struct dasmcl {
  dasmcl(DexClass* cl) : cl(cl), outer_class(NULL) {}

  DexClass* cl;
  
  dasmcl* outer_class;
  std::vector<dasmcl*> inner_classes;

  std::set<std::string> import_table;
  std::map<ref_method*, std::string, RefMethodCompare> method_alias_map;
  std::map<ref_field*, std::string, RefFieldCompare> field_alias_map;
};

void strip_classes(DexFile* dxfile);

void prep_classes(DexFile* dxfile, std::vector<dasmcl>& clist,
                  std::map<std::string, dasmcl*>& clmap);

std::string get_package_name(const std::string& name);

std::string type_brief(const std::string& type);

std::string get_import_name(dasmcl* referer, const std::string& cldesc);

#endif
