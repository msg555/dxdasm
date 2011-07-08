#include "modids.h"

void modifyIdentifiers(DexFile* file) {
  vector<char*> source_list;
  vector<char*> dest_list;
  for(DexClass* cl = dxfile->classes; !dxc_is_sentinel_class(cl); ++cl) {
    string type = cl->name->s;
    string tbrief = type_brief(type);
    if(!('a' <= tbrief[0] && tbrief[0] <= 'z') &&
       !('A' <= tbrief[0] && tbrief[0] <= 'Z') && tbrief[0] != '_') {
      type.insert(type.size() - tbrief.size() - 1, "__idmod_");
      source_list.push_back(copy_str(cl->name->s));
      dest_list.push_back(copy_str(type.c_str()));
    }
  }
  dxc_rename_classes(dxfile, source_list.size(), &source_list[0],
                     &dest_list[0]);
  for(int i = 0; i < source_list.size(); i++) {
    free(source_list[i]);
    free(dest_list[i]);
  }
}

void repairIdentifiers(DexFile* file) {

}
