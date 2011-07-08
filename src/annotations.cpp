#include <stdlib.h>

#include "annotations.h"

static
DexCode* setup_empty_code(int regs, int in_regs) {
  DexCode* ret = (DexCode*)calloc(1, sizeof(DexCode));
  ret->registers_size = regs;
  ret->ins_size = in_regs;
  ret->tries = (DexTryBlock*)malloc(sizeof(DexTryBlock));
  dxc_make_sentinel_try_block(ret->tries);
  return ret;
}

static
void setup_noret_method(DexMethod* method, const char* type, const char* name) {
  method->access_flags = ACC_PUBLIC;
  method->name = dxc_induct_str(name);
  method->prototype = dxc_create_strstr(1);
  method->prototype->s[0] = dxc_induct_str(type);
  method->code_body = NULL;
  method->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(method->annotations);
  method->parameter_annotations =
      (DexAnnotation**)malloc(sizeof(DexAnnotation*));
  *method->parameter_annotations = NULL;
}

void setup_int_method(DexMethod* method, const char* name) {
  setup_noret_method(method, "I", name);
}

static
void setup_insns_method(DexMethod* method) {
  method->access_flags = ACC_PUBLIC;
  method->name = dxc_induct_str("insns");
  method->prototype = dxc_create_strstr(1);
  method->prototype->s[0] = dxc_induct_str("[Ljava/lang/String;");
  method->code_body = NULL;
  method->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(method->annotations);
  method->parameter_annotations =
      (DexAnnotation**)malloc(sizeof(DexAnnotation*));
  *method->parameter_annotations = NULL;
}

static
void setup_enum_init(DexMethod* method) {
  method->access_flags = (DexAccessFlags)(ACC_PUBLIC | ACC_CONSTRUCTOR);
  method->name = dxc_induct_str("<init>");
  method->prototype = dxc_create_strstr(3);
  method->prototype->s[0] = dxc_induct_str("V");
  method->prototype->s[1] = dxc_induct_str("Ljava/lang/String;");
  method->prototype->s[2] = dxc_induct_str("I");
  method->code_body = setup_empty_code(16, 2);
  method->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(method->annotations);
  method->parameter_annotations =
      (DexAnnotation**)malloc(sizeof(DexAnnotation*));
  *method->parameter_annotations = NULL;
}

void add_dxdasm_annotations(DexFile* f) {
  int size = 0;
  for(DexClass* cl = f->classes; !dxc_is_sentinel_class(cl); ++cl) size++;
  f->classes = (DexClass*)realloc(f->classes, (size + 12) * sizeof(DexClass));
  DexClass* cl = f->classes + size;
  DexClass* cl2 = f->classes + size + 1;
  DexClass* cl3 = f->classes + size + 2;
  DexClass* cl4 = f->classes + size + 3;
  DexClass* cl5 = f->classes + size + 4;
  DexClass* cl6 = f->classes + size + 5;
  DexClass* cl7 = f->classes + size + 6;
  DexClass* cl8 = f->classes + size + 7;
  DexClass* cl9 = f->classes + size + 8;
  DexClass* cl10 = f->classes + size + 9;
  DexClass* cl11 = f->classes + size + 10;
  dxc_make_sentinel_class(f->classes + size + 11);

  cl->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmMethod;");
  cl->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl->interfaces = dxc_create_strstr(0);
  cl->source_file = NULL;
  cl->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl->annotations);
  cl->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl->static_values);
  cl->static_fields = cl->instance_fields = (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl->static_fields);
  cl->direct_methods = (DexMethod*)malloc(sizeof(DexMethod));
  dxc_make_sentinel_method(cl->direct_methods);

  cl->virtual_methods = (DexMethod*)calloc(8, sizeof(DexMethod));
  setup_int_method(cl->virtual_methods + 0, "registers");
  setup_int_method(cl->virtual_methods + 1, "outsSize");
  setup_insns_method(cl->virtual_methods + 2);
  setup_noret_method(cl->virtual_methods + 3,
                     "[Lorg/dxcut/dxdasm/DxdasmPacked;", "packedSwitches");
  setup_noret_method(cl->virtual_methods + 4,
                     "[Lorg/dxcut/dxdasm/DxdasmSparse;", "sparseSwitches");
  setup_noret_method(cl->virtual_methods + 5,
                     "[Lorg/dxcut/dxdasm/DxdasmData;", "dataArrays");
  setup_noret_method(cl->virtual_methods + 6,
                     "[Lorg/dxcut/dxdasm/DxdasmTry;", "tryBlocks");
  dxc_make_sentinel_method(cl->virtual_methods + 7);

  cl2->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmSynthetic;");
  cl2->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl2->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl2->interfaces = dxc_create_strstr(0);
  cl2->source_file = NULL;
  cl2->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl2->annotations);
  cl2->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl2->static_values);
  cl2->static_fields = cl2->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl2->static_fields);
  cl2->direct_methods = (DexMethod*)malloc(sizeof(DexMethod));
  dxc_make_sentinel_method(cl2->direct_methods);

  cl2->virtual_methods = (DexMethod*)calloc(2, sizeof(DexMethod));
  setup_int_method(cl2->virtual_methods + 0, "accessFlags");
  dxc_make_sentinel_method(cl2->virtual_methods + 1);

  cl3->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmEnum;");
  cl3->access_flags = (DexAccessFlags)(ACC_PUBLIC | ACC_ABSTRACT);
  cl3->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl3->interfaces = dxc_create_strstr(0);
  cl3->source_file = NULL;
  cl3->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl3->annotations);
  cl3->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl3->static_values);
  cl3->static_fields = cl3->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl3->static_fields);
  cl3->direct_methods = (DexMethod*)calloc(2, sizeof(DexMethod));
  setup_enum_init(cl3->direct_methods);
  dxc_make_sentinel_method(cl3->direct_methods + 1);
  cl3->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl3->virtual_methods);

  cl4->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmPacked;");
  cl4->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl4->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl4->interfaces = dxc_create_strstr(0);
  cl4->source_file = NULL;
  cl4->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl4->annotations);
  cl4->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl4->static_values);
  cl4->static_fields = cl4->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl4->static_fields);
  cl4->direct_methods = (DexMethod*)calloc(3, sizeof(DexMethod));
  setup_int_method(cl4->direct_methods, "firstKey");
  setup_noret_method(cl4->direct_methods + 1, "[Ljava/lang/String;", "targets");
  dxc_make_sentinel_method(cl4->direct_methods + 2);
  cl4->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl4->virtual_methods);

  cl5->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmSparse;");
  cl5->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl5->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl5->interfaces = dxc_create_strstr(0);
  cl5->source_file = NULL;
  cl5->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl5->annotations);
  cl5->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl5->static_values);
  cl5->static_fields = cl5->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl5->static_fields);
  cl5->direct_methods = (DexMethod*)calloc(3, sizeof(DexMethod));
  setup_noret_method(cl5->direct_methods, "[I", "keys");
  setup_noret_method(cl5->direct_methods + 1, "[Ljava/lang/String;", "targets");
  dxc_make_sentinel_method(cl5->direct_methods + 2);
  cl5->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl5->virtual_methods);

  cl6->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmData;");
  cl6->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl6->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl6->interfaces = dxc_create_strstr(0);
  cl6->source_file = NULL;
  cl6->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl6->annotations);
  cl6->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl6->static_values);
  cl6->static_fields = cl6->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl6->static_fields);
  cl6->direct_methods = (DexMethod*)calloc(3, sizeof(DexMethod));
  setup_noret_method(cl6->direct_methods, "I", "elementWidth");
  setup_noret_method(cl6->direct_methods + 1, "[J", "data");
  dxc_make_sentinel_method(cl6->direct_methods + 2);
  cl6->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl6->virtual_methods);

  cl7->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmTry;");
  cl7->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl7->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl7->interfaces = dxc_create_strstr(0);
  cl7->source_file = NULL;
  cl7->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl7->annotations);
  cl7->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl7->static_values);
  cl7->static_fields = cl7->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl7->static_fields);
  cl7->direct_methods = (DexMethod*)calloc(5, sizeof(DexMethod));
  setup_noret_method(cl7->direct_methods, "Ljava/lang/String;", "startInsn");
  setup_noret_method(cl7->direct_methods + 1, "I", "insnLength");
  setup_noret_method(cl7->direct_methods + 2,
      "[Lorg/dxcut/dxdasm/DxdasmHandler;", "handlers");
  setup_noret_method(cl7->direct_methods + 3,
      "Ljava/lang/String;", "catchAllTarget");
  dxc_make_sentinel_method(cl7->direct_methods + 4);
  cl7->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl7->virtual_methods);

  cl8->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmHandler;");
  cl8->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl8->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl8->interfaces = dxc_create_strstr(0);
  cl8->source_file = NULL;
  cl8->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl8->annotations);
  cl8->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl8->static_values);
  cl8->static_fields = cl8->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl8->static_fields);
  cl8->direct_methods = (DexMethod*)calloc(3, sizeof(DexMethod));
  setup_noret_method(cl8->direct_methods, "Ljava/lang/Class;", "catchType");
  setup_noret_method(cl8->direct_methods + 1, "Ljava/lang/String;",
                     "target");
  dxc_make_sentinel_method(cl8->direct_methods + 2);
  cl8->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl8->virtual_methods);

  cl9->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmAliases;");
  cl9->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl9->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl9->interfaces = dxc_create_strstr(0);
  cl9->source_file = NULL;
  cl9->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl9->annotations);
  cl9->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl9->static_values);
  cl9->static_fields = cl9->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl9->static_fields);
  cl9->direct_methods = (DexMethod*)calloc(3, sizeof(DexMethod));
  setup_noret_method(cl9->direct_methods,
      "[Lorg/dxcut/dxdasm/DxdasmMethodAlias;", "methodAliases");
  setup_noret_method(cl9->direct_methods + 1,
      "[Lorg/dxcut/dxdasm/DxdasmFieldAlias;", "fieldAliases");
  dxc_make_sentinel_method(cl9->direct_methods + 2);
  cl9->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl9->virtual_methods);

  cl10->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmMethodAlias;");
  cl10->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl10->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl10->interfaces = dxc_create_strstr(0);
  cl10->source_file = NULL;
  cl10->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl10->annotations);
  cl10->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl10->static_values);
  cl10->static_fields = cl10->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl10->static_fields);
  cl10->direct_methods = (DexMethod*)calloc(5, sizeof(DexMethod));
  setup_noret_method(cl10->direct_methods, "Ljava/lang/String;", "alias");
  setup_noret_method(cl10->direct_methods + 1, "Ljava/lang/Class;", "clazz");
  setup_noret_method(cl10->direct_methods + 2, "Ljava/lang/String;", "name");
  setup_noret_method(cl10->direct_methods + 3,
                     "[Ljava/lang/Class;", "prototype");
  dxc_make_sentinel_method(cl10->direct_methods + 4);
  cl10->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl10->virtual_methods);

  cl11->name = dxc_induct_str("Lorg/dxcut/dxdasm/DxdasmFieldAlias;");
  cl11->access_flags = (DexAccessFlags)
                     (ACC_PUBLIC | ACC_INTERFACE | ACC_ANNOTATION);
  cl11->super_class = dxc_induct_str("Ljava/lang/Object;");
  cl11->interfaces = dxc_create_strstr(0);
  cl11->source_file = NULL;
  cl11->annotations = (DexAnnotation*)malloc(sizeof(DexAnnotation));
  dxc_make_sentinel_annotation(cl11->annotations);
  cl11->static_values = (DexValue*)malloc(sizeof(DexValue));
  dxc_make_sentinel_value(cl11->static_values);
  cl11->static_fields = cl11->instance_fields =
      (DexField*)malloc(sizeof(DexField));
  dxc_make_sentinel_field(cl11->static_fields);
  cl11->direct_methods = (DexMethod*)calloc(5, sizeof(DexMethod));
  setup_noret_method(cl11->direct_methods, "Ljava/lang/String;", "alias");
  setup_noret_method(cl11->direct_methods + 1, "Ljava/lang/Class;", "clazz");
  setup_noret_method(cl11->direct_methods + 2, "Ljava/lang/String;", "name");
  setup_noret_method(cl11->direct_methods + 3, "Ljava/lang/Class;", "type");
  dxc_make_sentinel_method(cl11->direct_methods + 4);
  cl11->virtual_methods = (DexMethod*)calloc(1, sizeof(DexMethod));
  dxc_make_sentinel_method(cl11->virtual_methods);
}
