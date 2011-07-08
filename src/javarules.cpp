#include "javarules.h"

#include <cstring>
#include <cstdio>

#include "mutf8.h"

using namespace std;

const char* java_keywords[] = {
  "abstract",
  "boolean",
  "break",
  "byte",
  "case",
  "catch",
  "char",
  "class",
  "const",
  "continue",
  "default",
  "do",
  "double",
  "else",
  "extends",
  "final",
  "finally",
  "float",
  "for",
  "goto",
  "if",
  "implements",
  "import",
  "instanceof",
  "int",
  "interface",
  "long",
  "native",
  "new",
  "package",
  "private",
  "protected",
  "public",
  "return",
  "short",
  "static",
  "strictfp",
  "super",
  "switch",
  "synchronized",
  "this",
  "throw",
  "throws",
  "transient",
  "try",
  "void",
  "volatile",
  "while",
};

bool is_java_keyword(const char* s) {
  int lo = 0;
  int hi = sizeof(java_keywords) / sizeof(const char*);
  while(lo < hi) {
    int md = lo + (hi - lo) / 2;
    int cmp = strcmp(s, java_keywords[md]);
    if(!cmp) {
      return true;
    } else if(cmp < 0) {
      hi = md;
    } else {
      lo = md + 1;
    }
  }
  return false;
}

bool is_java_identifier_start(unsigned int cp) {
  if(cp < 64) {
    return false; // Disclude synthetic identifiers with $
  } else if(cp < 128) {
    return (0x7FFFFFE87FFFFFEll & 1ll << cp - 64) != 0;
  } else {
    return true; // This isn't strictly true but the rules seemed sufficiently
                 // complicated that I didn't want to implement it for the rare
                 // cases this isn't correct.
  }
}

bool is_java_identifier_part(unsigned int cp) {
  return is_java_identifier_start(cp) || '0' <= cp && cp <= '9';
}

bool is_java_identifier(const char* s) {
  if(is_java_keyword(s)) return false;
  if(!is_java_identifier_start(mutf8NextCodePoint(&s))) return false;
  while(*s) {
    if(!is_java_identifier_part(mutf8NextCodePoint(&s))) {
      return false;
    }
  }
  return true;
}

bool is_toplevel_class(const char* s) {
  bool result = true;
  for(; *s; ++s) {
    if(*s == '/') {
      result = true;
    } else if(*s == '$') {
      result = false;
    }
  }
  return result;
}

string get_toplevel_class(const string& s) {
  int pos = s.find_last_of('/');
  pos = s.find('$', pos + 1);
  if(pos == -1) return s;
  string res = s.substr(0, pos) + ";";
  return res;
}
