#ifndef JAVARULES_H
#define JAVARULES_H

#include <string>

bool is_java_keyword(const char* s);

bool is_java_identifier_start(int cp);

bool is_java_identifier_part(int cp);

bool is_java_identifier(const char* s);

bool is_toplevel_class(const char* s);

std::string get_toplevel_class(const std::string& s);

#endif // JAVARULES_H
