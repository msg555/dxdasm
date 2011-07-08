#include "mutf8.h"

#include <cstdio>

unsigned int mutf8NextCodePoint(char const** s) {
  unsigned char head = *(*s)++;
  if(head >> 7 == 0x00) {
    // A single byte code point.
    return head;
  } else if(head >> 5 == 0x06) {
    // Two byte code point.
    unsigned char n1 = *(*s)++;
    if(n1 >> 6 != 0x02) {
      fprintf(stderr, "error decoding string\n");
      fflush(stderr);
      return 0;
    }
    return (head & 0x1F) << 6 | n1 & 0x3F;
  } else if(head >> 4 == 0x0E) {
    // Three byte code point.
    unsigned char n1 = *(*s)++;
    if(n1 >> 6 != 0x02) {
      fprintf(stderr, "error decoding string\n");
      fflush(stderr);
      return 0;
    }
    unsigned char n2 = *(*s)++;
    if(n2 >> 6 != 0x02) {
      fprintf(stderr, "error decoding string\n");
      fflush(stderr);
      return 0;
    }
    return (head & 0x1F) << 12 | (n1 & 0x3F) << 6 | n2 & 0x3F;
  } else {
    fprintf(stderr, "error decoding string\n");
    fflush(stderr);
    return 0;
  }
}
