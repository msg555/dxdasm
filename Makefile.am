AUTOMAKE_OPTIONS = subdir-objects
ACLOCAL_AMFLAGS = ${ACLOCAL_FLAGS}

bin_PROGRAMS = dxdasm dxreasm

dxdasm_LDFLAGS = -ldxcut
dxdasm_SOURCES = \
  src/dxdasm.cpp \
  src/dasmcl.cpp \
  src/annotations.cpp \
  src/javarules.cpp \
  src/mutf8.cpp

dxreasm_LDFLAGS = -ldxcut
dxreasm_SOURCES = \
  src/dxreasm.cpp \
  src/dasmcl.cpp \
  src/annotations.cpp \
  src/javarules.cpp \
  src/mutf8.cpp
