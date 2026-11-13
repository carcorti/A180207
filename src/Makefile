# Canonical A180207 build. Copyright (c) 2026 Carlo Corti.
CC = gcc-13
CPPFLAGS = -DSOURCE_SHA='"$(shell sha256sum a180207.c | cut -d " " -f 1)"' -DMAKE_SHA='"$(shell sha256sum Makefile | cut -d " " -f 1)"'
CFLAGS = -std=c17 -O3 -march=znver4 -mtune=znver4 -flto -funroll-loops -fomit-frame-pointer -fopenmp -Wall -Wextra -Wpedantic -Wshadow -Wconversion -Wdouble-promotion -Wformat=2
LDLIBS = -lcrypto -lm
.PHONY: all clean
all: a180207
a180207: a180207.c Makefile
	$(CC) $(CPPFLAGS) $(CFLAGS) $< -o $@ $(LDFLAGS) $(LDLIBS)
clean:
	rm -f a180207
