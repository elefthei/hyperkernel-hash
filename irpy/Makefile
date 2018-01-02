#
# Copyright 2017 Hyperkernel Authors
#
# Licensed under the Apache License, Version 2.0 (the "License");
# you may not use this file except in compliance with the License.
# You may obtain a copy of the License at
#
#     http://www.apache.org/licenses/LICENSE-2.0
#
# Unless required by applicable law or agreed to in writing, software
# distributed under the License is distributed on an "AS IS" BASIS,
# WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
# See the License for the specific language governing permissions and
# limitations under the License.
#

# Try the latest version first
LLVM_CONFIG  := llvm-config-5.0
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_CONFIG  := llvm-config
endif
# Homebrew hides llvm here
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_CONFIG  := /usr/local/opt/llvm/bin/llvm-config
endif
ifeq ($(shell which $(LLVM_CONFIG) 2> /dev/null),)
LLVM_PREFIX  :=
else
LLVM_PREFIX  := "$(shell '$(LLVM_CONFIG)' --bindir)/"
endif
LIBDIR		= $(shell "$(LLVM_CONFIG)" --libdir)
LIBS		= $(shell "$(LLVM_CONFIG)" --libs)
SYSLIBS		= $(shell "$(LLVM_CONFIG)" --system-libs)
CXXFLAGS	= $(shell "$(LLVM_CONFIG)" --cxxflags)
CLANG		= $(shell "$(LLVM_CONFIG)" --bindir)/clang
IRPY_SRCS	= $(wildcard compiler/*.cc)
IRPY_OBJS	= $(patsubst %.cc,%.o,$(IRPY_SRCS))

ifeq ($(PROFILE_IRPY), 1)
IRPY_CFLAGS := -DPROFILER
else
IRPY_CFLAGS :=
endif

ifeq ($(DEBUG), 1)
IRPY_CFLAGS += -DLLVM_ENABLE_DUMP
else
IRPY_CFLAGS +=
endif

ifeq ($(PROFILE_IRPY), 1)
IRPY_LDFLAGS := -Wl,--no-as-needed -lprofiler -Wl,--as-needed
else
IRPY_LDFLAGS :=
endif

compiler/%.o: compiler/%.cc
	$(CXX) -o $@ -c $(CXXFLAGS) $(IRPY_CFLAGS) -Wall -g -O2 $<

compiler/irpy: $(IRPY_OBJS)
	$(CXX) $(IRPY_CFLAGS) $^ -L$(LIBDIR) $(LIBS) $(SYSLIBS) -g $(IRPY_LDFLAGS) -O2 -o "$@"

# Testing stuff

TEST_SRCS = $(wildcard test/*.c)
TEST_LL_O = $(subst test/,o.test/,$(patsubst %.c,%.ll,$(TEST_SRCS)))
TEST_LL  += $(patsubst %.ll,%_0.ll,$(TEST_LL_O))
TEST_LL  += $(patsubst %.ll,%_1.ll,$(TEST_LL_O))
TEST_LL  += $(patsubst %.ll,%_2.ll,$(TEST_LL_O))
TEST_PY   = $(patsubst %.ll,%.py,$(TEST_LL))
TEST_BIN  = $(patsubst %.ll,%,$(TEST_LL))

LIBIRPY_PY := $(wildcard libirpy/*.py)

TEST_LIBIRPY_PY := $(addprefix o.test/,$(LIBIRPY_PY:%=%))

o.test/%_0.ll: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -mno-sse -mno-sse2 -nostdlib -O0 -S -emit-llvm "$^" -o "$@"

o.test/%_1.ll: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -mno-sse -mno-sse2 -nostdlib -O1 -S -emit-llvm "$^" -o "$@"

o.test/%_2.ll: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -mno-sse -mno-sse2 -nostdlib -O2 -S -emit-llvm "$^" -o "$@"

o.test/%_0: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -O0 "$^" -o "$@"

o.test/%_1: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -O1 "$^" -o "$@"

o.test/%_2: test/%.c
	$(Q)$(MKDIR_P) $(@D)
	$(CLANG) -O2 "$^" -o "$@"

o.test/%.py: o.test/%.ll compiler/irpy
	$(Q)$(MKDIR_P) $(@D)
	./compiler/irpy "$<" > "$@"

o.test/test.py: test/test.py
	$(Q)$(MKDIR_P) $(@D)
	cp $^ $@

o.test/libirpy/%.py: libirpy/%.py
	$(Q)$(MKDIR_P) $(@D)
	$(LN_S) -f $(realpath $^) $@

test: o.test/test.py $(TEST_LIBIRPY_PY) $(TEST_LL) $(TEST_PY) $(TEST_BIN)
	cd irpy/o.test && python2 test.py $(ARGS)

clean:
	rm $(IRPY_OBJS) compiler/irpy

.SECONDARY: $(TEST_LL)
.PHONY: test
