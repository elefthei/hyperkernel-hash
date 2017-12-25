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

import sys
import z3

import libirpy
from libirpy import util
from hv6py.base import BaseStruct, Struct, Map

def _populate_enums():
    module = sys.modules[__name__]
    ctx = libirpy.newctx()
    import hv6py.kernel.impl as hv6
    hv6._init_metadata(ctx)
    for k, v in ctx.metadata.items():
        if isinstance(v, tuple) and v[0] == 'DICompositeType':
            if v[1].get('tag') == 'DW_TAG_enumeration_type':
                name = v[1].get('name')
                size = v[1].get('size')
                elements = v[1].get('elements')

                if name is None or size is None or elements is None:
                    continue

                setattr(module, name + '_t', z3.BitVecSort(size))
                enum = {}

                for element in ctx.metadata.get(elements):
                    element = ctx.metadata.get(element)
                    assert element[0] == 'DIEnumerator'
                    element_name = element[1].get('name')
                    element_value = element[1].get('value')
                    enum[element_name] = z3.BitVecVal(element_value, size)

                setattr(module, name, type(name, (), enum))


# Fetch the enums from the llvm metadata and populate this module with their values
_populate_enums()

bool_t = z3.BoolSort()
size_t = z3.BitVecSort(64)
ssize_t = z3.BitVecSort(64)

# Unsinged ints
uint64_t = z3.BitVecSort(64)
uint32_t = z3.BitVecSort(32)
uint16_t = z3.BitVecSort(16)
uint8_t = z3.BitVecSort(8)
uchar_t = z3.BitVecSort(8)

# Signed ints
int64_t = z3.BitVecSort(64)
int32_t = z3.BitVecSort(32)
int16_t = z3.BitVecSort(16)
int8_t = z3.BitVecSort(8)
char_t = z3.BitVecSort(8)

# Files and pointers
fd_t = z3.BitVecSort(32)
pte_t = z3.BitVecSort(64)
uintptr_t = z3.BitVecSort(64)

"""
Global hash table state for specification
"""
class ImplState(BaseStruct):
    # Array of string -> string
    # or ArraySort(BitVecSort(8)) -> ArraySort(BitVecSort(8))
    # table = Map()
    foo = 0

