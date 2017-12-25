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
import argparse
import copy
import unittest
import inspect

import libirpy
import libirpy.util as util
import libirpy.solver as solver
import libirpy.ex as ex
import libirpy.itypes as itypes
from libirpy.datatypes import BitcastPointer

import pyimpl.impl as impl

import datatypes as dt
import z3
import spec

Solver = solver.Solver

def panic(ctx, *args, **kwargs):
    ue = ex.UnreachableException(ctx.path_condition[-1])
    ue.stacktrace = copy.deepcopy(ctx.stacktrace[-1])

def putchar(ctx, *args, **kwargs):
    return

def memcpy(ctx, dst, src, size):
    if isinstance(dst, BitcastPointer):
        dst = dst._ptr

    if isinstance(src, BitcastPointer):
        src = src._ptr

    # Same paranoid checks
    assert dst.type().is_pointer()
    assert src.type().is_pointer()

    assert dst.type().deref().is_array()
    assert src.type().deref().is_array()

    assert dst.type().deref().size() == src.type().deref().size()
    assert dst.type().deref().length() == src.type().deref().length()

    dst_start = dst.getelementptr(ctx, util.i64(0), util.i64(0))
    src_start = src.getelementptr(ctx, util.i64(0), util.i64(0))

    dst_end = dst.getelementptr(ctx, util.i64(0), util.i64(0))
    src_end = src.getelementptr(ctx, util.i64(0), util.i64(0))

    dst_start_path = dst_start.canonical_path()
    src_start_path = src_start.canonical_path()

    dst_end_path = dst_end.canonical_path()
    src_end_path = src_end.canonical_path()

    assert dst_start_path[-1].as_long() == src_start_path[-1].as_long()
    assert dst_end_path[-1].as_long() == src_end_path[-1].as_long()

    dst_tup, dst_start_args = dst._ref.build_field_tuple_and_path(
        ctx, dst_start_path)
    src_tup, src_start_args = src._ref.build_field_tuple_and_path(
        ctx, src_start_path)

    _, dst_end_args = dst._ref.build_field_tuple_and_path(ctx, dst_end_path)
    _, src_end_args = src._ref.build_field_tuple_and_path(ctx, src_end_path)

    dst_end_args[-1] += size
    src_end_args[-1] += size

    assert len(dst_start_args) == len(dst_end_args)
    assert len(dst_end_args) == len(src_end_args)

    dstfn = ctx['references'][dst._ref._name][dst_tup]
    srcfn = ctx['references'][src._ref._name][src_tup]

    # At this point we know that the src and dst are same-sized arrays.
    # They are both indexed starting from 0 up to length - 1.
    # So, we just do update the uf using an ite of the form
    # arg1 == dst_arg1, arg2 == dst_arg2, .. dst_argn_start <= arg1 < dst_argn_end

    def newf(*args):
        assert len(args) == len(dst_end_args)
        cond = []
        for a, b in zip(args[:-1], dst_start_args[:-1]):
            cond.append(a == b)

        cond.append(z3.UGE(args[-1], dst_start_args[-1]))
        cond.append(z3.ULT(args[-1], dst_end_args[-1]))

        cond = z3.And(*cond)

        srcargs = src_start_args[:-1] + [args[-1]]

        return util.If(cond, srcfn(*srcargs), dstfn(*args))

    ctx['references'][dst._ref._name][dst_tup] = newf

    return dst


def memset(ctx, ptr, val, size):
    val = z3.Extract(7, 0, val)

    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        ptr = ptr._ptr

    inner = ptr.type().deref()

    # We are memsetting an array whose inner type matches the size of the val
    assert inner.is_array()
    assert inner.deref().size() % val.size() == 0

    val = z3.Concat(*([val] * (inner.deref().size() / val.size())))

    if inner.deref().is_int():
        array_len = ptr.type().deref().length()

        dst_start = ptr.getelementptr(ctx, util.i64(0), util.i64(0))
        dst_end = ptr.getelementptr(
            ctx, util.i64(0), util.i64(array_len - 1))

        dst_start_path = dst_start.canonical_path()
        dst_end_path = dst_end.canonical_path()

        dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_start_path)
        _, dst_end_args = ptr._ref.build_field_tuple_and_path(
            ctx, dst_end_path)

        dstfn = ctx['references'][ptr._ref._name][dst_tup]

        def newf(*args):
            assert len(args) == len(dst_end_args)
            cond = []
            for a, b in zip(args[:-1], dst_start_args[:-1]):
                cond.append(a == b)

            cond.append(z3.UGE(args[-1], dst_start_args[-1]))
            cond.append(z3.ULE(args[-1], dst_end_args[-1]))

            cond = z3.And(*cond)

            return util.If(cond, val, dstfn(*args))

        ctx['references'][ptr._ref._name][dst_tup] = newf
        return ptr

    else:
        raise NotImplementedError(
            "Don't know how to memset {!r}".format(inner))


def bzero(ctx, ptr, size):
    size = size.as_long()

    # If we're passed a bitcasted pointer we just check if the write size is a
    # multiple of the underlying types write size, then we can just ignore the bitcast.
    if isinstance(ptr, BitcastPointer):
        ptr = ptr._ptr

    inner = ptr.type().deref()

    if inner.is_int():
        assert size * 8 <= 64
        ptr.write(ctx, z3.BitVecVal(0, size * 8))
    elif inner.is_struct():
        assert inner.size() / \
            8 == size, "Can not partially bzero a struct: {} v {}".format(
                inner.size() / 8, size)

        for i, field in enumerate(inner.fields()):
            subptr = ptr.getelementptr(ctx, util.i64(0), util.i64(i),
                                       type=itypes.PointerType(field))
            bzero(ctx, subptr, z3.simplify(z3.BitVecVal(field.size() / 8, 64)))
    elif inner.is_array():
        write_size = inner.deref().size()

        if inner.deref().is_int():

            array_len = ptr.type().deref().length()

            dst_start = ptr.getelementptr(ctx, util.i64(0), util.i64(0))
            dst_end = ptr.getelementptr(
                ctx, util.i64(0), util.i64(array_len - 1))

            dst_start_path = dst_start.canonical_path()
            dst_end_path = dst_end.canonical_path()

            dst_tup, dst_start_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_start_path)
            _, dst_end_args = ptr._ref.build_field_tuple_and_path(
                ctx, dst_end_path)

            dstfn = ctx['references'][ptr._ref._name][dst_tup]

            def newf(*args):
                assert len(args) == len(dst_end_args)
                cond = []
                for a, b in zip(args[:-1], dst_start_args[:-1]):
                    cond.append(a == b)

                cond.append(z3.UGE(args[-1], dst_start_args[-1]))
                cond.append(z3.ULE(args[-1], dst_end_args[-1]))

                cond = z3.And(*cond)

                return util.If(cond, z3.BitVecVal(0, write_size), dstfn(*args))

            ctx['references'][ptr._ref._name][dst_tup] = newf

        else:
            raise NotImplementedError(
                "Don't know how to bzero {!r}".format(inner))

    else:
        raise NotImplementedError("Don't know how to bzero {!r}".format(inner))


def ms_to_cycles(ctx, ms):
    return util.FreshBitVec('cycles', dt.uint64_t)
ms_to_cycles.read = lambda *args: ms_to_cycles


def pdb(ctx, *args):
    from ipdb import set_trace
    set_trace()
    return util.i64(0)
pdb.read = lambda *args: pdb


def syslog(ctx, *args):
    pass
syslog.read = lambda *args: syslog


class ImplBase(unittest.TestCase):

    def _prove(self, cond, pre=None, return_model=False, minimize=True):
        if minimize:
            self.solver.push()
        self.solver.add(z3.Not(cond))

        res = self.solver.check()
        if res != z3.unsat:
            if not minimize and not return_model:
                self.assertEquals(res, z3.unsat)

            model = self.solver.model()
            if return_model:
                return model

            print "Could not prove, trying to find a minimal ce..."
            assert res != z3.unknown
            if z3.is_and(cond):
                self.solver.pop()
                # Condition is a conjunction of some child clauses.
                # See if we can find something smaller that is sat.

                if pre is not None:
                    ccond = sorted(
                        zip(cond.children(), pre.children()), key=lambda x: len(str(x[0])))
                else:
                    ccond = sorted(cond.children(), key=lambda x: len(str(x)))

                for i in ccond:
                    self.solver.push()
                    if isinstance(i, tuple):
                        self._prove(i[0], pre=i[1])
                    else:
                        self._prove(i)
                    self.solver.pop()

            print "Can not minimize condition further"
            if pre is not None:
                print "Precondition"
                print pre
                print "does not imply"
            print cond
            self.assertEquals(model, [])

def newctx():
    ctx = libirpy.newctx()
    # If we don't need the values of any constants we don't have to
    # initialize them, slightly faster execution time.
    ctx.eval.declare_global_constant = ctx.eval.declare_global_variable
    libirpy.initctx(ctx, impl)

    ctx.globals['@panic'] = panic
    ctx.globals['@bzero'] = bzero
    ctx.globals['@memset'] = memset
    ctx.globals['@memcpy'] = memcpy
    ctx.globals['@putchar'] = putchar
    ctx.globals['@pdb'] = pdb
    ctx.globals['@syslog'] = syslog
    ctx.globals['@ms_to_cycles'] = ms_to_cycles

    return ctx

class Impl(ImplBase):
    def setUp(self):
        self.ctx = newctx()
        self.state = dt.ImplState()

        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)

        self._pre_state = spec.state_equiv(self.ctx, self.state)
        self.ctx.add_assumption(spec.impl_invariants(self.ctx))
        self.solver.add(self._pre_state)

    def tearDown(self):
        if isinstance(self.solver, solver.Solver):
            del self.solver

    # use this to test no-fault case
    def test_preempt(self):
        with self.assertRaises(util.NoReturn):
            self.ctx.call('@preempt')
        newstate = spec.switch_proc(self.state, pid)[1]
        self._prove(z3.Exists([pid], spec.state_equiv(self.ctx, newstate)))

    # use this to test faulty case
    def test_fault(self):
        with self.assertRaises(util.NoReturn):
            self.ctx.call('@fault')
        pid = util.FreshBitVec('pid', dt.pid_t)
        s = self.state.copy()
        s.procs[s.current].killed = z3.BoolVal(True)
        newstate = spec.switch_proc(s, pid)[1]
        self._prove(z3.Exists([pid], spec.state_equiv(self.ctx, newstate)))

    syscalls_generic = _syscalls


# Test cases to check if python and c versions of implementation invariants match
class PyImplInvs(HV6Base):
    def setUp(self):
        self.solver = Solver()
        self.solver.set(AUTO_CONFIG=False)
        self.ctx = newctx()

    def test_inv_py_imply_c(self):
        self._prove(z3.Implies(spec.impl_invariants_py(
            self.ctx), spec.impl_invariants_c(self.ctx)))

    def test_inv_c_imply_py(self):
        self._prove(z3.Implies(spec.impl_invariants_c(
            self.ctx), spec.impl_invariants_py(self.ctx)))

if __name__ == "__main__":
    parser = argparse.ArgumentParser()

    parser.add_argument('--interactive', type=bool, nargs='?',
            default=False, const=True)
    parser.add_argument('--model-hi', type=bool, nargs='?',
            default=False, const=True)
    args, unknown = parser.parse_known_args(sys.argv)

    INTERACTIVE = args.interactive
    MODEL_HI = args.model_hi

    del sys.argv[:]
    sys.argv.extend(unknown)

    if INTERACTIVE:
        Solver = z3.Solver

    print "Using z3 v" + '.'.join(map(str, z3.get_version()))

    unittest.main()
