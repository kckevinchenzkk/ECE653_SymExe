# The MIT License (MIT)
# Copyright (c) 2016 Arie Gurfinkel

# Permission is hereby granted, free of charge, to any person obtaining
# a copy of this software and associated documentation files (the
# "Software"), to deal in the Software without restriction, including
# without limitation the rights to use, copy, modify, merge, publish,
# distribute, sublicense, and/or sell copies of the Software, and to
# permit persons to whom the Software is furnished to do so, subject to
# the following conditions:

# The above copyright notice and this permission notice shall be
# included in all copies or substantial portions of the Software.

# THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND,
# EXPRESS OR IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF
# MERCHANTABILITY, FITNESS FOR A PARTICULAR PURPOSE AND
# NONINFRINGEMENT. IN NO EVENT SHALL THE AUTHORS OR COPYRIGHT HOLDERS BE
# LIABLE FOR ANY CLAIM, DAMAGES OR OTHER LIABILITY, WHETHER IN AN ACTION
# OF CONTRACT, TORT OR OTHERWISE, ARISING FROM, OUT OF OR IN CONNECTION
# WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE SOFTWARE.
import traceback
import unittest
import z3
from . import ast, sym
# from unittest.mock import patch
# import importlib
import subprocess
from wlang import sym 
import wlang

class TestSym (unittest.TestCase):
    
    # Testing havoc assume and assert and throw error
    def test_one(self):
        prg1 = "havoc x; assume x >= 10; assert x <= 15"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    def test_assert_vio(self):
        prg1 = "havoc x; assume x >= 10; assert x < 10"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 0)
    def test_assert_stmt_list_none(self):
        prg1 = "while false do skip"
        ast1 = ast.parse_string(prg1)
        ast1.stmts = None
        engine = sym.SymExec()
        st = sym.SymState()
        self.assertIsNone(engine.visit_StmtList(ast1, state = st))
    
    # Testing havoc assume and assert and without error
    def test_two(self):
        prg1 = "havoc x; assume x > 10; assert x > 9"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    #Testing AExp
    def test_three(self):
        prg1 = "x := 10; y := 10; z := x + y; z := x - y; a := x * y; b := x/y"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    # Testing BExp
    def test_four(self):
        prg1 = "havoc x; x := 10; if not x = 10 or true then skip"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    def test_if_stmt(self):
        prg1 = "havoc a, b, x, y; if b < 0 then {if a < 0 then y := 1}; assert(not(x = 3))"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 3)
        prg1 = "havoc x, y; if x > 0 then y := 0 else skip"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 2)
    # Testing BExp
    def test_five(self):
        prg1 = "havoc x; x := 10; if x < 5 and true then skip else x:= 20"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    # Testing while
    def test_six(self):
        prg1 = "x := 10; while x < 18 do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    # Testing while
    def test_seven(self):
        prg1 = "havoc x;  x := 10; while x < 9 do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    
    def test_eight(self):
        prg1 = "havoc x; x := 1; if x >= 0 or false then x := x/1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)
    
    def test_nine(self):
        prg1 = "havoc x; while not x = 0 do x:= x-1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)
    def test_ten(self):
        prg1 = "havoc x; if x < 10 then {x := x + 1; x:=-1} else {x := 1; x := x/100}; x := x - 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 2)
    # def test_11(self):
    #     prg1 = "havoc x; while x < 10 do {x := 1; x := x/100}; x := x - 1; print_state"
    #     ast1 = ast.parse_string(prg1)
    #     engine = sym.SymExec()
    #     st = sym.SymState()
    #     out = [s for s in engine.run(ast1, st)]
    #     self.assertEquals(len(out), 1)

    def test_invalid_relational_operator(self):
        x_var = ast.IntVar(name='x')
        st = sym.SymState()
        st.env['x'] = z3.Int('x') 
        # Create a RelExp with an invalid operator
        invalid_rel_exp = ast.RelExp(op='InvalidOp', lhs=x_var, rhs=ast.IntConst(val=10))
        engine = sym.SymExec()
        with self.assertRaises(AssertionError):
            engine.visit_RelExp(invalid_rel_exp, state=st)

    def test_unsupported_boolean_operator(self):
        unsupported_bexp = ast.BExp(op='unsupported_op', args=[ast.BoolConst(val=True)])
        st = sym.SymState()
        engine = sym.SymExec()
        with self.assertRaises(AssertionError):
            engine.visit_BExp(unsupported_bexp, state=st)

    def test_unsupported_arithmetic_operator(self):
        unsupported_aexp = ast.AExp(op='unsupported_op', args=[
            ast.IntConst(val=1), 
            ast.IntConst(val=2)
        ])
        st = sym.SymState()
        engine = sym.SymExec()
        with self.assertRaises(AssertionError):
            engine.visit_AExp(unsupported_aexp, state=st)
            
    def test_inv(self):
        prg1 = "havoc n; assume n >= 0; x := 1; i := 2; while i <= n inv (i <= n + 1) do {x := x; i := i + 1}"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 11)

    def test_inv_e(self):
        prg1 = "x := 10; while x < 18 do x := x + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        self.assertEquals(len(out), 1)

    def test_while_with_unsatisfiable_inv(self):
        # The invariant "i > n + 1" contradicts the loop condition "i <= n"
        # when combined with the assumption "n >= 0"
        prg1 = "havoc n; assume n >= 0; i := 1; while i <= n inv (i > n + 1) do i := i + 1"
        ast1 = ast.parse_string(prg1)
        engine = sym.SymExec()
        st = sym.SymState()
        out = [s for s in engine.run(ast1, st)]
        # Expecting the loop to result in an error state due to the unsatisfiable invariant
        self.assertFalse(len(out))
        
    #Test case with a solver
    def test_symstate_with_solver(self):
        custom_solver = z3.Solver()
        state = sym.SymState(solver=custom_solver)
        self.assertIs(state._solver, custom_solver)

    # def test_fail(self):
    #     prg1 = "i := 0;while i < 5 do{  i := i + 1;  print_state;  j := 0;  while j < 3 do  { j := j + 1 };  j := 0};print_state;assert i = 4"
    #     out = []
    #     try:
    #         ast1 = ast.parse_string (prg1)
    #         sym = wlang.sym.SymExec ()
    #         st = wlang.sym.SymState ()
    #         out = [s for s in sym.run (ast1, st) if not s.is_error()]
    #     except:
    #         traceback.print_exc()
    #     self.assertEqual (len(out), 0)

    def test_2_loop (self):
        # 3 output states for 3 path (one for X = 3, one for X = 4 and one for any X &gt; 5)
        prg1 = "havoc x; assume x > 2; while x < 5 do x := x + 1; print_state"
        out = []
        try:
            ast1 = ast.parse_string (prg1)
            sym = wlang.sym.SymExec ()
            st = wlang.sym.SymState ()
            out = [s for s in sym.run (ast1, st) if not s.is_error()]
        except:
            traceback.print_exc()
        self.assertEqual(len(out), 3)
    def test_1_loop (self):
        # 3 output states for 3 path (one for X = 3, one for X = 4 and one for any X &gt; 5)
        prg1 = "havoc x; x := 3 ; while x < 5 do x := x + 1; print_state"
        out = []
        try:
            ast1 = ast.parse_string (prg1)
            sym = wlang.sym.SymExec ()
            st = wlang.sym.SymState ()
            out = [s for s in sym.run (ast1, st) if not s.is_error()]
        except:
            traceback.print_exc()
        self.assertEqual(len(out), 1)







    # #Testing divergence
    # def test_diverge(self):
    #     prg1 = "havoc x; c := 1; while c < 5 do {c:=c+1;if x < -100 then {f := x + 1; x := x/100 + f}; if x < -1000 then {f := 2 * x; x := x/10 * f + x}; if x < 1000 then {f := 3 / x;" \
    #            " x := x * f+ 10}; if x > 0 then {f := x /4; x := x*5/f}; if x >= 10 then {f := 5+x; x := x-20*f}; if x = 100 then {f := 6-x; x := 100/f}} "
    #     ast1 = ast.parse_string(prg1)
    #     engine = sym.SymExec()
    #     st = sym.SymState()
    #     out = [s for s in engine.run(ast1, st)]
    #     self.assertEquals(len(out), 1)
    