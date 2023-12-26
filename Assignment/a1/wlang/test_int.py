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

import unittest

from . import ast, int, parser


class TestInt(unittest.TestCase):
    # cover int.py
    def test_one(self):
        prg1 = "x := 10; print_state"
        # test if, +, >, skip
        prg2 = "x := 10; skip; if x > 5 then x:= x + 1 else skip"
        # test while, -
        prg3 = "x := 14; while x > 12 do x:= x - 1"
        # test (), *, if then
        prg4 = "x := 10; if x = 10 and not false then x:= (x+10) * 2 else skip"
        # test >=, /, true
        prg5 = "x := 10; if x >= 5 or true then x:= x / 2 else skip"
        # test <=
        prg6 = "x := 10; if x <= 5 then x:= x + 1 else skip"
        # test <
        prg7 = "x := 10; if x < 9 and false then x:= x - 1"
        # test havoc
        prg8 = "x := -10; havoc x"
        prg_list = [prg1, prg2, prg3, prg4, prg5, prg6, prg7, prg8]
        value_list = [10,11,12,40,5,10,10,0]
        length_list = [1,1,1,1,1,1,1,1]
        for i in range(len(prg_list)):               
            # test parser
            ast1 = ast.parse_string(prg_list[i])
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
            # x is defined
            self.assertIn("x", st.env)
            self.assertEquals(st.env["x"], value_list[i])
            # no other variables in the state
            self.assertEquals(len(st.env), length_list[i])


    # test assume
    def test_assume(self):
        # test assume
        prg8 = "x := 10; assume x > 12"
        prg9 = "x := 10; assume x < 12"
        flag = 0
        try:
            ast1 = ast.parse_string(prg8)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
        except:
            flag = 1
        self.assertEquals(flag,1)   
        flag = 0 
        try:
            ast1 = ast.parse_string(prg9)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
        except:
            flag = 1
        self.assertEquals(flag,0)
    # test state repr
    def test_state_repr(self):
        flag = 0
        try:
            prg10 = "x := 1"
            ast1 = ast.parse_string(prg10)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
            repr(st)
        except:
            flag = 1
        self.assertEquals(flag,1)
    # test assert
    def test_assert(self):
        flag = 0
        try:
            prg = "x := 10; assert(x < 10)"
            ast1 = ast.parse_string(prg)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
        except:
            flag = 1
        self.assertEquals(flag,1)
        flag = 0
        try:
            prg = "x := 10; assert(x > 9)"
            ast1 = ast.parse_string(prg)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
            self.assertIsNotNone(st)
        except:
            flag = 1
        self.assertEquals(flag,0)

    def test_RelExp_err(self):
        prg = "if 2>1 then x := 1 else x:= 2"
        ast1 = ast.parse_string(prg)
        ast1.cond.op = "=="
        cond = ast1.cond
        interp = int.Interpreter()
        with self.assertRaises(Exception) as context:
            interp.visit_RelExp(cond)

    def test_int_main(self):
        with self.assertRaises(SystemExit) as context:
            int.main()
        

     # for parser.py test while with inv 
    def test_while_inv(self):
        prg = "x:=1; while x < 3 inv true do x:=x+1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        self.assertEquals(st.env["x"], 3)
        # no other variables in the state
    #######################################################################
    # cover ast.py
    # test ast.repr()
    def test_ast(self):
        prg = "x := -10"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        #self.assertIsNotNone(st)
        self.assertEquals(repr(ast1),"x := -10")
    
    # test stmList.equal and None
    def test_stmlist(self):
        prg = "x := 1; y := 1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertIsNotNone(st)
        self.assertTrue(ast1 == ast2) 

        # prg = "x := 1; y:=1"
        # ast1 = ast.parse_string(prg)
        # self.assertTrue(ast1 == ast1)

    # test skipsmt_equal
    def test_skipstmt(self):
        prg = "skip"
        ast1 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast1)
    
    # test assignment_smt equal
    def test_AsgnStmt(self):
        prg = "havoc x, y ; x := 1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2)   

    # test printstatesmt_equal
    def test_PrintStateStmt(self):
        prg = "print_state"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2) 
    
    # test while_smt equal
    def test_WhileStmt(self):
        prg = "while false do skip; y:=0; x := 2; while (x > 0) do {x:=x-1; y:=y+1}"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        self.assertIn("x", st.env)
        self.assertIn("y", st.env)
        self.assertEquals(st.env["x"], 0)
        self.assertEquals(st.env["y"], 2)
        self.assertEquals(len(st.env), 2)
        list_stmts = list(ast1.stmts)
        self.assertTrue(list_stmts[1] == list_stmts[1])
        ast2 = ast.parse_string(prg)
        self.assertTrue(str(ast1) == str(ast2))
    
    def test_WhileStmt_eq(self):
        prg = "x:= 1; while (x > 0) do x:=x-1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        self.assertIn("x", st.env)
        self.assertEquals(st.env["x"], 0)
        self.assertEquals(len(st.env), 1)
        list_stmts = list(ast1.stmts)
        self.assertTrue(list_stmts[1] == list_stmts[1])
        ast2 = ast.parse_string(prg)
        self.assertTrue(str(ast1) == str(ast2))
    

    # test assert equal
    def test_assertStmt(self):
        prg = "x:=1; assert x=1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        list_stmts = list(ast1.stmts)
        self.assertTrue(list_stmts[0] == list_stmts[0])

    # test assume_stmt equal
    def test_assumeStmt(self):
        prg = "x:=1; assume x = 1"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2) 

   # test havocsmt_equal
    def test_havocStmt(self):
        prg = "havoc x"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2) 
    
    # test Exp
    def test_ExpStmt(self):
        prg = "x := 12 * (5 + 1)"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2) 
    # test assert equal
    def test_assertStmt(self):
        prg = "assert true"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2) 

    # test if equal
    def test_ifStmt(self):
        prg = "if true then skip"
        ast1 = ast.parse_string(prg)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        ast2 = ast.parse_string(prg)
        self.assertTrue(ast1 == ast2)    

    def test_IfStmt (self):
        prg1 = "x := 1 ; if x = 1 then y := 0; if false then z := 0 else z:= 1 ; if x = 10 then z := 1"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        self.assertIn("x", st.env)
        self.assertIn("y", st.env)
        self.assertIn("z", st.env)
        self.assertEquals(st.env["x"], 1)
        self.assertEquals(st.env["y"], 0)
        self.assertEquals(st.env["z"], 1)
        self.assertEquals(len(st.env), 3)
        ast2 = ast.parse_string(prg1)
        self.assertTrue(str(ast1) == str(ast2))  
        
    # test exp[0] binary
    def test_exp0(self):
        ast1 = ast.Exp(['+','-'],[11,11])
        self.assertEquals(ast1.arg(0),11)
        self.assertTrue(ast1.is_binary())

    # test Constant
    def test_Const(self):
        prg = "100"
        ast1 = ast.Const(prg)
        self.assertTrue(ast1 == ast1) 
        self.assertEquals(ast1.__str__(),"100")
        self.assertEquals(repr(ast1),"'100'")
        self.assertTrue(hash(prg)==ast1.__hash__())
    
    # test IntVar
    def test_IntVar(self):
        prg = "x"
        ast1 = ast.IntVar(prg)
        self.assertTrue(ast1 == ast1) 
        self.assertEquals(ast1.__str__(),"x")
        self.assertEquals(repr(ast1),"'x'")
        self.assertTrue(hash(prg )== ast1.__hash__())

    # test parse_file in ast.py and the block statement in parse.py
    def test_readfile(self):
        file = open("./wlang/testing.txt","w")
        file.writelines(["{x := 10; y:=1};\n","print_state"])
        file.close()
        file1 = "./wlang/testing.txt"
        ast1 = ast.parse_file(file1)
        interp = int.Interpreter()
        st = int.State()
        self.assertIsNone(print(ast1))
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        # x is defined
        self.assertIn("x", st.env)
        # x is 10
        self.assertEquals(st.env["x"], 10)
        # no other variables in the state
        self.assertEquals(len(st.env), 2)

    # for parser.py with empty semantics to catch error
    def test_stmt(self):
        flag = 0
        prg = ""
        try:
            ast1 = ast.parse_string(prg)
            interp = int.Interpreter()
            st = int.State()
            st = interp.run(ast1, st)
        except:
            flag = 1
        self.assertEquals(flag,1)
    
    def test_AstVisitor (self):
        astVisitor = ast.AstVisitor()
        with self.assertRaises(Exception) as context:
            astVisitor.visit_IntVar(ast.IntVar('x'))

    def test_AstVisitor1(self):
        astVisitor = OwnVisitor()

        ast1 = ast.parse_string("x:=1;y:=x")
        self.assertTrue(astVisitor.visit_AsgnStmt(ast1) == None)

        ast1 = ast.parse_string("x:=1; if x < 2 then y := 1")
        self.assertTrue(astVisitor.visit_IfStmt(ast1) == None)
        
        ast1 = ast.parse_string("x:=1; while x < 2 do y := 1")
        self.assertTrue(astVisitor.visit_WhileStmt(ast1) == None)
        
        ast1 = ast.parse_string("x:=1; assert x < 2; y:=1")
        self.assertTrue(astVisitor.visit_AssertStmt(ast1) == None)
        
        ast1 = ast.parse_string("x:=1; assume x < 2")
        self.assertTrue(astVisitor.visit_AssumeStmt(ast1) == None)
        
        ast1 = ast.parse_string("havoc x, y, z")
        self.assertTrue(astVisitor.visit_HavocStmt(ast1) == None)

    def test_printVisitor(self):
        visitor = ast.PrintVisitor()
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)
        ast1.stmts = None
        printVisitor = ast.PrintVisitor()
        self.assertEquals(printVisitor.visit_StmtList(ast1), None)
        
        # prg1 = "x:=1"
        # ast1 = ast.parse_string(prg1)
        # interp = int.Interpreter()
        # st = int.State()
        # st = interp.run(ast1, st)
        # self.assertIsNotNone(st)
        # printVisitor = ast.PrintVisitor()
        # self.assertEquals(printVisitor.visit_StmtList(ast1), None)
        
        prg1 = "x:=1; skip"
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        ast1.stmts = [ast1.stmts[0]]
        printVisitor = ast.PrintVisitor()
        self.assertEquals(printVisitor.visit_StmtList(ast1, indent=0, no_brkt=False), None)
        self.assertEquals(visitor.visit(ast.SkipStmt()),None)
        self.assertEquals(visitor.visit(ast.BoolConst(True)),None)
        self.assertEquals(visitor.visit(ast.BoolConst(False)),None)

        # prg1 = "skip;skip;skip"
        # ast1 = ast.parse_string(prg1)
        # interp = int.Interpreter()
        # st = int.State()
        # st = interp.run(ast1, st)
        # self.assertIsNotNone(st)
        # ast1.stmts = [ast1.stmts[0]]
        # printVisitor = ast.PrintVisitor()
        # self.assertEquals(printVisitor.visit_StmtList(ast1, indent=0, no_brkt=False), None)
        # self.assertEquals(visitor.visit(ast.SkipStmt()),None)
        # self.assertEquals(visitor.visit(ast.BoolConst(True)),None)
        # self.assertEquals(visitor.visit(ast.BoolConst(False)),None)


        prg1 = "skip"
        # test parser
        ast1 = ast.parse_string(prg1)
        interp = int.Interpreter()
        st = int.State()
        st = interp.run(ast1, st)
        self.assertIsNotNone(st)
        visitor = ast.PrintVisitor()
        visitor.visit(ast1)
        # prg = "x := 10"
        # self.assertEquals(visitor.visit_StmtList(ast.Exp(prg)),None)
    
    ### test parser
    def test_parser_main(self):
        try:
            parser.main("./wlang/test1.prg")
        except Exception:
            pass
        try: 
            parser.main("./wlang/testing.prg")
        except Exception:
            pass
    


    # test lang buffer:
    def test_langbuffer(self):
        buffer = parser.WhileLangBuffer("")
        self.assertIsNotNone(buffer)
    # test whilelangsemantics in parser.py
    def test(self):
        lang = parser.WhileLangSemantics()
        prg = "x:=10; if x > 8 then x:= x - 1"
        ast1 = ast.parse_string(prg)
        self.assertEquals(lang.start(ast1),ast1)
        self.assertEquals(lang.stmt_list(ast1),ast1)
        self.assertEquals(lang.stmt(ast1),ast1)
        self.assertEquals(lang.asgn_stmt(ast1),ast1)
        self.assertEquals(lang.block_stmt(ast1),ast1)
        self.assertEquals(lang.skip_stmt(ast1),ast1)
        self.assertEquals(lang.print_state_stmt(ast1),ast1)
        self.assertEquals(lang.if_stmt(ast1),ast1)
        self.assertEquals(lang.while_stmt(ast1),ast1)
        self.assertEquals(lang.assert_stmt(ast1),ast1)
        self.assertEquals(lang.assume_stmt(ast1),ast1)
        self.assertEquals(lang.havoc_stmt(ast1),ast1)
        self.assertEquals(lang.var_list(ast1),ast1)
        self.assertEquals(lang.bexp(ast1),ast1)
        self.assertEquals(lang.bterm(ast1),ast1)
        self.assertEquals(lang.bfactor(ast1),ast1)
        self.assertEquals(lang.batom(ast1),ast1)
        self.assertEquals(lang.bool_const(ast1),ast1)
        self.assertEquals(lang.rexp(ast1),ast1)
        self.assertEquals(lang.rop(ast1),ast1)
        self.assertEquals(lang.aexp(ast1),ast1)
        self.assertEquals(lang.addition(ast1),ast1)
        self.assertEquals(lang.subtraction(ast1),ast1)
        self.assertEquals(lang.term(ast1),ast1)
        self.assertEquals(lang.mult(ast1),ast1)
        self.assertEquals(lang.division(ast1),ast1)
        self.assertEquals(lang.factor(ast1),ast1)
        self.assertEquals(lang.neg_number(ast1),ast1)
        self.assertEquals(lang.atom(ast1),ast1)
        self.assertEquals(lang.name(ast1),ast1)
        self.assertEquals(lang.number(ast1),ast1)
        self.assertEquals(lang.INT(ast1),ast1)
        self.assertEquals(lang.NAME(ast1),ast1)
        self.assertEquals(lang.NEWLINE(ast1),ast1)

    
    
 
class OwnVisitor(ast.AstVisitor):
    def __init__(self):
        pass
    def visit_Stmt(self, node, *args, **kwargs):
        pass