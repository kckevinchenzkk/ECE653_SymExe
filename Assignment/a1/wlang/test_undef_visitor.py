import unittest

from . import ast, undef_visitor


class TestUndefVisitor(unittest.TestCase):
    def test1(self):
        prg1 = "x := 10; y := z"
        ast1 = ast.parse_string(prg1)
        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())
    
    def test_none(self):
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)
        ast1.stmts = None
        uv = undef_visitor.UndefVisitor()
        self.assertEquals(uv.visit_StmtList(ast1), None)
        self.assertEquals(uv.visit_Stmt(None), None)

    def test_assume(self):
        prg1 = "x := 10; assume x > z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())

    def test_assert(self):
        prg1 = "x := 10; assert x > z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)

        #print(uv.get_undefs)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())
    
    def test_if(self):
        prg1 = "x := 10; if x > z then skip else skip"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)

        #print(uv.get_undefs)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())

    def test_while(self):
        prg1 = "x := 10; while x > z do skip"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)

        #print(uv.get_undefs)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())
    
    def test_while(self):
        prg1 = "x := 10; while x > z inv true do skip"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)

        #print(uv.get_undefs)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())
    
    def test_havoc(self):
        prg1 = "x := 10; havoc y; assume y>z"
        ast1 = ast.parse_string(prg1)

        uv = undef_visitor.UndefVisitor()
        uv.check(ast1)

        #print(uv.get_undefs)
        # UNCOMMENT to run the test
        self.assertEquals (set ([ast.IntVar('z')]), uv.get_undefs ())
    
