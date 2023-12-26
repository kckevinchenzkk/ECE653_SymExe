import unittest

from . import ast, stats_visitor


class TestStatsVisitor(unittest.TestCase):
    def test_one(self):
        prg1 = "x := 10; print_state"
        ast1 = ast.parse_string(prg1)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)

    def test_ifStmt(self):
        prg = "x := 10; if x > 10 then x:=x-1 else x:=x+1"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 4)
        self.assertEquals(sv.get_num_vars(), 1)
    
    def test_whilefStmt_inv(self):
        prg = "x := 10; while x < 12 inv true do x := x - 1"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 3)
        self.assertEquals(sv.get_num_vars(), 1)
    
    def test_whilefStmt(self):
        prg = "x := 10; while x < 12 do x := x - 1"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 3)
        self.assertEquals(sv.get_num_vars(), 1)
    
    def test_assert(self):
        prg = "x := 10; assert x < 9"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)
    
    def test_assume(self):
        prg = "x := 10; assume x < 10"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 2)
        self.assertEquals(sv.get_num_vars(), 1)
    
    def test_Havoc(self):
        prg = "x := 10; y:=1; havoc x,y"
        ast1 = ast.parse_string(prg)
        sv = stats_visitor.StatsVisitor()
        sv.visit(ast1)
        # UNCOMMENT to run the test
        self.assertEquals(sv.get_num_stmts(), 3)
        self.assertEquals(sv.get_num_vars(), 2)

    def test_visit_StmtList_None(self):
        prg1 = "x := 1"
        ast1 = ast.parse_string(prg1)
        ast1.stmts = None
        sv = stats_visitor.StatsVisitor()
        self.assertEquals(sv.visit_StmtList(ast1), None)
    
    def test_main_stats_visitor(self):
        with self.assertRaises(Exception) as context:
            stats_visitor.main()