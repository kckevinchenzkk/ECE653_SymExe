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

import sys

import io 
import z3
import random, copy
from functools import reduce
from . import ast, int
from .undef_visitor import UndefVisitor


class Concolic_State(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.sym_env = dict()
        self.con_env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concrete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        #st = int.State()
        st = dict()
        for (k, v) in self.sym_env.items():
            st[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = Concolic_State()
        child.sym_env = dict(self.sym_env)
        child.con_env = dict(self.con_env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        buf.write('sym: ')
        for k, v in self.sym_env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('con: ')
        for k, v in self.con_env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class Concolic_Exec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        kwargs = dict()
        kwargs["state"] = state
        kwargs["mode"] = "con"
        args = []
        res = self.visit(ast, *args, **kwargs)
        return res
        # return [st for st in res]
        # res = self.visit(ast, state=state, mode="con")
        # return [st["state"] for st in res]
                
    # def visit_BoolRef(self, node, *args, **kwargs):
    #     # For BoolRef nodes, just return the node itself
    #     return node

    def visit_IntVar(self, node, *args, **kwargs):
        #print(kwargs)
        if (kwargs["mode"] == "sym"):
            return kwargs['state'].sym_env[node.name]
        else:
            #return node.name
            return kwargs['state'].con_env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        if (kwargs["mode"] == "sym"):
            return z3.BoolVal(node.val)
        else:
            return node.val
        
    def visit_IntConst(self, node, *args, **kwargs):
        if (kwargs["mode"] == "sym"):
            return z3.IntVal(node.val)
        else:
            return node.val

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        # if node.op == ">":
        else:
            return lhs > rhs
        #assert False
        
    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None
        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            if (kwargs["mode"] == "sym"):
                return z3.Not(kids[0])
            else:
                return not kids[0]

        if node.op == "and":
            if (kwargs["mode"] == "sym"):
                fn = lambda x, y: z3.And(x,y)
            else:
                fn = lambda x, y: x and y
        if node.op == "or":
            if (kwargs["mode"] == "sym"):
                fn = lambda x, y: z3.Or(x,y)
            else:
                fn = lambda x, y: x or y
        assert fn is not None
        if (kwargs["mode"] == "sym"):
            return z3.simplify(reduce(fn, kids))
        else:
            return reduce(fn, kids)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None
        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y
        #elif node.op == "/":
        else:
            fn = lambda x, y: x / y
        assert fn is not None
        if (kwargs["mode"] == "sym"):
            return z3.simplify(reduce(fn, kids))
        else:
            return reduce(fn, kids)

    def visit_SkipStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        return [state]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        print(state)
        return [state]


    def visit_AsgnStmt(self, node, *args, **kwargs):
    
        state = kwargs["state"]
        kwargs["mode"] = "sym"
        state.sym_env[node.lhs.name] = \
        self.visit(node.rhs, *args, **kwargs)
        kwargs["mode"] = "con"
        state.con_env[node.lhs.name] = self.visit(node.rhs, *args, **kwargs)        


        return [state]
    # def visit_AsgnStmt(self, node, *args, **kwargs):
    #     st = kwargs["state"]
    #     kwargs["mode"] == "sym"
    #     st.sym_env[node.lhs.name] = self.visit(node.rhs, *args, **kwargs)
    #     # for st in kwargs["state_in_progress"]:
    #         # kwargs["state"] = st 
    #     kwargs["mode"] == "con"
    #     st.con_env[node.lhs.name] = self.visit(node.rhs, *args, **kwargs)
    #     kwargs["state"] = st
    #     return [kwargs]
    
    def visit_IfStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        kwargs["mode"] = "sym"
        cond_sym = self.visit(node.cond, *args, **kwargs)

        kwargs["mode"] = "con"
        try:
            cond_con = z3.simplify(self.visit(node.cond, *args, **kwargs))
        except:
            cond_con = self.visit(node.cond, *args, **kwargs)

        curr_state, new_state = st.fork() #deepcopy
        out = []
        curr_state.add_pc(cond_sym)
        new_state.add_pc(z3.Not(cond_sym))

        true_branch = True
        #---------------------------------------------
        # concrete evaluate if stmt first
        if cond_con:
            true_branch = True
            #kwargs["state"] = curr_state
            st1 = self.visit(node.then_stmt, *args, state = curr_state)
            out.extend(st1)
        # conrete takes false
        else:
            true_branch = False
            #kwargs["state"] = new_state
            if node.has_else():
                st2 = self.visit(node.else_stmt, *args, state = new_state)
                out.extend(st2)
            else: #no else
                out.extend([new_state])
        #-----------------------------------------------
        # Then symbolic evaluate the branch not taken
        #kwargs["mode"] == "sym"
        if true_branch:
            if not new_state.is_empty():# if SAT
                if node.has_else():  
                    new_state_sym = self.visit(node.else_stmt, *args, state = new_state)
                    #update concrete vars
                    for state in new_state_sym:
                        state.con_env = state.pick_concrete()
                    out.extend(new_state_sym)
                else:
                    new_state.con_env = new_state.pick_concrete()
                    out.extend([new_state])
            else: # if not SAT
                new_state.mk_error()
                out.extend([new_state])
        else: # take the true branch symbolically
            if not curr_state.is_empty(): # if SAT
                curr_state_sym = self.visit(node.then_stmt, *args, state = curr_state)
                for state in curr_state_sym:
                    state.con_env = state.pick_concrete()
                out.extend(curr_state_sym)
            else:# if UNSAT
                curr_state.mk_error()
                out.extend([curr_state])
        return out

    
    def visit_WhileStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        out = []
        true_branch = None
        counter = 0
        if len(args) != 0:
            counter = args[0]
        if counter < 10:
            kwargs["mode"] = "sym"
            cond_sym = self.visit(node.cond, *args, **kwargs)
            kwargs["mode"] = "con"
            try:
                cond = z3.simplify(self.visit(node.cond, *args, **kwargs))
            except:
                cond = self.visit(node.cond, *args, **kwargs)
            #cond = self.visit(node.cond, *args, **kwargs)
            curr_state, new_state = st.fork()
            curr_state.add_pc(cond_sym)
            new_state.add_pc(z3.Not(cond_sym))
            if cond:
                true_branch = True
                st1 = self.visit(node.body, 0, state=curr_state)
                sts_new = []
                for i in range(len(st1)):
                    if not st1[i].is_error():
                        sts_new.extend(self.visit_WhileStmt(node, counter + 1, state=st1[i]))    
                st1 = sts_new
                out = st1
            else:
                true_branch = False
                out.extend([new_state])
            if true_branch:
                if not new_state.is_empty():
                    new_state.con_env = new_state.pick_concrete()
                    out.extend([new_state])
                else:
                    new_state.mk_error()
                    out.extend([new_state])
            else:
                if not curr_state.is_empty():
                    st1 = self.visit(node.body, 0, state=curr_state)
                    sts_new = []
                    for i in range(len(st1)):
                        if not st1[i].is_error():
                            sts_new.extend(self.visit_WhileStmt(node, counter + 1, state=st1[i]))
                    st1 = sts_new
                    out.extend(st1)
                else:
                    curr_state.mk_error()
                    out.extend([curr_state])
            return out
        return [st]

    def visit_AssertStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        kwargs["mode"] = "sym"
        cond_sym = self.visit(node.cond, *args, **kwargs)

        kwargs["mode"] = "con"
        try:
            cond_con = z3.simplify(self.visit(node.cond, *args, **kwargs))
        except:
            cond_con = self.visit(node.cond, *args, **kwargs)

        true_state, false_state = st.fork ()
        false_state.add_pc (z3.Not(cond_sym))
        true_state.add_pc (cond_sym)
        out = []
        true_branch = True
        # CONCRETEly evaluate assert first 
        if cond_con:
            true_branch = True
            out.append(true_state)
        else:
            true_branch = False
            false_state.mk_error()
            print("Assertion error: " + str(node))
            out.append(false_state)


        kwargs["mode"] = "sym"
        # then symbolical evaluate the branch not taken
        if true_branch: # need to take false in sym
            # if not false_state.is_empty():
            false_state.mk_error()
            print("Assertion error: " + str(node))
            out.append(false_state)
        else:# need to take true branch in sym
            if not true_state.is_empty():
                true_state.con_env = true_state.pick_concrete()
            else:
                true_state.mk_error()
                print("Assertion error: " + str(node))
            out.append(true_state)
        return out

    def visit_AssumeStmt(self, node, *args, **kwargs):
        kwargs["mode"] = "sym"
        cond_sym = self.visit(node.cond, *args, **kwargs)
        kwargs["mode"] = "con"
        try:
            cond = z3.simplify(self.visit(node.cond, *args, **kwargs))
        except:
            cond = self.visit(node.cond, *args, **kwargs)
        st = kwargs["state"]
        st.add_pc (cond_sym)
        if cond:
            return [st]
        else:
            if not st.is_empty():
                st.con_env = st.pick_concrete()
            else:
                st.mk_error()
            return [st]



    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        #print(st)
        # for st in kwargs["state_in_progress"]: 
        for v in node.vars:
            # assign 0 as the default value
            st.con_env[v.name] = random.randint(0, 100)
            st.sym_env[v.name] = z3.FreshInt(str(v.name).upper())
        return [st]


    def visit_StmtList(self, node, *args, **kwargs):
        if node.stmts is None:
            return
        #temp_kwargs = kwargs.copy()
        state_dict = [kwargs["state"]]
        for stmt in node.stmts:
            state_dict_new = []
            for state in state_dict:
                new_states = self.visit(stmt, state=state)
                for new_state in new_states:
                    if not new_state.is_error():
                        state_dict_new.extend([new_state])
            state_dict = state_dict_new
        return state_dict

class SymState_incremental(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.env = dict()
        # path condition
        self.path = list()
        self._solver = solver
        if self._solver is None:
            self._solver = z3.Solver()

        # true if this is an error state
        self._is_error = False

    def add_pc(self, *exp):
        """Add constraints to the path condition"""
        self.path.extend(exp)
        self._solver.append(exp)

    def is_error(self):
        return self._is_error

    def mk_error(self):
        self._is_error = True

    def is_empty(self):
        """Check whether the current symbolic state has any concrete states"""
        res = self._solver.check()
        return res == z3.unsat

    def pick_concrete(self):
        """Pick a concrete state consistent with the symbolic state.
           Return None if no such state exists"""
        res = self._solver.check()
        if res != z3.sat:
            return None
        model = self._solver.model()
        st = int.State()
        for (k, v) in self.env.items():
            st.env[k] = model.eval(v)
        return st

    def fork(self):
        """Fork the current state into two identical states that can evolve separately"""
        child = SymState_incremental()
        child.env = dict(self.env)
        child.add_pc(*self.path)

        return (self, child)

    def __repr__(self):
        return str(self)

    def to_smt2(self):
        """Returns the current state as an SMT-LIB2 benchmark"""
        return self._solver.to_smt2()

    def __str__(self):
        buf = io.StringIO()
        for k, v in self.env.items():
            buf.write(str(k))
            buf.write(': ')
            buf.write(str(v))
            buf.write('\n')
        buf.write('pc: ')
        buf.write(str(self.path))
        buf.write('\n')

        return buf.getvalue()


class SymExec_incremental(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        res = self.visit(ast, state=state)
        #print(len(res))
        return [st for st in res]

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        lhs = self.visit(node.arg(0), *args, **kwargs)
        rhs = self.visit(node.arg(1), *args, **kwargs)
        if node.op == "<=":
            return lhs <= rhs
        if node.op == "<":
            return lhs < rhs
        if node.op == "=":
            return lhs == rhs
        if node.op == ">=":
            return lhs >= rhs
        if node.op == ">":
            return lhs > rhs
        assert False
        
    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None
        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])

        if node.op == "and":
            fn = lambda x, y: z3.And(x,y)
        elif node.op == "or":
            fn = lambda x, y: z3.Or(x,y)
        assert fn is not None

        return reduce(fn, kids)

    def visit_AExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        fn = None
        if node.op == "+":
            fn = lambda x, y: x + y

        elif node.op == "-":
            fn = lambda x, y: x - y

        elif node.op == "*":
            fn = lambda x, y: x * y

        elif node.op == "/":
            fn = lambda x, y: x / y
        assert fn is not None

        return z3.simplify(reduce(fn, kids))

    def visit_SkipStmt(self, node, *args, **kwargs):
        return [kwargs["state"]]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
        return [kwargs["state"]]

    def visit_AsgnStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        # for st in kwargs["state_in_progress"]:
            # kwargs["state"] = st 
        st.env[node.lhs.name] = self.visit(node.rhs, *args, **kwargs)
        kwargs["state"] = st
        return [kwargs["state"]]

    def visit_IfStmt(self, node, *args, **kwargs):
        
        # for st in kwargs["state_in_progress"]:
        # kwargs["state"] = st
        st = kwargs["state"]
        cond = self.visit(node.cond, *args, **kwargs)
        curr_state, new_state = st.fork()
        out = []
        curr_state.add_pc(cond)
        new_state.add_pc(z3.Not(cond))
        solver = st._solver
        solver.push()
        solver.add(cond)
        if solver.check() == z3.sat:
            kwargs["state"] = curr_state
            st1 = self.visit(node.then_stmt, *args, **kwargs)
            out.extend(st1)
        solver.pop()
        solver.push()
        solver.add(z3.Not(cond))
        if solver.check() == z3.unsat:
            new_state.mk_error()
            out.extend([new_state])
        solver.pop()
        return out
    
    def visit_WhileStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        out = []
        cond = self.visit(node.cond, *args, **kwargs)
        curr_state, new_state = st.fork()
        curr_state.add_pc(cond)
        new_state.add_pc(z3.Not(cond))
        counter = 0
        if len(args) != 0:
            counter = args[0]
        if counter < 10:
            solver  = st._solver
            solver.push()
            solver.add(cond)
            if solver.check() == z3.sat:
            
                st1 = self.visit(node.body, 0, state=curr_state)
            
                sts_new = []
                for i in range(len(st1)):
                    if not st1[i].is_error():
                        sts_new.extend(self.visit_WhileStmt(node, counter + 1, state=st1[i]))
                
                st1 = sts_new

                out = st1
            else:
                curr_state.mk_error()
                out.extend([curr_state])
            solver.pop()
            solver.push()
            solver.add(z3.Not(cond))
            if solver.check() == z3.unsat:
                new_state.mk_error()
            
            out.extend([new_state])
            return out
        else:
            return [st]
    
    def visit_AssertStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        # for st in kwargs["state_in_progress"]: 
        # Don't forget to print an error message if an assertion might be violated
        cond = self.visit(node.cond, *args, **kwargs)
        true_state, false_state = st.fork ()
        false_state.add_pc (z3.Not(cond))
        true_state.add_pc (cond)
        solver = st._solver
        solver.push()
        solver.add(cond)
        if solver.check() == z3.sat:
            return [true_state]
        else:
            false_state.mk_error()
            print("Assertion error: " + str(node)) 
        solver.pop()
        return [false_state]
        
        

    def visit_AssumeStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        # for st in kwargs["state_in_progress"]: 
        # Don't forget to print an error message if an assertion might be violated
        cond = self.visit(node.cond, *args, **kwargs)
        st.add_pc (cond)
        if st.is_empty ():
            st.mk_error()
        return [st]

    def visit_HavocStmt(self, node, *args, **kwargs):
        st = kwargs["state"]
        # for st in kwargs["state_in_progress"]: 
        for v in node.vars:
            # assign 0 as the default value
            st.env[v.name] = z3.FreshInt(str(v.name).upper())
        kwargs["state"] = st
        return [kwargs["state"]]

    def visit_StmtList(self, node, *args, **kwargs):
        sts = [kwargs["state"]]
        if node.stmts is None:
            return
        for stmt in node.stmts:
            tmp_st = sts[:]
            for i in range(len(sts)):
                if not sts[i].is_error():
                    
                    new_state = self.visit(stmt, state=sts[i])
                    if len(new_state) == 1:
                        tmp_st[i] = new_state[0]
                    else:
                        del tmp_st[i]
                        tmp_st.extend(new_state)
            sts = tmp_st[:]
        return sts


def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='sym',
                                 description='WLang Interpreter')
    ap.add_argument('in_file', metavar='FILE',
                    help='WLang program to interpret')
    args = ap.parse_args()
    return args


def main():
    args = _parse_args()
    prg = ast.parse_file(args.in_file)
    st = Concolic_State()
    sym = Concolic_Exec()

    states = sym.run(prg, st)
    if states is None:
        print('[Concolic exec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[Concolic exec]: symbolic state reached')
            print(out)
        print('[Concolic exec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
