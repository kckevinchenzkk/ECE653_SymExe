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
from functools import reduce
from . import ast, int
from .undef_visitor import UndefVisitor


class SymState(object):
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

    def pick_concerete(self):
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
        child = SymState()
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


class SymExec(ast.AstVisitor):
    def __init__(self):
        pass

    def run(self, ast, state):
        # set things up and
        # call self.visit (ast, state=state)
        # pass
        # result = self.visit(ast, state=state)
        # return result
        return [st for st in self.visit(ast, state=state) if not st.is_error()]
                
    def visit_BoolRef(self, node, *args, **kwargs):
        # For BoolRef nodes, just return the node itself
        return node

    def visit_IntVar(self, node, *args, **kwargs):
        return kwargs['state'].env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        return z3.BoolVal(node.val)

    def visit_IntConst(self, node, *args, **kwargs):
        return z3.IntVal(node.val)

    def visit_RelExp(self, node, *args, **kwargs):
        state = kwargs['state']
        lhs_sym = self.visit(node.arg(0), state=state)
        rhs_sym = self.visit(node.arg(1), state=state)
        if node.op == '=':
            return lhs_sym == rhs_sym
        elif node.op == '<':
            return lhs_sym < rhs_sym
        elif node.op == '<=':
            return lhs_sym <= rhs_sym
        elif node.op == '>':
            return lhs_sym > rhs_sym
        elif node.op == '>=':
            return lhs_sym >= rhs_sym
        assert False

    def visit_BExp(self, node, *args, **kwargs):
        kids = [self.visit(a, *args, **kwargs) for a in node.args]
        
        if node.op == "not":
            assert node.is_unary()
            assert len(kids) == 1
            return z3.Not(kids[0])
        fn = None
        base = None
        if node.op == "and":
            fn = lambda x, y: z3.And(x,y)
            base = True

        elif node.op == "or":
            fn = lambda x, y: z3.Or(x,y)
            base = False

        assert fn is not None
        return reduce(fn, kids, base)


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
            fn = lambda x, y: x/ y

        assert fn is not None
        # Then simplify the resulting expression before returning it
        return z3.simplify(reduce(fn, kids))

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
        return kwargs['state']

    def visit_AsgnStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        rhs_val = self.visit(node.rhs, *args, **kwargs)
        state.env[node.lhs.name] = rhs_val
        return [state]
    

    def visit_IfStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        cond_sym = self.visit(node.cond, state=state)
        then_state, else_state = state.fork()  
        then_state.add_pc(cond_sym)
        else_state.add_pc(z3.Not(cond_sym))

        out_state = []
        if not then_state.is_empty():
            # Visit the 'then' statement and ensure it returns a list
            then_state = self.visit(node.then_stmt, state=then_state)
            out_state = then_state
            if not isinstance(then_state, list):
                out_state = [then_state]

        # if not else_state.is_empty():     
        #     if node.has_else():
        #         # Visit the 'else' statement and ensure it returns a list
        #         else_state = self.visit(node.else_stmt, state=else_state)
        #         out_state.extend(else_state)
        #     if not isinstance(else_state, list):
        #         out_state.extend([else_state])
        
        # Process the 'else' branch
        if node.has_else() and not else_state.is_empty():
                else_result = self.visit(node.else_stmt, state=else_state)
                if isinstance(else_result, list):
                    out_state.extend(else_result)
                else:
                    out_state.append(else_result)
        else:
            if not else_state.is_empty():
                out_state.append(else_state)
                # else:
                #     else_state.mk_error()
                #     eles_out = [else_state]
        # else:
        #     # _, else_state = state.fork()
        #     # else_state.add_pc(z3.Not(cond_sym))
        #     # if not else_state.is_empty():
        #     #     else_path = [else_state]
        #     out_state.extend([else_state])
           

        # Combine non-empty states from both 'then' and 'else' paths
        # non_empty_states = [s for s in then_path + else_path if not s.is_empty()]
        # return non_empty_states if non_empty_states else [state]
        return out_state
        #return then_path + else_path
    def visit_WhileStmt(self, node, *args, **kwargs):
        if node.inv is not None:
            return list(self.visit_WhileStmt_inv(node, *args, **kwargs))
        else:
            return list(self.visit_WhileStmt_noinv(node, *args, **kwargs))

    def visit_WhileStmt_noinv(self, node, *args, **kwargs):
        state = kwargs['state']
        MAX_ITERATION = 10
        counter = 0
        if len(args) != 0:
            counter = args[0]
        if counter >= 10:
            return [state]
        cond_sym = self.visit(node.cond, state=state)
        body_state, after_loop_state  = state.fork()
        body_state.add_pc(cond_sym)
        after_loop_state.add_pc(z3.Not(cond_sym))
        
        out_state = []
        
        if not body_state.is_empty()  and  counter < MAX_ITERATION:
            body_state = self.visit(node.body, 0, state=body_state)
            body_new = []
            for i in range(len(body_state)):
                body_new.extend(self.visit_WhileStmt(node, counter + 1, state=body_state[i]))
            body_state = body_new
            out_state = body_state
        else:
            body_state.mk_error()
            out_state = [body_state]

        if not after_loop_state.is_empty():
            out_state.extend([after_loop_state])
        else:
            after_loop_state.mk_error()
            out_state.extend([after_loop_state])
        return out_state

    def visit_WhileStmt_inv(self, node, *args, **kwargs):
        state = kwargs['state']
        cond_sym = self.visit(node.cond, state=state)
        inv = self.visit(node.inv, *args, **kwargs)
        # keep state for assert and entering loop
        pre_st, loop_st = kwargs['state'].fork()
        # assert invariant initialisation
        pre_st.add_pc(inv)
        if pre_st.is_empty():
            print('invariant fails in initialisation')
            pre_st.mk_error()
            return [pre_st]
           
        loop_st.add_pc(inv)
        # if loop_st.is_empty():
        #     loop_st.mk_error()
        #     return [loop_st]
        
        uv = UndefVisitor()
        uv.check(node.body)
        modified_vars = uv.get_defs()
        
        # havoc variables
        for var in modified_vars:
            loop_st.env[var.name] = z3.FreshInt(var.name)
        # assume invariant
        #inv = self.visit(node.inv, *args, state=loop_st)
        body_state, after_loop_state  = state.fork()
        body_state.add_pc(cond_sym)
        after_loop_state.add_pc(z3.Not(cond_sym))

        out_states = []
        # MAX_ITERATION = 10
        # counter = 0
        # if len(args) != 0:
        #     counter = args[0]
        # if counter >= MAX_ITERATION:
        #     return [state]
        
        if not body_state.is_empty():
            body_outs = self.visit(node.body, state=body_state)
            for out_state in body_outs:
                # Assert the invariant
                if not out_state.is_error():
                    inv = self.visit(node.inv, *args, state=out_state)
                    out_state.add_pc(inv)
                    if out_state.is_empty():
                        print("Invariant fails in loop")
                        out_state.mk_error()
                out_states.append(out_state)
            #return body_outs
        # return [after_loop_state]
        # if negation of loop condition can be satisfied then can exit
        
        if not after_loop_state.is_empty ():
            out_states.append(after_loop_state)
        
        return out_states

    def visit_AssertStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        assert_cond = self.visit(node.cond, state=state)

        # Fork the state into two: one assuming the assertion holds, the other assuming it does not
        state_holds, state_violated = state.fork()

        # Add the assertion condition to the state where it holds and its negation to the state where it's violated
        state_holds.add_pc(assert_cond)
        state_violated.add_pc(z3.Not(assert_cond))

        # Prepare a list to hold the resulting states
        result_states = []

        # Check if the state where the assertion holds is valid (not empty)
        if not state_holds.is_empty():
            result_states.append(state_holds)  # The assertion can hold in this state

        # Check if the state where the assertion does not hold is valid (not empty)
        if not state_violated.is_empty():
            print("Warning: Assertion might be violated:", node.cond)
            state_violated.mk_error()
            result_states.append(state_violated)  # There is a potential violation in this state

        return result_states

        # # Check if the assertion can be violated
        # # Push the current solver state
        # state._solver.push()  
        # state._solver.add(z3.Not(expr))  # Add the negation of the assertion condition
        # check = state._solver.check()
        # state._solver.pop()  # Pop to restore the previous state
        
        # if check == z3.sat:
        #     # If the negation is sat, then the assertion can be violated
        #     state.mk_error() 
        #     print("Error: Assertion might be violated:", node.cond)
        # state.add_pc(expr)
        # return [state]

    def visit_AssumeStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        expr = self.visit(node.cond, state=state)
        # Add this expression as a constraint to the path condition
        state.add_pc(expr)
        # if state.is_empty():
        #     state.mk_error()
        return [state]

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        for v in node.vars:
            state.env[v.name] = z3.FreshInt()
        return [state]

    def visit_StmtList(self, node, *args, **kwargs):

        state = kwargs['state']
        states = [state]  # Initialize with the current state
        if node.stmts is None:
            return
        for stmt in node.stmts:
            new_states = []
            for state in states:
                result = self.visit(stmt, state=state)
                # 'result' should always be a list of states
                if isinstance(result, list):
                    new_states.extend(result)  
                else:
                    new_states.append(result) 
            states = new_states  # Update the states with the new states

        return states


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
    st = SymState()
    sym = SymExec()

    states = sym.run(prg, st)
    if states is None:
        print('[symexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[symexec]: symbolic state reached')
            print(out)
        print('[symexec]: found', count, 'symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
