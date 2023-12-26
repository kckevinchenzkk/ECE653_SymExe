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
import random


class Concolic_State(object):
    def __init__(self, solver=None):
        # environment mapping variables to symbolic constants
        self.con_env = dict()
        self.sym_env = dict()
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
        st = dict()
        for (k, v) in self.sym_env.items():
            print((k,v),"here!!!!!")
            #st.env[k] = model.eval(v)
            # sym_var = self.sym_env[var]
            # if sym_var in model:
            #     # Get the concrete value assigned to the symbolic variable by the model
            #     concrete_value = model.eval(sym_var, model_completion=True).as_long()
            #     concrete_state[var] = concrete_value
            # else:
            #     # Handle cases where the model does not assign a value to a variable
            #     # This might involve assigning a default value or handling it as an error
            #     concrete_state[var] = self.default_value_for_var(sym_var)
            st[k] = model.eval(v, model_completion = True).as_long()
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
        # set things up and
        # call self.visit (ast, state=state)
        # pass
        # result = self.visit(ast, state=state)
        # return result
        #kwargs = {"state": state, "exec_mode": "concrete", "cond": "false"}
        kwargs = dict()
        kwargs["state"] = state
        kwargs["exec_mode"] = "concrete"
        kwargs["cond"] = "false"
        args = []
        #print(f"Debug: type of state before visit {type(state)} expected Concolic_State")
        result = self.visit(ast, *args, **kwargs)
        # Filter out error states
        return [res['state'] for res in result]
    # def concrete_eval(self, node, con_env):
    #     """
    #     Evaluate an AST node using concrete values from the given environment.
    #     """
    #     if isinstance(node, ast.IntConst):
    #         return node.val
    #     elif isinstance(node, ast.IntVar):
    #         # Retrieve the concrete value from con_env
    #         return con_env.get(node.name, 0)  # Default to 0 if not found
    #     elif isinstance(node, ast.RelExp):
    #         lhs = self.concrete_eval(node.arg(0), con_env)
    #         rhs = self.concrete_eval(node.arg(1), con_env)
    #         return self.visit_RelExp(node.op, lhs, rhs)
    #     elif isinstance(node, ast.AExp):
    #         values = [self.concrete_eval(arg, con_env) for arg in node.args]
    #         return self.visit_AExp(node.op, values)
    #     # Add handling for other node types as needed
    #     else:
    #         raise NotImplementedError(f"Concrete evaluation not implemented for node type {type(node)}")

    def visit_BoolRef(self, node, *args, **kwargs):
        # For BoolRef nodes, just return the node itself
        return node

    def visit_IntVar(self, node, *args, **kwargs):
        #return kwargs['state'].env[node.name]
        state = kwargs['state']
        #exec_mode = kwargs.get('exec_mode', 'symbolic')

        if kwargs["exec_mode"] == "symbolic":
            # Return the symbolic value from sym_env
            return state.sym_env[node.name]
        elif kwargs["exec_mode"] == "concrete":
            # Return the concrete value from con_env
            return state.con_env[node.name]

    def visit_BoolConst(self, node, *args, **kwargs):
        exec_mode = kwargs.get('exec_mode')  # Get exec_mode, default to 'symbolic'
        if (exec_mode == "symbolic"):
            return z3.BoolVal(node.val)

        # Concrete Execution
        else:
            return node.val

    def visit_IntConst(self, node, *args, **kwargs):
        exec_mode = kwargs.get('exec_mode')  # Get exec_mode, default to 'symbolic'
        if (exec_mode == "symbolic"):
            return z3.IntVal(node.val)

        # Concrete Execution
        else:
            return node.val

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
        exec_mode = kwargs.get('exec_mode')
        result = None
        if exec_mode == 'symbolic':
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
            result = z3.simplify(reduce(fn, kids))
        #elif exec_mode == 'concrete':
        else:
            # Concrete execution using Python's arithmetic operations
            kids = [self.visit(a, *args, **kwargs)['state'] for a in node.args]  # Get concrete values
            fn = None
            if node.op == "+":
                fn = lambda x, y: x + y
            elif node.op == "-":
                fn = lambda x, y: x - y
            elif node.op == "*":
                fn = lambda x, y: x * y
            elif node.op == "/":
                fn = lambda x, y: int(x / y)  # Ensure integer division
            assert fn is not None
            result = reduce(fn, kids)
        # Return the result wrapped in a dictionary with 'state' as the key
        origin_state = kwargs.copy()
        origin_state["state"] = result

        #return [{'state': origin_state}]
        # return [origin_state]
        #return result
        return origin_state
        #return {'state': result} if exec_mode == 'concrete' else origin_state

    def visit_SkipStmt(self, node, *args, **kwargs):
        return kwargs["state"]
        #return [{'state': kwargs['state']}]

    def visit_PrintStateStmt(self, node, *args, **kwargs):
        print(kwargs["state"])
       #return [{'state': kwargs['state']}]
        return kwargs['state']

    def visit_AsgnStmt(self, node, *args, **kwargs):
        # state = kwargs['state']
        # rhs_val = self.visit(node.rhs, *args, **kwargs)
        # state.env[node.lhs.name] = rhs_val
        state = kwargs["state"]
        state = kwargs['state'] if isinstance(kwargs['state'], Concolic_State) else kwargs['state']['state']
        #exec_mode = kwargs.get('exec_mode', 'symbolic')  # Get exec_mode, default to 'symbolic'

        print(f"Debug: type of state is {type(state)} expected Concolic_State")
        # symbolic
        sym_state = kwargs.copy()
        sym_state["exec_mode"] = "symbolic"
        state.sym_env[node.lhs.name] = self.visit(node.rhs, state = sym_state)

        dse_state = kwargs.copy()
        dse_state["exec_mode"] = "concrete" 
        state.con_env[node.lhs.name] = self.visit(node.rhs, state = dse_state)
        #con_rhs = self.concrete_eval(node.rhs, state.con_env)
        
        origin_state = kwargs.copy()
        origin_state["state"] = state

        #return [{'state': origin_state}]
        return [origin_state]
    

    def visit_IfStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        # cond_sym = self.visit(node.cond, state=state)
        # then_state, else_state = state.fork()  
        # then_state.add_pc(cond_sym)
        # else_state.add_pc(z3.Not(cond_sym))

        # out_state = []
        # if not then_state.is_empty():
        #     # Visit the 'then' statement and ensure it returns a list
        #     then_state = self.visit(node.then_stmt, state=then_state)
        #     out_state = then_state
        #     if not isinstance(then_state, list):
        #         out_state = [then_state]

        
        # # Process the 'else' branch
        # if node.has_else() and not else_state.is_empty():
        #         else_result = self.visit(node.else_stmt, state=else_state)
        #         if isinstance(else_result, list):
        #             out_state.extend(else_result)
        #         else:
        #             out_state.append(else_result)
        # else:
        #     if not else_state.is_empty():
        #         out_state.append(else_state)
        exec_mode = kwargs.get('exec_mode', 'both')

        # Evaluate the condition both symbolically and concretely
        sym_cond = self.visit(node.cond, state=state, exec_mode='symbolic')
        con_cond = self.concrete_eval(node.cond, state.con_env)

        # Fork states for symbolic execution
        sym_true_state, sym_false_state = state.fork()
        sym_true_state.add_pc(sym_cond)
        sym_false_state.add_pc(z3.Not(sym_cond))

        out_state = []

        # Handle the 'then' branch
        if con_cond or exec_mode == 'symbolic':
            then_kwargs = dict(kwargs, state=sym_true_state)
            out_state.extend(self.visit(node.then_stmt, *args, **then_kwargs))

        # Handle the 'else' branch
        if not con_cond or exec_mode == 'symbolic':
            else_kwargs = dict(kwargs, state=sym_false_state)
            if node.has_else():
                out_state.extend(self.visit(node.else_stmt, *args, **else_kwargs))
            else:
                out_state.append(sym_false_state)

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
        # MAX_ITERATION = 10
        # counter = 0
        # if len(args) != 0:
        #     counter = args[0]
        # if counter >= 10:
        #     return [state]
        # cond_sym = self.visit(node.cond, state=state)
        # body_state, after_loop_state  = state.fork()
        # body_state.add_pc(cond_sym)
        # after_loop_state.add_pc(z3.Not(cond_sym))
        
        # out_state = []
        
        # if not body_state.is_empty()  and  counter < MAX_ITERATION:
        #     body_state = self.visit(node.body, 0, state=body_state)
        #     body_new = []
        #     for i in range(len(body_state)):
        #         body_new.extend(self.visit_WhileStmt(node, counter + 1, state=body_state[i]))
        #     body_state = body_new
        #     out_state = body_state
        # else:
        #     body_state.mk_error()
        #     out_state = [body_state]

        # if not after_loop_state.is_empty():
        #     out_state.extend([after_loop_state])
        # else:
        #     after_loop_state.mk_error()
        #     out_state.extend([after_loop_state])
        exec_mode = kwargs.get('exec_mode', 'both')
        max_iterations = kwargs.get('max_iterations', 10)
        iteration = kwargs.get('iteration', 0)

        if iteration >= max_iterations:
            return [state]

        # Evaluate the condition both symbolically and concretely
        sym_cond = self.visit(node.cond, state=state, exec_mode='symbolic')
        con_cond = self.concrete_eval(node.cond, state.con_env)

        # Fork states for symbolic execution
        sym_loop_state, sym_exit_state = state.fork()
        sym_loop_state.add_pc(sym_cond)
        sym_exit_state.add_pc(z3.Not(sym_cond))

        out_state = []

        # Handle the loop body
        if con_cond or exec_mode == 'symbolic':
            loop_kwargs = dict(kwargs, state=sym_loop_state, iteration=iteration + 1)
            out_state.extend(self.visit(node.body, *args, **loop_kwargs))
            # Recur for the next iteration
            out_state.extend(self.visit(node, *args, **loop_kwargs))

        # Handle the state after exiting the loop
        if not con_cond or exec_mode == 'symbolic':
            exit_kwargs = dict(kwargs, state=sym_exit_state)
            out_state.append(sym_exit_state)

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

    def visit_AssumeStmt(self, node, *args, **kwargs):
        state = kwargs['state']
        expr = self.visit(node.cond, state=state)
        # Add this expression as a constraint to the path condition
        state.add_pc(expr)
        # if state.is_empty():
        #     state.mk_error()
        return [state]

    def visit_HavocStmt(self, node, *args, **kwargs):
        state = kwargs["state"]
        for v in node.vars:
            # Assign a fresh symbolic value to the variable in the symbolic environment
            state.sym_env[v.name] = z3.FreshInt(v.name)
            # Assign a random concrete value to the variable in the concrete environment
            # You might want to adjust the range of randint as per your requirements
            state.con_env[v.name] = random.randint(-100, 100)
        original = kwargs.copy()
        original["state"] = state
        return [{'state': original}]
        return [original]

    def visit_StmtList(self, node, *args, **kwargs):
        # Start with the initial state given in the arguments
        initial_state = kwargs.get('state')
        states = [{'state': initial_state}] if isinstance(initial_state, Concolic_State) else initial_state

        for stmt in node.stmts:
            new_states = []
            for state_dict in states:
                state = state_dict['state']
                result = self.visit(stmt, state=state)
                # Handle the result, which should be a list of dictionaries or a single Concolic_State
                new_states.extend(result if isinstance(result, list) else [{'state': result}])
            states = new_states

        return states
    

def _parse_args():
    import argparse
    ap = argparse.ArgumentParser(prog='dse_exe',
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

    states = st.run(prg, st)
    if states is None:
        print('[dseexec]: no output states')
    else:
        count = 0
        for out in states:
            count = count + 1
            print('[dseexec]: dynmaic symbolic state reached')
            print(out)
        print('[dseexec]: found', count, 'dynamic symbolic states')
    return 0


if __name__ == '__main__':
    sys.exit(main())
