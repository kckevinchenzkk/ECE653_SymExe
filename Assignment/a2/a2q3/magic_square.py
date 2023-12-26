'''Magic Square

https://en.wikipedia.org/wiki/Magic_square

A magic square is a n * n square grid filled with distinct positive integers in
the range 1, 2, ..., n^2 such that each cell contains a different integer and
the sum of the integers in each row, column, and diagonal is equal.

'''
import z3
from z3 import Solver, sat, unsat


def solve_magic_square(n, r, c, val):
    solver = Solver()
    # CREATE element for each cell
    cells = [[z3.Int(f'cell_{i}_{j}') for i in range(n)] for j in range(n)]
    # CREATE CONSTRAINTS AND LOAD STORE THEM IN THE SOLVER
    # constraint for each element is distinct
    solver.add(z3.Distinct([cells[i][j] for i in range(n) for j in range(n)]))
    # constraint for each element is 1 <= cells <= n^2
    cells_constraints1 = [cells[i][j] >= 1 for i in range(n) for j in range(n)]
    cells_constraints2 = [cells[i][j] <= n**2 for i in range(n) for j in range(n)]
    solver.add(cells_constraints1)
    solver.add(cells_constraints2)
    # constraint for each row, columns, diagonials are equal
    row_sum = None
    col_sum = None
    for i in range(n):
        row_sum = sum([cells[i][j] for j in range(n)])
        col_sum = sum([cells[j][i] for j in range(n)])
        solver.add(row_sum == col_sum)
        if i > 0:  # Ensure that the sum of each row and column is the same as the previous
            prev_row_sum = sum(cells[i-1])
            prev_col_sum = sum([cells[j][i-1] for j in range(n)])
            solver.add(row_sum == prev_row_sum)
            solver.add(col_sum == prev_col_sum)
    # Constraints for diagonal sums
    diag1_sum = sum([cells[i][i] for i in range(n)])  # main diagonal
    diag2_sum = sum([cells[i][n-i-1] for i in range(n)])  # secondary diagonal
    solver.add(diag1_sum == diag2_sum) # they are equal
    if n > 1:
        solver.add(diag1_sum == row_sum) # also euqal to row and column sum
    
    # constraint for specific number at rc
    solver.add(cells[r][c] == val)


    if solver.check() == sat:
        mod = solver.model()
        res = [[mod.evaluate(cells[i][j]).as_long() for i in range(n)] for j in range(n)]

        # CREATE RESULT MAGIC SQUARE BASED ON THE MODEL FROM THE SOLVER

        return res
    else:
        return None


def print_square(square):
    '''
    Prints a magic square as a square on the console
    '''
    n = len(square)

    assert n > 0
    for i in range(n):
        assert len(square[i]) == n

    for i in range(n):
        line = []
        for j in range(n):
            line.append(str(square[i][j]))
        print('\t'.join(line))


def puzzle(n, r, c, val):
    res = solve_magic_square(n, r, c, val)
    if res is None:
        print('No solution!')
    else:
        print('Solution:')
        print_square(res)


if __name__ == '__main__':
    n = 3
    r = 1
    c = 1
    val = 5
    puzzle(n, r, c, val)
