import fire
import sympy as sp
import logging
import sys

# logging.basicConfig(level=logging.INFO, stream=sys.stdout)

from rec_solver.core.solvable_polynomial import solve_solvable_map
from rec_solver import solve_ultimately_periodic_initial, solve_ultimately_periodic_symbolic
from rec_solver import parse_str, parse_file
from rec_solver import poly_expr_solving, solve_multivariate_rec
from rec_solver.recurrence import Recurrence
from rec_solver import utils

def main(file_path, method='symbolic', d=2, bnd=100, debug=False):
    if debug:
        logging.basicConfig(level=logging.DEBUG, stream=sys.stdout)
    else:
        logging.basicConfig(level=logging.INFO, stream=sys.stdout)
    rec = parse_file(file_path)
    if method == 'symbolic':
        closed_form = solve_ultimately_periodic_symbolic(rec, bnd)
    elif method == 'initial':
        closed_form = solve_ultimately_periodic_initial(rec, bnd)
    elif method == 'poly':
        closed_form = poly_expr_solving(rec, d)
    print(closed_form)

if __name__ == '__main__':
    fire.Fire(main)
