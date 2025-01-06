from ..rec_parser import parse_str
from .recurrence import LoopRecurrence, MultiRecurrence
from .multivariate import solve_multivariate_rec
from .ultimately_periodic import solve_ultimately_periodic_symbolic

def solve_str(s):
    rec = parse_str(s)
    if isinstance(rec, LoopRecurrence):
        return solve_ultimately_periodic_symbolic(rec)
    elif isinstance(rec, MultiRecurrence):
        return solve_multivariate_rec(rec)
    return None

def solve_file(filename):
    with open(filename) as fp:
        return solve_str(fp.read())
