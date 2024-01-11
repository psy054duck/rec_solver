from .lexer import lexer, tokens
import ply.yacc as yacc
import sympy as sp
from ..recurrence import Recurrence

def p_recurrence(p):
    '''recurrence : initialization if'''
    p[0] = Recurrence(p[1], p[2])

def p_initialization(p):
    '''initialization : assignments'''
    p[0] = p[1]

def p_assignments_1(p):
    '''assignments : assignment assignments'''
    p[0] = p[1] | p[2]

def p_assignments_2(p):
    '''assignments : '''
    p[0] = {}

def p_assignment(p):
    '''assignment : lhs ASSIGN expression SEMI'''
    p[0] = {p[1]: p[3]}

def p_expression_plus(p):
    '''expression : expression PLUS term'''
    p[0] = p[1] + p[3]

def p_expression_minus(p):
    '''expression : expression MINUS term'''
    p[0] = p[1] - p[3]

def p_expression_term(p):
    '''expression : term'''
    p[0] = p[1]

def p_term_times(p):
    '''term : term TIMES factor'''
    p[0] = p[1] * p[3]

def p_term_div(p):
    '''term : term DIV factor'''
    p[0] = p[1] / p[3]

def p_term_factor(p):
    '''term : factor'''
    p[0] = p[1]

def p_factor_num(p):
    '''factor : NUMBER'''
    p[0] = sp.Integer(p[1])

def p_factor_id(p):
    '''factor : ID'''
    p[0] = sp.Symbol(p[1], integer=True)

def p_factor_negative(p):
    '''factor : MINUS factor'''
    p[0] = -p[1]

def p_factor_paren(p):
    '''factor : LPAREN expression RPAREN'''
    p[0] = p[1]


def p_if_1(p):
    '''if : IF LPAREN condition RPAREN LBRACE assignments RBRACE'''
    cond = p[3]
    assignments = p[6]
    p[0] = [(cond, assignments)]

def p_if_2(p):
    '''if : IF LPAREN condition RPAREN LBRACE assignments RBRACE else'''
    cond = p[3]
    assignments = p[6]
    p[0] = [(cond, assignments)] + p[8]

def p_else_1(p):
    '''else : ELSE LBRACE assignments RBRACE'''
    p[0] = [(True, p[3])]

def p_else_2(p):
    '''else : ELSE if'''
    p[0] = p[2]

def p_condition_atom_GT(p):
    '''condition_atom : expression GT expression'''
    p[0] = p[1] > p[3]

def p_condition_atom_GE(p):
    '''condition_atom : expression GE expression'''
    p[0] = p[1] >= p[3]

def p_condition_atom_LT(p):
    '''condition_atom : expression LT expression'''
    p[0] = p[1] < p[3]

def p_condition_atom_LE(p):
    '''condition_atom : expression LE expression'''
    p[0] = p[1] <= p[3]

def p_condition_atom_EQ(p):
    '''condition_atom : expression EQ expression'''
    p[0] = sp.Eq(p[1], p[3])

def p_condition_atom_NE(p):
    '''condition_atom : expression NE expression'''
    p[0] = sp.Ne(p[1], p[3])

def p_condition_factor_1(p):
    '''condition_factor : condition_atom'''
    p[0] = p[1]

def p_condition_factor_2(p):
    '''condition_factor : NEG condition'''
    p[0] = sp.Not(p[2])

def p_condition_factor_3(p):
    '''condition_factor : LPAREN condition RPAREN'''
    p[0] = p[2]

def p_condition_term_1(p):
    '''condition_term : condition_factor AND condition_term'''
    p[0] = sp.And(p[1], p[3])

def p_condition_term_2(p):
    '''condition_term : condition_factor'''
    p[0] = p[1]

def p_condition_1(p):
    '''condition : condition_term'''
    p[0] = p[1]

def p_condition_2(p):
    '''condition : condition_term OR condition'''
    p[0] = sp.Or(p[1], p[2])

def p_lhs_1(p):
    '''lhs : ID'''
    p[0] = sp.Symbol(p[1], integer=True)

def p_lhs_2(p):
    '''lhs : ID LRECT expression_list RRECT'''
    f = sp.Function(p[1])
    args = p[3]
    p[0] = f(*args)

def p_expression_list_1(p):
    '''expression_list : expression'''
    p[0] = [p[1]]

def p_expression_list_2(p):
    '''expression_list : expression COMMA expression_list'''
    p[0] = [p[1]] + p[2]


def p_error(p):
    print("Syntax error in input: %s: (%s)" % (p, p.type))


# Build the parser
parser = yacc.yacc()
