from .lexer import lexer, tokens
import ply.yacc as yacc
import sympy as sp

def p_recurrence(p):
    '''recurrence : initialization if'''
    print(p[1])

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
    '''assignment : ID ASSIGN expression SEMI'''
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


def p_if(p):
    '''if : '''
    pass

def p_error(p):
    print("Syntax error in input: %s: (%s)" % (p, p.type))


# Build the parser
parser = yacc.yacc()
