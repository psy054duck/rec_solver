import ply.lex as lex

# List of token names.   This is always required
basic_tokens = ('NUMBER', 'ID', 'LPAREN', 'RPAREN', 'ASSIGN', 'SEMI')
arith_tokens = ('PLUS', 'MINUS', 'TIMES', 'DIV')
cmp_tokens = ('GE', 'GT', 'LE', 'LT', 'EQ', 'NE')
logical_tokens = ('AND', 'OR', 'NEG')


# Regular expression rules for simple tokens
t_PLUS    = r'\+'
t_MINUS   = r'-'
t_TIMES   = r'\*'
t_DIV     = r'/'
t_LPAREN  = r'\('
t_RPAREN  = r'\)'
t_ASSIGN  = r'='
t_SEMI    = r';'
t_GE      = r'>='
t_GT      = r'>'
t_LT      = r'<'
t_LE      = r'<='
t_EQ      = r'=='
t_NE      = r'!='
t_AND     = r'&&'
t_OR      = r'\|\|'
t_NEG     = r'!'

# A regular expression rule with some action code
reserved = {
   'if' : 'IF',
   'else' : 'ELSE'
}

# tokens = ['LPAREN','RPAREN',...,'ID'] + list(reserved.values())
tokens = basic_tokens + arith_tokens + cmp_tokens + logical_tokens + tuple(reserved.values())

def t_NUMBER(t):
    r'\d+'
    return t

def t_ID(t):
    r'[a-zA-Z_][a-zA-Z_0-9]*'
    t.type = reserved.get(t.value,'ID')    # Check for reserved words
    return t

# Define a rule so we can track line numbers
def t_newline(t):
    r'\n+'
    t.lexer.lineno += len(t.value)

# A string containing ignored characters (spaces and tabs)
t_ignore  = ' \t'

# Error handling rule
def t_error(t):
    print("Illegal character '%s'" % t.value[0])
    t.lexer.skip(1)

# Build the lexer
lexer = lex.lex()