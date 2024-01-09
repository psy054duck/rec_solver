from .rec_parser import parser

def main():
    s = '''a = 1; b = 3; c = u;'''
    parser.parse(s)