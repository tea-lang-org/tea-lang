from lark import Lark 

tea_parser = Lark.open('./tea/tea_grammar.lark', parser='earley')
tea_p = tea_parser.parse

def run_tea_program(program): 
    global tea_parser
    parse_tree = tea_parser.parse(program)
    print(parse_tree.pretty())

def test(): 
    text = """
        data data.csv
        design experiment [col_x1, col_x2] [col_y1]
        variables [col_x1, col_x2, col_y1]
        assume col_x1 is normally distributed
        hypothesize a >  b
        
    """
    # variables [col_x1, col_x2, co]_y1]

    run_tea_program(text)

if __name__ == '__main__': 
    test()