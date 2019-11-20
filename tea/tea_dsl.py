# from tea_eval import evaluate 

from lark import Lark 
from lark.tree import pydot__tree_to_png
from lark.visitors import Interpreter

tea_parser = Lark.open('./tea/tea_grammar.lark', parser='lalr')
tea_p = tea_parser.parse

def run_tea_program(program): 
    global tea_parser
    parse_tree = tea_parser.parse(program)
    print(parse_tree.pretty())
    
    # Draw parse tree out as a PNG
    pydot__tree_to_png(parse_tree, 'lark_test.png')
    
    evaluate(parse_tree)

def evaluate(parse_tree): 
    print('Here')
    intpr = Interpreter()
    tree = intpr.visit(tree=parse_tree)
    
    for node in tree: 
        print(node)
        import pdb; pdb.set_trace()
    

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