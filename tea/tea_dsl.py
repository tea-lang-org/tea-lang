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
        #token.type --> gives "STRING" etc.
    

def test(): 
    text = """
        data data.csv
        variables [
            (
                name=Southern, 
                data type=nominal, 
                categories=[0,1]
            ), 
            (
                name=Probability, 
                data type=ratio
            )
        ]
        assumptions [
                groups normally distributed=[[Southern, Probability]],
                Type I (False Positive) Error Rate= .05
        ]
        design [
            study type=observational study,
            contributor variables=Southern,
            outcome variables=Probability
        ]
        hypothesis [
            variables=[Southern, Probability],
            comparisons=Southern:1>0
        ]
    """

    run_tea_program(text)

if __name__ == '__main__': 
    test()