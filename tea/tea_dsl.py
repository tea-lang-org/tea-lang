from lark import Lark 

tea_parser = Lark.open('./tea/tea_grammar.lark', parser='lalr')
tea_p = tea_parser.parse

def run_tea_program(program): 
    global tea_parser
    parse_tree = tea_parser.parse(program)
    print(parse_tree)

def test(): 
    text = """
        data data.csv
    """

    run_tea_program(text)

if __name__ == '__main__': 
    test()