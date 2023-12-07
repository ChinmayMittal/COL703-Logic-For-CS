import sys
import json
from my_parser import Lark_StandAlone, Transformer, v_args
from utils import check_proof

inline_args = v_args(inline=True)

class TreeToDict(Transformer):
    
    def natded(self, children):
        return {
            "sequent": children[0],
            "proof": children[1]
        }
        
    def sequent(self, children):
        return {
            "premises": children[:-1],
            "deduction": children[-1]
        }
        
    def proof(self, children):
        ## line-number --> proof line
        ## proof lines start from line number 3
        return {i+3: child for i,child in enumerate(children)}
    
    def proof_line(self, children):
        return {
            "explanation": children[0],
            "formula": children[1]
        }
        
    def premise(self, children):
        return {
            "rule": "premise"
        }

    def assumption(self, children):
        return {
            "rule": "assumption"
        }

    def copy_op(self, children):
        return {
            "rule": "copy",
            "line": int(children[0])
        }

    def modus_ponens(self, children):
        return {
            "rule": "mp",
            "line-1": int(children[0]),
            "line-2": int(children[1])
        }

    def modus_tollens(self, children):
        return {
            "rule": "mt",
            "line-1": int(children[0]),
            "line-2": int(children[1])
        }

    def and_intro(self, children):
        return {
            "rule": "and-in",
            "line-1": int(children[0]),
            "line-2": int(children[1])
        }

    def and_elim1(self, children):
        return {
            "rule": "and-e1",
            "line": int(children[0])
        }

    def and_elim2(self, children):
        return {
            "rule": "and-e2",
            "line": int(children[0])
        }

    def or_intro1(self, children):
        return {
            "rule": "or-in1",
            "line": int(children[0])
        }

    def or_intro2(self, children):
        return {
            "rule": "or-in2",
            "line": int(children[0])
        }

    def or_elim(self, children):
        return {
            "rule": "or-el",
            "line": int(children[0]),
            "range-1": children[1],
            "range-2": children[2],
        }

    def impl_intro(self, children):
        return {
            "rule": "impl-in",
            "range": children[0]
        }

    def neg_intro(self, children):
        return {
            "rule": "neg-in",
            "range": children[0]
        }

    def neg_elim(self, children):
        return {
            "rule": "neg-el",
            "line-1": int(children[0]),
            "line-2": int(children[1]),
        }

    def bot_elim(self, children):
        return {
            "rule": "bot-el",
            "line": int(children[0]),
        }

    def d_neg_intro(self, children):
        return {
            "rule": "dneg-in",
            "line": int(children[0]),            
        }

    def d_neg_elim(self, children):
        return {
            "rule": "dneg-el",
            "line": int(children[0]),
        }

    def proof_by_contra(self, children):
        return {
            "rule": "pbc",
            "range": children[0]            
        }

    def lem(self, children):
        return {
            "rule": "lem",
        }

    def atomic_prop(self, children):
        return {
            "operation": "atomic_prop",
            "name": str(children[0])
        }
        
    def and_op(self, children):
        return {
            "operation": "and_op",
            "formula-1": children[0],
            "formula-2": children[1]
        }

    def or_op(self, children):
        return {
            "operation": "or_op",
            "formula-1": children[0],
            "formula-2": children[1],
        }

    def implies_op(self, children):
        return {
            "operation": "implies_op",
            "formula-1": children[0],
            "formula-2": children[1]
        }

    def not_op(self, children):
        return {
            "operation": "not_op",
            "formula": children[0],            
        }

    def bottom(self, children):
        return {
            "operation": "bottom",
        }

    def num_range(self, children):
        return {
                "start": children[0],
                "end": children[1]
            }

parser = Lark_StandAlone(transformer=TreeToDict())

def checkProof(filename):
    with open(filename) as f:
        try:
            ast_tree = (parser.parse(f.read()))
        except Exception as e:
            # print("Error in Parsing Parse Tree")
            return "incorrect"
        return "correct" if check_proof(ast_tree) else "incorrect"


if __name__ == '__main__':
    print(checkProof(sys.argv[1]))
