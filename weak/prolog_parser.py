##
## Chapter 6. Frontend parser.
##

#
# We'll use a 3rd-party PEG parser Arpeggio here.
# A simple pass decomposing left-hand structs in 'top' AST nodes into 'def' nodes.

from arpeggio import Optional, ZeroOrMore, OneOrMore, EOF,PTNodeVisitor, visit_parse_tree
from arpeggio import RegExMatch as _
from arpeggio import ParserPython

from weak.prolog_ast import *

# Note that only C-style comments are supported here:
def plgcomment():   return [_("//.*"), _("/\*.*\*/")]
def plgstring():    return _('"[^"]*"')
def plgnumber():    return _('-?\d+((\.\d*)?((e|E)(\+|-)?\d+)?)?')
def plgcut():       return "!"
def plgeq():        return plgxterm, "=", plgxterm
def plgstruct():    return plgident, [ ("(", ")"),
                                       ("(", plgterm, ZeroOrMore(",", plgterm), ")") ]
def plgnil():       return "[","]"
def plglist():      return "[", plgterm, ZeroOrMore([",","|"], plgterm), "]"

def plgvar():       return _(r"[A-Z]\w*")
def plgident():     return _(r"[a-z]\w*")
def plgconst():     return [plgnumber, plgstring, plgident]
def plgterm():      return [plgeq, plgcut, plgnil, plglist, plgstruct, plgvar, plgconst]
def plgxterm():     return [plglist, plgstruct, plgvar, plgconst]
def plgfact():      return plgstruct, "."
def plgpred():      return plgstruct, ":-", plgterm, ZeroOrMore(",", plgterm), "."
def plgquery():     return "?", plgterm, ZeroOrMore(",", plgterm), "."
def plgtoplevel():  return [plgquery, plgfact, plgpred]
def prolog():       return OneOrMore(plgtoplevel), EOF

prolog_parser = ParserPython(prolog, plgcomment)

# Convert the Arpreggio internal AST into our simple AST
def decode_list(ch):
    tp = ast_mk_struct_ar("cons", [None, None])
    cur = tp
    state = 0
    for c in ch:
        if state == 0:
            cur._args[0] = c
            state = 1
        elif state == 2:
            cur._args[1] = c
            state = 3
        elif state == 1:
            if c == ',':
                cur._args[1] = ast_mk_struct_ar("cons", [None, None])
                cur = cur._args[1]
                state = 0
            elif c == '|':
                state = 2
    if state == 1:
        cur._args[1] = ast_mk_struct_ar("nil", [])
    return tp
            

class PlgVisitor(PTNodeVisitor):
    def visit_prolog(self, node, ch):      return ch
    def visit_plgpred(self, node, ch):     return ast_mk_top(ch[0], ch[1:])
    def visit_plgfact(self, node, ch):     return ast_mk_top(ch[0], [])
    def visit_plgxterm(self, node, ch):    return ch[0]
    def visit_plgstring(selfs, node, ch):  return str(node.value)[1:-1]
    def visit_plgnumber(self,  node,  ch): return int(str(node.value))
    def visit_plgconst(self, node, ch):    return ast_mk_const(ch[0])
    def visit_plgident(self, node, ch):    return node.value
    def visit_plgvar(self, node, ch):      return ast_mk_var(node.value)
    def visit_plgstruct(self, node, ch):   return ast_mk_struct_ar(ch[0], ch[1:])
    def visit_plgeq(self, node, ch):       return ast_mk_struct_ar("equals", [ch[0], ch[1]])
    def visit_plgcut(self, node, ch):      return ast_mk_struct_ar("cut",[])
    def visit_plglist(self,node,ch):       return decode_list(ch)
    def visit_plglistbody(self,node,ch):   return ch[0]
    def visit_plgnil(self,node,ch):        return ast_mk_struct_ar("nil",[])
    def visit_plgterm(self, node, ch):
        if len(ch)>0:
            return ch[0]
        else: return node.value
    def visit_plgquery(self, node, ch):
        qs = ch
        qvars = prolog_ast_get_vars(qs)
        return ast_mk_top(ast_mk_struct_ar("_query",[ast_mk_var(v) for v in qvars]), qs)

def parse(code:str) -> list:
    '''
    Parse a default Prolog syntax
    :param code: Prolog predicates
    :return: a list of Prolog ASTs
    '''
    ast0 = prolog_parser.parse(code)
    ast1 = visit_parse_tree(ast0, PlgVisitor())
    return ast1
