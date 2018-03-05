# Symbols support
prolog_symbols = {}
def prolog_symbol(s):
    global prolog_symbols
    ret = prolog_symbols.get(s)
    if ret is None:
        prolog_symbols[s] = s
        return s
    else:
        return ret

# Let's now define primitives for constructing the intermediate language AST used by the compiler above.
# Sorry for the horrible boilerplate code, but Python is an awful language in general anyway.
useful = ['_id','_name','_args','_nxt','_body','_l','_r','_a','_b','_vars','_val','_opts']
class ASTNode:
    def __init__(self, tag):
        self._tag = tag
    def __repr__(self):
        global useful
        elts = []
        for d in dir(self):
            if d in useful:
                elts.append("(" +str(d) + " " + str(getattr(self,d)) + ")")
        return "(" + self._tag + " " + " ".join(elts) + ")"

def ast_mk_intros(vs, nxt):
    a = ASTNode('intros');a._vars = vs;a._nxt = nxt
    return a
def ast_mk_unify(arg_a,arg_b,nxt):
    a = ASTNode('unify');a._a = arg_a;a._b = arg_b;a._nxt = nxt
    return a
def ast_mk_choose(opts):
    a = ASTNode('choose');a._opts = opts
    return a
def ast_mk_call_with(nm, args, nxt):
    a = ASTNode('call_with');a._name = nm;a._args = args;a._nxt = nxt
    return a
def ast_mk_tailcall(nm, args):
    a = ASTNode('tailcall');a._name = nm;a._args = args
    return a
def ast_mk_new(nm, args):
    a = ASTNode('new');a._id = nm;a._args = args
    return a
def ast_mk_const(val):
    a = ASTNode('const');a._val = val
    return a
def ast_mk_var(nm):
    a = ASTNode('var');a._name = nm
    return a
def ast_mk_arg(nm):
    a = ASTNode('arg');a._name = nm
    return a
def ast_mk_proceed():
    return ASTNode('proceed')

# And  the frontend language constructors:
def ast_mk_struct(nm,args):
    a = ASTNode('struct'); a._name = nm; a._args = args
    return a
def ast_mk_struct_ar(nm,args):
    a = ASTNode('struct'); a._name = prolog_symbol(nm+"/"+str(len(args))); a._args = args
    return a
def ast_mk_def(nm,args,body):
    a = ASTNode('def');a._name = nm; a._args = args; a._body = body
    return a
def ast_mk_top(l, r):
    a = ASTNode('top');a._l = l; a._r = r
    return a

#
# This is not a very clean way of finding all the variables in a given AST, but
# it works, and we only need it for generating implicit queries.


recursive = ['_nxt','_opts','_a','_b','_args','_body','_l','_r']
def prolog_ast_vars(qvars, n):
    global recursive
    if n._tag == 'var':
        qvars[n._name] = True
    else:
        for d in dir(n):
            if d in recursive:
                v = getattr(n, d)
                if type(v) is ASTNode:
                    prolog_ast_vars(qvars, v)
                else:
                    for x in v:
                        prolog_ast_vars(qvars, x)
    
def prolog_ast_get_vars(qs):
    qvars = {}
    for q in qs:
        prolog_ast_vars(qvars, q)
    return list(qvars)

