# Instrument a given predicate with narration

from weak.prolog_ast import *

def narrate_mklist(l: [ASTNode]) -> ASTNode:
    if len(l)>1:
        return ast_mk_struct_ar("cons", [l[0], narrate_mklist(l[1:])])
    elif len(l)>0:
        return ast_mk_struct_ar("cons", [l[0], ast_mk_struct_ar("nil",[])])
    else:
        return ast_mk_struct_ar("nil",[])


def insert_narrate(pd: dict, p: ASTNode) -> ASTNode:
    '''

    :param pd: dictionary with all the predicate names to be narrated
    :param p: a predicate source AST
    :return: an instrumented AST
    '''

    if p._tag != "top":
        raise ValueError('Not a top entry')

    nleft = "NLeft"
    nright = "NRight"

    # 1. Insert a new argument
    p._l._args = [ast_mk_var(nleft)] + p._l._args
    predname = p._l._name.split("/")[0]
    p._l._name =  predname + "/" + str(len(p._l._args))

    # 2. Rewrite predicate calls if necessary - destructive!
    for pr in p._r:
        if pr._tag == 'struct' and not(pd.get(pr._name) is None):
            pr._args = [ast_mk_var(nright)] + pr._args
            pr._name = pr._name.split("/")[0] + "/" + str(len(pr._args))

    # 3. Insert a narrator call
    p._r = [ast_mk_struct_ar("narrate",
                             [ast_mk_var(nleft),ast_mk_var(nright),
                              ast_mk_const(predname),
                              narrate_mklist(p._l._args[1:])])] + p._r

    return p

def narrate_predicates(prs: [ASTNode]) -> [ASTNode]:
    pd = {}
    for pr in prs:
        if pr._tag == 'top':
            pd[pr._l._name] = True

    for pr in prs:
        insert_narrate(pd, pr)

    return prs
