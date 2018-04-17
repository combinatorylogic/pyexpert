import types
from weak.prolog_ast import *
import weak.prolog_parser

##
## Introduction.
##

# The reason we want a capable Prolog engine for the rule inference is simple -
# our goal is to narrate the order of reasoning that lead to a decision, and
# hacking a Prolog is the easiest way to achieve it. Instead of doing what any
# garden variety Prolog would do - i.e., say "Yes" or "No" to any question you
# ask, our hacked Prolog must be able to implicitly record the path it took to
# come to this conclusion.
#
# Sadly, a more compact and easy to understand ad hoc Prolog interpreter is
# harder to hack and extend, therefore we're starting here with implementing a
# more grown up, WAM-inspired kind of a Prolog compiler.
#
# This implementation is split into five chapters. First describes a destructive
# unification, aggravated by peculiarities of a Python implementation of a
# WAM-like memory model.
#
# Second chapter is introducing choice points and an execution environment,
# preparing us for the idea of backtracking.
#
# Third chapter goes into details of execution primitives, while fourth is
# constructing a compiler from an intermediate language (not quite a Prolog yet)
# into this set of primitives.
#
# Finally, fifth chapter introduces a front-end compiler from our augmented
# Prolog to an intermediate language.
#

##
## Chapter 1. Unification.
##

#
# In this chapter we'll explore the Prolog unification and a simple memory model.
#
# Prolog can only deal with the following data structure, called 'term':
#
# term := const
#      |  var
#      |  struct(ident, term...)
#      ;
#
# In order to be able to implement unification and backtracking we'll also
# introduce a 'reference' cell type.  All the term variants and references are
# implemented as instances of a 'Cell' class, with a field '_tag' holding a type
# descriptor - "VAR", "REF", "CONST" and "STRUCT".
#
# For efficiency and simplicity we'll allocate those tags statically and then
# we'll use a physical equivalence to compare tags.
prolog_tag_var = "VAR"
prolog_tag_ref = "REF"
prolog_tag_const = "CONST"
prolog_tag_struct = "STRUCT"

# And, in addition to the standard Prolog cell types, we'll define a "weak set" cell:
prolog_tag_weak = "WEAK"

# Helper functions to check Cell types - note the use of a physical equivalence operator 'is'.
def prolog_is_var(v):    return v._tag is prolog_tag_var
def prolog_is_ref(v):    return v._tag is prolog_tag_ref
def prolog_is_struct(v): return v._tag is prolog_tag_struct
def prolog_is_const(v):  return v._tag is prolog_tag_const
def prolog_is_weak(v):   return v._tag is prolog_tag_weak

# A Prolog memory cell, with a pretty-printer (__repr__) for convenience.
class Cell:
    def __init__(self, tag):
        self._tag = tag
    def __repr__(self):
        if (prolog_is_var(self)):
            return "V"
        elif (prolog_is_ref(self)):
            return self._ref.__repr__()
        elif (prolog_is_const(self)):
            return str(self._val)
        elif (prolog_is_struct(self)):
            return str(self._id) + "(" + ",".join([a.__repr__() for a in self._args]) + ")"
        elif (prolog_is_weak(self)):
            return "@[" + ",".join([a.__repr__() for a in self._lst]) + "]"
        else:
            return "<?>"

# Simple constructor functions for different cell types. We have to distinguish
# vars from weak sets here in order to support a correct backtracking for both.
def prolog_mk_var():   v = Cell(prolog_tag_var); v._lst = None; return v
def prolog_mk_weak():  v = Cell(prolog_tag_weak); v._lst = []; return v
def prolog_mk_ref(r):  v = Cell(prolog_tag_ref); v._ref = r; return r
def prolog_mk_struct(sid, args):
    v = Cell(prolog_tag_struct)
    v._id = sid; v._args = args
    return v
def prolog_mk_const(c):
    v = Cell(prolog_tag_const)
    v._val = c
    return v

# Reference is a special kind of cell - it contains a reference to another cell,
# which can also be a reference.  For most of our purposes we're only interested
# in the end of this chain, so we have to follow the REF-type cells recursively
# until a non-REF value is found.
def prolog_deref(v: Cell) -> Cell:
    if (prolog_is_ref(v)): return prolog_deref(v._ref)
    else:                  return v

# A variable is also a special kind of cell - in can be turned into a
# reference. Unifying a variable with another cell turns this variable into a
# reference pointing to that cell. Every time we turn a variable into a
# reference we have to store it in our current choice point list of unified
# variables - we'll have to convert them all back to variables if we backtrack
# to this choice point.
#
# Note that this is exactly the reason why this implementation is called a
# "destructive unification" - variables are destroyed when unified, and restored
# when backtracking.
def prolog_set_var(env, v, r):
    # flip a Var into a Ref
    prolog_remember_cell(env, v)
    v._tag = prolog_tag_ref; v._ref = r
    return r

# A helper function - check two constant cells equality
def prolog_const_eq(a,b):
    return a._val == b._val

# Now, behold: unification itself.
# Unification rules are simple:
#  unify(X,X) = True
#  unify(X,?) = True, X is turned into a reference to ?
#  unify(?,X) = True, X is turned into a reference to ?
#  unify(struct(...), struct(...)) = True if structures have same tags,
#        same number of arguments and all arguments unify
#  unify(const(...), const(...)) = True if constant values are equivalent
#  unify(weak(...), weak(...)) = True, always, resulting in merging two weak sets
#  For everything else it's = False
#
def prolog_unify(env, a:  Cell, b: Cell) -> bool:
    da = prolog_deref(a)
    db = prolog_deref(b)
    if da is db:
        return True
    elif (prolog_is_var(da)):
        prolog_set_var(env, da, b)
        return True
    elif (prolog_is_var(db)):
        prolog_set_var(env, db, a)
        return True
    elif (prolog_is_struct(da) and prolog_is_struct(db)):
        return prolog_unify_structs(env, da, db)
    elif (prolog_is_const(da) and prolog_is_const(db)):
        return prolog_const_eq(da,db)
    elif (prolog_is_weak(da) and prolog_is_weak(db)):
        if da is db:
            return True
        else: return prolog_fuse_weak(env, da, db)
    else:
        return False

def prolog_fuse_weak(env, da, db):
    newlst = da._lst + db._lst
    nw = prolog_mk_weak(); nw._lst = newlst
    db._tag = prolog_tag_ref
    db._ref = nw
    da._tag = prolog_tag_ref
    da._ref = nw
    prolog_remember_cell(env, da)
    prolog_remember_cell(env, db)
    return True

# Attempt to unify two structures (terms). Terms unify only if their tags are
# equal, they have the same number of arguments, and all the arguments unify.
def prolog_unify_structs(env, a, b):
    if a._id is b._id:
        argsa = a._args
        argsb = b._args
        if len(argsa)!=len(argsb):
            return False
        for (a,b) in zip(argsa,argsb):
            if  not(prolog_unify(env, a, b)):
                return False
        return True
    return False

##
## Chapter 2. Choice points and execution environments:
##

# In the previous chapter we used a function 'prolog_remember_cell' to store the
# fact of a variable unification in the current execution environment. Here
# we'll give it a definition, and we'll introduce the structure of choice points
# and execution environments.
#
# Every time Prolog have more than one variants of a predicate to run, a choice
# point is created. It stores a list of variables that were turned into
# references by unification after this choice point was created, and a list of
# next variants to try upon backtracking. Every time we backtrack, all the new
# references are turned back into variables and then a next continuation is
# executed.


class ChoicePoint:
    def __init__(self, env):
        self._vars = []
        self._cnts = []
        self._prev = None
        self._env = env
        self._cont = None

class PrologEnv:
    def __init__(self):
        self._chpoint = ChoicePoint(self)
        self._preds = {}
        self._collapsed = {}

# Store a variable cell in the current choice point kill list
def prolog_remember_cell(env: PrologEnv, r):
    env._chpoint._vars.append(r)

##
## Chapter 3. Execution primitives.
##

#
# Execution primitives are used to construct the interpreter. They closely
# correspond to the elements of the intermediate language described in the
# Chapter 4.
#

# Create a new choice point in the current environment, with a given current continuation and
#    a list of choice continuations
def prolog_new_choice_point(env: PrologEnv, cont, cnts):
    prevchp = env._chpoint
    chp = ChoicePoint(env)
    chp._prev = prevchp
    chp._cont = cont
    chp._cnts = cnts[1:]
    env._chpoint = chp
    return cnts[0](env, cont)

# Execute the next continuation in the list, or, if nothing is left there, get
# back to a previous choice point Note that we're not even testing if it exists
# - we'll always provide the "final" choice point in the top level interpreter.
def prolog_next_choice_point(chp):
    if (len(chp._cnts)>0):
        cnt = chp._cnts[0]
        chp._cnts = chp._cnts[1:]
        return lambda: cnt(chp._env,chp._cont)
    elif chp._prev:
        chp._env._chpoint = chp._prev
        return lambda: prolog_failure_f(chp._env)
    else:
        return False

# And the most important part of the backtracking mechanism - failure, a
# function that is executed every time when unification fails. Note the variable
# cleansing: all the variables that were unified from the beginning of the most
# recent choice point are wiped out before we proceed to the next variant in the
# current choice point.
def prolog_failure_f(env: PrologEnv):
    chp = env._chpoint
    # Reset the variables created in this choice point - this is an equivalent to stack unwind in WAM
    for v in chp._vars:
        if v._lst is None:  v._tag = prolog_tag_var
        else:               v._tag = prolog_tag_weak
        v._ref = None
    chp._vars = []
    return prolog_next_choice_point(chp)
    
# Note the 0-argument lambda functions returned by the choice point function?
# The same are created by the other execution primitives too. They're handled by
# the following CPS mini-interpreter - this way we're avoiding possible stack
# overflows (because Python cannot do proper tail calls optimisation anyway):
def prolog_mini_cps(f):
    while type(f) is types.LambdaType:
        f = f()
    return f

# Now we'll define the implementation of VarEnv. It contains a reference to the Prolog environment,
# a current continuation, and two dictionaries - variables (valid within the current context, we
# don't have any lexical scoping) and arguments (which is filled in by a caller).
class VarEnv:
    def __init__(self, env, cont):
        self._env = env
        self._cont = cont
        self._vars = []
        self._args = {}
    
# The following functions are primitives used by the compiler above.
def prolog_int_intros(varenv: VarEnv, nvars, nxt):
    varenv._vars = [prolog_mk_var() for n in range(nvars)]
    return nxt(varenv)

def prolog_int_unify(varenv: VarEnv, va, vb, nxt):
    if (prolog_unify(varenv._env, va, vb)):
        return nxt(varenv)
    else:
        return prolog_failure_f(varenv._env)


def prolog_int_choice_point(varenv: VarEnv, vconts):
    def cntf(varenv, vc):
        return lambda env, cont: vc(prolog_get_envcont(varenv, env, cont))
    nconts = [cntf(varenv,vc) for vc in vconts]
    return prolog_new_choice_point(varenv._env, varenv._cont, nconts)

##
## Chapter 4. Translating backend language into the execution primitives.
##

#
# In this chapter we'll get familiar with the language that appears after a
# first step of compilation of our source Prolog. This language already have
# explicit variable declarations (intros), explicit continuations and choice
# points. All the predicate calls arguments are either variables or constants,
# and argument unification is explicit. This language is already ripe for a
# direct interpretation.
#
#
# Backend language is defined as follows:
#
# toplevel := function(name, *arg, expr)
# expr := intros(*var, expr)
#       | unify(ctor, ctor, expr)
#       | choose(*expr)
#       | call_with(ident,*callarg,expr)
#       | tailcall(ident,*callarg)
#       | proceed()
# ctor := new(name, *ctor)
#       | const(...)
#       | var(name)
#       | arg(name)
# callarg := var(name)
#          | arg(name)
#          | const(...)
#
# Let's have a closer look at all the possible expressions:
#   intros(*var,expr): will allocate new variable cells with given names and make them
#      available within the context of its inner expression
#   unify(ctor:a, ctor:b, expr): will execute two constructors (i.e., allocate the cells
#          or use the named variable or argument cells), unify them and then execute
#          the inner expression
#   choose(*expr): create a new choice point, linked to the existing one. Peek the first expression
#          and push the rest into the choice point continuations list. Execute the first expression,
#          and if it is true, carry on with the current continuation, otherwise execute the fail
#          procedure (which will keep taking continuations from a choice point until it's empty, and then
#          move on to an upper level choice point).
#   call_with(ident, *callarg, expr): call a predicate with given primitive
#          arguments (variables, arguments and constants) and a given continuation
#   tailcall(ident, *callarg): the same, but with a current continuation only
#
#

#
#  We'll translate this intermediate language into lambda functions that take a
#  VarEnv instance as a sole argument.  VarEnv holds a list of current predicate
#  arguments, current predicate variables and a reference to an environment and
#  a continuation, to make this interpreter work together with the execution
#  primitives defined above.
#
def prolog_attempt_const_struct_inner(expr):
    if expr._tag == 'var' or expr._tag == 'arg':
        raise ValueError('var')
    if expr._tag == 'new':
        return prolog_mk_struct(expr._id,
                                [prolog_attempt_const_struct_inner(c)
                                 for c in expr._args])
    if expr._tag == 'const':
        return prolog_mk_const(expr._val)
    else:
        raise ValueError("...")

def prolog_attempt_const_struct(expr):
    try:
        return prolog_attempt_const_struct_inner(expr)
    except ValueError:
        return None

def prolog_compile_ctor(cenv, expr):
    cstruct = prolog_attempt_const_struct(expr)
    if cstruct:
        return lambda varenv: cstruct
    
    if expr._tag == 'new':
        cargs = [prolog_compile_ctor(cenv, a) for a in expr._args]
        return lambda varenv: prolog_mk_struct(expr._id, [c(varenv) for c in cargs])
    elif expr._tag == 'const':
        c = prolog_mk_const(expr._val)
        return lambda varenv: c
    elif expr._tag == 'var':
        (aenv, venv, nv) = cenv
        vnum = venv[expr._name]
        return lambda varenv: varenv._vars[vnum]
    elif expr._tag == 'arg':
        (aenv, venv, nv) = cenv
        anum = aenv[expr._name]
        return lambda varenv: varenv._args[anum]
    else:
        raise ValueError("ctor tag")

def prolog_update_cenv(cenv, vlst):
    (aenv, venv, nv) = cenv
    newvars = venv.copy()
    for v,i in zip(vlst, range(len(vlst))):
        newvars[v] = i + nv
    return (aenv, newvars, nv+len(vlst))

def prolog_compile_intermediate(cenv, expr):
    if expr._tag == 'intros':
        nxt = prolog_compile_intermediate(prolog_update_cenv(cenv, expr._vars), expr._nxt)
        nvars = len(expr._vars)
        return lambda varenv: prolog_int_intros(varenv, nvars, nxt)
    elif expr._tag == 'unify':
        ctor_a = prolog_compile_ctor(cenv, expr._a)
        ctor_b = prolog_compile_ctor(cenv, expr._b)
        nxt = prolog_compile_intermediate(cenv, expr._nxt)
        return lambda varenv: prolog_int_unify(varenv, ctor_a(varenv), ctor_b(varenv), nxt)
    elif expr._tag == 'choose':
        vconts = [prolog_compile_intermediate(cenv, e) for e in expr._opts]
        return lambda varenv: prolog_int_choice_point(varenv, vconts)
    elif expr._tag == 'call_with':
        vargs = [prolog_compile_ctor(cenv, a) for a in expr._args]
        vnext = prolog_compile_intermediate(cenv, expr._nxt)
        return prolog_compile_call(expr._name, vargs, vnext)
    elif expr._tag == 'tailcall':
        vargs = [prolog_compile_ctor(cenv, a) for a in expr._args]
        return prolog_compile_call(expr._name, vargs, None)
    elif expr._tag == 'proceed':
        return lambda varenv: lambda: varenv._cont(varenv._env)
    else:
        raise ValueError("expr tag")

def prolog_compile_call(name, args, nxt):
    def callfn1(varenv, fn, fargs):
        newenv = prolog_new_varenv(varenv._env, varenv._cont)
        for (na, a) in zip(fargs, args):
            newenv._args[na] = a(varenv)
        return lambda: fn(newenv)
    def callfn2(varenv, fn, fargs):
        nfun = lambda env: nxt(varenv)
        newenv = prolog_new_varenv(varenv._env, nfun)
        for (na, a) in zip(fargs, args):
            newenv._args[na] = a(varenv)
        return lambda: fn(newenv)
    refn = None
    refargs = None
    def wrapper(varenv, fn):
        nonlocal refn,refargs
        if refn is None:
            refn, refargs =  varenv._env._preds[name]
        return lambda: fn(varenv, refn, refargs)
    if nxt is None:
        return lambda varenv: wrapper(varenv, callfn1)
    else:
        return lambda varenv: wrapper(varenv, callfn2)

# Construct a new varenv with the same sets of variable and arguments, replacing an execution environment
# and a continuation fields.
def prolog_get_envcont(varenv: VarEnv, env: PrologEnv, cont):
    newenv = VarEnv(env,cont)
    newenv._vars = varenv._vars
    newenv._args = varenv._args
    return newenv

# Make a new varenv with empty variables and arguments sets.
def prolog_new_varenv(env: PrologEnv, cont):
    return VarEnv(env, cont)

def enumlist(l):
    r = {}
    for v,i in zip(l,range(len(l))):
        r[v] = i
    return r

def prolog_gen_cenv(args):
    argsmap = enumlist(args)
    varsmap = {}
    return (argsmap, varsmap, 0)

# Top level predicate definitions handling:
def prolog_define(env: PrologEnv, top):
    if top._tag == 'function':
        args = top._args
        cenv = prolog_gen_cenv(top._args)
        body = prolog_compile_intermediate(cenv, top._body)
        iargs = [i for i in range(len(args))]
        env._preds[top._name] = (body, iargs)
    else:
        raise ValueError("top tag")

def prolog_define_primitive(env: PrologEnv, name: str, args: list, fn):
    def get_args(varenv, arglist):
        a = varenv._args
        return [a[nm] for nm in arglist]
    fnc = lambda varenv:  fn(varenv._env, varenv._cont, *get_args(varenv, args))
    iargs = [i for i in range(len(args))]
    env._preds[name] = (fnc, args)

prolog__cons = prolog_symbol("cons/2")
prolog__nil = prolog_symbol("nil/0")

def prolog_mk_cons_cell():
    return prolog_mk_struct(prolog__cons, [None,None])
def prolog_cons_sethead(c, v):
    c._args[0] = v
def prolog_cons_settail(c, v):
    c._args[1] = v
def prolog_cons_setnil(c):
    c._id = prolog__nil
    c._args = []


##
## Chapter 5. Translating a source Prolog into an intermediate language.
##

#
# Source language is also built of the ASTNodes, with the following variants:
#
# top := def(name, *terms, *terms)
# term := var(name)
#      |  const(value)
#      |  struct(name, *terms)
#
# For the facts, body terms list is empty. We assume that lists of definitions are already grouped
# by name. We assume that names already contain their arity.
#

#
# We'll compile our frontend Prolog into the intermediate language in few small staps:
#
#  * group together the predicates with the same  name.
#  * remove complex (structural) arguments from the predicate calls
#  * explicitly unify predicate arguments with their values
#  * translate sequences of predicate calls into the intermediate language, inject intros
#

# First translation phase would introduce a new top node variant:
# top += defx(name, *options)
# option := opt(*terms, *terms)
#
# Essentially it just puts all the variants of the same predicate under a single entry.
def prolog_lower_options(tops):
    ret = []
    prevname = ""
    current = []
    def mkopt(args, body):
        nd = ASTNode('opt'); nd._args = args; nd._body = body
        return nd
    def flush(name, acc):
        if len(acc)>0:
            nd = ASTNode('defx')
            nd._name  = name
            nd._opts = [mkopt(a,b) for [a,b] in acc]
            ret.append(nd)
    for t in tops:
        if t._name == prevname:
            current.append([t._args, t._body])
        else:
            flush(prevname, current)
            prevname = t._name
            current = [ [t._args, t._body] ]
    flush(prevname, current)
    return ret
                
# Second translation phase takes lists of terms in the option bodies and
# flattens complex arguments into new variable assignments.
#
# equals/2 is treated as a special predicate that is translated into unification
# directly - i.e., its arguments do not need to be flattened.
globsymbolscounter = 0
def gensym() -> str:
    global globsymbolscounter
    globsymbolscounter = globsymbolscounter + 1
    return '_S' + str(globsymbolscounter)

def prolog_lower_call(b):
    fn = b._args[0]
    if (fn._tag != "struct"):
         raise ValueError('high order constructive call is not supported')
    fn0 = fn._name.split("/")[0] # strip the arity
    fn1 = prolog_symbol(fn0 + "/" + str(len(fn._args) + len(b._args) - 1))
    b1 = ast_mk_struct(fn1, fn._args + b._args[1:])
    b2 = ast_mk_struct(prolog_symbol("call/1"), [b1])
    return b2

def prolog_lower_flatten_inner(body):
    ret = []
    def insarg(a):
        if a._tag == "struct":
            newvar = ast_mk_var(gensym())
            neweq = ASTNode("struct"); neweq._name = "equals/2"
            neweq._args = [newvar, a]
            ret.append(neweq)
            return newvar
        else:
            return a
    for b in body:
        if b._tag == "struct" and (b._name == "call/2"
                                   or b._name == "call/3"): # rewrite a special case call/N
            b = prolog_lower_call(b)
        elif b._tag == "struct" and b._name != "equals/2":
            newargs = [insarg(a) for a in b._args]
            b._args = newargs
        ret.append(b)
    return ret

# This pass is destructive - AST is modified directly
def prolog_lower_flatten(tops):
    for t in tops:
        for o in t._opts:
            o._body = prolog_lower_flatten_inner(o._body)
    return tops

# Third translation pass will lower option arguments into unifications A
# potential for optimisation here: for simple variable arguments rewrite all the
# variable occurrences with an argument reference directly, instead of injecting
# a new unification.
def prolog_lower_args_inner(defargs, args, body):
    ret = []
    for d,a in zip(defargs, args):
         neweq = ASTNode("struct"); neweq._name = "equals/2"
         neweq._args = [d, a]
         ret.append(neweq)
    for b in  body:
        ret.append(b)
    return ret

# Here we'll finally drop 'defx' nodes and replace them with 'function' nodes
# (still containing _opts field though)
def prolog_lower_args(tops):
    ret = []
    def makeargs(n):
        return ["_A"+str(i) for i in range(n)]
    for t in tops:
        nargs = len(t._opts[0]._args)
        arglist = makeargs(nargs)
        argnodes = [ast_mk_arg(a) for a in arglist]
        nopts = []
        for o in t._opts:
            body = prolog_lower_args_inner(argnodes, o._args, o._body)
            nopts.append(body)
        nfun = ASTNode("function")
        nfun._args = arglist
        nfun._opts = nopts
        nfun._name = t._name
        ret.append(nfun)
    return ret
    
# Now we'll translate our flattened lists of terms into an intermediate language
def prolog_lower_body_inner(itbody):
    nxt = next(itbody, None)
    if (nxt is None):
        return ast_mk_proceed() # TODO: detect tail calls
    cnt = prolog_lower_body_inner(itbody)
    if (nxt._tag == 'struct' and nxt._name == 'equals/2'):
        return ast_mk_unify(prolog_lower_ctor(nxt._args[0]),prolog_lower_ctor(nxt._args[1]),cnt)
    elif (nxt._tag == 'struct'):
        return ast_mk_call_with(nxt._name, [prolog_lower_ctor(a) for a in nxt._args], cnt)
    else:
        raise ValueError('me not understanding: ' + str(nxt) )

# Constructors are pretty much as they were straight out of a parser, with an
# only difference in using a 'new' node instead of 'struct'.
def prolog_lower_ctor(c):
    if c._tag == 'struct':
        nargs  = [prolog_lower_ctor(a) for a in c._args]
        return ast_mk_new(c._name, nargs)
    else:
        return c

# A boilerplate code for finding all possible var references.
def prolog_lower_intros_rec(nvars, code):
    if code._tag == 'var':
        nvars[code._name] = True
    elif code._tag == 'unify':
        prolog_lower_intros_rec(nvars, code._a)
        prolog_lower_intros_rec(nvars, code._b)
        prolog_lower_intros_rec(nvars, code._nxt)
    elif code._tag == 'call_with':
        for a in code._args:
            prolog_lower_intros_rec(nvars, a)
        prolog_lower_intros_rec(nvars,code._nxt)
    elif code._tag == 'tailcall':
        for a in code._args:
            prolog_lower_intros_rec(nvars, a)
    elif code._tag == 'new':
        for a in code._args:
            prolog_lower_intros_rec(nvars,a)

# We'll explicitly introduce all the variables mentioned in a given chunk of
# code, for simplicity.
def prolog_lower_intros(code):
    nvars = {}
    prolog_lower_intros_rec(nvars,code)
    if len(nvars)>0:
        return ast_mk_intros(list(nvars), code)
    else:
        return code

def prolog_lower_body(tops):
    for t in tops:
        if t._tag == 'function':
            nopts = []
            for o in t._opts:
                b = prolog_lower_intros(prolog_lower_body_inner(iter(o)))
                nopts.append(b)
            nbody = []
            if (len(nopts) > 1):
                nbody = ast_mk_choose(nopts)
            else:
                nbody = nopts[0]
            t._body = nbody
            t._opts = None
    return tops
    
# And now we'll chain all the compilation passes together
def prolog_compile(tops):
    '''
    Compile a Prolog AST into an intermediate language
    :param tops: A list of predicates
    :return: A list of IR function definitions
    '''
    p1 = prolog_lower_options(tops)
    p2 = prolog_lower_flatten(p1)
    p3 = prolog_lower_args(p2)
    p4 = prolog_lower_body(p3)
    return p4

def prolog_lower_tops(tops):
    ret = []
    for t in tops:
        name = t._l._name; args = t._l._args; body = t._r
        ret.append(ast_mk_def(name, args, body))
    return ret

# Now let's bring everything together:
#  - If it's a query, compile it as a function, extract a list of variables
#    names, execute the function directly with prepared variable cell arguments and
#    bind them to a dictionary using their names.
#  - Otherwise just compile the predicate definitions and store them in the environment.

class Prolog_suspend:
    def __init__(self, v):
        self.v = v

def prolog_driver_ast(env: PrologEnv, tops) -> (bool, dict):
    '''
    Refine, compile, pre-compile and run a list of Prolog predicates. Run only if a list
    contains a single "query" predicate
    :param env: runtime environment
    :param tops: list of predicate source ASTs
    :return: (answer, variables)
    '''
    # handle a special case
    if len(tops)==1 and tops[0]._l._name.split("/")[0] == '_query':
        args = [a._name for a in tops[0]._l._args]
        aargs = ["_A"+str(i) for i in range(len(args))]
        ccode = prolog_compile(prolog_lower_tops(tops))
        expr = ccode[0]._body
        cenv = prolog_gen_cenv(aargs)
        vexpr = prolog_compile_intermediate(cenv, expr)
        ve = prolog_new_varenv(env, lambda env: True)
        for a in range(len(args)):
            ve._args[a] = prolog_mk_var()
        fn = vexpr(ve)
        ret = prolog_mini_cps(fn)
        if isinstance(ret, Prolog_suspend):
            return False, ret
        if ret:
            argvals = {}
            for a,n in zip(args,range(len(args))):
                argvals[a] = ve._args[n]
            return True, argvals
        else: return False, {}
    else: # handle top-level definitions
        ccode = prolog_compile(prolog_lower_tops(tops))
        for c in ccode:
            # each 'c' is 'function'(name, args, body)
            prolog_define(env, c)
        return True, {}


def prolog_driver(env: PrologEnv, code: str, instrument = []) -> (bool, dict):
    '''
    Parse, compile and execute (if it is a query) a Prolog code
    :param env: valid Prolog runtime environment
    :param code: Prolog code in a default syntax
    :return: (answer, variables)
    '''
    ast1 = weak.prolog_parser.parse(code)
    for i in instrument:
        ast1 = i(ast1)
    return prolog_driver_ast(env, ast1)


# We can trigger a failure in order to explore the next possible solution.
def prolog_next_solution(env: PrologEnv) -> bool:
    """
    Fail the current state of a given runtime environment and attempt to find another solution.
    :param env: Prolog runtime environment
    :return: True if there is a solution
    """
    return prolog_mini_cps(prolog_failure_f(env))

def prolog_resume(suspend):
    return prolog_mini_cps(suspend.v)

def prolog_to_list(ap,l):
    """
    Convert a Prolog list (i.e., nested cons/2 and nil/0 terms) into nested Python lists,
    ignoring the dotted pairs (cons/2 cells where second argument is not a cons/2 cell or nil/0).

    Must be called as 'prolog_to_list(None, prolog_list)'
    :param ap: None
    :param l: Prolog list
    :return:  Python list
    """
    # prolog_deref(...) returns an actual value of a Prolog memory cell (which can be accessible via a long chain of
    # references).
    w = prolog_deref(l)
    if (prolog_is_struct(w)): # Both cons/2 and nil/0 are 'struct' type cells
        if w._id == 'cons/2':
            if (ap is None):  # We're starting a new Python list
                l = []
                l.append(prolog_to_list(None, w._args[0]))
                prolog_to_list(l, w._args[1])
                return l
            else: # Keep appending to an existing Python list
                ap.append(prolog_to_list(None, w._args[0]))
                prolog_to_list(ap, w._args[1])
                return ap
        elif w._id == 'nil/0':
            return []
    else:
        # Any other kind of a Prolog cell is just represented as a string
        return str(l)

# Make a copy of a Prolog data structure, removing all references and making a new set of variables
def prolog_collapse_struct(visited, v0):
    v = prolog_deref(v0)
    if id(v) in visited:
        return visited[id(v)]
    nv = None
    if prolog_is_struct(v):
        nargs = [prolog_collapse_struct(visited, a) for a in v._args]
        nv = prolog_mk_struct(v._id, nargs)
    elif prolog_is_const(v):
        nv = v
    elif prolog_is_var(v):
        nv = prolog_mk_var()
    visited[id(v)] = nv
    return nv

def prolog_shallow_list(src):
    r = prolog_mk_cons_cell()
    cur = r
    for i in src:
        prolog_cons_sethead(cur, i)
        tmp  = prolog_mk_cons_cell()
        prolog_cons_settail(cur, tmp)
        cur = tmp
    prolog_cons_setnil(cur)
    return r

def prolog_topmost_choice_point(env, cont):
    chp = ChoicePoint(env)
    chp._cnts = [cont]
    ex = env._chpoint
    while ex._prev:
        ex = ex._prev
    ex._prev = chp
    chp._vars = []
    ex._vars = []

def prolog_collapse_cnt(env, cnt, dst):
    def fn(env, xcont):
        ndsts = env._collapsed[id(dst)]
        out = prolog_shallow_list(ndsts)
        if prolog_unify(env, out, dst):
            return lambda: cnt(env)
        else:
            return prolog_failure_f(env)
    return fn
    
# Collapse all variants of src into a list, leave no possible next solutions
def prolog_collapse_fun(env, cnt, src, dst):
    if id(dst) in env._collapsed:
        ndst = prolog_collapse_struct({}, src)
        env._collapsed[id(dst)].append(ndst)
        return prolog_failure_f(env)
    else:
        env._collapsed[id(dst)] = []
        ndst = prolog_collapse_struct({}, src)
        env._collapsed[id(dst)].append(ndst)
        prolog_topmost_choice_point(env, prolog_collapse_cnt(env, cnt, dst))
        return prolog_failure_f(env)
    
def prolog_default_env(library = None) -> PrologEnv:
    '''
    Make a Prolog runtime environment and populate it with some essential primitives (cut, fail, call, ...)
    :param library: optionally, a string containing a core library to be used. If none, the default one is compiled.
    :return: an environment
    '''

    global prolog_core_library

    # Debugging output primitive
    def prolog_print_fun(env, cnt, x):
        print("Out: " + str(x))
        return lambda: cnt(env)

    # An implementation of a Prolog cut (!) predicate
    def prolog_cut_fun(env, cnt):
        chp = env._chpoint
        env._chpoint = chp._prev
        chp._prev._vars = chp._prev._vars + chp._vars
        return lambda: cnt(env)

    # An implementation of an explicit fail/0 predicate
    def prolog_fail_fun(env, cnt):
        return prolog_failure_f(env)

    # Construct a single weak element
    def prolog_weak_fun(env, cnt, v, d):
        c = prolog_mk_weak()
        c._lst.append(v)
        if (prolog_unify(env, c, d)):
            return lambda: cnt(env)
        else:
            return prolog_failure_f(env)

    # Construct an empty weak set
    def prolog_weak1_fun(env, cnt, d):
        c = prolog_mk_weak()
        if (prolog_unify(env, c, d)):
            return lambda: cnt(env)
        else:
            return prolog_failure_f(env)

    # Call/1 function
    def prolog_call1_fun(env, cnt, nd):
        dt = prolog_deref(nd)
        if not (prolog_is_struct(dt)):
            return prolog_failure_f(env)
        else:
            varenv = prolog_new_varenv(env, cnt)
            fn, fargs = env._preds[dt._id]
            for (na, a) in zip(fargs, dt._args):
                varenv._args[na] = a
            return lambda: fn(varenv)

    def prolog_call2_fun(env, cnt, nd, a1, a2):
        dt = prolog_deref(nd)
        newid = ""
        if (prolog_is_struct(dt)):
            newid = dt._id.split("/")[0] + "/2"
        elif (prolog_is_const(dt)):
            newid = dt._val + "/2"
        else:
            return prolog_failure_f(env)

        fn, fargs = env._preds[newid]
        varenv = prolog_new_varenv(env, cnt)
        for (na, a) in zip(fargs, [a1,a2]):
            varenv._args[na] = a
        return lambda: fn(varenv)

    def prolog_concat3_fun(env, cnt, s1, s2, r):
        ds1 = prolog_deref(s1)
        ds2 = prolog_deref(s2)
        if not (prolog_is_const(ds1) and prolog_is_const(ds2)):
            return prolog_failure_f(env)
        else:
            rs = ds1._val + ds2._val
            ret = prolog_mk_const(rs)
            if (prolog_unify(env, ret, r)):
                return lambda: cnt(env)
            else:
                return prolog_failure_f(env)

    def prolog_str2_fun(env, cnt, s, r):
        ds1 = prolog_deref(s)
        if not (prolog_is_const(ds1) or prolog_is_struct(ds1)):
            return prolog_failure_f(env)
        else:
            rs = str(ds1)
            ret = prolog_mk_const(rs)
            if (prolog_unify(env, ret, r)):
                return lambda: cnt(env)
            else:
                return prolog_failure_f(env)

    def prolog_weak2l_fun(env, cnt, w, l):
        w1 = prolog_deref(w)
        if not (prolog_is_weak(w1)):
            return prolog_failure_f(env)
        else:
            r = prolog_mk_cons_cell()
            cur = r
            for i in w1._lst:
                prolog_cons_sethead(cur, i)
                tmp = prolog_mk_cons_cell()
                prolog_cons_settail(cur, tmp)
                cur = tmp
            prolog_cons_setnil(cur)
            if (prolog_unify(env, r, l)):
                return lambda: cnt(env)
            else:
                return prolog_failure_f(env)

    env = PrologEnv()
    prolog_define_primitive(env, "print/1", ["X"], prolog_print_fun)
    prolog_define_primitive(env, "cut/0", [], prolog_cut_fun)
    prolog_define_primitive(env, "fail/0", [], prolog_fail_fun)
    prolog_define_primitive(env, "weak/2", ["V", "D"], prolog_weak_fun)
    prolog_define_primitive(env, "weak/1", ["D"], prolog_weak1_fun)
    prolog_define_primitive(env, "call/1", ["S"], prolog_call1_fun)
    prolog_define_primitive(env, "call2/3", ["S","A1","A2"], prolog_call2_fun)
    prolog_define_primitive(env, "concat/3", ["S1", "S2", "R"], prolog_concat3_fun)
    prolog_define_primitive(env, "str/2", ["S1", "R"], prolog_str2_fun)
    prolog_define_primitive(env, "weak_to_list/2", ["W", "L"], prolog_weak2l_fun)
    prolog_define_primitive(env, "collapse/2", ["Src", "Dst"], prolog_collapse_fun)

    if library is None:
        prolog_driver(env, prolog_core_library)

    return env

def mkcpsfun(env, nxt):
    def c():
        v = prolog_mini_cps(nxt)
        if isinstance(v, Prolog_suspend):
            env.globquery[0] = mkcpsfun(env, v.v)
        else:
            env.globquery[0] = lambda: None
    return c
    

def prolog_ask_fun(env, cnt, msg, options, dst):
    keyd = str(prolog_deref(msg))
    msgd = str(prolog_deref(msg))
    opts = prolog_to_list(None,prolog_deref(options))
    dst = prolog_deref(dst)
    
    def contfun():
        if keyd in env.globanswers:
            answ = prolog_mk_const(env.globanswers[keyd])
            if (prolog_unify(env, dst, answ)):
                return lambda: cnt(env)
            else:
                return prolog_failure_f(env)
        else:
            env.globquery[0] = mkcpsfun(env, contfun)
            env.display_fun(keyd, msgd, opts)
            return Prolog_suspend(contfun)
    return contfun()


def prolog_register_ask(env, answers, query, display_fun):
    prolog_define_primitive(env, "ask/3", ["Msg","Options", "Dst"],
                            prolog_ask_fun)
    env.globanswers = answers
    env.globquery = query
    env.display_fun = display_fun

# A library of essential functions for Prolog, implemented in core Prolog:
prolog_core_library = """
   equals(X,X).
   
   and(A,B) :- call(A), call(B).
   or(A,B) :- call(A).
   or(A,B) :- call(B).
   
   append([], L, L).
   append([H|T], L, [H|A]) :- append(T, L, A).
    
   revert([], []).
   revert([H|L], R) :- revert(L, RL), append(RL,[H],R).

   in(E, []) :- fail().
   in(E, [E|X]) :- !.
   in(E, [X|Y]) :- in(E,Y).

   unifiqinner([], R, R).
   unifiqinner([H|T], Prev, R) :- in(H,Prev),!,unifiqinner(T,Prev,R).
   unifiqinner([H|T], Prev, R) :- unifiqinner(T,[H|Prev],R).

   unifiq([], []) :- !.
   unifiq(L, R) :- unifiqinner(L,[],R),!.

   concat(A,B,C,R) :- concat(A,B,X),concat(X,C,R).

   printlist([], "[]").
   printlist([H], R) :- printlist(H,R1), concat("(",R1,")",R), !.
   printlist([H|T],R) :-  printlistinner([H|T],X),concat("(",X,")",R), !.
   printlist(X,R) :- str(X,R), !.
   
   printlistinner([],"[]"):-!.
   printlistinner([H], R) :- printlist(H,R),!.
   printlistinner([H|T], R) :- printlistinner(T,V), printlist(H,Z), concat(Z," ",V,R),!.
   printlistinner(X,R) :-  str(X,R),!.
   
   // A predicate for execution narration instrumentation
   narrate(N, M, Name, Args) :-
      weak(M),
      weak(entry([Name|Args],M), N).

   // deconstruct narration from the weak lists
   debrief(entry(V, W), [V| WL]) :- weak_to_list(W, WX), debrief(WX, WL),!.
   debrief([H|T], [R|Tl]) :- debrief(H,R),debrief(T,Tl),!.
   debrief(X, X) :- !.

   // Report a list-form of a narration
   explain(N, LL) :-
      weak_to_list(N, L), 
      debrief(L, LL).
      
   // A generic map
   map(Fn, [], []) :- !.
   map(Fn, [H|T], [Rh|Rt]) :- call2(Fn, H, Rh), map(Fn, T, Rt).

   // Tree merge
   treemerge([ [[Tg|Args]|TailA] | NextA], [ [[Tg|Args]|TailB] | NextB],
             [ [[Tg|Args]|TailAB] | NextAB]) :- !, treemerge(TailA, TailB, TailAB), treemerge(NextA, NextB, NextAB).
   treemerge(A, B, R) :- !, append(A, B, R).

   foldmerge([A], [A]).
   foldmerge([A, B | Next], R) :- !, treemerge([A], [B], [AB]), foldmerge([AB | Next], R).

   

  """
