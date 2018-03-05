from weak.prolog import prolog_driver,prolog_default_env,prolog_next_solution,prolog_core_library
from weak.narrate import narrate_predicates

def test():
    lib = """
      ntest(X, Y) :-
          testX(X,aaa),
          testY(Y,bbb).
      testX(X, []).
      testX(X, V) :-
          X = V.
      testY(X, V) :-
          X = V. 

    """
    
    query1 = '? append(A, B, [x,y]).'
    query2 = '? revert([a,b,c,d,e], A).'
    query3 = '? revert(A,[a,b,c]).'
    query4 = '? unifiq([x,y,x,z,y,x,z], L).'

    query5 = '? weak(xxx,A), weak(yyy,B), weak(zzz,A), A=B.'

    query6 = '? weak(nil, N),  ntest(N, aaa, bbb), weak_to_list(N, L), debrief(L,LL), printlist(LL, X), print(X).'
    env = prolog_default_env()
    prolog_driver(env, prolog_core_library)
    prolog_driver(env, lib, [narrate_predicates])
    ret,vars = prolog_driver(env, query1)
    assert(ret)
    print(vars)
    assert(str(vars['B'])=="cons/2(x,cons/2(y,nil/0()))")
    assert(prolog_next_solution(env))
    print(vars)
    assert(str(vars['A'])=="cons/2(x,nil/0())")
    assert(prolog_next_solution(env))
    print(vars)
    assert(str(vars['B'])=="nil/0()")
    ret,vars = prolog_driver(env, query2)
    assert(ret)
    print(vars)
    assert(str(vars['A'])=='cons/2(e,cons/2(d,cons/2(c,cons/2(b,cons/2(a,nil/0())))))')
    ret,vars = prolog_driver(env, query3)
    assert(ret)
    print(vars)
    assert(str(vars['A'])=='cons/2(c,cons/2(b,cons/2(a,nil/0())))')
    ret,vars = prolog_driver(env, query4)
    assert(ret)
    print(vars)
    assert(str(vars['L'])=='cons/2(z,cons/2(y,cons/2(x,nil/0())))')
    
    ret,vars = prolog_driver(env, query5)
    assert(ret)
    print(vars)
    assert(prolog_next_solution(env))
    print(vars)

    ret,vars = prolog_driver(env, query6)
    assert(ret)

    ret,vars = prolog_driver(env, '? A="a a ", "b b" = B, concat(A,B,C), and(print(C),print(666)).')
    assert(ret)
    assert(str(vars['C'])=='a a b b')
    ret,vars = prolog_driver(env, '? A=1,B=2,or(A=B,print(bbb)).')
    assert(ret)
    ret,vars = prolog_driver(env, '? printlist([[a],[b,c],d],R).')
    assert(ret)
    print(vars)
    assert(str(vars['R'])=='((a) (b c) d)')
    ret,vars = prolog_driver(env, '? weak(xxx,A), weak(yyy,B), weak(zzz,A), A=B, weak_to_list(A,R), printlist(R,C), print(C).')
    assert(ret)

    ret,vars = prolog_driver(env, '? A=[a,b,c], call(printlist(A),B), print(B).')
    assert(ret)

test()
        
