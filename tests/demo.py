from pyexpert import *

# Initialise environment
env = prolog_default_env()

# An example taken from D. Merritt, 'Building Expert Systems in Prolog', 1989.
rules = '''

family(X) :- fail(). // must list all the facts stubs here,
color(X) :- fail().  // in order to include them in narration.
voice(X) :- fail().

bird(laysan_albatross):-
    family(albatross),
    color(white). 
bird(black_footed_albatross) :-
    family(albatross),
    color(dark). 
bird(whistling_swan) :-
    family(swan),
    voice(muffled_musical_whistle). 
bird(trumpeter_swan) :-
    family(swan), 
    voice(loud_trumpeting).

'''

facts = '''
family(swan).
color(X).
voice(X).
'''



# Rewrite the narration tree into a plain English - this approach can potentially be scaled to a
# full fledged Natural Language Generation system.

# Decision tree (as produced by 'explain' function) looks like this:
# [['bird', 'whistling_swan'], [['voice', 'muffled_musical_whistle']], [['family', 'swan']]]
#
# We can apply rewrite rules to transform it into something more readable.

fmtrules = '''
// narrate_birds(Decision_Tree, Narration)

narrate_birds([[bird,Name]|Why], ["Bird is ",Name,", because ", WhyX]) :-
  map(narrate_birds, Why, WhyX). // recursively apply rewrite rule 'narrate_birds' to sub-nodes of the decision tree
narrate_birds([[color,X]|Why], ["its colour is ", X, "; "]).
narrate_birds([[voice,X]|Why], ["its voice is ", X, "; "]).
narrate_birds([[family,X]|Why], ["it belongs to the '", X, "' family; "]).

// 'narrate_birds' rule generates nested lists of strings, need one final pass
// to assemble them into a single string.
assemble([H|T],S) :- !, assemble(H, Hx), assemble(T,Tx), concat(Hx,Tx,S).
assemble([],"").
assemble(X,X).
'''

prolog_driver(env, rules, [narrate_predicates])
prolog_driver(env, facts, [narrate_predicates])
prolog_driver(env, fmtrules)

# Execute query
ret, vars = prolog_driver(env,
    '''? bird(N, X), explain(N,[LL]), collapse(LL,LL1),
         foldmerge(LL1, LL2), map(narrate_birds, LL2, LX),
         map(assemble,LX,Result).''')

if ret:
    print(prolog_to_list(None, vars['LL2']))
    print(prolog_to_list(None, vars['Result']))
else:
    print("No answer.")

