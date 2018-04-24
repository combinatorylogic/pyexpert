from weak.prolog import prolog_driver, prolog_default_env, prolog_next_solution, prolog_to_list
from weak.narrate import narrate_predicates

# Initialise environment
env = prolog_default_env()

# An example taken from D. Merritt, 'Building Expert Systems in Prolog', 1989.
rules = '''

family(X) :- fail().
color(X) :- fail().
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

fmtrules = '''
t([[bird,Name]|Why], ["Bird is ",Name,", because ", WhyX]) :-
  map(t, Why, WhyX).
t([[color,X]|Why], ["its colour is ", X, "; "]).
t([[voice,X]|Why], ["its voice is ", X, "; "]).
t([[family,X]|Why], ["it belongs to the '", X, "' family; "]).

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
         foldmerge(LL1, LL2), map(t, LL2, LX),
         map(assemble,LX,Result).''')

if ret:
    print(prolog_to_list(None, vars['Result']))
else:
    print("No answer.")

