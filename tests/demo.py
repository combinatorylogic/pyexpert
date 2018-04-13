from weak.prolog import prolog_driver, prolog_default_env, prolog_next_solution
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

prolog_driver(env, rules, [narrate_predicates])
prolog_driver(env, facts, [narrate_predicates])

# Execute query
prolog_driver(env, '? bird(N, X), explain(N,LL), printlist(LL, MM), print(MM).')

# Inspect all the remaining solutions
while prolog_next_solution(env):
    pass

