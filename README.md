# PyExpert 0.0.1

This is a small embeddable Prolog interpreter in Python3, designed primarily for
implementing explainable expert systems.



Usage:

```python

# Imports
from weak.prolog import prolog_driver,prolog_default_env,prolog_next_solution,prolog_core_library

# Initialise environment
env = prolog_default_env()

# Execute query
ret,vars = prolog_driver(env, '? append(A, B, [x,y]).')
print(vars)

# Inspect all the remaining solutions
while prolog_next_solution(env):
    print(vars)

```

# Weak sets

The main feature of this implementation is a `weak set` - a value that unifies
with any other weak set, resulting in a new set containing elements of both
sets. This is useful for implementing certain kinds of type systems and for
higher level hacks, such as tracing a Prolog execution (e.g., for a
human-readable narration of an expert system decision), implementing
constraints, etc.

For example:

```prolog
? weak(a,W1), weak(b,W1), weak(c,W2), W1=W2.
```

results in `W1=W2=[a,b,c]`

See `weak/narrate.py` for an example of an instrumentation of a Prolog code for
producing execution traces, or a "narration", which can then be used to
generate, for example, a plain English narration of the expert system thought
process.

See `tests/demo.py` for an example of constructing an explainable expert system.
