# Types of Datalog Programs

## SuperNice programs (a subset of the syntactically valid Datalog programs)

These are the datalog programs where each premise of a rule has only bare variables appearing as arguments to the premise.

A formal definition of a SuperNice program doesn't appear in this repo, since my compiler doesn't generate SuperNice programs.

## Runnable programs (a superset of the SuperNice programs)

These are those programs where each variable appearing in a rule appears "bare" at least once in a premise of the rule.

Formal definition is here: TODO add reference

## Queryable programs (a superset of the Runnable programs)

...

Formal definition is here: TODO add reference

TODO is there a nice way of talking about termination for general queryable programs?

## Remarks

I wrote a compiler (see src/ATLToDatalog.v) that transforms ATL programs into queryable datalog programs.
Going directly from ATL to runnable Datalog programs would've been quite unpleasant.

I wrote a compiler (see src/TODOputmeinmyownfile) that transforms Queryable Datalog programs into Runnable Datalog programs.
This "compiler" is pretty trivial, consisting of about a couple dozen lines of Gallina.
(On the other hand, its proof currently takes up about 1000 lines.)
TODO describe how to query the resulting runnable program.  

Since we have a mostly-generic way of transforming Queryable programs into runnable programs, compilers from Datalog to lower-level languages should not need to worry about compiling Queryable programs.
Perhaps they don't even need to consider the possibility of being queried, either.

It's not clear to me that there's a nice, efficient, general way of transforming Runnable programs into SuperNice programs, so compilers from Datalog to lower-level languages should probably be able to handle all Runnable programs (i.e., for many applications, just handling SuperNice programs might not suffice).
