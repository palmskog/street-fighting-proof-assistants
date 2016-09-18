# Imp

This development formalizes a simple imperative programming language for
the University of Washington's Programming Languages course.

Imp supports integer operations, arrays, and first order functions.  We
provide a parser from a "sugared" flavor of the language to core Imp and a
pretty printer from Imp to Python.  This allows us to reason about Imp
programs in Coq and extract and run them in Python.

Like Python, Imp does not provide a type system.  This can make it
difficult to tell whether a program will ever get "stuck" (try to perform
an illegal operation).  The second half of the class will turn to the
lambda calculus and type theory to precisely study this problem, as well as
scope and higher order functions.

## Style

Lines are kept short to support low-resolution projection in the classroom.

Proofs are kept verbose to support students stepping through them.
