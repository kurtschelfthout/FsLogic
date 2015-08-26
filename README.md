# MiniKanren for FSharp

MiniKanren is a logic programming language embedded in Scheme, originally. It was, I believe, mainly popularized 
by David Nolen's port to Clojure, now core.logic. You can learn much more about it at http://minikanren.org.

This port aims to be philosophically close to the original implementation of MiniKanren, that is, it should be simple to read
and understand, perhaps in favor of doing optimizations like convert everything to continuation passing style. That said, 
while hopefully be fast enough to be used for real applications.

The main difference with original MiniKanren is that this is typed logic programming, i.e. it isn't statically possible to unify
a list with an int (whhich would not unify at runtime anyway).

In time I'd like to take some of the extensions on board, like alpha-kanren and I'm especially interested in cKanren.

For now, have a look at the tests for examples.
