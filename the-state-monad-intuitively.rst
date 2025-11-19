The state monad, intuitively
============================

In functional programming languages, there's is an idiom called the "state monad".
In short, it makes it possible to simulate an implicit state that can be mutated as
the program makes progress, even in programming languages that don't have mutable variables.

There exist detailed explanations of the state monad, like `this one`__. However,
it took a while for me for the concept to click. What worked for me in the end
is picturing a translation scheme from programs that use the state monads to equivalent
programs written in a imperative language. I'll now say more about this translation
scheme.

.. __: https://en.wikibooks.org/wiki/Haskell/Understanding_monads/State#
