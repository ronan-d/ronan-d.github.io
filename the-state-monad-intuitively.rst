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

How we use state in imperative languages
----------------------------------------

We begin the analogy on the imperative side, with examples given in Rust. Say that
you have a function that computes the Fibonacci numbers:

.. code-block:: rust

   fn fib(n: u64) -> u64 {
       if n <= 1 { 1 } else { fib(n - 1) + fib(n - 2) }
   }

Now, say that in addition to getting the nth Fibonacci number, you also want to
get the number of recursive calls it took to compute it. Here's one way to proceed:

.. code-block:: rust

   fn fib_with_counter(n: u64, count: &mut u64) -> u64 {
       *count += 1;
       if n <= 1 { 1 } else { fib(n - 1) + fib(n - 2) }
   }

You can call this function like so:

.. code-block:: rust

   let mut count = 0;
   let f = fib_with_counter(10, &mut count);

What we changed from the original function is that we added a new parameter that's a mutable reference.

Same thing, (pure) functional language
--------------------------------------

Here's the function we use as a starting point, in Lean this time:

.. code-block:: lean

   def fib (n : Nat) : Nat :=
     if n <= 1 then 1 else fib (n - 1) + fib (n - 2)

Like in the previous section, we now want to also get the total number of calls that were made.
We cannot add a mutable reference as parameter like we did in Rust, but we'll do
something analogous the state monad in Lean's standard library, ``StateM``.

Let concentrate our attention to the function's type for the moment. Recall that
the signature of the original Rust function was

   (n: u64) -> u64

and that to add the call counter to it, we changed it to

   (n: u64\ :strong:`, count: &mut u64`) -> u64

In Lean, we're going to go from

   (n : Nat) : Nat

to

   (n : Nat) : :strong:`StateM Nat Nat`

This looks rather different from what we did in Rust. Here, the parameters don't change, it's the return type that does.

.. code-block:: lean

   def fib_with_counter (n : Nat) : StateM Nat Nat := do
     let count ← get
     set (count + 1)
     if n <= 1 then
       pure 1
     else do
       let f1 ← fib_with_counter (n - 1)
       let f2 ← fib_with_counter (n - 2)
       pure (f1 + f2)
