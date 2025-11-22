The state monad, intuitively
============================

.. role:: rust(code)
   :language: rust

.. role:: lean(code)
   :language: lean

In functional programming languages, there is an idiom called the "state monad".
In short, it makes it possible to simulate implicit state that can be mutated as
the program makes progress, even in programming languages that don't have mutable variables.

There exist detailed explanations of the state monad, like `this one`__. However,
it took a while for me for the concept to click. What worked in the end
was picturing a translation scheme from programs that use the state monads to equivalent
programs written in an imperative language. I'll now say more about this translation
scheme.

.. __: https://en.wikibooks.org/wiki/Haskell/Understanding_monads/State#

How we use state in imperative languages
----------------------------------------

We begin the analogy on the imperative side, with examples given in Rust. Say that
you have a function that computes the nth Fibonacci number:

.. code-block:: rust

   fn fib(n: u64) -> u64 {
       if n <= 1 { 1 } else { fib(n - 1) + fib(n - 2) }
   }

Now, say that in addition to getting the nth Fibonacci number, you also want to
return whether the number of recursive calls it took to compute it is even.
Here's one way to proceed:

.. code-block:: rust

   fn fib_with_parity(n: u64, is_even: &mut bool) -> u64 {
       *is_even = !*is_even;
       if n <= 1 {
           1
       } else {
           fib_with_parity(n - 1, is_even) + fib_with_parity(n - 2, is_even)
       }
   }

You can call this function like so:

.. code-block:: rust

   let mut is_even = true;
   let f = fib_with_parity(10, &mut is_even);

What we changed from the original function is that we added a new parameter that's a mutable reference
to a :rust:`bool`, and we flip that :rust:`bool` on entry to the function.

Same thing, (pure) functional language
--------------------------------------

Here's the function we use as a starting point, in Lean this time:

.. code-block:: lean

   def fib (n : Nat) : Nat :=
     if n <= 1 then 1 else fib (n - 1) + fib (n - 2)

Like in the previous section, we now want to also get the parity of the total number of calls that were made.
We cannot add a mutable reference as parameter like we did in Rust, but we'll do
something analogous using the state monad in Lean's standard library, :lean:`StateM`.

Let concentrate our attention to the function's type for the moment. Recall that
the signature of the original Rust function was

   (n: u64) -> u64

and that to add the call counter to it, we changed it to

   (n: u64\ :strong:`, is_even: &mut bool`) -> u64

In Lean, we're going to go from

   (n : Nat) : Nat

to

   (n : Nat) : :strong:`StateM Bool` Nat

This looks rather different from what we did in Rust. Here, the parameters don't change, it's the return type that does.
Instead of adding a mutable reference to :rust:`bool` as parameter, we made our return type :lean:`StateM Bool Nat`.

OK, now let's see the entire function.

.. code-block:: lean

   def fib_with_parity (n : Nat) : StateM Bool Nat := do
     let is_even ← get
     set (!is_even)
     if n <= 1 then
       pure 1
     else
       let f1 ← fib_with_parity (n - 1)
       let f2 ← fib_with_parity (n - 2)
       pure (f1 + f2)

It's not quite as concise as the Rust version, to say the least. In particular, the
recursive case went from

.. code-block:: rust

   fib_with_parity(n - 1, is_even) + fib_with_parity(n - 2, is_even)

to

.. code-block:: lean

   let f1 ← fib_with_parity (n - 1)
   let f2 ← fib_with_parity (n - 2)
   pure (f1 + f2)

There is one interesting thing here: since the recursive calls "have effects", Lean forces
to clearly specify in what order the recursive calls are evaluated. We either evaluate
:lean:`fib_with_parity (n - 1)` first and :lean:`fib_with_parity (n - 2)` second, or the other
way around. In the Rust version, the order of evaluation is not specified, and it is not
a problem because the two possible orderings have the same effect on the mutable :rust:`bool`.

Using :lean:`fib_with_parity` in Lean also takes a bit more than a function call,
we need it to give the initial value for the state and also "unwrap" the
:lean:`StateM Bool Nat` at the end. Here's how it's done:

.. code-block:: lean

   def pair := (fib_with_counter 10).run false
   def f := pair.fst
   def count := pair.snd

Note in particular the call to the :lean:`run` method with the initial value of the
state as argument.

Takeaways
---------

I think the above comparison clears up something about the state monad the can be
counterintuitive: making the return type of a function more complicated (e.g. by changing it
from :lean:`Nat` so :lean:`StateM Nat Bool`) actually makes the function's job easier (because
it gives it access to a piece of mutable state). I don't think that's very common
outside monadic-ish environment.

One situation this knowledge is helpful is when one, for a reason or another, is
programming in a pure functional language and finds that mutable state would be
helpful to achieve something. It suffices to imagine an imperative program that uses
the state passing a mutable reference around, and then the translation scheme above
can help devise an equivalent program that uses a state monad.
