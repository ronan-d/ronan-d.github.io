The connection between longest common subsequence and diff algorithms
=====================================================================

If you read `the diff program's Wikipedia page <wiki_>`_, you might be intrigued by the following sentence:

   The operation of diff is based on solving the longest common subsequence problem.

.. _wiki: https://en.wikipedia.org/wiki/Diff

In this post, I will illustrate this claim using examples in Isabelle/HOL.

Subsequences, formally
----------------------

Let's give a formal definition of "list :code:`l1` is a subsequence of list :code:`l2`".
This will be the following inductively defined predicate:

.. code-block:: isabelle

   inductive is_subseq :: "'a list ⇒ 'a list ⇒ bool" where
   nil_subseq_nil: "is_subseq Nil Nil" |
   subseq_take: "is_subseq l1 l2 ⟹ is_subseq (Cons x l1) (Cons x l2)" |
   subseq_skip: "is_subseq l1 l2 ⟹ is_subseq l1 (Cons x l2)"

The first constructor represents the fact that empty list is a subsequence of
itself.

The second and third constructors represent the basic operations we have
available when we construct a subsequence :code:`l1` from a list :code:`l2`.
We iterate over the elements of :code:`l2` from right to left and, for each
element, we either:

1. Put the element in our work-in-progress subsequence :code:`l1` (:code:`subseq_take`).
2. Leave out the element (:code:`subseq_skip`).
