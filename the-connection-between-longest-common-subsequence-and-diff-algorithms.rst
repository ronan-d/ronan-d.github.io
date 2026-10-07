The connection between longest common subsequence and diff algorithms
=====================================================================

If you read `the diff program's Wikipedia page <wiki_>`_, you might be intrigued by the following sentence:

   The operation of diff is based on solving the longest common subsequence problem.

.. _wiki: https://en.wikipedia.org/wiki/Diff

In this post, I will illustrate this claim using examples in Isabelle/HOL.

Subsequences, formally
----------------------

Let's give a formal definition of "list `l1` is a subsequence of list `l2`".
This will be the following inductively defined predicate:

```isabelle
inductive is_subseq :: "'a list ⇒ 'a list ⇒ bool" where
nil_subseq_nil: "is_subseq Nil Nil" |
subseq_take: "is_subseq l1 l2 ⟹ is_subseq (Cons x l1) (Cons x l2)" |
subseq_skip: "is_subseq l1 l2 ⟹ is_subseq l1 (Cons x l2)"
```
