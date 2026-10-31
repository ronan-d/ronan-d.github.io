From Stdlib Require Import List. Import ListNotations.

(** First, let's copy the bits from part 1 that we're going to need: *)

Parameter T: Set.

Inductive is_subseq : list T -> list T -> Prop :=
| nil_subseq_nil : is_subseq [] []
| subseq_take x l1 l2 : is_subseq l1 l2 -> is_subseq (x :: l1) (x :: l2)
| subseq_skip x l1 l2 : is_subseq l1 l2 -> is_subseq l1 (x :: l2).

(** Good. Welcome to part 2 of Difftopia. In part 1, we gave an inductive
    definition of what it means for a sequence to be a subsequence of another.
    In this part, we'll see that there exists a decision procedure that
    reflects this definition. That is, provided that [T] has decidable
    equality. Let's assume so: *)

Parameter T_eq : forall x y : T, {x = y} + {x <> y}.

(** How can we effectively check that a list [l1] is a subsequence of a list
    [l2]?
    
    First, if [l1] is empty, it is certainly a subseqence of [l2].
    
    Otherwise and if [l2] is empty, [l1] is certainly not a subsequence of [l2].
    
    Last, if neither [l1] or [l2] is empty, we can compare their first elements.
    If they're equal, we recursively check whether the tail of [l1] is a
    subsequence of the tail of [l2]. If the heads are not equal, we recursively
    check whether the tail of [l1] is a subsequence of the entire [l2]. *)
