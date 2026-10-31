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
