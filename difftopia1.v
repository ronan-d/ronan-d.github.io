From Stdlib Require Import List. Import ListNotations.

(** We're going to start this exploration of diff algorithms by looking at the
    concept of a subsequence. Start by reading the first paragraph of the Wikipedia
    entry at https://en.wikipedia.org/wiki/Subsequence.

    To formalize this idea into Rocq, we'll identify sequences with Rocq lists.
    For this, we'll need a type for the elements of our lists. To be as general as
    possible, we'll make it a type parameter [T]: *)

Parameter T: Set.

(** From now on, we'll use "sequence" as a synonym for "term of type [list T]".

    Let's concretize what it means for a list [l1] to be a subsequence of another
    list [l2]. For this, we'll define a binary relation over lists. In other words,
    something of type [list T -> list T -> Prop]. You can look at the
    "Properties of Relations" chapter of Software Foundations volume 1 if you
    need a refresher on binary relations.

    Given a sequence [l2], one way to construct a subsequence of it is to
    iterate over the elements of [l2] from right to left and, for each element,
    decide whether we include it in the subsequence or not.

    We capture this in the following inductive type: *)

Inductive is_subseq : list T -> list T -> Prop :=
(** When we start, we haven't looked at any element of [l2] and our
    work-in-progress subsequence is also empty: *)
| nil_subseq_nil : is_subseq [] []
(** When we take one step and look at an elemenf of [l2], one option is to
    include it in the subsequence: *)
| subseq_take x l1 l2 : is_subseq l1 l2 -> is_subseq (x :: l1) (x :: l2)
(** The other option is to leave the element out: *)
| subseq_skip x l1 l2 : is_subseq l1 l2 -> is_subseq l1 (x :: l2).

(** To get familiar with [is_subseq], I propose that you do a few exercises. *)

(** **** Exercise: 1 star (nil_is_subseq_l)

    You will surely agree that the empty list is a subsequence of any list [l].
    Prove the following theorem to make sure. *)

Theorem nil_is_subseq_l : forall l, is_subseq [] l.
Proof. (** HIDE *)
  induction l as [| x l' IH ].
  - exact nil_subseq_nil.
  - apply subseq_skip.
    exact IH.
Qed.

(** **** Exercise: 1 star (l_is_subseq_l)

    Likewise, every list is a subsequence of itself. *)

Theorem l_is_subseq_l : forall l, is_subseq l l.
Proof. (** HIDE *)
  induction l as [| x l' IH].
  - exact nil_subseq_nil.
  - apply subseq_take.
    exact IH.
Qed.

(** **** Exercise: 1 star (cons_not_subseq_nil)

    A non-empty list is never a subsequence of the empty list. *)

Theorem cons_not_subseq_nil : forall x l, ~ is_subseq (x :: l) [].
Proof. (** HIDE *)
  intros.
  intro.
  inversion H.
Qed.

(** OK, that was warmup. Let's look at another property that also seems rather
    obvious: given a non empty list [l1] of another list [l2], we can strip the
    first element of [l1] and what we get is still a subsequence of [l2]. *)

(** **** Exercise: 3 stars (tail_of_subseq_is_subseq)

    To conclude part 1, prove the following theorem: *)

Theorem tail_of_subseq_is_subseq : forall x l1 l2,
  is_subseq (x :: l1) l2 -> is_subseq l1 l2.
Proof. (** HIDE *)
  intros.
  generalize dependent l1.
  generalize dependent x.
  induction l2 as [| x2 l2' IH ].
  {
    intros.
    inversion H.
  }
  intros.
  assert (is_subseq l1 l2').
  {
    inversion H; clear H; subst.
    - assumption.
    - apply (IH x l1).
      assumption.
  }
  apply subseq_skip.
  assumption.
Qed.
