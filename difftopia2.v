From Stdlib Require Import List. Import ListNotations.

(** First, let's copy the bits from part 1 that we're going to need: *)

Parameter T: Set.

Inductive is_subseq : list T -> list T -> Prop :=
| nil_subseq_nil : is_subseq [] []
| subseq_take x l1 l2 : is_subseq l1 l2 -> is_subseq (x :: l1) (x :: l2)
| subseq_skip x l1 l2 : is_subseq l1 l2 -> is_subseq l1 (x :: l2).

Theorem nil_is_subseq_l : forall l, is_subseq [] l.
Proof. (** HIDE *)
  induction l as [| x l' IH ].
  - exact nil_subseq_nil.
  - apply subseq_skip.
    exact IH.
Qed.

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
  apply subseq_skip.
  inversion H; clear H; subst.
  - assumption.
  - apply (IH x l1).
    assumption.
Qed.

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
    check whether [l1] is a subsequence of the tail of [l2]. *)

Fixpoint is_subseq_rec (l1 l2 : list T) : bool := match l1, l2 with
| [], _ => true
| _, [] => false
| x1 :: l1', x2 :: l2' => if (T_eq x1 x2) then
    is_subseq_rec l1' l2'
  else
    is_subseq_rec l1 l2'
end.

(** The rest of this part is going to be about showing that [is_subseq_rec]
    indeed corresponds to [is_subseq]. *)

(** **** Exercise: 3 stars (tail_of_subseq_is_subseq_rec)

    Start by proving the equivalent of part 1's last theorem: *)

Theorem tail_of_subseq_is_subseq_rec : forall x l1 l2,
  is_subseq_rec (x :: l1) l2 = true -> is_subseq_rec l1 l2 = true.
Proof. (** HIDE *)
  intros.
  generalize dependent l1.
  generalize dependent x.
  induction l2 as [| x2 l2' IH ]; intros x l1 H.
  {
    cbn in H.
    discriminate.
  }
  assert (H0 : is_subseq_rec l1 l2' = true).
  {
    cbn in H.
    destruct (T_eq x x2).
    - assumption.
    - apply IH in H.
      exact H.
  }
  clear H.
  destruct l1 as [| x1 l1' ].
  {
    reflexivity.
  }
  cbn.
  destruct (T_eq x1 x2).
  - apply IH in H0.
    assumption.
  - assumption.
Qed.

(** **** Exercise: 2 stars (subseq_skip_rec) 

    Prove the equivalent of the [subseq_skip] constructor of [is_subseq]: *)

Theorem subseq_skip_rec : forall l1 x l2,
  is_subseq_rec l1 l2 = true -> is_subseq_rec l1 (x :: l2) = true.
Proof. (** HIDE *)
  induction l1 as [| x1 l1' IH ]; intros x l2 H.
  {
    reflexivity.
  }
  cbn.
  destruct (T_eq x1 x).
  - apply tail_of_subseq_is_subseq_rec in H.
    assumption.
  - assumption.
Qed.

(** **** Exercise: 3 stars (is_subseq_implies_is_subseq_rec) 

         Prove the inductive-to-recursive direction of the equivalence: *)

Theorem is_subseq_implies_is_subseq_rec : forall l1 l2,
    is_subseq l1 l2 -> is_subseq_rec l1 l2 = true.
Proof. (** HIDE *)
  intros l1 l2.
  generalize dependent l1.
  induction l2 as [| x2 l2' IH ]; intros l1 H.
  {
    inversion H; clear H; subst.
    reflexivity.
  }
  destruct l1 as [| x1 l1' ].
  {
    reflexivity.
  }
  cbn.
  destruct (T_eq x1 x2).
  - apply IH.
    subst x2.
    inversion H; clear H; subst.
    + assumption.
    + apply tail_of_subseq_is_subseq with (x := x1).
      assumption.
  - apply IH.
    inversion H; subst; clear H.
    + intuition.
    + assumption.
Qed.

(** **** Exercise: 3 stars (is_subseq_rev_implies_is_subseq)

    Now prove the other direction: *)

Theorem is_subseq_rec_implies_is_subseq : forall l1 l2,
  is_subseq_rec l1 l2 = true -> is_subseq l1 l2.
Proof. (** HIDE *)
  intros l1 l2.
  generalize dependent l1.
  induction l2 as [| x2 l2' IH ]; intros l1 H.
  {
    cbn in H.
    destruct l1.
    - exact nil_subseq_nil.
    - discriminate.
  }
  destruct l1 as [| x1 l1' ].
  {
    apply nil_is_subseq_l.
  }
  cbn in H.
  destruct (T_eq x1 x2); apply IH in H.
  - subst x2.
    apply subseq_take.
    assumption.
  - apply subseq_skip.
    assumption.
Qed.

Theorem is_subseq_rec_correct : forall l1 l2,
  is_subseq_rec l1 l2 = true <-> is_subseq l1 l2.
Proof.
  intros.
  split.
  - apply is_subseq_rec_implies_is_subseq.
  - apply is_subseq_implies_is_subseq_rec.
Qed.
