From Stdlib Require Import List. Import ListNotations.

Parameter T: Set.

Parameter T_eq : forall x y : T, {x = y} + {x <> y}.

Inductive is_subseq : list T -> list T -> Prop :=
| nil_subseq_nil : is_subseq [] []
| subseq_take x l1 l2 : is_subseq l1 l2 -> is_subseq (x :: l1) (x :: l2)
| subseq_skip x l1 l2 : is_subseq l1 l2 -> is_subseq l1 (x :: l2).

Theorem cons_not_subseq_nil x l : ~is_subseq (x :: l) [].
Proof.
  intro.
  inversion H.
Qed.

Fixpoint is_subseq_rec (l1 l2 : list T) : bool := match l1, l2 with
| [], _ => true
| x1 :: l1', [] => false
| x1 :: l1', x2 :: l2' =>
    match T_eq x1 x2 with
    | left _ => is_subseq_rec l1' l2'
    | right _ => is_subseq_rec (x1 :: l1') l2'
    end
end.

Lemma is_subseq_rec_lemma1 : forall l1 l2 x,
  is_subseq_rec (x :: l1) l2 = true -> is_subseq_rec l1 l2 = true.
Proof.
  intros l1 l2.
  generalize dependent l1.
  induction l2 as [|x2 l2'].
  - intros.
    cbn in H.
    discriminate.
  - intros.
    assert (is_subseq_rec l1 l2' = true).
    {
      cbn in H.
      destruct (T_eq x x2).
      - assumption.
      - apply IHl2' in H.
        exact H.
    }
    destruct l1 as [|x1 l1'].
    + reflexivity.
    + cbn.
      destruct (T_eq x1 x2).
      * apply IHl2' in H0.
        exact H0.
      * assumption.
Qed.

Lemma is_subseq_rec_lemma2 : forall l1 l2 x,
  is_subseq_rec l1 l2 = true -> is_subseq_rec l1 (x :: l2) = true.
Proof.
  induction l1 as [|x1 l1'].
  - intros.
    cbn.
    reflexivity.
  - intros.
    cbn.
    destruct (T_eq x1 x). 2: assumption.
    destruct l2 as [|x2 l2']. cbn in H. discriminate.
    apply IHl1'.
    cbn in H.
    destruct (T_eq x1 x2).
    * assumption.
    * apply is_subseq_rec_lemma1 in H.
      exact H.
Qed.

Theorem is_subseq_rec_correct l1 l2 :
  is_subseq l1 l2 <-> is_subseq_rec l1 l2 = true.
Proof.
  split; intro.
  induction H.
  cbn.
  reflexivity.
  cbn.
  destruct (T_eq x x).
  assumption.
  intuition.

Qed.
