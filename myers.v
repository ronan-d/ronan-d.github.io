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
  induction l1 as [|x1 l1'].
  - intros.
    destruct l2; reflexivity.
  - induction l2 as [|x2 l2'].
    + intros.
      cbn in H.
      discriminate.
    + intros.
      cbn in H.
      destruct (T_eq x x2).
      * cbn.
        destruct (T_eq x1 x2).
        -- subst x1.
           subst x2.
           apply IHl1' in H.
           assumption.
        -- assumption.
      * cbn.
        destruct (T_eq x1 x2).
        -- apply IHl1' with (x := x1).
           apply IHl2' with (x := x).
           assumption.
        -- apply IHl2' in H.
           assumption.
Qed.

Lemma is_subseq_rec_lemma2 l1 x2 l2' :
  is_subseq_rec l1 l2' = true -> is_subseq_rec l1 (x2 :: l2') = true.
Proof.
  generalize dependent x.
  generalize dependent l2.
  induction l1 as [|x1 l1']; intros.
  - cbn.
    reflexivity.
  - cbn.
    destruct (T_eq x1 x).
    2: assumption.
    induction l2 as [|x2 l2'].
    cbn in H.
    discriminate.
    cbn in H.
    destruct (T_eq x1 x2).
    apply IHl1'.
    assumption.
    apply IHl1'.
    apply IHl2'.
    assumption.
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
