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
| x1 :: l1, [] => false
| x1 :: l1, x2 :: l2 =>
    match T_eq x1 x2 with
    | left _ => is_subseq_rec l1 l2
    | right _ => is_subseq_rec (x1 :: l1) l2
    end
end.

Fixpoint is_subseq_rec_ind (P : list T -> list T -> Prop) :
  (forall l2, P [] l2) ->
  (forall x1 l1, P (x1 :: l1) []) ->
  (forall x l1 l2, P l1 l2 -> P (x :: l1) (x :: l2)) ->
  (forall x1 x2 l1 l2, x1 <> x2 -> P (x1 :: l1) l2 -> P (x1 :: l1) (x2 :: l2)) ->
  forall l1 l2, P l1 l2 :=
fun H1 H2 H3 H4 l1 l2 => match l1, l2 with
| [], _ => H1 l2
| x1 :: l1', [] => H2 x1 l1'
| x1 :: l1', x2 :: l2' =>
    match T_eq x1 x2 with
    | left Heq => H3 x1 l1' l2' (is_subseq_rec_ind P H1 H2 H3 H4 l1' l2')
    | right Hne => H4 x1 x2 l1' l2' Hne (is_subseq_rec_ind P H1 H2 H3 H4 l1' l2')
    end
end.
    

Lemma is_subseq_rec_lemma1 l1 x l2 :
  is_subseq_rec l1 l2 = true -> is_subseq_rec l1 (x :: l2) = true.
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
