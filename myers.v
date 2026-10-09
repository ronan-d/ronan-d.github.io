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

Fixpoint find_first x l : option (list T) := match l with
| [] => None
| y :: l' => if T_eq x y then Some l' else find_first x l'
end.

Fixpoint is_subseq_rec2 (l1 l2 : list T) : bool := match l1 with
| [] => true
| x1 :: l1' => match find_first x1 l2 with
    | None => false
    | Some l2' => is_subseq_rec2 l1' l2'
    end
end.

Lemma is_subseq_rec2_lemma1 : forall x1 l1' l2,
  is_subseq_rec2 (x1 :: l1') l2 = true -> is_subseq_rec2 l1' l2 = true.
Proof.
  intros.
  destruct l2 as [|x2 l2'].
  cbn in H.
  discriminate.
  generalize dependent l2'.
  generalize dependent x2.
  induction l1' as [|x1' l1'']; intros.
  reflexivity.
  cbn in H.
  Admitted.

Fixpoint is_subseq_rec (l1 l2 : list T) : bool := match l1, l2 with
| [], _ => true
| x1 :: l1', [] => false
| x1 :: l1', x2 :: l2' =>
    match T_eq x1 x2 with
    | left _ => is_subseq_rec l1' l2'
    | right _ => is_subseq_rec (x1 :: l1') l2'
    end
end.

Fixpoint is_subseq_rec_ind (P : list T -> list T -> Prop) : forall l1 l2,
  (forall l, P [] l) ->
  (forall x l, P (x :: l) []) ->
  (forall x l1 l2, P l1 l2 -> P (x :: l1) (x :: l2)) ->
  (forall x1 l1 x2 l2, x1 <> x2 -> P (x1 :: l1) l2 -> P (x1 :: l1) (x2 :: l2)) ->
  P l1 l2.
intros.
destruct (l1) as [|x1 l1'].
apply H.
destruct l2 as [|x2 l2'].
apply H0.
destruct (T_eq x1 x2).
subst x2.
apply H1.
exact (is_subseq_rec_ind P l1' l2' H H0 H1 H2).
apply H2.
assumption.
exact (is_subseq_rec_ind P (x1 :: l1') l2' H H0 H1 H2).
Defined.

Lemma is_subseq_rec_app : forall x l1 l2,
  is_subseq_rec (x :: l1) l2 = true <->
    exists l3 l4, l2 = l3 ++ [x] ++ l4 /\ is_subseq_rec l1 l4 = true.
Proof.
  split; intros.
  induction l2 as [| x2 l2'].
  cbn in H.
  discriminate.
  cbn in H.
  destruct (T_eq x x2).

Qed.

Lemma is_subseq_rec_lemma1 x1 l1' l2 :
  is_subseq_rec (x1 :: l1') l2 = true -> is_subseq_rec l1' l2 = true.
Proof.
  destruct l2; intros.
  cbn in H.
  discriminate.
Qed.

Lemma is_subseq_rec_lemma2 l1 x2 l2' :
  is_subseq_rec l1 l2' = true -> is_subseq_rec l1 (x2 :: l2') = true.
Proof.
  destruct l1 as [| x1 l1']; intros.
  - reflexivity.
  - generalize dependent x2.
    induction l2' as [|x2' l2''].
    + cbn in H.
      discriminate.
    + intro.
      replace (is_subseq_rec (x1 :: l1') (x2 :: x2' :: l2'')) with match T_eq x1 x2 with
      | left _ => is_subseq_rec l1' (x2' :: l2'')
      | right _ => is_subseq_rec (x1 :: l1') (x2' :: l2'')
    end.
    destruct (T_eq x1 x2).
    * 

    

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
