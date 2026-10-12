From Corelib Require Import Nat.
From Stdlib Require Import List. Import ListNotations.

Parameter T: Set.

Parameter T_eq : forall x y : T, {x = y} + {x <> y}.

Inductive is_subseq : list T -> list T -> Prop :=
| nil_subseq_nil : is_subseq [] []
| subseq_take x l1 l2 : is_subseq l1 l2 -> is_subseq (x :: l1) (x :: l2)
| subseq_skip x l1 l2 : is_subseq l1 l2 -> is_subseq l1 (x :: l2).

Theorem nil_subseq_l : forall l, is_subseq [] l.
Proof.
  induction l as [|x l' IH].
  - exact nil_subseq_nil.
  - apply subseq_skip.
    exact IH.
Qed.

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
  - induction H.
    + reflexivity.
    + cbn.
      destruct (T_eq x x); intuition.
    + destruct l1 as [|x1 l1']. reflexivity.
      cbn.
      destruct (T_eq x1 x).
      * apply is_subseq_rec_lemma1 in IHis_subseq.
        assumption.
      * assumption.
  - generalize dependent l1.
    induction l2 as [|x2 l2'].
    + destruct l1.
      * intro. exact nil_subseq_nil.
      * intro. cbn in H.
        discriminate.
    + destruct l1 as [|x1 l1']; intro.
      * apply subseq_skip.
        apply IHl2'.
        destruct l2'; reflexivity.
      * cbn in H.
        destruct (T_eq x1 x2).
        -- subst x2.
           apply subseq_take.
           apply IHl2'.
           assumption.
        -- apply subseq_skip.
           apply IHl2'.
           assumption.
Qed.

Inductive presence_tag :=
| both
| only_left
| only_right.

Definition diff := list (presence_tag * T).

Definition present_in_left (x : presence_tag * T) : bool := match fst x with
| both | only_left => true
| only_right => false
end.

Definition extract_left (d : diff) : list T := map snd (filter present_in_left d).

Definition present_in_right (x : presence_tag * T) : bool := match fst x with
| both | only_right => true
| only_left => false
end.

Definition extract_right (d : diff) : list T := map snd (filter present_in_right d).

Definition present_in_both (x : presence_tag * T) : bool := match fst x with
| both => true
| only_left | only_right => false
end.

Definition extract_common (d : diff) : list T := map snd (filter present_in_both d).

Definition is_common_subseq s l1 l2 := is_subseq s l1 /\ is_subseq s l2.

Theorem extract_common_is_common_subseq : forall d,
  is_common_subseq (extract_common d) (extract_left d) (extract_right d).
Proof.
  induction d as [| x d' IH].
  - cbn.
    split; exact nil_subseq_nil.
  - destruct x as [tag x].
    split.
    + destruct IH as [IH _].
      destruct tag.
      * cbn.
        apply subseq_take.
        exact IH.
      * cbn.
        apply subseq_skip.
        exact IH.
      * cbn.
        exact IH.
    + destruct IH as [_ IH].
      destruct tag.
      * cbn.
        apply subseq_take.
        exact IH.
      * exact IH.
      * cbn.
        apply subseq_skip.
        exact IH.
Qed.

Definition is_pseudo_diff d l1 l2 := extract_left d = l1 /\ extract_right = l2.

Definition is_lcs s l1 l2 :=
  is_common_subseq s l1 l2 /\
  forall s0, is_common_subseq s0 l1 l2 -> length s <= length s0.

Definition longest (l1 l2 : list T) := if length l1 <=? length l2 then l2 else l1.

Inductive pop_pair :
  (list T * list T) -> (list T * list T) -> Prop :=
| pop_right l1 x2 l2' : pop_pair (pair l1 l2') (pair l1 (x2 :: l2'))
| pop_left x1 l1' l2 : pop_pair (pair l1' l2) (pair (x1 :: l1') l2)
| pop_both x1 l1' x2 l2' : pop_pair (pair l1' l2') (pair (x1 :: l1') (x2 :: l2')).

Theorem pop_pair_acc : forall p, Acc pop_pair p.
Proof.
  intros [l1 l2].
  apply Acc_intro.
  generalize dependent l2.
  induction l1 as [|x1 l1' IH1].
  - induction l2 as [|x2 l2' IH2].
    + intros.
      inversion H.
    + intros.
      inversion H.
      subst.
      apply Acc_intro.
      intros.
      apply IH2.
      assumption.
  - induction l2 as [|x2 l2' IH2].
    + intros.
      inversion H.
      subst.
      apply Acc_intro.
      intros.
      apply IH1 in H0.
      exact H0.
    + intros.
      inversion H; subst.
      * apply Acc_intro.
        intros.
        apply IH2.
        exact H0.
      * apply Acc_intro.
        intros.
        apply IH1 in H0.
        exact H0.
      * apply Acc_intro.
        intros.
        apply IH1 in H0.
        exact H0.
Qed.

Fixpoint lcs_rec (l1 l2 : list T) (ACC : Acc pop_pair (pair l1 l2)) : list T :=
match l1, l2 with
| [], _ | _, [] => []
| x1 :: l1', x2 :: l2' =>
    if T_eq x1 x2 then
      lcs_rec l1' l2' (Acc_inv ACC (pop_both x1 l1' x2 l2'))
    else
      []
end.

Theorem lcs_rec_is_common_subseq : forall l1 l2, is_common_subseq (lcs_rec l1 l2) l1 l2.
Proof.
  induction l1 as [|x1 l1' IH1].
  - intros.
    split; cbn; apply nil_subseq_l.
  - induction l2 as [|x2 l2' IH2].
    + cbn.
      split; apply nil_subseq_l.
    + cbn.
      destruct (T_eq x1 x2).
      * subst x2.
        split; apply subseq_take; apply IH1.
      * 
Qed.

Theorem lcs_rec_is_lcs : forall l1 l2, is_lcs (lcs_rec l1 l2) l1 l2.
Proof.
  induction l1 as [|x1 l1' IH1].
  - cbn.
    intros.
    split.
    + split.
      * exact nil_subseq_nil.
      * apply nil_subseq_l.
    + intros.
      cbn.
      apply le_0_n.
  - induction l2 as [|x2 l2' IH2].
    + cbn.
      split.
      * split; apply nil_subseq_l.
      * intros.
        apply le_0_n.
    + split.

Qed.
