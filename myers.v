From Corelib Require Import Nat.
From Stdlib Require Import List. Import ListNotations.
From Stdlib Require Import ZArith.

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

Theorem tail_of_subseq_is_subseq : forall x l1 l2,
  is_subseq (x :: l1) l2 -> is_subseq l1 l2.
Proof.
  intros.
  generalize dependent l1.
  generalize dependent x.
  induction l2 as [|x2 l2' IH2].
  {
    intros.
    inversion H.
  }
  intros.
  inversion H; clear H; subst.
  - apply subseq_skip.
    assumption.
  - apply subseq_skip.
    apply IH2 in H2.
    exact H2.
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

Parameter (l1 l2 : list T).

Inductive presence_tag :=
| both
| only_left
| only_right.

Definition diff := list presence_tag.

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

Definition is_pseudo_diff d l1 l2 : Prop := extract_left d = l1 /\ extract_right d = l2.

Definition is_lcs s l1 l2 :=
  is_common_subseq s l1 l2 /\
  forall s0, is_common_subseq s0 l1 l2 -> length s0 <= length s.

Definition longest (l1 l2 : list T) := if length l1 <=? length l2 then l2 else l1.

Fixpoint lcs_rec (l1 l2 : list T) := match l1 with
| [] => []
| x1 :: l1' => (fix f l2 := match l2 with
  | [] => []
  | x2 :: l2' =>
      if T_eq x1 x2 then
        x1 :: (lcs_rec l1' l2')
      else
        longest (lcs_rec l1' l2) (f l2')
  end) l2
end.

Lemma lcs_rec_nil_l : forall l, lcs_rec [] l = [].
Proof.
  intros.
  reflexivity.  
Qed.

Lemma lcs_rec_l_nil : forall l, lcs_rec l [] = [].
Proof.
  intros.
  destruct l; reflexivity.
Qed.

Lemma lcs_rec_cons_cons : forall x1 l1' x2 l2',  lcs_rec (x1 :: l1') (x2 :: l2') =
  if T_eq x1 x2 then
    x1 :: (lcs_rec l1' l2')
  else
    longest (lcs_rec l1' (x2 :: l2')) (lcs_rec (x1 :: l1') l2').
Proof.
  intros.
  reflexivity.
Qed.

Opaque lcs_rec.

Theorem lcs_rec_is_common_subseq : forall l1 l2, is_common_subseq (lcs_rec l1 l2) l1 l2.
Proof.
  induction l1 as [|x1 l1' IH1].
  - intros.
    split.
    + rewrite lcs_rec_nil_l.
      exact nil_subseq_nil.
    + rewrite lcs_rec_nil_l.
      apply nil_subseq_l.
  - induction l2 as [|x2 l2' IH2].
    + split; rewrite lcs_rec_l_nil; apply nil_subseq_l.
    + split.
      * rewrite lcs_rec_cons_cons.
        destruct (T_eq x1 x2).
        -- apply subseq_take.
           apply IH1.
        -- unfold longest.
           destruct (length (lcs_rec l1' (x2 :: l2')) <=? length (lcs_rec (x1 :: l1') l2')).
           ++ apply IH2.
           ++ apply subseq_skip.
              apply IH1.
      * rewrite lcs_rec_cons_cons.
        destruct (T_eq x1 x2).
        -- subst x2.
           apply subseq_take.
           apply IH1.
        -- unfold longest.
           destruct (length (lcs_rec l1' (x2 :: l2')) <=? length (lcs_rec (x1 :: l1') l2')).
           ++ apply subseq_skip.
              apply IH2.
           ++ apply IH1.
Qed.

Theorem lcs_rec_is_longest : forall l1 l2, forall s0,
  is_common_subseq s0 l1 l2 -> length s0 <= length (lcs_rec l1 l2).
Proof.
  induction l1 as [|x1 l1' IH1].
  {
    intros.
    rewrite lcs_rec_nil_l.
    destruct H as [H _].
    inversion H.
    apply le_n.
  }
  induction l2 as [|x2 l2' IH2].
  {
    intros.
    rewrite lcs_rec_l_nil.
    destruct H as [_ H].
    inversion H.
    apply le_n.
  }
  intros.
  rewrite lcs_rec_cons_cons.
  destruct (T_eq x1 x2).
  - cbn.
    subst x2.
    destruct H as [Hl Hr].
    inversion Hl; clear Hl; subst; inversion Hr; clear Hr; subst.
    + cbn.
      apply le_n_S.
      apply IH1.
      split; assumption.
    + cbn.
      apply le_n_S.
      apply tail_of_subseq_is_subseq in H2.
      apply IH1.
      split; assumption.
    + cbn.
      apply le_n_S.
      apply IH1.
      apply tail_of_subseq_is_subseq in H1.
      split; assumption.
    + apply le_S.
      apply IH1.
      split; assumption.
  - unfold longest.
    destruct (PeanoNat.Nat.leb_spec0 
      (length (lcs_rec l1' (x2 :: l2')))
      (length (lcs_rec (x1 :: l1') l2'))).
    + destruct H as [Hl Hr].
      inversion Hl; subst; clear Hl; inversion Hr; clear Hr; subst.
      * exfalso. intuition.
      * apply IH2.
        split.
        -- apply subseq_take.
           assumption.
        -- assumption.
      * eapply PeanoNat.Nat.le_trans.
        2: exact l.
        apply IH1.
        split. assumption.
        apply subseq_take.
        assumption.
      * apply IH2.
        split.
        -- apply subseq_skip.
           assumption.
        -- assumption.
    + destruct H as [Hl Hr].
      apply PeanoNat.Nat.lt_nge in n0.
      inversion Hl; subst; clear Hl; inversion Hr; clear Hr; subst.
      * exfalso. intuition.
      * apply PeanoNat.Nat.lt_le_incl in n0.
        eapply PeanoNat.Nat.le_trans.
        2: exact n0.
        apply IH2.
        split.
        -- apply subseq_take.
           assumption.
        -- assumption.
      * apply IH1.
        split. assumption.
        apply subseq_take.
        assumption.
      * apply IH1.
        split. assumption.
        apply subseq_skip.
        assumption.
Qed.

Fixpoint lcs_rec_with_counter (l1 l2 : list T) : (list T) * nat :=
match l1 with
| [] => pair [] 1
| x1 :: l1' => (fix f l2 := match l2 with
  | [] => pair [] 1
  | x2 :: l2' => if (T_eq x1 x2) then
      let (c, n) := lcs_rec_with_counter l1' l2' in
      pair (x1 :: c) (n + 1)
    else
      let (c1, n1) := lcs_rec_with_counter l1' l2 in
      let (c2, n2) := f l2' in
      pair (longest c1 c2) (n1 + n2 + 1)
  end) l2
end.

Fixpoint diff_rec (l1 l2 : list T) : diff :=
match l1 with
| [] => List.map (fun x => pair only_right x) l2
| x1 :: l1' => (fix f l2 := match l2 with
  | [] => List.map (fun x => pair only_left x) l1
  | x2 :: l2' => if (T_eq x1 x2) then
      pair both x1 :: diff_rec l1' l2'
    else
      let d1 := diff_rec l1' l2 in
      let d2 := f l2' in
      if length (extract_common d1) <=? length (extract_common d2) then
        pair only_right x2 :: d2
      else
        pair only_left x1 :: d1
  end) l2
end.

Lemma diff_rec_nil_l : forall l,
  diff_rec [] l = List.map (fun x => pair only_right x) l.
Proof.
  reflexivity.
Qed.

Lemma diff_rec_l_nil : forall l,
  diff_rec l [] = List.map (fun x => pair only_left x) l.
Proof.
  destruct l; reflexivity.
Qed.

Lemma diff_rec_cons_cons : forall x1 l1' x2 l2',
  diff_rec (x1 :: l1') (x2 :: l2') =
    if (T_eq x1 x2) then
        pair both x1 :: diff_rec l1' l2'
      else
        let d1 := diff_rec l1' (x2 :: l2') in
        let d2 := diff_rec (x1 :: l1') l2' in
        if length (extract_common d1) <=? length (extract_common d2) then
          pair only_right x2 :: d2
        else
          pair only_left x1 :: d1.
Proof.
  reflexivity.
Qed.

Opaque diff_rec.

Theorem diff_rec_is_pseudo_diff : forall l1 l2,
  is_pseudo_diff (diff_rec l1 l2) l1 l2.
Proof.
  induction l1 as [|x1 l1' IH1].
  {
    intros.
    rewrite diff_rec_nil_l.
    induction l2 as [|x2 l2' IH2].
    - cbn.
      split; reflexivity.
    - cbn.
      split.
      + cbn.
        destruct IH2 as [IH2 _].
        unfold extract_left in IH2.
        assumption.
      + cbn.
        destruct IH2 as [_ IH2].
        unfold extract_right in IH2.
        rewrite IH2.
        reflexivity.
  }
  induction l2 as [|x2 l2' IH2].
  {
    rewrite diff_rec_l_nil.
    cbn.
    split.
    - destruct (IH1 []) as [IH _].
      cbn.
      unfold extract_left in IH.
      rewrite diff_rec_l_nil in IH.
      rewrite IH.
      reflexivity.
    - destruct (IH1 []) as [_ IH].
      cbn.
      rewrite diff_rec_l_nil in IH.
      exact IH.
  }
  rewrite diff_rec_cons_cons.
  destruct (T_eq x1 x2).
  - split.
    + cbn.
      destruct (IH1 l2') as [IH _].
      unfold extract_left in IH.
      rewrite IH.
      reflexivity.
    + cbn.
      destruct (IH1 l2') as [_ IH].
      unfold extract_right in IH.
      rewrite IH.
      subst x2.
      reflexivity.
  - cbn.
    destruct (length (extract_common (diff_rec l1' (x2 :: l2'))) <=?
      length (extract_common (diff_rec (x1 :: l1') l2'))).
    + split.
      * destruct IH2 as [IH2 _].
        unfold extract_left in IH2.
        cbn.
        exact IH2.
      * cbn.
        destruct IH2 as [_ IH2].
        unfold extract_right in IH2.
        rewrite IH2.
        reflexivity.
    + split.
      * cbn.
        destruct (IH1 (x2 :: l2')) as [IH _].
        unfold extract_left in IH.
        rewrite IH.
        reflexivity.
      * cbn.
        destruct (IH1 (x2 :: l2')) as [_ IH].
        unfold extract_right in IH.
        exact IH.
Qed.

Record Path := mkPath {
  d : diff;
  l1 : list T;
  l2 : list T;
}.

Definition cost (path : Path) : nat :=
  let costs := map
    (fun x => match fst x with | only_left | only_right => 1 | both => 0 end)
    path.(d)
  in
    list_sum costs.

Definition diagonal (path : Path) : Z :=
  let offsets := map
    (fun x => match fst x with | only_left => 1%Z | only_right => (-1)%Z | both => 0%Z end)
    path.(d)
  in
    fold_left Z.add offsets 0%Z.

Definition distance (path : Path) : nat :=
  length path.(l1) + length path.(l2).

Definition is_path (path : Path) (la lb : list T) : Prop :=
    la = extract_left path.(d) ++ path.(l1) /\
    lb = extract_right path.(d) ++ path.(l2).

Definition is_best_at_cost_on_diag
  (path : Path)
  (la lb : list T)
: Prop
:=
  is_path path la lb /\
  forall (p0 : Path),
    (is_path p0 la lb /\
     cost p0 = cost path /\
     diagonal p0 = diagonal path) ->
    distance path <= distance p0.

Lemma myers_lemma_2 : forall (c : nat) (path : Path) (la lb : list T),
  (is_best_at_cost_on_diag path la lb /\ cost path = S c) ->
  ((exists p, cost p = c /\ ) \/
   todo).
