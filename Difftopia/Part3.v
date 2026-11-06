From Corelib Require Import Nat.
From Stdlib Require Import List Lia. Import ListNotations.
From Equations Require Import Equations.

From Difftopia Require Import Part1.
From Difftopia Require Import Part2.

(** We say that [s] is a common subsequence of [l1] and [l2] if [s] is both a
    subsequence of [l1] and a subsequence of [l1]: *)

Definition is_common_subseq s l1 l2 := is_subseq s l1 /\ is_subseq s l2.

(** We say that [s] is a longest common subsequence (LCS) of [l1] and [l2] is [s] is
    a common subsequence of [l1] and [l2] and s is as least as long as any other
    common subsequence of [l1] and [l2]: *)

Definition is_lcs s l1 l2 :=
  is_common_subseq s l1 l2 /\
  (forall s0, is_common_subseq s0 l1 l2 -> length s0 <= length s).

(** When equality over [T] is decidable, there exists an effective procedure to
    construct a longest common subsequence of any pair of lists [(l1, l2)]: *)

Parameter T_eq : forall (x y : T), {x = y} + {x <> y}.

Equations? lcs_rec (l1 l2 : list T) : list T by wf (length l1 + length l2) lt :=
lcs_rec [] _ := [];
lcs_rec _ [] := [];
lcs_rec (x1 :: l1') (x2 :: l2') :=
  if (T_eq x1 x2) then
    x1 :: lcs_rec l1' l2'
  else
    let c1 := lcs_rec l1' (x2 :: l2') in
    let c2 := lcs_rec (x1 :: l1') l2' in
    if length c1 <=? length c2 then
      c2
    else
      c1.
Proof.
  all: lia.
Qed.

Theorem lcs_rec_is_lcs : forall l1 l2, is_lcs (lcs_rec l1 l2) l1 l2.
Proof. (** HIDE *)
  intros.
  funelim (lcs_rec l1 l2).
  {
    split.
    - split; apply nil_is_subseq_l.
    - intros.
      cbn.
      destruct H as [H _].
      inversion H; subst.
      reflexivity.
  }
  {
    split.
    - split; apply nil_is_subseq_l.
    - intros.
      destruct H as [_ H].
      inversion H; subst.
      apply le_n.
  }
  destruct (T_eq x1 x2).
  - specialize (H e).
    subst x2.
    destruct H as [[Hl1 Hl2] Hl].
    split. split.
    + apply subseq_take.
      assumption.
    + apply subseq_take.
      assumption.
    + intros.
      destruct H as [H01 H02].
      inversion H01; inversion H02; subst; clear H01; clear H02; cbn.
      1-3: apply le_n_S.
      4: apply le_S.
      all: apply Hl.
      1: inversion H6; subst.      
      all: split.
      all: try assumption.
      all: apply tail_of_subseq_is_subseq with (x := x1); assumption.
  - specialize (H0 n).
    specialize (H1 n).
    destruct H0 as [[H01 H02] H0l].
    destruct H1 as [[H11 H12] H1l].
    repeat split.
    all: cycle 2.
    intros s0 [Hs1 Hs2].
    inversion Hs1; subst; clear Hs1.
    all: cycle 1.
    eapply PeanoNat.Nat.le_trans. apply H0l.
    all: cycle 4.
    inversion Hs2; subst; clear Hs2.
    1: exfalso. apply n. reflexivity.
    eapply PeanoNat.Nat.le_trans. apply H1l.
    all: destruct
      (length (lcs_rec l1' (x2 :: l2')) <=? length (lcs_rec (x1 :: l1') l2'))
      eqn:Heq.
    all: try apply PeanoNat.Nat.leb_le in Heq.
    all: try apply PeanoNat.Nat.leb_gt in Heq.
    all: try split.
    all: try assumption.
    all: try apply subseq_take; try assumption.
    all: try apply le_n.
    all: try apply subseq_skip.
    all: try assumption.
    lia.
Qed.
