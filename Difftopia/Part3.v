From Corelib Require Import Nat.
From Stdlib Require Import List Lia. Import ListNotations.
From Equations Require Import Equations.

From Difftopia Require Import Part1.

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
    lcs_rec l1' l2'
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
Proof.
  
Qed.
