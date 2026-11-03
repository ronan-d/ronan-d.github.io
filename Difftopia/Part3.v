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
