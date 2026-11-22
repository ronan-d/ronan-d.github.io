From Corelib Require Import Nat.

From Stdlib Require Import List Lia. Import ListNotations.

From Equations Require Import Equations.

From Difftopia Require Import Part1.
From Difftopia Require Import Part3.

(** Do you remember the diff of the poems in part 4? It had three kinds of lines:

    - Gray lines that were present in both poems.
    - Red lines that were present only in the first poemK
    - Green lines that were present only in the second poem.

    Let's define a type to reflect that categorization: *)

Inductive tag : Set :=
| both
| only_first
| only_second.

(** We're going to use this type to define a type for diffs. We'll define diffs
    as lists whose elements are pairs composed of a tag and a value of type [T]: *)

Definition diff := list (tag * T).

(** From a diff [d], we can reconstruct the first of the two sequences [d] was
    generated from: *)

Definition extract_first (d : diff) : list T :=
  map snd (filter (fun x => match x with
  | (both, _) | (only_first, _) => true
  | (only_second, _) => false
  end) d).

(** We're using a couple of things from Rocq's standard library here, like [map]
    and [filter]. They are similar to their homonyms in OCaml and other programming
    languages but they come with lemmas that you'll have to use to complete the
    exercises.

    We can symetrically reconstruct the second list a diff [d] was generated from: *)

Definition extract_second (d : diff) : list T :=
  map snd (filter (fun x => match x with
  | (both, _) | (only_second, _) => true
  | (only_first, _) => false
  end) d).

(** Last, we can also extract the underlying common subsequence we discussed in
    part 4: *)

Definition extract_common (d : diff) : list T :=
  map snd (filter (fun x => match x with
  | (both, _) => true
  | (only_first, _) | (only_second, _) => false
  end) d).

(** We now have just enough matter for our first warm-up exercise. *)

(** **** Exercise: 1 star (extract_common_is_common_subseq)

    Prove that, for any diff [d], [extract_common d] is a common subsequence of
    [extract_first d] and [extract_second d]: *)

Theorem extract_common_is_common_subseq : forall (d : diff),
  is_common_subseq (extract_common d) (extract_first d) (extract_second d).
Proof. (** HIDE *)
  induction d as [| [t x] d' IH ].
  1: split; cbn; exact nil_subseq_nil.
  destruct IH.
  destruct t;
  split;
  cbn;
  try apply subseq_take;
  try apply subseq_skip;
  assumption.
Qed.

(** We say that a diff [d] expands into two lists [l1] and [l2] if extracting the
    first list of [d] gives [l1] and extracting the second list of [d] gives [l2]: *)

Definition expands_into d l1 l2 :=
  l1 = extract_first d /\ l2 = extract_second d.

(** Note that [expands_into d l1 l2] is not enough to say that [d] is a diff of
    [l1] and [l2]! A crucial ingredient is still missing; we'll add it later. *)

(** **** Exercise: 2 stars (trivial_expands_into)

    [expands_into] is much weaker that the notion of diff and there exist trivial
    procedures that, for any [l1] and [l2], return a diff that expands into [l1] and
    [l2]. Find one such procedure: *)

Theorem trivial_expands_into :
  exists (f : list T -> list T -> diff), forall l1 l2, expands_into (f l1 l2) l1 l2.
Proof. (** HIDE *)
  exists (fun l1 l2 =>
    map (fun x => (only_first, x)) l1 ++ map (fun x => (only_second, x)) l2).
  unfold expands_into.
  intros.
  split;
  unfold extract_first,extract_second;
  rewrite filter_app;
  rewrite map_app;
  rewrite filter_map_swap;
  rewrite filter_map_swap;
  rewrite filter_true;
  rewrite filter_false.
  1: rewrite app_nil_r.
  2: rewrite app_nil_l.
  all: rewrite map_map;
  cbn;
  rewrite map_id;
  reflexivity.
Qed.

(** **** Exercise: 2 stars (length_extract)

    Prove the following equality: *)

Theorem length_extract : forall d,
  length d + length (extract_common d) =
  length (extract_first d) + length (extract_second d).
Proof. (** HIDE *)
  intros.
  induction d as [| [t x] d' IH].
  1: reflexivity.
  unfold extract_first,extract_second,extract_common in *.
  destruct t; cbn; lia.
Qed.

(** Another interesting property: for every common subsequence [s] of two lists [l1]
    and [l2], it is possible to construct a diff that expands into [l1] and [l2] and
    whose common part is [s]. That the subject of the next exercise. *)

(** **** Exercise: 3 stars (exists_diff_of_cs)

    Prove the following theorem: *)

Theorem exists_diff_of_cs : forall s l1 l2,
  is_common_subseq s l1 l2 ->
  exists d, expands_into d l1 l2 /\ extract_common d = s.
Proof. (** HIDE *)
  intros s l1 l2 [H1 H2].
  generalize dependent l2.
  induction H1 as [| x s' l1' H1 IH | x1 s l1' H1 IH]; intros.
  - exists (map (fun x => (only_second, x)) l2).
    split.
    + unfold expands_into,extract_first,extract_second.
      rewrite filter_map_swap.
      rewrite filter_map_swap.
      rewrite filter_true,filter_false.
      rewrite map_map.
      rewrite map_map.
      cbn.
      split. reflexivity.
      symmetry.
      apply map_id.
    + unfold extract_common.
      rewrite filter_map_swap.
      rewrite filter_false.
      reflexivity.
  - remember (x :: s') as s eqn:E.
    induction H2 as [| x0 s2' l2' H2' IH2 | x2 s l2' H2' IH2]. subst.
    + inversion E.
    + inversion E; subst.
      destruct (IH l2') as [d' IH0].
      1: assumption.
      exists ((both, x) :: d').
      unfold expands_into,extract_first,extract_second,extract_common in *.
      split. split.
      all: cbn;
      apply f_equal.
      * exact (proj1 (proj1 IH0)).
      * exact (proj2 (proj1 IH0)).
      * exact (proj2 IH0).
    + destruct (IH2 E) as [d' Hd'].
      exists ((only_second, x2) :: d').
      unfold expands_into,extract_common,extract_first,extract_second.
      split. split.
      * exact (proj1 (proj1 Hd')).
      * cbn.
        apply f_equal.
        exact (proj2 (proj1 Hd')).
      * cbn.
        exact (proj2 Hd').
  - destruct (IH l2) as [d' IHd'].
    1: assumption.
    exists ((only_first, x1) :: d').
    split. split.
    + cbn.
      apply f_equal.
      exact (proj1 (proj1 IHd')).
    + cbn.
      exact (proj2 (proj1 IHd')).
    + cbn.
      exact (proj2 IHd').
Qed.

(** So far, the [diff] type and the [expands_into] relation we defined do not say
    anything about _longest_ common subsequences. But, as we touched on in part 4,
    a proper diff of two lists [l1] and [l2] has a maximal common part. The
    following relation captures this: *)

Definition is_diff (d : diff) (l1 l2 : list T) : Prop :=
  expands_into d l1 l2 /\ is_lcs (extract_common d) l1 l2.

(** Exercise: 2 stars (lcs_shortest_diff)

    Prove that when [expands_into d l1 l2], [extract_common d] is an LCS of [l1]
    and [l2] if and only if [d] is not longer than any diff that expands into [l1]
    and [l2]: *)

Theorem lcs_shortest_diff : forall d l1 l2,
  expands_into d l1 l2 ->
  (is_lcs (extract_common d) l1 l2) <->
  (forall d', expands_into d' l1 l2 -> length d <= length d').
Proof. (** HIDE *)
  intros.
  split; intros.
  - assert (E1 := length_extract d).
    rewrite <- (proj1 H) in E1.
    rewrite <- (proj2 H) in E1.
    assert (E2 := length_extract d').
    rewrite <- (proj1 H1) in E2.
    rewrite <- (proj2 H1) in E2.
    destruct H0 as [_ H0].
    specialize (H0 (extract_common d')).
    assert (is_common_subseq (extract_common d') l1 l2).
    {
      rewrite (proj1 H1).
      rewrite (proj2 H1).
      apply extract_common_is_common_subseq.
    }
    specialize (H0 H2).
    lia.
  - unfold is_lcs.
    split.
    + rewrite (proj1 H),(proj2 H).
      apply extract_common_is_common_subseq.
    + intros.
      
Qed.

(** Do you remember the [lcs_rec] procedure from part 3? It is possible
    and relatively simple to extend it into a procedure that returns a diff of
    [l1] and [l2] instead of just an LCS of [l1] and [l2]. *)

(** **** Exercise: 4 stars (exists_diff_rec)

    Taking inspiration from [lcs_rec], write a procedure that returns a diff of
    its arguments. Do not hesitate to write the procedure as a toplevel definition
    above the proof placeholder. *)

(** BEGIN HIDE *)
Equations? diff_rec (l1 l2 : list T) : diff by wf (length l1 + length l2) :=
diff_rec [] l2 := map (fun x => (only_second, x)) l2;
diff_rec l1 [] := map (fun x => (only_first, x)) l1;
diff_rec (x1 :: l1') (x2 :: l2') :=
  if (T_eq x1 x2) then
    (both, x1) :: diff_rec l1' l2'
  else
    let c1 := diff_rec l1' (x2 :: l2') in
    let c2 := diff_rec (x1 :: l1') l2' in
    if length c1 <=? length c2 then
      (only_second, x2) :: c1
    else
      (only_first, x1) :: c2.
Proof.
  all: lia.
Qed.
(** END HIDE *)

Theorem exists_diff_rec : exists (f : list T -> list T -> diff),
  forall l1 l2, is_diff (f l1 l2) l1 l2.
Proof. (** HIDE *)
  exists diff_rec.
  intros.
  split. 2: split.
  1,2: shelve.
  assert (extract_common (diff_rec l1 l2) = lcs_rec l1 l2).
  {
    funelim (diff_rec l1 l2).
    1,2: autorewrite with lcs_rec;
      unfold extract_common;
      rewrite filter_map_swap;
      rewrite filter_false;
      reflexivity.
    autorewrite with lcs_rec.
    destruct (T_eq x1 x2).
    + cbn.
      apply f_equal.
      exact (H e).
    + cbn.
      specialize (H0 n).
      specialize (H1 n).
      assert (
        L1 : forall d l1 l2, is_diff d l1 l2 ->
        length l1 + length l2 = 2 * length d - length (extract_common d)).
      {
        induction d as [| [t x] d' IH ].
        {
          intros.
          destruct H2 as (H21 & H22 &_).
          inversion H21; inversion H22; subst.
          reflexivity.
        }

      }
      destruct (length (diff_rec l1' (x2 :: l2')) <=? length (diff_rec (x1 :: l1') l2')).

  }
Qed.
