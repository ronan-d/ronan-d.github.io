From Stdlib Require Import List. Import ListNotations.

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

(** So far, the [diff] type we defined does not say anything about _longest_
    common subsequences. But, as we touched on in part 4, a proper diff of two
    lists [l1] and [l2] has a maximal common part. The following relation captures
    this: *)

Definition is_diff (d : diff) (l1 l2 : list T) : Prop :=
  l1 = extract_first d /\
  l2 = extract_second d /\
  is_lcs (extract_common d) l1 l2.

(** Do you remember the [lcs_rec] procedure from part 3? It is possible
    and relatively simple to extend it into a procedure that returns a diff of
    [l1] and [l2] instead of just an LCS of [l1] and [l2]. *)

(** **** Exercise: 4 stars (exists_diff_rec)

    Taking inspiration from [lcs_rec], write a procedure that returns a diff of
    its arguments. Do not hesitate to write the procedure as a toplevel definition
    above the proof placeholder. *)

(** BEGIN HIDE *)
Equations? diff_rec (l1 l2 : list T)
(** END HIDE *)

Theorem exists_diff_rec : exists (f : list T -> list T -> diff),
  forall l1 l2, is_diff (f l1 l2) l1 l2.
Proof. (** HIDE *)
Qed.
