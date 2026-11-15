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
