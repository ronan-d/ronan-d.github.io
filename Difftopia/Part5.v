From Stdlib Require Import List. Import ListNotations.

From Difftopia Require Import Part1.

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

    We can symetrically extract the second list a diff [d] was generated from: *)

Definition extract_second (d : diff) : list T :=
  map snd (filter (fun x => match x with
  | (both, _) | (only_second, _) => true
  | (only_first, _) => false
  end) d).
