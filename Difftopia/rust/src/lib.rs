use creusot_std::prelude::*;

#[logic]
#[variant(l2.len())]
fn is_subseq<T>(l1: Seq<T>, l2: Seq<T>) -> bool {
    match l1.get(0) {
        None => true,
        Some(x1) => match l2.get(0) {
            None => false,
            Some(x2) => {
                if pearlite! {x1 == x2} {
                    is_subseq(l1.tail(), l2.tail())
                } else {
                    is_subseq(l1, l2.tail())
                }
            }
        },
    }
}

#[logic]
#[requires(is_subseq(Seq::cons(x, l1), l2))]
#[ensures(is_subseq(l1, l2))]
#[variant(l2.len())]
fn tail_of_subseq_is_subseq<T>(x: T, l1: Seq<T>, l2: Seq<T>) {
    if 0 < l2.len() {
        if x != l2[0] {
            proof_assert!(is_subseq(Seq::cons(x, l1), l2.tail()));
            tail_of_subseq_is_subseq(x, l1, l2.tail());
        }

        proof_assert!(is_subseq(l1, l2.tail()));

        if 0 < l1.len() {
            if l1[0] == l2[0] {
                tail_of_subseq_is_subseq(l1[0], l1.tail(), l2.tail());
            }
        }
    }
}

// #[logic]
// #[requires(is_subseq(l1, l2))]
// #[ensures(is_subseq(l1, Seq::cons(x, l2)))]
// fn subseq_skip<T>(l1: Seq<T>, x: T, l2: Seq<T>) {
//     if !l1.is_empty_ghost() {
//         subseq_skip(l1.tail(), l2)
//     }
// }
