use creusot_std::prelude::*;

enum PresenceTag {
    OnlyLeft,
    OnlyRight,
    Both,
}

enum TraceStep {
    GoRight,
    GoUp,
}

type Trace = Vec<TraceStep>;

type Diff<T> = Vec<(PresenceTag, T)>;

fn follow_trace<T: Eq + Clone>(trace: Trace, mut l1: &[T], mut l2: &[T]) -> Option<Diff<T>> {
    let mut diff = Vec::new();

    let mut steps = trace.into_iter();

    loop {
        while let (Some((x1, l01)), Some((x2, l02))) = (l1.split_first(), l2.split_first()) {
            if x1 == x2 {
                l1 = l01;
                l2 = l02;
                diff.push((PresenceTag::Both, x1.clone()))
            } else {
                break;
            }
        }

        match steps.next() {
            Some(TraceStep::GoRight) => {
                if let Some((x1, l01)) = l1.split_first() {
                    l1 = l01;
                    diff.push((PresenceTag::OnlyLeft, x1.clone()));
                } else {
                    return None;
                }
            }
            Some(TraceStep::GoUp) => {
                if let Some((x2, l02)) = l2.split_first() {
                    l2 = l02;
                    diff.push((PresenceTag::OnlyRight, x2.clone()));
                } else {
                    return None;
                }
            }
            None => break,
        }
    }

    Some(diff)
}

#[logic]
fn is_compatible<T: Eq>(trace: Seq<TraceStep>, mut l1: Seq<T>, mut l2: Seq<T>) -> bool {
    let mut steps = trace.into_iter();

    loop
}
