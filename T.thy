theory T imports Main begin

inductive is_subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
nil_subseq_nil: "is_subseq [] []" |
subseq_take: "is_subseq l1 l2 \<Longrightarrow> is_subseq (x # l1) (x # l2)" |
subseq_skip: "is_subseq l1 l2 \<Longrightarrow> is_subseq l1 (x # l2)"

theorem is_subseq_nil_l: "is_subseq [] l"
  apply (induction l)
   apply (rule nil_subseq_nil)
  apply (rule subseq_skip)
  apply (auto)
  done

theorem not_cons_subseq_nil: "\<not> is_subseq (x # l) []"
proof
  assume "is_subseq (x # l) []"
  thus False
    by cases
qed

theorem tail_of_subseq_is_subseq: "is_subseq (x # l1) l2 \<Longrightarrow> is_subseq l1 l2"
proof (induction rule: is_subseq.induct)
  case nil_subseq_nil
  then show ?case
next
  case (subseq_take l1 l2 x)
  then show ?case sorry
next
  case (subseq_skip l1 l2 x)
  then show ?case sorry
qed

fun is_subseq_rec :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_subseq_rec Nil _ = True" |
"is_subseq_rec (_ # _) Nil = False" |
"is_subseq_rec (x1 # l1) (x2 # l2) =
   (if x1 = x2 then is_subseq_rec l1 l2 else is_subseq_rec l1 (x2 # l2))"

lemma is_subseq_rec_lemma1: "is_subseq_rec (x # l1) l2 \<longrightarrow> is_subseq_rec l1 l2"
proof (induction l2)
  case Nil
  show ?case by simp
next
  case (Cons x2 l2')
  show ?case by simp
qed


thm is_subseq_rec.induct



datatype presence_tag =
OnlyLeft |
OnlyRight |
Both

type_synonym 'a diff = "(presence_tag * 'a) list"

datatype 'a diff = Null_diff | Left 'a "'a diff" | Right 'a "'a diff" | Both 'a "'a diff"

fun get_left :: "'a diff \<Rightarrow> 'a list" where
"get_left Null_diff = []" |
"get_left (Left x d) = x # get_left d" |
"get_left (Right x d) = get_left d" |
"get_left (Both x d) = x # get_left d"



end