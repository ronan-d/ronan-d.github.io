theory T imports Main begin

typedecl label

fun my_plus :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
"my_plus 0 n = n" |
"my_plus (Suc m) n = Suc (my_plus m n)"

lemma my_plus_n_zero: "my_plus n 0 = n"
  apply(induction n)
  apply(auto)
  done

inductive is_subseq :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
nil_subseq_nil: "is_subseq [] []" |
subseq_take: "is_subseq l1 l2 \<Longrightarrow> is_subseq (Cons x l1) (Cons x l2)" |
subseq_skip: "is_subseq l1 l2 \<Longrightarrow> is_subseq l1 (Cons x l2)"

theorem is_subseq_nil_l: "is_subseq Nil l"
  apply (induction l)
   apply (rule nil_subseq_nil)
  apply (rule subseq_skip)
  apply (auto)
  done

fun is_subseq_rec :: "'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"is_subseq_rec Nil _ = True" |
"is_subseq_rec (_ # _) Nil = False" |
"is_subseq_rec (x1 # l1) (x2 # l2) = (if x1 = x2 then is_subseq_rec l1 l2 else is_subseq_rec l1 (x2 # l2))"

theorem cons_not_subseq_nil: "\<not> is_subseq (x # l) Nil"
  apply (auto elim: is_subseq.cases)
  done

thm is_subseq_rec.induct

definition P1 :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool" where
"P1 x l1 l2 = (is_subseq_rec l1 l2 \<longrightarrow> is_subseq_rec l1 (x # l2))
               \<and> is_subseq_rec (x # l1) l2 \<longrightarrow> is_subseq_rec l1 l2"

lemma is_subseq_rec_lemma1: "P1 x l1 l2"
  apply (induction rule: is_subseq_rec.induct)
    apply (simp_all add: P1_def)
  

theorem is_subseq_rec_correct: "is_subseq l1 l2 = is_subseq_rec l1 l2"
  apply (induction l1)
   apply (simp)
   apply (rule is_subseq_nil_l)
  apply (induction l2)
   apply (simp)
   apply (rule cons_not_subseq_nil)
  apply (simp)
  apply (rule conjI)

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