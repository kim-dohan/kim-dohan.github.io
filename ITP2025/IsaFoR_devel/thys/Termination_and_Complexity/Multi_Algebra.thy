(*
Author:  Akihisa Yamada (2017-2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Multi_Algebra
  imports 
    Ord.Ordered_Algebra
    Auxx.Util
begin


subsection \<open>Multi-Encoding\<close>

text \<open>
  Here we consider algebras where the carrier is vectors -- more generally mappings from
  natural numbers.
\<close>

locale pre_multi_encoding =
  fixes E :: "'f \<Rightarrow> nat \<comment> \<open>arity\<close> \<Rightarrow> nat \<comment> \<open>index\<close> \<Rightarrow> ('g, nat\<times>nat) term"
begin

definition I where "I f ss i \<equiv> (E f (length ss) i) \<cdot> (\<lambda>(i,j). (ss ! i) j)"

sublocale algebra I.

end

locale pre_multi_encoded_algebra = target: algebra I + encoder: pre_multi_encoding E
  for I :: "'g \<Rightarrow> 'a list \<Rightarrow> 'a"
  and E :: "'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('g, nat\<times>nat) term"
begin

definition encode :: "('f,'v) term \<Rightarrow> nat \<Rightarrow> ('g,'v\<times>nat) term"
  where "encode s \<equiv> encoder.eval s (curry Var)"

definition IE :: "'f \<Rightarrow> (nat \<Rightarrow> 'a) list \<Rightarrow> nat \<Rightarrow> 'a"
  where "IE f vs k \<equiv> target.eval (E f (length vs) k) (\<lambda>(i,j). (vs ! i) j)"

sublocale algebra IE.

end

locale multi_encoding = pre_multi_encoding +
  fixes d :: nat
  assumes var_domain_1: "(i,j) \<in> vars_term (E f n k) \<Longrightarrow> i < n"
  assumes var_domain_2: "(i,j) \<in> vars_term (E f n k) \<Longrightarrow> j < d"
begin

lemmas var_domain = var_domain_1 var_domain_2

lemma var_domainE[elim]:
  assumes 1: "ij \<in> vars_term (E f n k)"
    and 2: "fst ij < n \<Longrightarrow> snd ij < d \<Longrightarrow> thesis"
  shows thesis
  by (cases ij, insert 1, auto dest: var_domain intro!: 2)

end

locale multi_encoded_algebra = pre_multi_encoded_algebra + encoder: multi_encoding
begin

text \<open>The following notion is for argument filtering technique.\<close>
lemma constant_at_via_encoding:
  assumes "\<And>j k. j < d \<Longrightarrow> target.constant_term_on (E f n k) (i,j)"
  shows "constant_at f n i"
proof (intro constant_atI)
  fix as :: "(nat \<Rightarrow> 'b) list" and b
  assume 1: "i < n" and 2: "length as = n"
  then have 3: "(\<lambda>(i',j). ((as [i := b]) ! i') j) = (\<lambda>(i',j). if i = i' then b j else (as ! i') j)"
    by auto
  show "IE f (as[i:=b]) = IE f as"
  proof (intro ext)
    fix k
    from assms have 5: "j < d \<Longrightarrow> target.constant_term_on (E f n k) (i,j)" for j by auto
    have "target.eval (E f n k) ((\<lambda>(i', j). (as[i:=b] ! i') j)) =
          target.eval (E f n k) (\<lambda>(i',j). if i = i' \<and> j < d then b j else (as ! i') j)"
      (is "_ = target.eval ?t (?f d)")
      by (auto simp: 3 intro!: target.eval_same_vars)
    also have "\<dots> = target.eval (E f n k) (\<lambda>(i, j). (as ! i) j)"
    proof (insert 5, induct d)
      case (Suc d)
      have "target.eval ?t (?f (Suc d)) = target.eval ?t ((?f d) ((i, d) := b d))"
        by auto
      also have "\<dots> = target.eval ?t (?f d)"
        using target.constant_term_onD[OF Suc(2), of "d" "?f d" "b d"]
        by auto
      also have "\<dots> = target.eval ?t (\<lambda>(i, j). (as ! i) j)"
        using Suc by auto
      finally show ?case.
    qed simp
    finally show "IE f (as[i := b]) k = IE f as k"
      by (auto simp: IE_def 2)
  qed
qed

definition "constant_positions f n \<equiv> [i \<leftarrow> [0..<n]. \<forall>k. \<forall>(i',j) \<in> vars_term (E f n k). i' \<noteq> i]"

lemma set_constant_positions:
  "set (constant_positions f n) = {i. i < n \<and> (\<forall>k j. (i,j) \<notin> vars_term (E f n k))}"
  by (auto simp: constant_positions_def elim!: encoder.var_domain)

lemma constant_positionsE:
  assumes "i \<in> set (constant_positions f n)"
    and "i < n \<Longrightarrow> (\<And>k j. (i,j) \<notin> vars_term (E f n k)) \<Longrightarrow> thesis"
  shows thesis
  using assms set_constant_positions by auto

lemma constant_positions: "i \<in> set (constant_positions f n) \<Longrightarrow> constant_at f n i"
  apply (rule constant_at_via_encoding)
  apply (rule target.constant_term_on_extra_var)
  by (auto simp: constant_positions_def image_def elim!: constant_positionsE)

sublocale algebra_hom "(\<lambda>t k. target.eval (t k) \<alpha>)" "encoder.I" IE
  apply unfold_locales
  apply (unfold IE_def encoder.I_def)
  by (auto simp: target.eval_hom.hom_eval intro!: target.eval_same_vars elim!: encoder.var_domainE)

text \<open>
  The following lemma should be used to derive code equations for @{term "\<lbrakk>x\<rbrakk>"}.
\<close>
lemma eval_via_encoding: "\<lbrakk>s\<rbrakk> \<alpha> i = target.eval (encode s i) (case_prod \<alpha>)"
proof (induct s arbitrary: i)
  case (Var x)
  then show ?case by (auto simp: encode_def)
next
  define e where "\<And>s i. e s i \<equiv> target.eval (encode s i) (case_prod \<alpha>)"
  case (Fun f ss)
  then have IH: "map (\<lambda>s. \<lbrakk>s\<rbrakk> \<alpha>) ss = map e ss" by (auto simp: e_def)
  have "\<lbrakk>Fun f ss\<rbrakk> \<alpha> i = IE f (map e ss) i"
    by (unfold IE_def algebra.eval.simps, fold IE_def, unfold IH, auto)
  also have "\<dots> = e (Fun f ss) i"
    apply (unfold e_def encode_def encoder.eval.simps, fold encode_def, fold e_def)
    apply (subst cong[OF hom])
    by (auto simp: o_def e_def[symmetric])
  finally show ?case by (simp add: e_def)
qed

end

context ord_syntax begin

definition less_eq_fun (infix "\<sqsubseteq>\<^sub>f" 50) where "f \<sqsubseteq>\<^sub>f g \<equiv> \<forall>i. f i \<sqsubseteq> g i"

lemma less_eq_funI[intro!]: assumes "\<And>i. f i \<sqsubseteq> g i" shows "f \<sqsubseteq>\<^sub>f g"
  using assms by (auto simp: less_eq_fun_def)

lemma less_eq_funE: assumes "f \<sqsubseteq>\<^sub>f g" and "(\<And>i. f i \<sqsubseteq> g i) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: less_eq_fun_def)

lemma less_eq_funD: assumes "f \<sqsubseteq>\<^sub>f g" shows "f i \<sqsubseteq> g i"
  using assms by (auto simp: less_eq_fun_def)

end


locale pre_multi_encoded_ord_algebra =
  target: ord less_eq less + pre_multi_encoded_algebra I E
  for less_eq less :: "'a \<Rightarrow> 'a \<Rightarrow> bool"
  and I :: "'g \<Rightarrow> 'a list \<Rightarrow> 'a"
  and E :: "'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('g, nat\<times>nat) term"
begin

sublocale target: ord_algebra.

interpretation target: ord_syntax.

abbreviation less_vec where "less_vec f g \<equiv> f 0 \<sqsubset> g 0 \<and> f \<sqsubseteq>\<^sub>f g"

sublocale ord "(\<sqsubseteq>\<^sub>f)" less_vec.

sublocale ord_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec.

end

locale multi_encoded_ordered_algebra =
  target: quasi_order + pre_multi_encoded_ord_algebra + multi_encoded_algebra
begin

sublocale target: ord_syntax.
sublocale target: ordered_algebra..

sublocale ordered_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec
  apply (unfold_locales, unfold target.less_eq_fun_def)
      apply force
     apply (auto dest: target.order_trans)[1]
    apply (auto dest: target.le_less_trans)[1]
    apply (auto dest: target.order_trans)[1]
   apply (intro conjI)
    apply (auto dest: target.less_le_trans)[1]
   apply (auto dest: target.order_trans)[1]
  apply auto
  done

end

locale multi_encoded_wf_algebra = target: wf_order + multi_encoded_ordered_algebra
begin

sublocale target: wf_algebra by (unfold_locales, fact target.less_induct)

sublocale wf_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec
proof unfold_locales
  fix P a
  assume 1: "(\<And>x. (\<And>y. less_vec y x \<Longrightarrow> P y) \<Longrightarrow> P x)"
  show "P a"
    by (induct "a 0" arbitrary: a rule: target.less_induct, auto intro:1)
qed

end

text \<open>Multi-interpretation is always weakly monotone, if the base algebra is weakly monotone.\<close>

locale multi_encoded_weak_mono_algebra = multi_encoded_ordered_algebra +
  target: weak_mono_algebra
begin

sublocale weak_mono_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec
  by (unfold_locales, auto simp: IE_def nth_append_Cons target.less_eq_funD intro!: target.eval_le_eval)

end

text \<open>The strict monotonicity of a multi-interpretation is ensured by that of the first
 coordinate.\<close>

locale multi_encoded_mono_algebra = multi_encoded_ordered_algebra +
  target: weak_mono_algebra +
  assumes str_mono_0:
    "i < n \<Longrightarrow> less (\<alpha>(i,0)) b \<Longrightarrow> less (target.eval (E f n 0) \<alpha>) (target.eval (E f n 0)(\<alpha>((i,0):=b)))"
begin

sublocale multi_encoded_weak_mono_algebra..

sublocale mono_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec
proof (unfold_locales, intro conjI)
  fix f :: 'c and ls rs :: "(nat \<Rightarrow> 'a) list" and a b :: "nat \<Rightarrow> 'a"
  define n where [simp]: "n \<equiv> Suc (length ls + length rs)"
  let ?C = "\<lambda>c. IE f (ls @ c # rs)"
  define \<alpha> where [simp]: "\<alpha> \<equiv> \<lambda>(i, j). ((ls @ a # rs) ! i) j"
  assume ab: "less_vec a b"
  then have "a \<sqsubseteq>\<^sub>f b" by auto
  then show "?C a \<sqsubseteq>\<^sub>f ?C b" by (rule append_Cons_le_append_Cons)
  have 1: "length ls < n" by simp
  have "target.eval (E f n 0) \<alpha> \<sqsubset> target.eval (E f n 0) (\<alpha>((length ls, 0) := b 0))"
    using str_mono_0[OF 1, of "\<alpha>" "b 0" f] ab
    by auto
  also have "\<alpha>((length ls, 0) := b 0) = (\<lambda>(i,j). ((ls @ a (0 := b 0) # rs) ! i) j)"
    (is "?l = ?m")
  proof (intro ext)
    fix ij show "?l ij = ?m ij"
      by (cases "fst ij" "length ls" rule:linorder_cases, auto simp: nth_append split:prod.split)
  qed
  also have "target.eval (E f n 0) \<dots> \<sqsubseteq> target.eval (E f n 0) (\<lambda>(i,j). ((ls @ b # rs) ! i) j)"
  proof (intro target.eval_le_eval, safe, goal_cases)
    case (1 i j)
    with ab show ?case
      by (cases i "length ls" rule: linorder_cases, auto simp: nth_append target.less_eq_funD)
  qed
  finally show "?C a 0 \<sqsubset> ?C b 0" by (auto simp: IE_def)
qed

end

text \<open>Well-foundedness is trivial.\<close>

locale multi_encoded_wf_weak_mono_algebra =
  multi_encoded_weak_mono_algebra + target: wf_order
begin

sublocale multi_encoded_wf_algebra..

sublocale wf_weak_mono_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec..

end

locale multi_encoded_wf_mono_algebra =
  multi_encoded_mono_algebra + target: wf_order
begin

sublocale multi_encoded_wf_weak_mono_algebra..

sublocale wf_mono_algebra where I = IE and less_eq = "(\<sqsubseteq>\<^sub>f)" and less = less_vec..

end

end
