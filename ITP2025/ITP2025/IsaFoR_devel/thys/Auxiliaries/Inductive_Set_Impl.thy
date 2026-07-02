(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Inductive_Set_Impl
imports 
  Util
begin

locale generic_inductive_set =
  fixes R :: "'a set"
  and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and Q :: "'a \<Rightarrow> 'b set"
begin
(* we offer two equivalent induction schemes, try to align your inductive set 
   with the more suitable one *)
inductive the_set1 :: "'b \<Rightarrow> 'a \<Rightarrow>  bool" where
  "a \<in> R \<Longrightarrow> P b a \<Longrightarrow> the_set1 b a"
| "a \<in> R \<Longrightarrow> P b a \<Longrightarrow> b' \<in> Q a \<Longrightarrow> the_set1 b' a' \<Longrightarrow> the_set1 b a'"

inductive the_set :: "'b \<Rightarrow> 'a \<Rightarrow>  bool" where
  non_rec: "a \<in> R \<Longrightarrow> P b a \<Longrightarrow> the_set b a"
| rec_rec: "the_set b a \<Longrightarrow> b' \<in> Q a \<Longrightarrow> the_set b' a' \<Longrightarrow> the_set b a'"

lemma the_set1_rec_rec: "the_set1 b a \<Longrightarrow> b' \<in> Q a \<Longrightarrow> the_set1 b' a' \<Longrightarrow> the_set1 b a'"
  by (induct arbitrary: b' a' rule: the_set1.induct, auto intro: the_set1.intros)

lemma the_set1_the_set: "the_set1 = the_set"
proof (intro ext)
  fix b a
  show "the_set1 b a = the_set b a" (is "?l = ?r")
  proof
    assume ?l
    then show ?r
      by (induct rule: the_set1.induct, auto intro: the_set.intros)
  next
    assume ?r
    then show ?l
      by (induct rule: the_set.induct, auto intro: the_set1.intros(1) the_set1_rec_rec)
  qed
qed

lemmas the_set_intros = the_set1.intros[unfolded the_set1_the_set]
lemmas rec = the_set_intros(2)
lemmas the_set_cases[consumes 1, case_names non_rec rec] = the_set1.cases[unfolded the_set1_the_set]
lemmas the_set_induct[consumes 1, case_names non_rec rec] = the_set1.induct[unfolded the_set1_the_set]

end

locale generic_inductive_set_list_impl =   
  fixes R :: "'a list"
    and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
    and Q :: "'a \<Rightarrow> 'b list"
begin
definition "new_as bs as \<equiv> filter (\<lambda> a. \<exists> b \<in> set bs. P b a) as"

function the_set_impl_main :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'b list \<Rightarrow> 'a list" where 
  "the_set_impl_main remain have bs = (let
     new = new_as bs remain
     in (if new = [] then have else the_set_impl_main (list_diff remain new) (new @ have) (remdups (concat (map Q new)))))"
  by pat_completeness auto

termination
proof
  fix r h :: "'a list" and bs new
  assume new: "new = new_as bs r" and e: "new \<noteq> []"
  from new[unfolded new_as_def] have "set new \<subseteq> set r" by auto
  with e have "set (list_diff r new) \<subset> set r" by (cases new, auto)
  then have "card (set (list_diff r new)) < card (set r)"
    by (rule psubset_card_mono[OF finite_set])
  then show "((list_diff r new, new @ h, remdups (concat (map Q new))), r, h, bs) \<in> measure (\<lambda> (r,h,t). card (set r))" by simp
qed simp    

declare the_set_impl_main.simps[simp del]

definition "the_set_impl bs = the_set_impl_main R [] bs"

partial_function (tailrec) the_set_impl_main_lazy :: "('b \<Rightarrow> 'a list) \<Rightarrow> 'a list \<Rightarrow> 'a set \<Rightarrow> 'b list \<Rightarrow> 'a list" where 
  "the_set_impl_main_lazy gen_as have_as have_as' bs = (let
     new_as = [a . b <- bs, a <- gen_as b, a \<notin> have_as']     
     in (if new_as = [] then have_as else the_set_impl_main_lazy gen_as (new_as @ have_as) (set new_as \<union> have_as') (remdups (concat (map Q new_as)))))"

definition "the_set_impl_lazy gen_as bs = the_set_impl_main_lazy gen_as [] {} bs"

lemmas the_set_impl_code = 
  the_set_impl_main.simps 
  the_set_impl_def 
  new_as_def 
  the_set_impl_main_lazy.simps
  the_set_impl_lazy_def
end

declare generic_inductive_set_list_impl.the_set_impl_code[code]

definition "inductive_set_impl = generic_inductive_set_list_impl.the_set_impl"
definition "inductive_set_impl_lazy Q P = generic_inductive_set_list_impl.the_set_impl_lazy P Q"


locale generic_inductive_set_list_impl_sound = generic_inductive_set R P Q + generic_inductive_set_list_impl R' P Q' for
      R :: "'a set"
  and P :: "'b \<Rightarrow> 'a \<Rightarrow> bool"
  and Q :: "'a \<Rightarrow> 'b set"
  and R' :: "'a list"
  and Q' :: "'a \<Rightarrow> 'b list" +
  assumes R[simp]: "set R' = R"
   and Q[simp]: "set (Q' a) = Q a"
begin
lemma the_set_impl_main_sound: assumes "set have \<subseteq> { a . \<exists> b \<in> B. the_set b a}"
  and "set remain \<subseteq> R"
  shows "set (the_set_impl_main remain have bs) \<subseteq> { a. \<exists> b \<in> set bs \<union> B. the_set b a}"
  using assms
proof (induct remain "have" bs arbitrary: B rule: the_set_impl_main.induct)
  case (1 remain "have" bs B)
  let ?new = "new_as bs remain"
  let ?newbs = "remdups (concat (map Q' ?new))"
  have id: "set (the_set_impl_main remain have bs) = set (if ?new = [] then have else the_set_impl_main (list_diff remain ?new) (?new @ have) ?newbs)"
    unfolding the_set_impl_main.simps[of remain] Let_def ..
  show ?case
  proof (cases "?new = []")
    case True
    with 1(2) show ?thesis unfolding id by auto
  next
    case False
    note IH = 1(1)[OF refl False]
    from id False have id: "set (the_set_impl_main remain have bs) = set (the_set_impl_main (list_diff remain ?new) (?new @ have) ?newbs)" by auto
    define B' where "B' = set bs \<union> B"
    let ?B = "{a. \<exists>b\<in>B'. the_set b a}"
    have "set have \<subseteq> ?B" using 1(2) unfolding B'_def by blast
    moreover have "set ?new \<subseteq> ?B"
    proof
      fix a
      assume "a \<in> set ?new"
      from this[unfolded new_as_def] obtain b where a: "a \<in> set remain" and b: "b \<in> set bs" and P: "P b a"
        by auto     
      from a 1(3) have "a \<in> R" by auto
      from non_rec[OF this P] have "the_set b a" .
      with b show "a \<in> ?B" unfolding B'_def by auto
    qed
    ultimately
    have "set (?new @ have) \<subseteq> ?B" by auto
    note IH = IH[folded id, OF this]
    have "set (list_diff remain ?new) \<subseteq> R" using 1(3) by auto
    note IH = IH[OF this]
    show ?thesis
      by (rule order_trans[OF IH], insert \<open>set ?new \<subseteq> ?B\<close>, auto simp: B'_def intro: rec_rec)
  qed
qed

lemma the_set_impl_main_have: 
  "set have \<subseteq> set (the_set_impl_main remain have bs)"
proof (induct remain "have" bs rule: the_set_impl_main.induct)
  case (1 r h ts)
  then show ?case by (simp add: the_set_impl_main.simps[of r] Let_def split: if_splits)
qed


abbreviation reason where "reason S \<equiv> \<lambda> b a n bs as. b = bs 0 \<and> a = as n \<and> (\<forall> i \<le> n. as i \<in> set (new_as [bs i] S)) \<and> (\<forall> i < n. bs (Suc i) \<in> Q (as i))"

lemma the_set_reason: "the_set b a \<Longrightarrow> \<exists> n bs as. reason R' b a n bs as"
proof (induct rule: the_set_induct)
  case (non_rec a b)
  show ?case 
  proof (intro exI)
    show "reason R' b a 0 (\<lambda> _ . b) (\<lambda> _ . a)" using non_rec by (auto simp: new_as_def)
  qed
next
  case (rec a b b' a')
  note new_as_def [simp]
  from rec(5) obtain n bs as where reason: "reason R' b' a' n bs as" by auto
  show ?case
  proof (intro exI)
    show "reason R' b a' (Suc n) (\<lambda> i. if i = 0 then b else bs (i - 1)) (\<lambda> i. if i = 0 then a else as (i - 1))"
      using reason rec(1-3) by (auto, case_tac i, auto)
  qed
qed

lemma the_set_impl_main_complete:  
  "reason remain b a n bs as \<Longrightarrow> b \<in> set bsi \<Longrightarrow> a \<in> set (the_set_impl_main remain have bsi)" 
proof (induct remain "have" bsi arbitrary: b a n bs as rule: the_set_impl_main.induct)
  case (1 remain "have" bsi b a n bs as)  
  let ?new = "new_as bsi remain"
  let ?remain = "list_diff remain ?new"
  let ?have = "?new @ have"
  let ?bsi = "remdups (concat (map Q' ?new))"
  note reason = 1(2)
  from reason have "as 0 \<in> set (new_as [b] remain)" by simp
  also have "set (new_as [b] remain) \<subseteq> set ?new" using 1(3) unfolding new_as_def by auto
  finally have as0: "as 0 \<in> set ?new" .
  then have "?new \<noteq> []" by auto
  note IH = 1(1)[OF refl this]
  have id: "the_set_impl_main remain have bsi = the_set_impl_main ?remain ?have ?bsi"
    unfolding the_set_impl_main.simps[of remain] Let_def using as0 by auto
  note IH = IH[folded id]
  show ?case
  proof (cases "a \<in> set ?new")
    case True
    with id the_set_impl_main_have[of ?have ?remain] show ?thesis by auto
  next
    case False
    with reason as0 have n: "n > 0" by (cases n, auto)
    let ?P = "\<lambda> i. i \<le> n \<and> as i \<in> set ?new"
    let ?Q = "\<lambda> i. as (n - i) \<in> set ?new"
    define k where "k = (LEAST k. ?Q k)"
    define m where "m = n - k"
    from reason False have ln: "\<not> ?P n" by auto
    from reason as0 have "?Q n" by simp
    from LeastI[of ?Q, OF this, folded k_def] have "?Q k" .
    then have m: "?P m" unfolding m_def by auto
    from not_less_Least[of _ ?Q, folded k_def] have less: "\<And> k'. k' < k \<Longrightarrow> \<not> ?Q k'" .
    from m ln have "m \<noteq> n" by auto
    with m_def have mn: "m < n" by auto
    {
      fix m'
      assume m': "m' \<le> n" "m' > m"
      then have not: "\<not> ?P m'" using less[of "n - m'"] m_def by auto
      from m' have "m' = Suc (m' - 1)" and "m' - 1 < n" by auto
      with reason have "as m' \<in> set (new_as [bs m'] remain)" and b: "bs m' \<in> set (Q' (as (m' - 1)))" by auto
      with not m' have "as m' \<in> set (new_as [bs m'] ?remain)" unfolding new_as_def by auto
      note this b
    } note greater = this
    let ?as = "\<lambda> i. as (m + i + 1)"
    let ?bs = "\<lambda> i. bs (m + i + 1)"
    let ?n = "n - m - 1"
    show ?thesis
    proof (rule IH[of "bs (m + 1)" ?bs a ?as ?n], intro conjI allI impI)
      fix i
      assume "i \<le> ?n"
      then show "?as i \<in> set (new_as [?bs i] ?remain)"
        by (intro greater, insert mn, auto)
    next
      from reason mn have "bs (m + 1) \<in> Q (as m)" by auto
      with m show "bs (m + 1) \<in> set ?bsi" by auto
    qed (insert reason mn, auto)
  qed
qed

lemma the_set_impl: "set (the_set_impl bs) = { a . \<exists> b \<in> set bs. the_set b a}" (is "?l = ?r")
proof -
  {
    fix a
    assume "a \<in> ?l"
    from this[unfolded the_set_impl_def]
      the_set_impl_main_sound[of Nil "{}" R' bs]
    have "a \<in> ?r" by auto
  }
  moreover
  {
    fix a
    assume "a \<in> ?r"
    then obtain b where b: "b \<in> set bs" and a: "the_set b a" by auto
    from the_set_reason[OF a] obtain n bs as where "reason R' b a n bs as" by blast
    from the_set_impl_main_complete[OF this b] have "a \<in> ?l" unfolding the_set_impl_def by auto
  }
  ultimately show ?thesis by blast
qed

context
  fixes P' :: "'b \<Rightarrow> 'a list"
  assumes P': "\<And> b. set (P' b) = { a. P b a \<and> a \<in> R}"
begin
lemma the_set_impl_main_lazy: assumes "set RR = set R' - set as"
  and "set as' = set as"
  and "set bs' = set bs"
  and "As' = set as'"
  shows "set (the_set_impl_main_lazy P' as' As' bs') =
    set (the_set_impl_main RR as bs)"
  using assms
proof (induct RR as bs arbitrary: as' bs' As' rule: the_set_impl_main.induct)
  case (1 RR as bs as' bs' As')
  let ?new_as' = "concat (map (\<lambda>b. concat (map (\<lambda>a. if a \<notin> As' then [a] else []) (P' b))) bs')"
  let ?new_as = "new_as bs RR"
  have new_as: "set ?new_as' = set ?new_as" unfolding new_as_def
    by (auto simp: 1(2-5) P')
  note simps = the_set_impl_main.simps[of _ _ bs] the_set_impl_main_lazy.simps[of _ _ _ bs'] Let_def
  show ?case 
  proof (cases "?new_as = []")
    case True
    with new_as have new_as: "?new_as' = []" by auto
    show ?thesis unfolding simps new_as True by (auto simp: 1(3-5))
  next
    case False
    with new_as have new_as'F: "(?new_as' = []) = False" by (cases ?new_as', auto)+
    from new_as False have new_asF: "(?new_as = []) = False" by simp
    show ?thesis unfolding simps new_asF new_as'F if_False
      by (rule 1(1)[OF refl False], (force simp: 1(2-5) new_as[symmetric])+)
  qed
qed

lemma the_set_impl_lazy_eq: 
  "set (the_set_impl_lazy P' bs) = set (the_set_impl bs)"
  unfolding the_set_impl_def the_set_impl_lazy_def 
  using the_set_impl_main_lazy [of R' Nil Nil bs bs] by auto

lemma the_set_impl_lazy: 
  "set (the_set_impl_lazy P' bs) = { a . \<exists> b \<in> set bs. the_set b a}" (is "?l = ?r")
  unfolding the_set_impl_lazy_eq by (rule the_set_impl)
end
end

lemma inductive_set_impl_lazy: assumes R: "set R' = R" and P: "\<And> b a. set (P' b) = {a. P b a \<and> a \<in> R}" and Q: "\<And> a. set (Q' a) = Q a"
  shows "set (inductive_set_impl_lazy P' Q' bs) = {a. \<exists>b\<in>set bs. generic_inductive_set.the_set R P Q b a}"
  unfolding inductive_set_impl_lazy_def
  by (rule generic_inductive_set_list_impl_sound.the_set_impl_lazy[OF _ P],
  unfold_locales, rule R, rule Q)

lemma inductive_set_impl: assumes R: "set R' = R" and P: "\<And> b a. P' b a = P b a" and Q: "\<And> a. set (Q' a) = Q a"
  shows "set (inductive_set_impl R' P' Q' bs) = {a. \<exists>b\<in>set bs. generic_inductive_set.the_set R P Q b a}"
proof -
  from P have P: "P' = P" by (intro ext, auto)
  with R Q show ?thesis
  using 
  generic_inductive_set_list_impl_sound.the_set_impl
  [unfolded generic_inductive_set_list_impl_sound_def, folded inductive_set_impl_def] 
  by blast
qed

lemma inductive_set_impl_pred: assumes R: "set R' = R" and P: "\<And> b a. P' b a = P b a" and Q: "\<And> a. set (Q' a) = Q a"
  and B: "set bs = {b. B b}"
  shows "set (inductive_set_impl R' P' Q' bs) = {a. \<exists>b. B b \<and> generic_inductive_set.the_set R P Q b a}"
  by (rule trans[OF inductive_set_impl[OF R P Q]], unfold B, blast)

lemma inductive_set_impl_single: "set R' = R \<Longrightarrow> (\<And> b a. P' b a = P b a) \<Longrightarrow> (\<And> a. set (Q' a) = Q a) \<Longrightarrow>
  set (inductive_set_impl R' P' Q' [b]) = {a. generic_inductive_set.the_set R P Q b a}"
  by (simp add: inductive_set_impl) 

end
