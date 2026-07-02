(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Critical Pairs for Right Conditional Semi-Thue Systems\<close>

theory CSTS_R_Critical_Pairs
  imports
   Conditional_String_Rewriting
   ShortLex
begin

(* Definition 31(i) *)
definition csts_r_critical_pairs where
  "csts_r_critical_pairs R = {((v @ y, x @ v'), cs' @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs) | x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {((v, x @ v' @ y), cs @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs') | x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and>
    u = x @ u' @ y}"

lemma csts_r_critical_pairs_elim:
  fixes R :: "csts"
  assumes "((s, t), cond) \<in> csts_r_critical_pairs R"
  shows "\<exists>x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and> ((u @ y = x @ u' \<and> length x < length u \<and>
    s = v @ y \<and> t = x @ v' \<and> cond = cs' @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs) \<or> (u = x @ u' @ y \<and> s = v \<and> t = x @ v' @ y \<and> cond = cs @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs'))"
  using assms unfolding csts_r_critical_pairs_def by blast

definition csts_conds_r_sat where
  "csts_conds_r_sat R cs y \<longleftrightarrow> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ y, t\<^sub>i @ y) \<in> (csr_r_join_step R)\<^sup>\<down>)"

definition all_ccps_r_joinable where
  "all_ccps_r_joinable R = (\<forall>s t cs. ((s, t), cs) \<in> csts_r_critical_pairs R \<longrightarrow>
    (\<forall>y. csts_conds_r_sat R cs y \<longrightarrow> (s @ y, t @ y) \<in> (csr_r_join_step R)\<^sup>\<down>))"

lemma cond_r_sat_append: assumes "csts_conds_r_sat R cs (y @ w)"
  shows "csts_conds_r_sat R (map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs) w" 
proof -
  from assms have "(\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ y @ w, t\<^sub>i @ y @ w) \<in> (csr_r_join_step R)\<^sup>\<down>)" 
    by (simp add: csts_conds_r_sat_def)
  hence "(\<forall>(s\<^sub>i, t\<^sub>i) \<in> set (map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs). (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step R)\<^sup>\<down>)" unfolding app_list_def 
    by (auto split:prod.splits)
  then show ?thesis using csts_conds_r_sat_def by (auto split:prod.splits)
qed

lemma csts_conds_concat_sat: assumes "csts_conds_r_sat R cs w"
  and "csts_conds_r_sat R cs' w"
shows "csts_conds_r_sat R (cs @ cs') w" using assms unfolding csts_conds_r_sat_def by auto 

lemma CR_imp_all_ccps_r_joinable:
  fixes R :: "csts"
  assumes cr:"CR (csr_r_join_step R)"
  shows "all_ccps_r_joinable R"
unfolding all_ccps_r_joinable_def
proof (intro allI impI)
  fix s t cond app
  assume ccps:"((s, t), cond) \<in> csts_r_critical_pairs R" and cond_sat:"csts_conds_r_sat R cond app"
  then obtain x y u v u' v' cs cs' where uv:"((u, v), cs) \<in> R" and u'v':"((u', v'), cs') \<in> R" and 
    "((u @ y = x @ u' \<and> length x < length u \<and>
    s = v @ y \<and> t = x @ v' \<and> cond = cs' @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs) \<or> (u = x @ u' @ y \<and> s = v \<and> t = x @ v' @ y \<and> cond = cs @ map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs'))"
    using csts_r_critical_pairs_elim[OF ccps] by blast
  then show "(s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>"
  proof(auto, goal_cases)
    case 1
    from cond_sat[unfolded csts_conds_r_sat_def] 
    have *:"\<forall>(s, t) \<in> set cond. (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" by (auto split:prod.splits)
    hence "\<forall>(s, t) \<in> set (map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs). (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using 1(6)
      by (auto split:prod.splits) 
    hence "\<forall>(s, t) \<in> set cs. (s @ y @ app, t @ y @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" 
      by (auto split:prod.splits) 
    hence "(u @ y @ app, v @ y @ app) \<in> csr_r_join_step R" using uv csr_r_join_stepI[of u v cs R "y @ app" Hole] 
      by (auto split:prod.splits) 
    hence "(x @ u' @ app, v @ y @ app) \<in> csr_r_join_step R" by (metis 1(3) append.assoc)
    moreover have "(x @ u' @ app, x @ v'@ app) \<in> csr_r_join_step R"
    proof -
      from * have "\<forall>(s, t) \<in> set cs'. (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using 1(6)
        by (auto split:prod.splits)
      hence "(u' @ app, v' @ app) \<in> csr_r_join_step R" using u'v' csr_r_join_stepI[of u' v' cs' R app Hole] 
        by (auto split:prod.splits) 
      then show ?thesis 
        by (metis append.right_neutral csr_r_join_step_ctxt_closed sctxt_closed_strings)
    qed
    ultimately show ?case using cr[unfolded CR_on_def] by blast
  next
    case 2
    from cond_sat[unfolded csts_conds_r_sat_def] 
    have *:"\<forall>(s, t) \<in> set cond. (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" by (auto split:prod.splits)
    hence "\<forall>(s, t) \<in> set cs. (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using 2(5)
      by (auto split:prod.splits)
    hence **:"(u @ app, v @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using uv csr_r_join_stepI[of u v cs R app Hole]
      by (auto split:prod.splits)
    from * have "\<forall>(s, t) \<in> set (map (\<lambda>(lhs, rhs). (lhs @ y, rhs @ y)) cs'). (s @ app, t @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using 2(5) by auto
    hence "\<forall>(s, t) \<in> set cs'. (s @ y @ app, t @ y @ app) \<in> (csr_r_join_step R)\<^sup>\<down>"
      by (auto split:prod.splits)
    hence "(u' @ y @ app, v' @ y @ app) \<in> (csr_r_join_step R)" using u'v' csr_r_join_stepI[of u' v' cs' R "y @ app" Hole]
      by (auto split:prod.splits)
    hence "(x @ u' @ y @ app, x @ v' @ y @ app) \<in> (csr_r_join_step R)"
      by (metis append.right_neutral csr_r_join_step_ctxt_closed sctxt_closed_strings)
    hence "(u @ app, x @ v' @ y @ app) \<in> (csr_r_join_step R)\<^sup>\<down>" using 2(3) by auto
    then show ?case using cr[unfolded CR_on_def] using 2(3) **
      by (meson CR_join_left_I cr joinD rtrancl_join_join)
  qed
qed

lemma app_join_csr_r_joinstep[simp]: assumes "(u, v) \<in> (csr_r_join_step R)\<^sup>\<down>"
  shows "(u @ w, v @ w) \<in> (csr_r_join_step R)\<^sup>\<down>" using assms unfolding csr_r_join_step_def 
  by (metis append.right_neutral csr_r_join_step_ctxt_closed csr_r_join_step_def 
      empty_append join_def sctxt.closed_comp sctxt.closed_converse sctxt.closed_rtrancl sctxt_closed_strings)


locale reductive_r_join = shortlex_total
begin

definition reductive :: "csts \<Rightarrow> bool"
where
  "reductive R \<longleftrightarrow> (\<forall>((l, r),cs) \<in> R. l \<succ>\<^sub>s\<^sub>l r \<and> (\<forall>(u, v) \<in> set cs. l \<succ>\<^sub>s\<^sub>l u \<and> l \<succ>\<^sub>s\<^sub>l v))"

lemma sl_preserve_csr_r_step:assumes st:"(s, t) \<in> (csr_r_join_step R)"
  and rd:"reductive R"
shows "s \<succ>\<^sub>s\<^sub>l t"
proof -
  from st obtain n where "(s, t) \<in> (csr_r_join_step_n R (Suc n))"
    using csr_r_join_step_iff using csr_r_join_step_n_E by blast
  then obtain C l r w cs where lr:"((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n)\<^sup>\<down>"
    and s:"s = C\<llangle>l @ w\<rrangle>"
    and t:"t = C\<llangle>r @ w\<rrangle>" using csr_r_join_step_n_SucE[of s t R n] by auto
  from rd[unfolded reductive_def] have lgr:"l \<succ>\<^sub>s\<^sub>l r" using lr by auto
  have "l @ w \<succ>\<^sub>s\<^sub>l r @ w" using sctxt_shortlex_closed_S_pre[of l r "[]" w] using lgr by auto
  then show ?thesis using sctxt_shortlex_closed_S[of "l @ w" "r @ w" C] using s t 
    by fastforce
qed

lemma sl_preserve_csr_r_step_transitive: assumes st:"(s, t) \<in> (csr_r_join_step R)\<^sup>+"
  and rd:"reductive R"
shows "s \<succ>\<^sub>s\<^sub>l t" using st
proof(induct)
  case (base y)
  then show ?case 
    using sl_preserve_csr_r_step rd by blast
next
  case (step y z)
  from  sl_preserve_csr_r_step[of y z R]
  have "y \<succ>\<^sub>s\<^sub>l z" using rd step by auto
  then show ?case using step(3) shortlex_trans[of s y z] by fastforce
qed

lemma sl_preserve_csr_r_step_rtrans: assumes st:"s \<succ>\<^sub>s\<^sub>l t"
  and rd:"reductive R"
  and tu:"(t, u) \<in> (csr_r_join_step R)\<^sup>*"
shows "s \<succ>\<^sub>s\<^sub>l u" using tu
proof(induct)
  case base
  then show ?case using assms by auto
next
  case (step y z)
  then show ?case using assms shortlex_trans 
    by (metis sl_preserve_csr_r_step)
qed

definition csr_r_join_desc :: "string \<Rightarrow> csts \<Rightarrow> string set" where
  "csr_r_join_desc u R = {v. (u, v) \<in> (csr_r_join_step R)\<^sup>*}"

definition csr_r_join_desc_single :: "string \<Rightarrow> csts \<Rightarrow> string set" where
  "csr_r_join_desc_single u R = {v. (u, v) \<in> csr_r_join_step R}"

lemma sctxt_pred_r_to_string: fixes u::string
  shows "{v | C v l r w cs. u = C\<llangle>l @ w\<rrangle> \<and> v = C\<llangle>r @ w\<rrangle> \<and> P l r cs} = {v | x y v l r w cs.  u = x @ l @ w @ y \<and> 
    v = x @ r @ w @ y \<and> P l r cs}" by (auto, metis append.assoc sctxt_app_step, metis ShortLex.hole 
    ShortLex.more append_assoc)

lemma finite_image_conc: assumes "finite A"
  and "finite B"
shows "finite {x @ y | x y. x \<in> A \<and> y \<in> B}" using assms 
  by (simp add: finite_image_set2)

lemma sublist_r_finite: fixes u::string and R::csts
  assumes fnR:"finite R"
  shows "finite {(x @ r @ w @ y) | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" using assms 
proof -
  have lr:"finite {(l, r) | x y l r cs v w. u = x @ l @ w @ y  \<and> ((l, r), cs) \<in> R}" using fnR
      finite_Domain Collect_mono_iff Domain_unfold finite_subset by (smt (z3))
  have l'r':"finite {(l, r) | l r cs. ((l, r), cs) \<in> R}" using fnR finite_Domain 
    by (smt (verit) Collect_cong Domain_unfold case_prodI2 case_prod_curry)
  have l':"finite {l |  l r cs . ((l, r), cs) \<in> R}" using  l'r'  finite_Domain by fastforce 
  hence r':"finite {r |  l r cs . ((l, r), cs) \<in> R}" using  l'r' l'  finite_Domain by fastforce 
  hence l:"finite {l | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" 
    using Collect_mono_iff finite_subset Collect_mono_iff Domain_unfold finite_subset l' by force
  have "{y | x y l r cs w.  u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R} \<subseteq> set (subseqs u)" 
    by (auto, simp add: list_emb_append2)
  hence fnY:"finite {y | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}"  (is "finite ?Y") 
    using infinite_super by blast
  have "{x | x y l r cs w.  u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R} \<subseteq> set (subseqs u)" by auto
  hence fnX:"finite {x | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" (is "finite ?X") 
    using infinite_super by blast
  have r:"finite {r | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" (is "finite ?R")
    using Collect_mono_iff finite_subset Collect_mono_iff Domain_unfold finite_subset r' by (smt (verit, best))
  let ?C = "{x @ r | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}"
  have "?X = {x | x . x \<in> ?X}" by force
  moreover have "?R = {x | x . x \<in> ?R}" by force
  ultimately have c:"?C \<subseteq> {x @ r | x r . x \<in> ?X \<and> r \<in> ?R }" using fnX r by blast
  have "finite {x @ r | x r . x \<in> ?X \<and> r \<in> ?R }" using finite_image_conc[of ?X ?R] c fnX r by auto 
  hence fnC:"finite ?C" using c by (meson finite_subset)
  have "{w | x y l r cs w.  u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R} \<subseteq> set (subseqs u)" by force
  hence fnW:"finite {w | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" (is "finite ?W") 
    using infinite_super by blast
  let ?D = "{x @ r @ w | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R }"
  have d:"?D \<subseteq> {s @ s' | s s'. s \<in> ?C \<and> s' \<in> ?W}"
    by (smt (verit) Collect_mono_iff append.assoc mem_Collect_eq)
  hence fnD:"finite {s @ s' | s s'. s \<in> ?C \<and> s' \<in> ?W}" (is "finite ?D")
    using fnC fnW finite_image_conc by blast
  let ?E = "{x @ r @ w @ y | x y l r cs w . u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R }"
  have d:"?E \<subseteq> {s @ s' | s s'. s \<in> ?D \<and> s' \<in> ?Y}"
    by (auto, metis append_eq_append_conv2)
  moreover have "finite {s @ s' | s s'. s \<in> ?D \<and> s' \<in> ?Y}" using fnD fnY finite_image_conc by blast
  ultimately show ?thesis using finite_subset by fastforce
qed

lemma finite_desc_r_sctxt_pre: fixes R::csts and u::string
  assumes fnR: "finite R"
  shows "finite {v | l r cs x y v w. u = x @ l @ w @ y \<and> v = x @ r @ w @ y \<and> ((l, r), cs) \<in> R}" using assms 
proof -
  have lr:"finite {(l, r) | x y l r cs v w. u = x @ l @ w @ y \<and> v = x @ r @ w @ y \<and> ((l, r), cs) \<in> R}" using fnR
      finite_Domain by (smt (verit, ccfv_SIG) Collect_mono_iff Domain_unfold finite_subset)
  have l:"finite {l | x y l r cs v w. u = x @ l @ w @ y \<and> v = x @ r @ w @ y \<and> ((l, r), cs) \<in> R}" 
    using lr finite_Domain  by (smt (verit, best) Collect_cong Domain_unfold mem_Collect_eq prod.inject)
  have l'r':"finite {(l, r) | l r cs. ((l, r), cs) \<in> R}" using fnR finite_Domain 
    by (smt (verit) Collect_cong Domain_unfold case_prodI2 case_prod_curry)
  have l':"finite {l |  l r cs . ((l, r), cs) \<in> R}" using  l'r'  finite_Domain by fastforce 
  hence r':"finite {r |  l r cs . ((l, r), cs) \<in> R}" using  l'r' l'  finite_Domain by fastforce 
  hence r:"finite {r | x y l r cs v w. u = x @ l @ w @  y \<and> ((l, r), cs) \<in> R}" 
    using Collect_mono_iff finite_subset by fastforce
  hence "finite {x @ r @ w @ y | x y l r cs w. u = x @ l @ w @ y \<and> ((l, r), cs) \<in> R}" using  fnR sublist_r_finite[of R u]
    by auto
  then show ?thesis using lr l r 
    by (smt (verit, ccfv_threshold) Collect_cong)
qed

lemma finite_desc_r_sctxt: fixes R::csts and u::string
  assumes fnR: "finite R"
  shows "finite {v | C l r cs v w. u = C\<llangle>l @ w\<rrangle> \<and> v = C\<llangle>r @ w\<rrangle> \<and> ((l, r), cs) \<in> R}" (is "finite ?A")
proof -
  let ?P = "\<lambda> l r cs. ((l, r), cs) \<in> R"
  show ?thesis using assms finite_desc_r_sctxt_pre[of R u] 
    sctxt_pred_r_to_string[of u ?P] by (smt (verit) Collect_cong)
qed

lemma finite_descendants_csr_r_join_steps: fixes u::string and R::csts 
  assumes rd:"reductive R"
    and fn:"finite R"
  shows "finite (csr_r_join_desc u R)"
proof -
  have sn:"SN shortlex_S" using shortlex_SN by auto
  show ?thesis
  proof(induct rule: wf_induct[OF SN_imp_wf[OF sn], rule_format])
    case (1 u)
    let ?single_desc = "{v. (u, v) \<in> (csr_r_join_step R)}"
    have ord:"\<forall>d. d \<in> ?single_desc \<longrightarrow> u \<succ>\<^sub>s\<^sub>l d" using rd
      by (metis mem_Collect_eq sl_preserve_csr_r_step)
    have *:"\<forall>v. v \<in> ?single_desc \<longrightarrow> (\<exists>C l r cs w. ((l, r), cs) \<in> R \<and> u = C\<llangle>l @ w\<rrangle>)"
      by blast
    have fn_single:"finite (?single_desc)"
    proof -
      have sub:"?single_desc \<subseteq> {v | C l r cs v w.  u = C\<llangle>l @ w\<rrangle> \<and> v = C\<llangle>r @ w\<rrangle> \<and> ((l, r), cs) \<in> R}" (is "?A \<subseteq> ?B") by blast
      have "finite {v | C l r cs v w.  u = C\<llangle>l @ w\<rrangle> \<and> v = C\<llangle>r @ w\<rrangle> \<and> ((l, r), cs) \<in> R}" 
        using finite_desc_r_sctxt[of R u] fn by fastforce 
      then show ?thesis using sub by (meson finite_subset)
    qed
    have **:"csr_r_join_desc u R = {u} \<union> {w |v w. v \<in> ?single_desc \<and> (v, w) \<in> (csr_r_join_step R)\<^sup>*}" (is "_ = ?X \<union> ?Y")
      unfolding csr_r_join_desc_def by (auto, metis converse_rtranclE)
    have "finite ?X" by force
    moreover have "finite ?Y" using ord fn_single 
      by (auto, metis 1 case_prodI converse_iff csr_r_join_desc_def mem_Collect_eq rd sl_preserve_csr_r_step)
    ultimately show ?case using ** by simp
  qed
qed  


(* Lemma 30(i) *)
lemma SN_and_finite_descendants_csr_r_join_steps: 
  assumes rd:"reductive R" and fn:"finite R" 
  shows "SN (csr_r_join_step R) \<and> finite (csr_r_join_desc u R)"
proof(rule conjI, goal_cases)
  case 1
  then show ?case using assms[unfolded reductive_def] case_prodI shortlex_SN sl_preserve_csr_r_step
  unfolding CollectI SN_on_def by (auto split:prod.splits, insert rd, metis CollectI UNIV_I sl_preserve_csr_r_step)
next
  case 2
  then show ?case using finite_descendants_csr_r_join_steps[OF rd fn] by auto
qed

end


context reductive_r_join
begin

lemma disjoint_r_imp_CR:
  fixes R :: "csts"
  assumes rd:"reductive R"
    and s1:"s = bef @ l @ w @ aft" 
    and s2:"s = bef' @ l' @ w' @ aft'"
    and t':"t' = bef @ r @ w @ aft" 
    and u':"u' = bef' @ r' @ w' @ aft'"
    and len:"length bef' \<ge> length (bef @ l)"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
      cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
      cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i @ w', t\<^sub>i @ w') \<in> (csr_r_join_step_n R m')\<^sup>\<down>"
    and IH:"\<forall>a b c. ((a, s) \<in> shortlex_S\<inverse> \<longrightarrow>
      (a, b) \<in> (csr_r_join_step R)\<^sup>* \<longrightarrow> (a, c) \<in> (csr_r_join_step R)\<^sup>* \<longrightarrow> (b, c) \<in> (csr_r_join_step R)\<^sup>\<down>)"
  shows "(t', u') \<in> (csr_r_join_step R)\<^sup>\<down>"
proof -
  from len s1 s2 obtain some where s_new:"s = bef @ l @ some @ l' @ w' @ aft'" 
    by (auto, metis append_eq_appendI append_eq_append_conv_if)
  hence pr:"prefix w (some @ l' @ w' @ aft')" using prefixI s1 by blast
  hence t_new:"t' = bef @ r @ some @ l' @ w' @ aft'" using t' s_new s1 by fastforce
  from pr obtain some' where some':"some @ l' @ w' @ aft' = w @ some'"
    using prefixE by blast
  from s_new u' have u:"u' = bef @ l @ some @ r' @ w' @ aft'" using s2 by auto
  let ?join ="bef @ r @ some @ r' @ w' @ aft'"
  have *:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs'. (s\<^sub>i @ w', t\<^sub>i @ w') \<in> (csr_r_join_step R)\<^sup>\<down>" using cond2 csr_r_join_step_iff
    by (auto split:prod.splits, metis csr_r_join_steps_n_imp_csteps joinD joinI)
  have "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step R)\<^sup>\<down>" 
    using cond1 csr_r_join_step_iff 
    by (auto split:prod.splits, metis csr_r_join_steps_n_imp_csteps joinD joinI)
  hence csj:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i @ some @ l' @ w' @ aft', t\<^sub>i @ some @ l' @ w' @ aft') \<in> (csr_r_join_step R)\<^sup>\<down>"
    using some' app_join_csr_r_joinstep by (auto split:prod.splits, metis append.assoc)
  from rd[unfolded reductive_def]
  have "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. l \<succ>\<^sub>s\<^sub>l s\<^sub>i \<and> l \<succ>\<^sub>s\<^sub>l t\<^sub>i" using lr by (auto split:prod.splits, fastforce+)
  hence "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. l @ some @ l' @ w' @ aft' \<succ>\<^sub>s\<^sub>l s\<^sub>i @ some @ l' @ w' @ aft' \<and> 
              l @ some @ l' @ w' @ aft' \<succ>\<^sub>s\<^sub>l t\<^sub>i @ some @ l' @ w' @ aft'" using   
    sctxt_shortlex_closed_S_pre by (auto split:prod.splits, fastforce, fastforce) 
      (smt (z3) append.assoc append_Cons lexorder.elims(2) order_less_imp_not_less, fastforce) 
  hence "\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. bef @ l @ some @ l' @ w' @ aft' \<succ>\<^sub>s\<^sub>l s\<^sub>i @ some @ l' @ w' @ aft' \<and> 
              bef @ l @ some @ l' @ w' @ aft' \<succ>\<^sub>s\<^sub>l t\<^sub>i @ some @ l' @ w' @ aft'" using sl_left_append[of "set cs" "l @ some @ l' @ w' @ aft'" "some @ l' @ w' @ aft'" bef]
    by (auto split:prod.splits)
  hence ssl:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. s \<succ>\<^sub>s\<^sub>l s\<^sub>i @ some @ l' @ w' @ aft' \<and> s \<succ>\<^sub>s\<^sub>l t\<^sub>i @ some @ l' @ w' @ aft'" 
    using s_new by auto
  have **:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i @ some @ r' @ w' @ aft', t\<^sub>i @ some @ r' @ w' @ aft') \<in> (csr_r_join_step R)\<^sup>\<down>"
  proof -
    {
      fix u v
      assume uv:"(u, v) \<in> set cs"
      hence "(u @ some @ r' @ w' @ aft', v @ some @ r' @ w' @ aft') \<in> (csr_r_join_step R)\<^sup>\<down>"
      proof -
        have "(u @ some @ l' @ w' @ aft', v @ some @ l' @ w' @ aft') \<in> (csr_r_join_step R)\<^sup>\<down>"
          using csj uv by (auto split:prod.splits) 
        then obtain cjoin where uc:"(u @ some @ l' @ w' @ aft', cjoin) \<in> (csr_r_join_step R)\<^sup>*" and
          vc:"(v @ some @ l' @ w' @ aft', cjoin) \<in> (csr_r_join_step R)\<^sup>*" by auto
        have ustep:"(u @ some @ l' @ w' @ aft', u @ some @ r' @ w' @ aft') \<in> (csr_r_join_step R)"
          using l'r' * csr_r_join_stepI[of l' r' cs' R w'] by (auto split:prod.splits, 
              metis append_eq_appendI csr_r_join_step_ctxt_closed 
              sctxt_apply_string.simps(1) sctxt_closed_strings)
        have vstep:"(v @ some @ l' @ w' @ aft', v @ some @ r' @ w' @ aft') \<in> (csr_r_join_step R)"
          using l'r' * csr_r_join_stepI[of l' r' cs' R w'] by (auto split:prod.splits, 
              metis append_eq_appendI csr_r_join_step_ctxt_closed 
              sctxt_apply_string.simps(1) sctxt_closed_strings)
        note IH_cujoin = IH[rule_format, of "u @ some @ l' @ w' @ aft'" "u @ some @ r' @ w' @ aft'" "cjoin"]
        note IH_cvjoin = IH[rule_format, of "v @ some @ l' @ w' @ aft'" "v @ some @ r' @ w' @ aft'" "cjoin"]
        have su:"s \<succ>\<^sub>s\<^sub>l u @ some @ l' @ w' @ aft'" and sv:"s \<succ>\<^sub>s\<^sub>l v @ some @ l' @ w' @ aft'"
          using ssl uv by (auto split:prod.splits)
        from su obtain cujoin where cujoin:"(u @ some @ r' @ w' @ aft', cujoin) \<in> (csr_r_join_step R)\<^sup>*" and
          cjcu:"(cjoin, cujoin) \<in> (csr_r_join_step R)\<^sup>*" 
          by (metis uc su IH_cujoin case_prodI converseI joinD mem_Collect_eq r_into_rtrancl ustep)
        from sv obtain cvjoin where cvjoin:"(v @ some @ r' @ w' @ aft', cvjoin) \<in> (csr_r_join_step R)\<^sup>*" and
          cjcv:"(cjoin, cvjoin) \<in> (csr_r_join_step R)\<^sup>*" 
          by (metis vc sv IH_cvjoin case_prodI converseI joinD mem_Collect_eq r_into_rtrancl vstep)
        have s_cjoin:"s \<succ>\<^sub>s\<^sub>l cjoin" using sl_preserve_csr_r_step_rtrans[of s "u @ some @ l' @ w' @ aft'" R cjoin] using su rd uc
          by fastforce
        note IH_cjoin = IH[rule_format, of "cjoin" "cujoin" "cvjoin"]
        then show ?thesis using IH_cjoin s_cjoin 
          by (metis case_prodI cjcu cjcv converse_iff cujoin cvjoin join_rtrancl_join mem_Collect_eq rtrancl_join_join)
        qed
    } then show ?thesis by blast
  qed
  let ?C = "More (bef @ r @ some) Hole aft'" 
  have "(t', ?join) \<in> csr_r_join_step R" using l'r' t_new * csr_r_join_stepI[of l' r' cs' R w' ?C]
    by (auto split:prod.splits) 
  moreover have "(u', ?join) \<in> csr_r_join_step R" using lr u ** csr_r_join_stepI[of l r cs R "some @ r' @ w' @ aft'" _]  
    by (auto split:prod.splits, metis append.right_neutral csr_r_join_step_ctxt_closed sctxt.cop_nil sctxt_closed_strings)
  ultimately show ?thesis by blast
qed

lemma critical_overlap_r_type1_imp_CR:
  fixes R :: "csts"
  assumes acj:"all_ccps_r_joinable R"
    and s1m:"s = mbef @ pbef @ l @ paft @ maft"
    and s2m:"s = mbef @ pbef' @ l' @ paft' @ maft"
    and t':"t' = bef @ r @ w @ aft"
    and u':"u' = bef' @ r' @ w' @ aft'"
    and pbe:"pbef = [] \<or> pbef' = []"
    and pae:"paft = [] \<or> paft' = []"
    and pbef:"mbef @ pbef = bef"
    and pbef':"mbef @ pbef' = bef'"
    and paft:"paft @ maft = w @ aft"
    and paft':"paft' @ maft = w' @ aft'"
    and len:"length pbef' \<le> length pbef \<and> length (pbef @ l) \<le> length (pbef' @ l')"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
      cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
      cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i @ w', t\<^sub>i @ w') \<in> (csr_r_join_step_n R m')\<^sup>\<down>"
  shows "(t', u') \<in> (csr_r_join_step R)\<^sup>\<down>"
proof -
  have l'l:"length l' \<ge> length l" using s1m s2m len by auto
  moreover have "length (mbef @ pbef) \<ge> length (mbef @ pbef')" using len pbe by auto
  moreover have len_main:"length (mbef @ pbef' @ l') \<ge> length (mbef @ pbef @ l)" 
    using len by auto
  moreover have el1:"\<exists>l1. s = mbef @ pbef' @ l1 @ l @ paft @ maft" 
    using len pbe s1m by fastforce
  moreover have suf:"suffix (paft' @ maft) (paft @ maft)" using len s1m s2m len_main 
    by (smt (verit, ccfv_threshold) append.assoc append.left_neutral append_eq_conv_conj 
        append_same_eq drop_eq_Nil length_append pae same_append_eq suffixI)
  then obtain l1 where sl1:"s = mbef @ pbef' @ l1 @ l @ paft @ maft" using el1 by auto
  moreover have "\<exists>l2. s = mbef @ pbef' @ l1 @ l @ l2 @ paft' @ maft" using s1m s2m len sl1 l'l len_main suf  
    by (auto, metis suffix_take)
  then obtain l2 where sl1l2:"s = mbef @ pbef' @ l1 @ l @ l2 @ paft' @ maft" by auto
  hence lpm:"l2 @ paft' @ maft = paft @ maft" 
    by (smt (verit, ccfv_SIG) append_same_eq length_append pae same_append_eq same_suffix_nil 
        self_append_conv self_append_conv2 sl1 suf)
  hence mpl:"mbef @ pbef' @ l1 = mbef @ pbef" 
    by (smt (verit, del_insts) append.assoc append_same_eq s1m same_append_eq sl1)
  ultimately have l':"l' = l1 @ l @ l2" using s1m s2m len
    by (smt (verit) append.assoc append_same_eq length_append same_append_eq sl1l2)
  hence s_new1:"s = mbef @ pbef' @ l1 @ l @ l2 @ paft' @ maft" using s2m by auto
  have s_new2:"s = mbef @ pbef' @ l' @ paft' @ maft" using s2m by auto
  hence t'_new:"t' = mbef @ pbef' @ l1 @ r @ l2 @ paft' @ maft" using paft lpm mpl pbef t' by fastforce
  have u'_new:"u' = mbef @ pbef' @ r' @ paft' @ maft" using u'
    by (metis append_assoc paft' pbef')
  have "((r', l1 @ r @ l2), cs' @ map (\<lambda>(lhs, rhs). (lhs @ l2, rhs @ l2)) cs) \<in> csts_r_critical_pairs R" 
    unfolding csts_r_critical_pairs_def using lr l'r' l' by auto
  moreover have "csts_conds_r_sat R cs' w'" unfolding csts_conds_r_sat_def
    by (auto, metis case_prod_conv cond2 csr_r_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_r_sat R cs w" using cond1 unfolding csts_conds_r_sat_def
    by (auto split:prod.splits, metis csr_r_join_steps_n_imp_csteps joinD joinI)
  moreover have "prefix w (l2 @ paft' @ maft)" using s_new1 s1m 
    by (metis lpm paft prefixI)
  moreover have "prefix w' (paft' @ maft)" by (metis paft' prefixI)
  moreover have "csts_conds_r_sat R cs' (paft' @ maft)" unfolding csts_conds_r_sat_def 
    by (auto,metis app_join_csr_r_joinstep append.assoc calculation(2) case_prod_conv csts_conds_r_sat_def paft')
  moreover have "csts_conds_r_sat R (map (\<lambda>(lhs, rhs). (lhs @ l2, rhs @ l2)) cs) (paft' @ maft)" using cond_r_sat_append 
    unfolding csts_conds_r_sat_def app_list_def
    by (auto, metis app_join_csr_r_joinstep append.assoc calculation(3) case_prodD csts_conds_r_sat_def lpm paft)
  moreover have "csts_conds_r_sat R (cs' @ map (\<lambda>(lhs, rhs). (lhs @ l2, rhs @ l2)) cs) (paft' @ maft)" 
    using csts_conds_concat_sat[of R cs' "paft' @ maft" "map (\<lambda>(lhs, rhs). (lhs @ l2, rhs @ l2)) cs"]
    by (metis calculation(6) calculation(7))
  ultimately have "(l1 @ r @ l2 @ paft' @ maft, r'@ paft' @ maft) \<in> (csr_r_join_step R)\<^sup>\<down>" using acj[unfolded all_ccps_r_joinable_def]
    by (metis append.assoc join_sym)
  then obtain join1 where j1:"(l1 @ r @ l2 @ paft' @ maft, join1) \<in> (csr_r_join_step R)\<^sup>*" and j2:"(r' @ paft' @ maft, join1) \<in> (csr_r_join_step R)\<^sup>*"
    by auto
  have "(mbef @ pbef' @ l1 @ r @ l2 @ paft' @ maft, mbef @ pbef' @ join1 ) \<in> (csr_r_join_step R)\<^sup>*"
    using j1 csr_r_join_sctxt_closed[of "l1 @ r @ l2 @ paft' @ maft" "join1" R "mbef @ pbef'" "[]" ] by auto 
  moreover have "(mbef @ pbef' @ r' @ paft' @ maft, mbef @ pbef' @ join1) \<in> (csr_r_join_step R)\<^sup>*"
    using j2 csr_r_join_sctxt_closed[of "r' @ paft' @ maft" "join1" R "mbef @ pbef'" "[]"] by auto
  ultimately show ?thesis using t'_new u'_new by auto
qed

lemma critical_overlap_r_type2_imp_CR:
  fixes R :: "csts"
  assumes acj:"all_ccps_r_joinable R"
    and s1m:"s = mbef @ pbef @ l @ paft @ maft"
    and s2m:"s = mbef @ pbef' @ l' @ paft' @ maft"
    and t':"t' = bef @ r @ w @ aft"
    and u':"u' = bef' @ r' @ w' @ aft'"
    and pbe:"pbef = [] \<or> pbef' = []"
    and pae:"paft = [] \<or> paft' = []"
    and pbef:"mbef @ pbef = bef"
    and pbef':"mbef @ pbef' = bef'"
    and paft:"paft @ maft = w @ aft"
    and paft':"paft' @ maft = w' @ aft'"
    and len_overlap:"(length (bef @ l) > length bef' \<and> length (bef' @ l') > length bef)"
    and len:"length pbef' < length pbef \<and> length (pbef' @ l') < length (pbef @ l)"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
      cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
      cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i @ w', t\<^sub>i @ w') \<in> (csr_r_join_step_n R m')\<^sup>\<down>"
  shows "(t', u') \<in> (csr_r_join_step R)\<^sup>\<down>"
proof -
  obtain u where u:"pbef = pbef' @ u" using len using pbe by fastforce
  have "prefix (mbef @ pbef @ l) s" using s1m by (metis append.assoc prefixI)
  moreover have "prefix (mbef @ pbef' @ l') s" using s2m by (metis append.assoc prefixI)
  moreover have "length (mbef @ pbef @ l) >  length (mbef @ pbef' @ l')" using len by auto
  ultimately have "strict_prefix (mbef @ pbef' @ l') (mbef @ pbef @ l)" using s1m s2m 
    by (metis (mono_tags, lifting) less_or_eq_imp_le nat_neq_iff prefix_length_prefix prefix_order.less_le) 
  then obtain v where v:"mbef @ pbef @ l = mbef @ pbef' @ l' @ v"  
    by (metis Nil_is_append_conv u pbe prefix_def prefix_order.less_le same_prefix_prefix)
  have nue:"u \<noteq> []" and nve:"v \<noteq> []" using len u v by auto
  let ?pbef = "take (length pbef - length u) pbef"
  let ?paft'= "drop (length v) paft'"
  have ueq:"?pbef @ u = pbef" using u by auto
  hence peq:"?pbef = pbef'" using s1m s2m u by auto
  have veq:"paft' @ maft = v @ ?paft' @ maft" using s2m v nve 
    by (smt (verit, del_insts) append.assoc append_eq_conv_conj append_same_eq length_append pae s1m same_append_eq)
  hence pmeq:"paft @ maft = ?paft' @ maft" using s1m s2m u v nve 
    by (smt (verit) append.assoc append_same_eq same_append_eq)
  have s1_new:"s = mbef @ ?pbef @ u @ l @ paft @ maft" using u s1m s2m by auto
  have s2_new:"s = mbef @ pbef' @ l' @ v @ ?paft' @ maft" using v s1m s2m veq by metis
  have t'_new:"t' = mbef @ ?pbef @ u @ r @ paft @ maft" using t' ueq
    by (metis append.assoc paft pbef)
  have u'_new:"u' = mbef @ pbef' @ r' @ v @ ?paft' @ maft" using v s1m s2m veq
    by (metis append.assoc paft' pbef' u')
  have "length u < length l'" using u len_overlap pbe pbef pbef' by fastforce
  hence "((r' @ v, u @ r), cs @ map (\<lambda>(lhs, rhs). (lhs @ v, rhs @ v)) cs') \<in> csts_r_critical_pairs R" 
    unfolding csts_r_critical_pairs_def using lr l'r' u v by (auto, metis)
  moreover have "csts_conds_r_sat R cs' w'" unfolding csts_conds_r_sat_def
    by (auto, metis case_prod_conv cond2 csr_r_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_r_sat R cs w" using cond1 unfolding csts_conds_r_sat_def
    by (auto split:prod.splits, metis csr_r_join_steps_n_imp_csteps joinD joinI)
  moreover have "prefix w (paft @ maft)" using s1_new s1m by (metis paft prefixI) 
  moreover have "prefix w' (paft' @ maft)" by (metis paft' prefixI)
  moreover have "csts_conds_r_sat R cs (paft @ maft)" unfolding csts_conds_r_sat_def 
    by (auto, metis app_join_csr_r_joinstep append.assoc calculation(3) case_prod_conv csts_conds_r_sat_def paft)
  moreover have "csts_conds_r_sat R (map (\<lambda>(lhs, rhs). (lhs @ v, rhs @ v)) cs') (paft @ maft)" using cond_r_sat_append v pmeq
    unfolding csts_conds_r_sat_def app_list_def 
    by (auto, metis app_join_csr_r_joinstep append.assoc calculation(2) case_prod_conv csts_conds_r_sat_def paft' veq)
  moreover have "csts_conds_r_sat R (cs @ map (\<lambda>(lhs, rhs). (lhs @ v, rhs @ v)) cs') (paft @ maft)" 
    using csts_conds_concat_sat [of R cs "paft @ maft" "map (\<lambda>(lhs, rhs). (lhs @ v, rhs @ v)) cs"] 
    by (metis calculation(6) calculation(7) csts_conds_concat_sat)
  ultimately have "(r' @ v @ paft @ maft, u @ r @ paft @ maft) \<in> (csr_r_join_step R)\<^sup>\<down>" using acj[unfolded all_ccps_r_joinable_def]
    by (metis append.assoc)
  then obtain join1 where j1:"(r' @ v @ paft @ maft, join1) \<in> (csr_r_join_step R)\<^sup>*" and j2:"(u @ r @ paft @ maft, join1) \<in> (csr_r_join_step R)\<^sup>*"
    by auto
  have "(mbef @ pbef' @ r' @ v @ paft @ maft, mbef @ pbef' @ join1 ) \<in> (csr_r_join_step R)\<^sup>*"
    using j1 csr_r_join_sctxt_closed[of "r' @ v @ paft @ maft" "join1" R "mbef @ pbef'" "[]" ] by auto 
  moreover have "(mbef @ ?pbef @ u @ r @ paft @ maft, mbef @ ?pbef @ join1) \<in> (csr_r_join_step R)\<^sup>*"
    using j2 csr_r_join_sctxt_closed[of "u @ r @ paft @ maft" "join1" R "mbef @ ?pbef" "[]"] by auto
  ultimately show ?thesis using t'_new u'_new peq pmeq by auto
qed

lemma all_ccps_r_joinable_imp_CR:
  fixes R :: "csts"
  assumes acj:"all_ccps_r_joinable R"
    and sn:"SN shortlex_S"
    and rd:"reductive R"
  shows "CR (csr_r_join_step R)" 
proof -
  {
    fix s t u
    assume str:"(s, t) \<in> (csr_r_join_step R)\<^sup>*" and sur:"(s, u) \<in> (csr_r_join_step R)\<^sup>*"
    hence "(t, u) \<in> (csr_r_join_step R)\<^sup>\<down>"
    proof(induct s arbitrary: t u rule: wf_induct[OF SN_imp_wf[OF sn], rule_format])
      case (1 s)
      note IH = this(1)
      { 
        assume "s = t \<or> s = u"
        hence "(t, u) \<in> (csr_r_join_step R)\<^sup>\<down>" using str sur 1(2-3) by blast
      }
      moreover
      {
        assume "\<exists>t'. (s, t') \<in> csr_r_join_step R \<and> (t', t) \<in> (csr_r_join_step R)\<^sup>*"
          and "\<exists>u'. (s, u') \<in> csr_r_join_step R \<and> (u', u) \<in> (csr_r_join_step R)\<^sup>*"
        then obtain t' u' where st':"(s, t') \<in> csr_r_join_step R" and t't:"(t', t) \<in> (csr_r_join_step R)\<^sup>*"
          and su':"(s, u') \<in> csr_r_join_step R" and u'u:"(u', u) \<in> (csr_r_join_step R)\<^sup>*" by auto
        from st' obtain n where st':"(s, t') \<in> csr_r_join_step_n R n" using csr_r_join_step_iff by auto
        from su' obtain m where su':"(s, u') \<in> csr_r_join_step_n R m" using csr_r_join_step_iff by auto
        from csr_r_join_step_n_E[OF st']
        obtain C l r w cs n' where lr:"((l, r), cs) \<in> R" and nn':"n = Suc n'" and 
          cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i @ w, t\<^sub>i @ w) \<in> (csr_r_join_step_n R n')\<^sup>\<down>" and
          sC:"s = C\<llangle>l @ w\<rrangle>" and tC:"t' = C\<llangle>r @ w\<rrangle>" by metis
        from csr_r_join_step_n_E[OF su']
        obtain D l' r' w' cs' m' where l'r':"((l', r'), cs') \<in> R" and mm':"m = Suc m'" and 
          cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i @ w', t\<^sub>i @ w') \<in> (csr_r_join_step_n R m')\<^sup>\<down>" and
          sD:"s = D\<llangle>l' @ w'\<rrangle>" and uD:"u' = D\<llangle>r' @ w'\<rrangle>" by metis
        from sC tC obtain bef aft where s1:"s = bef @ l @ w @ aft" and t':"t' = bef @ r @ w @ aft" 
          by (auto, metis append_assoc sctxt_app_step)
        from sD uD obtain bef' aft' where s2:"s = bef' @ l' @ w' @ aft'" and u':"u' = bef' @ r' @ w' @ aft'" 
          by (auto, metis append_assoc sctxt_app_step)
        hence t'u':"(t', u') \<in> (csr_r_join_step R)\<^sup>\<down>"
        proof (cases "length bef' \<ge> length (bef @ l) \<or> length bef \<ge> length (bef' @ l')")
          case True
          then show ?thesis
          proof
            assume asm:"length bef' \<ge> length (bef @ l)"
            note disjoint_r_imp_CR = disjoint_r_imp_CR[of R s bef l w aft bef' l' w' aft' t' r u' r' cs n n' cs' m m'] 
            then show ?thesis using disjoint_r_imp_CR rd s1 s2 t' u' asm lr l'r' IH(1) nn' mm' cond1 cond2 
              by (auto split:prod.splits, insert IH asm cond1 cond2, fastforce)
          next
            assume asm:"length bef \<ge> length (bef' @ l')"
            note disjoint_r_imp_CR' = disjoint_r_imp_CR[of R s bef' l' w' aft' bef l w aft u' r' t' r cs' m m' cs n n'] 
            then show ?thesis using disjoint_r_imp_CR' rd s1 s2 t' u' asm lr l'r' IH(1) nn' mm' cond1 cond2 
              by (auto split:prod.splits, metis IH asm cond1 cond2 join_sym)
          qed
        next
          case False
          hence *:"(length (bef @ l) > length bef' \<and> length (bef' @ l') > length bef)" by auto
          let ?mbef_size = "min (length bef) (length bef')"
          let ?maft_size = "min (length (w @ aft)) (length (w' @ aft'))"
          let ?mbef = "take ?mbef_size s"
          let ?maft = "drop (length s - ?maft_size) s"
          have pr1:"prefix ?mbef bef" by (simp add: s1 take_is_prefix)
          have pr2:"prefix ?mbef bef'" by (simp add: s2 take_is_prefix)
          have len1:"length (w @ aft) \<ge> length ?maft" by auto
          hence su1:"suffix ?maft (w @ aft)" using s1 suffixI suffix_appendD suffix_drop 
            by (auto, smt (verit, ccfv_SIG) add.commute diff_cancel2 diff_diff_left drop_append suffix_drop)
          have len2:"length (w' @ aft') \<ge> length ?maft" by auto
          have su2:"suffix ?maft (w' @ aft')"using s2 suffixI suffix_appendD suffix_drop 
            by (auto, smt (verit, ccfv_SIG) add.commute diff_cancel2 diff_diff_left drop_append suffix_drop)
          from pr1 obtain pbef where pbef:"?mbef @ pbef = bef" by (metis prefixE)
          from pr2 obtain pbef' where pbef':"?mbef @ pbef' = bef'" by (metis prefixE)
          from su1 obtain paft where paft:"paft @ ?maft = w @ aft" by (metis suffixE)
          from su2 obtain paft' where paft':"paft' @ ?maft = w' @ aft'" by (metis suffixE)
          have s1m:"s = ?mbef @ pbef @ l @ paft @ ?maft" using s1 pbef paft by auto
          have s2m:"s = ?mbef @ pbef' @ l' @ paft' @ ?maft" using s2 pbef' paft' by auto
          have pbe:"pbef = [] \<or> pbef' = []" using s1 s2 s1m s2m 
            by (metis append_eq_conv_conj min_def pbef pbef' self_append_conv)
          have pae:"paft = [] \<or> paft' = []" using s1 s2 s1m s2m  paft paft' 
            by (cases "length (w @ aft) \<ge> length (w' @ aft')", metis append_take_drop_id min.absorb2 
                same_append_eq self_append_conv2 suffixI suffix_append suffix_take)
             (smt (verit, best) append.assoc append_eq_append_conv append_take_drop_id min_def self_append_conv2 suffixI suffix_take)
          then show ?thesis
          proof(cases "(length pbef \<ge> length pbef' \<and> length (pbef' @ l') \<ge> length (pbef @ l)) \<or> 
            (length pbef' \<ge> length pbef \<and> length (pbef @ l) \<ge> length (pbef' @ l'))")
            case True
            then show ?thesis
            proof 
              assume asm:"length pbef' \<le> length pbef \<and> length (pbef @ l) \<le> length (pbef' @ l')"
              note critical_overlap_r_type1_imp_CR = critical_overlap_r_type1_imp_CR[of R s ?mbef pbef 
                  l paft ?maft pbef' l' paft' t' bef r w aft u' bef' r' w' aft' cs n n' cs' m m']
              show ?thesis using critical_overlap_r_type1_imp_CR asm acj cond1 cond2 
                  critical_overlap_r_type1_imp_CR l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                  s1m s2m t' u' by fastforce
            next
              assume asm:"length pbef \<le> length pbef' \<and> length (pbef' @ l') \<le> length (pbef @ l)"
              note critical_overlap_r_type1_imp_CR' = critical_overlap_r_type1_imp_CR[of R s ?mbef pbef' 
                  l' paft' ?maft pbef l paft u' bef' r' w' aft' t' bef r w aft cs' m m' cs n n']
              show ?thesis using critical_overlap_r_type1_imp_CR' asm acj asm cond1 cond2 
                  critical_overlap_r_type1_imp_CR' l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                  s1m s2m t' u' by blast
            qed
          next
            case False
            hence "(length pbef > length pbef' \<and> length (pbef @ l) > length (pbef' @ l') \<or>
                length pbef' > length pbef \<and> length (pbef' @ l') > length (pbef @ l))" (is "?A \<or> ?B") by auto
            then show ?thesis
            proof
              assume asm:"?A"
              note critical_overlap_r_type2_imp_CR = critical_overlap_r_type2_imp_CR[of R s ?mbef pbef l paft ?maft
                  pbef' l' paft' t' bef r w aft u' bef' r' w' aft' cs n n' cs' m m']
              show ?thesis using asm critical_overlap_r_type2_imp_CR 
                using * acj asm cond1 cond2 critical_overlap_r_type2_imp_CR l'r' lr mm' nn' pae paft 
                  paft' pbe pbef pbef' s1m s2m t' u' by fastforce
            next
              assume asm:"?B"
              note critical_overlap_r_type2_imp_CR' = critical_overlap_r_type2_imp_CR[of R s ?mbef pbef' l' paft' ?maft
                  pbef l paft u' bef' r' w' aft' t' bef r w aft cs' m m' cs n n']
              show ?thesis using asm critical_overlap_r_type2_imp_CR' using "*" acj asm cond1 
                  cond2 critical_overlap_r_type2_imp_CR' l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                  s1m s2m t' u' by blast
            qed
          qed
        qed
        hence "(t, u) \<in> (csr_r_join_step R)\<^sup>\<down>"
        proof -
          from t'u' obtain jt'u' where t'jt'u':"(t', jt'u') \<in> (csr_r_join_step R)\<^sup>*" and 
            u'jt'u':"(u', jt'u') \<in> (csr_r_join_step R)\<^sup>*" by auto
          from st' have st'R:"(s, t') \<in> csr_r_join_step R" using csr_r_join_step_n_imp_cstep by auto
          have sgt':"s \<succ>\<^sub>s\<^sub>l t'" using sl_preserve_csr_r_step[of s t' R] st'R rd by auto
          note IH_t'join = IH[of "t'" "jt'u'" "t"]
          have "(t, jt'u') \<in> (csr_r_join_step R)\<^sup>\<down>" using IH_t'join 
            by (metis IH_t'join t'jt'u' sgt' case_prodI converseI join_sym mem_Collect_eq t't)
          then obtain jtu' where tjtu':"(t, jtu') \<in> (csr_r_join_step R)\<^sup>*" and jj:"(jt'u', jtu') \<in> (csr_r_join_step R)\<^sup>*" by auto
          hence u'jtu':"(u', jtu') \<in> (csr_r_join_step R)\<^sup>*" using jj u'jt'u' by auto
          note IH_u'join = IH[of "u'" "jtu'" "u"]
          from su' have su'R:"(s, u') \<in> csr_r_join_step R" using csr_r_join_step_n_imp_cstep by auto
          have sgu':"s \<succ>\<^sub>s\<^sub>l u'" using sl_preserve_csr_r_step[of s u' R] su'R rd by auto
          hence "(jtu', u) \<in> (csr_r_join_step R)\<^sup>\<down>" using IH_u'join IH_u'join u'jtu' u'u sgu' by blast
          then obtain jtu where jtu'tu:"(jtu', jtu) \<in> (csr_r_join_step R)\<^sup>*" and ujtu:"(u, jtu) \<in> (csr_r_join_step R)\<^sup>*" by auto
          hence "(t, jtu) \<in> (csr_r_join_step R)\<^sup>*" and "(u, jtu) \<in> (csr_r_join_step R)\<^sup>*" 
            using tjtu' ujtu by auto
          then show ?thesis by auto
        qed
      }
      ultimately have "(t, u) \<in> (csr_r_join_step R)\<^sup>\<down>" 
        by (meson 1(2-3) converse_rtranclE)
      then show ?case by blast
    qed
  } then show ?thesis unfolding CR_on_def by auto
qed

(* Lemma 32 *)
lemma csts_r_critical_pair_lemma:
  assumes rd:"reductive R"
    and fn:"finite R"
  shows "CR (csr_r_join_step R) \<longleftrightarrow> all_ccps_r_joinable R"
proof 
  assume cr:"CR (csr_r_join_step R)"
  then show "all_ccps_r_joinable R" using CR_imp_all_ccps_r_joinable[of R] by auto
next
  assume "all_ccps_r_joinable R"
  then show "CR (csr_r_join_step R)" using all_ccps_r_joinable_imp_CR[of R] assms 
    using shortlex_SN by blast
qed

end

end
