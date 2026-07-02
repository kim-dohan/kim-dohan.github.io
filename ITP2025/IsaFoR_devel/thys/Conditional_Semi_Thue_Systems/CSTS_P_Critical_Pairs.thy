(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Critical Pairs for Pure Conditional Semi-Thue Systems\<close>

theory CSTS_P_Critical_Pairs
  imports
    Conditional_String_Rewriting
    ShortLex
begin

(* Definition 31(iii) *)
definition csts_p_critical_pairs :: "csts \<Rightarrow> csts" where
  "csts_p_critical_pairs R = {((v @ y, x @ v'), cs' @ cs) | x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {((v, x @ v' @ y), cs @ cs') | x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and>
    u = x @ u' @ y}"

lemma csts_p_critical_pairs_elim:
  fixes R :: "csts"
  assumes "((s, t), cond) \<in> csts_p_critical_pairs R"
  shows "\<exists>x y u v u' v' cs cs'. ((u, v), cs) \<in> R \<and> ((u', v'), cs') \<in> R \<and> ((u @ y = x @ u' \<and> length x < length u \<and>
    s = v @ y \<and> t = x @ v' \<and> cond = cs' @ cs) \<or> (u = x @ u' @ y \<and> s = v \<and> t = x @ v' @ y \<and> cond = cs @ cs'))"
  using assms unfolding csts_p_critical_pairs_def by blast

definition csts_conds_p_sat where
  "csts_conds_p_sat R cs \<longleftrightarrow> (\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>)"

definition all_ccps_p_joinable where
  "all_ccps_p_joinable R = (\<forall>s t cs. ((s, t), cs) \<in> csts_p_critical_pairs R \<longrightarrow>
    csts_conds_p_sat R cs \<longrightarrow> (s, t) \<in> (csr_p_join_step R)\<^sup>\<down>)"

lemma csts_p_conds_concat_sat: assumes "csts_conds_p_sat R cs"
  and "csts_conds_p_sat R cs'"
shows "csts_conds_p_sat R (cs @ cs')" using assms unfolding csts_conds_p_sat_def by auto

lemma CR_imp_all_ccps_p_joinable:
  fixes R :: "csts"
  assumes cr:"CR (csr_p_join_step R)"
  shows "all_ccps_p_joinable R"
  unfolding all_ccps_p_joinable_def
proof (intro allI impI)
  fix s t cond
  assume ccps:"((s, t), cond) \<in> csts_p_critical_pairs R" and cond_sat:"csts_conds_p_sat R cond"
  then obtain x y l r l' r' cs cs' where lr:"((l, r), cs) \<in> R" and l'r':"((l', r'), cs') \<in> R" and 
    cond_main:"((l @ y = x @ l' \<and> length x < length l \<and>
    s = r @ y \<and> t = x @ r' \<and> cond = cs' @ cs) \<or> (l = x @ l' @ y \<and> s = r  \<and> t = x @ r' @ y \<and> cond = cs @ cs'))"
    using csts_p_critical_pairs_elim[OF ccps] by blast
  from cond_sat[unfolded csts_conds_p_sat_def] 
  have *:"\<forall>(s, t) \<in> set cond. (s, t) \<in> (csr_p_join_step R)\<^sup>\<down>" by (auto split:prod.splits)
  hence condcs:"\<forall>(s, t) \<in> set cs. (s, t) \<in> (csr_p_join_step R)\<^sup>\<down>" using cond_sat cond_main 
    by auto
  have condcs':"\<forall>(s, t) \<in> set cs'. (s, t) \<in> (csr_p_join_step R)\<^sup>\<down>" using * cond_sat cond_main
    by auto
  show "(s, t) \<in> (csr_p_join_step R)\<^sup>\<down>" using lr l'r' cond_main
  proof(auto, goal_cases)
    case 1
    let ?C = "More x Hole []"
    let ?D = "More [] Hole y"
    have "(x @ l', x @ r') \<in> csr_p_join_step R" using l'r' csr_p_join_stepI[of l' r' cs' R ?C] condcs' by auto 
    moreover have "(l @ y, r @ y) \<in> csr_p_join_step R" using lr csr_p_join_stepI[of l r cs R ?D] condcs by auto
    moreover have "(x @ l', r @ y) \<in> csr_p_join_step R" using \<open>l @ y = x @ l'\<close>
      using calculation(2) by auto
    ultimately show ?case using cr[unfolded CR_on_def] by blast
  next
    case 2
    let ?C' = "More x Hole y"
    have "(x @ l' @ y, x @ r' @ y) \<in> csr_p_join_step R" using l'r' csr_p_join_stepI[of l' r' cs' R ?C'] condcs' by auto
    moreover have "(x @ l' @ y, r) \<in> csr_p_join_step R" using lr csr_p_join_stepI[of l r cs R] condcs \<open>l = x @ l' @ y\<close>
      by (metis sctxt.cop_nil)
    ultimately show ?case using cr[unfolded CR_on_def] by blast
  qed
qed

lemma app_csr_r_joinstep[simp]: assumes "(s, t) \<in> (csr_p_join_step R)\<^sup>\<down>"
  shows "(u @ s @ v, u @ t @ v) \<in> (csr_p_join_step R)\<^sup>\<down>"
proof -
  from assms obtain w where sw:"(s, w) \<in> (csr_p_join_step R)\<^sup>*" and tw:"(t, w) \<in> (csr_p_join_step R)\<^sup>*" by auto
  from sw tw have "(u @ s @ v, u @ w @ v) \<in> (csr_p_join_step R)\<^sup>*" and "(u @ t @ v, u @ w @ v) \<in> (csr_p_join_step R)\<^sup>*"
    using csr_p_join_step_ctxt_closed sctxt.closed_rtrancl sctxt_closed_strings by auto
  then show ?thesis by auto
qed

locale reductive_p_join = shortlex_total
begin

definition reductive :: "csts \<Rightarrow> bool"
  where
    "reductive R \<longleftrightarrow> (\<forall>((l, r),cs) \<in> R. l \<succ>\<^sub>s\<^sub>l r \<and> (\<forall>(u, v) \<in> set cs. l \<succ>\<^sub>s\<^sub>l u \<and> l \<succ>\<^sub>s\<^sub>l v))"

lemma sl_preserve_csr_p_step:assumes st:"(s, t) \<in> (csr_p_join_step R)"
  and rd:"reductive R"
shows "s \<succ>\<^sub>s\<^sub>l t"
proof -
  from st obtain n where "(s, t) \<in> (csr_p_join_step_n R (Suc n))"
    using csr_p_join_step_iff using csr_p_join_step_n_E by metis
  then obtain C l r cs where lr:"((l, r), cs) \<in> R"
    and "\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n)\<^sup>\<down>"
    and s:"s = C\<llangle>l\<rrangle>"
    and t:"t = C\<llangle>r\<rrangle>" using csr_p_join_step_n_SucE[of s t R n] by auto
  from rd[unfolded reductive_def] have lgr:"l \<succ>\<^sub>s\<^sub>l r" using lr by auto
  have "l \<succ>\<^sub>s\<^sub>l r" using sctxt_shortlex_closed_S_pre[of l r "[]"] using lgr by auto
  then show ?thesis using sctxt_shortlex_closed_S[of "l" "r" C] using s t 
    by fastforce
qed

lemma sl_preserve_csr_p_step_transitive: assumes st:"(s, t) \<in> (csr_p_join_step R)\<^sup>+"
  and rd:"reductive R"
shows "s \<succ>\<^sub>s\<^sub>l t" using st
proof(induct)
  case (base y)
  then show ?case 
    using sl_preserve_csr_p_step rd by blast
next
  case (step y z)
  from  sl_preserve_csr_p_step[of y z R]
  have "y \<succ>\<^sub>s\<^sub>l z" using rd step by auto
  then show ?case using step(3) shortlex_trans[of s y z] by fastforce
qed

lemma sl_preserve_csr_step_rtrans: assumes st:"s \<succ>\<^sub>s\<^sub>l t"
  and rd:"reductive R"
  and tu:"(t, u) \<in> (csr_p_join_step R)\<^sup>*"
shows "s \<succ>\<^sub>s\<^sub>l u" using tu
proof(induct)
  case base
  then show ?case using assms by auto
next
  case (step y z)
  then show ?case using assms shortlex_trans sl_preserve_csr_p_step 
    by metis
qed

definition csr_p_join_desc :: "string \<Rightarrow> csts \<Rightarrow> string set" where
  "csr_p_join_desc u R = {v. (u, v) \<in> (csr_p_join_step R)\<^sup>*}"

definition csr_p_join_desc_single :: "string \<Rightarrow> csts \<Rightarrow> string set" where
  "csr_p_join_desc_single u R = {v. (u, v) \<in> csr_p_join_step R}"

lemma finite_desc_pure: fixes R::csts and u::string
  assumes fnR: "finite R"
  shows "finite {v | l r cs v. u = l \<and> v = r \<and> ((l, r), cs) \<in> R}" using assms 
proof -
  have *:"finite {(l, r) | l r cs . ((l, r), cs) \<in> R}" using fnR
    by (smt (z3) Collect_cong Domain_unfold case_prodE case_prodI2 finite_Domain)
  moreover have "finite {l | l r cs . ((l, r), cs) \<in> R}" 
    using calculation finite_Domain by fastforce
  moreover have "finite {r | l r cs . ((l, r), cs) \<in> R}" using * 
    using calculation finite_Domain by fastforce
  ultimately show ?thesis
    by (metis (no_types, lifting) Collect_mono_iff rev_finite_subset)
qed

lemma finite_image_conc: assumes "finite A"
  and "finite B"
shows "finite {x @ y | x y. x \<in> A \<and> y \<in> B}" using assms 
  by (simp add: finite_image_set2)

lemma sublist_p_finite: fixes u::string and R::csts
  assumes fnR:"finite R"
  shows "finite {(x @ r @ y) | x y l r cs. u = x @ l @ y \<and> ((l, r), cs) \<in> R}" using assms
proof -
  have lr:"finite {(l, r) | x y l r cs v. u = x @ l @ y  \<and> ((l, r), cs) \<in> R}" using fnR
      finite_Domain Collect_mono_iff Domain_unfold finite_subset by (smt (z3))
  have l'r':"finite {(l, r) | l r cs. ((l, r), cs) \<in> R}" using fnR finite_Domain 
    by (smt (verit) Collect_cong Domain_unfold case_prodI2 case_prod_curry)
  have l':"finite {l |  l r cs . ((l, r), cs) \<in> R}" using  l'r'  finite_Domain by fastforce 
  hence r':"finite {r |  l r cs . ((l, r), cs) \<in> R}" using  l'r' l'  finite_Domain by fastforce 
  hence l:"finite {l | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R}" 
    using Collect_mono_iff finite_subset Collect_mono_iff Domain_unfold finite_subset l' by force
  have "{y | x y l r cs.  u = x @ l @ y \<and> ((l, r), cs) \<in> R} \<subseteq> set (subseqs u)" 
    by (auto, simp add: list_emb_append2)
  hence fnY:"finite {y | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R}"  (is "finite ?Y") 
    using infinite_super by blast
  have "{x | x y l r cs.  u = x @ l @ y \<and> ((l, r), cs) \<in> R} \<subseteq> set (subseqs u)" by auto
  hence fnX:"finite {x | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R}" (is "finite ?X") 
    using infinite_super by blast
  have r:"finite {r | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R}" (is "finite ?R")
    using Collect_mono_iff finite_subset Collect_mono_iff Domain_unfold finite_subset r' by (smt (verit, best))
  let ?C = "{x @ r | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R}"
  have "?X = {x | x . x \<in> ?X}" by force
  moreover have "?R = {x | x . x \<in> ?R}" by force
  ultimately have c:"?C \<subseteq> {x @ r | x r . x \<in> ?X \<and> r \<in> ?R }" using fnX r by blast
  have "finite {x @ r | x r . x \<in> ?X \<and> r \<in> ?R }" using finite_image_conc[of ?X ?R] c fnX r by auto 
  hence fnC:"finite ?C" using c by (meson finite_subset)
  let ?D = "{x @ r @ y | x y l r cs . u = x @ l @ y \<and> ((l, r), cs) \<in> R }"
  have d:"?D \<subseteq> {s @ s' | s s'. s \<in> ?C \<and> s' \<in> ?Y}"
    by (smt (verit) Collect_mono_iff append.assoc mem_Collect_eq)
  moreover have "finite {s @ s' | s s'. s \<in> ?C \<and> s' \<in> ?Y}" using finite_image_conc[of ?C ?Y] fnY fnC by blast
  ultimately show ?thesis using finite_subset by fastforce
qed

lemma sctxt_pred_to_string: fixes u::string
  shows "{v | C v l r cs. u = C\<llangle>l\<rrangle> \<and> v = C\<llangle>r\<rrangle> \<and> P l r cs} = {v | x y v l r cs.  u = x @ l @ y \<and> v = x @ r @ y \<and> P l r cs}" 
  by (auto, meson sctxt_app_step, metis ShortLex.more sctxt.cop_nil)

lemma finite_desc_sctxt_pre: fixes R::csts and u::string
  assumes fnR: "finite R"
  shows "finite {v | l r cs x y v. u = x @ l @ y \<and> v = x @ r @ y \<and> ((l, r), cs) \<in> R}" using assms
proof -
  have lr:"finite {(l, r) | x y l r cs v. u = x @ l @ y \<and> v = x @ r @ y \<and> ((l, r), cs) \<in> R}" using fnR
      finite_Domain by (smt (verit, ccfv_SIG) Collect_mono_iff Domain_unfold finite_subset)
  have l:"finite {l | x y l r cs v. u = x @ l @ y \<and> v = x @ r @ y \<and> ((l, r), cs) \<in> R}" 
    using lr finite_Domain  by (smt (verit, best) Collect_cong Domain_unfold mem_Collect_eq prod.inject)
  have l'r':"finite {(l, r) | l r cs. ((l, r), cs) \<in> R}" using fnR finite_Domain 
    by (smt (verit) Collect_cong Domain_unfold case_prodI2 case_prod_curry)
  have l':"finite {l |  l r cs . ((l, r), cs) \<in> R}" using  l'r'  finite_Domain by fastforce 
  hence r':"finite {r |  l r cs . ((l, r), cs) \<in> R}" using  l'r' l'  finite_Domain by fastforce 
  hence r:"finite {r | x y l r cs v. u = x @ l @ y \<and> ((l, r), cs) \<in> R}" 
    using Collect_mono_iff finite_subset by fastforce
  hence "finite {x @ r @ y | x y l r cs. u = x @ l @ y \<and> ((l, r), cs) \<in> R}" using  fnR sublist_p_finite[of R u]
    by auto
  then show ?thesis using lr l r 
    by (smt (verit, ccfv_threshold) Collect_cong)
qed

lemma finite_desc_sctxt: fixes R::csts and u::string
  assumes fnR: "finite R"
  shows "finite {v | C l r cs v. u = C\<llangle>l\<rrangle> \<and> v = C\<llangle>r\<rrangle> \<and> ((l, r), cs) \<in> R}" 
proof -
  let ?P = "\<lambda> l r cs. ((l, r), cs) \<in> R"
  show ?thesis using assms finite_desc_sctxt_pre[of R u] 
    sctxt_pred_to_string[of u ?P] by (auto, smt (verit, best) Collect_cong)
qed

lemma finite_descendants_csr_p_join_steps: fixes u::string and R::csts 
  assumes rd:"reductive R"
    and fn:"finite R"
  shows "finite (csr_p_join_desc u R)"
proof -
  have sn:"SN shortlex_S" using shortlex_SN by auto
  show ?thesis
  proof(induct rule: wf_induct[OF SN_imp_wf[OF sn], rule_format])
    case (1 u)
    let ?single_desc = "{v. (u, v) \<in> (csr_p_join_step R)}"
    have ord:"\<forall>d. d \<in> ?single_desc \<longrightarrow> u \<succ>\<^sub>s\<^sub>l d" using rd
      by (metis mem_Collect_eq sl_preserve_csr_p_step)
    have *:"\<forall>v. v \<in> ?single_desc \<longrightarrow> (\<exists>C l r cs. ((l, r), cs) \<in> R \<and> u = C\<llangle>l\<rrangle>)"
      by blast
    have fn_single:"finite (?single_desc)"
    proof -
      have sub:"?single_desc \<subseteq> {v | C l r cs v.  u = C\<llangle>l\<rrangle> \<and> v = C\<llangle>r\<rrangle> \<and> ((l, r), cs) \<in> R}" (is "?A \<subseteq> ?B") by blast
      have "finite {v | C l r cs v.  u = C\<llangle>l\<rrangle> \<and> v = C\<llangle>r\<rrangle> \<and> ((l, r), cs) \<in> R}" using finite_desc_sctxt[of R u] 
        using fn by fastforce
      then show ?thesis using sub by (meson finite_subset)
    qed
    have **:"csr_p_join_desc u R = {u} \<union> {w |v w. v \<in> ?single_desc \<and> (v, w) \<in> (csr_p_join_step R)\<^sup>*}" (is "_ = ?X \<union> ?Y")
      unfolding csr_p_join_desc_def by (auto, metis converse_rtranclE)
    have "finite ?X" by force
    moreover have "finite ?Y" using ord fn_single 
      by (auto, metis 1 case_prodI converse_iff csr_p_join_desc_def mem_Collect_eq rd sl_preserve_csr_p_step)
    ultimately show ?case using ** by simp
  qed
qed  

(* Lemma 30(ii) *)
lemma SN_and_finite_descendants_csr_p_join_steps: 
  assumes rd:"reductive R" and fn:"finite R" 
  shows "SN (csr_p_join_step R) \<and> finite (csr_p_join_desc u R)"
proof(rule conjI, goal_cases)
  case 1
  then show ?case using assms[unfolded reductive_def] case_prodI shortlex_SN sl_preserve_csr_p_step 
    unfolding CollectI SN_on_def by (auto split:prod.splits, insert rd, metis CollectI UNIV_I sl_preserve_csr_p_step)
next
  case 2
  then show ?case using finite_descendants_csr_p_join_steps[OF rd fn] by auto
qed

end

context reductive_p_join
begin

lemma disjoint_imp_CR:
  fixes R :: "csts"
  assumes rd:"reductive R"
    and s1:"s = bef @ l @ aft" 
    and s2:"s = bef' @ l' @ aft'"
    and t':"t' = bef @ r @ aft" 
    and u':"u' = bef' @ r' @ aft'"
    and len:"length bef' \<ge> length (bef @ l)"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
    cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
    cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R m')\<^sup>\<down>"   
  shows "(t', u') \<in> (csr_p_join_step R)\<^sup>\<down>"
proof -
  from len s1 s2 obtain some where s_new:"s = bef @ l @ some @ l' @ aft'" 
    by (auto, metis append_eq_appendI append_eq_append_conv_if)
  hence t_new:"t' = bef @ r @ some @ l' @ aft'" using t' s_new s1 by fastforce
  from s_new u' have u:"u' = bef @ l @ some @ r' @ aft'" using s2 by auto
  let ?join ="bef @ r @ some @ r' @ aft'"
  have *:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>" 
    using cond1 csr_p_join_step_iff 
    by (auto split:prod.splits, metis csr_p_join_steps_n_imp_csteps joinD joinI)
  have **:"\<forall>(s\<^sub>i, t\<^sub>i)\<in>set cs'. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step R)\<^sup>\<down>" using cond2 csr_p_join_step_iff
    by (auto split:prod.splits, metis csr_p_join_steps_n_imp_csteps joinD joinI)
  let ?C = "More (bef @ r @ some) Hole aft'"
  let ?D = "More bef Hole (some @ r' @ aft')" 
  have "(t', ?join) \<in> csr_p_join_step R" using l'r' t_new ** csr_p_join_stepI[of l' r' cs' R ?C]
    by (auto split:prod.splits) 
  moreover have "(u', ?join) \<in> csr_p_join_step R" using * lr u csr_p_join_stepI[of l r cs R ?D]  
    by (auto split:prod.splits)
  ultimately show ?thesis by blast
qed  

lemma critical_overlap_p_type1_imp_CR:
  fixes R :: "csts"
  assumes acj:"all_ccps_p_joinable R"
    and s1m:"s = mbef @ pbef @ l @ paft @ maft"
    and s2m:"s = mbef @ pbef' @ l' @ paft' @ maft"
    and t':"t = bef @ r @ aft"
    and u':"u = bef' @ r' @ aft'"
    and pbe:"pbef = [] \<or> pbef' = []"
    and pae:"paft = [] \<or> paft' = []"
    and pbef:"mbef @ pbef = bef"
    and pbef':"mbef @ pbef' = bef'"
    and paft:"paft @ maft = aft"
    and paft':"paft' @ maft = aft'"
    and len:"length pbef' \<le> length pbef \<and> length (pbef @ l) \<le> length (pbef' @ l')"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
    cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
    cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R m')\<^sup>\<down>"
  shows "(t, u) \<in> (csr_p_join_step R)\<^sup>\<down>" 
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
  hence t'_new:"t = mbef @ pbef' @ l1 @ r @ l2 @ paft' @ maft" using paft lpm mpl pbef t' by fastforce
  have u'_new:"u = mbef @ pbef' @ r' @ paft' @ maft" using u'
    by (metis append_assoc paft' pbef')
  have "((r', l1 @ r @ l2), cs' @ cs) \<in> csts_p_critical_pairs R" 
    unfolding csts_p_critical_pairs_def using lr l'r' l' by auto
  moreover have "csts_conds_p_sat R cs'" unfolding csts_conds_p_sat_def
    by (auto, metis case_prod_conv cond2 csr_p_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_p_sat R cs" using cond1 unfolding csts_conds_p_sat_def
    by (auto split:prod.splits, metis csr_p_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_p_sat R (cs' @ cs)" unfolding csts_conds_p_sat_def 
    using calculation csts_conds_p_sat_def by auto
  ultimately have "(r', l1 @ r @ l2) \<in> (csr_p_join_step R)\<^sup>\<down>" using acj[unfolded all_ccps_p_joinable_def]
    by auto
  then obtain join1 where j1:"(l1 @ r @ l2, join1) \<in> (csr_p_join_step R)\<^sup>*" and j2:"(r', join1) \<in> (csr_p_join_step R)\<^sup>*"
    by auto
  have "(mbef @ pbef' @ l1 @ r @ l2 @ paft' @ maft, mbef @ pbef' @ join1 @ paft' @ maft ) \<in> (csr_p_join_step R)\<^sup>*"
    using j1 csr_join_sctxt_closed[of "l1 @ r @ l2" "join1" R "mbef @ pbef'" "paft' @ maft" ] by auto
  moreover have "(mbef @ pbef' @ r' @ paft' @ maft, mbef @ pbef' @ join1 @ paft' @ maft) \<in> (csr_p_join_step R)\<^sup>*"
    using j2 csr_join_sctxt_closed[of "mbef @ pbef' @ r' @ paft' @ maft" "join1" R "mbef @ pbef'" "paft' @ maft"] 
    by (metis append_self_conv csr_join_sctxt_closed)
  ultimately show ?thesis using t'_new u'_new by auto
qed

lemma critical_overlap_p_type2_imp_CR:
  fixes R :: "csts"
  assumes acj:"all_ccps_p_joinable R"
    and s1m:"s = mbef @ pbef @ l @ paft @ maft"
    and s2m:"s = mbef @ pbef' @ l' @ paft' @ maft"
    and t':"t = bef @ r @ aft"
    and u':"u = bef' @ r' @ aft'"
    and pbe:"pbef = [] \<or> pbef' = []"
    and pae:"paft = [] \<or> paft' = []"
    and pbef:"mbef @ pbef = bef"
    and pbef':"mbef @ pbef' = bef'"
    and paft:"paft @ maft = aft"
    and paft':"paft' @ maft = aft'"
    and len_overlap:"(length (bef @ l) > length bef' \<and> length (bef' @ l') > length bef)"
    and len:"length pbef' < length pbef \<and> length (pbef' @ l') < length (pbef @ l)"
    and lr:"((l, r), cs) \<in> R" and "n = Suc n'" and 
    cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n')\<^sup>\<down>"
    and l'r':"((l', r'), cs') \<in> R" and "m = Suc m'" and 
    cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R m')\<^sup>\<down>"
  shows "(t, u) \<in> (csr_p_join_step R)\<^sup>\<down>"
proof -
  obtain u' where u:"pbef = pbef' @ u'" using len using pbe by fastforce
  have "prefix (mbef @ pbef @ l) s" using s1m by (metis append.assoc prefixI)
  moreover have "prefix (mbef @ pbef' @ l') s" using s2m by (metis append.assoc prefixI)
  moreover have "length (mbef @ pbef @ l) >  length (mbef @ pbef' @ l')" using len by auto
  ultimately have "strict_prefix (mbef @ pbef' @ l') (mbef @ pbef @ l)" using s1m s2m 
    by (metis (mono_tags, lifting) less_or_eq_imp_le nat_neq_iff prefix_length_prefix prefix_order.less_le) 
  then obtain v where v:"mbef @ pbef @ l = mbef @ pbef' @ l' @ v"  
    by (metis Nil_is_append_conv u pbe prefix_def prefix_order.less_le same_prefix_prefix)
  have nue:"u' \<noteq> []" and nve:"v \<noteq> []" using len u v by auto
  let ?pbef = "take (length pbef - length u') pbef"
  let ?paft'= "drop (length v) paft'"
  have ueq:"?pbef @ u' = pbef" using u by auto
  hence peq:"?pbef = pbef'" using s1m s2m u by auto
  have veq:"paft' @ maft = v @ ?paft' @ maft" using s2m v nve 
    by (smt (verit, del_insts) append.assoc append_eq_conv_conj append_same_eq length_append pae s1m same_append_eq)
  hence pmeq:"paft @ maft = ?paft' @ maft" using s1m s2m u v nve 
    by (smt (verit) append.assoc append_same_eq same_append_eq)
  have s1_new:"s = mbef @ pbef' @ u' @ l @ paft @ maft" using u s1m s2m by auto
  have s2_new:"s = mbef @ pbef' @ l' @ v @ paft @ maft" using v s1m s2m veq pmeq by argo
  have t_new:"t = mbef @ pbef' @ u' @ r @ paft @ maft" using t' ueq 
    by (simp add: paft pbef peq)
  have u_new:"u = mbef @ pbef' @ r' @ v @ ?paft' @ maft" using v s1m s2m veq
    by (metis append.assoc paft' pbef' u')
  have "length u' < length l'" using u len_overlap pbe pbef pbef' by fastforce
  hence "((r' @ v, u' @ r), cs @ cs') \<in> csts_p_critical_pairs R" 
    unfolding csts_p_critical_pairs_def using lr l'r' u v by fastforce
  moreover have "csts_conds_p_sat R cs'" unfolding csts_conds_p_sat_def
    by (auto, metis case_prod_conv cond2 csr_p_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_p_sat R cs" using cond1 unfolding csts_conds_p_sat_def
    by (auto split:prod.splits, metis csr_p_join_steps_n_imp_csteps joinD joinI)
  moreover have "csts_conds_p_sat R (cs @ cs')" using csts_conds_p_sat_def calculation(2) calculation(3)
    by auto
  ultimately have "(r' @ v, u' @ r) \<in> (csr_p_join_step R)\<^sup>\<down>" using acj[unfolded all_ccps_p_joinable_def]
    by auto
  then obtain join1 where j1:"(r' @ v, join1) \<in> (csr_p_join_step R)\<^sup>*" and j2:"(u' @ r, join1) \<in> (csr_p_join_step R)\<^sup>*"
    by auto
  have "(mbef @ pbef' @ r' @ v @ paft @ maft, mbef @ pbef' @ join1 @ paft @ maft) \<in> (csr_p_join_step R)\<^sup>*"
    using j1 csr_join_sctxt_closed[of "r' @ v" "join1" R "mbef @ pbef'" "paft @ maft"] by auto 
  moreover have "(mbef @ ?pbef @ u' @ r @ paft @ maft, mbef @ pbef' @ join1 @ paft @ maft) \<in> (csr_p_join_step R)\<^sup>*"
    using j2 peq csr_join_sctxt_closed[of "u' @ r" "join1" R "mbef @ ?pbef" "paft @ maft"] by auto
  ultimately show ?thesis using t_new u_new peq pmeq by auto
qed


lemma all_ccps_p_joinable_imp_WCR:
  fixes R :: "csts"
  assumes acj:"all_ccps_p_joinable R"
    and rd:"reductive R"
  shows "WCR (csr_p_join_step R)"
proof -
  {
    fix s t u
    assume st:"(s, t) \<in> csr_p_join_step R" and su:"(s, u) \<in> csr_p_join_step R"
    have sn: "SN shortlex_S" using shortlex_SN by blast
    from st su have "(t, u) \<in> (csr_p_join_step R)\<^sup>\<down>"
    proof(induct s arbitrary: t u rule: wf_induct[OF SN_imp_wf[OF sn], rule_format])
      case (1 s)
      note IH = this(1)
      from st obtain n where st:"(s, t) \<in> csr_p_join_step_n R n" using csr_p_join_step_iff 1 by auto
      from su obtain m where su:"(s, u) \<in> csr_p_join_step_n R m" using csr_p_join_step_iff 1 by auto
      from csr_p_join_step_n_E[OF st]
      obtain C l r cs n' where lr:"((l, r), cs) \<in> R" and nn':"n = Suc n'" and 
        cond1:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R n')\<^sup>\<down>" and
        sC:"s = C\<llangle>l\<rrangle>" and tC:"t = C\<llangle>r\<rrangle>" by metis
      from csr_p_join_step_n_E[OF su]
      obtain D l' r' cs' m' where l'r':"((l', r'), cs') \<in> R" and mm':"m = Suc m'" and 
        cond2:"\<forall>(s\<^sub>i, t\<^sub>i) \<in> set cs'. (s\<^sub>i, t\<^sub>i) \<in> (csr_p_join_step_n R m')\<^sup>\<down>" and
        sD:"s = D\<llangle>l'\<rrangle>" and uD:"u = D\<llangle>r'\<rrangle>" by metis
      from sC tC obtain bef aft where s1:"s = bef @ l @ aft" and t:"t = bef @ r @ aft" 
        by (auto, metis sctxt_app_step)
      from sD uD obtain bef' aft' where s2:"s = bef' @ l' @ aft'" and u:"u = bef' @ r' @ aft'" 
        by (auto, metis sctxt_app_step)
      then show ?case
      proof (cases "length bef' \<ge> length (bef @ l) \<or> length bef \<ge> length (bef' @ l')")
        case True
        then show ?thesis
        proof
          assume asm:"length bef' \<ge> length (bef @ l)"
          note disjoint_imp_CR = disjoint_imp_CR[of R s bef l aft bef' l' aft' t r u r' cs n n' cs' m m'] 
          then show ?thesis using disjoint_imp_CR rd s1 s2 t u asm lr l'r' nn' mm' cond1 cond2 
            by fastforce
        next
          assume asm:"length bef \<ge> length (bef' @ l')"
          note disjoint_imp_CR' = disjoint_imp_CR[of R s bef' l' aft' bef l aft u r' t r cs' m m' cs n n'] 
          then show ?thesis using disjoint_imp_CR' rd s1 s2 t u asm lr l'r' nn' mm' cond1 cond2 
            by blast
        qed
      next
        case False
        hence *:"(length (bef @ l) > length bef' \<and> length (bef' @ l') > length bef)" by auto
        let ?mbef_size = "min (length bef) (length bef')"
        let ?maft_size = "min (length aft) (length aft')"
        let ?mbef = "take ?mbef_size s"
        let ?maft = "drop (length s - ?maft_size) s"
        have pr1:"prefix ?mbef bef" by (simp add: s1 take_is_prefix)
        have pr2:"prefix ?mbef bef'" by (simp add: s2 take_is_prefix)
        have len1:"length aft \<ge> length ?maft" by auto
        hence su1:"suffix ?maft aft" using s1 suffixI suffix_appendD suffix_drop 
          by (auto, smt (verit, ccfv_SIG) add.commute diff_cancel2 diff_diff_left drop_append suffix_drop)
        have len2:"length aft' \<ge> length ?maft" by auto
        have su2:"suffix ?maft aft'"using s2 suffixI suffix_appendD suffix_drop 
          by (auto, smt (verit, ccfv_SIG) add.commute diff_cancel2 diff_diff_left drop_append suffix_drop)
        from pr1 obtain pbef where pbef:"?mbef @ pbef = bef" by (metis prefixE)
        from pr2 obtain pbef' where pbef':"?mbef @ pbef' = bef'" by (metis prefixE)
        from su1 obtain paft where paft:"paft @ ?maft = aft" by (metis suffixE)
        from su2 obtain paft' where paft':"paft' @ ?maft = aft'" by (metis suffixE)
        have s1m:"s = ?mbef @ pbef @ l @ paft @ ?maft" using s1 pbef paft by auto
        have s2m:"s = ?mbef @ pbef' @ l' @ paft' @ ?maft" using s2 pbef' paft' by auto
        have pbe:"pbef = [] \<or> pbef' = []" using s1 s2 s1m s2m 
          by (metis append_eq_conv_conj min_def pbef pbef' self_append_conv)
        have pae:"paft = [] \<or> paft' = []" using s1 s2 s1m s2m  paft paft' 
          by (auto, smt (verit, del_insts) append.assoc append_eq_append_conv diff_diff_cancel length_drop min.cobounded1 min_def self_append_conv)
        then show ?thesis
        proof(cases "(length pbef \<ge> length pbef' \<and> length (pbef' @ l') \<ge> length (pbef @ l)) \<or> 
            (length pbef' \<ge> length pbef \<and> length (pbef @ l) \<ge> length (pbef' @ l'))")
          case True
          then show ?thesis
          proof
            assume asm:"length pbef \<ge> length pbef' \<and> length (pbef' @ l') \<ge> length (pbef @ l)"
            note critical_overlap_p_type1_imp_CR = critical_overlap_p_type1_imp_CR[of R s ?mbef pbef 
                l paft ?maft pbef' l' paft' t bef r aft u bef' r' aft' cs n n' cs' m m']
            show ?thesis using critical_overlap_p_type1_imp_CR asm acj cond1 cond2 
                critical_overlap_p_type1_imp_CR l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                s1m s2m t u by fastforce
          next
            assume asm:"length pbef' \<ge> length pbef \<and> length (pbef @ l) \<ge> length (pbef' @ l')"
            note critical_overlap_p_type1_imp_CR' = critical_overlap_p_type1_imp_CR[of R s ?mbef pbef' 
                l' paft' ?maft pbef l paft u bef' r' aft' t bef r aft cs' m m' cs n n']
            show ?thesis using critical_overlap_p_type1_imp_CR' asm acj asm cond1 cond2 
                critical_overlap_p_type1_imp_CR' l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                s1m s2m t u by blast
          qed
        next
          case False
          hence "(length pbef > length pbef' \<and> length (pbef @ l) > length (pbef' @ l') \<or>
                length pbef' > length pbef \<and> length (pbef' @ l') > length (pbef @ l))" (is "?A \<or> ?B") by auto
          then show ?thesis
          proof
            assume asm:"?A"
            note critical_overlap_p_type2_imp_CR = critical_overlap_p_type2_imp_CR[of R s ?mbef pbef l paft ?maft
                pbef' l' paft' t bef r  aft u bef' r' aft' cs n n' cs' m m' ]
            show ?thesis using asm critical_overlap_p_type2_imp_CR 
              using * acj asm cond1 cond2 critical_overlap_p_type2_imp_CR l'r' lr mm' nn' pae paft 
                paft' pbe pbef pbef' s1m s2m t u by auto
          next
            assume asm:"?B"
            note critical_overlap_p_type2_imp_CR' = critical_overlap_p_type2_imp_CR[of R s ?mbef pbef' l' paft' ?maft
                pbef l paft u bef' r' aft' t bef r aft cs' m m' cs n n']
            show ?thesis using asm critical_overlap_p_type2_imp_CR' using * acj asm cond1 
                cond2 critical_overlap_p_type2_imp_CR' l'r' lr mm' nn' pae paft paft' pbe pbef pbef' 
                s1m s2m t u by auto
          qed
        qed
      qed
    qed
  } then show ?thesis unfolding WCR_on_def by auto
qed

lemma all_ccps_p_joinable_imp_CR:
  assumes acj:"all_ccps_p_joinable R"
    and rd:"reductive R"
    and fn:"finite R"
  shows "CR (csr_p_join_step R)" using assms all_ccps_p_joinable_imp_WCR
  by (simp add: Newman SN_and_finite_descendants_csr_p_join_steps)

(* Lemma 33 *)
lemma csts_p_critical_pair_lemma:
  assumes rd:"reductive R"
    and fn:"finite R"
  shows "CR (csr_p_join_step R) \<longleftrightarrow> all_ccps_p_joinable R"
proof 
  assume cr:"CR (csr_p_join_step R)"
  then show "all_ccps_p_joinable R" using CR_imp_all_ccps_p_joinable[of R] by auto
next
  assume "all_ccps_p_joinable R"
  then show "CR (csr_p_join_step R)" using all_ccps_p_joinable_imp_CR[of R] assms 
    using shortlex_SN by blast
qed

end

end
