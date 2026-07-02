(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Non_Confluence
imports 
  Usable_Rules_NJ
  Sem_Lab.Semantic_Labeling
  Ord.Argument_Filter
  Auxx.Name
  LS_Modularity
begin

lemma modularity_of_non_confluence: fixes R :: "('f,'v)trs" 
  assumes nCR: "\<not> CR (rstep R)"
  and wfR: "\<And> l r. (l,r) \<in> R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and wfS: "\<And> l r. (l,r) \<in> S \<Longrightarrow> is_Fun l"
  and disj: "funas_trs R \<inter> funas_trs S = {}"
  and fin: "finite (funas_trs R \<union> funas_trs S)"
  and inf: "infinite (UNIV :: 'f set)"
  shows "\<not> CR (rstep (R \<union> S))"
proof -
  define F where "F = funas_trs R"
  define G where "G = funas_trs S"
  from F_def have R: "funas_trs R \<subseteq> F" by auto
  from G_def have S: "funas_trs S \<subseteq> G" by auto
  from nCR obtain s t u where stR: "(s,t) \<in> (rstep R)^*" and suR: "(s,u) \<in> (rstep R)^*"
    and tu: "(t,u) \<notin> join (rstep R)" unfolding CR_on_def by blast
  define H where "H = funas_term s - F"
  have "finite (fst ` (F \<union> G \<union> H))" unfolding H_def F_def G_def using finite_funas_term[of s] fin by auto
  from finite_fresh_names_infinite_univ[OF this inf] obtain f g where fg: "\<And> x. x \<in> fst ` (F \<union> G \<union> H) \<Longrightarrow>
    f x \<notin> fst ` (F \<union> G \<union> H) \<and> g (f x) = x" by blast
  define ren where "ren = (\<lambda> (h,n). if (h,n) \<in> F then h else f h)"
  define H' where "H' = (\<lambda>(h, y). (f h, y)) ` H"
  let ?m = "map_funs_term_wa ren"
  have id: "\<And> g n. (g,n) \<in> F \<Longrightarrow> ren (g,n) = g"
    unfolding ren_def by force
  have mR: "map_funs_trs_wa ren R = R"
    by (rule map_funs_trs_wa_funas_trs_id[OF R id])
  from map_funs_trs_wa_rsteps[OF stR, of ren] map_funs_trs_wa_rsteps[OF suR, of ren]
  have st: "(?m s, ?m t) \<in> (rstep R)^*" and su: "(?m s, ?m u) \<in> (rstep R)^*" unfolding mR .
  have sFH: "funas_term s \<subseteq> F \<union> H" unfolding H_def by blast
  then have "funas_term (?m s) \<subseteq> (\<lambda>(f, y). (ren (f,y), y)) ` (F \<union> H)" unfolding funas_term_map_funs_term_wa by blast
  also have "\<dots> = F \<union> ((\<lambda>(f, y). (ren (f,y), y)) ` H)" using id by force
  also have "\<dots> \<subseteq> F \<union> H'" unfolding H'_def ren_def by force
  finally have fs: "funas_term (?m s) \<subseteq> F \<union> H'" by auto
  from R have RH: "funas_trs R \<subseteq> F \<union> H'" by auto
  from rsteps_preserve_funas_terms_var_cond[OF RH fs st wfR] have ft: "funas_term (?m t) \<subseteq> F \<union> H'" .
  from rsteps_preserve_funas_terms_var_cond[OF RH fs su wfR] have fu: "funas_term (?m u) \<subseteq> F \<union> H'" .
  from su have su: "(?m s, ?m u) \<in> (rstep (R \<union> S))^*" unfolding rstep_union by regexp
  from st have st: "(?m s, ?m t) \<in> (rstep (R \<union> S))^*" unfolding rstep_union by regexp
  {
    fix v
    assume tv: "(?m t, v) \<in> (rstep (R \<union> S))^*" and uv: "(?m u, v) \<in> (rstep (R \<union> S))^*"
    {
      fix t
      have "(t,v) \<in> (rstep (R \<union> S))^* \<Longrightarrow> funas_term t \<subseteq> F \<union> H' \<Longrightarrow> (t,v) \<in> (rstep R)^*"
      proof (induct rule: rtrancl_induct)
        case (step u v)
        from rsteps_preserve_funas_terms_var_cond[OF RH step(4) step(3)[OF step(4)] wfR]
        have fu: "funas_term u \<subseteq> F \<union> H'" by auto
        from step(2)[unfolded rstep_union] have "(u,v) \<in> rstep R"
        proof
          assume "(u,v) \<in> (rstep S)"
          then obtain C l r \<sigma> where lr: "(l,r) \<in> S" and u: "u = C \<langle> l \<cdot> \<sigma> \<rangle>" by auto
          from wfS[OF lr] obtain h ls where l: "l = Fun h ls" by (cases l, auto)
          let ?h = "(h,length ls)"
          from l lr S have hG: "?h \<in> G" unfolding funas_trs_def by (force simp: funas_rule_def)
          from fu[unfolded u l] have "?h \<in> F \<union> H'" by auto
          with disj hG have "?h \<in> H'" unfolding F_def G_def by auto
          from this[unfolded H'_def] obtain h' where h': "(h',length ls) \<in> H" and h: "h = f h'" by auto
          then have hfst: "h' \<in> fst ` (F \<union> G \<union> H)" by force
          from fg[OF hfst, folded h] hG have False by force
          then show ?thesis ..
        qed
        with step(3)[OF step(4)] show ?case by auto
      qed simp
    } note disjoint = this
    from disjoint[OF tv ft] have tv: "(?m t, v) \<in> (rstep R)^*" .
    from disjoint[OF uv fu] have uv: "(?m u, v) \<in> (rstep R)^*" .
    define ren' where "ren' = (\<lambda> (h,n). if (h,n) \<in> F then h else g h)"
    let ?m' = "map_funs_term_wa ren'"
    have id: "\<And> g n. (g,n) \<in> F \<Longrightarrow> ren' (g,n) = g"
      unfolding ren'_def by force
    have mR: "map_funs_trs_wa ren' R = R"
      by (rule map_funs_trs_wa_funas_trs_id[OF R id])
    have RH: "funas_trs R \<subseteq> F \<union> H" using R by auto
    {
      fix t
      assume t: "funas_term t \<subseteq> F \<union> H"
      have "?m' (?m t) = t"
        unfolding map_funs_term_wa_compose
      proof (rule map_funs_term_wa_funas_term_id[OF subset_refl], unfold split)
        fix h n
        assume "(h,n) \<in> funas_term t"
        then have "(h,n) \<in> F \<union> (H - F)" using t by auto
        then show "ren' (ren (h, n), n) = h"
        proof
          assume "(h,n) \<in> F"
          then show ?thesis unfolding ren_def ren'_def by auto
        next
          assume h: "(h,n) \<in> H - F"
          then have ren: "ren (h,n) = f h" unfolding ren_def by auto
          from h have "h \<in> fst ` (F \<union> G \<union> H)" by force
          from fg[OF this] have "(f h,n) \<notin> F" "g (f h) = h" by force+
          then show ?thesis unfolding ren ren'_def by auto
        qed
      qed
    }
    note map_map = this[OF rsteps_preserve_funas_terms_var_cond[OF RH sFH _ wfR]]
    from map_funs_trs_wa_rsteps[OF tv, of ren'] map_funs_trs_wa_rsteps[OF uv, of ren']
    have tv: "(t, ?m' v) \<in> (rstep R)^*" and uv: "(u, ?m' v) \<in> (rstep R)^*" unfolding mR 
      using map_map[OF stR] map_map[OF suR] by auto
    from tv uv tu have False by auto
  }
  then have "(?m t, ?m u) \<notin> join (rstep (R \<union> S))" by auto
  with st su show ?thesis by auto
qed


definition rules_lhs_restrict_sig :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs" where
  "rules_lhs_restrict_sig R S = { lr \<in> R. funas_term (fst lr) \<subseteq> funas_trs S }" 

context
  fixes R S :: "('f,'v :: infinite)trs" 
  assumes SR: "S \<subseteq> R" 
    and restr: "rules_lhs_restrict_sig R S \<subseteq> (rstep S)^*" 
    and wf_S: "wf_trs S" 
begin

lemma hirokowa_shintani_iwc_2024_lemma_1: 
  "(s,t) \<in> rstep R \<Longrightarrow> funas_term s \<subseteq> funas_trs S \<Longrightarrow> (s,t) \<in> (rstep S)^* \<and> funas_term t \<subseteq> funas_trs S" 
  "(s,t) \<in> (rstep R)^* \<Longrightarrow> funas_term s \<subseteq> funas_trs S \<Longrightarrow> (s,t) \<in> (rstep S)^*" 
proof -
  {
    fix s t
    assume st: "(s,t) \<in> rstep R" and sS: "funas_term s \<subseteq> funas_trs S" 
    from st obtain l r C \<sigma> where s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" and lr: "(l,r) \<in> R" by auto
    from sS have "funas_term l \<subseteq> funas_trs S" unfolding s by (simp add: funas_term_subst)
    with lr restr have "(l,r) \<in> (rstep S)^*" unfolding rules_lhs_restrict_sig_def by force
    hence st: "(s, t) \<in> (rstep S)^*" unfolding s t
      using rstep_rtrancl_idemp by blast
    with sS wf_S have "funas_term t \<subseteq> funas_trs S"
      by (meson order_eq_refl rsteps_preserve_funas_terms)
    with st show "(s,t) \<in> (rstep S)^* \<and> funas_term t \<subseteq> funas_trs S" by blast
  } note 1 = this
  assume "(s,t) \<in> (rstep R)^*" 
  hence "funas_term s \<subseteq> funas_trs S \<Longrightarrow> (s,t) \<in> (rstep S)^* \<and> funas_term t \<subseteq> funas_trs S" 
  proof (induct s t)
    case *: (rtrancl_into_rtrancl s t u)
    from 1[OF *(3)] *(2)[OF *(4)]
    show ?case by auto
  qed auto
  thus "funas_term s \<subseteq> funas_trs S \<Longrightarrow> (s,t) \<in> (rstep S)^*" by auto
qed

lemma hirokowa_shintani_iwc_2024_prop_4: "CR (rstep S) \<longleftrightarrow> 
  (\<forall> s t u. funas_term s \<union> funas_term t \<union> funas_term u \<subseteq> funas_trs S \<longrightarrow> (s,t) \<in> (rstep S)^* \<longrightarrow> (s,u) \<in> (rstep S)^* \<longrightarrow>
    (t,u) \<in> join (rstep S))" (is "_ = ?cond")
proof
  assume "CR (rstep S)" 
  thus ?cond by auto
next
  assume *: ?cond
  show "CR (rstep S)"
  proof (intro CR_on_imp_CR[OF wf_S subset_refl], intro CR_onI, goal_cases)
    case (1 s t u)
    hence "funas_term s \<union> funas_term t \<union> funas_term u \<subseteq> funas_trs S" using wf_S
      by (metis mem_Collect_eq rsteps_preserve_funas_terms set_eq_subset sup_least)
    from *[rule_format, OF this] 1 show ?case by auto
  qed
qed
  

lemma hirokowa_shintani_iwc_2024_theorem_5:
  assumes "CR (rstep R)" 
  shows "CR (rstep S)" 
  unfolding hirokowa_shintani_iwc_2024_prop_4
proof (intro allI impI, goal_cases)
  case (1 s t u)
  with SR have "(s,t) \<in> (rstep R)^*" "(s,u) \<in> (rstep R)^*" using rtrancl_mono[OF rstep_mono] by auto
  with assms have "(t,u) \<in> join (rstep R)" by auto
  then obtain w where "(t,w) \<in> (rstep R)^*" and "(u,w) \<in> (rstep R)^*" by auto
  from 1 hirokowa_shintani_iwc_2024_lemma_1(2)[OF this(1)] hirokowa_shintani_iwc_2024_lemma_1(2)[OF this(2)]
  have "(t, w) \<in> (rstep S)\<^sup>*" "(u, w) \<in> (rstep S)\<^sup>*" by auto
  thus "(t, u) \<in> join (rstep S)" by auto
qed
end
      

text \<open>Formalization of some techniques Aoto's FroCoS'13 paper\<close>

lemma eval_lab_eval[simp]: "fst (Semantic_Labeling.eval_lab I L LC \<alpha> t) = I\<lbrakk>t\<rbrakk>\<alpha>"
proof (induct t)
  case (Fun f ss)
  then have [simp]: "map (fst \<circ> eval_lab I L LC \<alpha>) ss = map (\<lambda> t. I\<lbrakk>t\<rbrakk>\<alpha>) ss" by auto
  show ?case by (simp add: Let_def)
qed simp

lemma wf_eval: assumes I: "wf_inter I C" and ass: "wf_assign C \<alpha>"
  shows "I\<lbrakk>t\<rbrakk>\<alpha> \<in> C"
proof (induct t)
  case (Var x)
  with ass show ?case unfolding wf_assign_def by auto
next
  case (Fun f ts)
  note I = I[unfolded wf_inter_def, rule_format]
  show ?case unfolding eval_term.simps
    by (rule I, insert Fun, auto)
qed

abbreviation qmodel_rule where "qmodel_rule I C cge l r \<equiv> \<forall> \<alpha>. wf_assign C \<alpha> \<longrightarrow> cge (I\<lbrakk>l\<rbrakk>\<alpha>) (I\<lbrakk>r\<rbrakk>\<alpha>)"
definition qmodel where "qmodel I C cge R \<equiv> \<forall> (l,r) \<in> R. qmodel_rule I C cge l r"

lemma qmodel_model[simp]: "Semantic_Labeling.qmodel I L LC C cge R = qmodel I C cge R"
  unfolding Semantic_Labeling.qmodel_def qmodel_def by auto

lemma sl_interpr: "c \<in> C \<Longrightarrow> wf_inter I C \<Longrightarrow> cge_wm I C cge \<Longrightarrow> 
  sl_interpr C c I cge (\<lambda> _ _. (=)) (\<lambda> _ _. ()) (\<lambda> x y z. (x,z)) id (\<lambda> _ _ _. True)"
  by (unfold_locales, auto simp: lge_wm lge_to_lgr_rel_def lge_to_lgr_def Let_def wf_label_def)

lemma sem_rewrites: fixes R' :: "('f,'v)trs"
  assumes steps: "(s,t) \<in> (rstep U)^*"
  and U: "U \<subseteq> R'"
  and wf_ass: "wf_assign C (\<alpha> :: ('v,'c)assign)"
  and c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and wm: "cge_wm I C cge"
  and model: "qmodel I C cge R'"
  and refl: "\<And> c. c \<in> C \<Longrightarrow> cge c c"
  and trans: "\<And> c d e. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> e \<in> C \<Longrightarrow> cge c d \<Longrightarrow> cge d e \<Longrightarrow> cge c e"
  shows "cge (I\<lbrakk>s\<rbrakk>\<alpha>) (I\<lbrakk>t\<rbrakk>\<alpha>)"
proof -
  interpret sl_interpr C c I cge "\<lambda> _ _. (=)" "\<lambda> _ _. ()" "(\<lambda> x y z. (x,z))" id "\<lambda> _ _ _. True"
    by (rule sl_interpr[OF c wf_I wm])
  have "Semantic_Labeling.qmodel I (\<lambda>_ _. ()) (\<lambda>x y. Pair x) C cge R'" using model by simp
  from quasi_sem_rewrite[OF _ this wf_ass, unfolded eval_lab_eval, of _ _ False "{}"] rstep_mono[OF U]
  have eval: "\<And> s t. (s,t) \<in> rstep U \<Longrightarrow> cge (I\<lbrakk>s\<rbrakk>\<alpha>) (I\<lbrakk>t\<rbrakk>\<alpha>)" by auto
  note wf = wf_eval[OF wf_I wf_ass]
  from steps
  show ?thesis
  proof (induct)
    case (step t u)
    show ?case 
      by (rule trans[OF wf wf wf step(3) eval[OF step(2)]])
  next
    case base
    show ?case by (rule refl[OF wf])
  qed
qed

abbreviation cgt where "cgt cge a b \<equiv> cge a b \<and> \<not> cge b a"

lemma aoto_theorem_2: (* we weakened > to not \<le> *)
  assumes model: "qmodel I C cge (Rs^-1 \<union> Rt)"
  and c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and wm: "cge_wm I C cge"
  and refl: "\<And> c. c \<in> C \<Longrightarrow> cge c c"
  and trans: "\<And> c d e. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> e \<in> C \<Longrightarrow> cge c d \<Longrightarrow> cge d e \<Longrightarrow> cge c e"
  and not_ge: "\<not> cge (I\<lbrakk>t\<rbrakk>(\<lambda>_. c)) (I\<lbrakk>s\<rbrakk>(\<lambda>_. c))" (is "\<not> cge (eval_term _ _ ?ass) _")
  (* before not_ge was [t] > [s] where > was defined as \<ge> \ \<le> *)
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
proof
  let ?eval = "\<lambda> t. I \<lbrakk>t\<rbrakk> ?ass"
  assume "(\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
  then obtain u where su: "(s,u) \<in> (rstep Rs)^*" and tu: "(t,u) \<in> (rstep Rt)^*" by auto
  have wf: "wf_assign C ?ass" unfolding wf_assign_def using c by auto
  from su have us: "(u,s) \<in> (rstep (Rs^-1))^*"
    unfolding rstep_converse rtrancl_converse by auto
  note sem = sem_rewrites[OF _ _ wf c wf_I wm model refl trans]
  note wf = wf_eval[OF wf_I wf]
  from sem[OF us] have us: "cge (?eval u) (?eval s)" by auto
  from sem[OF tu] have tu: "cge (?eval t) (?eval u)" by auto
  from trans[OF wf wf wf tu us] have ts: "cge (?eval t) (?eval s)" .
  with not_ge show False by auto
qed

lemma aoto_theorem_10: (* we weakened > to not \<le> *)
  assumes model: "qmodel I C cge ((usable_rules_reach R s)^-1 \<union> usable_rules_reach R t)"
  and c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and wm: "cge_wm I C cge"
  and refl: "\<And> c. c \<in> C \<Longrightarrow> cge c c"
  and trans: "\<And> c d e. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> e \<in> C \<Longrightarrow> cge c d \<Longrightarrow> cge d e \<Longrightarrow> cge c e"
  and not_ge: "\<not> cge (I\<lbrakk>t\<rbrakk>(\<lambda>_. c)) (I\<lbrakk>s\<rbrakk>(\<lambda>_. c))" (is "\<not> cge (eval_term _ _ ?ass) _")
  (* before not_ge was [t] > [s] where > was defined as \<ge> \ \<le> *)
  shows "(s,t) \<notin> join (rstep R)"
  using usable_rules_reach_nj[OF aoto_theorem_2[OF model c wf_I wm refl trans not_ge]]
  by auto

lemma aoto_theorem_10_af: (* not present in Aoto, but simple consequence *)
  assumes model: "qmodel I C cge ((usable_rules_reach (af_rule \<pi> ` (usable_rules_reach R s)) (af_term \<pi> s))^-1 \<union> 
    usable_rules_reach (af_rule \<pi> ` (usable_rules_reach R t)) (af_term \<pi> t))"
  and c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and wm: "cge_wm I C cge"
  and refl: "\<And> c. c \<in> C \<Longrightarrow> cge c c"
  and trans: "\<And> c d e. c \<in> C \<Longrightarrow> d \<in> C \<Longrightarrow> e \<in> C \<Longrightarrow> cge c d \<Longrightarrow> cge d e \<Longrightarrow> cge c e"
  and not_ge: "\<not> cge (I\<lbrakk>af_term \<pi> t\<rbrakk>(\<lambda>_. c)) (I\<lbrakk>af_term \<pi> s\<rbrakk>(\<lambda>_. c))" (is "\<not> cge (eval_term _ _ ?ass) _")
  (* before not_ge was [t] > [s] where > was defined as \<ge> \ \<le> *)
shows "(s,t) \<notin> join (rstep R)"
  using usable_rules_reach_nj[OF argument_filter_nj[OF usable_rules_reach_nj[OF aoto_theorem_2[OF model c wf_I wm refl trans not_ge]]]] by auto
  
lemma aoto_corollary_6: (* we show that this is an instance of theorem 10 *)
  assumes model: "qmodel I C (=) (usable_rules_reach R s \<union> usable_rules_reach R t)"
  and c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and neg: "I\<lbrakk>s\<rbrakk>(\<lambda>_. c) \<noteq> I\<lbrakk>t\<rbrakk>(\<lambda>_. c)" (is "eval_term _ _ ?ass \<noteq> _")
  shows "(s,t) \<notin> join (rstep R)"
proof -
  interpret usable_rules_reachability R .
  {
    fix l r
    note model = model[unfolded qmodel_def, rule_format]
    assume "(l,r) \<in> (Ur s)^-1 \<union> Ur t"
    then have "(l,r) \<in> Ur s \<union> Ur t \<or> (r,l) \<in> Ur s \<union> Ur t" by auto
    with model[of "(l,r)"] model[of "(r,l)"]
    have "qmodel_rule I C (=) l r" by auto
  }
  then have model: "qmodel I C (=) ((Ur s)^-1 \<union> Ur t)"
    unfolding qmodel_def by auto
  show ?thesis by (rule aoto_theorem_10[OF model c wf_I], insert neg, auto simp: cge_wm)
qed


lemma aoto_pre_theorem_12:
  assumes "discrimination_pair S NS"
  and s: "Rs^-1 \<subseteq> NS"
  and t: "Rt \<subseteq> NS"
  and st: "(s,t) \<in> S"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
proof
  assume "(\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
  then obtain u where su: "(s,u) \<in> (rstep Rs)^*" and tu: "(t,u) \<in> (rstep Rt)^*" by auto
  from su have us: "(u,s) \<in> (rstep (Rs^-1))^*" unfolding rtrancl_converse rstep_converse by simp
  interpret discrimination_pair S NS by fact
  from rtrancl_mono[OF rstep_imp_NS[OF s]] us have us: "(u,s) \<in> NS^*" by auto
  from rtrancl_mono[OF rstep_imp_NS[OF t]] tu have tu: "(t,u) \<in> NS^*" by auto
  from tu us have "(t,s) \<in> NS^*" by auto
  with st have "(t,t) \<in> NS^* O S" by auto
  with trCompat have "(t,t) \<in> S" by auto
  with irrefl_S show False by blast
qed

lemma aoto_pre_theorem_12_co:
  assumes "co_discrimination_pair S NS"
  and s: "Rs^-1 \<subseteq> NS"
  and t: "Rt \<subseteq> NS"
  and st: "(s,t) \<in> S"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
proof
  assume "(\<exists> u. (s,u) \<in> (rstep Rs)^* \<and> (t,u) \<in> (rstep Rt)^*)"
  then obtain u where su: "(s,u) \<in> (rstep Rs)^*" and tu: "(t,u) \<in> (rstep Rt)^*" by auto
  from su have us: "(u,s) \<in> (rstep (Rs^-1))^*" unfolding rtrancl_converse rstep_converse by simp
  interpret co_discrimination_pair S NS by fact
  from rtrancl_mono[OF rstep_imp_NS[OF s]] us have us: "(u,s) \<in> NS^*" by auto
  from rtrancl_mono[OF rstep_imp_NS[OF t]] tu have tu: "(t,u) \<in> NS^*" by auto
  from tu us have "(t,s) \<in> NS^*" by auto
  with trans_NS refl_NS have "(t,s) \<in> NS"
    by (simp add: trans_refl_imp_rtrancl_id)
  with st have "(t,t) \<in> NS O S" by auto
  with disj_NS_S show False by blast
qed

  
lemma aoto_theorem_12_co: 
  assumes pair: "co_discrimination_pair S NS"
  and s: "(usable_rules_reach R s)^-1 \<subseteq> NS"
  and t: "usable_rules_reach R t \<subseteq> NS"
  and st: "(s,t) \<in> S"
  shows "(s,t) \<notin> join (rstep R)"
  using usable_rules_reach_nj[OF aoto_pre_theorem_12_co[OF pair s t st]] by auto

lemma aoto_theorem_14_co: 
  assumes pair: "co_discrimination_pair S NS"
  and s: "(usable_rules_reach (af_rule \<pi> ` (usable_rules_reach R s)) (af_term \<pi> s))^-1 \<subseteq> NS" 
  and t: "usable_rules_reach (af_rule \<pi> ` (usable_rules_reach R t)) (af_term \<pi> t) \<subseteq> NS"
  and st: "(af_term \<pi> s,af_term \<pi> t) \<in> S"
  shows "(s,t) \<notin> join (rstep R)"
  using usable_rules_reach_nj[OF argument_filter_nj[OF usable_rules_reach_nj[OF aoto_pre_theorem_12_co[OF pair s t st]]]]
  by auto

end
