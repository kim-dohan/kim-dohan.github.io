(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Non_Confluence_Impl
imports 
  Critical_Pairs_Impl
  Non_Confluence
  Usable_Rules_NJ_Impl
  Usable_Rules_NJ_Unif_Impl
  Ord.Term_Order_Impl
  Sem_Lab.Semantic_Labeling_Carrier
  TA.Tree_Automata_Impl
  Auxx.RTrancl_Impl
begin

definition "check_rule_removal infos R Rdel S = do {
  let F = funas_trs_list S;
  let RS = filter (\<lambda> lr. \<forall> f \<in> set (funas_term_list (fst lr)). f \<in> set F) Rdel;
  check_wf_trs S;
  check_allm (\<lambda> lr. case map_of infos lr of None \<Rightarrow> error (showsl_lit (STR ''did not find info for rule: '') o showsl_rule lr)
     | Some info \<Rightarrow> check_rsteps S info (fst lr) (snd lr)) RS
} <+? (\<lambda> e. e o showsl_nl o showsl_lit (STR ''problem in rule removal''))"                      

lemma check_rule_removal: fixes R S :: "('f :: showl,'v :: {infinite,showl})rules" 
  assumes "set S \<subseteq> set R" "set R - set S \<subseteq> set Rdel" 
  and "isOK(check_rule_removal infos R Rdel S)" 
  and "\<not> CR (rstep (set S))" 
shows "\<not> CR (rstep (set R))" 
proof
  note check = assms(3)[unfolded check_rule_removal_def Let_def, simplified]
  from check have wf: "wf_trs (set S)" by auto
  assume "CR (rstep (set R))" 
  from hirokowa_shintani_iwc_2024_theorem_5[OF assms(1) _ wf this] assms(4)
  have "\<not> rules_lhs_restrict_sig (set R) (set S) \<subseteq> (rstep (set S))\<^sup>*" by auto
  then obtain l r where lr: "(l,r) \<in> set R" and l: "funas_term l \<subseteq> funas_trs (set S)" and steps: "(l,r) \<notin> (rstep (set S))^*" 
    unfolding rules_lhs_restrict_sig_def by force
  show False
  proof (cases "(l,r) \<in> set S")
    case True
    hence "(l,r) \<in> rstep (set S)" by auto
    with steps show False by auto
  next
    case False
    with lr assms(2) have "(l,r) \<in> set Rdel" by auto
    with check[THEN conjunct2, rule_format, of l r] l obtain info where
      "isOK (check_rsteps S info l r)" by (cases "map_of infos (l, r)", auto)
    from check_rsteps_sound_star[OF this] steps show False by auto
  qed
qed
  

definition "check_modularity_ncr R R' = do {
  check_subseteq R' R <+? (\<lambda> _. showsl_lit (STR ''new TRS is not a subsystem of given TRS''));
  let S = list_diff R R';
  let F = funas_trs_list R';
  let G = funas_trs_list S;
  check (set F \<inter> set G \<subseteq> {}) (showsl_lit (STR ''signatures are not disjoint''));
  check_varcond_subset R';
  check_all (\<lambda>(l, r). is_Fun l) S
    <+? (\<lambda> _. showsl_lit (STR ''lhss must not be variables''))
}"

lemma check_modularity_ncr: fixes R :: "('f :: showl, 'v :: showl) rules"
  assumes ok: "isOK (check_modularity_ncr R R')"
    and nCR: "\<not> CR (rstep (set R'))"
    and inf: "infinite (UNIV :: 'f set)"
  shows "\<not> CR (rstep (set R))"
proof -
  let ?S = "set R - set R'"
  note ok = ok[unfolded check_modularity_ncr_def, simplified] 
  from ok have id: "set R = set R' \<union> ?S" and subset: "set R' \<subseteq> set R" by auto
  from id have id: "rstep (set R) = rstep (set R' \<union> ?S)" by auto
  show ?thesis unfolding id
    by (rule modularity_of_non_confluence[OF nCR],
    insert ok inf, auto intro: finite_funas_trs)
qed

abbreviation(input) join where "join \<equiv> Abstract_Rewriting.join"

fun
  check_qmodel_rule_ass ::
    "('f:: showl,'c:: showl)inter  
     \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> ('v:: showl,'c)assign \<Rightarrow> ('f,'v)rule \<Rightarrow> showsl check"
where
  "check_qmodel_rule_ass I cge \<alpha> (l, r) = do {
     let cl = I\<lbrakk>l\<rbrakk>\<alpha>;
     let cr = I\<lbrakk>r\<rbrakk>\<alpha>;
     check (cge cl cr)
       (showsl_lit (STR ''rule '') \<circ> showsl_rule (l, r) \<circ> showsl_lit (STR '' violates the model condition, [lhs] = '')
         \<circ> showsl cl \<circ> showsl_lit (STR '', [rhs] = '') \<circ> showsl cr)
   }"

definition
  check_qmodel_rule ::
    "('f:: showl,'c:: showl)inter  
     \<Rightarrow> 'c list 
     \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> ('f,'v:: showl)rule \<Rightarrow> showsl check"
where
  "check_qmodel_rule I C cge lr = check_allm (\<lambda>\<alpha>. check_qmodel_rule_ass I cge \<alpha> lr) 
     (map fun_of (enum_vectors C (vars_rule_impl lr)))"

definition
  check_qmodel ::
    "('f:: showl,'c:: showl)inter  
     \<Rightarrow> 'c list 
     \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> ('f,'v:: showl)sl_check0"
where
  "check_qmodel I C cge R = check_allm (check_qmodel_rule I C cge) R"


lemma check_qmodel:
  fixes I :: "('f :: showl,'c:: showl)inter" 
  assumes ok: "isOK (check_qmodel I C cge R)"
  shows "qmodel I (set C) cge (set R)"
proof -  
  let ?L = undefined
  let ?LC = undefined
  {
    fix l r
    assume lr: "(l,r) \<in> set R"
    {
      fix \<alpha>
      have "check_sl_rule_ass True I ?L ?LC cge UNIV \<alpha> (l,r) = check_qmodel_rule_ass I cge \<alpha> (l,r)" 
        by (simp add: Let_def check_def)
    } note id = this
    from lr ok[unfolded check_qmodel_def] have "True = isOK(check_qmodel_rule I C cge (l,r))" by auto
    also have "\<dots> = isOK (check_sl_rule I ?L ?LC C cge True UNIV (l,r))" 
      unfolding check_qmodel_rule_def check_sl_rule.simps id ..
    finally have "isOK (check_sl_rule I ?L ?LC C cge True UNIV (l,r))" by simp
    from check_sl_rule_sound[OF this] have "Semantic_Labeling.qmodel_rule I ?L ?LC (set C) cge l r" by simp
  }
  then have "Semantic_Labeling.qmodel I ?L ?LC (set C) cge (set R)" unfolding Semantic_Labeling.qmodel_def by auto
  then show ?thesis by simp  
qed

definition check_non_join_model ::
    "('c \<Rightarrow> 'c:: showl \<Rightarrow> bool) \<Rightarrow>     
     (('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f,'c,'l,'v)sl_ops) \<Rightarrow>
     ('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)rules \<Rightarrow>
     ('f,'v)term \<Rightarrow>
     ('f,'v)term \<Rightarrow>     
     showsl check"
where
  "check_non_join_model cge gen Rs Rt s t \<equiv> 
      do {
        ops \<leftarrow> gen (funas_trs_list (Rs @ Rt)) [];
        let I = sl_ops.sl_I ops;
        let e = (\<lambda> t. I\<lbrakk>t\<rbrakk>(\<lambda> _. sl_ops.sl_c ops));
        let es = e s;
        let et = e t;
        check (\<not> cge et es) (showsl_lit (STR ''the inequality must not hold: ['') \<circ> showsl t \<circ> showsl_lit (STR ''] = '') \<circ> showsl et \<circ> showsl_lit (STR '' >= '') 
          \<circ> showsl es \<circ> showsl_lit (STR '' = ['') \<circ> showsl s \<circ> showsl_lit (STR '']''));
        check_qmodel I (sl_ops.sl_C ops) cge (reverse_rules Rs @ Rt)
     } <+? (\<lambda> s. showsl_lit (STR ''problem in disproving non-joinability via interpretations'') \<circ> showsl_nl \<circ> s)"

lemma (in sl_finite_impl) check_non_join_model: assumes ok: "isOK(check_non_join_model cge sl_gen Rs Rt s t)"
  and refl: "\<And> x. cge x x"
  and trans: "\<And> x y z. cge x y \<Longrightarrow> cge y z \<Longrightarrow> cge x z"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
proof -
  note ok = ok[unfolded check_non_join_model_def Let_def]
  from ok obtain ops where gen: "sl_gen (funas_trs_list (Rs @ Rt)) [] = Inr ops" by auto
  let ?c = "sl_c ops"
  let ?I = "sl_I ops"
  let ?C = "sl_C ops"
  note ok = ok[unfolded gen, simplified]
  from sl_gen_inter[OF gen] 
  interpret sl_interpr_root_same "set ?C" ?c ?I cge lge "sl_L ops" LC LD "sl_LS ops" "sl_L'' ops" "sl_LS'' ops" .
  from ok have "isOK (check_qmodel ?I ?C cge (reverse_rules Rs @ Rt))" by auto
  from check_qmodel[OF this]
  have "qmodel ?I (set ?C) cge ((set Rs)^-1 \<union> set Rt)" by simp
  note aoto = aoto_theorem_2[OF this c wf_I wm_cge refl]
  let ?e = "\<lambda> t. ?I\<lbrakk>t\<rbrakk>(\<lambda> _. ?c)"
  from ok have "\<not> cge (?e t) (?e s)" by simp
  note aoto = aoto[OF trans this]
  show ?thesis
    by (rule aoto)
qed

definition check_non_join_discr_pair ::
    "('f::{showl,compare_order}, 'v:: showl) rel_impl \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow>
     ('f,'v)term \<Rightarrow>
     ('f,'v)term \<Rightarrow>     
     showsl check" where
  "check_non_join_discr_pair rp Rs Rt s t \<equiv> 
    do {
        rel_impl_co_discrimination_pair rp;
        rel_impl_ns rp (reverse_rules Rs @ Rt);
        rel_impl.s rp (s, t)
     } <+? (\<lambda> s. showsl_lit (STR ''problem in disproving non-joinability via co-discrimination pairs'') \<circ> showsl_nl \<circ> s)"

lemma check_non_join_discr_pair: assumes rp: "rel_impl rp"
  and ok: "isOK(check_non_join_discr_pair rp Rs Rt s t)"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
proof -
  note ok = ok[unfolded check_non_join_discr_pair_def Let_def, simplified]
  from ok have valid: "isOK(rel_impl_co_discrimination_pair rp)" by simp
  from ok have ns: "isOK (rel_impl_ns rp (reverse_rules Rs @ Rt))" by simp
  from ok have s: "isOK (rel_impl_s rp [(s,t)])" by (simp add: rel_impl_list)
  from rel_impl_co_discrimination_pair[OF rp valid s ns]
    obtain S NS where dp: "co_discrimination_pair S NS" 
    and NS: "(set Rs)^-1 \<union> set Rt \<subseteq> NS" and S: "(s,t) \<in> S" by auto
  show ?thesis
    by (rule aoto_pre_theorem_12_co[OF dp], insert NS S, auto)
qed

text \<open>Now we have to link to concrete interpretations and reduction pairs\<close>

type_synonym 'f lt = "('f,label_type)lab"

fun check_non_join_finite_model :: "(('f :: showl)lt,'v :: showl) sl_variant \<Rightarrow> 
  ('f lt,'v)rules \<Rightarrow> ('f lt,'v)rules \<Rightarrow>
  ('f lt,'v)term  \<Rightarrow> 
  ('f lt,'v)term \<Rightarrow> showsl check" where 
  "check_non_join_finite_model (Rootlab x) Rs Rt s t = check_non_join_model (=) (slm_gen_to_sl_gen (rl_slm x)) Rs Rt s t"
| "check_non_join_finite_model (Finitelab sli) Rs Rt s t = 
    check_non_join_model (=) (slm_gen_to_sl_gen (\<lambda>_ _. return (sli_to_slm sli))) Rs Rt s t"
| "check_non_join_finite_model (QuasiFinitelab sli v) Rs Rt s t = 
    or_ok (check_non_join_model qmodel_cge (\<lambda> F G. qsli_to_sl v F G sli) Rs Rt s t)
     (check_non_join_model qmodel_cge (\<lambda> F G. qsli_to_sl v F G sli) Rt Rs t s)" 

(* TODO: delete in the future, will be available in AFP 2024 or newer *)
lemma or_is_or[simp]: "isOK (or_ok a b) = (isOK a \<or> isOK b)" 
  by (cases a, auto)

lemma check_non_join_finite_model: assumes ok: "isOK(check_non_join_finite_model I Rs Rt s t)"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
proof (cases I)
  case (Rootlab I)
  with ok show ?thesis
    by (intro rl_fin_model.check_non_join_model, auto)
next
  case (Finitelab I)
  with ok show ?thesis
    by (intro sl_fin_model.check_non_join_model, auto)
next
  case (QuasiFinitelab I v)
  with ok consider (normal) "isOK (check_non_join_model qmodel_cge (\<lambda>F G. qsli_to_sl v F G I) Rs Rt s t)" 
    | (swap) "isOK (check_non_join_model qmodel_cge (\<lambda>F G. qsli_to_sl v F G I) Rt Rs t s)" by auto
  thus ?thesis 
  proof (cases)
    case normal 
    thus ?thesis by (intro arith_finite_qmodel.check_non_join_model, auto simp: qmodel_cge_def)
  next
    case swap
    hence "\<not> (\<exists> u. (t,u) \<in> (rstep (set Rt))^* \<and> (s,u) \<in> (rstep (set Rs))^*)" 
      by (intro arith_finite_qmodel.check_non_join_model, auto simp: qmodel_cge_def)
    thus ?thesis by auto
  qed
qed


context 
  fixes R :: "('f,'v)rules"
begin

partial_function (option) all_reachable_terms :: "(_,_)term list \<Rightarrow> (_,_)term list option" where
  [code]: "all_reachable_terms ts = (let new_terms = List.maps (rewrite R) ts;
     really_new = filter (\<lambda> t. t \<notin> set ts) new_terms
    in if really_new = [] then Some ts else all_reachable_terms (ts @ really_new))" 

lemma all_reachable_terms: assumes "all_reachable_terms ts = Some reach"
  and wf:"wf_trs (set R)" 
shows "set reach = {t. \<exists> s \<in> set ts. (s,t) \<in> (rstep (set R))^*}" (is "_ = ?RHS")
proof (induct rule: all_reachable_terms.raw_induct[OF _ assms(1)])
  case (1 all_reachable_terms ts reach)
  define new_terms where "new_terms =  List.maps (rewrite R) ts"
  define really_new where "really_new = filter (\<lambda> t. t \<notin> set ts) new_terms"
  note result = 1(2)[unfolded Let_def, folded new_terms_def, folded really_new_def]
  from wf have var:"(\<And>l r. (l, r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l)" by (simp add: wf_trs_def)
  hence rewr[simp]: "set (rewrite R s) = {t. (s, t) \<in> rstep (set R)}" for s
    using rewrite[OF var] by auto
  show ?case
  proof(cases "really_new = []")
    case True
    with result have rts: "reach = ts" by (auto split: if_splits)
    from True have "set really_new = {}" by auto
    from this[unfolded really_new_def new_terms_def List.maps_def]
    have one_step_closed: "t \<in> set ts \<Longrightarrow> (t, s) \<in> rstep (set R) \<Longrightarrow> s \<in> set ts" for t s by auto  
    show ?thesis unfolding rts
    proof (standard, force, clarsimp)
      fix s t
      show "(s, t) \<in> (rstep (set R))\<^sup>* \<Longrightarrow> s \<in> set ts \<Longrightarrow> t \<in> set ts" 
        by (induct rule: rtrancl_induct, insert one_step_closed, auto)
    qed
  next
    case False
    with result have all:"all_reachable_terms (ts @ really_new) = Some reach" by auto
    from 1(1)[OF this]
    have IH: "set reach = {t. \<exists>s\<in>set (ts @ really_new). (s, t) \<in> (rstep (set R))\<^sup>*}" by auto
    show ?thesis unfolding IH set_append
    proof ((standard; clarify), goal_cases)
      case (1 t s)
      then show ?case 
      proof(cases "s \<in> set ts")
        case True
        then show ?thesis using 1(2) by auto
      next
        case False
        then have "s \<in> set really_new" 
          using 1(1) by auto
        from this[unfolded really_new_def new_terms_def List.maps_def, simplified]
        obtain s' where "s' \<in> set ts" and "(s', s) \<in> rstep (set R)" by auto
        thus ?thesis using 1(2) by (intro bexI[of _ s'], auto)
      qed      
    qed auto
  qed
qed
end
      

definition "is_non_joinable_finite_reachable R1 R2 s t = (do {
  check_wf_trs R1;
  check_wf_trs R2;
  case (all_reachable_terms R1 [s], all_reachable_terms R2 [t]) of
    (Some reach1, Some reach2) \<Rightarrow> 
    check_allm (\<lambda> u. check (u \<notin> set reach2) (showsl_lit (STR ''the following term is a join: '') o showsl u)) reach1
   | _ \<Rightarrow> check False (showsl_lit (STR ''cannot happen: is_non_join is non-terminating''))
  })"

lemma check_non_joinable_finite_reachable: assumes ok: "isOK(is_non_joinable_finite_reachable Rs Rt s t)"
  shows "\<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
proof -
  note ok = ok[unfolded is_non_joinable_finite_reachable_def, simplified]
  from ok obtain reach1 where all1: "all_reachable_terms Rs [s] = Some reach1" (is "?expr = _") by (cases ?expr, auto)
  note ok = ok[unfolded all1, simplified]
  from ok obtain reach2 where all2: "all_reachable_terms Rt [t] = Some reach2" (is "?expr = _") by (cases ?expr, auto)
  note ok = ok[unfolded all2, simplified]
  from all_reachable_terms[OF all1]
  show ?thesis
  proof(safe)
    have wfs:"wf_trs (set Rs)" using ok by auto
    have wft:"wf_trs (set Rt)" using ok by auto
    have "set reach1 = {t. \<exists>s\<in>set [s]. (s, t) \<in> (rstep (set Rs))\<^sup>*}" 
      using all_reachable_terms[OF all1] ok by auto
    show "\<And> u. (s, u) \<in> (rstep (set Rs))\<^sup>* \<Longrightarrow> (t, u) \<in> (rstep (set Rt))\<^sup>* \<Longrightarrow> False"
    proof -
    { fix u
      assume su:"(s, u) \<in> (rstep (set Rs))\<^sup>*"
      then show "(t, u) \<in> (rstep (set Rt))\<^sup>* \<Longrightarrow> False"
      proof -
        assume "(t, u) \<in> (rstep (set Rt))\<^sup>*"
        then show False using ok su all_reachable_terms[OF all1] all_reachable_terms[OF all2] by simp
      qed
    } 
    qed
  qed
qed

definition "is_non_joinable_finite_reachable_rtrancl succsR succsS s t = (do {
  case (rtrancl_option succsR [s], rtrancl_option succsS [t]) of
    (Some reach1, Some reach2) \<Rightarrow> 
    check_allm (\<lambda> u. check (u \<notin> set reach2) (showsl_lit (STR ''the following term is a join: '') o showsl u)) reach1
   | _ \<Rightarrow> check False (showsl_lit (STR ''cannot happen: is_non_join is non-terminating''))
  })"


lemma is_non_joinable_finite_reachable_rtrancl: 
  fixes R S :: "'f :: showl rel" and succsR succsS :: "'f :: showl \<Rightarrow> 'f :: showl list" 
  assumes ok: "isOK(is_non_joinable_finite_reachable_rtrancl succsR succsS s t)"
  and succsR[simp]: "\<And> x. set (succsR x) = {y. (x,y) \<in> R}"
  and succsS[simp]: "\<And> x. set (succsS x) = {y. (x,y) \<in> S}"
  shows "\<not> (\<exists> u. (s,u) \<in> R^* \<and> (t,u) \<in> S^*)"
proof -
  note ok = ok[unfolded is_non_joinable_finite_reachable_rtrancl_def, simplified]
  from ok obtain reach1 where all1: "rtrancl_option succsR [s] = Some reach1" (is "?expr = _") by (cases ?expr, auto)
  note ok = ok[unfolded all1, simplified]
  from ok obtain reach2 where all2: "rtrancl_option succsS [t] = Some reach2" (is "?expr = _") by (cases ?expr, auto)
  note ok = ok[unfolded all2, simplified]
  from rtrancl_option[OF all1]
  show ?thesis
  proof(safe)
    have "set reach1 = {t. \<exists>s\<in>set [s]. (s, t) \<in> R^*}" 
      using rtrancl_option[OF all1] ok by auto
    show "\<And> u. (s, u) \<in> R^* \<Longrightarrow> (t, u) \<in> S^* \<Longrightarrow> False"
    proof -
    { fix u
      assume su:"(s, u) \<in> R^*"
      then show "(t, u) \<in> S^* \<Longrightarrow> False"
      proof -
        assume "(t, u) \<in> S^*"
        then show False using ok su rtrancl_option[OF all1] rtrancl_option[OF all2] by simp
      qed
    } 
    qed
  qed
qed


text \<open>combine all techniques for non-joinability\<close>
datatype (dead 'f, dead 'v, 'q, 'rp) non_join_info =
  Diff_NFs
| Tcap_Non_Unif "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) subst"
| Tree_Aut_Intersect_Empty "('q, 'f) tree_automaton" "'q ta_relation" 
      "('q, 'f) tree_automaton" "'q ta_relation" 
| Finite_Model_Gt "('f, 'v) sl_variant"
| Discr_Pair_Gt "('f,'v,'rp)rel_impl_type" 'rp
| Usable_Rules_Reach_NJ "('f, 'v, 'q, 'rp) non_join_info"
| Usable_Rules_Reach_Unif_NJ "('f, 'v) rules + ('f, 'v) rules" "('f, 'v, 'q, 'rp) non_join_info"
| Finitely_Reachable  
| Argument_Filter_NJ "'f afs_list" "('f, 'v, 'q, 'rp) non_join_info"
| Grounding "('f, 'v) substL" "('f, 'v, 'q, 'rp) non_join_info"
| Subterm_NJ pos "('f, 'v, 'q, 'rp) non_join_info"

primrec check_non_join :: "(('f :: {compare_order,showl})lt,string)rules \<Rightarrow> ('f lt,string)rules \<Rightarrow> ('f lt,string)term \<Rightarrow> ('f lt,string)term \<Rightarrow> 
  ('f lt,string,'q :: {showl,compare_order},_)non_join_info \<Rightarrow> showsl check" where
  "check_non_join Rs Rt s t Diff_NFs = do {
                  check (s \<noteq> t) (showsl_lit (STR ''the terms '') \<circ> showsl s \<circ> showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are identical''));
                  let chknf = (\<lambda> s R. check (is_NF_trs R s) (showsl_lit (STR ''the term '') \<circ> showsl s \<circ> showsl_lit (STR '' is not in normal form'')));
                  chknf s Rs;
                  chknf t Rt
               }"
| "check_non_join Rs Rt s t (Grounding \<sigma> prf) = do {
       let \<sigma>' = mk_subst Var \<sigma>;
       check_non_join Rs  Rt  (s \<cdot> \<sigma>') (t \<cdot> \<sigma>') prf
     }"
| "check_non_join Rs Rt s t (Subterm_NJ p prf) = do {
       check (p \<in> pos_gctxt (tcapI Rs s)) (showsl_lit (STR ''position '') \<circ> showsl_pos p \<circ> showsl_lit (STR '' not in capped term  of '') \<circ> showsl s);
       check (p \<in> pos_gctxt (tcapI Rt t)) (showsl_lit (STR ''position '') \<circ> showsl_pos p \<circ> showsl_lit (STR '' not in capped term  of '') \<circ> showsl t);
       check_non_join Rs  Rt  (s |_ p) (t |_ p) prf
     }"
| "check_non_join Rs Rt s t (Tcap_Non_Unif grd_subst) = do {
                 let \<sigma> = grd_subst s t;
                 let cs = tcapI Rs (s \<cdot> \<sigma>);
                 let ct = tcapI Rt (t \<cdot> \<sigma>);
                 check (Ground_Context_Impl.merge cs ct = None) (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not joinable''))
               }"
| "check_non_join Rs Rt s t (Tree_Aut_Intersect_Empty ta1 rel1 ta2 rel2) = do {
                 non_join_with_ta ta1 rel1 Rs s ta2 rel2 Rt t
                   <+? (\<lambda> e. (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not joinable'') \<circ> showsl_nl \<circ> e))
                 }"
| "check_non_join Rs Rt s t (Finite_Model_Gt I) = do {
                 check_non_join_finite_model I Rs Rt s t
                   <+? (\<lambda> e. (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not joinable'') \<circ> showsl_nl \<circ> e))
                }"
| "check_non_join Rs Rt s t (Discr_Pair_Gt grt rp) = do { \<comment> \<open>use symmetric version by request of Takahito\<close>
                 or_ok (check_non_join_discr_pair (rel_impl_of grt rp) Rs Rt s t)
                   (check_non_join_discr_pair (rel_impl_of grt rp) Rt Rs t s)
                   <+? (\<lambda> e. (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not joinable by discrimination pair'')))
                }"
| "check_non_join Rs Rt s t (Usable_Rules_Reach_NJ prf) = 
    check_non_join (usable_rules_reach_impl Rs s) (usable_rules_reach_impl Rt t) s t prf"
| "check_non_join Rs Rt s t (Usable_Rules_Reach_Unif_NJ U_sum prf) = (
    case U_sum of 
      Inl U \<Rightarrow> do {
        check_usable_rules_unif Rs U s;
        check_non_join U Rt s t prf
      }
    | Inr U \<Rightarrow> do {
        check_usable_rules_unif Rt U t;
        check_non_join Rs U s t prf
      }
    )
    "
| "check_non_join Rs Rt s t Finitely_Reachable = do {
    check_wf_trs Rs;
    check_wf_trs Rt;
    is_non_joinable_finite_reachable_rtrancl (rewrite Rs) (rewrite Rt) s t
      <+? (\<lambda> e. (showsl_lit (STR ''could not infer that '') \<circ> showsl s \<circ> 
                     showsl_lit (STR '' and '') \<circ> showsl t \<circ> showsl_lit (STR '' are not joinable by finitely reachable terms'')))
  }"
| "check_non_join Rs Rt s t (Argument_Filter_NJ pi prf) = (case afs_of pi of 
    None \<Rightarrow> error (showsl_lit (STR ''invalid argument filter'')) 
  | Some \<pi> \<Rightarrow> let af = af_term \<pi>; afs = af_rules \<pi>
      in check_non_join (afs Rs) (afs Rt) (af s) (af t) prf
      )"

lemma check_non_join:
  "isOK(check_non_join Rs Rt s t prf) \<Longrightarrow> \<not> (\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*)"
proof (induct "prf" arbitrary: Rs Rt s t)
  case Diff_NFs
  note ok = Diff_NFs[simplified]
  show ?case
  proof
    assume "\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*"
    then obtain u where su: "(s,u) \<in> (rstep (set Rs))^*" and tu: "(t,u) \<in> (rstep (set Rt))^*" by auto
    from NF_not_suc[OF su] NF_not_suc[OF tu] ok show False by auto
  qed
next
  case (Subterm_NJ p prof) note IH = this
  then have p: "p \<in> pos_gctxt (tcap (set Rs) s)" "p \<in> pos_gctxt (tcap (set Rt) t)" 
    and ok: "isOK (check_non_join Rs Rt (s |_ p) (t |_p) prof)" by auto
  from subterm_tcap_nj[OF p IH(1)[OF ok]]
  show ?case .
next
  case (Grounding sigma prof)
  show ?case
  proof
    assume "\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*"
    then obtain u where su: "(s,u) \<in> (rstep (set Rs))^*" and tu: "(t,u) \<in> (rstep (set Rt))^*" by auto
    define \<sigma> where "\<sigma> = mk_subst Var sigma"
    from rsteps_closed_subst[OF su] have s: "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (set Rs))^*" .
    from rsteps_closed_subst[OF tu] have t: "(t \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (set Rt))^*" .
    from Grounding(2) have ok: "isOK (check_non_join Rs Rt (s \<cdot> \<sigma>) (t \<cdot> \<sigma>) prof)" unfolding \<sigma>_def
      by (simp add: Let_def)
    from Grounding(1)[OF this] s t show False by auto
  qed
next
  case (Tcap_Non_Unif grd_subst)
  obtain \<sigma> where sigma: "\<sigma> = grd_subst s t" by auto
  show ?case
  proof
    assume "\<exists> u. (s,u) \<in> (rstep (set Rs))^* \<and> (t,u) \<in> (rstep (set Rt))^*"
    then obtain u where su: "(s,u) \<in> (rstep (set Rs))^*" and tu: "(t,u) \<in> (rstep (set Rt))^*" by auto
    from rsteps_closed_subst[OF su] have s: "(s \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (set Rs))^*" .
    from rsteps_closed_subst[OF tu] have t: "(t \<cdot> \<sigma>, u \<cdot> \<sigma>) \<in> (rstep (set Rt))^*" .
    from tcap_sound[of "s \<cdot> \<sigma>" Var "u \<cdot> \<sigma>"] s have u1: "u \<cdot> \<sigma> \<in> equiv_class (tcap (set Rs) (s \<cdot> \<sigma>))" by simp
    from tcap_sound[of "t \<cdot> \<sigma>" Var "u \<cdot> \<sigma>"] t have u2: "u \<cdot> \<sigma> \<in> equiv_class (tcap (set Rt) (t \<cdot> \<sigma>))" by simp
    from u1 u2 Tcap_Non_Unif show False using sigma by (auto simp: Let_def)
  qed
next
  case (Tree_Aut_Intersect_Empty ta1 rel1 ta2 rel2)
  then have "isOK (non_join_with_ta ta1 rel1 Rs s ta2 rel2 Rt t)" by auto
  from non_join_with_ta[OF this] show ?case .
next
  case (Finite_Model_Gt I)
  then have "isOK (check_non_join_finite_model I Rs Rt s t)" by auto
  from check_non_join_finite_model[OF this] show ?case .
next 
  case (Discr_Pair_Gt grt rp)
  then have "isOK (check_non_join_discr_pair (rel_impl_of grt rp) Rs Rt s t)
    \<or> isOK (check_non_join_discr_pair (rel_impl_of grt rp) Rt Rs t s)" by auto
  with check_non_join_discr_pair[OF rel_impl_of, of grt rp] show ?case by auto
next
  case (Usable_Rules_Reach_NJ p)
  note * = this
  from usable_rules_reach_nj[OF *(1)[OF *(2)[unfolded check_non_join.simps], unfolded usable_rules_reach_impl]]
  show ?case .
next
  case (Usable_Rules_Reach_Unif_NJ U_sum p)
  note * = this
  show ?case
  proof (cases U_sum)
    case (Inl U)
    show ?thesis
      by (rule check_usable_rules_unif_left[OF _ *(1)], insert *(2) Inl, auto)
  next
    case (Inr U)
    show ?thesis
      by (rule check_usable_rules_unif_right[OF _ *(1)], insert *(2) Inr, auto)
  qed
next
  case (Argument_Filter_NJ pi p)
  note * = this
  note ok = *(2)[simplified]
  from ok obtain \<pi> where pi: "afs_of pi = Some \<pi>" by (cases "afs_of pi", auto)
  from ok[unfolded pi]
  have rec: "isOK (check_non_join (af_rules \<pi> Rs) (af_rules \<pi> Rt) (af_term \<pi> s) (af_term \<pi> t) p)" 
    by (auto simp: Let_def)
  from argument_filter_nj[OF *(1)[OF rec, unfolded af_rules]]
  show ?case .
next
  case Finitely_Reachable
  hence wf: "wf_trs (set Rs)" "wf_trs (set Rt)" and 
    join: "isOK (is_non_joinable_finite_reachable_rtrancl (rewrite Rs) (rewrite Rt) s t)" 
    by auto
  show ?case
    by (rule is_non_joinable_finite_reachable_rtrancl[OF join rewrite rewrite], insert wf, auto simp: wf_trs_def)
qed  

text \<open>and combine with reachability checker to disprove CR\<close>

definition check_non_cr :: "(('f :: {compare_order,showl})lt,string)rules \<Rightarrow> ('f lt,string)term \<Rightarrow> ('f lt,string)rseq \<Rightarrow> ('f lt,string)rseq \<Rightarrow> 
     ('f lt,string,'q :: {showl,compare_order}, _)non_join_info \<Rightarrow> showsl check"
  where "check_non_cr R s seq1 seq2 reason \<equiv> do {
             let chk = check_rsteps_last R s;
             chk seq1;
             chk seq2;
             check_non_join R R (rseq_last s seq1) (rseq_last s seq2) reason
        }"

lemma check_non_cr: assumes ok: "isOK(check_non_cr R s seq1 seq2 prf)"
  shows "\<not> CR (rstep (set R))"
proof 
  let ?R = "rstep (set R)"
  assume CR: "CR ?R"
  note ok = ok[unfolded check_non_cr_def Let_def, simplified]
  let ?last = "rseq_last s" 
  let ?l1 = "?last seq1"
  let ?l2 = "?last seq2"
  from check_rsteps_last_sound ok have s1: "(s,?l1) \<in> (rstep (set R))^*" by auto  
  from check_rsteps_last_sound ok have s2: "(s,?l2) \<in> (rstep (set R))^*" by auto
  from ok have "isOK (check_non_join R R ?l1 ?l2 prf)" by auto
  from CR s1 s2 check_non_join[OF this] show False by auto
qed

end
