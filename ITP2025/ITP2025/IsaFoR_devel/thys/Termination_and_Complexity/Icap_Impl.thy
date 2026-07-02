(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Icap_Impl
imports
  TRS.Q_Restricted_Rewriting_Impl
  Icap
  Framework.Dependency_Pair_Problem_Spec
  Framework.Termination_Problem_Spec
  Show.Shows_Literal
  Auxx.Map_Choice
begin

lemma NF_subset_conditions:
  fixes R :: "('f, 'v) trs" and Q :: "('f, 'v) terms"
  shows "(\<forall>l\<in>lhss R. \<exists>t\<in>Q. \<exists>C \<sigma>. l = C\<langle>t \<cdot> \<sigma>\<rangle>) \<longleftrightarrow> NF_terms Q \<subseteq> NF_trs R"
proof (intro iffI allI impI subsetI)
  fix t assume 1: "\<forall>l\<in>lhss R. \<exists>t\<in>Q. \<exists>C \<sigma>. l = C\<langle>t \<cdot> \<sigma>\<rangle>" and 2: "t \<in> NF_terms Q"
  show "t \<in> NF_trs R"
  proof (rule ccontr)
    assume "t \<notin> NF_trs R"
    then obtain C l and \<sigma> :: "('f, 'v) subst" where "l \<in> lhss R" and t: "t = C\<langle>l \<cdot> \<sigma>\<rangle>" by blast
    with 1[THEN bspec, OF \<open>l \<in> lhss R\<close>]
      obtain u D and \<tau> :: "('f, 'v) subst" where "u \<in> Q" and l: "l = D\<langle>u \<cdot> \<tau>\<rangle>" by auto
    then have "(u, u) \<in> Id_on Q" by auto
    from rstep_ctxt[OF rstep_subst[OF rstep_ctxt[OF rstep_subst[OF rstep_rule[OF this]]]], of C D "\<tau>" "\<sigma>",
      unfolded l[symmetric] t[symmetric]]
      show False using \<open>t \<in> NF_terms Q\<close> by (auto simp: NF_def)
  qed
next
  assume 1: "NF_terms Q \<subseteq> NF_trs R"
  show "\<forall>l\<in>lhss R. \<exists>t\<in>Q. \<exists>C \<sigma>. l = C\<langle>t \<cdot> \<sigma>\<rangle>"
  proof
    fix l assume "l \<in> lhss R"
    then obtain r where "(l, r) \<in> R" by auto
    from rstep_rule[OF this] have "l \<notin> NF_trs R" by (auto simp: NF_def)
    with 1 have "l \<notin> NF_terms Q" by blast
    then obtain C l' and \<sigma> :: "('f, 'v) subst" where "l' \<in> Q" and "l = C\<langle>l' \<cdot> \<sigma>\<rangle>" by auto
    then show "\<exists>t\<in>Q. \<exists>C \<sigma>. l = C\<langle>t \<cdot> \<sigma>\<rangle>" by auto
  qed
qed

lemma ctxt_supteq_ex: "(\<exists>C \<sigma>. t = C\<langle>u \<cdot> \<sigma>\<rangle>) \<longleftrightarrow> (\<exists>\<sigma>. t \<unrhd> u \<cdot> \<sigma>)"
  using supteq_ctxt_conv[of t] by auto

lemma efficient_NF_check[simp]: "lhss R \<inter> NF_terms Q = {} \<longleftrightarrow> NF_terms Q \<subseteq> NF_trs R"
  using NF_terms_subset_criterion[of "lhss R" Q]
  unfolding NF_terms_lhss .

lemma term_map_subset:
  "set (term_map ts x) \<subseteq> set ts"
  using elem_list_to_rm.rm_set_lookup[of "the \<circ> root" ts x]
  by (auto simp: o_def term_map_def rm_set_lookup_def)

lemma efficient_ball:
  assumes "\<forall>t\<in>set ts. the (root t) \<noteq> the (root s) \<longrightarrow> P s t"
  shows
    "(\<forall>t\<in>set ts. P s t) \<longleftrightarrow>
     (\<forall>t\<in>set (term_map ts (the (root s))). P s t)"
  using assms
    and elem_list_to_rm.rm_set_lookup[of "the \<circ> root" ts "the (root s)"]
  by (auto simp: o_def term_map_def rm_set_lookup_def)

fun icap_impl_gen ::
  "bool \<Rightarrow> (('f, string) term \<Rightarrow> bool) \<Rightarrow> ('f, string) term list
    \<Rightarrow> ('f, string) term list \<Rightarrow> (string \<Rightarrow> bool) \<Rightarrow> ('f, string) term \<Rightarrow> ('f, unit + string) term"
where
  "icap_impl_gen nf isQnf ls S Sx (Var x) =
    (if nf \<and> Sx x then Var (Inr x) else Var (Inl ()))" 
| "icap_impl_gen nf isQnf ls S Sx (Fun f ts) = (
    let t' = Fun f (map (icap_impl_gen nf isQnf ls S Sx) ts) in
    if \<exists>l\<in>set ls. (case mgu_class t' l of None \<Rightarrow> False | Some \<mu> \<Rightarrow> 
       (\<forall>u\<in>set (args l). isQnf (mv_yvar u \<cdot> \<mu>)) \<and>
       (\<forall>u\<in>set S. isQnf (u \<cdot> \<mu>)))
      then Var (Inl ())
      else t')"

text\<open>The efficient implementation of @{const icap} is correct.\<close>
lemma icap_impl_gen:
  fixes Q :: "('f, string) terms" and S
  defines Sx: "Sx \<equiv> \<lambda>x. (\<exists>t \<in> set S. x \<in> vars_term t)"
  shows
  "icap_impl_gen (NF_terms Q \<subseteq> NF_trs (set R))
             (\<lambda> t. t \<in> NF_terms Q)
             (map fst R) S Sx t =
    icap (set R) Q (set S) t" (is "icap_impl_gen ?inn ?nf _ _ _ _ = _")
proof (induct t)
  case (Var x) show ?case by (simp add: Sx)
next
  case (Fun f ts)
  then have IH: "map (icap_impl_gen ?inn ?nf
                            (map fst R) S Sx) ts =
    map (icap (set R) Q (set S)) ts" using map_eq_conv by blast  
  {
    fix f x P
    have "(case f of None \<Rightarrow> False | Some x \<Rightarrow> P x) = (\<exists> x. f = Some x \<and> P x)"
      by (cases f, auto)
  } note id = this
  show ?case
    unfolding icap_impl_gen.simps
    unfolding IH
    unfolding id
    unfolding icap.simps(2)[of "set R" Q "set S" f ts]
    unfolding Let_def    
      by auto
qed


definition icap_impl' :: "(('f,string)term \<Rightarrow> bool) \<Rightarrow> ('f, string) rules
    \<Rightarrow> ('f, string) term list \<Rightarrow> ('f, string) term \<Rightarrow> ('f, unit + string) term" where
  "icap_impl' isnf R \<equiv> (
    let ls = map fst R;
        nf = is_NF_subset isnf ls;
        ic = icap_impl_gen nf isnf ls
      in (\<lambda> S. let S' = map mv_xvar S;
        Sx = ceta_set_of (concat (map vars_term_list S')) in
    (\<lambda> t. ic S' Sx (mv_xvar t))))"

lemma icap_impl'_sound[simp]: "icap_impl' (\<lambda> t. t \<in> NF_terms Q) R S = icap_mv (set R) Q (set S)"
  unfolding icap_impl'_def 
  unfolding Let_def
  by (rule ext, unfold icap_mv_def set_map[symmetric] icap_impl_gen[symmetric], simp) 


definition icap_impl_dpp_mv :: "('d,'f,string)dpp_ops \<Rightarrow> 'd \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,unit + string)term"
  where "icap_impl_dpp_mv I d \<equiv> 
    let QR = dpp_ops.NFQ_subset_NF_rules I d;
        qnf = dpp_ops.is_QNF I d;
        r = dpp_ops.rules I d;
        ic = icap_impl_gen QR qnf (map fst r)    
    in (\<lambda> S. let S' = map mv_xvar S;
                 Sx = ceta_set_of (concat (map vars_term_list S'))
             in (\<lambda> t. ic S' Sx (mv_xvar t)))"

lemma icap_impl_dpp_icap_mv[simp]:
  fixes I::"('d, 'f:: showl, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
      and r: "r \<equiv> dpp_ops.rules I d"
  assumes I: "dpp_spec I"
  shows "icap_impl_dpp_mv I d s = icap_mv (set r) (set q) (set s)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
    by (rule ext, 
      unfold icap_mv_def set_map[symmetric] icap_impl_gen[symmetric],
      unfold icap_impl_dpp_mv_def Let_def r q, simp)
qed    

definition icap_impl_dpp :: "('d,'f,string)dpp_ops \<Rightarrow> 'd \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,unit + string)term"
  where "icap_impl_dpp I d \<equiv> 
    let QR = dpp_ops.NFQ_subset_NF_rules I d;
        qnf = dpp_ops.is_QNF I d;
        r = dpp_ops.rules I d;
        ic = icap_impl_gen QR qnf (map fst r)    
    in (\<lambda> S. let Sx = ceta_set_of (concat (map vars_term_list S))
             in ic S Sx)"

lemma icap_impl_dpp_icap [simp]:
  fixes I :: "('d, 'f:: showl, string) dpp_ops" and d::"'d"
  defines q: "q \<equiv> dpp_ops.Q I d"
    and r: "r \<equiv> dpp_ops.rules I d"
  assumes I: "dpp_spec I"
  shows "icap_impl_dpp I d s = icap (set r) (set q) (set s)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
    by (rule ext, 
      unfold set_map[symmetric] icap_impl_gen[symmetric],
      unfold icap_impl_dpp_def Let_def r q, simp)
qed    

definition icap_impl_tp :: "('d,'f,string)tp_ops \<Rightarrow> 'd \<Rightarrow> ('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,unit + string)term"
  where "icap_impl_tp I d \<equiv> 
    let QR = tp_ops.NFQ_subset_NF_rules I d;
        qnf = tp_ops.is_QNF I d;
        r = tp_ops.rules I d;
        ic = icap_impl_gen QR qnf (map fst r)    
    in (\<lambda> S. let Sx = ceta_set_of (concat (map vars_term_list S))
             in ic S Sx)"

lemma icap_impl_tp_icap [simp]:
  fixes I :: "('d, 'f:: showl, string) tp_ops" and d::"'d"
  defines q: "q \<equiv> tp_ops.Q I d"
    and r: "r \<equiv> tp_ops.rules I d"
  assumes I: "tp_spec I"
  shows "icap_impl_tp I d s = icap (set r) (set q) (set s)"
proof -
  interpret tp_spec I by fact
  show ?thesis
    by (rule ext, 
      unfold set_map[symmetric] icap_impl_gen[symmetric],
      unfold icap_impl_tp_def Let_def r q, simp)
qed    

end
