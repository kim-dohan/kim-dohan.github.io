theory Cut_Points
imports 
  Show.Show_Instances
  Certification_Monads.Check_Monad
  Gabow_SCC_RBT
  Weighted_Path_Order.Relations
  Diff_Array_Code_Haskell
  Show.Shows_Literal
begin
  
  
definition "cut_points R X \<equiv> \<forall>Y. Y \<noteq> {} \<longrightarrow> Y \<times> Y \<subseteq> (R \<restriction> Y)\<^sup>+ \<longrightarrow> X \<inter> Y \<noteq> {}"

lemma cut_points_via_acyclic:
  assumes "acyclic (R \<restriction> (UNIV - X))" shows "cut_points R X"
  unfolding cut_points_def
proof (intro allI impI notI)
  fix Y
  assume Y: "Y \<noteq> {}" "Y \<times> Y \<subseteq> (R \<restriction> Y)\<^sup>+" "X \<inter> Y = {}" 
  from Y obtain y where y: "y \<in> Y" by auto
  from y Y have "(y,y) \<in> (R \<restriction> Y)\<^sup>+" by auto 
  also have "\<dots> \<subseteq> (R \<restriction> (UNIV - X))\<^sup>+" 
    by (rule trancl_mono_set, insert Y(3), auto)
  finally show False using assms[unfolded acyclic_def] by auto
qed

lemma acyclic_via_sccs: "acyclic R = (\<forall> C. is_scc R C \<longrightarrow> C \<times> C \<subseteq> R^+ \<longrightarrow> False)"
  unfolding acyclic_def
proof (intro iffI allI notI impI)
  fix x
  assume "(x,x) \<in> R\<^sup>+" and no_scc: "\<forall>C. is_scc R C \<longrightarrow> C \<times> C \<subseteq> R\<^sup>+ \<longrightarrow> False" 
  then obtain y where xy: "(x,y) \<in> R" "(y,x) \<in> R\<^sup>*" by (meson tranclD)
  from is_scc_ex[of R x] obtain X where x: "x \<in> X" and scc: "is_scc R X" by blast
  from no_scc[rule_format, OF scc] obtain x1 x2 where x1: "x1 \<in> X" "x2 \<in> X" and no: "(x1,x2) \<notin> R^+" by auto
  from is_scc_closed[OF scc x _ xy(2)] xy(1) have y: "y \<in> X" by auto
  note conn = is_scc_connected[OF scc]
  from conn[OF x1(1) x] xy(1) conn[OF y x1(2)] have "(x1,x2) \<in> R^+" by auto
  with no show False by auto
next
  fix C
  assume *: "\<forall> x. (x,x) \<notin> R^+" "is_scc R C" "C \<times> C \<subseteq> R^+" 
  from *(2) have "C \<noteq> {}" by auto
  then obtain v where v: "v \<in> C" by auto
  with *(1,3) show False by auto
qed

definition check_acyclic :: "('a :: {showl,compare_order} \<times> 'a) list \<Rightarrow> showsl check"
  where "check_acyclic R \<equiv> do {
      check_allm (\<lambda> scc. error (showsl_lit (STR ''SCC '') o showsl_list scc o showsl_lit (STR '' detected ''))) 
        (scc_decomp R)
    } <+? (\<lambda> s. showsl_lit (STR ''\<newline>graph '') o showsl_list R o showsl_lit (STR '' not acyclic\<newline>'') o s)"

lemma check_acyclic[simp]: "isOK(check_acyclic R) = acyclic (set R)" 
  unfolding check_acyclic_def acyclic_via_sccs by (simp add: scc_decomp_empty)

definition check_cut_points :: "('a :: {showl,compare_order} \<times> 'a) list \<Rightarrow> 'a set \<Rightarrow> showsl check"
  where "check_cut_points R X \<equiv> check_acyclic(filter (\<lambda> ab. fst ab \<notin> X \<and> snd ab \<notin> X) R)"

lemma check_cut_points:
  "isOK(check_cut_points R X) \<Longrightarrow> cut_points (set R) X"
proof - 
  have id: "{x \<in> set R. fst x \<notin> X \<and> snd x \<notin> X}  = set R \<restriction> (UNIV - X)" by force
  show  "isOK(check_cut_points R X) \<Longrightarrow> cut_points (set R) X"
  unfolding check_cut_points_def
  by (intro cut_points_via_acyclic, simp add: id)
qed

end
