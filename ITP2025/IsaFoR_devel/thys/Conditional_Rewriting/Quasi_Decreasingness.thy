(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014, 2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015, 2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Quasi_Decreasingness
imports
  Conditional_Rewriting
begin

definition "quasi_reductive_order R S \<longleftrightarrow>
  trans S \<and> SN S \<and>
  ctxt.closed S \<and>
  (\<forall> l r cs (\<sigma> :: ('f, 'v) subst). ((l, r), cs) \<in> R \<longrightarrow> 
    (\<forall> i. i < length cs \<longrightarrow> (\<forall>j < i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S\<^sup>=) \<longrightarrow>
      (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> (S \<union> {\<rhd>})\<^sup>+) \<and> 
        ((\<forall>j < length cs. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S\<^sup>=) \<longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S))"

definition "quasi_decreasing_order R S \<longleftrightarrow> 
  (trans S \<and> SN S \<and> 
  cstep R \<subseteq> S \<and> {\<rhd>} \<subseteq> S \<and> 
  (\<forall> l r cs (\<sigma> :: ('f, 'v) subst). ((l, r), cs) \<in> R \<longrightarrow> 
    (\<forall> i. i < length cs \<longrightarrow> (\<forall>j < i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>* ) \<longrightarrow>
      (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> S)))"

definition "quasi_reductive R \<longleftrightarrow> (\<exists>S. quasi_reductive_order R S)"

definition "quasi_decreasing R \<longleftrightarrow> (\<exists>S. quasi_decreasing_order R S)"

lemma quasi_reductive_order_cstep:
  assumes "quasi_reductive_order (R :: ('f, 'v) ctrs) S"
  shows "cstep R \<subseteq> S"
proof -
  from assms [unfolded quasi_reductive_order_def]
  have trans: "trans S"
  and mono: "ctxt.closed S"
  and qr: "\<And> l r cs (\<sigma> :: ('f,'v)subst).
             ((l, r), cs) \<in> R \<Longrightarrow>
             (\<forall>j<length cs. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S^=) \<Longrightarrow> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S" by auto
  show "cstep R \<subseteq> S"
  proof
    fix s t
    assume "(s,t) \<in> cstep R"
    then obtain n where "(s,t) \<in> cstep_n R n" unfolding cstep_def by auto
    then show "(s,t) \<in> S"
    proof (induct n arbitrary: s t)
      case (Suc n s t)
      from Suc(2)
      obtain l r cs C \<sigma> where lr: "((l,r),cs) \<in> R" and
        cs: "\<And> s\<^sub>i t\<^sub>i.  (s\<^sub>i,t\<^sub>i) \<in> set cs \<Longrightarrow> (s\<^sub>i \<cdot> \<sigma>, t\<^sub>i \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*"
        and s: "s = C \<langle> l \<cdot> \<sigma> \<rangle>" and t: "t = C \<langle> r \<cdot> \<sigma> \<rangle>" by (blast elim: cstep_n_SucE)
      note qr = qr[OF lr, of \<sigma>]
      have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> S"
      proof (rule qr[rule_format])
        fix j
        assume j: "j < length cs"
        obtain sj tj where csj: "cs ! j = (sj,tj)" by force
        from j have "(sj,tj) \<in> set cs" unfolding csj[symmetric] set_conv_nth by auto
        from cs[OF this] have steps: "(sj \<cdot> \<sigma>, tj \<cdot> \<sigma>) \<in> (cstep_n R n)\<^sup>*" .
        {
          fix s t
          assume "(s,t) \<in> (cstep_n R n)\<^sup>*"
          then have "(s,t) \<in> S^="
          proof (induct)
            case (step t u)
            from step(3) Suc(1)[OF step(2)] have "(s,u) \<in> S^= O S" by auto
            then show "(s,u) \<in> S^=" using trans[unfolded trans_def] by blast
          qed simp
        }
        from this[OF steps]
        show "(fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S^=" unfolding csj by simp
      qed 
      from ctxt.closedD[OF mono this, of C]
      show ?case unfolding s t .
    qed simp
  qed
qed

lemma quasi_reductive_order_quasi_decreasing_order: 
  assumes qro: "quasi_reductive_order (R :: ('f, 'v) ctrs) S"
  shows "quasi_decreasing_order R ((S \<union> {\<rhd>})\<^sup>+)"
proof -
  let ?S = "(S \<union> {\<rhd>})\<^sup>+"
  from quasi_reductive_order_cstep[OF qro] have "cstep R \<subseteq> S" by auto
  then have "cstep R \<subseteq> ?S" by auto
  from qro[unfolded quasi_reductive_order_def]
  have trans: "trans S" and SN: "SN S"
  and mono: "ctxt.closed S"
  and decr: "\<And> l r cs i (\<sigma> :: ('f,'v)subst).
             ((l, r), cs) \<in> R \<Longrightarrow>
              i  < length cs \<Longrightarrow>
               (\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S\<^sup>=) \<Longrightarrow> (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> ?S" 
    by auto
  from mono SN have "SN (S \<union> {\<rhd>})" by (metis SN_imp_SN_union_supt)
  then have "SN ?S" unfolding SN_trancl_SN_conv .
  have "trans ?S" by simp
  have "{\<rhd>} \<subseteq> ?S" by auto
  show ?thesis unfolding quasi_decreasing_order_def
  proof (intro conjI, rule \<open>trans ?S\<close>, rule \<open>SN ?S\<close>, rule \<open>cstep R \<subseteq> ?S\<close>, rule \<open>{\<rhd>} \<subseteq> ?S\<close>, intro allI impI)
    fix l r cs \<sigma> i
    assume lr: "((l,r), cs) \<in> R" and i: "i < length cs"
     and args: "\<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
    show "(l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> ?S"
    proof (rule decr[OF lr i], intro allI impI)
      fix j
      assume "j < i"
      with args have "(fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" by auto
      also have "(cstep R)\<^sup>* \<subseteq> S^*" by (rule rtrancl_mono[OF \<open>cstep R \<subseteq> S\<close>])
      also have "S^* = (S^+)^=" by regexp
      also have "S^+ = S" using trans by auto
      finally show "(fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> S^=" .
    qed
  qed
qed

lemma quasi_reductive_quasi_decreasing: 
  "quasi_reductive R \<Longrightarrow> quasi_decreasing R"
  unfolding quasi_reductive_def quasi_decreasing_def
    using quasi_reductive_order_quasi_decreasing_order by blast

lemma quasi_decreasing_SN:
  assumes qd: "quasi_decreasing R"
  shows "SN (cstep R)"
proof -
  from qd[unfolded quasi_decreasing_def] obtain S where "quasi_decreasing_order R S" by blast
  from this[unfolded quasi_decreasing_order_def] have "SN S" and "cstep R \<subseteq> S" by auto
  then show ?thesis
    by (rule SN_subset)
qed

lemma quasi_reductive_SN:
  "quasi_reductive R \<Longrightarrow> SN (cstep R)"
  by (rule quasi_decreasing_SN[OF quasi_reductive_quasi_decreasing])


lemma quasi_reductive_order_csteps:
  assumes "quasi_reductive_order R S"
  shows "(cstep R)\<^sup>* \<subseteq> S\<^sup>="
proof -
  from assms have trans: "trans S" and RsubS: "cstep R \<subseteq> S"
    using quasi_reductive_order_cstep [OF assms] by (auto simp: quasi_reductive_order_def)
  have "(cstep R)\<^sup>* \<subseteq> S^*" by (rule rtrancl_mono[OF RsubS])
  also have "S^* = (S^+)^=" by regexp
  also have "S^+ = S" using trans by auto
  finally show ?thesis by blast
qed

lemma quasi_reductive_obtains_normalized_subst:
  assumes "quasi_reductive_order R S"
  obtains \<tau> where "normalized R \<tau>" and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
    and "\<tau> = (\<lambda>x. some_NF (cstep R) (\<sigma> x))"
proof -
  have *: "SN (cstep R)" using assms using quasi_reductive_SN quasi_reductive_def by auto
  define \<tau> where "\<tau> \<equiv> \<lambda>x. some_NF (cstep R) (\<sigma> x)"
  { fix x
    from * have "(\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" unfolding \<tau>_def by (simp add: SN_def some_NF)
    then have "(\<sigma>  x, \<tau> x) \<in> (cstep R)\<^sup>*" by auto
  }
  then have "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" by auto
  moreover have "normalized R \<tau>" by (auto simp: normalized_def) (metis SN_def * \<tau>_def some_NF)
  ultimately obtain \<tau> where "normalized R \<tau>" and  "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
    and "\<tau> = (\<lambda>x. some_NF (cstep R) (\<sigma> x))" using \<tau>_def by blast
  then show ?thesis ..
qed

lemma quasi_decreasing_order_csteps:
  assumes "quasi_decreasing_order R S"
  shows "(cstep R)\<^sup>* \<subseteq> S\<^sup>="
proof -
  from assms have trans: "trans S" and RsubS: "cstep R \<subseteq> S"
    by (auto simp: quasi_decreasing_order_def)
  have "(cstep R)\<^sup>* \<subseteq> S^*" by (rule rtrancl_mono[OF RsubS])
  also have "S^* = (S^+)^=" by regexp
  also have "S^+ = S" using trans by auto
  finally show ?thesis by blast
qed

lemma quasi_decreasing_order_conds_sat:
  assumes qd: "quasi_decreasing_order R S"
    and rule: "((l, r), cs) \<in> R"
    and cs: "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*"
  shows "\<forall>i < length cs. (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> (S \<union> {\<rhd>})\<^sup>+"
proof -
  from quasi_decreasing_order_csteps [OF qd] have "(cstep R)\<^sup>* \<subseteq> S\<^sup>=" .
  moreover from qd [unfolded quasi_decreasing_order_def]
    have *: "\<forall>l r cs \<sigma>. ((l, r), cs) \<in> R \<longrightarrow>
    (\<forall>i < length cs. (\<forall>j < i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*) \<longrightarrow>
    (l \<cdot> \<sigma>, fst (cs ! i) \<cdot> \<sigma>) \<in> (S \<union> {\<rhd>})\<^sup>+)" by blast
  ultimately have "\<forall>(s, t) \<in> set cs. (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" using cs by blast
  then have "\<forall>i < length cs. \<forall>j<i. (fst (cs ! j) \<cdot> \<sigma>, snd (cs ! j) \<cdot> \<sigma>) \<in> (cstep R)\<^sup>*" by force
  with * rule show ?thesis by auto
qed

lemma quasi_decreasing_obtains_normalized_subst:
  assumes "quasi_decreasing_order R S"
  obtains \<tau> where "normalized R \<tau>" and "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
    and "\<tau> = (\<lambda>x. some_NF (cstep R) (\<sigma> x))"
proof -
  have *: "SN (cstep R)" using assms using quasi_decreasing_SN quasi_decreasing_def by auto
  define \<tau> where "\<tau> \<equiv> \<lambda>x. some_NF (cstep R) (\<sigma> x)"
  { fix x
    from * have "(\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" unfolding \<tau>_def by (simp add: SN_def some_NF)
    then have "(\<sigma>  x, \<tau> x) \<in> (cstep R)\<^sup>*" by auto
  }
  then have "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*" by auto
  moreover have "normalized R \<tau>" by (auto simp: normalized_def) (metis SN_def * \<tau>_def some_NF)
  ultimately obtain \<tau> where "normalized R \<tau>" and  "\<forall>x. (\<sigma> x, \<tau> x) \<in> (cstep R)\<^sup>*"
    and "\<tau> = (\<lambda>x. some_NF (cstep R) (\<sigma> x))" using \<tau>_def by blast
  then show ?thesis ..
qed

end
