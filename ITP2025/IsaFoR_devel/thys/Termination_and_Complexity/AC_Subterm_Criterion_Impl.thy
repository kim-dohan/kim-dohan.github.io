(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>AC Subterm Criterion -- Implementation\<close>

theory AC_Subterm_Criterion_Impl
imports
  Ord.Subterm_Multiset
  Ord.Status_Impl
  Ord.Term_Order_Impl
  Weighted_Path_Order.Multiset_Extension2_Impl
  Framework.AC_Dependency_Pair_Problem_Spec
  Framework.Dependency_Pair_Problem_Spec
  AC_TRS.AC_Rewriting_Impl
  AC_Subterm_Criterion
begin

lemma irrefl_imp_irrefl_on: "irrefl R \<Longrightarrow> irrefl_on A R"
  unfolding irrefl_on_def by auto

lemma suptmulexeq_impl [code_unfold]:
  "M \<unrhd>\<^sub># N = multeqp_code (\<lambda>x y. supt_impl y x) N M"
proof -
  have *: "multeqp_code (\<lambda>x y. supt_impl y x) N M \<longleftrightarrow> (N, M) \<in> (mult {\<lhd>})\<^sup>="
    by (rule multeqp_code_iff_reflcl_mult [OF irrefl_imp_irrefl_on[OF irrefl_subt] trans_subt])
      (auto simp: supt_impl)
  show ?thesis
    using mult_subt_converse and suptmulex_eq
    unfolding * by fastforce
qed

lemma suptmulex_impl [code_unfold]:
  "M \<rhd>\<^sub># N \<longleftrightarrow> multeqp_code (\<lambda>x y. supt_impl y x) N M \<and> M \<noteq> N"
by (auto simp: suptmulexeq_impl [symmetric] s_ns_mul_ext suptmulex_not_refl suptmulex_eq)

definition [simp]: "strict_supt_mul = suptproj_pred"

definition [simp]:"weak_supt_mul = suptprojeq_pred"

definition check_suptproj_pred :: "'f status \<Rightarrow> 'f sig \<Rightarrow> ('f :: showl, 'v :: showl)rule \<Rightarrow> showsl check" where
  "check_suptproj_pred \<pi> F lr = check (case lr of (l, r) \<Rightarrow> strict_supt_mul \<pi> F l r) 
     (showsl_lit (STR ''could not orient rule '') o showsl_rule lr o showsl_lit (STR '' by supt^mul''))"

definition check_supteqproj_pred :: "'f status \<Rightarrow> 'f sig \<Rightarrow> ('f :: showl, 'v :: showl) rule \<Rightarrow> showsl check" where
  "check_supteqproj_pred \<pi> F lr = check (case lr of (l, r) \<Rightarrow> weak_supt_mul \<pi> F l r) 
     (showsl_lit (STR ''could not orient rule '') o showsl_rule lr o showsl_lit (STR '' by supteq^mul''))"

lemma check_suptproj_pred [simp]:
  "isOK (check_suptproj_pred \<pi> F lr) = suptproj_pred \<pi> F (fst lr) (snd lr)"
unfolding check_suptproj_pred_def by auto

lemma check_supteqproj_pred [simp]:
  "isOK (check_supteqproj_pred \<pi> F lr) = suptprojeq_pred \<pi> F (fst lr) (snd lr)"
unfolding check_supteqproj_pred_def by auto

definition
  ac_subterm_proc ::
    "('dpp, 'f :: showl, 'v :: showl) ac_dpp_ops \<Rightarrow> 'f status_impl \<Rightarrow>
     ('f, 'v)rules \<Rightarrow> 'dpp proc"
where
  "ac_subterm_proc I pi P_remove dpp = check_return (do {
     let P = ac_dpp_ops.pairs I dpp;
     let R = ac_dpp_ops.rules I dpp;
     let E = ac_dpp_ops.E I dpp;
     let RE = R @ E;
     let F = map fst pi;
     let FF = set F;
     let pi_opt = status_of pi;
     check (pi_opt \<noteq> None) (showsl_lit (STR ''argument filter lists invalid positions''));
     let \<pi> = the pi_opt;
     let Premove = set P_remove;
     let (ps, pns) = partition (\<lambda> lr. lr \<in> Premove) P;
     check_allm (\<lambda> f. check (status \<pi> f \<noteq> []) 
       (showsl_lit (STR ''status of symbol '') o showsl f o showsl_lit (STR '' in F must be non-empty''))) F;
     check_size_preserving_trs E 
       <+? (\<lambda> s. showsl_lit (STR ''E is not size preserving\<newline>'') o s);
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) RE;        
     check_allm (check_supteqproj_pred \<pi> FF) (filter (\<lambda> lr. the (root (fst lr)) \<in> FF) RE)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting rules with root in F\<newline>'') o s);
     check_allm (check_supteqproj_pred \<pi> FF) pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s);
     check_allm (check_suptproj_pred \<pi> FF) ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the AC subterm processor\<newline>'') o s))
   (ac_dpp_ops.delete_pairs_rules I dpp P_remove [])"

lemma (in ac_dpp_spec) ac_subterm_proc:
  shows "sound_proc_impl (ac_subterm_proc I pi ps)"
proof 
  fix d d'
  assume fin: "finite_rel_dpp (ac_dpp d')"
    and ok: "ac_subterm_proc I pi ps d = return d'"
  define F where "F = map fst pi"
  define \<pi> where "\<pi> = the (status_of pi)"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?PP = "?P \<union> ?Pw"
  let ?R = "set (R d)"
  let ?Rw = "set (Rw d)"
  let ?E = "set (E d)"
  let ?RE = "?R \<union> ?Rw \<union> ?E"
  let ?Sup = "suptproj_pred \<pi> (set F)"
  let ?SupEq = "suptprojeq_pred \<pi> (set F)"
  obtain Ps Pns where p: "partition (\<lambda> lr. lr \<in> set ps) (pairs d) = (Ps,Pns)" by force
  note ok = ok[unfolded ac_subterm_proc_def Let_def p split, folded F_def \<pi>_def, simplified]
  from ok have var: "\<And> l r. (l, r)\<in> ?RE \<Longrightarrow> is_Fun l"
      and size: "size_preserving_trs (set (E d))"
      and d': "d' = ac_dpp_ops.delete_pairs_rules I d ps []"
      and \<pi>: "\<forall>f\<in> set F. status \<pi> f \<noteq> []"
      and supt: "\<And> l r. (l,r) \<in> set Ps \<Longrightarrow> ?Sup l r"
      and supteq: "\<And> l r. (l,r) \<in> set Pns \<Longrightarrow> ?SupEq l r"
    by auto
  {
    fix l r
    assume "(l,r) \<in> ?PP"
    with p have "(l,r) \<in> set Ps \<union> set Pns" by auto
    with s_ns_mul_ext[OF supt[of l r]] supteq[of l r] have "?SupEq l r" by auto
  } note PP = this
  {
    fix l r
    assume lr: "(l,r) \<in> ?RE" and "root l \<in> Some ` set F"
    with ok have rt: "the (root l) \<in> set F" by (cases l, auto)
    from ok have "(l,r) \<in> ?RE \<Longrightarrow> the (root (fst (l,r))) \<in> set F \<Longrightarrow> ?SupEq (fst (l,r)) (snd (l,r))"
      by blast
    with rt lr have "?SupEq l r" by auto
  } note RE = this
  have id: "?PP = set (pairs d)" "?RE = set (R d @ Rw d @ E d)" by auto
  note fin = fin[unfolded d' delete_pairs_rules_sound, simplified]
  show "finite_rel_dpp (ac_dpp d)" unfolding ac_dpp_sound
    by (rule ac_subterm_proc[OF \<pi> fin PP RE supt size var], insert p, auto)
qed

definition
  generalized_subterm_proc ::
    "('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow> 'f status_impl \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 'dpp proc"
where
  "generalized_subterm_proc I pi P_remove dpp = check_return (do {
     let P = dpp_ops.pairs I dpp;
     let R = dpp_ops.rules I dpp;
     let F = map fst pi;
     let FF = set F;
     let pi_opt = status_of pi;
     check (dpp_ops.Q I dpp = []) (showsl_lit (STR ''currently generalized subterm criterion does not support strategies''));
     check (dpp_ops.minimal I dpp) (showsl_lit (STR ''minimality required''));
     check (pi_opt \<noteq> None) (showsl_lit (STR ''argument filter lists invalid positions''));
     let \<pi> = the pi_opt;
     let Premove = set P_remove;
     let (ps, pns) = partition (\<lambda> lr. lr \<in> Premove) P;
     check_allm (\<lambda> f. check (status \<pi> f \<noteq> []) 
       (showsl_lit (STR ''status of symbol '') o showsl f o showsl_lit (STR '' in F must be non-empty''))) F;
     check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''variables as lhss not allowed''))) R;        
     check_allm (check_supteqproj_pred \<pi> FF) (filter (\<lambda> lr. the (root (fst lr)) \<in> FF) R)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting rules with root in F\<newline>'') o s);
     check_allm (check_supteqproj_pred \<pi> FF) pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s);
     check_allm (check_suptproj_pred \<pi> FF) ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the subterm processor\<newline>'') o s))
   (dpp_ops.delete_P_Pw I dpp P_remove P_remove)"

lemma (in dpp_spec) generalized_subterm_proc:
  shows "sound_proc_impl (generalized_subterm_proc I pi ps)"
proof 
  fix d d'
  assume fin: "finite_dpp (dpp d')"
    and ok: "generalized_subterm_proc I pi ps d = return d'"
  define F where "F = map fst pi"
  define \<pi> where "\<pi> = the (status_of pi)"
  let ?P = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?PP = "?P \<union> ?Pw"
  let ?R = "set (R d)"
  let ?Q = "set (Q d)"
  let ?Rw = "set (Rw d)"
  let ?RE = "?R \<union> ?Rw"
  let ?M = "M d"
  let ?Sup = "suptproj_pred \<pi> (set F)"
  let ?SupEq = "suptprojeq_pred \<pi> (set F)"
  obtain Ps Pns where p: "partition (\<lambda> lr. lr \<in> set ps) (pairs d) = (Ps,Pns)" by force
  note ok = ok[unfolded generalized_subterm_proc_def Let_def p split, folded F_def \<pi>_def, simplified]
  from ok have var: "\<And> l r. (l, r)\<in> ?RE \<Longrightarrow> is_Fun l"
      and d': "d' = dpp_ops.delete_P_Pw I d ps ps"
      and \<pi>: "\<forall>f\<in> set F. status \<pi> f \<noteq> []"
      and supt: "\<And> l r. (l,r) \<in> set Ps \<Longrightarrow> ?Sup l r"
      and supteq: "\<And> l r. (l,r) \<in> set Pns \<Longrightarrow> ?SupEq l r"
      and Q: "?Q = {}" and M: "?M = True"
    by auto
  {
    fix l r
    assume "(l,r) \<in> ?PP"
    with p have "(l,r) \<in> set Ps \<union> set Pns" by auto
    with s_ns_mul_ext[OF supt[of l r]] supteq[of l r] have "?SupEq l r" by auto
  } note PP = this
  {
    fix l r
    assume lr: "(l,r) \<in> ?RE" and "root l \<in> Some ` set F"
    with ok have rt: "the (root l) \<in> set F" by (cases l, auto)
    from ok have "(l,r) \<in> ?RE \<Longrightarrow> the (root (fst (l,r))) \<in> set F \<Longrightarrow> ?SupEq (fst (l,r)) (snd (l,r))"
      by simp
    with rt lr have "?SupEq l r" by auto
  } note RE = this
  have id: "?PP = set (pairs d)" "?RE = set (R d @ Rw d)" by auto
  note fin = fin[unfolded d' delete_P_Pw_sound M Q, simplified]
  show "finite_dpp (dpp d)" unfolding dpp_sound Q M
    by (rule generalized_subterm_proc[OF \<pi> fin PP RE supt var], insert p, auto)
qed

end
