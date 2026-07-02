(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Reduction_Impl
imports
  Q_Reduction
  Framework.QDP_Framework_Impl
  TRS.Q_Restricted_Rewriting_Impl
begin

definition
  q_reduction_proc_min_inn ::
    "('dpp, 'f::{compare_order,showl}, 'v:: showl) dpp_ops \<Rightarrow>
    ('f,'v)term list \<Rightarrow> 
    'dpp proc"
where
  "q_reduction_proc_min_inn I Q' dpp \<equiv> 
    let Pb  = dpp_ops.pairs I dpp;
        Rb = dpp_ops.rules I dpp;
        F = map Some (funas_trs_list (Pb @ Rb));
        Q = dpp_ops.Q I dpp;
        isnf = dpp_ops.is_QNF I dpp;
        QQ = filter (\<lambda> q. Ball (set (args q)) isnf) Q;
        rQ = filter (\<lambda> q. root q \<in> set F) QQ
 in check_return (do {
  check (dpp_ops.NFQ_subset_NF_rules I dpp) (showsl_lit (STR ''innermost rewriting required''));  
  check_wf_trs Rb;
  check_NF_terms_subset (is_NF_terms Q') rQ <+? (\<lambda> q. showsl_lit (STR ''the term '') \<circ> showsl q \<circ> showsl_lit (STR '' is missing in Q' ''));
  check_NF_terms_subset (is_NF_terms QQ) Q' <+? (\<lambda> q. showsl_lit (STR ''the term '') \<circ> showsl q \<circ> showsl_lit (STR '' is not allowed in Q' ''));
  if (dpp_ops.nfs I dpp) then succeed else check_varcond_subset Pb
  } <+?
  (\<lambda> e. showsl_lit (STR ''problem when reducing Q in the DP problem\<newline>'') \<circ>  
  showsl_dpp I dpp \<circ> showsl_lit (STR ''\<newline>to the set\<newline>'')  
  \<circ> showsl_terms (STR ''Q':'') Q' \<circ> showsl_nl \<circ> e)) 
     (dpp_ops.mk I (dpp_ops.nfs I dpp) (dpp_ops.minimal I dpp) (dpp_ops.P I dpp) (dpp_ops.Pw I dpp) Q' (dpp_ops.R I dpp) (dpp_ops.Rw I dpp))"

lemma q_reduction_proc_min_inn: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (q_reduction_proc_min_inn I (Q' :: ('f :: {compare_order,showl},'v :: showl)term list))"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'    
    assume ok: "q_reduction_proc_min_inn I Q' d = Inr d'" and fin: "finite_dpp (dpp d')"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Pb = "?P \<union> ?Pw"
    let ?Q = "set (Q d)"
    let ?QQ = "{q . set (args q) \<subseteq> NF_terms ?Q \<and> q \<in> ?Q}"
    let ?Q' = "set Q'"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "?R \<union> ?Rw"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?F = "funas_trs ?Pb \<union> funas_trs ?Rb"
    let ?rQ = "{ q. q \<in> ?QQ \<and> root q \<in> Some ` ?F}"
    let ?dpp = "\<lambda> q. (?nfs,?m,?P,?Pw,q,?R,?Rw)"
    note ok = ok[unfolded q_reduction_proc_min_inn_def Let_def dpp_spec_sound, simplified] 
    have NFQQ: "NF_terms ?Q = NF_terms ?QQ"
    proof
      show "NF_terms ?QQ \<supseteq> NF_terms ?Q"
        by (rule NF_terms_anti_mono, auto)
      show "NF_terms ?QQ \<subseteq> NF_terms ?Q"
      proof -
        {
          fix q
          assume "q \<in> ?Q" and "q \<in> NF_terms ?QQ"
          then have False
          proof (induct q rule: wf_induct[OF wf_measure[of size]])
            case (1 q)
            {
              assume "set (args q) \<subseteq> NF_terms ?Q"
              with 1(2) have "q \<in> ?QQ" by auto
              then have "q \<notin> NF_terms ?QQ" by blast
              with 1(3) have False by auto
            }
            then obtain p where pq: "p \<in> set (args q)" and NF: "p \<notin> NF_terms ?Q" by auto
            from NF obtain C q' \<sigma> where p: "p = C \<langle> q' \<cdot> \<sigma> \<rangle>" and q': "q' \<in> ?Q" by auto
            from pq obtain f ts where q: "q = Fun f ts" and pts: "p \<in> set ts" by (cases q, auto)
            from pts[unfolded in_set_conv_decomp] obtain bef aft where ts: "ts = bef @ p # aft" by blast
            let ?C = "More f bef C aft"
            from q ts p have qq': "q = ?C \<langle> q' \<cdot> \<sigma> \<rangle>" by simp
            then have "q \<unrhd> q' \<cdot> \<sigma>" by auto
            from NF_instance[OF NF_subterm[OF 1(3) this]] have q'NF: "q' \<in> NF_terms ?QQ" .
            have "size q' \<le> size (q' \<cdot> \<sigma>)" by (rule size_subst)
            also have "\<dots> \<le> size (C \<langle>q' \<cdot> \<sigma>\<rangle>)" by (rule supteq_size, auto)
            also have "\<dots> < size q" unfolding qq' by simp
            finally show False using 1(1) q' q'NF by auto
          qed
        }
        then show ?thesis unfolding NF_terms_subset_criterion[symmetric]
          by auto
      qed
    qed
    then have nfqq : "NF_terms ?QQ = NF_terms ?Q" by simp
    from ok have inn: "NF_terms ?QQ \<subseteq> NF_trs ?Rb" unfolding nfqq by auto
    from ok have wf: "wf_trs ?Rb" by auto
    from ok have NFQ: "NF_terms ?QQ \<subseteq> NF_terms ?Q'" by force
    from ok have "NF_terms ?Q'
      \<subseteq> NF_terms {q \<in> ?Q.
      (\<forall>t\<in>set (args q). t \<in> NF_terms ?Q) \<and> root q \<in> Some ` ?F}" (is "_ \<subseteq> NF_terms ?QQQ") by auto
    also have "?QQQ = ?rQ" by auto
    finally have NFrQ: "NF_terms ?Q' \<subseteq> NF_terms ?rQ" unfolding nfqq .
    from ok have vars: "\<And> l r.  \<not> NFS d \<Longrightarrow> (l,r) \<in> ?Pb \<Longrightarrow> vars_term r \<subseteq> vars_term l" by force
    from ok have id: "dpp d = ?dpp ?Q" "dpp d' = ?dpp ?Q'" by auto
    {
      fix s t \<sigma>
      assume Qchain: "min_ichain (?dpp ?Q) s t \<sigma>"
      from min_ichain_mono[OF this subset_refl subset_refl NFQQ subset_refl refl]
      have Qchain: "min_ichain (?dpp ?QQ) s t \<sigma>" .
      from min_ichain_reduced_Q[OF inn refl _ _ wf vars Qchain, of ?F]
      have rQchain: "min_ichain (?dpp ?rQ) s t \<sigma>" by auto
      from Qchain have Qchain: "ichain (?dpp ?QQ) s t \<sigma>" by auto
      have Q'chain: "ichain (?dpp ?Q') s t \<sigma>"
        by (rule ichain_mono[OF Qchain], insert NFQ, auto)
      {
        fix i
        from rQchain have SN: "?m \<Longrightarrow> SN_on (qrstep ?nfs ?rQ ?Rb) {t i \<cdot> \<sigma> i}" by (auto simp: minimal_cond_def)
        have SN: "?m \<Longrightarrow> SN_on (qrstep ?nfs ?Q' ?Rb) {t i \<cdot> \<sigma> i}"
          by (rule SN_on_mono[OF SN qrstep_mono], insert NFrQ, auto)
      }
      with Q'chain
      have "min_ichain (?dpp ?Q') s t \<sigma>" by (auto simp: minimal_cond_def)
    }
    with fin      
    show "finite_dpp (dpp d)" unfolding id finite_dpp_def by blast
  qed
qed

definition
  q_reduction_proc_non_min ::
    "('dpp, 'f:: showl, 'v:: showl) dpp_ops \<Rightarrow>
    ('f,'v)term list \<Rightarrow> 
    'dpp proc"
where
  "q_reduction_proc_non_min I Q' dpp \<equiv> 
  check_return (do {
   check_NF_terms_subset (dpp_ops.is_QNF I dpp) Q' <+? (\<lambda> q. showsl_lit (STR ''the term '') \<circ> showsl q \<circ> showsl_lit (STR '' is not allowed in Q' ''));
   succeed
  } <+?
  (\<lambda> e. showsl_lit (STR ''problem when reducing Q in the DP problem\<newline>'') \<circ>  
  showsl_dpp I dpp \<circ> showsl_lit (STR ''\<newline>to the set\<newline>'') 
  \<circ> showsl_terms (STR ''Q':'') Q' \<circ> showsl_nl \<circ> e)) 
     (dpp_ops.mk I (dpp_ops.nfs I dpp) False (dpp_ops.P I dpp) (dpp_ops.Pw I dpp) Q' (dpp_ops.R I dpp) (dpp_ops.Rw I dpp))"

lemma q_reduction_proc_non_min: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (q_reduction_proc_non_min I (Q' :: ('f :: showl,'v :: showl)term list))"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'    
    assume ok: "q_reduction_proc_non_min I Q' d = Inr d'" and fin: "finite_dpp (dpp d')"
    let ?Q = "set (Q d)"
    let ?Q' = "set Q'"
    let ?m = "M d"
    let ?dpp = "\<lambda> m q. (NFS d,m,set (P d),set (Pw d),q,set (R d),set (Rw d))"
    note ok = ok[unfolded q_reduction_proc_non_min_def Let_def dpp_spec_sound, simplified] 
    from ok have NF: "NF_terms ?Q \<subseteq> NF_terms ?Q'" and 
      d': "d' = mk (NFS d) False (P d) (Pw d) Q' (R d) (Rw d)" by auto
    {
      fix s t \<sigma>
      assume "min_ichain (?dpp ?m ?Q) s t \<sigma>"
      then have "ichain (?dpp ?m ?Q) s t \<sigma>" by auto
      from ichain_reduced_Q[OF NF this] have "ichain (?dpp ?m ?Q') s t \<sigma>" .
      then have "min_ichain (?dpp False ?Q') s t \<sigma>" by (simp add: minimal_cond_def ichain.simps)
      with fin have False unfolding d' finite_dpp_def by auto
    }
    then show "finite_dpp (dpp d)" unfolding finite_dpp_def by auto
  qed
qed

(* try to keep minimality, otherwise use more applicable version, which
  drops minimality *)
definition
  q_reduction_proc ::
    "('dpp, 'f::{compare_order,showl}, 'v:: showl) dpp_ops \<Rightarrow>
    ('f,'v)term list \<Rightarrow> 
    'dpp proc" where
  "q_reduction_proc I Q' dpp \<equiv> 
    case (q_reduction_proc_min_inn I Q' dpp) of return dpp' \<Rightarrow> return dpp'
    | _ \<Rightarrow> q_reduction_proc_non_min I Q' dpp"

lemma q_reduction_proc: assumes I: "dpp_spec I"
 shows "dpp_spec.sound_proc_impl I (q_reduction_proc I (Q' :: ('f :: {compare_order,showl},'v :: showl)term list))"
proof -
  from assms interpret dpp_spec I .
  show ?thesis
  proof
    fix d d'
    assume ok: "q_reduction_proc I Q' d = Inr d'" and fin: "finite_dpp (dpp d')"
    note ok = ok[unfolded q_reduction_proc_def]
    show "finite_dpp (dpp d)"
    proof (cases "q_reduction_proc_min_inn I Q' d")
      case (Inr d'')
      with ok sound_proc_impl[OF q_reduction_proc_min_inn[OF I] Inr] fin show ?thesis by auto
    next
      case Inl
      with ok have ok: "q_reduction_proc_non_min I Q' d = Inr d'" by auto
      from sound_proc_impl[OF q_reduction_proc_non_min[OF I] ok fin] show ?thesis .
    qed
  qed
qed

end
