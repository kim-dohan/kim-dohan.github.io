(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Reduction_Nonterm_Impl
  imports 
    Q_Reduction_Nonterm
    Framework.QDP_Framework_Impl
    TRS.Q_Restricted_Rewriting_Impl
begin

datatype ('f,'v)dp_q_reduction_nonterm_prf = DP_q_reduction_nonterm_prf "('f,'v)term list"

fun dp_q_reduction_nonterm where
  "dp_q_reduction_nonterm I dpp (DP_q_reduction_nonterm_prf Q') = (do {
    let P = dpp_ops.pairs I dpp;
    let R = dpp_ops.rules I dpp;
    let Q = dpp_ops.Q I dpp;
    let nfs  = dpp_ops.nfs I dpp;
    let F = set (funas_trs_list (P @ R));
    let rQ = filter (\<lambda> q. funas_term q \<subseteq> F) Q;
    check_NF_terms_subset (is_NF_terms Q') rQ <+? (\<lambda> q. showsl_lit (STR ''the term '') \<circ> showsl q \<circ> showsl_lit (STR '' is missing in Q' ''));
    return (dpp_ops.mk I nfs False P [] Q' [] R)
  })"

lemma dp_q_reduction_nonterm: fixes "prf" :: "('f :: {compare_order,showl},'v :: showl)dp_q_reduction_nonterm_prf"
  assumes I: "dpp_spec I" 
  and ok: "dp_q_reduction_nonterm I dpp prf = return dpp'"
  and inf: "infinite_dpp (dpp_ops.nfs I dpp', set (dpp_ops.pairs I dpp'), set (dpp_ops.Q I dpp'), set (dpp_ops.rules I dpp'))"
  and infinite: "infinite (UNIV :: 'f set)"
  shows "infinite_dpp (dpp_ops.nfs I dpp, set (dpp_ops.pairs I dpp), set (dpp_ops.Q I dpp), set (dpp_ops.rules I dpp))"
proof -
  obtain Q' where id: "prf = DP_q_reduction_nonterm_prf Q'" by (cases "prf", auto)
  note ok = ok[unfolded id dp_q_reduction_nonterm.simps Let_def]
  interpret dpp_spec I by fact  
  let ?Q    = "set (Q dpp)"
  let ?P    = "set (pairs dpp)"
  let ?R    = "set (rules dpp)"  
  let ?nfs  = "NFS dpp"
  let ?F = "funas_trs ?P \<union> funas_trs ?R" 
  let ?rQ = "{q. q \<in> ?Q \<and> funas_term q \<subseteq> ?F}"
  let ?Q' = "set Q'"
  from ok have NF: "NF_terms ?Q' \<subseteq> NF_terms ?rQ" by auto
  from ok have dpp': "dpp' = mk (NFS dpp) False (pairs dpp) [] Q' [] (rules dpp)" by auto
  note inf = inf[unfolded dpp']
  have inf: "infinite_dpp (?nfs,?P,?rQ,?R)" 
    by (rule infinite_dpp_mono[OF subset_refl subset_refl NF], insert inf, auto)
  show ?thesis
    by (rule infinite_dpp_q_reduction[OF inf _ _ _ infinite], auto)
qed

end
