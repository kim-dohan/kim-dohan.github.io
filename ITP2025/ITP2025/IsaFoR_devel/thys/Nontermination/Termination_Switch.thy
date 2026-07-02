(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Termination_Switch
imports
  Nontermination
  Innermost_Switch
begin

lemma five_chain_into_three_chain: 
  assumes "ichain (nfs,m,P,{},Q,{},R) s t sigma"
  shows "i_chain (nfs,P,Q,R) s t sigma"
proof -
  note nfsub = NF_subterm[OF _ supt_imp_supteq, of _ "Id_on Q"]
  from nfsub have a: "\<forall>i. s i \<cdot> sigma i \<in> NF_terms Q \<Longrightarrow> \<forall>i u. s i \<cdot> sigma i \<rhd> u \<longrightarrow> u \<in> NF_terms Q" by blast
  from assms a show ?thesis unfolding ichain.simps i_chain.simps by force
qed

lemma three_chain_into_five_chain: "i_chain (nfs,P,{},R) s t sigma \<Longrightarrow> ichain (nfs,m,P,{},{},{},R) s t sigma" 
  by (simp add: ichain.simps)

lemma termination_switch_proc:
  assumes inf: "infinite_dpp (nfs,P,{},R)"
  and crit: "critical_pairs ren P R = {}"
  and WCR: "WCR (rstep R)"
  and NF: "NF_trs R \<subseteq> NF_terms Q"
  and var: "\<And> l r. nfs \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  and SN: "SN (qrstep nfs Q R) \<Longrightarrow> SN (rstep R)"
  shows "infinite_dpp (nfs,P,Q,R)"
proof (cases "SN (qrstep nfs Q R)")
  case False
  then show ?thesis by simp
next
  case True
  from True SN have SNR: "SN (rstep R)" by simp
  let ?dppT = "(nfs,True,P,{},{},{},R)"
  let ?dppI = "(nfs, True,P,{},lhss R,{},R)"
  from inf SNR have nchain: "\<exists> s t sigma. i_chain(nfs,P,{},R) s t sigma" unfolding infinite_dpp.simps by force
  then obtain s t sigma where nchain: "i_chain(nfs,P,{},R) s t sigma" by blast
  then have nchain: "ichain ?dppT s t sigma" by (rule three_chain_into_five_chain)
  with SNR have chain: "min_ichain ?dppT s t sigma" 
    by (simp add: minimal_cond_def SN_def)
  then have nfin: "\<not> finite_dpp ?dppT" unfolding finite_dpp_def by blast
  from crit have crit: "critical_pairs ren (P \<union> {}) R = {}" by auto
  have NFempty: "NF_trs R \<subseteq> NF_terms {}" by auto
  from WCR have WCR: "WCR_on (qrstep nfs {} R) {t. SN_on (qrstep nfs {} R) {t}}" 
    unfolding WCR_on_def by auto
  note inn_switch = switch_to_innermost_proc[OF WCR NFempty crit TrueI var]
  have "\<not> finite_dpp ?dppI" using inn_switch and nfin by fast
  then obtain s t sigma where ichain: "ichain ?dppI s t sigma" 
    unfolding finite_dpp_def by auto
  have ichain : "ichain (nfs,True,P,{},Q,{},R) s t sigma"
  proof (rule ichain_mono[OF ichain])
    show "NF_terms (lhss R) \<subseteq> NF_terms Q" using NF by auto
  qed auto
  then have ichain: "i_chain (nfs,P,Q,R) s t sigma" by (rule five_chain_into_three_chain)
  then show ?thesis unfolding infinite_dpp.simps by blast
qed

end
