theory Commutation
  imports 
    First_Order_Rewriting.Trs
    TRS.More_Abstract_Rewriting
begin

text \<open>Since commutation is a property that depends on the signature, we define a signature based
  version of commutation where just the starting terms of peaks have to respect the signature.
  The advantage is that it uses the unrestricted rewrite relation @{const rstep}.\<close>
definition sig_commute :: "'f sig \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "sig_commute F R S = (\<forall> t s r. funas_term t \<subseteq> F \<longrightarrow> (t,s) \<in> (rstep S)^* \<longrightarrow> (t,r) \<in> (rstep R)^*
    \<longrightarrow> (\<exists> u. (s,u) \<in> (rstep R)^* \<and> (r,u) \<in> (rstep S)^*))"  

lemma sig_commuteI[intro]: 
  assumes "\<And> s t r. funas_term t \<subseteq> F \<Longrightarrow> (t,s) \<in> (rstep S)^* \<Longrightarrow> (t,r) \<in> (rstep R)^* \<Longrightarrow> 
     \<exists> u. (s,u) \<in> (rstep R)^* \<and> (r,u) \<in> (rstep S)^*" 
  shows "sig_commute F R S" 
  using assms unfolding sig_commute_def by auto

lemma sig_commuteD[dest]: 
  assumes "sig_commute F R S" 
  shows "funas_term t \<subseteq> F \<Longrightarrow> (t,s) \<in> (rstep S)^* \<Longrightarrow> (t,r) \<in> (rstep R)^* \<Longrightarrow> 
     \<exists> u. (s,u) \<in> (rstep R)^* \<and> (r,u) \<in> (rstep S)^*" 
  using assms unfolding sig_commute_def by auto
   


abbreviation sig_rstep :: "'f sig \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs" where
  "sig_rstep F R \<equiv> sig_step F (rstep R)" 

lemma sig_rstep_if_rstep: 
  "wf_trs R \<Longrightarrow> funas_trs R \<subseteq> F \<Longrightarrow> funas_term t \<subseteq> F \<Longrightarrow> (t,s) \<in> rstep R \<Longrightarrow> (t,s) \<in> sig_rstep F R \<and> funas_term s \<subseteq> F" 
  using rstep_preserves_funas_terms by blast

lemma sig_rsteps_if_rsteps: assumes "wf_trs R" "funas_trs R \<subseteq> F"
    "funas_term t \<subseteq> F"
    "(t,s) \<in> (rstep R)^*"
  shows "(t,s) \<in> (sig_rstep F R)^* \<and> funas_term s \<subseteq> F" 
  using assms(4,3) 
proof (induct rule: rtrancl_induct)
  case step
  then show ?case using sig_rstep_if_rstep[OF assms(1-2) _ step(2)] by auto
qed auto

lemma rsteps_if_sig_rsteps: 
  assumes "(t,s) \<in> (sig_rstep F R)^*"
  shows "(t,s) \<in> (rstep R)^*"
  using assms rtrancl_mono[of "sig_rstep F R" "rstep R"] 
    by (metis (no_types, lifting) sig_stepE subrelI subsetD)+


text \<open>@{const sig_commute} is sensible in the way that for well-formed TRSs it is exactly
  commutation of the signature restricted version of rewriting @{const sig_rstep}.\<close>
lemma sig_commute_commute: assumes wf: "wf_trs R" "wf_trs S" 
  and sig: "funas_trs R \<subseteq> F" "funas_trs S \<subseteq> F"
  shows "sig_commute F R S \<longleftrightarrow> commute (sig_rstep F R) (sig_rstep F S)"
proof 
  assume comm: "sig_commute F R S" 
  show "commute (sig_rstep F R) (sig_rstep F S)" 
  proof
    fix t r s
    assume ts: "(t,s) \<in> (sig_rstep F S)^*" and tr: "(t,r) \<in> (sig_rstep F R)^*" 
    hence ts': "(t,s) \<in> (rstep S)^*" and tr': "(t,r) \<in> (rstep R)^*" 
      using rsteps_if_sig_rsteps by auto
    show "\<exists>z. (r, z) \<in> (sig_rstep F S)^* \<and> (s, z) \<in> (sig_rstep F R)^*" 
    proof (cases "funas_term t \<subseteq> F")
      case t: True
      from sig_commuteD[OF comm t ts' tr'] obtain u where su: "(s, u) \<in> (rstep R)\<^sup>*" 
        and ru: "(r, u) \<in> (rstep S)\<^sup>*" by auto
      from sig_rsteps_if_rsteps[OF wf(2) sig(2) t ts']
        sig_rsteps_if_rsteps[OF wf(1) sig(1) _ su]
      have su: "(s, u) \<in> (sig_rstep F R)^*" by auto 
      from sig_rsteps_if_rsteps[OF wf(1) sig(1) t tr']
        sig_rsteps_if_rsteps[OF wf(2) sig(2) _ ru]
      have ru: "(r, u) \<in> (sig_rstep F S)^*" by auto 
      from su ru show ?thesis by auto
    next
      case False
      have "(t,s) \<in> (sig_rstep F R)^* \<Longrightarrow> s = t" for R s
        by (induct rule: rtrancl_induct, insert False, auto)
      from this[OF ts] this[OF tr] show ?thesis by auto
    qed
  qed
next
  assume comm: "commute (sig_rstep F R) (sig_rstep F S)"  
  show "sig_commute F R S" 
  proof
    fix s t r
    assume t: "funas_term t \<subseteq> F" and ts: "(t, s) \<in> (rstep S)\<^sup>*" and tr: "(t, r) \<in> (rstep R)\<^sup>*" 
    from sig_rsteps_if_rsteps[OF wf(1) sig(1) t tr] have tr': "(t, r) \<in> (sig_rstep F R)\<^sup>*" by auto
    from sig_rsteps_if_rsteps[OF wf(2) sig(2) t ts] have ts': "(t, s) \<in> (sig_rstep F S)\<^sup>*" by auto
    from commuteE[OF comm tr' ts'] obtain u where 
      ru: "(r, u) \<in> (sig_rstep F S)\<^sup>*" and su: "(s, u) \<in> (sig_rstep F R)\<^sup>*" by auto
    from rsteps_if_sig_rsteps[OF ru] rsteps_if_sig_rsteps[OF su]
    show "\<exists>u. (s, u) \<in> (rstep R)\<^sup>* \<and> (r, u) \<in> (rstep S)\<^sup>*" by auto
  qed
qed

lemma commute_imp_sig_commute: assumes "commute (rstep R) (rstep S)" 
  shows "sig_commute F R S" 
  by (intro sig_commuteI, insert commuteE[OF assms], auto)

lemma sig_commute_swap: "sig_commute F R S \<Longrightarrow> sig_commute F S R" 
  by (intro sig_commuteI, drule sig_commuteD, auto)

end