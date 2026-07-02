(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Q_Relative_Rewriting
imports 
  Q_Restricted_Rewriting
begin

type_synonym ('f, 'v) qreltrs = "bool \<times> ('f, 'v) terms \<times> ('f, 'v) trs \<times> ('f, 'v) trs"
 
abbreviation rel_qrstep :: "('f, 'v) qreltrs \<Rightarrow> ('f, 'v) term rel" where
  "rel_qrstep \<equiv> \<lambda>(nfs,Q, R, S). relto (qrstep nfs Q R) (qrstep nfs Q S)"

abbreviation rel_rstep where "rel_rstep \<equiv> \<lambda>(R, S). rel_qrstep (False, {}, R, S)"

lemma ctxt_closed_rel_qrstep[intro] : "ctxt.closed (rel_qrstep QRS)"
  by (cases QRS) auto
  
lemma subst_closed_rel_rstep : "subst.closed (rel_rstep RS)"
proof (cases RS)
  case (Pair R S)
  from subst.closed_rtrancl[OF subst_closed_rstep[of S]] have S: "subst.closed ((rstep S)^*)" .
  from Pair subst.closed_comp[OF S subst.closed_comp[OF subst_closed_rstep[of R] S] ]
  show ?thesis by simp
qed

lemma rel_qrstep_mono: "R \<subseteq> R' \<Longrightarrow> S \<subseteq> S' \<Longrightarrow> NF_terms Q \<subseteq> NF_terms Q' \<Longrightarrow> rel_qrstep (nfs,Q,R,S) \<subseteq> rel_qrstep (nfs,Q',R',S')"
  unfolding split by (rule relto_mono[OF qrstep_mono qrstep_mono]) auto
      
lemma rel_qrstep_Id: "rel_qrstep (nfs,Q, R, S \<union> Id) = rel_qrstep (nfs,Q, R, S)" (is "?L = ?R")
proof -
  have "qrstep nfs Q (S^=) \<subseteq> (qrstep nfs Q S)^=" unfolding qrstep_union
    using qrstep_Id[of nfs Q] by auto
  from rtrancl_mono[OF this]
  have "?L \<subseteq> relto (qrstep nfs Q R) ((qrstep nfs Q S)^=)" by auto
  also have "... = ?R" unfolding relto_Id by simp
  finally have "?L \<subseteq> ?R" .
  moreover
  have "?R \<subseteq> ?L" by (rule rel_qrstep_mono, auto)
  ultimately show ?thesis by auto
qed

definition qrs_ideriv where
  "qrs_ideriv nfs Q R S = (\<lambda> as. ideriv (qrstep nfs Q R) (qrstep nfs Q S) as)"

lemmas qrs_ideriv_defs = qrs_ideriv_def ideriv_def

lemma qrs_ideriv_mono:
  assumes R: "R \<subseteq> R'"
    and S: "S \<subseteq> S'"
    and Q: "NF_terms Q \<subseteq> NF_terms Q'"
    and ideriv: "qrs_ideriv nfs Q R S ts"
  shows "qrs_ideriv nfs Q' R' S' ts"
  unfolding qrs_ideriv_def
  by (rule ideriv_mono[OF qrstep_mono[OF R Q] qrstep_mono[OF S Q] ideriv[unfolded qrs_ideriv_def]])

lemma qrs_ideriv_split:
  assumes ideriv: "qrs_ideriv nfs Q R S as"
    and nideriv: "\<not> qrs_ideriv nfs Q (D \<inter> (R \<union> S)) (R \<union> S - D) as" (is "\<not> ?q")
  shows "\<exists> i. qrs_ideriv nfs Q (R - D) (S - D) (shift as i)"
proof -
  let ?D = "D \<inter> (R \<union> S)"
  let ?Q = "qrstep nfs Q"
  let ?QD = "?Q ?D"
  let ?QR = "?Q R"
  let ?QS = "?Q S"
  let ?QRS = "?Q (R \<union> S)"
  have nideriv: "\<not> ideriv (?QD \<inter> ?QRS) (?QRS - ?QD) as" (is "\<not> ?i")
  proof 
    assume ?i
    have ?q unfolding qrs_ideriv_def
    proof (rule ideriv_mono[OF _ _ \<open>?i\<close>])
      show "?Q (D \<inter> (R \<union> S)) \<inter> ?QRS \<subseteq> ?Q (D \<inter> (R \<union> S))" by auto
    next
      {
        fix s t
        assume "(s,t) \<in> ?QRS" and "(s,t) \<notin> ?QD"
        then have "(s,t) \<in> ?Q (R \<union> S - D)" unfolding
          qrstep_rule_conv[where R = "R \<union> S"]
          qrstep_rule_conv[where R = ?D]
          qrstep_rule_conv[where R = "R \<union> S - D"]
          by auto
      }
      then show "?QRS - ?QD \<subseteq> ?Q (R \<union> S - D)"  by auto
    qed
    with nideriv show False ..
  qed
  have "\<exists> i. ideriv (?QR - ?QD) (?QS - ?QD) (shift as i)"
    by (rule ideriv_split[OF ideriv[unfolded qrs_ideriv_def]  nideriv[unfolded qrstep_union]])
  then obtain i where ideriv: "ideriv (?QR - ?QD) (?QS - ?QD) (shift as i)" ..
  show ?thesis
    by (rule exI[of _ i], unfold qrs_ideriv_def, 
      rule ideriv_mono[OF qrstep_diff qrstep_diff ideriv], auto)
qed


lemma rel_qrstep_SN: "SN_rel (qrstep nfs Q R) (qrstep nfs Q S) = (\<not> (\<exists> ts. qrs_ideriv nfs Q R S ts))"
  unfolding qrs_ideriv_def
  by (rule SN_rel_ideriv) 

definition rel_tt :: "(('f, 'v) qreltrs \<Rightarrow> ('f, 'v) qreltrs \<Rightarrow> bool) \<Rightarrow> bool" where
  "rel_tt tt \<longleftrightarrow> (\<forall>nfs Q R S rnfs rQ rR rS ts.
    (tt (nfs,Q, R, S) (rnfs,rQ, rR, rS) \<longrightarrow> qrs_ideriv nfs Q R S ts \<longrightarrow>
    (\<exists>ts'. qrs_ideriv rnfs rQ rR rS ts')))"

definition SN_qrel :: "('f, 'v) qreltrs \<Rightarrow> bool" where
  "SN_qrel = (\<lambda>(nfs, Q, R, S). SN_rel (qrstep nfs Q R) (qrstep nfs Q S))"

lemma SN_qrel_split: 
  assumes sn1: "SN_qrel (nfs,Q, D \<inter> (R \<union> S), R \<union> S - D)"
  and sn2: "SN_qrel (nfs,Q,R - D, S - D)"
  shows "SN_qrel (nfs,Q,R,S)"
  unfolding SN_qrel_def rel_qrstep_SN split
proof (clarify)
  fix ts
  assume "qrs_ideriv nfs Q R S ts"
  from qrs_ideriv_split[OF this, of D] sn1 sn2
  show False unfolding SN_qrel_def rel_qrstep_SN by auto
qed

lemma SN_qrel_map:
  fixes R Rw R' Rw' :: "('f, 'v) trs" and Q Q' :: "('f, 'v) terms" and nfs
  defines QR: "QR \<equiv> qrstep nfs Q R"
  defines QRw: "QRw \<equiv> qrstep nfs Q Rw"
  defines QR': "QR' \<equiv> qrstep nfs Q' R'"
  defines QRw': "QRw' \<equiv> qrstep nfs Q' Rw'"
  defines A: "A \<equiv> QR' \<union> QRw'"
  assumes SN: "SN_qrel (nfs,Q',R',Rw')"
  and R: "\<And> s t. (s,t) \<in> QR \<Longrightarrow> (f s, f t) \<in> A^* O QR' O A^*"
  and Rw: "\<And> s t. (s,t) \<in> QRw \<Longrightarrow> (f s, f t) \<in> A^*"
  shows "SN_qrel (nfs,Q,R,Rw)"
  by (unfold SN_qrel_def split, 
    rule SN_rel_map[OF 
    SN[unfolded SN_qrel_def split] 
    R[unfolded QR A QR' QRw'] 
    Rw[unfolded QRw A QR' QRw']])
  
lemma SN_qrel_empty_S[simp]: "SN_qrel (nfs,Q,R,{}) = SN (qrstep nfs Q R)"
  unfolding SN_qrel_def
  by auto

lemma SN_qrel_empty_Q[simp]: "SN_qrel (nfs,{},R,S) = SN_rel (rstep R) (rstep S)"
  unfolding SN_qrel_def by auto


lemma SN_qrel_mono_plain: assumes subset1: "qrstep nfs Q R \<subseteq> qrstep nfs Q' R'" and subset2: "qrstep nfs Q S \<subseteq> qrstep nfs Q' (R' \<union> S')" shows "SN_qrel (nfs,Q',R',S') \<Longrightarrow> SN_qrel (nfs,Q,R,S)"
  using SN_rel_mono'[OF subset1 subset2[unfolded qrstep_union]] 
  unfolding SN_qrel_def by auto

lemma SN_qrel_mono: 
  assumes subset1: "NF_terms Q \<subseteq> NF_terms Q'" 
    and subset2: "R \<subseteq> R'"
    and subset3: "S \<subseteq> R' \<union> S'"
  shows "SN_qrel (nfs,Q',R',S') \<Longrightarrow> SN_qrel (nfs,Q,R,S)"
  by (rule SN_qrel_mono_plain[OF qrstep_mono[OF subset2 subset1] qrstep_mono[OF subset3 subset1]])

lemma rel_tt:
  assumes sound: "rel_tt tt"
    and tt: "tt QRS QRS'"
    and SN: "SN_qrel QRS'"
  shows "SN_qrel QRS"
proof (cases QRS)
  case (fields nfs Q R S) note QRS = this
  show ?thesis
  proof (cases QRS')
    case (fields rnfs rQ rR rS) note QRS' = this
    show ?thesis unfolding QRS SN_qrel_def
      SN_rel_ideriv
    proof(clarify)
      fix ts
      assume "ideriv (qrstep nfs Q R) (qrstep nfs Q S) ts"
      then have "qrs_ideriv nfs Q R S ts" unfolding qrs_ideriv_def .
      with sound[unfolded rel_tt_def] tt 
      have "\<exists> ts. qrs_ideriv rnfs rQ rR rS ts" unfolding QRS QRS' qrs_ideriv_def by blast
      with SN[unfolded QRS'] show False unfolding SN_rel_ideriv SN_qrel_def qrs_ideriv_def by auto
    qed
  qed
qed

lemma SN_qrel_imp_SN_qrstep:
  assumes "SN_qrel (nfs,Q, R, S)"
  shows "SN (qrstep nfs Q R)"
  using assms unfolding SN_qrel_def split_def fst_conv snd_conv
  using SN_rel_imp_SN[of "qrstep nfs Q R"] by blast


end

