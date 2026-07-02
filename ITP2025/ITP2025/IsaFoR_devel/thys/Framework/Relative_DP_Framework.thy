(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016)
Author:  Rene Thiemann <rene.thiemann@uibk.ac.at> (2016)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Relative_DP_Framework
  imports
    TRS.QDP_Framework
    Ord.Term_Order
    Knuth_Bendix_Order.Lexicographic_Extension
    Weighted_Path_Order.Relations
begin

locale order_pair_restrict = base: order_pair
begin
sublocale order_pair "S \<restriction> X" "(NS \<restriction> X)\<^sup>="
proof(unfold_locales, unfold trans_O_iff refl_O_iff)
  show "Id \<subseteq> (NS \<restriction> X)\<^sup>=" by simp
  from base.trans_S_point
  show "S \<restriction> X O S \<restriction> X \<subseteq> S \<restriction> X" by auto
  from base.trans_NS_point
  show "(NS \<restriction> X)\<^sup>= O (NS \<restriction> X)\<^sup>= \<subseteq> (NS \<restriction> X)\<^sup>=" by auto
  from base.compat_S_NS_point
  show "S \<restriction> X O (NS \<restriction> X)\<^sup>= \<subseteq> S \<restriction> X" by auto
  from base.compat_NS_S_point
  show "(NS \<restriction> X)\<^sup>= O S \<restriction> X \<subseteq> S \<restriction> X" by auto
qed
end

lemma SN_on_imp_SN_restrict: assumes "SN_on R X" shows "SN (R \<restriction> X)"
proof
  fix f assume chain: "chain (R \<restriction> X) f"
  then have "f 0 \<in> X" "chain R f" by (auto simp: restrict_def)
  from not_SN_onI[OF this] assms show False by auto
qed

locale SN_order_pair_restrict = base: order_pair
begin

definition "SN_terms \<equiv> {x. SN_on S {x}}"

interpretation order_pair_restrict..

sublocale SN_order_pair "S \<restriction> SN_terms" "(NS \<restriction> SN_terms)\<^sup>="
  by (unfold_locales, auto intro: SN_on_imp_SN_restrict simp: SN_terms_def)

end

lemma subterm_preserves_SN_rel: "SN_on (relstep R S) {s} \<Longrightarrow> s \<rhd> t \<Longrightarrow> SN_on (relstep R S) {t}"
  by(rule subterm_preserves_SN_gen, auto)

lemma SN_on_Un_supt:
  assumes cl: "ctxt.closed R" and SN: "SN_on R X"
  shows "SN_on (R \<union> {\<rhd>}) X" (is "SN_on _ ?X")
proof(rule SN_on_subset2)
  from ctxt_closed_supt_subset[OF cl]
  have push: "{\<rhd>} O R \<subseteq> R O {\<rhd>}\<^sup>*" by auto
  from SN have "SN_on R ((({\<rhd>} \<union> R)^^n) `` X)" for n
  proof(induct n arbitrary: X)
    case 0 then show ?case by auto
  next
    case (Suc n)
    then show ?case
    proof (unfold relpow_Suc relcomp_Image, intro Suc, unfold Un_Image, intro SN_on_Un2)
      show "SN_on R ({\<rhd>} `` X)" by (rule SN_on_subset2[OF _ SN_on_Image_push[OF push Suc.prems]], auto)
      from Suc.prems show "SN_on R (R `` X)" by (unfold SN_on_Image_conv)
    qed
  qed
  then have SN: "SN_on R (({\<rhd>} \<union> R)\<^sup>* `` X)" (is "SN_on _ ?X")
  by (unfold rtrancl_is_UN_relpow UN_Image) (rule SN_on_UN, auto)
  show "SN_on (R \<union> {\<rhd>}) ?X"
  proof(rule iffD2[OF SN_on_Un, OF _ conjI])
    show "SN_on (relto R {\<rhd>}) ?X"
      apply (unfold SN_on_relto_relcomp, rule SN_on_O_comm, rule SN_on_O_push[OF push])
      apply (rule SN_on_subset2[OF _ SN], fold relcomp_Image, rule Image_subsetI, regexp)
      done
    show "(R \<union> {\<rhd>}) `` ?X \<subseteq> ?X" by (fold relcomp_Image, rule Image_subsetI, regexp)
    show "SN_on {\<rhd>} ?X" by (rule SN_on_subset2[OF _ SN_supt], auto)
  qed
  show "X \<subseteq> ?X" by auto
qed

lemma SN_on_relto_Un_supt:
  assumes clR: "ctxt.closed R" and clS: "ctxt.closed S" and SN: "SN_on (relto R S) X"
  shows "SN_on (relto R (S \<union> {\<rhd>})) X"
proof(unfold SN_on_relto_relcomp, intro SN_onI)
  from ctxt_closed_supt_subset[OF assms(2)]
  have pushS: "{\<rhd>} O S \<subseteq> S O {\<rhd>}\<^sup>*" by auto
  from ctxt_closed_supt_subset[OF assms(1)]
  have pushR: "{\<rhd>} O R \<subseteq> R O {\<rhd>}\<^sup>*" by auto
  from assms have cl: "ctxt.closed (S\<^sup>* O R)" by blast
  fix f assume f0: "f 0 \<in> X" and chain: "chain ((S \<union> {\<rhd>})\<^sup>* O R) f"
  have "\<not> SN_on ((S\<^sup>* O R \<union> {\<rhd>})\<^sup>+) {f 0}" (is "\<not> SN_on ?ord _")
  proof(intro lower_set_imp_not_SN_on ballI)
    fix "fi" assume "fi \<in> range f"
    then obtain i where [simp]: "fi = f i" by auto
    from chain have "(fi, f (Suc i)) \<in> (S \<union> {\<rhd>})\<^sup>* O R" by auto
    also have "... \<subseteq> S\<^sup>* O {\<rhd>}\<^sup>* O R" using rtrancl_U_push[OF pushS] by (auto simp: ac_simps)
    also have "... \<subseteq> S\<^sup>* O R O {\<rhd>}\<^sup>*" using rtrancl_O_push[OF pushR] by (auto simp: ac_simps)
    also have "... \<subseteq> (S\<^sup>* O R \<union> {\<rhd>})\<^sup>+" by regexp
    finally have "(fi, f (Suc i)) \<in> ..." by auto
    moreover have "f (Suc i) \<in> range f" by auto
    ultimately show "\<exists>t\<in> range f. (fi,t) \<in> (S\<^sup>* O R \<union> {\<rhd>})\<^sup>+" by auto
  qed auto
  moreover
    from SN_on_Un_supt[OF cl] SN[unfolded SN_on_relto_relcomp]
    have "SN_on ?ord X" by (auto simp: SN_on_trancl_SN_on_conv)
    from SN_on_subset2[OF _ this] f0 have "SN_on ?ord {f 0}" by auto
  ultimately show False by auto
qed


(* main part *)

type_synonym ('f, 'v) rel_dpp =
  "('f, 'v) trs \<times> ('f, 'v) trs \<times> ('f, 'v) trs \<times> ('f, 'v) trs \<times> ('f, 'v) trs"

fun min_relchain :: "('f, 'v) rel_dpp \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) term seq \<Rightarrow> ('f, 'v) subst seq \<Rightarrow> bool" where
  "min_relchain (P,Q,R,Rw,E) s t \<sigma> =
  ((\<forall>i. (s i, t i) \<in> P \<union> Q) \<and>
  (\<forall>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep (R \<union> Rw \<union> E))\<^sup>*) \<and>
  ((\<exists>\<^sub>\<infinity>i. (s i, t i) \<in> P) \<or>
   (\<exists>\<^sub>\<infinity>i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> relto (rstep R) (rstep (R \<union> Rw \<union> E)))) \<and>
  (\<forall>i. SN_on (relstep (R \<union> Rw) E) {t i \<cdot> \<sigma> i}))"

declare min_relchain.simps[simp del]

text \<open>The following characterization admits to reuse lemmas such as
  @{thm ichain_split} which are crucial for reduction pair processors, etc.\<close>
lemma min_relchain_via_ichain: "min_relchain (P,Q,R,Rw,E) s t \<sigma> \<longleftrightarrow>
  ichain (False, False, P, Q, {}, R, Rw \<union> E) s t \<sigma> \<and> (\<forall>i. SN_on (relstep (R \<union> Rw) E) {t i \<cdot> \<sigma> i})"
by (auto simp: min_relchain.simps ichain.simps ac_simps)

lemma min_relchain_split:
  assumes chain: "min_relchain (P,Q,R,Rw,E) s t \<sigma>"
    and nchain: "\<not> min_relchain (Ps \<inter> (P \<union> Q), P \<union> Q - Ps, Rs \<inter> (R \<union> Rw), R \<union> Rw - Rs, E) s t \<sigma>"
  shows "\<exists> i. min_relchain (P - Ps, Q - Ps, R - Rs, Rw - Rs, E) (shift s i) (shift t i) (shift \<sigma> i)"
proof -
  have Rw: "R \<union> Rw = (Rs \<inter> (R \<union> Rw)) \<union> (R \<union> Rw - Rs)" by auto
  have nchain: "\<not> ichain (False,False,Ps \<inter> (P \<union> Q), P \<union> Q - Ps, {}, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs \<union> E) s t \<sigma>"
  proof
    assume ichain: "ichain (False,False,Ps \<inter> (P \<union> Q), P \<union> Q - Ps, {}, Rs \<inter> (R \<union> Rw),  R \<union> Rw - Rs \<union> E) s t \<sigma>"
    then have "min_relchain (Ps \<inter> (P \<union> Q), P \<union> Q - Ps, Rs \<inter> (R \<union> Rw), R \<union> Rw - Rs, E) s t \<sigma>"
      unfolding min_relchain_via_ichain
      using chain[unfolded min_relchain_via_ichain]
      by (simp add: Rw[symmetric])
    with nchain show False by auto
  qed
  from chain have ichain: "ichain (False,False,P,Q,{},R,Rw \<union> E) s t \<sigma>" 
    unfolding min_relchain_via_ichain by auto
  from ichain_split_gen[OF ichain nchain] obtain i
    where ichain: "ichain (False,False,P - Ps, Q - Ps, {}, R - Rs, Rw - Rs \<union> E) (shift s i) (shift t i) (shift \<sigma> i)" ..
  have "min_relchain (P - Ps, Q - Ps, R - Rs, Rw - Rs, E) (shift s i) (shift t i) (shift \<sigma> i)"
    unfolding min_relchain_via_ichain
    by (rule conjI[OF ichain], rule allI,
    rule SN_on_mono[OF _ relto_mono[OF rstep_mono[of _ "R \<union> Rw"] subset_refl]],
    insert chain[unfolded min_relchain_via_ichain], auto)
  then show ?thesis ..
qed

lemma min_relchain_split_top:
  assumes chain: "min_relchain (P,Q,R,Rw,E) s t \<sigma>"
    and nchain: "\<not> min_relchain (Ps \<inter> (P \<union> Q), P \<union> Q - Ps, {}, R \<union> Rw, E) s t \<sigma>"
  shows "\<exists> i. min_relchain (P - Ps, Q - Ps, R, Rw, E) (shift s i) (shift t i) (shift \<sigma> i)"
using min_relchain_split [OF chain, of Ps "{}"] nchain by auto

definition "min_relchain_alt P Q R Rw E s t \<longleftrightarrow>
  (\<forall>i. (s i, t i) \<in> rrstep (P \<union> Q)) \<and>
  (\<forall>i. (t i, s (Suc i)) \<in> (rstep (R \<union> Rw \<union> E))\<^sup>*) \<and>
  ((\<exists>\<^sub>\<infinity>i. (s i, t i) \<in> rrstep P) \<or>
   (\<exists>\<^sub>\<infinity>i. (t i, s (Suc i)) \<in> relstep R (R \<union> Rw \<union> E))) \<and>
  (\<forall>i. SN_on (relstep (R \<union> Rw) E) {t i})"

lemma min_relchain_altI:
  "min_relchain (P,Q,R,Rw,E) s t \<sigma> \<Longrightarrow> min_relchain_alt P Q R Rw E (\<lambda>i. s i \<cdot> \<sigma> i) (\<lambda>i. t i \<cdot> \<sigma> i)"
by (auto simp: min_relchain.simps min_relchain_alt_def INFM_mono rrstepI)

lemma min_relchain_altD:
  assumes "min_relchain_alt P Q R Rw E s t"
  shows "\<exists>s t \<sigma>. min_relchain (P,Q,R,Rw,E) s t \<sigma>"
proof -
  { fix i :: nat
    have "\<exists>u v \<sigma>. (u, v) \<in> P \<union> Q \<and> s i = u \<cdot> \<sigma> \<and> t i = v \<cdot> \<sigma>"
      using assms by (auto simp: min_relchain_alt_def elim!: rrstepE dest!: spec [of _ i]) }
  then obtain u and v and \<sigma>
    where *: "\<forall>i. (u i, v i) \<in> P \<union> Q \<and> s i = u i \<cdot> \<sigma> i \<and> t i = v i \<cdot> \<sigma> i" by metis
  consider (P) "\<exists>\<^sub>\<infinity>i. (s i, t i) \<in> rrstep P" | (R) "\<exists>\<^sub>\<infinity>i. (t i, s (Suc i)) \<in> relstep R (R \<union> Rw \<union> E)"
    using assms by (auto simp: min_relchain_alt_def)
  then show ?thesis
  proof (cases)
    let ?P = "\<lambda> i j. j \<ge> i \<and> (\<exists>u v \<sigma>. (u, v) \<in> P \<and> s j = u \<cdot> \<sigma> \<and> t j = v \<cdot> \<sigma>)" 
    define I where "I = (\<lambda>i. LEAST j. ?P i j)" 
    case P
    then have P: "\<forall>i. \<exists>j. ?P i j" by (force simp: INFM_nat_le elim!: rrstepE)
    then have "\<forall>i. \<exists>u v \<sigma>. (u, v) \<in> P \<and> s (I i) = u \<cdot> \<sigma> \<and> t (I i) = v \<cdot> \<sigma>"
      by (auto simp: I_def dest!: LeastI_ex)
    then obtain u' and v' and \<sigma>'
      where **: "\<forall>i. (u' i, v' i) \<in> P \<and> s (I i) = u' i \<cdot> \<sigma>' i \<and> t (I i) = v' i \<cdot> \<sigma>' i" by metis
    define U where "U \<equiv> \<lambda>i. if \<exists>j. i = I j then u' (LEAST j. i = I j) else u i"
    define V where "V \<equiv> \<lambda>i. if \<exists>j. i = I j then v' (LEAST j. i = I j) else v i"
    define S where "S \<equiv> \<lambda>i. if \<exists>j. i = I j then \<sigma>' (LEAST j. i = I j) else \<sigma> i"
    { fix i :: nat
      have "(U i, V i) \<in> P \<union> Q \<and> (V i \<cdot> S i, U (Suc i) \<cdot> S (Suc i)) \<in> (rstep (R \<union> Rw \<union> E))\<^sup>* \<and>
        SN_on (relstep (R \<union> Rw) E) {V i \<cdot> S i}"
        using assms and * and **
        by (auto simp: min_relchain_alt_def U_def V_def S_def) (metis (mono_tags, lifting) LeastI_ex)+ }
    moreover
    { fix i :: nat
      have "(U (I i), V (I i)) \<in> P" using ** by (auto simp: U_def V_def)
      moreover have "I i \<ge> i" using P by (auto simp: I_def dest!: LeastI_ex)
      ultimately have "\<exists>j\<ge>i. (U j, V j) \<in> P" by blast }
    ultimately show ?thesis by (auto simp: min_relchain.simps INFM_nat_le)
  next
    case R
    then have "min_relchain (P,Q,R,Rw,E) u v \<sigma>"
      using assms and * by (auto simp: min_relchain_alt_def min_relchain.simps)
    then show ?thesis by blast
  qed
qed

lemma no_chain_imp_SN_rel_ext:
  assumes " \<not> (\<exists>s t \<sigma>. min_relchain (P, Q, R, Rw, E) s t \<sigma>)"
  shows "SN_rel_ext (rrstep P) (rrstep Q) (rstep R) (rstep Rw \<union> rstep E) (\<lambda>t. SN_on (relstep (R \<union> Rw) E) {t})"
    (is "SN_rel_ext ?P ?Q ?R (?Rw \<union> ?E) ?M")
proof (rule ccontr)
  let ?rel = "SN_rel_ext_step ?P ?Q ?R (?Rw \<union> ?E)"
  assume "\<not> ?thesis"
  from this[unfolded SN_rel_ext_def] obtain f ty where
    steps: "\<And> i. (f i, f (Suc i)) \<in> ?rel (ty i)"
   and min: "\<And> i. ?M (f i)"
   and inf1: "INFM i. ty i \<in> {top_s,top_ns}"
   and inf2: "INFM i. ty i \<in> {top_s,normal_s}" by blast
  obtain p where p: "\<And> i. p i = (ty i \<in> {top_s,top_ns})" by auto
  interpret infinitely_many p
    by (unfold_locales, insert inf1, unfold INFM_nat_le p)
  let ?ind = "infinitely_many.index p"
  let ?g = "\<lambda> i. f (?ind i)"
  let ?h = "\<lambda> i. f (Suc (?ind i))"
  let ?prop = "\<lambda> s t \<sigma> i. (s, t) \<in> P \<union> Q \<and> ?g i = s \<cdot> \<sigma> \<and> ?h i = t \<cdot> \<sigma> \<and> (ty (?ind i) = top_s \<longrightarrow> (s, t) \<in> P)"
  {
    fix i
    have "ty (?ind i) \<in> {top_s,top_ns}"
      using index_p[of i] unfolding p .
    then have one: "(?g i, ?h i) \<in> ?P \<union> ?Q" and two: "ty (?ind i) = top_s \<Longrightarrow> (?g i, ?h i) \<in> ?P" using steps[of "?ind i"]
      by auto      
    have "\<exists> s t \<sigma>. ?prop s t \<sigma> i"
    proof (cases "ty (?ind i) = top_s")
      case True
      with two[OF True] have "(?g i, ?h i) \<in> rrstep P" by simp
      then show ?thesis by (auto elim!: rrstepE)
    next
      case False
      moreover from one have "(?g i, ?h i) \<in> rrstep (P \<union> Q)" by (auto simp: rrstep_union)
      ultimately show ?thesis by (auto elim!: rrstepE)
    qed
  }
  from choice[OF allI[OF this]] obtain s where "\<forall> i. \<exists> t \<sigma>. ?prop (s i) t \<sigma> i" ..
  from choice[OF this] obtain t where "\<forall> i. \<exists> \<sigma>. ?prop (s i) (t i) \<sigma> i" ..
  from choice[OF this] obtain \<sigma> where st\<sigma>: "\<And> i. ?prop (s i) (t i) (\<sigma> i) i" by auto
  from st\<sigma> have PQ: "\<And> i. (s i, t i) \<in> P \<union> Q" by auto
  from st\<sigma> have s: "\<And> i. s i \<cdot> \<sigma> i = ?g i" by auto
  from st\<sigma> have t: "\<And> i. t i \<cdot> \<sigma> i = ?h i" by auto
  from st\<sigma> have P: "\<And> i. ty (?ind i) = top_s \<Longrightarrow> (s i, t i) \<in> P" by auto
  {
    fix i
    from st\<sigma>[of i] have "?M (t i \<cdot> \<sigma> i)" using min[of "Suc (?ind i)"] by auto
  } note min = this
  let ?f = "\<lambda> i j. f (Suc (?ind i) + j)"
  let ?n = "\<lambda> i. ?ind (Suc i) - Suc (?ind i)"
  let ?RE = "qrstep False {} (R \<union> (Rw \<union> E))"
  have "ichain (False, False, P, Q, {}, R, Rw \<union> E) s t \<sigma>"
    unfolding ichain_alternative
  proof (rule exI[of _ ?f], rule exI[of _ ?n], intro conjI allI impI, rule PQ)
    fix i
    show "?f i 0 = t i \<cdot> \<sigma> i" unfolding t by simp
  next
    fix i
    show "?f i (?n i) = s (Suc i) \<cdot> \<sigma> (Suc i)" unfolding s
      using index_ordered[of i] by auto
  next
    fix i j
    let ?k = "Suc (?ind i) + j"
    obtain k where k: "?k = k" by auto
    assume "j < ?n i"
    with index_not_p_between[of i ?k]
    have "\<not> p ?k" by auto
    then have "ty ?k \<in> {normal_s,normal_ns}" unfolding p k by (cases "ty k", auto)
    with steps[of ?k] show "(?f i j, ?f i (Suc j)) \<in> ?RE" unfolding qrstep_union
      by auto
  next
    let ?L = "\<lambda> i. (s i, t i) \<in> P"
    let ?R = "\<lambda> i. \<exists> j < ?n i. (?f i j, ?f i (Suc j)) \<in> qrstep False {} R"
    show "(INFM i. ?L i) \<or> (INFM i. ?R i)" 
      unfolding INFM_disj_distrib[symmetric] 
      unfolding INFM_nat_le
    proof (intro allI)
      fix i
      from inf2[unfolded INFM_nat_le]
      obtain k where k: "k \<ge> ?ind i" and ty: "ty k \<in> {top_s,normal_s}" by auto
      from index_surj[OF k]
      obtain j j' where kj: "k = ?ind j + j'" and j': "?ind j + j' < ?ind (Suc j)" by auto
      note ty = ty[unfolded kj]
      from k[unfolded kj] j' have lt: "?ind i < ?ind (Suc j)" by auto
      {
        assume "j < i"
        then have "Suc j \<le> i" by auto
        from index_ordered_le[OF this] lt have False by auto
      }
      then have j: "i \<le> j" by presburger
      show "\<exists> j \<ge> i. ?L j \<or> ?R j"
      proof (intro exI conjI, rule j)
        show "?L j \<or> ?R j"
        proof (cases j')
          case 0
          from index_p[of j]
            ty[unfolded 0] have "ty (?ind j) = top_s" unfolding p by auto
          from P[OF this] show ?thesis by auto
        next
          case (Suc j'')
          from index_not_p_between[of j "?ind j + j'", OF _ j']
          have "ty (?ind j + j') \<notin> {top_s,top_ns}" unfolding p Suc by auto
          with ty have ty: "ty (?ind j + j') = normal_s" by auto
          have j'': "j'' < ?ind (Suc j) - Suc (?ind j)" using j' unfolding Suc by auto
          have "?R j"
            by (rule exI[of _ j''], rule conjI[OF j''],
              insert steps[of "?ind j + j'", unfolded ty], unfold Suc, auto)
          then show ?thesis by auto
        qed
      qed
    qed
  qed auto
  then have "min_relchain (P,Q,R,Rw,E) s t \<sigma>"
    using min unfolding min_relchain_via_ichain by auto
  with assms show False by auto
qed

definition finite_rel_dpp :: "('f,'v) rel_dpp \<Rightarrow> bool" where "finite_rel_dpp DPP = (\<not>(\<exists>s t \<sigma>. min_relchain DPP s t \<sigma>))"

lemma finite_dpp_via_finite_rel_dpp: "finite_dpp (nfs,True,P,Pw,{},R,Rw) = finite_rel_dpp (P,Pw,R,Rw,{})"
  unfolding finite_dpp_def finite_rel_dpp_def min_relchain_via_ichain[abs_def] min_ichain.simps[abs_def]
  by (auto simp: minimal_cond_def ichain.simps)

lemma finite_rel_dppI[intro]: "(\<And> s t \<sigma>.  min_relchain dpp s t \<sigma> \<Longrightarrow> False) \<Longrightarrow> finite_rel_dpp dpp"
  unfolding finite_rel_dpp_def by auto

lemma finite_rel_dpp_split_top: "finite_rel_dpp (P - Ps, Q - Ps, R, Rw, E) \<Longrightarrow> 
   finite_rel_dpp (Ps \<inter> (P \<union> Q), P \<union> Q - Ps, {}, R \<union> Rw, E) \<Longrightarrow>
   finite_rel_dpp (P,Q,R,Rw,E)"
   unfolding finite_rel_dpp_def using min_relchain_split_top by blast

lemma finite_rel_dpp_split: "finite_rel_dpp (P - Ps, Q - Ps, R - Rs, Rw - Rs, E) \<Longrightarrow> 
  finite_rel_dpp (Ps \<inter> (P \<union> Q), P \<union> Q - Ps, Rs \<inter> (R \<union> Rw), R \<union> Rw - Rs, E) \<Longrightarrow>
  finite_rel_dpp (P,Q,R,Rw,E)"
  unfolding finite_rel_dpp_def using min_relchain_split by blast

lemma finite_rel_dpp_pairs_mono: assumes fin: "finite_rel_dpp (P',Q',R,Rw,E)"
  and P: "P \<subseteq> P'" and Q: "Q \<subseteq> P' \<union> Q'"
  shows "finite_rel_dpp (P,Q,R,Rw,E)"
proof -
  from P Q have Q: "P \<union> Q \<subseteq> P' \<union> Q'" by auto
  have *: "\<And> x. x \<subseteq> x" by auto
  from fin show ?thesis
  unfolding finite_rel_dpp_def min_relchain_via_ichain[abs_def] 
  using ichain_mono[OF _ P Q * * *, of False False "{}" R "Rw \<union> E"] by blast
qed



locale relative_trss =
  fixes R E :: "('f,'v) trs"
begin

definition "M = {s. SN_on (relstep R E) {s}}"

abbreviation "minstep P \<equiv> rrstep P \<restriction> M"

end

lemma Tinf_relstep_defined_root:
  assumes "wf_trs (R \<union> E)" and "t \<in> Tinf (relstep R E)"
  shows "defined (R \<union> E) (the (root t))"
using assms(1)
  and Tinf_imp_SN_nr_first_root_step_rel[of _ False "{}" _ "{}", unfolded qrstep_rstep_conv nrqrstep_nrrstep rqrstep_rrstep_conv, OF assms(2)]
  and nrrsteps_imp_eq_root_arg_rsteps [of t _ "R \<union> E"]
  and assms
by (auto simp: nrrstep_union wf_trs_def defined_def elim!: rrstepE) (case_tac l; auto)+

lemma trans_trancl_eq: "trans r \<longleftrightarrow> r\<^sup>+ = r" by (metis trancl_id trans_trancl)

locale relative_dp = sharp_syntax + relative_trss R E for R E :: "('f, 'v) trs" +
  assumes shp_not_defined: "\<And> f n. defined (R \<union> E) (f, n) \<Longrightarrow> \<not> defined (R \<union> E) (shp f, n)"
    and inj_shp: "\<And> f g. shp f = shp g \<Longrightarrow> f = g"
    and wf: "wf_trs (R \<union> E)"
begin

lemma Tinf_sharp_imp_SN:
  assumes "s \<in> Tinf (relstep R E)"
  shows "SN_on (relstep R E) {\<sharp> s}"
proof -
  from Tinf_imp_SN_nr_first_root_step_rel[of _ False "{}" E "{}" R, 
    unfolded qrstep_rstep_conv nrqrstep_nrrstep rqrstep_rrstep_conv nrrstep_union[symmetric]
    rrstep_union[symmetric], OF assms]
  obtain t u where st: "(s,t) \<in> (nrrstep (R \<union> E))\<^sup>*" and tu: "(t,u) \<in> rrstep (R \<union> E)" by auto
  from rrstepE[OF tu] obtain l r \<sigma> where lr: "(l,r) \<in> R \<union> E" and t: "t = l \<cdot> \<sigma>" .
  from wf lr have "is_Fun l" unfolding wf_trs_def by force
  then obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  with lr have "defined (R \<union> E) (f,length ls)" unfolding defined_def by auto
  from shp_not_defined[OF this] have ndef: "\<not> defined (R \<union> E) (\<sharp> f, length ls)" by auto
  from nrrsteps_imp_eq_root_arg_rsteps[OF st, unfolded t l, THEN conjunct1]
  obtain ss where s: "s = Fun f ss" and len: "length ss = length ls" by (cases s, auto)
  show ?thesis unfolding s sharp_term.simps
  proof (rule SN_args_imp_SN_rel_rstep[OF _ _ ndef[folded len]])
    fix s
    assume "s \<in> set ss"
    with assms[unfolded s Tinf_def] show "SN_on (relstep R E) {s}" by auto
  qed (insert wf, force simp: wf_trs_def)
qed  

lemma rrstep_imp_minstep:
  defines "NT \<equiv> Tinf (relstep R E)"
  assumes "{f. defined (R \<union> E) f} \<subseteq> F"
    and "wf_trs (R \<union> E)" and "s \<in> NT"
    and *: "\<not> SN_on (relstep R E) {t}"
  shows "(s, t) \<in> rrstep R \<Longrightarrow> \<exists>t' \<unlhd> t. t' \<in> NT \<and> (\<sharp> s, \<sharp> t') \<in> minstep (DP_on \<sharp> F R)"
    and "(s, t) \<in> rrstep E \<Longrightarrow> \<exists>t' \<unlhd> t. t' \<in> NT \<and> (\<sharp> s, \<sharp> t') \<in> minstep (DP_on \<sharp> F E)"
proof -
  have "wf_trs R" using assms by (auto simp: wf_trs_def)
  assume "(s, t) \<in> rrstep R"
  then obtain l and r and \<sigma> where "(l, r) \<in> R"
    and [simp]: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" by (auto elim: rrstepE)
  obtain u where "u \<unlhd> r \<cdot> \<sigma> " and "u \<in> NT" using not_SN_imp_subt_Tinf [OF *] by (auto simp: NT_def)
  { fix x assume "x \<in> vars_term r"
    then have "\<sigma> x \<lhd> s"
      using \<open>(l, r) \<in> R\<close> and \<open>wf_trs R\<close> by (auto simp: wf_trs_def dest: subst_image_subterm)
    then have "SN_on (relstep R E) {\<sigma> x}" using \<open>s \<in> NT\<close> by (auto simp: NT_def Tinf_def) }
  note ** = this
  then have "\<forall>x \<in> vars_term r. \<not> (\<sigma> x \<unrhd> u)"
    using \<open>u \<in> NT\<close> by (auto simp: Tinf_def NT_def dest: subterm_preserves_SN_on_relstep)
  then obtain v where "r \<unrhd> v" and [simp]: "u = v \<cdot> \<sigma>"
    using subt_instance_and_not_subst_imp_subt [OF \<open>r \<cdot> \<sigma> \<unrhd> u\<close>] by auto
  with ** obtain f and ts where [simp]: "v = Fun f ts"
    using subteq_Var_imp_in_vars_term [of r] and \<open>u \<in> NT\<close> by (cases v) (auto simp: NT_def Tinf_def)
  from \<open>u \<in> NT\<close> have v: "v \<cdot> \<sigma> \<in> NT" by simp
  then have "\<not> l \<rhd> v" using \<open>s \<in> NT\<close> by (auto dest: supt_subst simp: NT_def Tinf_def)
  moreover have "(f, length ts) \<in> F" using \<open>v \<cdot> \<sigma> \<in> NT\<close>
    using assms by (auto simp: M_def dest: Tinf_relstep_defined_root)
  ultimately have "(\<sharp> l, \<sharp> v) \<in> DP_on \<sharp> F R"
    using \<open>r \<unrhd> v\<close> and \<open>(l, r) \<in> R\<close> by (auto simp: DP_on_def)
  then have "(\<sharp>(l \<cdot> \<sigma>), \<sharp>(v \<cdot> \<sigma>)) \<in> rrstep (DP_on \<sharp> F R)"
    using wf_trs_imp_lhs_Fun [OF \<open>wf_trs R\<close> \<open>(l, r) \<in> R\<close>] by auto
  moreover from \<open>r \<unrhd> v\<close> have "r \<cdot> \<sigma> \<unrhd> v \<cdot> \<sigma>" by (rule supteq_subst)
  ultimately show "\<exists>u \<unlhd> t. u \<in> NT \<and> (\<sharp> s, \<sharp> u) \<in> minstep (DP_on \<sharp> F R)"
    using v \<open>s \<in> NT\<close> by (auto intro:Tinf_sharp_imp_SN simp: NT_def M_def)
next
  have "wf_trs E" using assms by (auto simp: wf_trs_def)
  assume "(s, t) \<in> rrstep E"
  then obtain l and r and \<sigma> where "(l, r) \<in> E"
    and [simp]: "s = l \<cdot> \<sigma>" "t = r \<cdot> \<sigma>" by (auto elim: rrstepE)
  obtain u where "u \<unlhd> r \<cdot> \<sigma> " and "u \<in> NT" using not_SN_imp_subt_Tinf [OF *] by (auto simp: NT_def)
  { fix x assume "x \<in> vars_term r"
    then have "\<sigma> x \<lhd> s"
      using \<open>(l, r) \<in> E\<close> and \<open>wf_trs E\<close> by (auto simp: wf_trs_def dest: subst_image_subterm)
    then have "SN_on (relstep R E) {\<sigma> x}" using \<open>s \<in> NT\<close> by (auto simp: NT_def Tinf_def) }
  note ** = this
  then have "\<forall>x \<in> vars_term r. \<not> (\<sigma> x \<unrhd> u)"
    using \<open>u \<in> NT\<close> by (auto simp: Tinf_def NT_def dest: subterm_preserves_SN_on_relstep)
  then obtain v where "r \<unrhd> v" and [simp]: "u = v \<cdot> \<sigma>"
    using subt_instance_and_not_subst_imp_subt [OF \<open>r \<cdot> \<sigma> \<unrhd> u\<close>] by auto
  with ** obtain f and ts where [simp]: "v = Fun f ts"
    using subteq_Var_imp_in_vars_term [of r] and \<open>u \<in> NT\<close> by (cases v) (auto simp: NT_def Tinf_def)
  from \<open>u \<in> NT\<close> have v: "v \<cdot> \<sigma> \<in> NT" by simp
  then have "\<not> l \<rhd> v" using \<open>s \<in> NT\<close> by (auto dest: supt_subst simp: NT_def Tinf_def)
  moreover have "(f, length ts) \<in> F" using \<open>v \<cdot> \<sigma> \<in> NT\<close>
    using assms by (auto dest: Tinf_relstep_defined_root)
  ultimately have "(\<sharp> l, \<sharp> v) \<in> DP_on \<sharp> F E"
    using \<open>r \<unrhd> v\<close> and \<open>(l, r) \<in> E\<close> by (auto simp: DP_on_def)
  then have "(\<sharp>(l \<cdot> \<sigma>), \<sharp>(v \<cdot> \<sigma>)) \<in> rrstep (DP_on \<sharp> F E)"
    using wf_trs_imp_lhs_Fun [OF \<open>wf_trs E\<close> \<open>(l, r) \<in> E\<close>] by auto
  moreover from \<open>r \<unrhd> v\<close> have "r \<cdot> \<sigma> \<unrhd> v \<cdot> \<sigma>" by (rule supteq_subst)
  ultimately show "\<exists>u \<unlhd> t. u \<in> NT \<and> (\<sharp> s, \<sharp> u) \<in> minstep (DP_on \<sharp> F E)"
    using v \<open>s\<in>NT\<close> by (auto intro: Tinf_sharp_imp_SN simp: NT_def M_def)
qed

definition "relchain_part P Q s v n \<equiv>
  (\<forall>i. v i \<in> Tinf (relstep R E)) \<and>
  s = v 0 \<and>
  (\<forall>i<n. (\<sharp> (v i), \<sharp> (v (Suc i))) \<in> minstep Q \<union> nrrstep E) \<and>
  (\<sharp> (v n), \<sharp> (v (Suc n))) \<in> minstep P \<union> nrrstep R"

lemma relchain_partI [intro]:
  assumes "\<And>i. v i \<in> Tinf (relstep R E)"
    and "s = v 0"
    and "\<And>i. i<n \<Longrightarrow> (\<sharp> (v i), \<sharp> (v (Suc i))) \<in> minstep Q \<union> nrrstep E"
    and "(\<sharp> (v n), \<sharp> (v (Suc n))) \<in> minstep P \<union> nrrstep R"
  shows "relchain_part P Q s v n"
using assms by (auto simp: relchain_part_def)

lemma relchain_partD [dest]:
  assumes "relchain_part P Q s v n"
  shows "\<And>i. v i \<in> Tinf (relstep R E)"
    and "s = v 0"
    and "\<And>i. i < n \<Longrightarrow> (\<sharp> (v i), \<sharp> (v (Suc i))) \<in> minstep Q \<union> nrrstep E"
    and "(\<sharp> (v n), \<sharp> (v (Suc n))) \<in> minstep P \<union> nrrstep R"
using assms by (auto simp: relchain_part_def)

definition "starts_relchain P Q s \<equiv> \<exists>v n. relchain_part P Q s v n"

lemma starts_relchain_pred:
  assumes s: "s \<in> Tinf (relstep R E)"
    and st: "(\<sharp> s, \<sharp> t) \<in> rrstep Q \<union> nrrstep E"
    and t: "starts_relchain P Q t"
  shows "starts_relchain P Q s"
proof -
  obtain v n where v: "relchain_part P Q t v n" using t by (auto simp: starts_relchain_def)
  define v' where "v' = (\<lambda>i. if i = 0 then s else v (i-1))"
  show ?thesis
  proof(unfold starts_relchain_def, intro exI relchain_partI)
    note * = relchain_partD[OF v]
    show "v' i \<in> Tinf (relstep R E)" for i unfolding v'_def using s *(1) by auto
    from Tinf_sharp_imp_SN[OF this] have M: "\<sharp> (v' i) \<in> M" for i by (auto simp: M_def)
    show "i < Suc n \<Longrightarrow> (\<sharp> (v' i), \<sharp> (v' (Suc i))) \<in> minstep Q \<union> nrrstep E" for i
    apply (auto intro: M)
    apply (unfold v'_def) using * s st apply (cases i, auto) done
    show "s = v' 0" unfolding v'_def by auto
    show "(\<sharp> (v' (Suc n)), \<sharp> (v' (Suc (Suc n)))) \<in> minstep P \<union> nrrstep R" using * unfolding v'_def by auto
  qed
qed

lemma Tinf_starts_relchain:
  assumes SN_suptrel: "SN (suptrel E)" and F: "{f. defined (R \<union> E) f} \<subseteq> F"
    and s: "s \<in> Tinf (relstep R E)" (is "_ \<in> ?M")
  shows "starts_relchain (DP_on \<sharp> F R) (DP_on \<sharp> F E) s"
proof -
  let ?lextwo = "lex_two (suptrel E) (supteqrel E) {(a,b). (b :: nat) < a}"
  have SN: "SN ?lextwo"
    by (rule lex_two[OF _ SN_suptrel SN_nat_gt], insert "suptrel_pair.compat_NS_S", blast)
  from s obtain n t u
    where st: "(s, t) \<in> (rstep E) ^^ n" and tu: "(t, u) \<in> (rstep R)" and u: "\<not> SN_on (relstep R E) {u}"
    using not_SN_on_rel_succ[OF conjunct1[OF s[unfolded Tinf_def mem_Collect_eq]]] by auto
  with s show ?thesis
  proof (induct "(s, n)" arbitrary: s t u n rule: SN_induct [OF SN])
    case 1
    then have s: "s \<in> ?M"
      and st: "(s, t) \<in> (rstep E) ^^ n"
      and tu: "(t, u) \<in> rstep R"
      and u: "\<not> SN_on (relstep R E) {u}"
      by auto
    note IH = 1(1)
    show ?case
    proof (cases "n")
      case 0
      then have [simp]: "s = t" using st by auto
      show ?thesis
      proof (cases rule: rstep_cases[OF tu])
        case 1
        then obtain t' where st': "(\<sharp> s, \<sharp> t') \<in> minstep (DP_on \<sharp> F R)" and t': "t' \<in> ?M"
          using rrstep_imp_minstep(1) [OF F wf s u] by auto
        then show ?thesis using s unfolding starts_relchain_def
          by (intro exI[of _ "\<lambda>i. if i = 0 then s else t'"] exI relchain_partI, auto)
      next
        case 2
        then have "(\<sharp> t, \<sharp> u) \<in> nrrstep R" using nrrstep_imp_sharp_nrrstep by auto
        moreover from s have u: "u \<in> ?M"
          apply(rule Tinf_nrrstep[OF _ _ u]) unfolding nrrstep_union using 2 by auto
        ultimately show ?thesis using s unfolding starts_relchain_def
          by (intro exI[of _ "\<lambda>i. if i = 0 then s else u"] exI, auto)
      qed
    next
      case (Suc n')
      with st obtain s' where ss': "(s,s') \<in> rstep E" and s't: "(s',t) \<in> (rstep E) ^^ n'"
        by (meson relpow_Suc_D2)
      from relpow_imp_rtrancl[OF s't] tu have "(s',u) \<in> relstep R E" by auto
      from step_preserves_SN_on[OF this] u
      have s': "\<not> SN_on (relstep R E) {s'}" by auto
      show ?thesis
      proof (cases rule: rstep_cases[OF ss'])
        case 1
        from rrstep_imp_minstep(2) [OF F wf s s' this]
          obtain s'' where sub: "s'' \<unlhd> s'" and s's'': "(\<sharp> s, \<sharp> s'') \<in> rrstep (DP_on \<sharp> F E)" and s'': "s'' \<in> ?M"
          by auto
        show ?thesis
        proof (cases "s'' = s'")
          case
          True then have s': "s' \<in> ?M" using s'' by auto
          have "(s,s') \<in> supteqrel E" using ss' unfolding supteqrel_def by auto
          then have "((s,n),(s',n')) \<in> ?lextwo" using Suc by auto
          note IH = IH[OF this s' s't tu u]
          show ?thesis
            apply (rule starts_relchain_pred[OF s _ IH])
            using s's'' True by auto
        next
          case False then have "s'' \<lhd> s'" using sub by auto
          then have "(s,s'') \<in> suptrel E" using ss' unfolding suptrel_def by auto
          then have *: "\<And>m. ((s,n),(s'',m)) \<in> ?lextwo" by auto
          from s''
            have "\<not> SN_on (relstep R E) {s''}" by (simp add: Tinf_def)
          from not_SN_on_rel_succ[OF this] obtain t' u' m
            where "(s'', t') \<in> rstep E ^^ m" "(t', u') \<in> rstep R"
            and "\<not> SN_on ((rstep E)\<^sup>* O rstep R O (rstep E)\<^sup>*) {u'}" by auto
          with IH[OF *[folded Suc] s'' this] s's''
            show ?thesis by(intro starts_relchain_pred[OF s], auto)
        qed
      next
        case 2
        from s have s': "s' \<in> ?M"
          apply (rule Tinf_nrrstep[OF _ _ s']) using 2 nrrstep_union by auto
        have "(s,s') \<in> supteqrel E" using ss' unfolding supteqrel_def by auto
        then have "((s,n),(s',n')) \<in> ?lextwo" using Suc by auto
        from IH[OF this s' s't tu u]
          show ?thesis apply(intro starts_relchain_pred[OF s])
          using nrrstep_imp_sharp_nrrstep[OF 2] by auto
      qed
    qed
  qed
qed

end

end
