(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Simple_Termination
imports
  Well_Quasi_Orders.Kruskal
  TRS.Signature_Extension
  "HOL-Cardinals.Wellorder_Extension"
  Embedding_Trs
begin

inductive_set gterms for F
where
  Fun [intro]: "(f, n) \<in> F \<Longrightarrow> length ts = n \<Longrightarrow> \<forall>t \<in> set ts. t \<in> gterms F \<Longrightarrow> Fun f ts \<in> gterms F"

interpretation kruskal_term: kruskal_tree F Fun "the \<circ> root" args "gterms F" for F
  by standard (auto simp: size_simp1 elim: gterms.cases)

lemma kruskal_emb_imp_embeq:
  assumes "kruskal_term.emb F P\<inverse>\<inverse>\<^sup>=\<^sup>= s t"
  shows "(t, s) \<in> embeq F P"
using assms
proof (induct)
  case (arg f m ts t s)
  then show ?case by (auto dest: embeq_arg embeq_trans)
next
  case (list_emb f m g n ss ts)
  then have "list_emb (\<lambda>s t. (t, s) \<in> embeq F P) ss ts" by (auto dest: list_emb_conjunct2)
  from list_emb_subseq_right [OF this] obtain us
    where sublist: "subseq us ts"
    and pairwise: "pairwise (\<lambda>s t. (t, s) \<in> embeq F P)\<^sup>=\<^sup>= ss us" by blast
  then have [simp]: "length us = length ss"
    and emb: "(Fun f us, Fun f ss) \<in> embeq F P" by (auto dest: pairwise_embeq pairwise_length)
  show ?case using \<open>P\<inverse>\<inverse>\<^sup>=\<^sup>= (f, m) (g, n)\<close>
  proof
    assume "P\<inverse>\<inverse> (f, m) (g, n)"
    with embeq_subseq [OF _ _ _ sublist, of P g f F] and list_emb
      have "(Fun g ts, Fun f us) \<in> embeq F P" by simp
    with emb show ?case by (blast dest: embeq_trans)
  next
    assume "(f, m) = (g, n)"
    then have [simp]: "f = g" "m = n" by auto
    have [simp]: "us = ts" using subseq_same_length [OF sublist] by (simp add: list_emb)
    show "(Fun g ts, Fun f ss) \<in> embeq F P" using pairwise by (auto dest: pairwise_embeq)
  qed
qed

lemma almost_full_on_gterms:
  assumes "almost_full_on P\<inverse>\<inverse>\<^sup>=\<^sup>= F"
  shows "almost_full_on (\<lambda>s t. (t, s) \<in> embeq F P) (gterms F)"
proof -
  have *: "almost_full_on (kruskal_term.emb F P\<inverse>\<inverse>\<^sup>=\<^sup>=) (gterms F)"
    using kruskal_term.almost_full_on_trees [OF assms] .
  show ?thesis by (intro almost_full_on_mono [OF subset_refl _ *] kruskal_emb_imp_embeq)
qed

definition "rewrite_relation R \<longleftrightarrow>
  ((\<forall>s t C. (s, t) \<in> R \<longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> R) \<and>
   (\<forall>s t \<sigma>. (s, t) \<in> R \<longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> R))"

definition "rewrite_order R \<longleftrightarrow> rewrite_relation R \<and> irrefl R \<and> trans R"

definition "simplification_order R \<longleftrightarrow> rewrite_order R \<and> (\<exists>Q. wqo_on Q\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV \<and> emb UNIV Q \<subseteq> R)"

text \<open>Every simplification order is strongly normalizing.\<close>
lemma simplification_order_imp_SN:
  fixes R :: "('f, 'v) term rel"
  assumes "simplification_order R"
  shows "SN R"
proof -
  from assms obtain Q
    where "rewrite_order R" and "wqo_on Q\<inverse>\<inverse>\<^sup>=\<^sup>= UNIV" and emb: "emb UNIV Q \<subseteq> R"
    by (auto simp: simplification_order_def)
  with almost_full_on_gterms [of Q UNIV]
    have af: "almost_full_on (\<lambda>s t. (t, s) \<in> (emb UNIV Q)\<^sup>=) (gterms UNIV)"
    and "trans R"
    and "irrefl R"
    and "rewrite_relation R"
    by (auto simp: wqo_on_imp_almost_full_on rewrite_order_def)
  then have subst: "\<And>s t \<sigma>. (s, t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> R" by (auto simp: rewrite_relation_def)
  note trans = \<open>trans R\<close> [unfolded trans_def, rule_format]
  { fix T :: "nat \<Rightarrow> ('f, 'v) term"
    assume *: "\<And>i. (T i, T (Suc i)) \<in> R"
    obtain c where "c \<in> (UNIV :: 'f set)" by auto
    define U where "U = (\<lambda>i. T i \<cdot> (\<lambda>_. Fun c [] :: ('f, 'v) term))"
    have "\<forall>i. U i \<in> gterms UNIV"
    proof
      fix i
      show "U i \<in> gterms UNIV"
        unfolding U_def by (induct ("T i")) (auto intro!: gterms.intros)
    qed
    with af have "good (\<lambda>s t. (t, s) \<in> (emb UNIV Q)\<^sup>=) U" by (auto simp: almost_full_on_def)
    then obtain i j where "i < j"
      and "(U j, U i) \<in> (emb UNIV Q)\<^sup>=" by auto
    with emb have "(U j, U i) \<in> R\<^sup>=" by blast
    moreover have "(U i, U j) \<in> R"
    proof -
      have "(T i, T j) \<in> R" using * and \<open>i < j\<close>
      proof (induct j)
        case (Suc j)
        then show ?case by (cases "i = j") (auto elim: trans)
      qed simp
      then show "(U i, U j) \<in> R" by (auto simp: U_def subst)
    qed
    ultimately have "(U i, U i) \<in> R" by (auto dest: trans)
    with \<open>irrefl R\<close> have False by (auto simp: irrefl_def) }
  then show "SN R" by (auto simp: SN_defs)
qed


definition "subterm_simplification_order R \<longleftrightarrow> rewrite_order R \<and> {\<rhd>} \<subseteq> R"

lemma kruskal_finite_sig:
  assumes "rewrite_order R"
  and "{\<rhd>} \<subseteq> R"
  and "kruskal_term.emb F (=) s t"
  and "s \<in> gterms F"
  and "t \<in> gterms F"
  and "s \<noteq> t"
shows "(t, s) \<in> R"
proof -
  have "(=) = (=)\<inverse>\<inverse>\<^sup>=\<^sup>=" by simp
  then have "(t, s) \<in> embeq F (=)" using assms(3) kruskal_emb_imp_embeq[of F "(=)" s t] by auto
  then have "(t, s) \<in> emb F (=)" using assms(6) using emb_reflcl_embeq by fastforce 
  moreover have "emb F (=) \<subseteq> (R\<^sup>=)"
    thm emb_subsetI[where ?F="F" and ?R="R\<^sup>=" and ?P="(=)"]
  proof (rule emb_subsetI[where ?F="F" and ?R="R\<^sup>=" and ?P="(=)"])
    have "R \<subseteq> R\<^sup>=" by blast
    then show "\<And>s t u. (s, t) \<in> R\<^sup>= \<Longrightarrow> (t, u) \<in> R\<^sup>= \<Longrightarrow> (s, u) \<in> R\<^sup>="
    and  "\<And>C s t. (s, t) \<in> R\<^sup>= \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> R\<^sup>=" 
    and "\<And>\<sigma> s t. (s, t) \<in> R\<^sup>= \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> R\<^sup>=" using assms(1) 
      unfolding rewrite_order_def rewrite_relation_def trans_def by blast+
    show "\<And>t f ts. t \<in> set ts \<Longrightarrow> (Fun f ts, t) \<in> R\<^sup>=" using assms(2) by (simp add: subset_iff) 
    show "\<And>f g ss ts. (f, length ss) = (g, length ts) \<Longrightarrow> subseq ts ss \<Longrightarrow> (Fun f ss, Fun g ts) \<in> R\<^sup>="
      using subseq_same_length by fastforce 
  qed
  ultimately show ?thesis using assms(6) by blast
qed

lemma gterm_UNIV_impl_gterm_funas:
  assumes "funas_term t \<subseteq> F"
  and "t \<in> gterms UNIV"
shows "t \<in> gterms F"
  using assms(2,1) by induct auto

lemma subterm_simplification_order_imp_SN:
  fixes S :: "('f, 'v) trs"
    and N :: "('f, 'v) trs"
  assumes "subterm_simplification_order R"
    and fin: "finite (funas_trs S)"
    and "S \<subseteq> R"
  shows "SN (rstep S)"
proof (rule ccontr)
  assume not_SN: "\<not> SN (rstep S)" 
  let ?Sig = "funas_trs S"
  from assms have rew: "rewrite_order R" and e: "{\<rhd>} \<subseteq> R"
    by (auto simp: subterm_simplification_order_def)
  then have rel: "rstep S \<subseteq> R" using \<open>S \<subseteq> R\<close> apply (auto simp:rewrite_order_def rewrite_relation_def)
    using set_rev_mp[of _ S R] by blast
  consider (a) "EX c. (c,0) \<in> ?Sig" | (b) "\<forall> c. (c,0) \<notin> ?Sig" by auto
  then have "EX F c. (c,0) \<in> F \<and> ?Sig \<subseteq> F \<and> finite F"
  proof cases
    case a
    then show ?thesis using fin by blast
  next
    case b
    then show ?thesis using fin by (meson UnCI finite.emptyI finite_Un finite_insert singletonI sup_ge1) 
  qed
  then obtain H c where H: "(c,0) \<in> H \<and> ?Sig \<subseteq> H" and finH: "finite H" by blast
  then have sub: "sig_step H (rstep S) \<subseteq> sig_step H R" using rel by (metis sig_step_union sup.order_iff) 
  have emb: "{(x,y). funas_term x \<subseteq> H \<and> funas_term y \<subseteq> H \<and> x \<rhd> y} \<subseteq> sig_step H R" using e by blast
  then have not_res_sn: "\<not> SN (sig_step H (rstep S))"
    using not_SN SN_sig_rstep_imp_SN_rstep[of S H] using H by blast 
  have tr: "trans R"
    and irr: "irrefl R"
    and rew_rel: "rewrite_relation R"
    using rew by (auto simp: rewrite_order_def)
  then have subst: "\<And>s t \<sigma>. (s, t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> R" by (auto simp: rewrite_relation_def)
  note trans = \<open>trans R\<close> [unfolded trans_def, rule_format]
  have transRes: "trans (sig_step H R)" by (metis trans sig_stepE sig_stepI transI) 
  have irrRes: "irrefl (sig_step H R)" by (meson \<open>irrefl R\<close> irrefl_def sig_stepE) 
  { fix T :: "nat \<Rightarrow> ('f, 'v) term"
    assume ass: "\<And>i. (T i, T (Suc i)) \<in> sig_step H (rstep S)"
    then have *: "\<And>i. (T i, T (Suc i)) \<in> sig_step H R"
      using sub by auto
    let ?U = "\<lambda>i. T i \<cdot> (\<lambda>_. Fun c [] :: ('f, 'v) term)"
    have wit: "\<forall>i. funas_term (?U i) \<subseteq> H"
    proof
      fix i
      have "funas_term (T i) \<subseteq> H" unfolding sig_step_def by (metis (no_types, lifting) "*" converse_rtranclE prod.sel(1) relcompE sig_stepE) 
      moreover have "funas_term (T i \<cdot> (\<lambda>_. Fun c [])) \<subseteq> funas_term (T i) \<union> {(c,0 ::nat)}"
      proof (induct "T i")
        case (Var x)
        then show ?case by auto
      next
        case (Fun f ss)
        have "funas_term (Fun c []) = {(c,0::nat)}" by simp
        then show ?case using funas_term_subst[of "T i" "\<lambda>_. Fun c []"] Fun by blast
      qed
      ultimately show "funas_term (T i \<cdot> (\<lambda>_. Fun c [])) \<subseteq> H" using H by blast
    qed
    moreover have "\<forall>i. ?U i \<in> gterms UNIV"
    proof
      fix i
      show "?U i \<in> gterms UNIV"
        by (induct ("T i")) (auto intro!: gterms.intros)
    qed
    ultimately  have grd: "\<forall>i. ?U i \<in> gterms H" using gterm_UNIV_impl_gterm_funas by blast
    let ?emb = "kruskal_term.emb H (=)"
    have "wqo_on ?emb (gterms H)"
      using finH by (intro kruskal_term.kruskal) (simp add: finite_eq_wqo_on)
    then have "good ?emb ?U" using grd wqo_on_imp_good by smt
    then obtain i j where ind: "i < j" and emb: "?emb (?U i) (?U j)" by blast
    have U: "(?U i, ?U j) \<in> sig_step H R"
    proof -
      have "(T i, T j) \<in> sig_step H R" using * and \<open>i < j\<close>
      proof (induct j)
        case (Suc j)
        show ?case
        proof (cases "i = j")
          case True
          then show ?thesis using Suc by simp 
        next
          case False
          then have "(T i, T j) \<in> sig_step H R" using Suc * by auto
          moreover have "(T j, T (Suc j)) \<in> sig_step H R" using * by auto
          ultimately show ?thesis using transRes unfolding trans_def by blast
        qed
      qed simp
      then show "(?U i, ?U j) \<in> sig_step H R"
        by (metis local.subst sig_stepE sig_stepI wit) 
    qed
    then have "?U i \<noteq> ?U j" using irrRes unfolding irrefl_def by auto
    with kruskal_finite_sig[of R H "?U i" "?U j"] have "(?U j, ?U i) \<in> R" using grd e rew ind emb by auto
    then have "(?U j, ?U i) \<in> sig_step H R" by (simp add: sig_stepI wit)
    with U have "(?U i, ?U i) \<in> sig_step H R" using transRes unfolding trans_def by blast
    then have False using irrRes unfolding irrefl_def by auto
  }
  then show False using not_res_sn unfolding SN_rel_on_def SN_on_def by blast
qed

lemma subterm_simplification_order_on_equations_imp_SN:
  fixes S :: "('f, 'v) trs"
    and N :: "('f, 'v) trs"
  assumes "subterm_simplification_order R"
    and "rewrite_relation E"
    and varcondS: "\<And> l r. (l,r) \<in> N \<Longrightarrow> vars_term r \<subseteq> vars_term l"
    and "finite F"
    and "funas_trs S \<subseteq> F"
    and "funas_trs N \<subseteq> F"
    and "S \<subseteq> R"
    and "N \<subseteq> E"
    and comp: "E\<^sup>* O R O E\<^sup>* \<subseteq> R"
  shows "SN_rel (rstep S) (rstep N)"
proof (rule ccontr)
  assume not_SN: "\<not> SN_rel (rstep S) (rstep N)" 
  let ?Sig = "funas_trs S"
  let ?SigN = "funas_trs N"
  have fin: "finite (funas_trs S)"
    using assms(4) assms(5) infinite_super by blast
  have finN: "finite (funas_trs N)" using assms(4) assms(6) infinite_super by blast 
  from assms have rew: "rewrite_order R" and e: "{\<rhd>} \<subseteq> R"
    by (auto simp: subterm_simplification_order_def)
  then have rel: "rstep S \<subseteq> R" using \<open>S \<subseteq> R\<close>  apply (auto simp:rewrite_order_def rewrite_relation_def)
    using set_rev_mp[of _ S R] by blast
  have relN: "rstep N \<subseteq> E" using \<open>N \<subseteq> E\<close> assms(2) unfolding rewrite_relation_def
    by (simp add: ctxt.closedI rstep_subset subst.closedI) 
  consider (a) "EX c. (c,0) \<in> ?Sig" | (b) "\<forall> c. (c,0) \<notin> ?Sig" by auto
  then have "EX F c. (c,0) \<in> F \<and> ?Sig \<subseteq> F \<and> finite F"
  proof cases
    case a
    then show ?thesis using fin by blast
  next
    case b
    then show ?thesis using fin by (meson UnCI finite.emptyI finite_Un finite_insert singletonI sup_ge1) 
  qed
  moreover have "\<exists> U. ?SigN \<subseteq> U \<and> finite U" using finN by blast
  ultimately have "\<exists> H U F c. (c,0) \<in> F \<and> ?Sig \<subseteq> F \<and> finite F \<and> ?SigN \<subseteq> U \<and> finite U \<and> H = U \<union> F" by blast
  then obtain H c where H: "\<exists> U F. (c,0) \<in> F \<and> ?Sig \<subseteq> F \<and> finite F \<and> ?SigN \<subseteq> U \<and> finite U \<and> H = U \<union> F" by blast
  then have finH: "finite H" by blast 
  then have sub: "sig_step H (rstep S) \<subseteq> sig_step H R" using rel by (metis sig_step_union sup.order_iff) 
  from finH have sub2: "sig_step H (rstep N) \<subseteq> sig_step H E" using relN by (metis sig_step_union sup.order_iff)
  have comp_sub: "(sig_step H E)\<^sup>* O sig_step H R O (sig_step H E)\<^sup>* \<subseteq> sig_step H R"
  proof
    fix x y
    assume ass: "(x, y) \<in> (sig_step H E)\<^sup>* O sig_step H R O (sig_step H E)\<^sup>*"
    then have "\<exists> z u. (x, z) \<in> (sig_step H E)\<^sup>* \<and> (z, u) \<in> sig_step H R \<and> (u, y)\<in> (sig_step H E)\<^sup>*" by blast
    then obtain z u where wit: "(x, z) \<in> (sig_step H E)\<^sup>* \<and> (z, u) \<in> sig_step H R \<and> (u, y)\<in> (sig_step H E)\<^sup>*" by blast
    then have "(x, z) \<in> E\<^sup>*" by (meson rtrancl_mono set_rev_mp sig_stepE subrelI)
    moreover have "(u, y) \<in> E\<^sup>*" using wit by (meson rtrancl_mono set_rev_mp sig_stepE subrelI)
    ultimately have "(x, y) \<in> R" using comp ass wit by blast
    then show "(x, y) \<in> sig_step H R" by (metis converse_rtranclE rtranclE sig_stepE sig_stepI wit) 
  qed
  have emb: "{(x,y). funas_term x \<subseteq> H \<and> funas_term y \<subseteq> H \<and> x \<rhd> y} \<subseteq> sig_step H R" using e by blast
  have "(c, 0) \<in> H \<and> funas_trs S \<subseteq> H \<and> funas_trs N \<subseteq> H" using H by blast
  then have not_res_sn: "\<not> SN_rel (sig_step H (rstep S)) (sig_step H (rstep N))"
    using not_SN sig_ext_relative_rewriting_var_cond[OF varcondS, of N] by auto
  { fix T :: "nat \<Rightarrow> ('f, 'v) term"
    assume ass: "\<And>i. (T i, T (Suc i)) \<in> relto (sig_step H (rstep S)) (sig_step H (rstep N))"
    then have "\<And>i. (T i, T (Suc i)) \<in> relto (sig_step H R) (sig_step H (rstep N))" using sub by blast
    then have "\<And>i. (T i, T (Suc i)) \<in> relto (sig_step H R) (sig_step H E)" using sub2
      by (meson Abstract_Rewriting.chain_mono order_refl relto_mono) 
    then have *: "\<And>i. (T i, T (Suc i)) \<in> sig_step H R" using comp_sub by blast
    then have nt_SN: "\<not> SN (rstep (sig_step H R))" by blast
    have "\<forall> r \<in> (sig_step H R). funas_rule r \<subseteq> H"
    proof
      fix r
      assume "r \<in> sig_step H R"
      then show "funas_rule r \<subseteq> H" by (metis Un_subset_iff funas_defs(2) prod.collapse sig_stepE)
    qed
    then have "funas_trs (sig_step H R) \<subseteq> H" unfolding funas_trs_def by blast
    then have "finite (funas_trs (sig_step H R))" using finH infinite_super by auto 
    then have False using subterm_simplification_order_imp_SN[OF assms(1), of "sig_step H R"] nt_SN by (meson sig_stepE subrelI) 
  }
  then show False using not_res_sn unfolding SN_rel_on_def SN_on_def by auto
qed


lemma wfp_on_SN_conv:
  "wfp_on P UNIV \<longleftrightarrow> SN {(x, y). P y x}"
  unfolding wfp_on_def SN_defs by blast

lemma wfp_on_imp_wf:
  assumes "wfp_on P A"
  shows "wf {(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  using wfp_on_imp_inductive_on [OF assms]
  unfolding wf_def inductive_on_def
  by (simp) (metis)

lemma well_order_extension':
  assumes "wfp_on P A"
  shows "\<exists>W. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> W x y) \<and> po_on W A \<and> wfp_on W A \<and> totalp_on A W"
proof -
  let ?R = "{(x, y). x \<in> A \<and> y \<in> A \<and> P x y}"
  from wfp_on_imp_wf [OF assms]
    have "wf ?R" and "Field ?R \<subseteq> A" by (auto simp: Field_def)
  from well_order_on_extension [OF this] obtain R
    where "?R \<subseteq> R" and "well_order_on A R" by blast
  then have wf_R: "wf (R - Id)" and "refl_on A R"
    and "antisym R" and "Relation.total_on A R"
    and "trans R"
    by (auto simp: well_order_on_def linear_order_on_def partial_order_on_def preorder_on_def)
  note [dest] = \<open>antisym R\<close> [unfolded antisym_def, rule_format]
                \<open>trans R\<close> [unfolded trans_def, rule_format]
  define W where "W = (\<lambda>x y. (x, y) \<in> R - Id)"
  have ext: "\<forall>x \<in> A. \<forall>y \<in> A. P x y \<longrightarrow> W x y"
    using \<open>?R \<subseteq> R\<close> using assms [THEN wfp_on_imp_irreflp_on] by (auto simp: W_def irreflp_on_def)
  moreover
  have "po_on W A"
    by (auto simp: po_on_def irreflp_on_def transp_on_def W_def)
  moreover
  have "wfp_on W A"
    by (rule wfp_on_subset [OF subset_UNIV], rule inductive_on_imp_wfp_on, insert wf_R)
       (simp only: W_def wfp_def wf_def inductive_on_def ball_UNIV)
  moreover
  have "totalp_on A W"
    using \<open>total_on A R\<close> by (auto simp: total_on_def totalp_on_def W_def)
  ultimately
  show ?thesis by blast
qed

lemma wqo_on_extension:
  assumes "wfp_on P A"
  shows "\<exists>W. (\<forall>x\<in>A. \<forall>y\<in>A. P x y \<longrightarrow> W x y) \<and> po_on W A \<and> wfp_on W A \<and> almost_full_on W\<^sup>=\<^sup>= A"
  using well_order_extension' [OF assms]
    and total_on_and_wfp_on_imp_almost_full_on [of A] by blast

end

