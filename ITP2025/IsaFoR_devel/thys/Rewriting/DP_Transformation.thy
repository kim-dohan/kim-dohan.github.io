(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory DP_Transformation
imports
  QDP_Framework
  Knuth_Bendix_Order.Lexicographic_Extension
begin

(* @{term "Tinf"} characterizes termination. *)
lemma Tinf_SN_conv: "(Tinf R = {}) = (SN R)"
proof
  assume "Tinf R = {}" then show "SN R" using not_SN_imp_Tinf by blast
next
  assume "SN R" then show "Tinf R = {}" unfolding Tinf_def SN_defs by blast
qed

definition "wwf_inn_qtrs nfs Q R \<equiv> nfs \<and> NF_terms Q \<subseteq> NF_trs R \<and> Ball (fst ` R) is_Fun"

lemma wwf_inn_qtrs_imp_left_fun: 
  "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> is_Fun l"
  using wwf_qtrs_imp_left_fun[of Q R l r] unfolding wwf_inn_qtrs_def by auto

lemma Tinf_lemma_1:
  assumes wwf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R"
    and Tinf: "Fun f ts \<in> Tinf (qrstep nfs Q R)" (is "?t \<in> _")
  shows "\<exists>l r u \<sigma>.
  (l, r) \<in> applicable_rules Q R \<and> 
  r \<unrhd> u \<and> 
  is_Fun u \<and> 
  (?t, l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>* \<and> 
  (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rqrstep nfs Q R \<and> 
  r \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma> \<and>
  l \<cdot> \<sigma> \<in> Tinf (qrstep nfs Q R) \<and>
  u \<cdot> \<sigma> \<in> Tinf (qrstep nfs Q R) \<and>
  \<not> (l \<rhd> u) \<and>
  NF_subst nfs (l, r) \<sigma> Q"
proof -
  let ?U = "applicable_rules Q R"
  let ?qr = "qrstep nfs Q R"
  let ?rqr = "rqrstep nfs Q R"
  let ?nrqr = "nrqrstep nfs Q R"
  from Tinf_imp_SN_nr_first_root_step [OF Tinf] obtain lhs and rhs
    where nsteps: "(Fun f ts, lhs) \<in> ?nrqr\<^sup>*" and step: "(lhs, rhs) \<in> ?rqr"
    and nSN: "\<not> SN_on ?qr {rhs}" by auto
  then obtain l r \<sigma> where NF: "\<forall>v \<lhd> l \<cdot> \<sigma>. v \<in> NF_terms Q"
    and "(l, r) \<in> R" and lhs: "l \<cdot> \<sigma> = lhs" and rhs: "r \<cdot> \<sigma> = rhs" 
    and nfs: "NF_subst nfs (l, r) \<sigma> Q" by auto
  with step have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?rqr" by auto
  from \<open>(l, r) \<in> R\<close> and only_applicable_rules [OF NF]
    have "(l, r) \<in> ?U" by (auto simp: applicable_rules_def)
  from nrqrsteps_preserve_root_fun [OF nsteps] obtain ls' where "lhs = Fun f ls'" by auto
  have A: "\<And>i. (ts ! i, ls' ! i) \<in> ?qr\<^sup>*"
  proof -
    fix j
    from nsteps have "(args ?t ! j, args (Fun f ls') ! j) \<in> ?qr\<^sup>*"
      unfolding \<open>lhs = Fun f ls'\<close> by (rule nrqrsteps_imp_arg_qrsteps)
    then show "?thesis j" by simp
  qed
  from nsteps and \<open>lhs = Fun f ls'\<close> have "(?t, Fun f ls') \<in> ?nrqr\<^sup>*" by simp
  from \<open>l \<cdot> \<sigma> = lhs\<close> and \<open>lhs = Fun f ls'\<close> have "l \<cdot> \<sigma> = Fun f ls'" by simp
  with \<open>(?t, Fun f ls') \<in> ?nrqr\<^sup>*\<close> have "(?t, l \<cdot> \<sigma>) \<in> ?nrqr\<^sup>*" by simp
  from \<open>(?t, Fun f ls') \<in> ?nrqr\<^sup>*\<close>
    have numargs: "num_args ?t = num_args (Fun f ls')" by (rule nrqrsteps_num_args)
  from wwf_inn_qtrs_imp_left_fun [OF wwf \<open>(l, r) \<in> R\<close>] obtain g ls where "l = Fun g ls" by force
  then have "l \<cdot> \<sigma> = Fun g (map (\<lambda>t. t \<cdot> \<sigma>) ls)" by simp
  with \<open>l \<cdot> \<sigma> = Fun f ls'\<close> have "g = f" and "ls' = map (\<lambda>t. t \<cdot> \<sigma>) ls" by auto
  then have B: "\<forall>i < length ls'. ls' ! i = (ls ! i) \<cdot> \<sigma>" by auto
  have "\<forall>i < num_args ?t. (ts ! i, (ls ! i) \<cdot> \<sigma>) \<in> ?qr\<^sup>*"
  proof (intro allI impI)
    fix i assume "i < num_args (Fun f ts)"
    with numargs have "i < length ls'" by simp
    with A [of i] show "(ts ! i, ls ! i \<cdot> \<sigma>) \<in> ?qr\<^sup>*" using B by simp
  qed
  from \<open>l \<cdot> \<sigma> = Fun f ls'\<close> numargs have "num_args ?t = num_args (l \<cdot> \<sigma>)"  by simp
  with \<open>l \<cdot> \<sigma> = Fun f ls'\<close> and \<open>\<forall>i<length ls'. ls' ! i = (ls ! i) \<cdot> \<sigma>\<close>
  have "\<And>i. i < num_args ?t \<Longrightarrow> (ls ! i) \<cdot> \<sigma> = ls' ! i" by auto
  have "\<And>i. i < num_args ?t \<Longrightarrow> ?t \<rhd> (ts ! i)"
  proof -
    fix i assume "i < num_args ?t"
    then have "ts ! i \<in> set ts" by simp
    then show "?t \<rhd> (ts ! i)" by (rule supt.arg)
  qed
  with Tinf [unfolded Tinf_def] have "\<And>i. i < num_args ?t \<Longrightarrow> SN_on ?qr {ts ! i}" by auto
  with \<open>\<forall>i < num_args ?t. (ts ! i, (ls ! i) \<cdot> \<sigma>) \<in> ?qr\<^sup>*\<close> 
    have "\<And>i. i < num_args ?t \<Longrightarrow> SN_on ?qr {(ls ! i) \<cdot> \<sigma>}"
    using steps_preserve_SN_on [of _ _ ?qr] by blast
  with \<open>\<And>i. i < num_args ?t \<Longrightarrow> (ls ! i) \<cdot> \<sigma> = ls' ! i\<close> and \<open>num_args ?t = num_args (l \<cdot> \<sigma>)\<close>
    and \<open>l \<cdot> \<sigma> = Fun f ls'\<close> and \<open>\<And>i. i < num_args ?t \<Longrightarrow> SN_on ?qr {(ls ! i) \<cdot> \<sigma>}\<close>
    have argsSN: "\<And>i. i < num_args (Fun f ls') \<Longrightarrow> SN_on ?qr {ls' ! i}" by auto
  have "\<forall>s \<lhd> Fun f ls'. SN_on ?qr {s}" 
  proof (intro allI impI)
    fix s
    assume tmp: "Fun f ls' \<rhd> s"
    then obtain C where "C \<noteq> \<box>" and "Fun f ls' = C\<langle>s\<rangle>" by auto
    then obtain bef aft C where id: "Fun f ls' = Fun f (bef @ C\<langle>s\<rangle> # aft)" by (cases C) auto
    then have len: "length bef < num_args (Fun f ls')" by auto
    with argsSN [OF len] and id have "SN_on ?qr {C\<langle>s\<rangle>}" by auto
    with ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep _ ctxt_imp_supteq [of C s]]
      show "SN_on ?qr {s}" by auto
  qed
  then have "\<forall>s \<lhd> l \<cdot> \<sigma>. SN_on ?qr {s}" unfolding \<open>l \<cdot> \<sigma> = Fun f ls'\<close> by simp 
  from nSN rhs obtain B where B0: "B 0 = r \<cdot> \<sigma>" and Bsteps: "\<And> i. (B i, B (Suc i)) \<in> ?qr" by auto
  from \<open>(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?rqr\<close> have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?qr" 
    unfolding qrstep_iff_rqrstep_or_nrqrstep by auto
  let ?B = "\<lambda>j. case j of 0 \<Rightarrow> l \<cdot> \<sigma> | Suc j \<Rightarrow> B j"
  have "?B 0 = l \<cdot> \<sigma>" using lhs by simp
  { fix i
    have "(?B i, ?B (Suc i)) \<in> ?qr"
      using Bsteps [of "i - Suc 0"] and \<open>(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> ?qr\<close> and B0 by (cases i) auto }
  note Bsteps = this
  with \<open>?B 0 = l \<cdot> \<sigma>\<close> have "\<not> SN_on ?qr {l \<cdot> \<sigma>}" unfolding SN_on_def by best
  with \<open>\<forall>s \<lhd> l \<cdot> \<sigma>. SN_on ?qr {s}\<close> have tinf_ls: "l \<cdot> \<sigma> \<in> Tinf ?qr" unfolding Tinf_def by simp
  { fix x
    assume x: "x \<in> vars_term r"
    from wwf have "SN_on ?qr {Var x \<cdot> \<sigma>}"
    proof
      assume "wwf_qtrs Q R"
      with x have "x \<in> vars_term l" using \<open>(l, r) \<in> ?U\<close> unfolding wwf_qtrs_def wwf_rule_def applicable_rules_def by auto
      then have "l \<rhd> Var x"
        using \<open>l = Fun g ls\<close> supteq_Var [OF \<open>x \<in> vars_term l\<close>] unfolding supt_supteq_conv by auto
      from supt_subst [OF this, of \<sigma>] and tinf_ls show ?thesis by (auto simp: Tinf_def)
    next
      assume "wwf_inn_qtrs nfs Q R"
      with nfs x have "\<sigma> x \<in> NF_trs R" unfolding NF_subst_def wwf_inn_qtrs_def vars_rule_def by auto
      then have "SN_on (rstep R) {\<sigma> x}" by (rule NF_imp_SN_on)
      from SN_on_mono [OF this]
        show ?thesis by auto
    qed }
  note xSN = this
  from nSN rhs have "\<not> SN_on ?qr {r \<cdot> \<sigma>}" by simp
  then obtain t' where "r \<cdot> \<sigma> \<unrhd> t'" and "t' \<in> Tinf ?qr" using not_SN_imp_subt_Tinf by auto
  have "\<forall>x \<in> vars_term r. \<not> (Var x \<cdot> \<sigma> \<unrhd> t')"
  proof
    fix x assume "x \<in> vars_term r"
    then have "SN_on ?qr {Var x \<cdot> \<sigma>}" using xSN by simp
    show "\<not> Var x \<cdot> \<sigma> \<unrhd> t'"
    proof
      assume "Var x \<cdot> \<sigma> \<unrhd> t'"
      with \<open>SN_on ?qr {Var x \<cdot> \<sigma>}\<close> have "SN_on ?qr {t'}" using ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep] by auto
      with \<open>t' \<in> Tinf ?qr\<close> show "False" unfolding Tinf_def by auto
    qed
  qed
  with \<open>r \<cdot> \<sigma> \<unrhd> t'\<close> have "\<exists>u. r \<unrhd> u \<and> t' = u \<cdot> \<sigma>"
    using subt_instance_and_not_subst_imp_subt [where s = r and \<sigma> = \<sigma>] by auto
  then obtain u where "r \<unrhd> u" and "t' = u \<cdot> \<sigma>" by best
  have "is_Fun u"
  proof (rule ccontr)
    assume "\<not> is_Fun u"
    then have "\<exists>x. u = Var x" by (cases u) simp_all
    then obtain x where "u = Var x" by best
    with \<open>r \<unrhd> u\<close> have "r \<unrhd> Var x" by auto
    then have "x \<in> vars_term r" using subteq_Var_imp_in_vars_term by best
    with xSN \<open>u = Var x\<close> have "SN_on ?qr {u \<cdot> \<sigma>}" by simp
    with \<open>t' = u \<cdot> \<sigma>\<close> have "SN_on ?qr {t'}" by simp
    with \<open>t' \<in> Tinf ?qr\<close> show "False" by (simp add: Tinf_def)
  qed
  from \<open>t' = u \<cdot> \<sigma>\<close> and \<open>t' \<in> Tinf ?qr\<close> have "u \<cdot> \<sigma> \<in> Tinf ?qr" by simp
  have "\<not> l \<rhd> u"
  proof
    assume "l \<rhd> u"
    then have "l \<cdot> \<sigma> \<rhd> u \<cdot> \<sigma>" by (rule supt_subst)
    with \<open>l \<cdot> \<sigma> \<in> Tinf ?qr\<close> have "SN_on ?qr {u \<cdot> \<sigma>}" unfolding Tinf_def by best
    with \<open>u \<cdot> \<sigma> \<in> Tinf ?qr\<close> show "False" by (auto simp: Tinf_def)
  qed
  from \<open>r \<unrhd> u\<close> have "r \<cdot> \<sigma> \<unrhd> (u \<cdot> \<sigma>)" by (rule supteq_subst)
  from \<open>(l, r) \<in> ?U\<close> and \<open>r \<unrhd> u\<close> and \<open>is_Fun u\<close> and \<open>(?t, l \<cdot> \<sigma>) \<in> ?nrqr\<^sup>*\<close> and \<open>(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> ?rqr\<close>
    and \<open>u \<cdot> \<sigma> \<in> Tinf ?qr\<close> and \<open>r \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma>\<close> and \<open>l \<cdot> \<sigma> \<in> Tinf ?qr\<close> and \<open>\<not> l \<rhd> u\<close> and nfs
  show ?thesis by blast
qed

lemma Tinf_var:
  assumes "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" shows "Var x \<notin> Tinf (qrstep nfs Q R)"
  using SN_on_Var_gen[of R nfs Q x] wwf_inn_qtrs_imp_left_fun[OF assms] unfolding Tinf_def by force
 
lemma Tinf_lemma:
  assumes wwf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" and tinf: "t\<in> Tinf (qrstep nfs Q R)"
  shows "\<exists>l r u \<sigma>.
    (l, r) \<in> applicable_rules Q R \<and> r \<unrhd> u \<and> is_Fun u \<and> (t, l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*
    \<and> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rqrstep nfs Q R \<and> r \<cdot> \<sigma> \<unrhd> u \<cdot> \<sigma> \<and> l \<cdot> \<sigma> \<in> Tinf (qrstep nfs Q R)
    \<and> u \<cdot> \<sigma> \<in> Tinf (qrstep nfs Q R) \<and> \<not> (l \<rhd> u) \<and> NF_subst nfs (l,r) \<sigma> Q"
proof (cases t)
  case (Var x)
  with Tinf_var[OF wwf] tinf have False by auto
  then show ?thesis ..
next
  case (Fun f ts)
  from Tinf_lemma_1[OF wwf tinf[simplified Fun]]
  show ?thesis unfolding Fun .
qed

lemma Tinf_imp_def_root_qrstep:
  assumes wwf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" and tinf: "t \<in> Tinf (qrstep nfs Q R)"
  shows "\<exists>f ss. t = Fun f ss \<and> defined (applicable_rules Q R) (f, length ss)"
proof -
  from Tinf_var[OF wwf] tinf obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  with tinf have tinf: "Fun f ts \<in> Tinf (qrstep nfs Q R)" by auto
  from Tinf_lemma[OF wwf tinf]
  obtain l r \<sigma> where lr: "(l,r) \<in> applicable_rules Q R" and "(Fun f ts,l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*" 
    by blast
  from lr have "(l,r) \<in> R" unfolding applicable_rules_def by auto
  from wwf_inn_qtrs_imp_left_fun[OF wwf this]
  obtain g ls where l: "l = Fun g ls" by blast
  with nrqrsteps_preserve_root[OF \<open>(Fun f ts,l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*\<close>]
    nrqrsteps_num_args[OF \<open>(Fun f ts,l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*\<close>]
  have "g = f" and "length ls = length ts" by auto
  with lr l have "defined (applicable_rules Q R) (f, length ts)" unfolding defined_def by auto
  with t show ?thesis by auto
qed

lemma Tinf_imp_Fun: 
   assumes wwf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" and "t \<in> Tinf (qrstep nfs Q R)"
   shows "\<exists>f ts. t = Fun f ts"
   using Tinf_var[OF wwf] assms(2) by (cases t, auto)

definition wf_qtrs :: "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "wf_qtrs nfs Q R \<equiv> (wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R) \<and> (\<forall>t\<in>Q. is_Fun t)"

lemma wf_qtrs_wf_trs_conv: "wf_qtrs nfs {} = wf_trs"
proof (rule ext)
  fix R :: "('f,'v)trs"
  show "wf_qtrs nfs {} R = wf_trs R"
    unfolding wf_qtrs_def wf_trs_def wwf_qtrs_def wwf_inn_qtrs_def
    by (force simp: applicable_rule_empty)
qed

lemma someI_ex4:
  "\<exists>w x y z. P (w, x, y, z) \<Longrightarrow> P (SOME (w, x, y, z). P (w, x, y, z))"
  by (simp add: some_eq_ex)

context
  fixes shp :: "'f \<Rightarrow> 'f"
begin

interpretation sharp_syntax .

fun initial_dpp :: "bool \<Rightarrow> bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs  \<Rightarrow> ('f, 'v) dpp"
where
  "initial_dpp nfs m Q R = (nfs, m, DP \<sharp> (applicable_rules Q R), {}, Q, {}, R)"

lemma Tinf_lemma_DP:
  assumes wf: "wf_qtrs nfs Q R" and s: "s \<in> Tinf (qrstep nfs Q R)"
    and ndef:
    "\<And>f n ss. defined (applicable_rules Q R) (f, n) \<Longrightarrow> length ss = n \<Longrightarrow> Fun (\<sharp> f) ss \<notin> Q"
  shows "\<exists>l r u \<sigma>. (l,r) \<in> DP \<sharp> (applicable_rules Q R) \<and> r \<cdot> \<sigma> = \<sharp> u
    \<and> u \<in> Tinf (qrstep nfs Q R) \<and> (\<sharp> s, l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*
    \<and> l \<cdot> \<sigma> \<in> NF_terms Q \<and> NF_subst True (l, r) \<sigma> Q"
proof -
  let ?qr = "qrstep nfs Q R"
  let ?U = "applicable_rules Q R"
  let ?nrqr = "nrqrstep nfs Q R"
  let ?rqr = "rqrstep nfs Q R"
  from wf have wf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" and wfQ: "\<forall>t\<in>Q. is_Fun t"
    unfolding wf_qtrs_def by auto
  let ?Q = "Q" and ?R = "R"
  let ?Iqr = "nrqrstep nfs ?Q ?R"
  obtain l r u \<sigma> where lr: "(l,r) \<in> ?U" and "r \<unrhd> u" and "is_Fun u" and "(s,l \<cdot> \<sigma>) \<in> ?nrqr\<^sup>*"
    and step: "(l \<cdot> \<sigma>,r \<cdot> \<sigma>) \<in> ?rqr" and "l \<cdot> \<sigma> \<in> Tinf ?qr" and "u \<cdot> \<sigma> \<in> Tinf ?qr" and "\<not> l \<rhd> u"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    using Tinf_lemma[OF wf s] by auto
  from lr have "(l,r) \<in> R" unfolding applicable_rules_def by auto
  let ?u = "u \<cdot> \<sigma>"
  let ?l = "\<sharp> l"
  let ?r = "\<sharp> u"
  let ?\<sigma> = \<sigma>
  obtain f us where "u = Fun f us" using \<open>is_Fun u\<close> by (cases u) auto
  have "root u = root ?u" unfolding \<open>u = Fun f us\<close> by simp
  obtain h vs where "?u = Fun h vs" and "defined ?U (h, length vs)"
    using Tinf_imp_def_root_qrstep[OF wf \<open>?u \<in> Tinf ?qr\<close>] by auto
  from \<open>(s,l \<cdot> \<sigma>) \<in> ?nrqr\<^sup>*\<close> have "(\<sharp> s, \<sharp> (l \<cdot> \<sigma>)) \<in> ?Iqr\<^sup>*"
    by (rule nrqrsteps_imp_sharp_qrsteps)
  from wwf_inn_qtrs_imp_left_fun[OF wf \<open>(l,r) \<in> R\<close>] obtain g ts where l: "l = Fun g ts" by force
  have "\<sharp> (l \<cdot> \<sigma>) = ?l\<cdot>?\<sigma>" unfolding \<open>l = Fun g ts\<close> by simp
  with \<open>(\<sharp> s,\<sharp> (l \<cdot> \<sigma>)) \<in> ?Iqr\<^sup>*\<close> have "(\<sharp> s,?l\<cdot>?\<sigma>) \<in> ?Iqr\<^sup>*" by simp
  from \<open>(u \<cdot> \<sigma>) = Fun h vs\<close> and \<open>u = Fun f us\<close> have "f = h" and "length us = length vs" by auto
  with \<open>defined ?U (h, length vs)\<close> have "defined ?U (f, length us)" by simp
  from \<open>(l,r) \<in> ?U\<close> and \<open>r \<unrhd> u\<close> and \<open>defined ?U (f, length us)\<close> and \<open>\<not>(l \<rhd> u)\<close> have "(?l,?r) \<in> DP \<sharp> ?U" unfolding DP_on_def \<open>u = Fun f us\<close> by auto
  have "?r\<cdot>?\<sigma> = \<sharp> ?u" unfolding \<open>u = Fun f us\<close> by simp
  from step have NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" unfolding rqrstep_def rstep_r_c_s_def by auto
  from lr l have gdef: "defined ?U (g, length ts)" unfolding defined_def by auto
  note ndef = ndef[OF gdef]
  note NF = NF[unfolded l]
  have "?l \<cdot> ?\<sigma> \<in> NF_terms ?Q"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    from not_NF_termsE[OF this]
    obtain q C \<gamma> where q: "q \<in> ?Q" and match: "?l \<cdot> ?\<sigma> = C\<langle>q \<cdot> \<gamma>\<rangle>" .
    from q have qg: "q \<cdot> \<gamma> \<notin> NF_terms Q" unfolding NF_def by force
    show False
    proof (cases C)
      case (More ff bef D aft)
      then have "Fun g ts \<cdot> ?\<sigma> \<rhd> q \<cdot> \<gamma>" using match l by auto
      with NF have "q \<cdot> \<gamma> \<in> NF_terms Q" by auto
      with qg show False by simp
    next
      case Hole
      with match have match: "?l\<cdot>?\<sigma> = q \<cdot> \<gamma>" by auto
      show ?thesis 
      proof (cases q)
        case (Fun ff qq)
        from match[unfolded l this] have ff: "ff = \<sharp> g" and qq: "length ts = length qq" using map_eq_imp_length_eq[of _ ts _ qq] by auto
        from ndef[OF qq[symmetric]] q[unfolded Fun ff]  
        show ?thesis by auto
      next
        case (Var x)
        from q[unfolded Var] wfQ show False by auto
      qed
    qed 
  qed
  then have NF: "?l \<cdot> ?\<sigma> \<in> NF_terms ?Q" by auto 
  have nfs: "NF_subst True (?l,?r) \<sigma> Q"
    unfolding NF_subst_def
  proof (intro impI subsetI)
    fix t
    assume t: "t \<in> \<sigma> ` vars_rule (?l,?r)"
    then obtain x where x: "x \<in> vars_rule (?l,?r)" and t: "t = \<sigma> x" by auto
    from x have "x \<in> vars_term ?l \<or> x \<in> vars_term ?r" unfolding vars_rule_def by auto
    then have "x \<in> vars_term ?l \<or> \<sigma> x \<in> NF_terms Q"
    proof 
      assume "x \<in> vars_term ?r"
      then have x: "x \<in> vars_term u" unfolding \<open>u = Fun f us\<close> by auto
      with supteq_imp_vars_term_subset [OF \<open>r \<unrhd> u\<close>] have x: "x \<in> vars_term r" by auto
      from wf show ?thesis
      proof
        assume "wwf_qtrs Q R"
        with lr x have "x \<in> vars_term l" unfolding wwf_qtrs_def applicable_rules_def by auto
        with \<open>l = Fun g ts\<close>
        show ?thesis by simp
      next
        assume "wwf_inn_qtrs nfs Q R"
        from this[unfolded wwf_inn_qtrs_def] have nfs by auto
        from nfs[unfolded NF_subst_def] vars_rule_def \<open>(l,r) \<in> R\<close> \<open>nfs\<close> x
        have "\<sigma> x \<in> NF_terms Q" by force
        then show ?thesis by simp
      qed
    qed simp
    then have "\<sigma> x \<in> NF_terms Q"
    proof
      assume "x \<in> vars_term ?l"
      then have "Var x \<unlhd> ?l" by auto
      then have "Var x \<cdot> \<sigma> \<unlhd> ?l \<cdot> \<sigma>" by auto
      from NF_subterm[OF NF this] show ?thesis by simp
    qed
    then show "t \<in> NF_terms Q" unfolding t .
  qed
  from NF nfs \<open>(?l,?r) \<in> DP \<sharp> ?U\<close> and \<open>?r\<cdot>?\<sigma> = \<sharp> ?u\<close>
    and \<open>?u \<in> Tinf ?qr\<close> and \<open>(\<sharp> s, ?l\<cdot>?\<sigma>) \<in> ?Iqr\<^sup>*\<close>
  show ?thesis by blast
qed

fun
  next4 :: "bool \<Rightarrow> ('f,'v)terms \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)term \<Rightarrow>
    ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)subst"
where
  "next4 nfs Q R s = (SOME (l, r, u, \<sigma>).
    (l, r) \<in> DP \<sharp> (applicable_rules Q R) \<and> r \<cdot> \<sigma> = \<sharp> u \<and> u \<in> Tinf (qrstep nfs Q R)
    \<and> (\<sharp> s, l \<cdot> \<sigma>) \<in> (nrqrstep nfs Q R)\<^sup>*
    \<and> l \<cdot> \<sigma> \<in> NF_terms Q \<and> NF_subst True (l,r) \<sigma> Q)"

fun
  concrete_seq :: "bool \<Rightarrow> ('f, 'v) terms \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> nat \<Rightarrow>
    ('f, 'v) term \<times> ('f, 'v) term \<times> ('f, 'v) term \<times> ('f, 'v) term \<times> ('f, 'v) subst"
where
  "concrete_seq nfs Q R s 0 = (s, next4 nfs Q R s)" |
  "concrete_seq nfs Q R r (Suc n) = (
    let ( _, _, _, s, _) = concrete_seq nfs Q R r n in
    (s, next4 nfs Q R s))"

theorem not_SN_imp_min_ichain:
  assumes "wf_qtrs nfs Q R" and "\<not> SN (qrstep nfs Q R)" 
  and ndef: "\<And> f n ss. defined (applicable_rules Q R) (f,n) \<Longrightarrow> length ss = n \<Longrightarrow> Fun (\<sharp> f) ss \<notin> Q"
  and m: "m = (\<forall> f n. defined (applicable_rules Q R) (f,n) \<longrightarrow> \<not> defined (applicable_rules Q R) (\<sharp> f,n))"
  shows "\<exists>s t \<sigma>. min_ichain (initial_dpp nfs m Q R) s t \<sigma>"
proof -
  let ?qr = "qrstep nfs Q R"
  let ?Q = "Q" and ?R = "R"
  let ?Iqr = "nrqrstep nfs ?Q ?R"
  from \<open>\<not>(SN(qrstep nfs Q R))\<close> obtain s' where "\<not> (SN_on ?qr {s'})"
    unfolding SN_on_def by auto
  then obtain s where "s' \<unrhd>  s" and "s \<in> Tinf ?qr" using not_SN_imp_subt_Tinf by auto
  from \<open>wf_qtrs nfs Q R\<close>
  have wwf: "wwf_qtrs Q R \<or> wwf_inn_qtrs nfs Q R" unfolding wf_qtrs_def by auto
  from wwf_inn_qtrs_imp_left_fun[OF wwf]
  have nvar: "\<forall> (l,r) \<in> R. is_Fun l" by auto    
  let ?I = "\<lambda>i. fst(concrete_seq nfs Q R s i)"
  let ?S = "\<lambda>i. fst(snd(concrete_seq nfs Q R s i))"
  let ?T = "\<lambda>i. fst(snd(snd(concrete_seq nfs Q R s i)))"
  let ?\<sigma> = "\<lambda>i. snd(snd(snd(snd(concrete_seq nfs Q R s i))))"
  let ?P = "\<lambda>s l r u \<sigma>. (l,r) \<in> DP \<sharp> (applicable_rules Q R) \<and> r \<cdot> \<sigma> = \<sharp> u
    \<and> u \<in> Tinf ?qr \<and> (\<sharp> s,l \<cdot> \<sigma>) \<in> ?Iqr\<^sup>* \<and> l \<cdot> \<sigma> \<in> NF_terms ?Q \<and> NF_subst True (l,r) \<sigma> Q"
  let ?P' =  "\<lambda>(l,r,u,\<sigma>). ?P s l r u \<sigma>"
  have main: "\<forall>i. ?P (?I i) (?S i) (?T i) (?I(Suc i)) (?\<sigma> i)"
  proof
    fix i show "?P (?I i) (?S i) (?T i) (?I(Suc i)) (?\<sigma> i)"
    proof (induct i)
      case 0 
      have "\<exists>l r u \<sigma>. ?P'(l,r,u,\<sigma>)"
        using Tinf_lemma_DP[OF \<open>wf_qtrs nfs Q R\<close> \<open>s \<in> Tinf ?qr\<close> ndef] unfolding split by auto
      then have "?P'(next4 nfs Q R s)" unfolding next4.simps using someI_ex4[where P = "?P'"] by best
      have ini: "?I 0 = s" unfolding concrete_seq.simps by simp
      have s: "?S 0 = fst(next4 nfs Q R s)" unfolding concrete_seq.simps by simp
      have t: "?T 0 = fst(snd(next4 nfs Q R s))" unfolding concrete_seq.simps by simp
      have sub: "?\<sigma> 0 = snd(snd(snd(next4 nfs Q R s)))"
        unfolding concrete_seq.simps Let_def split_def by auto
      have nxt: "?I(Suc 0) = fst(snd(snd(next4 nfs Q R s)))"
        unfolding concrete_seq.simps Let_def split_def by auto
      show ?case unfolding ini s t sub nxt using \<open>?P'(next4 nfs Q R s)\<close> by auto
    next
      case (Suc i)
      let ?P'' = "\<lambda>(w,x,y,z). ?P (?I(Suc i)) w x y z"
      from Suc have "?I (Suc i) \<in> Tinf ?qr" by simp
      have "\<exists>l r u \<sigma>. ?P''(l,r,u,\<sigma>)"
        using Tinf_lemma_DP[OF \<open>wf_qtrs nfs Q R\<close> \<open>?I (Suc i) \<in> Tinf ?qr\<close> ndef] by auto
      then have IH: "?P''(next4 nfs Q R (?I(Suc i)))"
        unfolding next4.simps using someI_ex4[where P = "?P''"] by simp
      have s: "?S(Suc i) = fst(next4 nfs Q R (?I(Suc i)))"
        unfolding concrete_seq.simps Let_def split_def by simp
      have t: "?T(Suc i) = fst(snd(next4 nfs Q R (?I(Suc i))))"
        unfolding concrete_seq.simps Let_def split_def by simp
      have sub: "?\<sigma>(Suc i) = snd(snd(snd(next4 nfs Q R (?I(Suc i)))))"
        unfolding concrete_seq.simps Let_def split_def by simp
      have nxt: "?I(Suc(Suc i)) = fst(snd(snd(next4 nfs Q R (?I(Suc i)))))"
        unfolding concrete_seq.simps Let_def split_def by simp
      show ?case unfolding s t sub nxt using IH by auto
    qed
  qed
  from main have P: "\<forall>i. (?S i,?T i) \<in> DP \<sharp> (applicable_rules Q R)" by simp
  from main have NF: "\<And>i. (?S i \<cdot> ?\<sigma> i) \<in> NF_terms ?Q" by auto
  from main have nfs: "\<And>i. NF_subst nfs (?S i, ?T i) (?\<sigma> i) Q" unfolding NF_subst_def by blast
  from main have eq: "\<And>i. \<sharp> (?I(Suc i)) = ?T i \<cdot> ?\<sigma> i" by auto
  have R: "\<forall>i. (?T i \<cdot> ?\<sigma> i,?S(Suc i) \<cdot> ?\<sigma>(Suc i)) \<in> ?Iqr\<^sup>*"
  proof
    fix i show "(?T i \<cdot> ?\<sigma> i,?S(Suc i)\<cdot>?\<sigma>(Suc i)) \<in> ?Iqr\<^sup>*"
    proof (cases i)
      case 0
      from main have first: "?T 0 \<cdot> ?\<sigma> 0 = \<sharp> (?I(Suc 0))" by best
      from main have "(\<sharp> (?I(Suc 0)),?S(Suc 0)\<cdot>?\<sigma>(Suc 0)) \<in> ?Iqr\<^sup>*" by best
      then show ?thesis unfolding 0 unfolding first by simp
    next
      case (Suc i) show ?thesis unfolding eq[symmetric] using main by best
    qed
  qed
  have Tinf: "\<forall>i. ?I i \<in> Tinf ?qr"
  proof
    fix i show "?I i \<in> Tinf ?qr" using main by (induct i) (auto simp: \<open>s \<in> Tinf ?qr\<close>)
  qed
  {
    fix i 
    from Tinf have Tinf: "?I (Suc i) \<in> Tinf ?qr" by best
    from main have "(?S i, ?T i) \<in> DP \<sharp> (applicable_rules Q R)" by auto
    then obtain f ts where ti: "?T i = Fun (\<sharp> f) ts" and "defined (applicable_rules Q R) (f,length ts)" unfolding DP_on_def by auto
    then obtain ts where id: "?T i \<cdot> ?\<sigma> i = Fun (\<sharp> f) ts" and d: "defined (applicable_rules Q R) (f,length ts)"  by auto
    from eq id have eq: "\<sharp> (?I(Suc i)) = Fun (\<sharp> f) ts" by simp
    from eq obtain g where "?I (Suc i) = Fun g ts" by (cases "?I (Suc i)", auto)
    from Tinf[unfolded this] have "Fun g ts \<in> Tinf ?qr" .
    from this[unfolded Tinf_def] have SN: "\<And> t. t \<in> set ts \<Longrightarrow> SN_on ?qr {t}" by auto
    then have "\<And> t. t \<in> set (args (?T i \<cdot> ?\<sigma> i)) \<Longrightarrow> SN_on ?qr {t}" unfolding id by simp
  } note SN_args = this
  have RR: "?Iqr\<^sup>* \<subseteq> ?qr\<^sup>*" by (rule rtrancl_mono, unfold qrstep_iff_rqrstep_or_nrqrstep, auto)
  from R have R: "\<forall> i. (?T i \<cdot> ?\<sigma> i,?S(Suc i) \<cdot> ?\<sigma>(Suc i)) \<in> ?qr\<^sup>*" using RR by blast
  note idd = initial_dpp.simps
  from P and R and NF nfs have ichain: "ichain (initial_dpp nfs m Q R) ?S ?T ?\<sigma>" 
    by (auto simp: ichain.simps)
  show ?thesis
  proof (intro exI, unfold idd min_ichain.simps, unfold idd[symmetric], rule conjI[OF ichain], rule impI)
    assume m
    then have ndef2: "\<forall> f n. defined (applicable_rules Q R) (f,n) \<longrightarrow> \<not> defined (applicable_rules Q R) (\<sharp> f, n)"
      unfolding m .
    have SN_t: "\<forall>i. SN_on ?qr {?T i \<cdot> ?\<sigma> i}"
    proof
      fix i
      from Tinf have Tinf: "?I (Suc i) \<in> Tinf ?qr" by best
      from main have "(?S i, ?T i) \<in> DP \<sharp> (applicable_rules Q R)" by auto
      then obtain f ts where "?T i = Fun (\<sharp> f) ts" and "defined (applicable_rules Q R) (f,length ts)" unfolding DP_on_def by auto
      then obtain ts where id: "?T i \<cdot> ?\<sigma> i = Fun (\<sharp> f) ts" and d: "defined (applicable_rules Q R) (f,length ts)"  by auto
      show "SN_on ?qr {?T i \<cdot> ?\<sigma> i}" unfolding id 
      proof (rule SN_args_imp_SN[OF _ nvar ndef2[THEN spec, THEN spec, THEN mp[OF _ d]]])
        fix t
        assume t: "t \<in> set ts"
        with SN_args[of t i, unfolded id]
        show "SN_on ?qr {t}" by auto
      qed
    qed
    then show "minimal_cond nfs Q ({} \<union> R) ?S ?T ?\<sigma>"
      unfolding minimal_cond_def by simp
  qed
qed

corollary not_SN_imp_ichain:
  assumes prem: "wf_qtrs nfs Q R" "\<not> SN (qrstep nfs Q R)" 
  "\<And> f n ss. defined (applicable_rules Q R) (f,n) \<Longrightarrow> length ss = n \<Longrightarrow> Fun (\<sharp> f) ss \<notin> Q"
  shows "\<exists>s t \<sigma>. ichain (initial_dpp nfs m Q R) s t \<sigma>"
proof -
  obtain mm where mm: "mm = (\<forall>f n. defined (applicable_rules Q R) (f, n) \<longrightarrow>
                    \<not> defined (applicable_rules Q R) (\<sharp> (f), n))" by auto
  from not_SN_imp_min_ichain[OF prem mm] 
  have "\<exists>s t \<sigma>. min_ichain (initial_dpp nfs mm Q R) s t \<sigma>" .
  then show ?thesis unfolding initial_dpp.simps min_ichain.simps ichain.simps by blast
qed

corollary not_SN_imp_ichain_rstep:
  fixes R :: "('f, 'v) trs"
  assumes wf: "wf_trs R" and nSN: "\<not> SN (rstep R)" 
  shows "\<exists> s t \<sigma>. ichain (nfs,m,DP \<sharp> R, {}, {}, {}, R) s t \<sigma>"
proof -
  let ?DP = "DP \<sharp> (applicable_rules {} R)"
  have U: "applicable_rules {} R = R" unfolding applicable_rules_def applicable_rule_def by auto
  from wf U have wf: "wf_qtrs nfs {} R" unfolding wf_qtrs_def wwf_qtrs_wf_trs by auto
  from nSN have nSN: "\<not> SN (qrstep nfs {} R)" by auto
  have id: "initial_dpp nfs m {} R = (nfs,m,DP \<sharp> R, {}, {}, {}, R)" by (simp add: applicable_rules_def applicable_rule_def)
  from not_SN_imp_ichain[OF wf nSN, of m, unfolded id U] show ?thesis by auto
qed

(* completeness lemma *)
lemma SN_imp_finite_dpp_simple:
  fixes R :: "('f, 'v) trs"
  assumes SN: "SN (qrstep nfs Q R)"  
    and shp: "\<And> f n. unshp \<noteq> id \<Longrightarrow> (f, n) \<in> D \<Longrightarrow> \<not> defined R (\<sharp> f, n)"
    and unshp: "\<And> f n. (f, n) \<in> D \<Longrightarrow> unshp (\<sharp> f) = f"
    and D: "\<And> fn. defined R fn \<Longrightarrow> fn \<in> D"
    and nfs: "nfs \<Longrightarrow> \<forall> l r. (l, r) \<in> R \<longrightarrow> is_Fun l"
  shows "finite_dpp (nfs, m, DP_simple \<sharp> D R, {}, Q, {}, R)"
proof (rule ccontr)
  let ?DP = "DP_simple \<sharp> D R"
  let ?u = "sharp_term unshp :: ('f,'v)term \<Rightarrow> ('f,'v)term"
  let ?r = "qrstep nfs Q R \<union> {\<rhd>}"
  assume "\<not> ?thesis"
  then obtain s t \<sigma> where "ichain (nfs,m,?DP,{},Q,{},R) s t \<sigma>" 
    unfolding finite_dpp_def by auto
  note ichain = this[unfolded ichain.simps]
  {
    fix l r x
    assume lr: "(l,r) \<in> R" and l: "l = Var x" 
    have False
    proof (cases nfs)
      case False
      from left_Var_imp_not_SN_qrstep[OF lr[unfolded l] False, of Q]
        SN show False unfolding SN_def by auto
    next
      case True
      with nfs[OF this] lr l show False by auto
    qed
  } note nvar = this
  then have varcond: "\<forall> (l,r) \<in> R. is_Fun l" by force
  {
    fix i
    from ichain have "(s i, t i) \<in> ?DP" by auto
    from this[unfolded DP_simple_def] obtain l r h us where s: "s i = \<sharp> l"
      and t: "t i = \<sharp> (Fun h us)" and lr: "(l,r) \<in> R" and ru: "r \<unrhd> Fun h us"
      and h: "(h,length us) \<in> D" by auto
    from nvar[OF lr]
    obtain f ls where l: "l = Fun f ls" by (cases l, auto)
    from lr[unfolded l] have f: "defined R (f, length ls)" unfolding defined_def by auto
    from ru obtain C where r: "r = C\<langle>Fun h us\<rangle>" by auto
    have si: "?u (s i \<cdot> \<sigma> i) =  l \<cdot> \<sigma> i" unfolding s l using unshp[OF D[OF f]]
      by simp
    define \<tau> where "\<tau> = (\<lambda> x. if x \<in> vars_term (s i) \<union> vars_term (t i) then \<sigma> i x else s 0 \<cdot> \<sigma> 0)" 
    have l\<tau>: "l \<cdot> \<tau> = l \<cdot> \<sigma> i" 
      by (rule term_subst_eq, insert s, auto simp: \<tau>_def)
    have h_us_\<tau>: "(Fun h us) \<cdot> \<tau> = (Fun h us) \<cdot> \<sigma> i" 
      by (rule term_subst_eq, insert t, auto simp: \<tau>_def)
    from ichain have "s i \<cdot> \<sigma> i \<in> NF_terms Q" and nfs: "NF_subst nfs (s i, t i) (\<sigma> i) Q"
      by auto
    from NF_imp_subt_NF[OF this(1)]
    have "\<forall> t \<in> set (args (s i \<cdot> \<sigma> i)). t \<in> NF_terms Q"
      unfolding NF_terms_args_conv .
    then have "\<forall> t \<in> set (args (l \<cdot> \<sigma> i)). t \<in> NF_terms Q" unfolding s l by simp
    then have NF: "\<forall> t \<lhd> l \<cdot> \<tau>. t \<in> NF_terms Q" unfolding l\<tau> NF_terms_args_conv .
    {
      assume nfs
      with nfs[unfolded NF_subst_def] have nfs: 
        "\<sigma> i ` vars_term (s i)  \<subseteq> NF_terms Q" 
        "\<sigma> i ` vars_term (t i)  \<subseteq> NF_terms Q"
        unfolding vars_rule_def by auto
      then have tau: "\<tau> x \<in> NF_terms Q" for x unfolding \<tau>_def using ichain by auto
      then have "NF_subst nfs (l,r) \<tau> Q" by auto
    }
    then have nfs: "NF_subst nfs (l,r) \<tau> Q" by (cases nfs, auto)
    have step: "(l \<cdot> \<sigma> i, r \<cdot> \<tau>) \<in> qrstep nfs Q R" unfolding l\<tau>[symmetric]
      by (rule qrstepI[OF _ lr, of \<tau> _ _ \<box>, OF NF], auto simp: nfs)
    have supt: "(r \<cdot> \<tau>, Fun h us \<cdot> \<sigma> i) \<in> {\<rhd>}\<^sup>=" unfolding h_us_\<tau>[symmetric] 
      using supteq_subst[OF ru, of \<tau>] unfolding supteq_supt_set_conv .
    from ichain have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q R)\<^sup>*" by auto    
    have "(?u (t i \<cdot> \<sigma> i), ?u (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> (qrstep nfs Q R)\<^sup>*" 
    proof (cases "unshp = id")
      case False
      have steps: "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (nrqrstep nfs Q R)\<^sup>*"
      proof (rule qrsteps_imp_nrqrsteps[OF varcond ndef_applicable_rules steps])
        show "\<not> defined R (the (root (t i \<cdot> \<sigma> i)))"
          unfolding t using shp False h by auto
      qed
      from nrqrsteps_imp_sharp_qrsteps[OF steps, of unshp]
      show ?thesis
        unfolding qrstep_iff_rqrstep_or_nrqrstep by regexp
    next
      case True
      from steps show ?thesis unfolding True sharp_term_id .
    qed
    then have steps: "(Fun h us \<cdot> \<sigma> i, ?u (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> (qrstep nfs Q R)\<^sup>*"
      unfolding t using unshp[OF h] by simp
    from si step supt steps have steps: "(?u (s i \<cdot> \<sigma> i), ?u (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in>
      qrstep nfs Q R O {\<rhd>}^= O (qrstep nfs Q R)\<^sup>*" by auto
    have "(?u (s i \<cdot> \<sigma> i), ?u (s (Suc i) \<cdot> \<sigma> (Suc i))) \<in> ?r^+"
      by (rule set_mp[OF _ steps], regexp)
  } note main = this
  obtain u where u: "u = (\<lambda> i. ?u (s i \<cdot> \<sigma> i))" by auto
  from main have "\<And> i. (u i, u (Suc i)) \<in> ?r^+" unfolding u .
  then have "\<not> SN (?r^+)" by auto
  then have "\<not> SN ?r" using SN_imp_SN_trancl[of ?r] by auto
  then show False using SN_imp_SN_union_supt[OF SN ctxt_closed_qrstep] ..
qed

lemma SN_imp_finite_dpp:
  fixes R :: "('f, 'v) trs"
  assumes SN: "SN (qrstep nfs Q R)"
    and shp: "\<And> f n. unshp \<noteq> id \<Longrightarrow> defined R (f, n) \<Longrightarrow> \<not> defined R (\<sharp> f, n)"
    and unshp: "\<And> f n. defined R (f,n) \<Longrightarrow> unshp (\<sharp> f) = f"
    and nfs: "nfs \<Longrightarrow> \<forall> l r. (l, r) \<in> R \<longrightarrow> is_Fun l"
  shows "finite_dpp (nfs, m, DP \<sharp> R, {}, Q, {}, R)"
by (rule finite_dpp_mono[OF SN_imp_finite_dpp_simple[OF SN shp unshp _ nfs, of "{fn . defined R fn}"]])
   (auto simp: DP_on_subset_DP_simple)

end

end
