(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2016)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Term_Order
imports
  First_Order_Rewriting.Trs
  Complexity
  Weighted_Path_Order.List_Order
  Weighted_Path_Order.Precedence
  Weighted_Path_Order.Status
begin

locale compat =
  fixes  S :: "'a rel" 
  and   NS :: "'a rel" 
  assumes compat: "NS O S \<subseteq> S"
begin

lemma trCompat: "NS^* O S \<subseteq> S" using compat by (rule compat_tr_compat)

lemma trans_split_NS_S_union:
  assumes "r^* \<subseteq> (NS \<union> S)^*"
  shows "r^* \<subseteq> S O S^* O NS^* \<union> NS^*"
proof(rule subrelI)
  fix x y
  assume "(x, y)  \<in> r^*"
  with assms have  "(x,y) \<in> (NS \<union> S)^*" by auto
  then show "(x,y) \<in> S O S^* O NS^* \<union> NS^*" using compatible_rtrancl_split[where S = S and NS = NS] compat by auto
qed
end

locale rewrite_pair = fixes S NS :: "('f,'v)trs" 
  assumes 
    ctxt_NS: "ctxt.closed NS"
    and subst_S: "subst.closed S"
    and subst_NS: "subst.closed NS"
begin
lemmas S_stable = subst.closedD[OF subst_S]
lemmas NS_stable = subst.closedD[OF subst_NS]
lemmas NS_mono = ctxt_closed_one[OF ctxt_NS]

lemma subst_NSS: "subst.closed (NS \<union> S)"
using subst_S and subst_NS by blast

lemma mono_NSS: "ctxt.closed S \<Longrightarrow> ctxt.closed (NS \<union> S)" using ctxt_NS by blast

lemma mono_rstep_NSS:
  assumes mono: "ctxt.closed S"
  shows "rstep (NS \<union> S) \<subseteq> NS \<union> S"
proof -
  from rstep_subset[OF mono_NSS[OF mono] subst_NSS]
  show ?thesis by auto
qed

lemma mono_rstep_S:
  assumes mono: "ctxt.closed S"
  shows "rstep S \<subseteq> S"
proof -
  from rstep_subset[OF mono subst_S]
  show ?thesis by auto
qed

lemma mono_rstep_NSS_rtrancl:
  assumes mono: "ctxt.closed S"
  shows "(rstep (NS \<union> S))^* \<subseteq> (NS \<union> S)^*"
  by (rule rtrancl_mono[OF mono_rstep_NSS[OF mono]])

lemma rstep_NS: "rstep NS \<subseteq> NS"
  using rstep_subset[OF ctxt_NS subst_NS] by simp

lemma rstep_NS_rtrancl: "(rstep NS)^* \<subseteq> NS^*" 
  by (rule rtrancl_mono[OF rstep_NS])
end

locale redpair = rewrite_pair S NS + SN_ars S 
  for S NS :: "('f,'v)trs" 

locale redpair_order = redpair S NS + pre_order_pair S NS for S NS :: "('f,'v)trs" 

locale rewrite_order = rewrite_pair S NS + pre_order_pair S NS for S NS :: "('f,'v)trs"

locale compat_redpair_order = redpair_order S NS + compat_pair S NS for S NS :: "('f,'v)trs" 

lemma (in rewrite_pair) rewrite_order: "rewrite_order (S^+) (NS^*)" (is "rewrite_order ?S ?NS")
proof 
  show "subst.closed ?NS" by (rule subst.closed_rtrancl[OF subst_NS])
  show "subst.closed ?S" by (rule subst.closed_trancl[OF subst_S])
  show "ctxt.closed ?NS" by (rule ctxt.closed_rtrancl[OF ctxt_NS])
  show "refl ?NS" by (rule refl_rtrancl)
  show "trans ?NS" by (rule trans_rtrancl)
  show "trans ?S" by (rule trans_trancl)
qed 

context redpair
begin
lemma redpair_order: "redpair_order (S^+) (NS^*)" (is "redpair_order ?S ?NS")
proof -
  interpret rewrite_order ?S ?NS by (rule rewrite_order)
  show ?thesis
  proof
    show "SN ?S" by (rule SN_imp_SN_trancl[OF SN])
  qed
qed 
end

locale pre_redtriple = redpair S NS 
  for S NS :: "('f,'v)trs" +
  fixes NST :: "('f,'v)trs" 
  assumes compat_NST: "NST O S \<subseteq> S"
    and subst_NST: "subst.closed NST"

locale pre_redtriple_order = pre_redtriple S NS NST + redpair_order S NS 
  for S NS NST :: "('f,'v)trs" +
  assumes  trans_NST: "trans NST"

lemma (in pre_redtriple) pre_redtriple_order: 
  "pre_redtriple_order (S^+) (NS^*) (NST^*)"
  (is "pre_redtriple_order ?S ?NS ?NST")
proof -
  from redpair_order interpret redpair_order ?S ?NS .
  show ?thesis
  proof
    show "subst.closed ?NST" by (rule subst.closed_rtrancl[OF subst_NST])
    show "?NST O ?S \<subseteq> ?S" unfolding trancl_unfold_left 
    proof (clarsimp)
      fix x y z u
      assume "(x,y) \<in> ?NST" and "(y,z) \<in> S" and zu: "(z,u) \<in> S^*"
      with compat.trCompat[unfolded compat_def, OF compat_NST] have "(x,z) \<in> S" by blast
      with zu show "(x,u) \<in> S O S^*" by auto
    qed 
    show "trans ?NST" by (rule trans_rtrancl)
  qed 
qed

definition "top_mono NS NST = (\<forall> f bef s t aft. (s,t) \<in> NS \<longrightarrow>
  (Fun f (bef @ s # aft),  Fun f (bef @ t # aft)) \<in> NST)" 

lemma top_mono_same: "ctxt.closed NS \<Longrightarrow> top_mono NS NS" 
  unfolding top_mono_def by (simp add: ctxt_closed_one)

locale root_redtriple = pre_redtriple S NS NST for S NS NST :: "('f,'v)trs" +
  assumes top_mono: "top_mono NS NST" 
begin

lemma compat_NS_root: "(s,t) \<in> NS \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NST"
  using top_mono[unfolded top_mono_def] by auto

lemma nrrstep_imp_NST: assumes R: "R \<subseteq> NS"
  and step: "(s,t) \<in> nrrstep R" 
  shows "(s,t) \<in> NST"
proof -
  from step[unfolded nrrstep_def']
  obtain l r C \<sigma> where one: "(l,r) \<in> R" "C \<noteq> \<box>" "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  then obtain f bef D aft where "C = More f bef D aft" by (cases C, auto)
  with one have id: "s = Fun f (bef @ D\<langle>l\<cdot>\<sigma>\<rangle> # aft)" "t = Fun f (bef @ D\<langle>r\<cdot>\<sigma>\<rangle> # aft)" by auto
  from one R have "(l,r) \<in> NS" by auto
  with subst_NS have "(l\<cdot>\<sigma>,r\<cdot>\<sigma>) \<in> NS" unfolding subst.closed_def by auto
  from ctxt.closedD[OF ctxt_NS this] have "(D\<langle>l\<cdot>\<sigma>\<rangle>,D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> NS" .
  from compat_NS_root[OF this]
  show "(s,t) \<in> NST" unfolding id .
qed

lemma compat_NSs_root: 
  "(s,t) \<in> NS^* \<Longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NST^*"
  by (induct rule: rtrancl_induct, insert compat_NS_root[of _ _ f bef aft], force+)


lemma nrrsteps_imp_NST: assumes R: "R \<subseteq> NS"
  and steps: "(s,t) \<in> (nrrstep R)^*" 
  shows "(s,t) \<in> NST^*"
  using steps
  by (induct rule: converse_rtrancl_induct, insert nrrstep_imp_NST[OF R], force+)

lemma nrrstep_compat: "nrrstep NS O S \<subseteq> S"
proof
  fix s t
  assume "(s,t) \<in> nrrstep NS O S"
  then obtain u where NS: "(s,u) \<in> nrrstep NS" and u: "(u,t) \<in> S" by auto
  from compat_NST nrrstep_imp_NST[OF subset_refl NS] u show "(s,t) \<in> S" by auto
qed

lemma compat_NSTs: "(s,t) \<in> NST^* \<Longrightarrow> (t,u) \<in> S \<Longrightarrow> (s,u) \<in> S"
  by (induct rule: converse_rtrancl_induct, insert compat_NST, auto)
end

sublocale root_redtriple \<subseteq> nrr: compat S "nrrstep NS \<union> NST" 
  by (unfold_locales, insert nrrstep_compat compat_NST, auto)

locale redtriple = pre_redtriple S NS NST + compat_pair S NS for S NS NST :: "('f,'v)trs" 
  + assumes S_imp_NS: "S \<subseteq> NS"

sublocale redtriple \<subseteq> both: compat S "NS \<union> NST"
  by (unfold_locales, insert compat_NS_S compat_NST, auto)

sublocale redtriple \<subseteq> NS: compat S NS
  by (unfold_locales, insert compat_NS_S compat_NST, auto)


locale redtriple_order = redtriple S NS NST + pre_redtriple_order S NS NST + order_pair S NS for S NS NST :: "('f,'v)trs" +
  assumes refl_NST: "refl NST"

sublocale redtriple_order \<subseteq> SN_order_pair  
  by (unfold_locales, rule SN)

locale root_redtriple_order = root_redtriple S NS NST + pre_redtriple_order S NS NST for S NS NST :: "('f,'v)trs"

lemma (in redtriple) redtriple_order: "redtriple_order (S^+) (NS^*) (NST^*)"
  (is "redtriple_order ?S ?NS ?NST")
proof -
  from pre_redtriple_order interpret pre_redtriple_order ?S ?NS ?NST .
  show ?thesis
  proof
    show "?NS O ?S \<subseteq> ?S" unfolding trancl_unfold_left by (simp add: order_simps)
    show "?S O ?NS \<subseteq> ?S" unfolding trancl_unfold_right by (simp add: order_simps)
    show "refl ?NST" by (rule refl_rtrancl)
    show "?S \<subseteq> ?NS" using trancl_mono[OF _ S_imp_NS] by force
  qed
qed

lemma (in root_redtriple) root_redtriple_order: "root_redtriple_order (S^+) (NS^*) (NST^*)"
proof -
  let ?NS = "NS^*"
  let ?NST = "NST^*"
  let ?S = "S^+"
  from pre_redtriple_order interpret pre_redtriple_order ?S ?NS ?NST .
  show ?thesis
  proof (unfold_locales, unfold top_mono_def, intro allI impI)
    fix s t f bef aft u
    assume st: "(s,t) \<in> ?NS" 
    have "(s,t) \<in> (rstep NS)^*" by (rule set_mp[OF rtrancl_mono st], auto)
    from nrrsteps_imp_NST[OF _ rsteps_ctxt_imp_nrrsteps[OF this, of "More f bef \<box> aft"]]
    show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ?NST" by auto  
  qed
qed

lemma (in redpair_order) all_ctxt_closed: "all_ctxt_closed F NS"
  by (rule trans_ctxt_imp_all_ctxt_closed[OF trans_NS refl_NS ctxt_NS])


fun ce_trs :: "('f \<times> nat) \<Rightarrow> ('f,'v)trs"
where "ce_trs (c,n) = 
  {(Fun c (t # s # replicate n (Var undefined)), t) | t s. True}
  \<union> {(Fun c (t # s # replicate n (Var undefined)), s) | t s. True}"

fun comb :: "('f \<times> nat) \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term" where 
  "comb (c,n) (t # ts) = Fun c (t # comb (c,n) ts # replicate n (Var undefined))"

lemma ce_trs_sound: "t \<in> set ts \<Longrightarrow> (comb cn ts, t) \<in> (rstep (ce_trs cn))^+"
proof (induct ts, simp)
  case (Cons s ss)
  obtain c n where cn: "cn = (c,n)" by force
  show ?case 
  proof (cases "s = t")
    case True 
    with cn have "(comb cn (s # ss),s) \<in> ce_trs cn" by simp
    then have "(comb cn (s # ss),t) \<in> rstep (ce_trs cn)" using True by blast
    then show ?thesis using True by force
  next
    case False
    then have ind: "(comb cn ss, t) \<in> (rstep (ce_trs cn))^+" using Cons by auto
    from cn have "(comb cn (s # ss),comb cn ss) \<in> ce_trs cn" by simp
    then have "(comb cn (s # ss),comb cn ss) \<in> rstep (ce_trs cn)" by blast 
    with ind show ?thesis by auto
  qed
qed

declare ce_trs.simps[simp del] comb.simps[simp del]


type_synonym 'f af = "('f \<times> nat) \<Rightarrow> nat set"

fun af_regarded_pos :: "'f af \<Rightarrow> ('f,'v)term \<Rightarrow> pos \<Rightarrow> bool"
  where "af_regarded_pos \<pi> t [] = True"
      | "af_regarded_pos \<pi> (Fun f ts) (Cons i p) = (i < length ts \<and> i \<in> \<pi> (f,length ts) \<and> af_regarded_pos \<pi> (ts ! i) p)"
      | "af_regarded_pos \<pi> (Var _) (Cons i p) = False"

lemma af_regarded_pos_append: "af_regarded_pos \<mu> t (p @ q) = 
  (af_regarded_pos \<mu> t p \<and> af_regarded_pos \<mu> (t |_p) q)"
  by (induct p arbitrary: t, simp, case_tac t, auto)

definition af_inter :: "'f af \<Rightarrow> 'f af \<Rightarrow> 'f af" where
  "af_inter \<pi> \<mu> f = \<pi> f \<inter> \<mu> f"

lemma af_regarded_pos_af_inter: 
  "af_regarded_pos (af_inter \<pi> \<mu>) t p = (af_regarded_pos \<pi> t p \<and> af_regarded_pos \<mu> t p)"
proof (induct p arbitrary: t)
  case (Cons i p t)
  then show ?case by (cases t, auto simp: af_inter_def)
qed simp

definition af_compatible :: "'f af \<Rightarrow> ('f,'v)trs \<Rightarrow> bool"
where "af_compatible \<pi> ord \<equiv>
   (\<forall> f bef s t aft. length bef \<in> \<pi> (f, (Suc (length bef + length aft))) \<or>
   (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ord)"

context
  fixes \<mu> :: "'f af"
begin

definition af_monotone :: "('f,'v)trs \<Rightarrow> bool"
where "af_monotone ord \<equiv>
   (\<forall> f bef s t aft. length bef \<in> \<mu> (f, (Suc (length bef + length aft)))
     \<longrightarrow> (s,t) \<in> ord \<longrightarrow> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ord)"

lemma af_monotoneD: assumes "af_monotone ord"
  and "length bef \<in> \<mu> (f, (Suc (length bef + length aft)))"
  and "(s,t) \<in> ord"
  shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ord" 
  using assms unfolding af_monotone_def by auto

lemma af_monotoneI: 
  assumes "\<And> f bef s t aft. 
  length bef \<in> \<mu> (f, (Suc (length bef + length aft))) \<Longrightarrow>
  (s,t) \<in> ord \<Longrightarrow>(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ord" 
  shows "af_monotone ord"
  using assms unfolding af_monotone_def by auto

lemma ctxt_closed_imp_af_monotone: assumes "ctxt.closed ord"
  shows "af_monotone ord"
  by (rule af_monotoneI[OF ctxt_closed_one[OF assms]])

lemma af_monotone_af_regarded_posD: assumes mono: "af_monotone ord"
  and *: "af_regarded_pos \<mu> (C\<langle>s\<rangle>) (hole_pos C)" and st: "(s,t) \<in> ord"
  shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ord"
  using *
proof (induct C)
  case (More f bef C aft)
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  from More(2) have i: "?i \<in> \<mu> (f,?n)" and af: "af_regarded_pos \<mu> (C\<langle>s\<rangle>) (hole_pos C)" by auto
  from More(1)[OF af] have "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ord" by auto
  from af_monotoneD[OF mono i this] show ?case by simp
qed (insert st, auto)
end

definition af_subset :: "'f af \<Rightarrow> 'f af \<Rightarrow> bool" where 
  "af_subset \<pi> \<mu> \<equiv> \<forall> f. \<pi> f \<subseteq> \<mu> f"

lemma af_subset_refl[simp]: "af_subset \<mu> \<mu>" unfolding af_subset_def by auto

lemma af_subset_af_monotone: "af_subset \<mu> \<mu>' \<Longrightarrow> af_monotone \<mu>' ord \<Longrightarrow> af_monotone \<mu> ord"
  unfolding af_subset_def af_monotone_def by force


lemma af_compatible_af_regarded_ctxt: assumes af: "af_compatible \<pi> ord"
  and ctxt: "ctxt.closed ord"
  and not: "\<not> af_regarded_pos \<pi> (C\<langle>u\<rangle>) (hole_pos C)"
  shows "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> ord"
  using not
proof (induct C)
  case Hole
  then show ?case by simp
next
  case (More f bef C aft)
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  let ?pi = "?i \<in> \<pi> (f,?n)"
  show ?case 
  proof (cases ?pi)
    case True
    with More(2) have "\<not> af_regarded_pos \<pi> (C\<langle>u\<rangle>) (hole_pos C)" by simp
    from More(1)[OF this] have "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> ord" .
    from ctxt_closed_one[OF ctxt this]
    show ?thesis by auto
  next
    case False
    with af[unfolded af_compatible_def, rule_format, of bef f]
    show ?thesis by auto
  qed
qed

definition full_af :: "'f af" where "full_af fn \<equiv> {0 ..< snd fn}"

definition empty_af :: "'f af" where "empty_af fn \<equiv> {}"

lemma full_af: "af_compatible full_af r" unfolding af_compatible_def full_af_def by auto
lemma empty_af: "af_monotone empty_af r" unfolding af_monotone_def empty_af_def by auto

lemma af_monotone_full_af_imp_ctxt_closed:
  assumes mono: "af_monotone full_af r"
  shows "ctxt.closed r"
proof (rule one_imp_ctxt_closed)
  fix f bef s t aft
  assume st: "(s,t) \<in> r"
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r"
    by (rule af_monotoneD[OF mono _ st], auto simp: full_af_def)
qed

lemma af_regarded_poss: "af_regarded_pos \<pi> t p \<Longrightarrow> p \<in> poss t"
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p t)
  show ?case
  proof (cases t)
    case (Var x)
    show ?thesis using Cons(2) unfolding Var by simp
  next
    case (Fun f ts)
    show ?thesis using Cons(2) Cons(1)[of "ts ! i"] unfolding Fun by auto
  qed
qed

lemma af_regarded_full: "af_regarded_pos full_af t p = (p \<in> poss t)"
proof (induct p arbitrary: t)
  case Nil
  show ?case by simp
next
  case (Cons i p t)
  show ?case
  proof (cases t)
    case (Var x)
    show ?thesis unfolding Var by simp
  next
    case (Fun f ts)
    show ?thesis using Cons[of "ts ! i"] unfolding Fun by (auto simp: full_af_def)
  qed
qed

lemma af_steps_imp_orient: assumes tran: "trans r" 
  and refl: "refl r"
  and ctxt: "ctxt.closed r" 
  and len: "length ts = length (ss :: ('f,'v)term list)"
  and steps: "\<forall>i<length ts. p i \<longrightarrow> (ts ! i, ss ! i) \<in> r"
  and compat: "\<forall> bef s t aft. ((length ts = Suc (length bef + length aft)) \<longrightarrow> (p (length bef) \<or> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r))"
  shows "(Fun f ts, Fun f ss) \<in> r" 
proof -
  from trans_refl_imp_rtrancl_id[OF tran refl] have r: "r^* = r" by auto
  let ?rel = "\<lambda> i. if p i then r else UNIV"
  have "(Fun f ts, Fun f ss) \<in> r^*"
  proof (rule args_steps_imp_steps_gen[OF _ len, of ?rel])
    fix i
    assume i: "i < length ss"
    with len steps show "(ts ! i, ss ! i) \<in> (?rel i)^*" by auto
  next
    fix bef aft :: "('f,'v)term list" and s t 
    assume rel: "(s,t) \<in> ?rel (length bef)" and len': "length ss = Suc (length bef + length aft)"
    from compat[rule_format, OF len'[unfolded len[symmetric]]]
    have "p (length bef) \<or> (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r" .
    then show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> r^*"
    proof
      assume "p (length bef)"
      with rel have "(s,t) \<in> r" by auto
      from ctxt_closed_one[OF ctxt this] show ?thesis by auto
    qed auto
  qed
  then show ?thesis unfolding r .
qed

locale af_redpair = redpair  S NS for S NS :: "('f,'v)trs"+
  fixes \<pi> :: "'f af"
  assumes af_compat: "af_compatible \<pi> NS"
begin
lemma af_redpair_order: "af_redpair (S^+) (NS^*) \<pi>"
proof -
  let ?NS = "NS^*"
  let ?S = "S^+"
  from redpair_order interpret redpair_order ?S ?NS .
  show ?thesis
  proof
    show "af_compatible \<pi> ?NS" using af_compat
      unfolding af_compatible_def by blast
  qed
qed
end

definition ce_compatible :: "('f,'v)trs \<Rightarrow> bool" where
  "ce_compatible rel = (\<exists> n. \<forall> m. m \<ge> n \<longrightarrow> (\<forall> c. ce_trs (c,m) \<subseteq> rel))" 

lemma ce_compatibleE: assumes "ce_compatible rel" 
  obtains n where "\<And> c m. m \<ge> n \<Longrightarrow> ce_trs (c,m) \<subseteq> rel" 
  using assms unfolding ce_compatible_def by blast

locale ce_redpair = redpair S NS for S NS :: "('f,'v)trs"+ 
  assumes NS_ce_compat: "ce_compatible NS"
begin 
lemma ce_redpair_order: "ce_redpair (S^+) (NS^*)"
proof -
  let ?S = "S^+"
  let ?NS = "NS^*"
  from redpair_order interpret redpair_order ?S ?NS .
  show ?thesis using NS_ce_compat
    by (unfold_locales; unfold ce_compatible_def; blast)
qed
end

locale af_redtriple_order = redtriple_order S NS NST + af_redpair S NS \<pi> for S NS NST \<pi>

locale ce_af_redpair = ce_redpair S NS + af_redpair S NS \<pi>
  for S NS :: "('f,'v)trs" and \<pi>

locale ce_redtriple = redtriple  S NS NST + ce_redpair S NS for S NS NST :: "('f,'v)trs"
begin
lemma ce_redtriple_order: "ce_redtriple (S^+) (NS^*) (NST^*)"
proof -
  let ?S = "S^+"
  let ?NS = "NS^*"
  let ?NST = "NST^*"
  from redtriple_order ce_redpair_order interpret redtriple_order ?S ?NS ?NST + ce_redpair ?S ?NS .
  show ?thesis by (unfold_locales)
qed
end


locale af_root_redtriple_order = root_redtriple_order S NS NST + af_redpair S NS \<pi> for S NS NST :: "('f,'v)trs" and \<pi> +
  fixes \<pi>' :: "'f af"              
  assumes af_compat': "af_compatible \<pi>' NST"

locale af_redtriple = redtriple S NS NST + af_redpair S NS \<pi> for S NS NST :: "('f,'v)trs" and \<pi>

locale ce_af_redtriple = ce_redtriple S NS NST + ce_af_redpair S NS \<pi> for S NS NST :: "('f,'v)trs" and \<pi>

sublocale ce_af_redtriple \<subseteq> af_redtriple ..

locale ce_af_redtriple_order = ce_redtriple S NS NST + ce_af_redpair S NS \<pi> + redtriple_order S NS NST for S NS NST :: "('f,'v)trs" and \<pi>

sublocale ce_af_redtriple_order \<subseteq> ce_af_redtriple ..

lemma (in ce_af_redtriple) ce_af_redtriple_order: "ce_af_redtriple_order (S^+) (NS^*) (NST^*) \<pi>"
proof -
  let ?S = "S^+"
  let ?NS = "NS^*"
  let ?NST = "NST^*"
  from redtriple_order ce_redpair_order af_redpair_order interpret redtriple_order ?S ?NS ?NST + ce_redpair ?S ?NS + af_redpair ?S ?NS \<pi> .
  show ?thesis by (unfold_locales)
qed

locale mono_redpair = redpair S NS + compat_pair S NS for S NS :: "('f,'v)trs" +
  assumes ctxt_S: "ctxt.closed S"

locale mono_redtriple = redtriple S NS NST + mono_redpair S NS for S NS NST :: "('f,'v)trs"

locale mono_redtriple_order = redtriple_order S NS NST + mono_redpair S NS for S NS NST :: "('f,'v)trs"

sublocale mono_redtriple_order \<subseteq> mono_redtriple ..

locale mono_ce_redtriple = mono_redtriple S NS NST + ce_redpair S NS for S NS NST :: "('f,'v)trs" + 
  assumes S_ce_compat: "ce_compatible S" 
begin 
lemma mono_ce_redtriple_order: "mono_ce_redtriple (S^+) (NS^*) (NST^*)"
proof -
  let ?S = "S^+"
  let ?NS = "NS^*"
  let ?NST = "NST^*"
  have subset: "\<And> x. x \<in> S \<Longrightarrow> x \<in> ?S" by auto
  from redtriple_order ce_redpair_order interpret redtriple_order ?S ?NS ?NST + ce_redpair ?S ?NS .
  show ?thesis using S_ce_compat subset ctxt.closed_trancl[OF ctxt_S]
    by (unfold_locales, unfold ce_compatible_def) (blast)+
qed

lemma orient_implies_var_cond: 
  assumes ctxt: "ctxt.closed S"
  and lr: "(l,r) \<in> NS \<union> S"
  shows "vars_term r \<subseteq> vars_term l"
proof (rule ccontr)
  interpret both: redpair "S^+" "((NS \<union> S)^*)"
    by (unfold_locales, insert ctxt ctxt_NS subst_S subst_NS SN, auto intro: SN_imp_SN_trancl)
  interpret order: redtriple_order "S^+" "NS^*" "NST^*" by (rule redtriple_order)
  from S_ce_compat obtain c n where ce: "ce_trs (c,n) \<subseteq> S" 
    unfolding ce_compatible_def by blast  
  define t where "t = comb (c,n) [l]"
  have "(t,l) \<in> (rstep (ce_trs (c,n)))^+"
    unfolding t_def 
    by (rule ce_trs_sound, simp)
  with rstep_subset[OF ctxt subst_S ce] have tl: "(t,l) \<in> S^+" by (metis trancl_mono)
  assume "\<not> ?thesis"
  then obtain x where xr: "x \<in> vars_term r" and xl: "x \<notin> vars_term l" by auto
  define \<sigma> where "\<sigma> \<equiv> \<lambda> y. if y = x then Fun c [t] else Var y"
  from lr have "(l,r) \<in> (NS \<union> S)^*" by auto
  from subst.closedD[OF both.subst_NS this]
  have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> (NS \<union> S)^*" by auto
  also have "l \<cdot> \<sigma> = l \<cdot> Var"
    by (rule term_subst_eq, insert xl, auto simp: \<sigma>_def)
  also have "\<dots> = l" by simp
  finally have step: "(l, r \<cdot> \<sigma>) \<in> (NS \<union> S)^*" by auto
  have "r \<cdot> \<sigma> \<unrhd> Var x \<cdot> \<sigma>" 
    by (rule supteq_subst, insert xr, auto)
  also have "Var x \<cdot> \<sigma> = Fun c [t]" unfolding \<sigma>_def by auto
  also have "Fun c [t] \<rhd> t" by auto
  finally have rt: "r \<cdot> \<sigma> \<rhd> t" by simp
  from NS.trCompat obtain A B where NSS: "NS^* O S = A" and S: "S = A \<union> B" by blast+
  from tl step rt  have tt: "(t,t) \<in> (S^+ O (NS \<union> S)^*) O {\<rhd>}" by auto
  have "S^+ O (NS \<union> S)^* \<subseteq> S^+ O ((NS^* O S)^* \<union> (NS^* O S)^* O NS^*)" by regexp
  also have "\<dots> \<subseteq> S^+ O (S^* \<union> S^* O NS^*)" unfolding NSS unfolding S by regexp
  also have "\<dots> = S^+ O NS^*" by regexp
  also have "\<dots> \<subseteq> S^+" by (rule order.compat_S_NS)
  finally have tt: "(t,t) \<in> S^+ O {\<rhd>}" using tt by auto
  let ?rel = "(S^+ \<union> {\<rhd>})"
  from tt have tt: "(t,t) \<in> ?rel O ?rel" by auto
  then have tt: "(t,t) \<in> ?rel^+" by regexp
  from SN_imp_SN_trancl[OF SN_imp_SN_union_supt[OF both.SN ctxt.closed_trancl[OF ctxt]]]
  have "SN (?rel^+)" .
  then show False using refl_not_SN[OF tt] by blast
qed
end
  

locale mono_ce_af_redtriple = ce_af_redtriple S NS NST \<pi> + mono_ce_redtriple S NS NST for S NS NST :: "('f,'v)trs" and \<pi>

locale mono_ce_af_redtriple_order = mono_ce_af_redtriple S NS NST \<pi> + redtriple_order S NS NST for S NS NST :: "('f,'v)trs" and \<pi>

sublocale mono_ce_af_redtriple_order \<subseteq> ce_af_redtriple_order ..

lemma (in mono_ce_af_redtriple)  mono_ce_af_redtriple_order: "mono_ce_af_redtriple_order (S^+) (NS^*) (NST^*) \<pi>"
proof -
  let ?S = "S^+"
  let ?NS = "NS^*"
  let ?NST = "NST^*"
  from ce_af_redtriple_order mono_ce_redtriple_order interpret ce_af_redtriple_order ?S ?NS ?NST \<pi> + mono_ce_redtriple ?S ?NS ?NST .
  show ?thesis ..
qed

locale cpx_term_rel = 
  fixes S :: "('f,'v)trs" 
    and cpx_class :: "('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> bool"
  assumes cpx_class: "\<And> cm cc. cpx_class cm cc \<Longrightarrow> deriv_bound_measure_class S cm cc"

locale cpx_ce_af_redtriple_order =
  ce_af_redtriple_order S NS NST \<pi> + cpx_term_rel S cpx_class 
  for S NS NST :: "('f, 'v) trs" and \<pi> \<mu> :: "'f af" and cpx_class +
  assumes \<mu>: "af_monotone \<mu> S"

locale ws_rewrite_order = rewrite_order S NS + order_pair S NS 
  for S NS :: "('f,'v)trs" +
  fixes \<sigma> :: "'f status"
  assumes ws_status: "i \<in> set (status \<sigma> f) \<Longrightarrow> simple_arg_pos NS f i"
    and S_imp_NS: "S \<subseteq> NS"
begin

lemmas \<sigma> = status[of \<sigma>]

lemma NS_arg: assumes i: "i \<in> set (status \<sigma> (f,length ts))"
  shows "(Fun f ts, ts ! i) \<in> NS"
  by (rule ws_status[OF i, unfolded simple_arg_pos_def fst_conv, rule_format],
  insert \<sigma>[of f "length ts"] i, auto)

lemma NS_subterm: assumes all: "\<And> f k. set (status \<sigma> (f,k)) = {0 ..< k}"
  shows "s \<unrhd> t \<Longrightarrow> (s,t) \<in> NS"
proof (induct s t rule: supteq.induct)
  case (refl)
  from refl_NS show ?case unfolding refl_on_def by blast
next
  case (subt s ss t f)
  from subt(1) obtain i where i: "i < length ss" and s: "s = ss ! i" unfolding set_conv_nth by auto
  from NS_arg[of i f ss, unfolded all] s i have "(Fun f ss, s) \<in> NS" by auto
  from trans_NS_point[OF this subt(3)] show ?case .
qed

lemma ce_\<sigma>: assumes "{0,1} \<subseteq> set (status \<sigma> (f,Suc (Suc k)))"
  shows "ce_trs (f,k) \<subseteq> NS"
proof -
  {
    fix s t :: "('f,'v)term"
    assume "(s,t) \<in> ce_trs (f,k)"
    from this[unfolded ce_trs.simps] 
    obtain u v where s: "s = Fun f (u # v # replicate k (Var undefined))" (is "_ = Fun _ ?ss")
      and t: "t = u \<or> t = v" by auto
    from t NS_arg[of 0 f ?ss] NS_arg[of 1 f ?ss] assms 
    have "(s,t) \<in> NS" unfolding s by (cases, auto)
  }
  then show ?thesis by auto
qed
end

locale ws_redpair_order = ws_rewrite_order + SN_ars +
  constrains S :: "('f,'v)trs" 

locale ss_rewrite_order = ws_rewrite_order +
  assumes ss_status: "i \<in> set (status \<sigma> f) \<Longrightarrow> simple_arg_pos S f i"
  and S_non_empty: "S \<noteq> {}" 

definition "supteqrel R = ({\<rhd>} \<union> rstep R)\<^sup>*"

lemma supteqrel_refl [simp]: "(t, t) \<in> supteqrel R" by (auto simp: supteqrel_def)

interpretation relto_pair: order_pair "(relto R E)\<^sup>+" "(R \<union> E)\<^sup>*"
  apply unfold_locales
  apply (fact refl_rtrancl)
  apply (fact trans_trancl)
  apply (fact trans_rtrancl) by regexp+

interpretation suptrel_pair: order_pair "suptrel R" "supteqrel R"
  unfolding suptrel_def unfolding supteqrel_def by standard

lemma supteqrel_subst:
  "(s, t) \<in> supteqrel R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> supteqrel R"
  by (auto simp: supteqrel_def) (metis supt_rsteps_stable)


locale co_discrimination_pair = fixes 
  S NS :: "('f,'v)term rel" 
    assumes ctxt_NS: "ctxt.closed NS"
      and subst_NS: "subst.closed NS"
      and refl_NS: "refl NS"
      and trans_NS: "trans NS" 
      and disj_NS_S: "NS \<inter> (S^-1) = {}" 
begin
lemma rstep_imp_NS: "R \<subseteq> NS \<Longrightarrow> rstep R \<subseteq> NS"
  by (rule rstep_subset[OF ctxt_NS subst_NS])
end

locale co_rewrite_pair = rewrite_pair S NS for 
  S NS :: "('f,'v)term rel" +
  assumes refl_NS: "refl NS"
    and trans_NS: "trans NS" 
    and disj_NS_S: "NS \<inter> (S^-1) = {}" 
begin
sublocale co_discrimination_pair
  by unfold_locales (intro refl_NS trans_NS disj_NS_S subst_NS ctxt_NS)+
end

sublocale compat_redpair_order \<subseteq> co_rewrite_pair
proof
  show "refl NS" by (rule refl_NS)
  show "trans NS" by (rule trans_NS)
  show "NS \<inter> S\<inverse> = {}" 
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain a b where "(a,b) \<in> NS" and "(b, a) \<in> S" by auto
    hence "(a,a) \<in> S" by (rule compat_NS_S_point)
    with SN show False by fast
  qed
qed


locale discrimination_pair = compat S NS (* we only require one side compatibility, although in
  paper it is stated that both directions are required: \<ge> o > \<subseteq> \<ge> *)
  for S NS :: "('f,'v)trs" +
  assumes ctxt_NS: "ctxt.closed NS"
  and subst_NS: "subst.closed NS"
  and irrefl_S: "(t,t) \<notin> S"
begin
lemma rstep_imp_NS: "R \<subseteq> NS \<Longrightarrow> rstep R \<subseteq> NS"
  by (rule rstep_subset[OF ctxt_NS subst_NS])
end  

end
