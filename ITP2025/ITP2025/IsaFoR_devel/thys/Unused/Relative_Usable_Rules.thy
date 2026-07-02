(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory Relative_Usable_Rules
imports
  First_Order_Rewriting.Trs_Impl
  Ord.Reduction_Pair
  Ord.Ordered_Algebra
  Framework.Relative_DP_Framework
begin

subsection \<open>Trivia, TODO: move\<close>
lemma Fun_nrrsteps:
  assumes st: "(Fun f ss,t) \<in> (nrrstep R)\<^sup>*"
  shows "\<exists>ts. t = Fun f ts \<and> length ts = length ss \<and> (\<forall>i<length ss. (ss ! i, ts ! i) \<in> (rstep R)\<^sup>*)"
proof-
  from nrrsteps_preserve_root[OF st] obtain ts where [simp]: "t = Fun f ts" by auto
  from nrrsteps_equiv_num_args[OF st] nrrsteps_imp_arg_rsteps[OF st]
  show ?thesis by auto
qed

lemma Fun_nrrstepI:
  fixes f pre post
  defines "c \<equiv> \<lambda>s. Fun f (pre@s#post)"
  assumes "(s,t) \<in> rstep R"
  shows "(c s, c t) \<in> nrrstep R"
proof-
  from assms obtain C \<sigma> l r where lr: "(l,r) \<in> R" and "s = C\<langle>l\<cdot>\<sigma>\<rangle>" "t = C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
  then have "c s = (More f pre C post)\<langle>l\<cdot>\<sigma>\<rangle>" "c t = (More f pre C post)\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: c_def)
  with lr show ?thesis by (auto intro!: nrrstepI)
qed

lemma nrrstep_subst:
  assumes "(s,t) \<in> nrrstep R"
  shows "(s\<cdot>\<sigma>, t\<cdot>\<sigma>) \<in> nrrstep R"
proof-
  from assms obtain C \<tau> l r
  where lr: "(l,r) \<in> R" and s: "s = C\<langle>l\<cdot>\<tau>\<rangle>" and t: "t = C\<langle>r\<cdot>\<tau>\<rangle>" and C: "C \<noteq> \<box>" by (elim nrrstepE)
  moreover from s have "s\<cdot>\<sigma> = (C\<cdot>\<^sub>c\<sigma>)\<langle>l \<cdot> \<tau> \<circ>\<^sub>s \<sigma>\<rangle>" by auto
  moreover from t have "t\<cdot>\<sigma> = (C\<cdot>\<^sub>c\<sigma>)\<langle>r \<cdot> \<tau> \<circ>\<^sub>s \<sigma>\<rangle>" by auto
  moreover from C have "C\<cdot>\<^sub>c\<sigma> \<noteq> \<box>" using subst_apply_ctxt.elims by auto
  ultimately show ?thesis by (intro nrrstepI)
qed

lemma rstep_small_induct[consumes 1]:
  assumes "(s,t) \<in> rstep R"
      and "\<And>l r \<sigma>. (l,r) \<in> R \<Longrightarrow> P (l\<cdot>\<sigma>) (r\<cdot>\<sigma>)"
      and "\<And>s t f pre post. (s,t) \<in> rstep R \<Longrightarrow> P s t \<Longrightarrow> P (Fun f (pre@s#post)) (Fun f (pre@t#post))"
    shows "P s t"
proof (insert assms(1), elim rstepE, goal_cases)
  case (1 s' t' C \<sigma> l r)
  then show ?case
  proof (induct C arbitrary: s t s' t')
    case Hole with assms(2) show ?case by auto
  next
    case (More f pre C post)
    then have "(C\<langle>l\<cdot>\<sigma>\<rangle>,C\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" "P C\<langle>l\<cdot>\<sigma>\<rangle> C\<langle>r\<cdot>\<sigma>\<rangle>" by auto
    from assms(3)[OF this] More show ?case by auto
  qed
qed

lemma qrstep_small_induct[consumes 1]:
  assumes "(s,t) \<in> qrstep nfs Q R"
      and "\<And>l r \<sigma>. \<forall>u \<lhd> l\<cdot>\<sigma>. u \<in> NF_terms Q \<Longrightarrow> (l,r) \<in> R \<Longrightarrow> NF_subst nfs (l,r) \<sigma> Q \<Longrightarrow> P (l\<cdot>\<sigma>) (r\<cdot>\<sigma>)"
      and "\<And>s t f pre post. (s,t) \<in> qrstep nfs Q R \<Longrightarrow> P s t \<Longrightarrow> P (Fun f (pre@s#post)) (Fun f (pre@t#post))"
  shows "P s t"
proof (insert assms(1), induct rule: qrstep.induct, fact assms)
  case (ctxt s t C)
  then show ?case
  proof(induct C)
    case Hole then show ?case by auto
  next
    case (More f pre C post)
    then have "(C\<langle>s\<rangle>,C\<langle>t\<rangle>) \<in> qrstep nfs Q R" "P C\<langle>s\<rangle> C\<langle>t\<rangle>" by auto
    from assms(3)[OF this] show ?case by auto
  qed
qed

context weak_mono_algebra begin

interpretation base2: ord_syntax less_eq less.

definition "af_compatiblep \<pi> \<equiv>
   \<forall> f bef x y aft. length bef \<in> \<pi> (f, (Suc (length bef + length aft))) \<or>
   I f (bef @ x # aft) \<sqsupseteq> I f (bef @ y # aft)"

lemma af_imp_le:
  assumes "af_compatiblep \<pi>"
  and "length pre \<notin> \<pi> (f, Suc (length pre + length post))"
  shows "I f (pre @ x # post) \<sqsupseteq> I f (pre @ y # post)"
  using assms[unfolded af_compatiblep_def] by blast

lemma "af_compatiblep \<pi> \<Longrightarrow> af_compatible \<pi> {(s,t). s \<sqsupseteq>\<^sub>t t}"
  by (unfold af_compatiblep_def af_compatible_def, force)

lemma af_mono:
  assumes af: "af_compatiblep \<pi>"
      and len: "length xs = length ys"
      and steps: "\<And>i. i \<in> \<pi> (f, length xs) \<Longrightarrow> i < length xs \<Longrightarrow> xs ! i \<sqsupseteq> ys ! i"
  shows "I f xs \<sqsupseteq> I f ys"
proof-
  { fix pre xs' ys' :: "'a list"
    assume "xs = pre @ xs'" "ys = pre @ ys'"
    with steps len have "I f xs \<sqsupseteq> I f ys"
    proof(induct xs' arbitrary: ys ys' pre)
      case Nil with len show ?case by auto
    next
      case IH: (Cons x xs' ys yys')
      from IH.prems have xs: "xs = pre @ x # xs'" by auto
      from IH.prems obtain y ys' where yys': "yys' = y # ys'" by (cases yys', auto)
      with IH.prems have ys: "ys = pre @ y # ys'" by auto
      with IH.prems have len: "length xs = length (pre @ x # ys')" by auto
      from ys have "I f ys = I f (pre @ y # ys')" by auto
      also have "... \<sqsubseteq> I f (pre @ x # ys')"
      proof(cases "length pre \<in> \<pi> (f, length xs)")
        case True from IH.prems(1)[OF this, unfolded IH.prems yys']
        show ?thesis by (auto intro: append_Cons_le_append_Cons)
      next
        case False then show ?thesis by (auto intro: af_imp_le[OF af] simp: len)
      qed
      also have "I f (pre @ x # ys') \<sqsubseteq> I f xs"
      proof(rule IH.hyps)
        from IH.prems show "xs = (pre @ [x]) @ xs'" by auto
        from len show "length xs = length (pre @ x # ys')" by simp
        fix i
        assume i: "i \<in> \<pi> (f, length xs)" "i < length xs"
        then show "(pre @ x # ys') ! i \<sqsubseteq> xs ! i"
        proof(cases "i = length pre")
          case True then show ?thesis by (auto simp: xs)
        next
          case False
          then have "(pre @ x # ys') ! i = (pre @ y # ys') ! i" by (fact append_Cons_nth)
          with IH.prems(1)[unfolded ys, OF i]
          show ?thesis by auto
        qed
      qed auto
      finally show ?case.
    qed
  }
  then show ?thesis by force
qed

end

lemma SN_on_relto_Image_S:
  assumes SN: "SN_on (relto R S) X"
  shows "SN_on (relto R S) (S\<^sup>* `` X)"
proof
  fix seq assume 0: "seq 0 \<in> S\<^sup>* `` X" and 1: "chain (relto R S) seq"
  from 0 obtain x where 2: "x \<in> X" and 3: "(x,seq 0) \<in> S\<^sup>*" by auto
  let ?seq = "\<lambda>i. if i = 0 then x else seq i"
  from 3 spec[OF 1, of 0] have "(x, seq (Suc 0)) \<in> S\<^sup>* O relto R S" by blast
  then have "(?seq 0, ?seq 1) \<in> S\<^sup>* O relto R S" by auto
  then have "(?seq 0, ?seq 1) \<in> relto R S" by regexp
  with 1 have "chain (relto R S) ?seq" by auto
  moreover from 2 have "?seq 0 \<in> X" by auto
  ultimately show False using assms by fast
qed

lemma SN_on_relto_Image:
  assumes SN: "SN_on (relto R S) X"
  shows "SN_on (relto R S) ((R \<union> S)\<^sup>* `` X)"
proof-
  note SN_on_Image_rtrancl[OF SN_on_relto_Image_S[OF SN]]
  note this[folded relcomp_Image]
  also have "S\<^sup>* O (S\<^sup>* O R O S\<^sup>*)\<^sup>* = (R \<union> S)\<^sup>*" by regexp
  finally show ?thesis.
qed

lemma SN_on_lex_rel:
  assumes SN: "SN_on (relto R S) X" and SN': "SN_on R' X"
      and closed: "(R \<union> R') `` X \<subseteq> X"
  shows "SN_on (R \<union> S \<inter> R') X" (is "SN_on ?r _")
proof
  fix f
  assume f0: "f 0 \<in> X" and chain: "chain ?r f"
  from chain have step: "\<And>i. (f i, f (Suc i)) \<in> R \<union> R'" by auto
  have "\<exists> j. \<forall> i \<ge> j. (f i, f (Suc i)) \<in> S - R" by (rule relative_ending, insert chain SN f0, auto)
  with step obtain j where steps: "\<And> i. i \<ge> j \<Longrightarrow> (f i, f (Suc i)) \<in> R'" by auto
  obtain g where g: "g = (\<lambda> i. f (j + i))" by auto
  from steps have "chain R' g" by (auto simp: g)
  moreover
    { fix i have "f i \<in> X" by (induct i, insert f0 step closed, auto) }
    then have "g 0 \<in> X" by (auto simp: g)
  ultimately have "\<not> SN_on R' X" by (auto simp: SN_on_def)
  with SN' f0 show False unfolding SN_defs by auto
qed

lemma image_rtrancl_expand: "{y. (x,y) \<in> R\<^sup>*} = {x} \<union> (\<Union> y \<in> R `` {x}. {z. (y,z) \<in> R\<^sup>*})" (is "?L = ?R")
proof(intro equalityI subsetI)
  fix z
  assume "z \<in> ?L"
  then have "(x,z) \<in> R\<^sup>*" by auto
  then obtain n where xz: "(x,z) \<in> R^^n" by auto
  show "z \<in> ?R"
  proof (cases n)
    case 0 with xz show ?thesis by auto
  next
    case (Suc m)
      from xz[unfolded this] obtain y where xy: "(x,y) \<in> R" and yz: "(y,z) \<in> R^^m" by (elim relpow_Suc_E2)
      from yz relpow_imp_rtrancl have "z \<in> R\<^sup>* `` {y}" by auto
      with xy show ?thesis by auto
  qed
qed auto

lemma finite_ImageI:
  assumes R: "\<And>x. x \<in> X \<Longrightarrow> finite {y. (x,y) \<in> R}" and X: "finite X"
  shows "finite (R `` X)"
proof-
  have "R `` X = (\<Union>x \<in> X. {y. (x,y) \<in> R})" by auto
  also with R have "finite ..." unfolding finite_UN[OF X] by auto
  finally show ?thesis by auto
qed

lemma finite_rule_reducts:
  assumes "vars_term r \<subseteq> vars_term l"
  shows "finite {t. (s, t) \<in> rstep {(l, r)}}" (is "finite ?T")
proof -
  define h where "h = (\<lambda>p. (ctxt_of_pos_term p s)\<langle>r \<cdot> the (match (s |_ p) l)\<rangle>)" \<comment> \<open>computes reduct from position\<close>
  define P where "P = {p \<in> poss s. \<exists>\<sigma>. match (s |_ p) l = Some \<sigma>}" \<comment> \<open>positions of subterms matching \<open>l\<close>\<close>
  { fix C \<sigma> assume [simp]: "s = C\<langle>l \<cdot> \<sigma>\<rangle>"
    then obtain \<tau> where *: "match (s |_ hole_pos C) l = Some \<tau>"
      and [simp]: "r \<cdot> \<sigma> = r \<cdot> \<tau>"
      using assms and match_complete' by (force simp: term_subst_eq_conv)
    then have "h (hole_pos C) = C\<langle>r \<cdot> \<sigma>\<rangle>" by (auto simp: h_def)
    moreover have "h (hole_pos C) \<in> h ` P" using * by (auto simp: P_def)
    ultimately have "C\<langle>r \<cdot> \<sigma>\<rangle> \<in> h ` P" by simp }
  then have "?T = h ` P" by (auto intro!: rstepI simp: h_def P_def match_matches ctxt_supt_id)
  moreover have "finite P" by (rule finite_subset [of _ "poss s"]) (auto simp: P_def)
  ultimately show ?thesis by simp
qed

lemma finite_rstep_reducts:
  assumes "finite R"
    and "\<forall>(l, r) \<in> R. vars_term r \<subseteq> vars_term l"
  shows "finite {t. (s, t) \<in> rstep R}" (is "finite ?T")
proof -
  have "?T = \<Union>((\<lambda>(l, r). {t. (s, t) \<in> rstep {(l, r)}}) ` R)" by auto
  then show ?thesis
    using assms by (auto simp: finite_rule_reducts)
qed

lemma finite_qrstep_reducts:
  assumes "finite (applicable_rules Q R)"
    and "wwf_qtrs Q R"
  shows "finite {t. (s,t) \<in> qrstep False Q R}" (is "finite ?T")
proof-
  have "?T = {t. (s,t) \<in> qrstep False Q (applicable_rules Q R)}" by (auto simp: qrstep_applicable_rules)
  also have "finite ..."
  proof(rule finite_subset)
    show "... \<subseteq> {t. (s, t) \<in> rstep (applicable_rules Q R)}" by auto
    show "finite ..." by(rule finite_rstep_reducts, insert assms, auto simp: wwf_qtrs_def applicable_rules_def)
  qed
  finally show ?thesis .
qed

lemma size_ctxt_compose_gt: assumes "D \<noteq> \<box>" shows "size (C \<circ>\<^sub>c D) > size C"
proof-
  have "size (C \<circ>\<^sub>c D) \<ge> size C \<and> (D = \<box> \<or> ?thesis)" by(induct C, cases D, auto)
  with assms show ?thesis by auto
qed

lemma size_ctxt_apply_ge: "size (C\<langle>s\<rangle>) \<ge> size C + size s" (* not equal! *) by(induct C, auto)

lemma O_cong:
  assumes "R = R'"
  shows "S O R = S O R'" "R O T = R' O T" "S O R O T = S O R' O T"
  using assms by auto

lemma reflcl_O_rtrancl[simp]:
  "R\<^sup>= O R\<^sup>* = R\<^sup>*" "S O R\<^sup>= O R\<^sup>* = S O R\<^sup>*" "R\<^sup>= O R\<^sup>* O T = R\<^sup>* O T" "S O R\<^sup>= O R\<^sup>* O T = S O R\<^sup>* O T"
  apply (force)
  apply (intro O_cong, force)
  apply (fold O_assoc, intro O_cong, force)
  apply (unfold O_assoc, intro O_cong, fold O_assoc, intro O_cong, force)
  done

context fixes S R assumes push: "S O R \<subseteq> R O S\<^sup>*" begin
lemma O_relpow_push: "S O R ^^ n \<subseteq> R ^^ n O S\<^sup>*"
proof(intro subrelI, induct n)
  case (Suc n s t)
    then obtain u where "(s,u) \<in> R ^^ n O S\<^sup>*" "(u,t) \<in> R" unfolding relpow.simps by force
    then have "(s,t) \<in> R ^^ n O S\<^sup>* O R" by auto
    also have "... \<subseteq> R ^^ n O R O S\<^sup>*" using rtrancl_O_push[OF push] by auto
    also have "... \<subseteq> R ^^ Suc n O S\<^sup>*" by auto
    finally show ?case.
qed auto
end

interpretation subterm: order_pair "{\<rhd>}" "{\<unrhd>}"
  using subterm.refl_NS subterm.trans_NS subterm.trans_S subterm.le_less_trans subterm.less_le_trans
  by (unfold_locales, auto)

locale order_pair_inv_image = base: order_pair
begin
sublocale order_pair "inv_image S f" "inv_image NS f"
  apply (unfold_locales, unfold trans_O_iff refl_O_iff)
  apply (auto intro: base.refl_NS_point base.trans_S_point base.compat_S_NS_point base.compat_NS_S_point base.trans_NS_point)
  done
end

locale SN_order_pair_inv_image = base: SN_order_pair
begin
interpretation order_pair_inv_image..
sublocale SN_order_pair "inv_image S f" "inv_image NS f" by (unfold_locales, fact SN_inv_image[OF base.SN])
end


context linorder begin

definition "sorted_distinct_list X \<equiv> (SOME xs. set xs = X \<and> sorted xs \<and> distinct xs)"

lemma finite_set_as_list: "finite X \<Longrightarrow> \<exists>xs. set xs = X \<and> sorted xs \<and> distinct xs"
proof(induct rule:finite_induct)
  case empty show ?case by auto
next
  case (insert x X)
    then obtain xs where [simp]: "X = set xs" and "sorted xs" "distinct xs" by auto
    with insert(2) show ?case
      apply (intro exI[of _ "insort_insert x xs"] conjI)
      apply (simp add: set_insort_insert)
      using sorted_insort_insert apply force
      using distinct_insort_insert apply force
      done
qed

lemma sorted_distinct_list:
  assumes "finite X"
  shows "sorted (sorted_distinct_list X)" "distinct (sorted_distinct_list X)" "set (sorted_distinct_list X) = X"
  using someI_ex[OF finite_set_as_list[OF assms]] unfolding sorted_distinct_list_def by auto

end




subsection \<open>Quasi-termination\<close>

definition "quasi_terminating_on R X \<equiv> \<forall>x \<in> X. finite {y. (x,y) \<in> R\<^sup>*}"

lemma quasi_terminating_onI[intro]:
  assumes "\<And>x. x \<in> X \<Longrightarrow> finite {y. (x,y) \<in> R\<^sup>*}"
  shows "quasi_terminating_on R X"
  using assms by (auto simp: quasi_terminating_on_def)

lemma quasi_terminating_onD[dest]:
  assumes "quasi_terminating_on R X" and "x \<in> X"
  shows "finite {y. (x,y) \<in> R\<^sup>*}"
  using assms[unfolded quasi_terminating_on_def] by auto

abbreviation "quasi_terminating R \<equiv> quasi_terminating_on R UNIV"

text \<open>Quasi-terminating TRSs\<close>

locale quasi_terminating_trs =
  fixes S
  assumes QT: "quasi_terminating (rstep S)"
begin

fun accumulate_ctxts where
  "accumulate_ctxts C 0 = \<box>"
  | "accumulate_ctxts C (Suc i) = accumulate_ctxts C i \<circ>\<^sub>c C i"

lemma SN_supt_relto:
  "SN (relto {\<rhd>} (rstep S))"
proof(rule SN_onI)
  let ?R = "(rstep S)\<^sup>*"
  fix seq assume chain: "chain (?R O {\<rhd>} O ?R) seq"
  have "\<forall>i. \<exists>C. C \<noteq> \<box> \<and> (seq i, C\<langle>seq (Suc i)\<rangle>) \<in> ?R" (is "\<forall>i. ?goal i")
  proof
    fix i
    from chain have "(seq i, seq (Suc i)) \<in> (?R O {\<rhd>} O ?R)" by auto
    then obtain s t
    where s: "(seq i, s) \<in> ?R"
      and st: "(s,t) \<in> {\<rhd>}"
      and t: "(t, seq (Suc i)) \<in> ?R" by auto
    from st obtain C where "s = C\<langle>t\<rangle>" and C: "C\<noteq>\<box>" by auto
    moreover with s have "(seq i,C\<langle>t\<rangle>) \<in> ?R" by auto
    moreover with t rsteps_closed_ctxt have "(C\<langle>t\<rangle>,C\<langle>seq (Suc i)\<rangle>) \<in> ?R" by auto
    ultimately show "?goal i" by auto
  qed
  from choice[OF this] obtain C where *: "\<And>i. C i \<noteq> \<box> \<and> (seq i, (C i)\<langle>seq (Suc i)\<rangle>) \<in> ?R" by auto
  let ?s = "\<lambda>i. (accumulate_ctxts C i)\<langle>seq i\<rangle>"
  define m where "m = Max { size t | t. (?s 0, t) \<in> ?R }"
  moreover
    have "(?s 0, ?s i) \<in> ?R" for i
    proof (induct i)
      case (Suc i)
      moreover from * have "(?s i, ?s (Suc i)) \<in> ?R" by (auto intro: rsteps_closed_ctxt)
      ultimately show ?case by auto
    qed auto
    note this[of "Suc m"]
  moreover
    from QT have "finite { t. (?s 0, t) \<in> ?R }" by auto
    then have "finite { size t | t. (?s 0, t) \<in> ?R }" by auto
  ultimately have "size (?s (Suc m)) \<le> m" by(auto intro: Max_ge)
  moreover
    have "size (?s i) \<ge> i" for i
    proof-
      have "size (accumulate_ctxts C i) \<ge> i"
      proof (induct i)
        case (Suc i)
        from *[of i] have "size (accumulate_ctxts C (Suc i)) > size (accumulate_ctxts C i)"
          by(auto intro: size_ctxt_compose_gt)
        with Suc show ?case by auto
      qed auto
      with size_ctxt_apply_ge[of "accumulate_ctxts C i" "seq i"]
      show ?thesis by auto
    qed
    note this[of "Suc m"]
  ultimately show False by auto
qed

lemma SN_supt: "SN ((rstep S)\<^sup>* O {\<rhd>})"
  by (rule SN_subset[OF SN_supt_relto], auto)

lemma QT_relstep:
  assumes SN: "SN_on (relstep R S) X"
      and fin: "finite R"
      and wf: "\<forall> (l,r) \<in> R. vars_term r \<subseteq> vars_term l"
    shows "quasi_terminating_on (relstep R S) X"
proof
  fix x assume "x \<in> X"
  with SN
  show "finite {y. (x,y) \<in> (relstep R S)\<^sup>*}"
  proof(induct x rule: SN_on_induct)
    case (IH x)
      have "{y. (x,y) \<in> (relstep R S)\<^sup>*} = {x} \<union> (\<Union> y \<in> relstep R S `` {x}. {z. (y,z) \<in> (relstep R S)\<^sup>*})"
        by(rule image_rtrancl_expand)
      also have "finite ..."
      proof (intro finite_UnI conjI finite_UN_I)
        from IH show "\<And>y. y \<in> relstep R S `` {x} \<Longrightarrow> finite {z. (y,z) \<in> (relstep R S)\<^sup>*}" by (auto simp: Image_def)
        have "finite ((rstep S)\<^sup>* `` rstep R `` (rstep S)\<^sup>* `` {x})"
        proof (rule finite_ImageI)
          show "finite (rstep R `` (rstep S)\<^sup>* `` {x})"
          proof (rule finite_ImageI)
            from QT show "finite ((rstep S)\<^sup>* `` {x})" by (auto simp: Image_def)
          qed (insert finite_rstep_reducts[OF fin wf], auto)
        qed (insert QT, auto simp: Image_def)
        then show "finite (relstep R S `` {x})" by (auto simp: relcomp_Image)
      qed auto
      finally show ?case.
  qed
qed

end

subsection \<open>Connectability\<close>

text \<open>The following notion characterizes what one estimates by TCAP-unifiability etc.\<close>

definition "connectable R s t \<equiv> \<exists>\<sigma> \<tau>. (s\<cdot>\<sigma>, t\<cdot>\<tau>) \<in> (nrrstep R)\<^sup>*"

lemma connectableI[intro]: fixes \<sigma> \<tau>
  shows "(s\<cdot>\<sigma>, t\<cdot>\<tau>) \<in> (nrrstep R)\<^sup>* \<Longrightarrow> connectable R s t" unfolding connectable_def by auto

lemma connectableE[elim]:
  assumes "connectable R s t" obtains \<sigma> \<tau> where "(s\<cdot>\<sigma>, t\<cdot>\<tau>) \<in> (nrrstep R)\<^sup>*"
  using assms[unfolded connectable_def] by auto

lemma connectable_stable:
  assumes con: "connectable R (s\<cdot>\<sigma>) t" shows "connectable R s t"
proof-
  from con obtain \<sigma>' \<tau> where "(s \<cdot> (\<sigma> \<circ>\<^sub>s \<sigma>'), t\<cdot>\<tau>) \<in> (nrrstep R)\<^sup>*" by auto
  from connectableI[OF this] show ?thesis by auto
qed

lemma connectable_subst[simp]:
  fixes R :: "('f,'v) trs" and \<sigma> :: "('f,'v) subst" shows "connectable R (s\<cdot>\<sigma>) s"
proof
  show "(s\<cdot>\<sigma>\<cdot>Var,s\<cdot>\<sigma>) \<in> (nrrstep R)\<^sup>*" by auto
qed

text\<open>Checks if a term is @{term connectable} to a usable rule.\<close>

definition i_trans_check where
  "i_trans_check R ur s \<equiv> (\<forall> (l,r) \<in> R. connectable R s l \<longrightarrow> (l,r) \<in> ur)"

lemma i_trans_checkI[intro]:
  assumes "(\<And>l r. (l,r) \<in> R \<Longrightarrow> connectable R s l \<Longrightarrow> (l,r) \<in> ur)"
  shows "i_trans_check R ur s"
  unfolding i_trans_check_def using assms by auto

lemma i_trans_checkD[dest]:
  assumes "i_trans_check R ur s"
  shows "(l,r) \<in> R \<Longrightarrow> connectable R s l \<Longrightarrow> (l,r) \<in> ur"
  using assms unfolding i_trans_check_def by auto

lemma i_trans_check_stable:
  assumes "i_trans_check R ur s" shows "i_trans_check R ur (s \<cdot> \<sigma>)"
proof
  fix l r
  assume lr: "(l,r) \<in> R" and sl: "connectable R (s \<cdot> \<sigma>) l"
  from connectable_stable[OF sl] have "connectable R s l" by auto
  with assms lr show "(l,r) \<in> ur" by auto
qed


subsection \<open>Main\<close>

definition qrel where "qrel Q R S \<equiv> relto (qrstep False Q R) (rstep S)"

lemma mem_qrelI[intro!]: "p \<in> relto (qrstep False Q R) (rstep S) \<Longrightarrow> p \<in> qrel Q R S" unfolding qrel_def by auto

lemma qrstep_subset_qrel: "qrstep False Q R \<subseteq> qrel Q R S" unfolding qrel_def by auto

lemma qrel_empty_is_qrstep: "qrel Q R {} = qrstep False Q R"
  unfolding qrel_def by auto

lemma ctxt_closed_qrel: "ctxt.closed (qrel Q R E)"
  unfolding qrel_def
  by (rule ctxt.closed_relto[OF ctxt_closed_qrstep ctxt_closed_rstep]) 

fun ur_closed_term_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> 'f af \<Rightarrow> ('f,'v)term \<Rightarrow> bool"
where "ur_closed_term_af _ _ _ (Var x) = True"
   |  "ur_closed_term_af R ur \<pi> (Fun f ts) =
   ( (\<forall> i < length ts. i \<in> \<pi> (f, (length ts)) \<longrightarrow> ur_closed_term_af R ur \<pi> (ts ! i)) \<and> 
     i_trans_check R ur (Fun f ts)
)"

abbreviation ur_closed_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> 'f af \<Rightarrow> bool"
where "ur_closed_af R ur \<pi> \<equiv> \<forall> (l,r) \<in> ur. ur_closed_term_af R ur \<pi> r"

abbreviation ur_P_closed_af :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> 'f af \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" 
  where "ur_P_closed_af R ur \<pi> P  \<equiv> \<forall> st \<in> P. ur_closed_term_af R ur \<pi> (snd st)"  

lemma i_trans_check_nrrstep:
  assumes ur_closed: "ur_closed_af R ur \<pi>"
  and s: "i_trans_check R ur s"
  and st: "(s,t) \<in> nrrstep R"
  shows "i_trans_check R ur t"
proof
  from nrrstep_imp_Fun[OF st] have sFun: "is_Fun s" by auto
  fix l r assume lr: "(l,r) \<in> R" and connect: "connectable R t l"
  from connect obtain \<sigma> \<tau> where "(t\<cdot>\<sigma>,l\<cdot>\<tau>) \<in> (nrrstep R)\<^sup>*" by (elim connectableE)
  moreover from nrrstep_subst[OF st] have "(s\<cdot>\<sigma>,t\<cdot>\<sigma>) \<in> nrrstep R" by auto
  ultimately have "connectable R s l" by (intro connectableI[of _ \<sigma> _ \<tau>], auto)
  with i_trans_checkD[OF s lr] show "(l,r)\<in> ur" by auto
qed

lemma SN_on_stable:
  assumes stable: "\<And>x y. x \<in> R\<^sup>* `` X \<Longrightarrow> (x,y) \<in> R \<Longrightarrow> (f x, f y) \<in> R" and SN: "SN_on R (f ` X)" shows "SN_on R X"
proof(intro SN_onI)
  fix seq assume 0: "seq 0 \<in> X" and chain: "chain R seq"
  show False
  proof(rule SN_onE[OF SN], elim notE, intro exI conjI)
    from 0 show "(f \<circ> seq) 0 \<in> f ` X" by auto
    show "chain R (f \<circ> seq)"
    proof
      fix i
      show "((f \<circ> seq) i, (f \<circ> seq) (Suc i)) \<in> R" unfolding comp_def
      proof(rule stable)
        from 0 chain have "seq i \<in> (R ^^ i) `` X" by (induct i, auto)
        also have "... \<subseteq> R\<^sup>* `` X" by (rule Image_mono, auto simp: relpow_imp_rtrancl)
        finally show "seq i \<in> ..." using chain by auto
      qed (insert chain, auto)
    qed
  qed
qed

locale itrans = wf_weak_mono_algebra less_eq less I + base: quasi_order_Sup Sup less_eq less
  for less_eq less and Sup :: "'a set \<Rightarrow> 'a"
  and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" +
  fixes Q :: "('f,'v)terms"
  and R :: "('f,'v)trs"
  and S :: "('f,'v)trs"
  and ur :: "('f,'v)trs"
  and cn :: "('f \<times> nat)"
  assumes SN_suptrel: "SN (relto {\<rhd>} (rstep S))"
  and wf: "wwf_qtrs Q R"
  and fin: "finite (applicable_rules Q R)"
begin

interpretation base: ord_syntax.

definition qr_successors :: "('f,'v)term \<Rightarrow> ('f,'v)term set" where
  "qr_successors s \<equiv> {t. (s,t) \<in> qrstep False Q R}"

context fixes \<alpha> :: "('v \<Rightarrow> 'a)"
begin
function i_trans :: "('f,'v) term \<Rightarrow> 'a"
where "i_trans s = (
       if \<not> SN_on (qrel Q R S) {s} then undefined
       else if i_trans_check (R \<union> S) ur s then
         (case s of Var x \<Rightarrow> \<alpha> x | Fun f ss \<Rightarrow> I f (map i_trans ss))
       else Sup
         ((\<lambda>s. case s of Var x \<Rightarrow> \<alpha> x | Fun f ss \<Rightarrow> I f (map i_trans ss)) ` (rstep S)\<^sup>* `` {s} \<union>
         i_trans ` qrstep False Q R `` (rstep S)\<^sup>* `` {s}))"
by (pat_completeness, auto)

abbreviation "SNT \<equiv> {s. SN_on (qrel Q R S) {s}}"
definition "po1s \<equiv> (relto (qrstep False Q R \<union> {\<rhd>}) (rstep S))\<^sup>+"
definition "po1w \<equiv> (qrstep False Q R \<union> {\<rhd>} \<union> rstep S)\<^sup>*"

termination i_trans
proof-
  have SN: "SN_on (qrel Q R S) SNT" by blast
  from SN_on_Image[OF SN] have 1: "SN_on (qrel Q R S) (qrel Q R S `` SNT)" by auto
  note cl_qrel = SN_on_subset_SN_terms[OF this]
  have "SN_on (qrel Q R S) (qrstep False Q R `` SNT)"
    by (rule SN_on_subset2[OF _ 1], rule Image_subsetI, auto simp: qrel_def)
  note cl_qr = SN_on_subset_SN_terms[OF this]
  from SN have SN_Un: "SN_on ({\<rhd>} \<union> qrel Q R S) SNT"
    by (intro SN_on_r_imp_SN_on_supt_union_r, auto simp: qrel_def)
  then have *: "SN_on ({\<rhd>} \<union> qrel Q R S) (({\<rhd>} \<union> qrel Q R S) `` SNT)" by (fact SN_on_Image)
  have "SN_on (qrel Q R S) ({\<rhd>} `` SNT)" by (rule SN_on_subset1, rule SN_on_subset2[OF _ *], auto)
  note cl_supt = SN_on_subset_SN_terms[OF this]

  from _ SN_on_relto_Image[OF SN[unfolded qrel_def], folded qrel_def]
  have "SN_on (qrel Q R S) (rstep S `` SNT)" apply (rule SN_on_subset2) by (auto)
  note cl_S = SN_on_subset_SN_terms[OF this]
  note cl_SS = Image_closed_trancl[OF this]

  from cl_qrel cl_supt cl_S have cl: "({\<rhd>} \<union> qrel Q R S \<union> rstep S) `` SNT \<subseteq> SNT" by auto

  { fix x y
    assume x: "SN_on (qrel Q R S) {x}" and xy: "(x,y) \<in> po1s"
    have "po1s \<subseteq> ({\<rhd>} \<union> qrel Q R S \<union> rstep S)\<^sup>*" by (unfold qrel_def po1s_def, regexp)
    with x xy Image_closed_trancl[OF cl] have "y \<in> SNT" by blast
    with x xy have "(x,y) \<in> po1s \<restriction> SNT" by auto
  }
  note mem_po2sI[intro!] = this

  interpret ord: order_pair_restrict "po1s" "po1w" by (unfold po1s_def po1w_def, unfold_locales)

  interpret ord: SN_order_pair "po1s \<restriction> SNT" "(po1w \<restriction> SNT)\<^sup>="
  proof
    show SN2: "SN (po1s \<restriction> SNT)"
    proof(unfold po1s_def, rule SN_on_imp_SN_restrict, unfold SN_on_trancl_SN_on_conv, subst SN_on_relto_Un; (intro conjI)?)
      from SN show "SN_on (relto (qrstep False Q R) ({\<rhd>} \<union> rstep S)) SNT"
        by(subst(1 2) Un_commute, intro SN_on_relto_Un_supt, auto simp: qrel_def)
      have "relto (qrstep False Q R \<union> {\<rhd>}) (rstep S) `` SNT \<subseteq> ({\<rhd>} \<union> qrel Q R S \<union> rstep S)\<^sup>* `` SNT"
        by (rule Image_subsetI, unfold qrel_def, regexp)
      also have "... = SNT" by (fact Image_closed_trancl[OF cl])
      finally show "relto (qrstep False Q R \<union> {\<rhd>}) (rstep S) `` SNT \<subseteq> SNT".
      from SN_on_subset2[OF _ SN_suptrel, of SNT]
      show "SN_on (relto {\<rhd>} (rstep S)) SNT" by auto
    qed
  qed

  interpret ord2: SN_order_pair_inv_image "(po1s \<restriction> SNT)" "((po1w \<restriction> SNT)\<^sup>=)" by (unfold_locales)

  let ?po = "(po1s \<restriction> SNT)"

  have SN3: "SN ?po" by (rule ord.SN)
  then have wf: "wf (?po\<inverse>)" (is "wf ?R") by (simp add: SN_iff_wf)
  have [dest]: "\<And>f ss s. SN_on (qrel Q R S) {Fun f ss} \<Longrightarrow> s \<in> set ss \<Longrightarrow> SN_on (qrel Q R S) {s}"
    by (rule SN_imp_SN_arg_gen, auto simp: qrel_def)
  have "{\<rhd>} \<subseteq> po1s" by (unfold po1s_def, regexp)
  then have [dest]: "\<And>f ss s. s \<in> set ss \<Longrightarrow> (Fun f ss, s) \<in> po1s"
    by (unfold po1s_def, auto)
  have [dest]: "\<And>s f ts t. (s, Fun f ts) \<in> (rstep S)\<^sup>* \<Longrightarrow> t \<in> set ts \<Longrightarrow> (s, t) \<in> po1s"
    by (unfold po1s_def, blast)
  have [dest]: "\<And>s t. SN_on (qrel Q R S) {s} \<Longrightarrow> (s,t) \<in> (rstep S)\<^sup>* \<Longrightarrow> SN_on (qrel Q R S) {t}"
    using cl_SS by auto
  have [dest]: "\<And>s t. SN_on (qrel Q R S) {s} \<Longrightarrow> (s,t) \<in> qrstep False Q R \<Longrightarrow> SN_on (qrel Q R S) {t}"
    using cl_qr by auto 
  have "qrstep False Q R \<subseteq> qrel Q R S" unfolding qrel_def by auto
  show ?thesis apply (rule "termination"[OF wf]) by (auto simp: po1s_def)
qed

declare "i_trans.simps"[simp del]

text \<open>Following definitions are just for the readability of proofs\<close>

private abbreviation mapper
where "mapper \<equiv> \<lambda>s. case s of Var x \<Rightarrow> \<alpha> x | Fun f ss \<Rightarrow> I f (map i_trans ss)"

private definition Extend
where [simp]: "Extend s \<equiv> mapper ` (rstep S)\<^sup>* `` {s} \<union> i_trans ` qrstep False Q R `` (rstep S)\<^sup>* `` {s}"

private lemma Extend_mono_S: assumes st: "(s,t) \<in> (rstep S)\<^sup>*" shows "Extend s \<supseteq> Extend t"
proof-
  have "(rstep S)\<^sup>* `` {t} \<subseteq> (rstep S)\<^sup>* `` {s}" using st by auto
  then show "Extend t \<subseteq> Extend s" by auto
qed

context
  assumes LUB_exists: "\<And>s. SN_on (qrel Q R S) {s} \<Longrightarrow> ord.Leasts less_eq (ord.Upper_Bounds less_eq (Extend s)) \<noteq> {}"
begin

lemma bounded:
  assumes SN: "SN_on (qrel Q R S) {s}" shows "a \<in> Extend s \<Longrightarrow> a \<sqsubseteq> Sup (Extend s)"
  using LUB_exists SN base.Sup_upper by blast

lemma Sup_mono:
  assumes SN: "SN_on (qrel Q R S) {s}" and st: "(s,t) \<in> (rstep S)\<^sup>*"
  shows "Sup (Extend s) \<sqsupseteq> Sup (Extend t)"
proof(rule base.Sup_mono[OF LUB_exists LUB_exists[OF SN] Extend_mono_S[OF st]])
  from st show "SN_on (qrel Q R S) {t}" unfolding qrel_def
  apply (intro steps_preserve_SN_on_relto[OF _ SN[unfolded qrel_def]]) by regexp
qed

lemma subst_inner:
  assumes SN: "SN_on (qrel Q R S) {s \<cdot> \<sigma>}"
  shows "i_trans (s\<cdot>\<sigma>) \<sqsupseteq> \<lbrakk>s\<rbrakk>(i_trans \<circ> \<sigma>)" (is "?goal1 s")
proof (insert SN, induct s)
  case (Var x) show ?case by (auto simp: supteq_var_imp_eq)
next
  case IH: (Fun f ss)
  define s where "s = Fun f ss"
  with IH have SN: "SN_on (qrel Q R S) {s\<cdot>\<sigma>}" by auto
  then have sns: "\<And> s. s \<in> set ss \<Longrightarrow> SN_on (qrel Q R S) {s \<cdot> \<sigma>}"
    by (simp add: s_def SN_imp_SN_arg_gen[OF ctxt_closed_qrel])
  define l where "l = (\<lambda>s. i_trans (s \<cdot> \<sigma>))"
  define r where "r = (\<lambda>s. \<lbrakk>s\<rbrakk>(i_trans \<circ> \<sigma>))"
  { fix s assume "s \<in> set ss"
    from IH.hyps[OF this sns[OF this]]
    have "l s \<sqsupseteq> r s" by (unfold l_def r_def, fast)
  }
  note sub = this
  have nearlyDone: "I f (map l ss) \<sqsupseteq> r s"
    by (unfold s_def r_def eval.simps, fold r_def, auto intro!: weak_mono_all_le sub)
  show ?case
  proof (cases "is_Var (s\<cdot>\<sigma>) \<or> i_trans_check (R\<union>S) ur (s\<cdot>\<sigma>)")
    case False
    with IH.prems SN have id: "l s = Sup (Extend (s\<cdot>\<sigma>))" by (auto simp: l_def s_def i_trans.simps)
    let ?f = "term.case_term \<alpha> (\<lambda>g ts. I g (map i_trans ts))"
    have "Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ss) \<in> (rstep S)\<^sup>* `` {Fun f (map (\<lambda>t. t \<cdot> \<sigma>) ss)}" by auto
    from imageI[OF this, of ?f]
    have "I f (map l ss) \<in> Extend (s\<cdot>\<sigma>)" by (auto simp: l_def o_def s_def)
    from bounded[OF SN] this[folded id]
    have "l s \<sqsupseteq> I f (map l ss)" by (auto simp add: id)
    with nearlyDone have "l s \<sqsupseteq> r s" by (rule order_trans)
    from this[unfolded r_def l_def s_def]
    show ?thesis by force
  next
    case check: True
      with SN nearlyDone have *: "?goal1 s" by (simp add: o_def s_def l_def r_def i_trans.simps)
      with check show ?thesis by (auto simp: s_def)
  qed
qed

lemma subst_outer:
  assumes af: "af_compatiblep \<pi>"
      and ur: "ur_closed_term_af (R\<union>S) ur \<pi> t"
      and SN: "SN_on (qrel Q R S) {t \<cdot> \<sigma>}"
  shows "\<lbrakk>t\<rbrakk>(i_trans \<circ> \<sigma>) \<sqsupseteq> i_trans (t \<cdot> \<sigma>)"
proof (insert ur SN, induct t)
  case (Fun f ts)
  then have sClosed: "\<And> i. i < length ts \<and> i \<in> \<pi> (f, (length ts)) \<Longrightarrow> ur_closed_term_af (R\<union>S) ur \<pi> (ts ! i)" by auto
  from \<open>SN_on (qrel Q R S) {Fun f ts \<cdot> \<sigma>}\<close> have sns: "\<And> s. s \<in> set ts \<Longrightarrow> SN_on (qrel Q R S) {s \<cdot> \<sigma>}"
    by (simp add: SN_imp_SN_arg_gen[OF ctxt_closed_qrel])
  let ?tis = "\<lambda> t. \<lbrakk>t\<rbrakk>(i_trans \<circ> \<sigma>)"
  let ?its = "\<lambda> t. i_trans (t \<cdot> \<sigma>)"
  have "i_trans (Fun f ts \<cdot> \<sigma>) = i_trans (Fun f (map (\<lambda> t. t \<cdot> \<sigma>) ts))" (is "?l = i_trans ?r") by auto
  also have "\<dots> = I f (map (i_trans \<circ> (\<lambda>t. t \<cdot> \<sigma>)) ts)"
  proof -
    from Fun(2)
    have inst: "\<forall> (l,r) \<in> R\<union>S. connectable (R\<union>S) (Fun f ts) l \<longrightarrow> (l,r) \<in> ur" by auto
    have "i_trans_check (R\<union>S) ur (Fun f ts \<cdot> \<sigma>)" (is ?check)
    proof
      fix l r assume lr: "(l,r) \<in> R\<union>S" and con: "connectable (R\<union>S) (Fun f ts \<cdot> \<sigma>) l"
      from connectable_stable[OF con] have "connectable (R\<union>S) (Fun f ts) l" by auto
      with inst lr show "(l,r) \<in> ur" by auto
    qed
    then have "i_trans_check (R\<union>S) ur ?r" by auto
    with Fun(3) show ?thesis using i_trans.simps by auto
  qed
  also have eq1: "\<dots> = I f (map ?its ts)" (is "_ = ?r") by (simp add: o_def)
  also have "... \<sqsubseteq> I f (map ?tis ts)"
  proof (intro af_mono[OF af], unfold length_map)
    fix i
    assume i: "i \<in> \<pi> (f, length ts)" "i < length ts"
    with sns have "ts ! i \<in> set ts" and "SN_on (qrel Q R S) {ts ! i \<cdot> \<sigma>}" by auto
    with sClosed i show "map ?tis ts ! i \<sqsupseteq> map ?its ts ! i"
      by(subst(1 2) nth_map, simp, intro Fun, auto)
  qed simp
  also have "... = \<lbrakk>Fun f ts\<rbrakk> (i_trans \<circ> \<sigma>)" by auto
  finally show ?case.
qed auto

lemma SN_on_qrel_preservation: assumes st: "(s,t) \<in> qrstep False Q R \<union> rstep S"
  and SN: "SN_on (qrel Q R S) {s}"
  shows "SN_on (qrel Q R S) {t}"
  by (rule step_preserves_SN_on_relto[OF _ SN[unfolded qrel_def], of t, folded qrel_def],
  insert st, auto)

lemma SN_on_qrel_preservation_steps: assumes SN: "SN_on (qrel Q R S) {t}" 
  shows "(t,s) \<in> (qrstep False Q R \<union> rstep S)^* \<Longrightarrow> SN_on (qrel Q R S) {s}"
proof (induct rule: rtrancl_induct)
  case (step s r)
  from SN_on_qrel_preservation[OF step(2-3)]
  show ?case by auto
qed (rule SN)

lemma step_R1:
  assumes SN: "SN_on (qrel Q R S) {s}"
      and st: "(s,t) \<in> qrstep False Q R"
      and chk: "\<not> i_trans_check (R\<union>S) ur s"
  shows "i_trans s \<sqsupseteq> i_trans t"
proof-
  from chk SN
  have id: "i_trans s = Sup (Extend s)" by (auto simp: i_trans.simps)
  from st have "i_trans t \<in> Extend s" by auto
  from bounded[OF SN this, folded id] show ?thesis.
qed

lemma step_R:
  assumes af: "af_compatiblep \<pi>"
      and ur: "ur_closed_af (R\<union>S) ur \<pi>"
      and ord: "\<And>l r. (l,r) \<in> ur \<Longrightarrow> l \<sqsupseteq>\<^sub>t r"
      and SN: "SN_on (qrel Q R S) {s}"
      and st: "(s,t) \<in> qrstep False Q R"
      and chk: "i_trans_check (R\<union>S) ur s"
  shows "i_trans s \<sqsupseteq> i_trans t"
proof(insert st SN chk, induct rule: qrstep_small_induct)
  case (1 l r \<sigma>)
  note SNl = \<open>SN_on (qrel Q R S) {l \<cdot> \<sigma>}\<close>
  from 1 have lr: "(l,r) \<in> ur" by auto
  have SNr: "SN_on (qrel Q R S) {r \<cdot> \<sigma>}"
  proof (unfold qrel_def, rule step_preserves_SN_on_relto, fold qrel_def)
    from 1 show "(l\<cdot>\<sigma>,r\<cdot>\<sigma>) \<in> qrstep False Q R \<union> rstep S" by auto
  qed fact
  with lr ur have "i_trans (r\<cdot>\<sigma>) \<sqsubseteq> \<lbrakk>r\<rbrakk>(i_trans \<circ> \<sigma>)" by (intro subst_outer[OF af], auto)
  also with ord[OF lr] have "... \<sqsubseteq> \<lbrakk>l\<rbrakk>(i_trans \<circ> \<sigma>)"  by auto
  also note subst_inner[OF SNl]
  finally show ?case .
next
  case IH: (2 s t f pre post)
  let ?C = "\<lambda>s. Fun f (pre @ s # post)"
  note st = \<open>(s, t) \<in> qrstep False Q R\<close>
  from st have st': "(?C s, ?C t) \<in> qrstep False Q R" by (auto intro: ctxt_closed_one simp: qrel_def)
  note SNs' = \<open>SN_on (qrel Q R S) {?C s}\<close>
  have SNs: "SN_on (qrel Q R S) {s}" by (rule subterm_preserves_SN_gen[OF ctxt_closed_qrel SNs'], auto)
  have SNt': "SN_on (qrel Q R S) {?C t}"
    by (rule step_preserves_SN_on[OF _ SNs'], insert st', auto simp: qrel_def)
  show ?case
  proof(cases "i_trans_check (R\<union>S) ur (?C s)")
    case check: True
    have check_t: "i_trans_check (R\<union>S) ur (?C t)"
    proof(rule i_trans_check_nrrstep[OF ur check])
      from st show "(?C s, ?C t) \<in> nrrstep (R\<union>S)" by (auto intro: Fun_nrrstepI)
    qed
    have st2: "i_trans s \<sqsupseteq> i_trans t"
    proof(cases "i_trans_check (R\<union>S) ur s")
      case True from IH(2)[OF SNs True] show ?thesis.
    next
      case False from step_R1[OF SNs st False] show ?thesis.
    qed
    from check check_t SNs' SNt'
    show ?thesis using i_trans.simps using st2 by (auto intro: append_Cons_le_append_Cons)
  next
    case check: False
    from st have "(?C s, ?C t) \<in> qrstep False Q R" by (auto intro: ctxt_closed_one)
    then show ?thesis by (rule step_R1[OF SNs' _ check])
  qed
qed

lemma step_S1:
  assumes SNs: "SN_on (qrel Q R S) {s}"
      and st: "(s,t) \<in> (rstep S)"
      and ur: "\<not> i_trans_check (R\<union>S) ur s"
  shows "i_trans s \<sqsupseteq> i_trans t"
proof-
  from SN_on_relto_Image_S[OF SNs[unfolded qrel_def], folded qrel_def] st
  have SNt: "SN_on (qrel Q R S) {t}" by blast
  from ur SNs
  have 1: "i_trans s = Sup (Extend s)" by (auto simp: i_trans.simps)
  show ?thesis
  proof(cases "i_trans_check (R\<union>S) ur t")
    case True
    with st SNt have "i_trans t = mapper t" by (auto simp: i_trans.simps)
    also from st have "... \<in> mapper ` (rstep S) `` {s}" by auto
    also have "... \<subseteq> Extend s" by auto
    finally have "i_trans t \<in> Extend s".
    from bounded[OF SNs this, folded 1]
    show ?thesis.
  next
   case False
    with SNt have 2: "i_trans t = Sup (Extend t)" by (auto simp: i_trans.simps)
    from Sup_mono[OF SNs] st show ?thesis by (unfold 1 2, auto)
  qed
qed

lemma step_S:
  assumes af: "af_compatiblep \<pi>"
      and ur: "ur_closed_af (R\<union>S) ur \<pi>"
      and ord: "\<And>l r. (l,r) \<in> ur \<Longrightarrow> l \<sqsupseteq>\<^sub>t r"
      and SN: "SN_on (qrel Q R S) {s}"
      and st: "(s,t) \<in> rstep S"
      and chk: "i_trans_check (R\<union>S) ur s"
  shows "i_trans s \<sqsupseteq> i_trans t"
proof(insert st SN chk, induct rule: rstep_small_induct)
  case (1 l r \<sigma>)
  note SNl = \<open>SN_on (qrel Q R S) {l \<cdot> \<sigma>}\<close>
  from 1 have lr: "(l,r) \<in> ur" by auto
  have SNr: "SN_on (qrel Q R S) {r \<cdot> \<sigma>}"
  proof (unfold qrel_def, rule step_preserves_SN_on_relto, fold qrel_def)
    from 1 show "(l\<cdot>\<sigma>,r\<cdot>\<sigma>) \<in> qrstep False Q R \<union> rstep S" by auto
  qed fact
  with lr ur have "i_trans (r\<cdot>\<sigma>) \<sqsubseteq> \<lbrakk>r\<rbrakk>(i_trans \<circ> \<sigma>)" by (intro subst_outer[OF af], auto)
  also with ord[OF lr] have "... \<sqsubseteq> \<lbrakk>l\<rbrakk>(i_trans \<circ> \<sigma>)"  by auto
  also note subst_inner[OF SNl]
  finally show ?case .
next
  case IH: (2 s t f pre post)
  let ?C = "\<lambda>s. Fun f (pre @ s # post)"
  note st = \<open>(s, t) \<in> rstep S\<close>
  from st have st': "(?C s, ?C t) \<in> rstep S" by (auto intro: ctxt_closed_one)
  note SNs' = \<open>SN_on (qrel Q R S) {?C s}\<close>
  have SNs: "SN_on (qrel Q R S) {s}" by (rule subterm_preserves_SN_gen[OF ctxt_closed_qrel SNs'], auto)
  have SNt': "SN_on (qrel Q R S) {?C t}"
    by (rule SN_on_qrel_preservation[OF _ SNs'], insert st', auto simp: qrel_def)
  show ?case
  proof(cases "i_trans_check (R\<union>S) ur (?C s)")
    case check: True
    have check_t: "i_trans_check (R\<union>S) ur (?C t)"
    proof(rule i_trans_check_nrrstep[OF ur check])
      from st show "(?C s, ?C t) \<in> nrrstep (R\<union>S)" by (auto intro: Fun_nrrstepI)
    qed
    have st2: "i_trans s \<sqsupseteq> i_trans t"
    proof(cases "i_trans_check (R\<union>S) ur s")
      case True from IH(2)[OF SNs True] show ?thesis.
    next
      case False from step_S1[OF SNs st False] show ?thesis.
    qed
    from check check_t SNs' SNt'
    show ?thesis using i_trans.simps using st2 by (auto intro: append_Cons_le_append_Cons)
  next
    case check: False
    from st have "(?C s, ?C t) \<in> rstep S" by (auto intro: ctxt_closed_one)
    then show ?thesis by (rule step_S1[OF SNs' _ check])
  qed
qed

end

lemma ur_sound:
  assumes "\<And>l r. (l,r) \<in> ur \<Longrightarrow> l \<sqsupseteq>\<^sub>t r"
      and af: "af_compatiblep \<pi>"
      and ur_closed: "ur_closed_af (R\<union>S) ur \<pi>"
      and fin: "finite_rel_dpp (P - Ps,  Pw - Ps, R, S, E)"
  shows "finite_rel_dpp (P, Pw, R, S, E)"
proof(rule finite_rel_dpp_split_top[OF fin])
  fix s t \<sigma>
  assume "min_relchain (P, Pw, R, S, E) s t \<sigma>"
  note step_R[OF _ af ur_closed]
  oops

end
end

lemma (in ce_af_redtriple) redpair_ur_sound:
  assumes rules: "ur \<subseteq> NS \<union> S"
      and nonStrict: "P \<union> Pw \<subseteq> NS \<union> S"
      and strictP: "Ps \<subseteq> S"
      and ur_closed: "ur_closed_af R ur \<pi>"
      and ur_P_closed: "ur_P_closed_af R ur \<pi> (P \<union> Pw)"
      and m: m
      and fin: "finite_rel_dpp (P - Ps, Pw - Ps, Q, R, Rw)"
  shows "finite_rel_dpp (P,Pw,Q,R,Rw)"
proof-
  oops



end
