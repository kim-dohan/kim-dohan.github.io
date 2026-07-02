(*
Author:  Akihisa Yamada (2017)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Max_Monus_Impl
  imports
    Max_Monus
    Ordered_Algebra_Impl
    IA_Checker
    Term_Order_Impl
begin

locale max_monus_encoding_impl =
  verbose.encoder: encoding_impl
  where default_fun = "\<lambda>x. max_monus.MaxF" +
  verbose: pre_encoded_ord_algebra
  where less_eq = "(\<le>)" and less = "(<)" and I = max_monus.I and E = verbose.encoder.E
begin

text \<open>
  We simplify the encoding terms. It is shown to preserve semantics, but the fact doesn't matter
  for soundness.
\<close>
definition "simplified_alist = map (map_prod id max_monus.simplify) alist"

sublocale encoder: encoding_impl
  where alist = "simplified_alist"
    and default_fun = "\<lambda>_. max_monus.MaxF" .

sublocale pre_encoded_ord_algebra
  where less_eq = "(\<le>)"
    and less = "(<)"
    and I = max_monus.I
    and E = encoder.E .

definition "check_less_term solver s t = IA.check_valid_formula solver (max_monus.less_via_IA (encode s) (encode t))"

definition "check_less_eq_term solver s t = IA.check_valid_formula solver (max_monus.le_via_IA (encode s) (encode t))"

definition "check_simple_arg_pos solver f n i = do {
  check (i < n) (showsl (STR ''bad argument number''));
  IA.check_valid_formula solver (max_monus.le_via_IA (Var i) (encoder.E f n))
}"

definition "check_ss_fun_arg solver f n i = do {
  check (i < n) (showsl (STR ''bad argument number''));
  IA.check_valid_formula solver (max_monus.less_via_IA (Var i)  (encoder.E f n))
}"

definition "create_max_monus_rel_impl solver = \<lparr>
  rel_impl.valid = encoder.check_encoding,
  standard = succeed,
  desc = showsl_lit (STR ''max-monus interpretations:'') \<circ>
    showsl_nl \<circ> encoder.showsl_encoding,
  s = (\<lambda>(s, t). check_less_term solver t s),
  ns = (\<lambda>(s, t). check_less_eq_term solver t s),
  nst = (\<lambda>(s, t). check_less_eq_term solver t s),
  af = (\<lambda>(f, n). {0..<n} - set (constant_positions f n)),
  top_af = (\<lambda>(f, n). {0..<n} - set (constant_positions f n)),
  SN = succeed,
  subst_s = succeed,
  ce_compat = succeed,
  co_rewr = succeed,
  top_mono = succeed,
  top_refl = succeed,
  mono_af = empty_af,
  mono = (\<lambda> sig. error (showsl_lit (STR ''monotonicity of max-monus is not yet supported''))),
  not_wst = Some (map fst simplified_alist),
  not_sst = None, \<comment> \<open>TODO: add something here to support WPO with rule (2d);
     such a change at least requires a different default-interpretation 
     which currently is [f](x1,...,xn) = max(x1,..,xn) which is not strictly
     simplifying. However, the required interpretation
     [f](x1,...,xn) = 1 + max(x1,...,xn) is currently not expressible in
     the @{locale encoding_impl} as there the structure of the 
     default interpretation is restricted to one function, expressed as term, 
     i.e., @{const max_monus.MaxF} in our case.\<close>
  cpx = no_complexity_check
\<rparr>"


lemma af_compatible:
  "af_compatible (\<lambda>(f, n). {0..<n} - set (constant_positions f n)) (rel_of (\<ge>\<^sub>\<A>))"
 (is "af_compatible ?pi _")
proof -
  {
    fix f and s t :: "('a, 'b) term" and bef aft :: "('a, 'b) term list" 
    let ?ss = "bef @ s # aft" 
    let ?n = "Suc (length bef + length aft)" 
    assume "length bef \<notin> ?pi (f, ?n)" 
    then have "length bef \<in> set (constant_positions f ?n)" by auto
    from constant_atD [OF constant_positions [OF this], of "map (\<lambda>s. \<lbrakk>s\<rbrakk>\<alpha>) ?ss" "\<lbrakk>t\<rbrakk>\<alpha>" for \<alpha>, simplified]
    have "Fun f (bef @ s # aft) \<ge>\<^sub>\<A> Fun f (bef @ t # aft)"
      by (auto simp: nth_append list_update_append)
  }
  then show ?thesis unfolding af_compatible_def by blast
qed

context
  assumes ok: "isOK encoder.check_encoding"
begin

interpretation encoder: encoding where E = encoder.E by (fact encoder.check_encoding[OF ok])
interpretation max_monus_encoding where E = encoder.E ..

lemma check_less_term:
  assumes "isOK (check_less_term solver s t)" shows "s <\<^sub>\<A> t"
  by (intro less_term_via_IA IA.check_valid_formula, insert assms, unfold check_less_term_def, auto)

lemma check_less_eq_term:
  assumes "isOK (check_less_eq_term solver s t)" shows "s \<le>\<^sub>\<A> t"
  by (intro less_eq_term_via_IA IA.check_valid_formula, insert assms, unfold check_less_eq_term_def, auto)

lemmas redpair = redpair

lemma check_simple_arg_pos:
  assumes "isOK (check_simple_arg_pos solver f n i)" shows "simple_arg_pos (rel_of (\<ge>\<^sub>\<A>)) (f, n) i"
  using assms by (intro simple_arg_pos_via_IA IA.check_valid_formula, auto simp: check_simple_arg_pos_def)

lemma check_ss_fun_arg:
  assumes "isOK (check_ss_fun_arg solver f n i)" shows "simple_arg_pos (rel_of (>\<^sub>\<A>)) (f, n) i"
  using assms by (intro ss_fun_arg_via_IA IA.check_valid_formula, auto simp: check_ss_fun_arg_def)

end

lemma default_E: "(f, n) \<notin> fst ` set simplified_alist \<Longrightarrow>
  encoder.E f n = Fun max_monus.MaxF (map Var [0..<n])"
  by (auto simp: encoder.E_def split: option.split dest!: map_of_SomeD)

end

lemma le_max_list: "(x::nat) \<in> set xs \<Longrightarrow> x \<le> max_list xs"
  using split_list by fastforce

lemma le_max_list1: "(x::nat) \<in> set xs \<Longrightarrow> x \<le> max_list1 xs"
  by (subst max_list_as_max_list1 [symmetric]) (auto simp: le_max_list)

datatype 'f max_monus_impl = Max_Monus_Impl la_solver_type "(('f \<times> nat) \<times> (max_monus.sig, nat)term) list"

fun max_monus_rel_impl where
  "max_monus_rel_impl (Max_Monus_Impl type rp) = max_monus_encoding_impl.create_max_monus_rel_impl rp type" 


lemma max_monus_rel_impl: "rel_impl (max_monus_rel_impl mpi)"
  unfolding rel_impl_def 
proof (intro impI allI, goal_cases)
  case (1 U)
  obtain type rp where mpi: "mpi = Max_Monus_Impl type rp" by (cases mpi, auto)
  interpret max_monus_encoding_impl rp . 
  note defs = mpi create_max_monus_rel_impl_def
  note 1 = 1[unfolded defs, simplified, unfolded defs, simplified]
  from 1 have enc: "isOK encoder.check_encoding" by auto
  then interpret encoder: encoding where E = encoder.E by (rule encoder.check_encoding)
  interpret max_monus_encoding where E = encoder.E..
  let ?S = "rel_of (>\<^sub>\<A>)" 
  let ?NS = "rel_of (\<ge>\<^sub>\<A>)" 
  interpret redpair_order ?S ?NS ..
  interpret redtriple_order ?S ?NS ?NS
    apply (unfold_locales; (intro redpair.subst_NS term.trans_NS term.compat_NS_S term.refl_NS)?)
    using term.less_imp_le by auto
  have [simp]: "map fst rp = map fst simplified_alist" by (auto simp: simplified_alist_def)
  have [simp]: "map (snd \<circ> fst) rp = map (snd \<circ> fst) simplified_alist"
    unfolding map_map [symmetric] by simp
  define n where "n \<equiv> max_list1 (map (snd \<circ> fst) rp) + 1"
  then have m: "\<And>c m. m \<ge> n \<Longrightarrow> (c, Suc (Suc m)) \<notin> set (map fst rp)"
    apply (auto simp:)
    apply (subgoal_tac "Suc (Suc m) \<le> max_list1 (map (snd \<circ> fst) simplified_alist)")
     apply simp
    apply (rule le_max_list1, force)
    done
  have 6: "ce_compatible ?NS"
  proof -
    {
      fix m c and l r :: "('a, 'e) term"
      assume nm: "n \<le> m" and "(l, r) \<in> ce_trs (c,m)"
      then obtain s t where l: "l = Fun c ([s,t] @ replicate m (Var undefined))" (is "_ = Fun _ ?ls") and r: "r = s \<or> r = t" 
        unfolding ce_trs.simps by auto
      have len: "length ?ls = Suc (Suc m)" by simp
      have id: "[0..<Suc (Suc m)] = [0,1] @ map (Suc o Suc) [0 ..< m]"
        unfolding map_map [symmetric] and map_Suc_upt
        by (auto simp: upt_conv_Cons)
      from m [OF nm] have "\<forall> \<alpha>. \<exists> k.\<lbrakk>l\<rbrakk>\<alpha> = max (\<lbrakk>s\<rbrakk> \<alpha>) (max (\<lbrakk>t\<rbrakk>\<alpha>) k)"
        unfolding default_E [OF m [OF nm, simplified]]
          and id and l and eval.simps and len and length_map
        by (auto)
      from choice [OF this] obtain k where "\<lbrakk>l\<rbrakk>\<alpha> = max (\<lbrakk>s\<rbrakk>\<alpha>) (max (\<lbrakk>t\<rbrakk>\<alpha>) (k \<alpha>))" for \<alpha> by blast
      with r have "l \<ge>\<^sub>\<A> r" by (auto intro: max.cobounded1)
      then have "(l,r) \<in> rel_of (\<ge>\<^sub>\<A>)" by auto
    }

    then show ?thesis unfolding ce_compatible_def by blast
  qed
  let ?rp = "max_monus_rel_impl mpi" 
  show ?case
  proof (rule exI[of _ ?S], intro exI[of _ ?NS] conjI impI 
      6 term.SN term.compat_S_NS term.compat_NS_S S_imp_NS term.trans_NS term.trans_S term.refl_NS top_mono_same)
    show "ctxt.closed ?NS" by blast
    show "subst.closed ?NS" by blast
    show "subst.closed ?S" by blast
    show "irrefl ?S" using term.SN unfolding irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this term.compat_NS_S] show "?NS \<inter> ?S^-1 = {}" .
    show "af_compatible (rel_impl.af ?rp) ?NS" 
      using af_compatible by (simp add: defs)
    show "af_compatible (rel_impl.top_af ?rp) ?NS" 
      using af_compatible by (simp add: defs)
    show "af_monotone (rel_impl.mono_af ?rp) ?S" 
      by (simp add: defs empty_af)
    show "not_subterm_rel_info ?NS (rel_impl.not_wst ?rp)" 
      by (auto simp:simple_arg_pos_def defs
        dest!:default_E 
        intro!: less_eq_termI le_max_list)
  qed (auto simp: defs no_complexity_check_def check_less_term[OF enc] check_less_eq_term[OF enc])
qed

declare max_monus_encoding_impl.check_less_term_def [code]
declare max_monus_encoding_impl.check_less_eq_term_def [code]
declare max_monus_encoding_impl.simplified_alist_def [code]
declare max_monus_encoding_impl.create_max_monus_rel_impl_def [code]
declare pre_encoded_algebra.constant_positions_def [code]

end
