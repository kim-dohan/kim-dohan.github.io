(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Outermost_Loops_Impl
imports
  Innermost_Loops_Impl
  Outermost_Loops
  TRS.Q_Restricted_Rewriting_Impl
  Framework.Termination_Problem_Spec
begin

definition o_match_probs_impl :: "('f,'v)term \<Rightarrow> pos \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v) match_prob list"
  where "o_match_probs_impl l q t \<equiv> map (\<lambda> p. (t |_ p, l)) (proper_prefix_list q)"

definition o_ematch_probs_impl :: "('f,'v)subst \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> pos \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) ematch_prob list" where
  "o_ematch_probs_impl \<mu> C l q t \<equiv> map (\<lambda> p. (C |_c p, l, C \<cdot>\<^sub>c \<mu>, t \<cdot> \<mu>)) (proper_prefix_list (hole_pos C))"

context fixed_subst
begin
lemma o_match_probs_impl[simp]: "set (o_match_probs_impl l q t) = o_match_probs l q t"
  unfolding o_match_probs_impl_def o_match_probs_def by auto

lemma o_ematch_probs_impl[simp]: "set (o_ematch_probs_impl \<mu> C l q t) = o_ematch_probs C l q t"
  unfolding o_ematch_probs_impl_def o_ematch_probs_def by auto
end

definition (in fixed_subst_incr) ostep_ctxt_subst_cond_impl where 
  "ostep_ctxt_subst_cond_impl C l q t \<equiv> (\<not> ((\<exists> mp \<in> set (o_match_probs_impl l q t). match_decision \<mu>_incr mp) \<or>
        (\<exists> mp \<in> set (o_ematch_probs_impl \<mu> C l q t). \<exists> idps \<in> set_option (ident_prob_of_emp mp). (\<forall> idp \<in> set idps. ident_decision \<mu>_incr idp))))"

declare fixed_subst_incr.ostep_ctxt_subst_cond_impl_def[code]

lemma (in fixed_subst_incr) ostep_ctxt_subst_cond_impl:
  assumes q: "q \<in> poss t"
  shows "ostep_ctxt_subst_cond_impl C l q t = 
  ostep_ctxt_subst_cond l C \<mu> q t"
  unfolding ostep_ctxt_subst_cond_impl_def o_ematch_probs_impl o_match_probs_impl ostep_ctxt_subst_cond_to_match_idents[OF q]
  unfolding match_decision[symmetric] ident_decision[symmetric]
  by auto

type_synonym ('f,'v)ostep_prob = "('f,'v)ctxt \<times> ('f,'v)term \<times> pos \<times> ('f,'v)term"

definition ostep_ctxt_subst_cond_decision :: "('f, 'v) subst_incr \<Rightarrow> ('f,'v)ostep_prob \<Rightarrow> bool" where
  "ostep_ctxt_subst_cond_decision \<mu> \<equiv> 
    (\<lambda>(C,l,q,t). fixed_subst_incr.ostep_ctxt_subst_cond_impl \<mu> C l q t)"

lemma ostep_ctxt_subst_cond_decision: assumes q: "q \<in> poss t"
  shows "ostep_ctxt_subst_cond_decision \<mu> (C,l,q,t) = 
        ostep_ctxt_subst_cond l C (si_subst \<mu>) q t"
proof -
  interpret fixed_subst_incr \<mu> .
  show ?thesis 
    unfolding ostep_ctxt_subst_cond_decision_def Let_def split 
    unfolding ostep_ctxt_subst_cond_impl[OF q] ..
qed

definition check_oloop :: "('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)ctxt \<Rightarrow> 
  ('f,'v)substL \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)rseq \<Rightarrow> showsl check"
  where "check_oloop R Q C \<sigma> t seq \<equiv> do {
        let \<mu> = subst_incr \<sigma>;
        let \<mu>' = si_subst \<mu>;
        check (seq \<noteq> []) (showsl_lit (STR ''looping reduction must not be empty''));
        check ((\<lambda> (_,_,t). t) (last seq) = C \<langle> t \<cdot> \<mu>' \<rangle>) (showsl_lit (STR ''last term in sequence is not C[t sigma]''));
        let seq' = zip (t # map (\<lambda> (_,_,t). t) seq) seq;
        let check_ostep = ostep_ctxt_subst_cond_decision \<mu>;
        check_allm (\<lambda> (t,p,r,s). do {
            check_rstep' R p r t s;
            check_allm (\<lambda> l. check (check_ostep (C,l,p,t)) ( 
              showsl_lit (STR ''reduction from '') \<circ> showsl t \<circ> showsl_lit (STR '' -->'') \<circ>
              showsl_pos p \<circ> showsl_lit (STR '' '') \<circ> showsl s \<circ> showsl_lit (STR '' does not respect iterated outermost condition''))) 
            Q
          }) seq'; 
        succeed
     }"

lemma check_oloop: assumes ok: "isOK (check_oloop R Q C \<mu> t seq)"
  shows "oloop (set Q) (set R) (C, mk_subst Var \<mu>, length seq - 1, nth (t # map (\<lambda> (_,_,t). t) seq), nth (map (\<lambda> (p,_,_).p) seq))"
  (is "oloop ?Q ?R (_,?\<mu>',?n,nth ?ts, nth ?ps)")
proof - 
  let ?zip = "zip (t # map (\<lambda>(_, _, t). t) seq) seq"
  let ?\<mu> = "subst_incr \<mu>"
  note ok = ok[unfolded check_oloop_def Let_def, simplified]
  from ok have seq: "seq \<noteq> []" by auto
  from last_conv_nth[OF this] have last: "last seq = seq ! ?n" .
  let ?rs = "map (\<lambda>(_,lr,_).lr) seq"
  {
    fix i
    assume i: "i \<le> ?n"
    with seq have i: "i < length seq" by (cases seq, auto)
    have len: "length ?zip = length seq" by simp
    have "(?ts ! i, ?ps ! i, ?rs ! i, ?ts ! (Suc i)) = ?zip ! i" using i by (cases "seq ! i", auto)    
    with i have mem: "(?ts ! i, ?ps ! i, ?rs ! i, ?ts ! (Suc i)) \<in> {?zip ! i | i. i < length seq}" by blast
    from ok[unfolded set_conv_nth[of ?zip] len] have 
      "\<And> t p ra s. (t, p, ra, s)\<in>{?zip ! i |i. i < length seq} \<Longrightarrow>
        (\<exists>\<sigma>. (t, s) \<in> rstep_r_p_s (set R) ra p \<sigma>) \<and> (\<forall>x\<in>set Q. ostep_ctxt_subst_cond_decision ?\<mu> (C, x, p, t))" by force
    from this[OF mem] have
      step: "\<exists>\<sigma>. (?ts ! i, ?ts ! Suc i) \<in> rstep_r_p_s ?R (?rs ! i) (?ps ! i) \<sigma>" and
      ocond: "(\<forall> l \<in> ?Q. ostep_ctxt_subst_cond_decision ?\<mu> (C, l, ?ps ! i, ?ts ! i))" by auto
    from step have "?ps ! i \<in> poss (?ts ! i)" unfolding rstep_r_p_s_def Let_def by auto
    from ocond[unfolded ostep_ctxt_subst_cond_decision[OF this], unfolded si_subst_subst_incr] have 
      ocond: "(\<forall> l \<in> ?Q. ostep_ctxt_subst_cond l C ?\<mu>' (?ps ! i) (?ts ! i))" .
    from step have "\<exists> \<sigma> lr. (?ts ! i, ?ts ! Suc i) \<in> rstep_r_p_s ?R lr (?ps ! i) \<sigma>" by blast
    note this ocond
  } note steps = this
  show ?thesis
  proof (rule oloopI)
    from ok have id: "((\<lambda> (_,_,t). t) (last seq)) = C\<langle>t \<cdot> ?\<mu>'\<rangle>" by (simp add: si_subst_subst_incr)
    have "?ts ! Suc ?n = ((\<lambda> (_,_,t). t) (last seq))" unfolding last using seq by simp
    also have "... = C \<langle> ?ts ! 0 \<cdot> ?\<mu>' \<rangle>" unfolding id by simp
    finally 
    show "?ts ! Suc ?n = C \<langle> ?ts ! 0 \<cdot> ?\<mu>' \<rangle>" .
  qed (insert steps, auto)
qed

lemma check_oloop_not_SN: assumes ok: "isOK(check_oloop R Q C \<mu> t seq)"
  shows "\<not> SN (ostep (set Q) (set R))"
proof -
  from oloop_imp_not_SN[OF check_oloop[OF ok]]
  show ?thesis unfolding SN_on_def by blast
qed

definition "check_oloop_tp I tp \<equiv> check_oloop (tp_ops.rules I tp) (tp_ops.Q I tp)"

lemma check_oloop_tp: assumes ok: "isOK(check_oloop_tp I tp C \<sigma> s rseq)"
  shows "\<not> SN (ostep (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))"
  by (rule check_oloop_not_SN[OF ok[unfolded check_oloop_tp_def]])

end
