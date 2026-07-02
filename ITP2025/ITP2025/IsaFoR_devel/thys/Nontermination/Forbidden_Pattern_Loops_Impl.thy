(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013, 2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Forbidden_Pattern_Loops_Impl
imports
  Innermost_Loops_Impl
  Forbidden_Pattern_Loops
  Nontermination_Impl
  TRS.Q_Restricted_Rewriting_Impl
  Framework.Termination_Problem_Spec
begin

(* from AFP/Automatic_Refinement/Lib/Misc *)
no_notation comp2 (infixl "oo" 55)

declare fixed_subst.n0_def[code]
declare fixed_subst.pos_dec_def[code]
declare fixed_subst.h_match_probs_def[code]

definition fp_H_decide where
  "fp_H_decide \<mu> l oo q C t \<equiv>
    \<not> (\<exists> mp \<in> fixed_subst.h_match_probs (si_subst \<mu>) l oo q C t. match_decision \<mu> mp)" 


context fixed_subst_incr
begin
lemma fp_H_decide: 
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
  shows "fp_H_decide \<mu>_incr l oo q C t = fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l,l|_oo,Forbidden_Patterns.H) C \<mu> q t"
  (is "?l = ?r")
proof -
  note d = fp_H_decide_def
  {
    assume "\<not> ?l"
    from this[unfolded d] obtain mp sol where mp: "mp \<in> h_match_probs l oo q C t" and sol: "match_solution mp sol" by auto
    from fp_h_match_probs_sound[OF qt ol mp, of "fst sol" "snd sol"] sol have "\<not> ?r" by auto
  }
  moreover
  {
    assume "\<not> ?r"
    from this[unfolded fpstep_ctxt_subst_cond_def] obtain n where
    "\<not> fpstep_cond_single (ctxt_of_pos_term oo l, l |_ oo, location.H) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)" by blast
    from fp_h_match_probs_complete[OF this qt] have "\<not> ?l" unfolding d ctxt_supt_id[OF ol] hole_pos_ctxt_of_pos_term[OF ol]
      by auto
  }
  ultimately show ?thesis by blast
qed


lemma a_match_probs_impl: "a_match_probs l oo q C t = (
  case t|_ q of Var x \<Rightarrow> {}
   | Fun f ls \<Rightarrow> 
    let
     \<comment> \<open>M_1\<close>
     h = hole_pos C; n = n0 h q oo; hn = h^n; cs = ctxt_subst C \<mu> n t; 
     q's = bounded_postfixes q (poss_list t);
     qoo's = concat (map (\<lambda> q'. map (Pair q') (prefix_list (hn @ q @ q'))) q's);
     qoo'sf = filter (\<lambda> qoo. (hn @ q) <\<^sub>p (snd qoo @ oo)) qoo's;
     m1 = map (\<lambda> qoo. (cs |_ snd qoo, l)) qoo'sf;
     \<comment> \<open>M_2\<close>
     sterms = remdups (map (si_subst \<mu>_incr) (si_W \<mu>_incr (t |_ q)));
     uterms = concat (map (filter is_Fun \<circ> supteq_list) sterms);
     m2 = map (\<lambda>u. (u, l)) (remdups uterms)
     in
     set (m1 @ m2))"
proof -
  note d = Let_def a_match_probs_def
  show ?thesis
  proof (cases "t|_q")
    case (Var x)
    show ?thesis unfolding d Var by auto
  next
    case (Fun f ts)
    have un_cong: "\<And> x1 x2 y1 y2. x2 = y2 \<Longrightarrow> x1 = y1 \<Longrightarrow> x1 \<union> x2 = y1 \<union> y2" by simp
    show ?thesis unfolding d Fun term.simps set_append by (rule un_cong, unfold si_W[symmetric] term.simps,force+)
  qed
qed
end

declare fixed_subst_incr.a_match_probs_impl[code_unfold]

definition fp_A_decide where
  "fp_A_decide \<mu> l oo q C t \<equiv>
    \<not> (\<exists> mp \<in> fixed_subst.a_match_probs (si_subst \<mu>) l oo q C t. match_decision \<mu> mp)"

context fixed_subst_incr
begin
lemma fp_A_decide: 
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and tq: "is_Fun (t |_ q)"
    and l: "is_Fun l"
  shows "fp_A_decide \<mu>_incr l oo q C t = fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l,l|_oo,Forbidden_Patterns.A) C \<mu> q t"
  (is "?l = ?r")
proof -
  note d = fp_A_decide_def
  {
    assume "\<not> ?l"
    from this[unfolded d] obtain mp sol where mp: "mp \<in> a_match_probs l oo q C t" and sol: "match_solution mp sol" by auto
    from mp obtain u where mp_ul: "mp = (u,l)" unfolding a_match_probs_def by (cases "t |_ q", auto)
    from fp_a_match_probs_sound[OF qt ol mp[unfolded mp_ul], of "fst sol" "snd sol"] sol mp_ul have "\<not> ?r" by auto
  }
  moreover
  {
    note id = ctxt_supt_id[OF ol] hole_pos_ctxt_of_pos_term[OF ol]
    assume "\<not> ?r"
    from this[unfolded fpstep_ctxt_subst_cond_def] obtain n where
      fp:"\<not> fpstep_cond_single (ctxt_of_pos_term oo l, l |_ oo, location.A) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)" by blast
    from l id have "is_Fun ((ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle>)" by auto
    from fp_a_match_probs_complete[OF fp qt tq this]
    have "\<not> ?l" unfolding d id by auto
  }
  ultimately show ?thesis by blast
qed
end


(* case B *)

context fixed_subst_incr
begin

definition n0b_impl :: "pos \<Rightarrow> pos \<Rightarrow> pos \<Rightarrow> nat" where "n0b_impl p q oo = n0b p q oo"

definition decompositions :: "pos  \<Rightarrow> (pos \<times> pos) list"
where "decompositions p \<equiv>  map (\<lambda> p'. (p',the (remove_prefix p' p))) (prefix_list p)"

lemma decompositions_ok: "set(decompositions p) = {u. \<exists> p' q. u = (p',q) \<and> p' @ q = p}"
proof(rule,rule)
 fix p' q
 assume p:"(p',q) \<in> set(decompositions p)"
 then have p:"p' \<in> set(prefix_list p) \<and> q = the (remove_prefix p' p)" unfolding decompositions_def by force
 with p have "remove_prefix p' p = Some q" by (metis mem_Collect_eq suffix_exists prefix_list option.sel)
  then have "p' @ q = p" by simp
 then show "(p',q) \<in> {u. \<exists> p' q. u = (p',q) \<and> p' @ q = p}" by blast
next
 show "{(p'', q') |p'' q'. p'' @ q' = p} \<subseteq> set (decompositions p)" 
 proof
  fix p' q
  assume ass:"(p',q) \<in> {u. \<exists> p' q. u = (p',q) \<and> p' @ q = p}"
  then have "p' @ q = p" by simp 
  then have p:"remove_prefix p' p = Some q" by simp
  then have q:"q = the (remove_prefix p' p)" by auto
  from p have "p' \<le>\<^sub>p p" unfolding less_eq_pos_def by simp
  with prefix_list have "p' \<in> set(prefix_list p)" by auto
  with q show "(p',q) \<in> set(decompositions p)" unfolding decompositions_def by auto
 qed
qed

lemma b_ematch_probs_impl: "b_ematch_probs l oo q C t = (
  let 
   p = hole_pos C;
   n = \<lambda> p''. n0b p p'' oo;
   ps = filter (\<lambda> (p''',p''). oo <\<^sub>p p'' @ p ^ (n p'') \<and> p''' <\<^sub>p p) (remdups (decompositions p))
  in
  set (map (\<lambda> (p''',p''). (C |_c p''', l, C \<cdot>\<^sub>c \<mu>, (ctxt_subst C \<mu> (n p'') t) \<cdot> \<mu>)) (remdups ps)))"
  (is "_ = ?r")
proof -
  let ?p = "hole_pos C"
  let ?n = "\<lambda> p''. n0b ?p p'' oo"
  let ?f = "\<lambda> (p''',p''). oo <\<^sub>p p'' @ ?p ^ (?n p'') \<and> p''' <\<^sub>p ?p"
  let ?m = "\<lambda> (p''',p''). (C |_c p''', l, C \<cdot>\<^sub>c \<mu>, (ctxt_subst C \<mu> (?n p'') t) \<cdot> \<mu>)"
  have "?r = {u. \<exists> x. u = ?m x \<and> x \<in> set (decompositions ?p) \<and> ?f x}" unfolding Let_def by force
  also have "\<dots> = {u. \<exists> p' q'. u = ?m (p',q') \<and> (p' @ q' = ?p) \<and> ?f (p',q')}" unfolding decompositions_ok by force
  finally show ?thesis unfolding b_ematch_probs_def by auto
qed

end

declare fixed_subst.n0b_def[code]
declare fixed_subst_incr.decompositions_def[code]
declare fixed_subst_incr.b_ematch_probs_impl[code_unfold]


lemma (in fixed_subst_incr) b_match_code: "b_match_probs l oo q C t = 
       \<Union> (set (map (\<lambda> q'. h_match_probs l oo q' C t) (proper_prefix_list q)))"
  unfolding  b_match_probs_def by auto

declare fixed_subst_incr.b_match_code[code_unfold]

definition fp_B_decide where
  "fp_B_decide \<mu> l oo q C t \<equiv> 
    \<not> (\<exists> mp \<in> fixed_subst.b_match_probs (si_subst \<mu>) l oo q C t. match_decision \<mu> mp) \<and>
    \<not> (\<exists> ep \<in> fixed_subst.b_ematch_probs (si_subst \<mu>) l oo q C t. 
       \<exists> idps \<in> set_option (fixed_subst_incr.ident_prob_of_emp \<mu>  ep). (\<forall> idp \<in> set idps. ident_decision \<mu> idp) )"

context fixed_subst_incr
begin

lemma fp_B_decide: 
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and l: "is_Fun l"
  shows "fp_B_decide \<mu>_incr l oo q C t = fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l,l|_oo,Forbidden_Patterns.B) C \<mu> q t"
  (is "?l = ?r")
proof -
  note d = fp_B_decide_def
  from l ol have l': "is_Fun (ctxt_of_pos_term oo l)\<langle>l|_oo\<rangle>" using ctxt_supt_id by fastforce
  {
    assume "\<not> ?l"
     from this[unfolded d] have AB:"(\<exists> mp \<in> b_match_probs l oo q C t. \<exists> sol. match_solution mp sol) \<or>
     (\<exists> ep \<in> b_ematch_probs l oo q C t. 
       \<exists> idps \<in> set_option (ident_prob_of_emp ep). (\<forall> idp \<in> set idps. ident_decision \<mu>_incr idp))" (is "?A \<or> ?B") 
     by auto
    have "\<not> ?r" proof(cases ?A)
     case True
      then obtain mp sol where mp: "mp \<in> b_match_probs l oo q C t" and sol: "match_solution mp sol" by auto
      from b_match_probs_sound[OF qt ol _ mp, of "fst sol" "snd sol"] sol show "\<not> ?r" by auto
     next
     case False
      with AB have ?B by auto
      then obtain ep idps where prob:"ep \<in> b_ematch_probs l oo q C t" and
      isol:"ident_prob_of_emp ep = Some idps \<and> (\<forall> idp \<in> set idps. \<exists> sol. ident_solution idp sol)" by force
      from prob[unfolded b_ematch_probs_def] obtain p t' where ep:"ep = (C |_c p, l, C \<cdot>\<^sub>c \<mu>, t')" and p:"p <\<^sub>p hole_pos C" by blast
      with ident_prob_of_emp[OF _ p] isol obtain sol where "ematch_solution ep sol" by fast
      with b_ematch_probs_sound[OF qt ol _ prob] show "\<not> ?r" unfolding fpstep_ctxt_subst_cond_def by (metis prod_cases3)
    qed
  }
  moreover
  {
    note id = ctxt_supt_id[OF ol] hole_pos_ctxt_of_pos_term[OF ol]
    assume "\<not> ?r"
    from this[unfolded fpstep_ctxt_subst_cond_def] obtain n where
      fp:"\<not> fpstep_cond_single (ctxt_of_pos_term oo l, l |_ oo, location.B) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)" by blast
    from l id have f:"is_Fun ((ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle>)" by auto
    from ol have l_is:"l = (ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle>" by (metis id(1))
    from fp_b_match_probs_complete[OF fp qt f] 
    have AB: "(\<exists>mp n \<sigma>. mp \<in> fixed_subst.b_match_probs \<mu> (ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle> (hole_pos (ctxt_of_pos_term oo l)) q C t \<and>
            fixed_subst.match_solution \<mu> mp (n, \<sigma>)) \<or>
  (\<exists>emp n k \<sigma> p t'.
      emp \<in> fixed_subst.b_ematch_probs \<mu> (ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle> (hole_pos (ctxt_of_pos_term oo l)) q C t \<and>
      fixed_subst.ematch_solution \<mu> emp (n, k, \<sigma>) \<and> emp = (C |_c p, l, C \<cdot>\<^sub>c \<mu>, t') \<and> p <\<^sub>p hole_pos C)" (is "?A \<or> ?B") using l_is by auto
    have "?B \<longrightarrow> (\<exists> ep \<in> b_ematch_probs l oo q C t. 
       \<exists> idps \<in> set_option (ident_prob_of_emp ep). (\<forall> idp \<in> set idps. ident_decision \<mu>_incr idp))" (is "?B \<longrightarrow> ?C")
    proof
     assume B:?B
     then obtain ep n' k \<sigma> p t' where aux:"ep \<in> b_ematch_probs l (hole_pos (ctxt_of_pos_term oo l)) q C t"
      and sol:"ematch_solution ep (n', k, \<sigma>)" and ep_is:"ep = (C |_c p, l, C \<cdot>\<^sub>c \<mu>, t')" and p:"p <\<^sub>p hole_pos C" using l_is by force
     from sol have "\<exists>idps. ident_prob_of_emp ep = Some idps \<and> (\<forall> idp \<in> set idps. \<exists>sol. ident_solution idp sol)" 
      using ident_prob_of_emp[OF _ p] unfolding ep_is by fast
     then show ?C by (metis aux elem_set id(2) ident_decision)
    qed
    with AB have "\<not> ?l" unfolding d ident_decision match_decision
      using id l_is by auto
  }
  ultimately show ?thesis by blast
qed

lemma possc_left: "(p \<in> poss C\<langle>t\<rangle> \<and> left_of_pos p (hole_pos C)) = (p \<in> possc C \<and> left_of_pos p (hole_pos C))"
 (is "?A = ?B")
proof
  assume "?A"
  then have px:"p \<in> poss C\<langle>t\<rangle>" and l:"left_of_pos p (hole_pos C)" by auto
  with left_pos_parallel have "hole_pos C \<bottom> p" by blast
  from par_hole_pos_in_possc[OF this px] l show "?B" by blast
 next
  show "?B \<Longrightarrow> ?A" unfolding possc_def by fast
qed

lemma r_match_probs_impl: "r_match_probs l oo q C t = ( 
    let
     \<comment> \<open>M_1\<close>
     h = hole_pos C; 
     q's = filter (\<lambda> q'. is_left_of q' q) (poss_list t);
     m1 = map (\<lambda> q'. (t |_ q', l)) q's;
     \<comment> \<open>M_2\<close>
     sterms = remdups (map (si_subst \<mu>_incr) (remdups (concat (map (\<lambda> q'. si_W \<mu>_incr (t |_ q')) q's))));
     uterms = concat (map supteq_list sterms);
     m2 = map (\<lambda>u. (u, l)) (remdups uterms);
     \<comment> \<open>M_3\<close>
     p's = filter (\<lambda> q'. is_left_of q' h) (poss_list C\<langle>t\<rangle>);
     m3 = map (\<lambda> p'. (C\<langle>t\<rangle> |_ p', l)) p's;
     \<comment> \<open>M_4\<close>
     sterms = remdups (map (si_subst \<mu>_incr) (remdups (concat (map (\<lambda> p'. si_W \<mu>_incr (C\<langle>t\<rangle> |_ p')) p's))));
     uterms = concat (map supteq_list sterms);
     m4 = map (\<lambda>u. (u, l)) (remdups uterms)
     in
     set (m1 @ m2 @ m3 @ m4))"
proof -
 have un_cong: "\<And> x1 y1 x2 y2 x3 y3 x4 y4. x1 = y1 \<Longrightarrow> x2 = y2 \<Longrightarrow> x3 = y3 \<Longrightarrow> x4 = y4 \<Longrightarrow> 
     (x1 \<union> x2 \<union> x3 \<union> x4) = (y1 \<union> (y2 \<union> (y3 \<union> y4)))" by force
 have aux:"\<And> p'. (p' \<in> poss C\<langle>t\<rangle> \<and> left_of_pos p' (hole_pos C)) = (p' \<in> (set (filter (right_of_pos (hole_pos C)) (poss_list C\<langle>t\<rangle>))))"
  unfolding term.simps by force+
 then have aux: 
  "{uu. \<exists>s u p'. uu = (u, l) \<and> p' \<in> possc C \<and> right_of_pos (hole_pos C) p' \<and> s \<in> \<mu> ` set (si_W \<mu>_incr (C\<langle>t\<rangle> |_ p')) \<and> s \<unrhd> u} =
    set (map (\<lambda>u. (u, l)) (remdups (concat (map supteq_list (remdups
                        (map \<mu> (remdups (concat (map (\<lambda>p'. si_W \<mu>_incr (C\<langle>t\<rangle> |_ p'))
                                                   (filter (right_of_pos (hole_pos C)) (poss_list C\<langle>t\<rangle>)))))))))))" 
     using possc_left[of _ C t] by auto
 show ?thesis unfolding Let_def r_match_probs_def set_append 
     by (rule un_cong, unfold si_W[symmetric] term.simps is_left_of aux, force+)
qed
end


declare fixed_subst_incr.r_match_probs_impl[code_unfold]

definition fp_R_decide where
  "fp_R_decide \<mu> l oo q C t \<equiv>
    \<not> (\<exists> mp \<in> fixed_subst.r_match_probs (si_subst \<mu>) l oo q C t. match_decision \<mu> mp)"

context fixed_subst_incr
begin
lemma fp_R_decide: 
  assumes qt: "q \<in> poss t" 
    and ol: "oo  \<in> poss l"
    and tq: "is_Fun (t |_ q)"
    and l: "is_Fun l"
  shows "fp_R_decide \<mu>_incr l oo q C t = fpstep_ctxt_subst_cond (ctxt_of_pos_term oo l,l|_oo,Forbidden_Patterns.R) C \<mu> q t"
  (is "?l = ?r")
proof -
  note d = fp_R_decide_def
  {
    assume "\<not> ?l"
    from this[unfolded d] obtain mp sol where mp: "mp \<in> r_match_probs l oo q C t" and sol: "match_solution mp sol" by auto
    from mp obtain u where mp_ul: "mp = (u,l)" unfolding r_match_probs_def by auto
    from fp_r_match_probs_sound[OF qt ol mp[unfolded mp_ul] l, of "fst sol" "snd sol"] sol mp_ul have "\<not> ?r" by auto
  }
  moreover
  {
    note id = ctxt_supt_id[OF ol] hole_pos_ctxt_of_pos_term[OF ol]
    assume "\<not> ?r"
    from this[unfolded fpstep_ctxt_subst_cond_def] obtain n where
      fp:"\<not> fpstep_cond_single (ctxt_of_pos_term oo l, l |_ oo, location.R) (hole_pos C ^ n @ q) (ctxt_subst C \<mu> n t)" by blast
    from l id have "is_Fun ((ctxt_of_pos_term oo l)\<langle>l |_ oo\<rangle>)" by auto
    from fp_r_match_probs_complete[OF fp qt, unfolded ctxt_supt_id[OF ol], OF l]  have "\<not> ?l" unfolding d id by auto
  }
  ultimately show ?thesis by blast
qed
end

definition fp_decide where
  "fp_decide \<mu> \<equiv> \<lambda> (q,C,t) (L,l,loc) . 
   ((loc = Forbidden_Patterns.H \<longrightarrow> fp_H_decide \<mu> L\<langle>l\<rangle> (hole_pos L) q C t) \<and> 
    (loc = Forbidden_Patterns.A \<longrightarrow> fp_A_decide \<mu> L\<langle>l\<rangle> (hole_pos L) q C t) \<and> 
    (loc = Forbidden_Patterns.B \<longrightarrow> fp_B_decide \<mu> L\<langle>l\<rangle> (hole_pos L) q C t) \<and>
    (loc = Forbidden_Patterns.R \<longrightarrow> fp_R_decide \<mu> L\<langle>l\<rangle> (hole_pos L) q C t))"


definition fp_decide_all where
  "fp_decide_all \<mu> P \<equiv> \<lambda> (q,C,t). \<forall> pt \<in> P. fp_decide \<mu> (q,C,t) pt"

definition fp_valid where "fp_valid P \<equiv> \<forall> (L,l,loc) \<in> P. is_Fun L\<langle>l\<rangle>"

context fixed_subst_incr
begin
lemma fp_decide: 
  assumes qt: "q \<in> poss t" and tq: "is_Fun (t |_ q)" and val:"fp_valid P" and mem:"(L,l,loc) \<in> P"
  shows "fp_decide \<mu>_incr (q,C,t) (L,l,loc) = fpstep_ctxt_subst_cond (L,l,loc) C \<mu> q t"
  proof-
   from val mem have lfun:"is_Fun L\<langle>l\<rangle>" unfolding fp_valid_def by auto
   have ol:"hole_pos L \<in> poss L\<langle>l\<rangle>" by (metis hole_pos_poss)
   then have x:"ctxt_of_pos_term (hole_pos L) L\<langle>l\<rangle> = L" by (metis ctxt_of_pos_term_hole_pos)  
   have y:" L\<langle>l\<rangle> |_ hole_pos L = l" by (metis subt_at_hole_pos)
   then show ?thesis
    unfolding fp_decide_def split fp_A_decide[OF qt ol tq lfun] fp_H_decide[OF qt ol] 
              fp_B_decide[OF qt ol lfun]  fp_R_decide[OF qt ol tq lfun] x y
    by (cases loc,simp_all)
  qed

lemma fp_decide_all:
 assumes qt: "q \<in> poss t" and tq: "is_Fun (t |_ q)" and val:"fp_valid P" and mem:"(L,l,loc) \<in> P"
 shows "fp_decide_all \<mu>_incr P (q,C,t) = (\<forall> pt \<in> P. fpstep_ctxt_subst_cond pt C \<mu> q t)"
 unfolding fp_decide_all_def split using fp_decide[OF qt tq val] by (metis prod_cases3)
end

declare fp_decide_def[code]

declare fp_decide_all_def[code]

fun showsl_pattern :: "('f :: showl, 'v :: showl)forb_pattern \<Rightarrow> showsl" where
  "showsl_pattern (C,s,p) = (showsl_lit (STR ''('') \<circ> showsl (C\<langle>s\<rangle>) \<circ> showsl_lit (STR '', '') \<circ> showsl_pos (hole_pos C) \<circ>
    showsl_lit (STR '', '') \<circ> showsl p \<circ> showsl_lit (STR '')''))"

datatype ('f,'v)fp_loop_prf = FP_loop_prf "('f,'v)ctxt" "('f,'v)substL" "('f,'v)term" "('f,'v)rseq"

primrec check_fploop :: "('f :: showl,'v :: showl)rules \<Rightarrow>('f,'v)forb_pattern list \<Rightarrow> 
  ('f,'v)fp_loop_prf \<Rightarrow> showsl check" where 
  "check_fploop R P (FP_loop_prf C \<sigma> t seq) = do {
        let \<mu> = subst_incr \<sigma>;
        let \<mu>' = si_subst \<mu>;
        check (seq \<noteq> []) (showsl_lit (STR ''looping reduction must not be empty''));
        check ((\<lambda> (_,_,t). t) (last seq) = C \<langle> t \<cdot> \<mu>' \<rangle>) (showsl_lit (STR ''last term in sequence is not C[t sigma]''));
        check (fp_valid (set P)) (showsl_lit (STR ''lhss in forbidden patterns must not be variables''));
        check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhss of TRS must not be variables''))) R;
        let seq' = zip (t # map (\<lambda> (_,_,t). t) seq) seq;
        check_allm (\<lambda> (t,q,r,s). do {
            check_rstep' R q r t s;
            let check_fpstep = fp_decide \<mu> (q,C,t);
            check_allm (\<lambda> pt. check (check_fpstep pt) ( 
              showsl_lit (STR ''iterating reduction '') \<circ> showsl t \<circ> showsl_lit (STR '' -->'') \<circ>
              showsl_pos q \<circ> showsl_lit (STR '' '') \<circ> showsl s \<circ> showsl_lit (STR '' does not respect forbidden pattern '') \<circ> showsl_pattern pt)) P
          }) seq'
     }"

lemma check_fploop: assumes ok: "isOK (check_fploop R P (FP_loop_prf C \<mu> t seq))"
  shows "fploop (set P) (set R) (C, mk_subst Var \<mu>, length seq - 1, nth (t # map (\<lambda> (_,_,t). t) seq), nth (map (\<lambda> (p,_,_).p) seq))"
  (is "fploop ?P ?R (_,?\<mu>',?n,nth ?ts, nth ?ps)")
proof - 
  let ?zip = "zip (t # map (\<lambda>(_, _, t). t) seq) seq"
  let ?\<mu> = "subst_incr \<mu>"
  note ok = ok[unfolded check_fploop.simps Let_def, simplified]
  from ok have seq: "seq \<noteq> []" by auto
  from last_conv_nth[OF this] have last: "last seq = seq ! ?n" .
  from ok have val:"fp_valid (set P)" by simp
  let ?rs = "map (\<lambda>(_,lr,_).lr) seq"
  {
    fix i
    assume i: "i \<le> ?n"
    with seq have i: "i < length seq" by (cases seq, auto)
    have len: "length ?zip = length seq" by simp
    define ti where "ti = ?ts ! i"
    define pi where "pi = ?ps ! i"
    have "(ti, pi, ?rs ! i, ?ts ! (Suc i)) = ?zip ! i" unfolding ti_def pi_def using i by (cases "seq ! i", auto)    
    with i have mem: "(ti, pi, ?rs ! i, ?ts ! (Suc i)) \<in> {?zip ! i | i. i < length seq}" by blast
    from ok[unfolded set_conv_nth[of ?zip] len] have
      "\<And> x. x \<in> {?zip ! i |i. i < length seq} \<Longrightarrow>
        case x of (t, q, r, s) \<Rightarrow>
          (\<exists>\<sigma>. (t, s) \<in> rstep_r_p_s (set R) r q \<sigma>) \<and> (\<forall>x\<in>set P. fp_decide (subst_incr \<mu>) (q, C, t) x)"
      by blast
    from this[OF mem] have
      step: "\<exists>\<sigma>. (ti, ?ts ! Suc i) \<in> rstep_r_p_s ?R (?rs ! i) pi \<sigma>" and
      fpcond: "(\<forall> pt \<in> set P. fp_decide ?\<mu> (pi, C, ti) pt)" by auto
    from step have x:"pi \<in> poss ti" unfolding rstep_r_p_s_def Let_def by auto
    from step[unfolded rstep_r_p_s_def] have y:"is_Fun (ti |_ pi)"
    proof-
     let ?l = "fst (?rs ! i)"
     from step obtain \<sigma> where step':"(ti, ?ts ! Suc i) \<in> rstep_r_p_s ?R (?rs ! i) pi \<sigma>" (is "?x \<in> ?X")by auto
     from this[unfolded rstep_r_p_s_def, unfolded Let_def] have " (?rs ! i) \<in> (set R)" by fast
     with ok have fl: "is_Fun (?l \<cdot> \<sigma>)" by force
     from step'[unfolded rstep_r_p_s_def, unfolded Let_def] have "(ctxt_of_pos_term pi ti)\<langle>?l \<cdot> \<sigma>\<rangle> = ti" by fastforce
     with fl show ?thesis using replace_at_subt_at[OF x] by metis
    qed
    from fpcond fixed_subst_incr.fp_decide[OF x y val] have 
      fpcond: "(\<forall> pt \<in> ?P. fpstep_ctxt_subst_cond pt C ?\<mu>' pi ti)" by (metis prod_cases3 si_subst_subst_incr) 
    from step have "\<exists> \<sigma> lr. (ti, ?ts ! Suc i) \<in> rstep_r_p_s ?R lr pi \<sigma>" by blast
    note this fpcond
  } note steps = this
  show ?thesis
  proof (rule fploopI)
    from ok have id: "((\<lambda> (_,_,t). t) (last seq)) = C\<langle>t \<cdot> ?\<mu>'\<rangle>" by (simp add: si_subst_subst_incr)
    have "?ts ! Suc ?n = ((\<lambda> (_,_,t). t) (last seq))" unfolding last using seq by simp
    also have "... = C \<langle> ?ts ! 0 \<cdot> ?\<mu>' \<rangle>" unfolding id by simp
    finally 
    show "?ts ! Suc ?n = C \<langle> ?ts ! 0 \<cdot> ?\<mu>' \<rangle>" .
  qed (insert steps, auto)
qed

lemma check_fploop_not_SN:
  assumes ok: "isOK(check_fploop R P prf)"
  shows "\<not> SN (fpstep (set P) (set R))"
proof -
  obtain C \<mu> t seq where id: "prf = FP_loop_prf C \<mu> t seq" by (cases "prf")
  from fploop_imp_not_SN[OF check_fploop[OF ok[unfolded id]]]
  show ?thesis unfolding SN_on_def by blast
qed

definition "check_fploop_tp I tp P \<equiv> check_fploop (tp_ops.rules I tp) P"

lemma check_fploop_tp:
  assumes ok: "isOK(check_fploop_tp I tp P prf)"
  shows "\<not> SN (fpstep (set P) (set (tp_ops.rules I tp)))"
  by (rule check_fploop_not_SN[OF ok[unfolded check_fploop_tp_def]])

definition [code_unfold]: "rule_removal_nonterm_fp_trs = rule_removal_nonterm_trs"

lemma rule_removal_nonterm_fp_trs: 
  assumes I: "tp_spec I" 
    and ok: "rule_removal_nonterm_fp_trs I tp prf = return tp'"
    and nSN: "\<not> SN (fpstep fp (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (fpstep fp (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof -
  note ok = ok[unfolded rule_removal_nonterm_fp_trs_def]
  note * = rule_removal_nonterm_trs_id[OF I ok]
  show ?thesis
  proof
    assume SN: "SN ?tp"
    have "SN ?tp'"
      by (rule SN_subset[OF SN], rule fpstep_mono, insert *(3), auto)
    with nSN show False by blast
  qed
qed

end

