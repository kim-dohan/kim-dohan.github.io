theory Invariant_Proof_Checkers
  imports 
    Invariant_Checker 
    Show_LTS 
    Invariants_To_Assertions
begin

datatype ('f,'v,'t,'l,'n,'tr,'s) invariant_proof =
   Impact "(('l \<times> ('f,'v,'t) exp formula) list)" "('f,'v,'t,'l,'n,'tr,'s) art_impl"

definition restrict_invariants :: "('l \<Rightarrow> ('f,'v,'t) exp formula) \<Rightarrow> 'l set \<Rightarrow> ('l \<Rightarrow> ('f,'v,'t) exp formula)" where
  "restrict_invariants I L l = (if l \<in> L then I l else True\<^sub>f)" 

(* we prune the given invariant function to nodes of the LTS, since we cannot check validity everywhere *)  
fun (in pre_art_checker) invariant_proof_checker ::
"('f, 'v, 't, 'l::showl, 'tr::showl) lts_impl \<Rightarrow>
 ('f,'v,'t,'l,'n::showl,'tr,'s :: {default,showl}) invariant_proof \<Rightarrow> showsl + ('l \<Rightarrow> ('f,'v,'t) exp formula)"
 where
 "invariant_proof_checker Pi (Impact II Ai) = debug id (STR ''invariant checking: Impact'') ((let I = map_of_default True\<^sub>f II in check_return (do {
    check_unique_names Ai;
    debug id (STR ''provided invariants against deduced invariants from ART graph'') (check_allm (\<lambda> l. do {
      let Il = I l;
      check (formula Il) (showsl_lit (STR ''ill-formed formula for location '') o showsl l); 
      check (check_trivial_implication (get_disj_invariant (art_of Pi Ai) l) Il)
        (showsl_lit (STR ''could not match provided invariant with invariant extracted from art-graph at location '')
          o showsl l)
      })
      (nodes_lts_impl Pi));
    debug id (STR ''checking ART graph'') (check_art_invariants_impl Ai Pi)
  } <+? (\<lambda> s. showsl_lit (STR ''problem in ensuring invariants for '') o showsl_lts Pi o showsl_lit (STR ''\<newline>via '') o showsl_art Ai o s)) 
  (restrict_invariants I (nodes_lts (lts_of Pi)))))"

lemma (in art_checker) invariant_proof_checker: assumes ok: "invariant_proof_checker Pi prf = return \<Phi>"
  and Pi: "lts_impl Pi" 
  shows "invariants (lts_of Pi) \<Phi>"
proof (cases "prf")
  case (Impact JJ Ai)
  let ?J = "map_of_default True\<^sub>f JJ" 
  note ok = ok[unfolded Impact invariant_proof_checker.simps Let_def, simplified]
  from ok have J: "\<And> l. l \<in> nodes_lts (lts_of Pi) \<Longrightarrow> 
    check_trivial_implication (get_disj_invariant (art_of Pi Ai) l) (?J l)" 
    and J': "\<And> l. l \<in> nodes_lts (lts_of Pi) \<Longrightarrow> formula (?J l)" by auto
  note J = check_trivial_implication[OF J]
  from ok have un: "unique_names Ai" and art: "isOK (check_art_invariants_impl Ai Pi)" by auto
  from check_art_invariants_impl[OF Pi art]
  have inv: "invariants (lts_of Pi) (get_disj_invariant (art_of Pi Ai))" by auto
  note d = invariants_def split
  show ?thesis unfolding d
  proof
    fix l
    show "invariant (lts_of Pi) l (\<Phi> l)"
    proof (cases "l \<in> nodes_lts (lts_of Pi)")
      case True
      then have id: "\<Phi> l = ?J l" using ok by (simp add: restrict_invariants_def nodes_lts_def)
      have imp: "get_disj_invariant (art_of Pi Ai) l \<Longrightarrow>\<^sub>f ..."
        by (rule J[OF True])
      have inv: "invariant (lts_of Pi) l (get_disj_invariant (art_of Pi Ai) l)" using inv[unfolded d o_def] by auto
      show ?thesis
      proof (intro invariantI)
        show "formula (\<Phi> l)" unfolding id using J'[OF True] .
        fix \<alpha>
        assume reach: "State \<alpha> l \<in> reachable_states (lts_of Pi)" 
        from invariantE[OF inv _] reach have "\<alpha> \<Turnstile> get_disj_invariant (art_of Pi Ai) l" by metis
        from impliesD[OF imp _ this] reachable_state[OF reach] 
        show "\<alpha> \<Turnstile> \<Phi> l" unfolding id by auto
      qed
    next
      case False
      then have "\<Phi> l = True\<^sub>f" using ok by (auto simp:restrict_invariants_def)
      then show ?thesis by auto
    qed
  qed 
qed  

declare pre_art_checker.invariant_proof_checker.simps[code]
end
