theory LTS_Termination_Prover
  imports 
    Initial_Cooperation_Program 
    Invariant_Proof_Checkers 
    Transition_Removal 
    Show_LTS
    Location_Addition 
    Fresh_Variable_Addition 
    Call_Graph_Scc_Decomp
    Invariants_To_Assertions
    Cut_Transition_Split
begin

datatype (dead 'f, dead 'v, dead 't, dead 'l, dead 'tr, dead 's) cooperation_proof =
  Trivial
| Invariants_Update
    "('f,'v,'t,'l sharp,string,'tr,'s) invariant_proof"
    "('f,'v,'t,'l,'tr,'s) cooperation_proof"
 | Location_Addition
    "('f,'v,'t,'l sharp,'tr) location_addition_info"
    "('f,'v,'t,'l,'tr,'s) cooperation_proof"
 | Fresh_Variable_Addition
    "('f, 'v, 't, 'tr) fresh_variable_addition_info"
    "('f,'v,'t,'l,'tr,'s) cooperation_proof"
| Transition_Removal
    "(('f,'v,'t) exp list, 't,'l,'tr,'s) transition_removal_info"
    "('f,'v,'t,'l,'tr,'s) cooperation_proof"
| Scc_Decomp
  "('l sharp scc_repr \<times> ('f,'v,'t,'l,'tr,'s) cooperation_proof)list" 
| Cut_Transition_Split
  "('tr cut_transition_split_repr \<times> ('f,'v,'t,'l,'tr,'s) cooperation_proof)list" 

datatype ('f,'v,'t,'l,'tr,'s) termination_proof =
  Trivial
| Via_Cooperation
   "(('f,'v,'t,'l,'tr) initial_cp_proof \<times> ('f,'v,'t,'l,'tr sharp,'s) cooperation_proof) list"
| Invariants_Update_LTS
    "('f,'v,'t,'l,string,'tr,'s) invariant_proof"
    "('f,'v,'t,'l,'tr,'s) termination_proof"

definition (in showsl_transition) trivial_termination_checker ::
  "('f,'v,'t,'l :: showl sharp,'tr :: showl) lts_impl \<Rightarrow> showsl check" where
  "trivial_termination_checker P = check (filter is_sharp_transition (map snd (transitions_impl P)) = []) 
     (showsl_lit (STR ''there are remaining sharp transitions in '') o showsl_lts P)"

declare showsl_transition.trivial_termination_checker_def[code]

locale pre_termination_checker =
  pre_art_checker where type_fixer = type_fixer +
  transition_removal: pre_transition_removal_bounded
    where type_fixer = "TYPE(_)"
      and logic_checker = tc2
      and showsl_atom = sa2
      and normalize_lit = ne2 
      and normalized_lit = ned2 + 
  pre_transition_definability_checker
    where type_fixer = "TYPE(_)"
  for type_fixer :: "('f:: showl \<times> 'v:: showl \<times> 't:: showl \<times> 'd \<times> 's::{default,showl}) itself"

locale termination_checker =
  pre_termination_checker where type_fixer = type_fixer +
  art_checker where type_fixer = type_fixer +
  transition_removal: transition_removal_bounded
    where type_fixer = "TYPE(_)"
      and logic_checker = tc2
      and showsl_atom = sa2
      and normalize_lit = ne2 
      and normalized_lit = ned2 + 
  transition_definability_checker
    where type_fixer = "TYPE(_)"
  for type_fixer :: "('f:: showl \<times> 'v:: showl \<times> 't:: showl \<times> 'd \<times> 's::{default,showl}) itself"

context pre_termination_checker
begin

lemma trivial_termination_checker:
  assumes "isOK(trivial_termination_checker P)"
  shows "cooperation_SN (lts_of P)"
proof -
  define freeze where "freeze = transition_step_lts (lts_of P)"
  interpret indexed_rewriting "freeze" .  
  define tau where  "tau = transitions_impl P" 
  from assms[unfolded trivial_termination_checker_def, simplified]
  have "filter is_sharp_transition (map snd (transitions_impl P)) = []" by auto 
  from arg_cong[OF this, of set]
  have empty: "sharp_transitions_of (lts_of P) = {}" by (auto simp: tau_def[symmetric])
  show ?thesis unfolding empty by (fold freeze_def, auto)
qed

function check_cooperation_proof :: "showsl \<Rightarrow> _ \<Rightarrow> ('f,'v,'t,'l::{compare_order,showl},'tr::showl,'s) cooperation_proof \<Rightarrow> _"
where
  "check_cooperation_proof i CPi cooperation_proof.Trivial = debug i (STR ''Trivial CP'') (
    trivial_termination_checker CPi
      <+? (\<lambda> s. i o showsl_lit (STR '': error in trivial cooperation termination checker\<newline>'') o s))"
| "check_cooperation_proof i CPi (Invariants_Update iproof cproof) = debug i (STR ''Invariants_Update'') (
    do {
      I \<leftarrow> invariant_proof_checker CPi iproof
        <+? (\<lambda> s. i o showsl_lit (STR '': error in invariant update\<newline>'') o showsl_cooperation_program CPi o s);
      Q \<leftarrow> fix_invariants CPi I;
      check_cooperation_proof (add_index i 1) Q cproof
        <+? (\<lambda> s. i o showsl_lit (STR '': error below invariant update\<newline>'') o s)
      })"
| "check_cooperation_proof i CPi (Transition_Removal info iproof) = debug i (STR ''Transition Removal'') (
   do {
    CPi' \<leftarrow> transition_removal.lex_processor info CPi
      <+? (\<lambda> s. i o showsl_lit (STR '': error in transition removal\<newline>'') o showsl_cooperation_program CPi o s);
    check_cooperation_proof (add_index i 1) CPi' iproof
      <+? (\<lambda> s. i o showsl_lit (STR '': error below transition removal\<newline>'') o s)
   })" 
| "check_cooperation_proof i CPi (Location_Addition info iproof) = debug i (STR ''Location Addition'') (
   do {
    Q \<leftarrow> location_addition CPi info <+? (\<lambda> s. i o showsl (STR '': error in location addition\<newline>'') o showsl_cooperation_program CPi o s);
    check_cooperation_proof (add_index i 1) Q iproof <+? (\<lambda> s. i o showsl (STR '': error below location addition\<newline>'') o s)
   })" 
| "check_cooperation_proof i CPi (Fresh_Variable_Addition info iproof) = debug i (STR ''Fresh Variable Addition'') (
   do {
    Q \<leftarrow> fresh_variable_addition CPi info
      <+? (\<lambda> s. i o showsl_lit (STR '': error in fresh variable addition\<newline>'') o showsl_cooperation_program CPi o s);
    check_cooperation_proof (add_index i 1) Q iproof
      <+? (\<lambda> s. i o showsl_lit (STR '': error below fresh variable addition\<newline>'') o s)
   })" 
| "check_cooperation_proof i CPi (Scc_Decomp scc_proofs) = debug i (STR ''SCC Decomp'') (
   do {
    sccs \<leftarrow> scc_decomposition CPi (map fst scc_proofs)
      <+? (\<lambda> s. i o showsl_lit (STR '': error in Scc decomposition\<newline>'') o showsl_cooperation_program CPi o s);
    check_allm_index (\<lambda> (scc, prof) j. 
      check_cooperation_proof (add_index i (Suc j)) scc prof
        <+? (\<lambda> s. i o showsl_lit (STR '': error below Scc decomposition\<newline>'') o s))
     (zip sccs (map snd scc_proofs))
   })" 
| "check_cooperation_proof i CPi (Cut_Transition_Split scc_proofs) = debug i (STR ''Cut Transition Split'') (
   do {
    sccs \<leftarrow> cut_transition_split (Cut_Transition_Split_Info (map fst scc_proofs)) CPi
      <+? (\<lambda> s. i o showsl_lit (STR '': error in cut-transition split\<newline>'') o showsl_cooperation_program CPi o s);
    check_allm_index (\<lambda> (scc, prof) j. 
      check_cooperation_proof (add_index i (Suc j)) scc prof
        <+? (\<lambda> s. i o showsl_lit (STR '': error below cut-transition split\<newline>'') o s))
      (zip sccs (map snd scc_proofs))
   })" by pat_completeness auto

termination proof (relation "measure (\<lambda> (i, C, prof). size prof)", goal_cases)
  case (6 i P scc_proofs sccs scc_prof e scc prof)
  then have "(scc, prof) \<in> set (zip sccs (map snd scc_proofs))" by auto
  from in_set_zipE[OF this] have "prof \<in> snd ` set scc_proofs" by auto
  then have "size prof \<le> size_list (size_prod (size_list size) size) scc_proofs"
    by (induct scc_proofs, force+)
  then show ?case by simp
next
  case (7 i P scc_proofs sccs scc_prof e scc prof)
  then have "(scc, prof) \<in> set (zip sccs (map snd scc_proofs))" by auto
  from in_set_zipE[OF this] have "prof \<in> snd ` set scc_proofs" by auto
  then have "size prof \<le> size_list (size_prod length size) scc_proofs"
    by (induct scc_proofs, force+)
  then show ?case by simp
qed auto


fun check_termination_proof :: "showsl \<Rightarrow> _" where
  "check_termination_proof i Pi termination_proof.Trivial = debug i (STR ''Trivial Termination'') (
    check (transitions_impl Pi = []) (showsl_lit (STR ''transition rules remains at trivial termination proof''))
      <+? (\<lambda> s. i o showsl_lit (STR '': error in trivial termination checker\<newline>'') o s))"
| "check_termination_proof i Pi (Invariants_Update_LTS iproof cproof) = debug i (STR ''Invariant Update'') (
    do {
      I \<leftarrow> invariant_proof_checker Pi iproof <+? (\<lambda> s. i o showsl_lit (STR '': error in invariant update\<newline>'') o s);
      Q \<leftarrow> fix_invariants Pi I;
      check_termination_proof (add_index i 1) Q cproof <+? (\<lambda> s. i o showsl_lit (STR '': error below invariant update\<newline>'') o s)
      })"
| "check_termination_proof i Pi (termination_proof.Via_Cooperation cp_proofs) = debug i (STR ''Switch to Cooperation Program'') (
    do {
      CPi \<leftarrow> create_initial_cp_prog Pi (map fst cp_proofs)
         <+? (\<lambda> s. i o showsl_lit (STR '': error in creating initial cooperation program\<newline>'') o s);
      check_allm_index (\<lambda> (R, prf) n. check_cooperation_proof (add_index i n) R prf
         <+? (\<lambda> s. i o showsl_lit (STR '': error below switching to initial cooperation program\<newline>'') o s))
             (zip CPi (map snd cp_proofs)) })"

definition check where
  "check Pi prf \<equiv> do {
     debug id (STR ''init - Check well-formedness'') (check_lts_impl Pi <+? (\<lambda> s. showsl_lit (STR ''input LTS is not well-formed'') o s));
     check_termination_proof id Pi prf
   }"

end

declare pre_termination_checker.check_cooperation_proof.simps[code]
declare pre_termination_checker.check_termination_proof.simps[code]
declare pre_termination_checker.check_def[code]


context termination_checker
begin
lemma check_cooperation_proof: "isOK(check_cooperation_proof i P prf) \<Longrightarrow> cooperation_SN_impl P" 
proof (induct "prf" arbitrary: P i)
  case Trivial note * = this
  from * have "isOK(trivial_termination_checker P)" by auto
  from trivial_termination_checker[OF this] show ?case by auto
next
  case *: (Invariants_Update Iprf "prf" P pre)
  show ?case
  proof
    assume P: "lts_impl P"
    from * obtain I where I: "invariant_proof_checker P Iprf = return I" by auto
    from * I obtain Q where Q: "fix_invariants P I = return Q" by auto
    from * I Q obtain i where "isOK(check_cooperation_proof i Q prf)" by auto
    from *(1)[OF this] have IH: "cooperation_SN_impl Q" .
    from invariant_proof_checker[OF I P] have inv: "invariants (lts_of P) I" by auto
    from fix_invariants_cooperation_SN[OF Q inv IH] P
    show "cooperation_SN (lts_of P)" by auto
  qed
next
  case *: (Transition_Removal info prof P)
  from * obtain Q where proc: "transition_removal.lex_processor info P = return Q" by auto
  with * obtain i where rec: "isOK (check_cooperation_proof i Q prof)" by auto
  from *(1)[OF this] have IH: "cooperation_SN_impl Q" .
  with transition_removal.lex_sound[OF proc]
  show ?case.
next
  case *: (Location_Addition info prof P)
  from * obtain Q where proc: "location_addition P info = return Q" by auto
  with * obtain i where rec: "isOK(check_cooperation_proof i Q prof)" by auto
  from *(1)[OF this] have IH: "cooperation_SN_impl Q" .
  from location_addition[OF IH proc]
  show ?case . 
next
  case *: (Fresh_Variable_Addition info prof P)
  from * obtain Q where proc: "fresh_variable_addition P info = return Q" by auto
  with * obtain i where rec: "isOK(check_cooperation_proof i Q prof)" by auto
  from *(1)[OF this] have IH: "cooperation_SN_impl Q" .
  from check_fresh_variable_addition[OF proc IH]
  show ?case . 
next
  case *: (Cut_Transition_Split scc_proofs P pre)
  from * obtain CPs where proc: "cut_transition_split (Cut_Transition_Split_Info (map fst scc_proofs)) P = return CPs" by auto
  show ?case
  proof (rule cut_transition_split[OF _ proc])
    fix C
    assume "C \<in> set CPs"
    then obtain i where i: "i < length CPs" and C: "C = CPs ! i" unfolding set_conv_nth by auto
    from length_cut_transition_split[OF proc] i have i': "i < length scc_proofs" by auto
    from *(2)[unfolded check_cooperation_proof.simps proc, simplified, rule_format, of i] C i i'
    obtain j where ok: "isOK (check_cooperation_proof j C (snd (scc_proofs ! i)))" by auto
    show "cooperation_SN_impl C" 
      by (rule *(1)[OF _ _ ok, of "scc_proofs ! i"], insert i', auto simp: set_conv_nth prod_set_defs)
  qed
next
  case *: (Scc_Decomp scc_proofs P pre)
  from * obtain CPs where proc: "scc_decomposition P (map fst scc_proofs) = return CPs" by auto
  show ?case
  proof (rule scc_decomposition[OF _ proc])
    fix C
    assume "C \<in> set CPs" 
    then obtain i where i: "i < length CPs" and C: "C = CPs ! i" unfolding set_conv_nth by auto
    from length_scc_decomposition[OF proc] i have i': "i < length scc_proofs" by auto
    from *(2)[unfolded check_cooperation_proof.simps proc, simplified, rule_format, of i] C i i'
    have ok: "isOK (check_cooperation_proof (add_index pre (Suc i)) C (snd (scc_proofs ! i)))" by auto
    show "cooperation_SN_impl C" 
      by (rule *(1)[OF _ _ ok, of "scc_proofs ! i"], insert i', auto simp: set_conv_nth prod_set_defs)
  qed
qed

lemma check_termination_proof: "lts_impl P \<Longrightarrow> isOK(check_termination_proof i P prf) \<Longrightarrow> lts_termination (lts_of P)" 
proof (induct "prf" arbitrary: P i)
  case *: Trivial
  from * have empty: "transition (lts_of P) = {}" unfolding transition_def by auto
  show ?case unfolding empty by auto
next
  case *: (Via_Cooperation cp_proofs P pre)
  from * obtain CPs where init: "create_initial_cp_prog P (map fst cp_proofs) = return CPs" by auto
  then have [simp]: "length cp_proofs = length CPs" unfolding create_initial_cp_prog_def Let_def by auto
  show ?case
  proof (rule create_initial_cp_prog[OF init _ *(1)])
    fix CP
    assume "CP \<in> set CPs"
    from this[unfolded set_conv_nth] obtain i where CP: "CP = CPs ! i" and i: "i < length CPs" by auto
    from *(2)[unfolded check_termination_proof.simps init, 
        simplified, rule_format, OF i, folded CP]
    obtain i prof where ok: "isOK (check_cooperation_proof i CP prof)" by blast
    show "cooperation_SN_impl CP" by (rule check_cooperation_proof[OF ok])
  qed
next
  case *: (Invariants_Update_LTS Iprf "prf" P pre)
  note P = *(2)
  from * obtain I where I: "invariant_proof_checker P Iprf = return I" by auto
  from * I obtain Q where Q: "fix_invariants P I = return Q" by auto
  from * I Q obtain i where "isOK(check_termination_proof i Q prf)" by auto
  from *(1)[OF _ this] have IH: "lts_impl Q \<Longrightarrow> lts_termination (lts_of Q)" .
  from invariant_proof_checker[OF I P] have inv: "invariants (lts_of P) I" by auto
  from fix_invariants_lts[OF Q inv IH] P
  show "lts_termination (lts_of P)" by auto
qed

theorem sound: "isOK (check Pi prf) \<Longrightarrow> lts_termination (lts_of Pi)"
  using check_termination_proof[of Pi _ "prf"]
  unfolding check_def by auto

end
end
