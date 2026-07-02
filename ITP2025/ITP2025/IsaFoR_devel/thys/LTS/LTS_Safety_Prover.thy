theory LTS_Safety_Prover
  imports 
    Invariant_Proof_Checkers
begin
  
datatype ('f,'v,'t,'l,'n,'tr,'s) safety_proof =
  Trivial
| Invariant_Assertion "('f,'v,'t,'l,'n,'tr,'s) invariant_proof" "('f,'v,'t,'l,'n,'tr,'s) safety_proof"
  
definition (in pre_logic_checker) safe_by_assertion_checker where
  "safe_by_assertion_checker Pi err = (check_allm (\<lambda> l. check_valid_formula default (\<not>\<^sub>f assertion_of Pi l)
      <+? (\<lambda> s. showsl_lit (STR ''could not deduce from assertion that '') o showsl l o showsl_lit (STR '' is unreachable''))) 
     err)" 

context pre_art_checker
begin
  
fun check_safety_proof :: "('f, 'v, 't, 'l::showl, 'tr::showl) lts_impl \<Rightarrow> 'l list \<Rightarrow>
 ('f,'v,'t,'l,'n::showl,'tr,'s :: {default,showl}) safety_proof \<Rightarrow> showsl check"
where
  "check_safety_proof Pi err safety_proof.Trivial = debug id (STR ''Unsatisfiable Error states'') (safe_by_assertion_checker Pi err)"
| "check_safety_proof Pi err (safety_proof.Invariant_Assertion inv_prf inner) = debug id (STR ''Add Invariants'') (do {
    I \<leftarrow> invariant_proof_checker Pi inv_prf;
    Qi \<leftarrow> fix_invariants Pi I;
    check_safety_proof Qi err inner
  })"

definition check_safety where "check_safety Pi err prf = do {
  debug id (STR ''init - Check well-formedness'') (check_lts_impl Pi);
  check_safety_proof Pi err prf
}"
end

(* lemma safety_via_assertions *)
lemma (in lts) safety_via_assertions: assumes E: "\<And> e. e \<in> E \<Longrightarrow> assertion P e \<Longrightarrow>\<^sub>f False\<^sub>f" 
shows "lts_safe P E" 
  unfolding lts_safe_def
proof (intro allI impI notI)
  fix \<alpha> l
  assume l: "l \<in> E" and reach: "State \<alpha> l \<in> reachable_states P" 
  from reachable_state[OF reach]
  have alpha: "assignment \<alpha>" and sat: "\<alpha> \<Turnstile> assertion P l" by auto
  from impliesD[OF E[OF l] this] show False by simp
qed

context lts_checker
begin
lemma safe_by_assertion_checker: assumes "lts_impl Pi" and "isOK(safe_by_assertion_checker Pi err)" 
  shows "lts_safe (lts_of Pi) (set err)"
proof (rule safety_via_assertions)
  fix e
  assume e: "e \<in> set err" 
  note assms = assms[unfolded safe_by_assertion_checker_def, simplified]
  from assms e have ok: "isOK(check_valid_formula default (\<not>\<^sub>f assertion_of Pi e))" by auto
  from assms(1) have "formula (assertion_of Pi e)" by (rule lts_impl_formula_assertion_of)
  then have "formula (\<not>\<^sub>f assertion_of Pi e)" by simp
  from check_valid_formula[OF ok this]
  show "assertion (lts_of Pi) e \<Longrightarrow>\<^sub>f False\<^sub>f" by (auto simp: valid_Language)
qed
end

context art_checker
begin
lemma check_safety_proof:
  assumes "lts_impl Pi"
  and "isOK(check_safety_proof Pi err prf)"
  shows "lts_safe (lts_of Pi) (set err)"
proof (insert assms, induct "prf" arbitrary: Pi)
  case Trivial
  from safe_by_assertion_checker[OF this(1)] this(2) show ?case by simp
next
  case IH: (Invariant_Assertion invp "prf")
  note ok = IH(3)[simplified]
  from ok obtain I where I: "invariant_proof_checker Pi invp = return I" by auto
  note ok = ok[unfolded I, simplified]
  from ok obtain Qi where Qi: "fix_invariants Pi I = return Qi" by auto
  note ok = ok[unfolded Qi, simplified]
  from IH.hyps[OF _ ok] fix_invariants_safety[OF Qi invariant_proof_checker[OF I IH(2)]] IH(2)
  show ?case by auto
qed

lemma check_safety:
  assumes ok: "isOK(check_safety Pi err prf)" shows "lts_safe (lts_of Pi) (set err)"
  by (rule check_safety_proof, insert ok, auto simp: check_safety_def)
end

declare pre_art_checker.check_safety_proof.simps[code]
declare pre_art_checker.check_safety_def[code]
declare pre_logic_checker.safe_by_assertion_checker_def[code]
  
end  
