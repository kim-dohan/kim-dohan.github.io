theory Litsim_Trs_Impl
  imports 
    Litsim_Trs
    TRS.Trs_Impl_More
begin

definition "check_litsim_trs R R' = do {
  check_variants_trs R R';
  check_variants_trs R' R
} <+? (\<lambda>e. showsl_trs R \<circ> showsl_lit (STR ''\<newline>is not literally similar to '') \<circ> showsl_trs R' \<circ> e)"

lemma check_litsim_trs [dest!]:
  assumes "isOK (check_litsim_trs R R')"
  shows "set R \<doteq> set R'"
  using assms by (auto simp: check_litsim_trs_def subsumable_trs.litsim_def)

end
