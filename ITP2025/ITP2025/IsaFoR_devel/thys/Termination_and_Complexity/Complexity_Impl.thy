(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Complexity_Impl
  imports 
    Ord.Complexity
    Certification_Monads.Check_Monad
    Show.Shows_Literal
begin

fun check_terms_of_main :: "('f,'v)complexity_measure \<Rightarrow> ('f :: showl,'v)complexity_measure \<Rightarrow> showsl check" where
  "check_terms_of_main (Derivational_Complexity F) (Derivational_Complexity G) = 
    check_subseteq F G <+? (\<lambda> f. showsl_lit (STR ''consider of symbol '') \<circ> showsl f)" 
| "check_terms_of_main (Runtime_Complexity F H) (Derivational_Complexity G) = 
    check_subseteq (F @ H) G <+? (\<lambda> f. showsl_lit (STR ''consider of symbol '') \<circ> showsl f)" 
| "check_terms_of_main (Runtime_Complexity F H) (Runtime_Complexity F1 H1) = 
    check_subseteq F F1 <+? (\<lambda> f. showsl_lit (STR ''consider symbol '') \<circ> showsl f) 
  >> check_subseteq H H1 <+? (\<lambda> f. showsl_lit (STR ''consider symbol '') \<circ> showsl f)" 
| "check_terms_of_main (Derivational_Complexity G) (Runtime_Complexity F1 H1) = 
    error (showsl_lit (STR ''mixing runtime complexity and derivational complexity''))"

definition check_terms_of_nat :: "('f,'v)complexity_measure \<Rightarrow> ('f :: showl,'v)complexity_measure \<Rightarrow> showsl check" where
  "check_terms_of_nat cm1 cm2 = check_terms_of_main cm1 cm2 <+? (\<lambda> e. showsl_lit (STR ''error comparing start terms\<newline>'') \<circ> e)"

lemma check_terms_of_nat: assumes ok: "isOK(check_terms_of_nat cm1 cm2)"
  shows "terms_of_nat cm1 n \<subseteq> terms_of_nat cm2 n"
proof -
  note ok = ok[unfolded check_terms_of_nat_def, simplified]
  show ?thesis
  proof (cases cm1)
    case (Derivational_Complexity F) note cm1 = this
    with ok obtain F1 where cm2: "cm2 = Derivational_Complexity F1" by (cases cm2, auto)
    with cm1 ok have "set F \<subseteq> set F1" by auto
    then show ?thesis unfolding cm1 cm2 by auto
  next
    case (Runtime_Complexity C1 D1) note cm1 = this
    note ok = ok[unfolded this]
    show ?thesis
    proof (cases cm2)
      case (Runtime_Complexity C2 D2)
      with ok show ?thesis unfolding cm1 by auto
    next
      case (Derivational_Complexity F) note cm2 = this
      with ok have "set C1 \<union> set D1 \<subseteq> set F" by auto
      from runtime_subset_derivational[OF this]
      show ?thesis unfolding cm1 cm2 .
    qed
  qed
qed

end
