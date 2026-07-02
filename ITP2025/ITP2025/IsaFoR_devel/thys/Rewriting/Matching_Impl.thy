(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2014)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Matching_Impl
imports
  "Containers.Map_To_Mapping"
  First_Order_Terms.Matching
begin

lift_definition
  match_term_list_code ::
    "(('f, 'v) term \<times> ('f, 'w) term) list \<Rightarrow>
    ('v, ('f, 'w) term) mapping \<Rightarrow>
    ('v, ('f, 'w) term) mapping option"
is match_term_list .

lemmas [code] = match_term_list.simps [containers_identify]

lemmas match_term_list_code_simps [simp]
  = match_term_list.simps [containers_identify]

lemma Mapping_match_term_list:
  "map_option Mapping (match_term_list P \<sigma>) =
    (match_term_list_code P (Mapping \<sigma>))"
  by (induct P \<sigma> rule: match_term_list.induct)
     (simp_all add: fun_upd_apply [abs_def] Mapping.lookup.abs_eq Mapping.update.abs_eq
               split: option.splits)

lemma match_term_list_conv:
  "match_term_list P \<sigma> = map_option Mapping.lookup (match_term_list_code P (Mapping \<sigma>))"
proof -
  from Mapping_match_term_list [of P \<sigma>]
    have "map_option Mapping.rep (map_option Mapping (match_term_list P \<sigma>)) =
      map_option Mapping.rep (match_term_list_code P (Mapping \<sigma>))" by simp
  then show ?thesis
    unfolding Mapping.lookup.rep_eq [abs_def]
    by (simp add: option.map_comp o_def Mapping_inverse option.map_ident)
qed

text \<open>More efficient code for @{const match_list}.\<close>
lemma [code]:
  "match_list d P =
    map_option (subst_of_map d \<circ> Mapping.lookup) (match_term_list_code P Mapping.empty)"
  by (simp add: match_list_def match_term_list_conv option.map_comp Mapping.empty.abs_eq)

end

