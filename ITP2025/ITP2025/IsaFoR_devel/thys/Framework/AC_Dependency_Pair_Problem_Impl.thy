(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2016)
License: LGPL (see file COPYING.LESSER)
*)
theory AC_Dependency_Pair_Problem_Impl
imports
  AC_Dependency_Pair_Problem_Spec
  TRS.Rule_Map
  TRS.Q_Restricted_Rewriting_Impl
begin

type_synonym ('f ,'v) ac_dpp_impl =
  "('f, 'v) rules \<times> \<comment> \<open>P\<close>
   ('f, 'v) rules \<times> \<comment> \<open>Pw\<close>   
   ('f, 'v) rules \<times> \<comment> \<open>R\<close>
   ('f, 'v) rules \<times> \<comment> \<open>Rw\<close>
   ('f, 'v) rules \<times> \<comment> \<open>E\<close>
   ('f, 'v, unit) rm \<comment> \<open>rule-map for E u R u Rw\<close>"

fun ac_dpp_impl :: "('f::compare_order, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rel_dpp" where
  "ac_dpp_impl (p, pw, r, rw, e, _) = (set p, set pw, set r, set rw, set e)"

fun P_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "P_impl (p, pw, r, rw, e, _) = p"
fun Pw_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "Pw_impl (p, pw, r, rw, e, _) = pw"
fun pairs_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "pairs_impl (p, pw, r, rw, e, _) = p @ pw"
fun R_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "R_impl (p, pw, r, rw, e, _) = r"
fun Rw_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "Rw_impl (p, pw, r, rw, e, _) = rw"
fun rules_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "rules_impl (p, pw, r, rw, e, _) = r @ rw"
fun E_impl :: "('f, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules" where "E_impl (p, pw, r, rw, e, _) = e"

fun rules_map_impl :: "('f::compare_order, 'v) ac_dpp_impl \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules"
where
  "rules_map_impl (p, pw, r, rw, e, m) fn =
    (case rm.lookup fn m of
      None \<Rightarrow> []
    | Some rs \<Rightarrow> map snd rs)"

definition
  mk_impl ::
    "('f::compare_order, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> 
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp_impl"
where
  "mk_impl p pw r rw e = (p, pw, r, rw, e, insert_rules () (r @ rw @ e) (rm.empty ()))"

fun
  delete_pairs_rules_impl :: "('f :: compare_order, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp_impl"
where
  "delete_pairs_rules_impl (p, pw, r, rw, e, m) pd rd = (if rd = [] then
    (list_diff p pd, list_diff pw pd, r, rw, e, m)
    else mk_impl (list_diff p pd) (list_diff pw pd) (list_diff r rd) (list_diff rw rd) e)"

fun
  intersect_pairs_impl :: "('f :: compare_order, 'v) ac_dpp_impl \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp_impl"
where
  "intersect_pairs_impl (p, pw, r, rw, e, m) pd = (list_inter p pd, list_inter pw pd, r, rw, e, m)"

fun is_ac_dpp :: "('f::compare_order, 'v) ac_dpp_impl \<Rightarrow> bool" where
  "is_ac_dpp (p, pw, r, rw, e, m) \<longleftrightarrow> (
      set (filter (is_Fun \<circ> fst) (r @ rw @ e)) = (set (rules_with (\<lambda> _. True) m))
    \<and> rm_inj m )"

lemma is_ac_dpp_imp_rules_with:
  assumes "is_ac_dpp (p, pw, r, rw, e, m)"
  shows "set (rules_with (\<lambda> _. True) m) = (set (filter (is_Fun \<circ> fst) (r @ rw @ e)))"
  using assms by auto

lemma ac_dpp_impl_sound':
  "ac_dpp_impl d =
    (set (P_impl d), set (Pw_impl d), set (R_impl d), set (Rw_impl d), set (E_impl d))"
  by (cases d) auto

lemma pairs_impl_sound:
  "set (pairs_impl d) = set (P_impl d) \<union> set (Pw_impl d)"
  by (cases d) simp_all

lemma rules_impl_sound:
  "set (rules_impl d) = set (R_impl d) \<union> set (Rw_impl d)"
  by (cases d) auto

lemma mk_impl_sound:
  "ac_dpp_impl (mk_impl p pw r rw e) = (set p, set pw, set r, set rw, set e)"
  by (auto simp: mk_impl_def Let_def)

lemma rules_map_impl_sound:
  assumes "is_ac_dpp d"
  shows "set (rules_map_impl d (f, n)) =
    {r |r. r \<in> set (rules_impl d) \<union> set (E_impl d) \<and> root (fst r) = Some (f, n)}"
    (is "?A = ?B")
proof (cases d)
  case (fields p pw r rw e m)
  note rules_with = is_ac_dpp_imp_rules_with[OF assms[unfolded fields]]
  show ?thesis 
  proof
    show "?A \<subseteq> ?B"
    proof
      fix l r assume 1: "(l, r) \<in> set (rules_map_impl d (f, n))"
      show "(l, r) \<in> ?B"
      proof (cases "rm.lookup (f, n) m")
        case None with 1 show ?thesis by (simp add: fields)
      next
        case (Some rs)
        with 1 have 2: "(l, r) \<in> snd `set rs" by (simp add: fields)
        from assms and Some have "\<forall>r\<in>set rs. key r = Some (f, n)"
          by (simp add: fields rm_inj_def mmap_inj_def rm.correct)
        moreover from 2 obtain a where "(a, l, r) \<in> set rs" by auto
        ultimately have "key (a, l, r) = Some (f, n)" by simp
        then have root: "root l = Some (f, n)"
          by (cases l, simp_all)
        from Some_in_values[OF Some] have "set rs \<subseteq> set (values m)" .
        then have "(l, r) \<in> snd ` set (values m)" using 2 by auto
        then have "(l, r) \<in> set (rules_impl d) \<union> set (E_impl d)" 
          by (auto simp: fields values_rules_with_conv_unit rules_with)
        with root show ?thesis by simp
      qed
    qed
  next
    show "?B \<subseteq> ?A"
    proof
      fix l r assume "(l, r) \<in> ?B"
      then have "(l, r) \<in> set (rules_impl d) \<union> set (E_impl d)"
        and "root l = Some (f, n)" by auto
      then have "(l, r) \<in> set (R_impl d) \<union> set (Rw_impl d) \<union> set (E_impl d)" by (simp add: rules_impl_sound)
      then have 1: "(l, r) \<in> set (rules_impl d) \<union> set (E_impl d)"
        by (auto simp: fields values_rules_with_conv)
      from \<open>root l = Some (f, n)\<close> obtain ts where l: "l = Fun f ts" by (cases l) auto
      have "(l, r) \<in> set (rules m)"
        using 1 l 
        by (auto simp add: fields rules_with; unfold values_rules_with_conv_unit[of m, unfolded rules_with],
          force+)
      then have "((), l, r) \<in> set (values m)" by auto
      from this[unfolded values_ran[unfolded ran_def]]
        obtain k vs where lookup: "rm.lookup k m = Some vs"
        and "((), l, r) \<in> set vs" by (auto simp: rm.correct)
      then have 2: "(l, r) \<in> set (rules_map_impl d k)" unfolding fields by force
      have k: "k = (f, n)"
      proof -
        from \<open>root l = Some (f, n)\<close> have "length ts = n" by (simp add: l)
        from lookup have alpha: "rm.\<alpha> m k = Some vs" by (auto simp: rm.correct)
        from assms[unfolded fields, simplified,
          unfolded rm_inj_def mmap_inj_def]          
          and alpha and \<open>((), l, r) \<in> set vs\<close> have "key ((), l, r) = Some k" 
          by blast
        then show ?thesis by (simp add: \<open>length ts = n\<close> l)
      qed
      from 2 show "(l, r) \<in> ?A" unfolding k .
    qed
  qed
qed

lemma delete_pairs_rules_impl_sound:
  "ac_dpp_impl (delete_pairs_rules_impl d p r) =
    (set (P_impl d) - set p, set (Pw_impl d) - set p, set (R_impl d) - set r, set (Rw_impl d) - set r, set (E_impl d))"
  by (cases d) (simp add: mk_impl_sound)

lemma intersect_pairs_impl_sound:
  "ac_dpp_impl (intersect_pairs_impl d p) =
    (set (P_impl d) \<inter> set p, set (Pw_impl d) \<inter> set p, set (R_impl d), set (Rw_impl d), set (E_impl d))"
  by (cases d) (simp add: mk_impl_sound)


lemmas ac_dpp_impl_sound =
  ac_dpp_impl_sound'
  pairs_impl_sound
  rules_impl_sound
  rules_map_impl_sound
  delete_pairs_rules_impl_sound
  intersect_pairs_impl_sound
  mk_impl_sound

section \<open>Invariant free implementation\<close>

lemma is_ac_dpp_mk_impl[simp]: "is_ac_dpp (mk_impl p pw r rw e)"
  unfolding mk_impl_def by auto

context
  notes [[typedef_overloaded]]
begin
typedef ('f, 'v) ac_dpp = "{d :: ('f::compare_order, 'v) ac_dpp_impl. is_ac_dpp d}"
  morphisms impl_of AC_DPP
  by (rule exI[of _ "mk_impl [] [] [] [] []"], auto)
end

setup_lifting type_definition_ac_dpp 

lift_definition ac_dpp :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) Relative_DP_Framework.rel_dpp" is ac_dpp_impl .

lift_definition P :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is P_impl .

lift_definition Pw :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is Pw_impl .

lift_definition pairs :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is pairs_impl .

lift_definition R :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is R_impl .

lift_definition Rw :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is Rw_impl .

lift_definition E :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is E_impl .

lift_definition rules :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules" is rules_impl . 

lift_definition rules_map :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f, 'v) rules" is rules_map_impl . 

definition reverse_rules_map :: "('f::compare_order,'v) ac_dpp \<Rightarrow> ('f \<times> nat) \<Rightarrow> ('f,'v) rules" where
  "reverse_rules_map d fn = [ (r,l) . (l,r) \<leftarrow> R d @ Rw d @ E d, root r = Some fn]"    

lift_definition mk :: "('f::compare_order, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules
    \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp" is mk_impl
  by simp 
  
lift_definition delete_pairs_rules :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp"
  is delete_pairs_rules_impl
proof -
  fix ac_dpp :: "('f,'v) ac_dpp_impl" and dp dr
  assume "is_ac_dpp ac_dpp"
  then show "is_ac_dpp (delete_pairs_rules_impl ac_dpp dp dr)"
    by (cases ac_dpp, simp)
qed

lift_definition intersect_pairs :: "('f::compare_order, 'v) ac_dpp \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) ac_dpp"
  is intersect_pairs_impl by auto

definition eq_rules_no_left_var :: "('f :: compare_order, 'v) ac_dpp \<Rightarrow> bool" where
  "eq_rules_no_left_var d = (let t = list_all (\<lambda> (l,r). is_Fun l)
    in t (R d) \<and> t (Rw d) \<and> t (E d))"

lemma eq_rules_no_left_var: "eq_rules_no_left_var d = (\<forall>(l, r)\<in>set (R d @ Rw d @ E d). is_Fun l)"
  unfolding eq_rules_no_left_var_def Let_def list_all_iff by auto

definition eq_rules_non_collapsing :: "('f :: compare_order, 'v) ac_dpp \<Rightarrow> bool" where
  "eq_rules_non_collapsing d = (let t = list_all (\<lambda> (l,r). is_Fun r)
    in t (R d) \<and> t (Rw d) \<and> t (E d))"

lemma eq_rules_non_collapsing: "eq_rules_non_collapsing d = (\<forall>(l, r)\<in>set (R d @ Rw d @ E d). is_Fun r)"
  unfolding eq_rules_non_collapsing_def Let_def list_all_iff by auto

lemma ac_dpp_sound': "ac_dpp d = (set (P d), set (Pw d), set (R d), set (Rw d), set (E d))"
  by (transfer, auto)

lemma pairs_sound: "set (pairs d) = set (P d) \<union> set (Pw d)"
  by (transfer, auto)

lemma rules_sound: "set (rules d) = set (R d) \<union> set (Rw d)"
  by (transfer, auto)

lemma rules_map_sound:
  "set (rules_map d (f, n)) =
    {r \<in> set (R d @ Rw d @E d). root (fst r) = Some (f, n)}"
  by (transfer, subst rules_map_impl_sound, auto)

lemma reverse_rules_map_sound: "set (reverse_rules_map d (f, n)) =
  {(snd r, fst r) |r. r \<in> set (R d @ Rw d @ E d) \<and> root (snd r) = Some (f, n)}" (is "?l = ?r")
  unfolding reverse_rules_map_def by auto  

lemma delete_pairs_rules_sound:
  "ac_dpp (delete_pairs_rules d p r) =
    (set (P d) - set p, set (Pw d) - set p, set (R d) - set r, set (Rw d) - set r, set (E d))"
  by (transfer, subst delete_pairs_rules_impl_sound, auto)

lemma intersect_pairs_sound:
  "ac_dpp (intersect_pairs d p) =
    (set (P d) \<inter> set p, set (Pw d) \<inter> set p, set (R d), set (Rw d), set (E d))"
  by (transfer, subst intersect_pairs_impl_sound, auto)

lemma mk_sound:
  "ac_dpp (mk p pw r rw e) = (set p, set pw, set r, set rw, set e)"
  by (transfer, subst mk_impl_sound, auto)

lemmas ac_dpp_sound =
  ac_dpp_sound'
  pairs_sound
  rules_sound
  rules_map_sound
  reverse_rules_map_sound
  delete_pairs_rules_sound
  intersect_pairs_sound
  eq_rules_no_left_var
  eq_rules_non_collapsing
  mk_sound

definition
  ac_dpp_rbt_impl :: "(('f::compare_order, 'v) ac_dpp, 'f, 'v) ac_dpp_ops"
where
  "ac_dpp_rbt_impl \<equiv> \<lparr>
    ac_dpp_ops.ac_dpp = ac_dpp,
    P = P,
    Pw = Pw,
    pairs = pairs,
    R = R,
    Rw = Rw,
    rules = rules,
    E = E,
    mk = mk,
    eq_rules_map = rules_map,
    reverse_eq_rules_map = reverse_rules_map,
    delete_pairs_rules = delete_pairs_rules,
    eq_rules_no_left_var = eq_rules_no_left_var,
    eq_rules_non_collapsing = eq_rules_non_collapsing,
    intersect_pairs = intersect_pairs
    \<rparr>"

lemma ac_dpp_rbt_impl: "ac_dpp_spec ac_dpp_rbt_impl"
 by (standard, simp_all only: ac_dpp_rbt_impl_def ac_dpp_ops.simps,
     (blast intro!: ac_dpp_sound)+)

hide_const (open) P Pw R Rw E mk rules rules_map


end
