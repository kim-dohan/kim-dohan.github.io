(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Multimap instance for rewrite rules\<close>

theory Rule_Map
imports
  First_Order_Rewriting.Trs_Impl
  Auxx.Multimap
begin

section \<open>Rule-Map Implementation\<close>

text \<open>A rule map associates function symbols (which are unambiguated by adding their
arity) with all rules defining the symbol annotated by some (possibly empty) additional
information.\<close>
type_synonym ('f, 'v, 'a) rm = "('f \<times> nat, ('a \<times> ('f, 'v) rule) list) rm"

abbreviation rules :: "('f::linorder, 'v, 'a) rm \<Rightarrow> ('f, 'v) rule list" where
  "rules m \<equiv> map snd (values m)"

text \<open>Obtain all rules whose annotation satisfies a given property.\<close>
definition
  rules_with :: "('a \<Rightarrow> bool) \<Rightarrow> ('f::linorder, 'v, 'a) rm \<Rightarrow> ('f, 'v) rule list"
where
  "rules_with p m \<equiv> map snd (filter (p \<circ> fst) (values m))"

text \<open>Rules are indexed according to their root symbol (+ arity).\<close>
fun key :: "'a \<times> ('f, 'v) rule \<Rightarrow> ('f \<times> nat) option" where
  "key (_, Fun f ts, _) = Some (f, length ts)"
| "key (_, Var _, _) = None"

definition
  insert_rules :: "'a \<Rightarrow> ('f::linorder, 'v) rules \<Rightarrow> ('f, 'v, 'a) rm \<Rightarrow> ('f, 'v, 'a) rm"
where
  "insert_rules a rs \<equiv> insert_values key (map (Pair a) rs)"

definition
  delete_rules :: "'a \<Rightarrow> ('f::linorder, 'v) rules \<Rightarrow> ('f, 'v, 'a) rm \<Rightarrow> ('f, 'v, 'a) rm"
where
  "delete_rules a rs \<equiv> delete_values key (map (Pair a) rs)"

definition
  intersect_rules :: "('f::linorder, 'v) rules \<Rightarrow> ('f, 'v, bool) rm \<Rightarrow> ('f, 'v, bool) rm"
where
  "intersect_rules rs \<equiv> intersect_values key (map (Pair True) rs @ map (Pair False) rs)"

lemma set_rules_with:
  "set (rules_with p m) = snd ` {x. x\<in>set (values m) \<and> p (fst x)}"
  unfolding rules_with_def o_def by force

lemma key_Fun_conv: "key arule \<noteq> None \<longleftrightarrow> is_Fun (fst (snd arule))"
proof (cases arule)
  case (fields a l r)
  show ?thesis unfolding fields by (cases l) simp_all
qed

lemma values_insert_rules:
  "set (values (insert_rules a rs m)) =
    Pair a ` set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (values m)"
proof -
  from values_insert_values[of key "map (Pair a) rs" m]
    show ?thesis by (simp add: key_Fun_conv insert_rules_def) force
qed

lemma rules_with_insert_rules_True:
  assumes "p a"
  shows "set (rules_with p (insert_rules a rs m)) =
    set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (rules_with p m)"
  using assms
  by (simp only: rules_with_def set_map values_insert_rules
                 set_filter Collect_Un image_Un image_snd_Pair Collect_nested_conj) simp

lemma rules_with_insert_rules_False:
  assumes "\<not> p a"
  shows "set (rules_with p (insert_rules a rs m)) = set (rules_with p m)"
  using assms by (auto simp: insert_rules_def rules_with_def)

definition rm_inj where "rm_inj m \<equiv> mmap_inj key (rm.\<alpha> m)"

lemma rm_inj_rm_empty[simp]: "rm_inj (rm.empty ())" by (simp add: rm_inj_def)

lemma values_delete_rules:
  assumes "rm_inj m"
  shows "set (values (delete_rules a rs m)) = set (values m) - (Pair a ` set rs)"
  using values_delete_values[OF assms[unfolded rm_inj_def]]
  by (simp add: delete_rules_def)

lemma values_intersect_rules:
  assumes "rm_inj m"
  shows "set (values (intersect_rules rs m)) = set (values m) \<inter> (Pair True ` set rs \<union> Pair False ` set rs)"
  using values_intersect_values[OF assms[unfolded rm_inj_def]]
  by (auto simp: intersect_rules_def)

lemma rm_inj_insert_rules[simp]:
  assumes "rm_inj m" shows "rm_inj (insert_rules a rs m)"
  using mmap_inj_insert_values[OF assms[unfolded rm_inj_def]]
  by (simp add: rm_inj_def insert_rules_def)

lemma rm_inj_delete_rules[simp]:
  assumes "rm_inj m" shows "rm_inj (delete_rules a rs m)"
  using mmap_inj_delete_values[OF assms[unfolded rm_inj_def]]
  by (simp add: rm_inj_def delete_rules_def)

lemma rm_inj_intersect_rules[simp]:
  assumes "rm_inj m" shows "rm_inj (intersect_rules rs m)"
  using mmap_inj_intersect_values[OF assms[unfolded rm_inj_def]]
  by (simp add: rm_inj_def intersect_rules_def)

lemma values_rules_with_conv:
  "set (values m) = Pair True ` set (rules_with id m) \<union> Pair False ` set (rules_with Not m)"
  unfolding rules_with_def by auto force

lemma values_rules_with_conv_unit:
  "set (values m) = Pair () ` set (rules_with (\<lambda> _. True) m)"
  unfolding rules_with_def by auto 

lemma in_values_Var_False:
  assumes "rm_inj m" and "(a, l, r)\<in>set (values m)" and "is_Var l"
  shows "False"
proof -
  from assms[unfolded values_ran]
    obtain vs where "vs \<in> ran (rm.\<alpha> m)" and "(a, l, r) \<in> set vs" by blast
  then obtain f n where "rm.\<alpha> m (f, n) = Some vs"
    unfolding ran_def by force
  with assms[unfolded rm_inj_def mmap_inj_def]
    and \<open>(a, l, r) \<in> set vs\<close> have "key (a, l, r) = Some (f, n)" by simp
  then have "is_Fun l" by (cases l) simp_all
  with assms show False by simp
qed

lemma rules_with_id_insert_rules_True[simp]:
  "set (rules_with id (insert_rules True rs m)) =
    set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (rules_with id m)"
  by (simp add: rules_with_insert_rules_True)

lemma rules_with_id_insert_rules_unit[simp]:
  "set (rules_with (\<lambda> _. True) (insert_rules () rs m)) =
    set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (rules_with (\<lambda> _. True) m)"
  by (simp add: rules_with_insert_rules_True)

lemma rules_with_id_insert_rules_False[simp]:
  "set (rules_with id (insert_rules False rs m)) = set (rules_with id m)"
  by (simp add: rules_with_insert_rules_False)

lemma rules_with_Not_insert_rules_True[simp]:
  "set (rules_with Not (insert_rules True rs m)) = set (rules_with Not m)"
  by (simp add: rules_with_insert_rules_False)

lemma rules_with_Not_insert_rules_False[simp]:
  "set (rules_with Not (insert_rules False rs m)) =
    set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (rules_with Not m)"
  by (simp add: rules_with_insert_rules_True)

lemma rules_with_empty[simp]: "rules_with f (rm.empty ()) = []"
  by (simp add: rules_with_def)

lemma values_delete_rules_subset:
  "rm_inj m \<Longrightarrow> set (values (delete_rules a rs m)) \<subseteq> set (values m)"
  by (auto simp: values_delete_rules[of m a rs])

lemma values_intersect_rules_subset:
  "rm_inj m \<Longrightarrow> set (values (intersect_rules rs m)) \<subseteq> set (values m)"
  by (auto simp: values_intersect_rules[of m rs])

lemma in_values_imp_not_Var[simp]:
  assumes "rm_inj m" and "(a, l, r)\<in>set (values m)" shows "is_Fun l"
  using in_values_Var_False[OF assms] by blast

lemma rules_rules_with_conv:
  "set (rules m) = set (rules_with id m) \<union> set (rules_with Not m)"
  using values_rules_with_conv[of m] by simp

lemma rules_insert_rules[simp]:
  "set (rules (insert_rules a rs m)) = set [r\<leftarrow>rs. is_Fun (fst r)] \<union> set (rules m)"
  by (auto simp add: values_insert_rules)

lemma rules_with_id_delete_rules_True[simp]:
  assumes "rm_inj m"
  shows "set (rules_with id (delete_rules True rs m)) = set (rules_with id m) - set rs"
  using values_delete_rules[OF assms, of True rs]
  unfolding values_rules_with_conv
  by (simp add: image_set_diff[OF inj_Pair1, symmetric])

lemma rules_with_id_delete_rules_False[simp]:
  assumes "rm_inj m"
  shows "set (rules_with id (delete_rules False rs m)) = set (rules_with id m)"
  using values_delete_rules[OF assms, of False rs]
  unfolding values_rules_with_conv
  by (simp add: image_set_diff[OF inj_Pair1, symmetric])

lemma rules_with_Not_delete_rules_False[simp]:
  assumes "rm_inj m"
  shows "set (rules_with Not (delete_rules False rs m)) = set (rules_with Not m) - set rs"
  using values_delete_rules[OF assms, of False rs]
  unfolding values_rules_with_conv
  by (simp add: image_set_diff[OF inj_Pair1, symmetric])

lemma rules_with_Not_delete_rules_True[simp]:
  assumes "rm_inj m"
  shows "set (rules_with Not (delete_rules True rs m)) = set (rules_with Not m)"
  using values_delete_rules[OF assms, of True rs]
  unfolding values_rules_with_conv
  by (simp add: image_set_diff[OF inj_Pair1, symmetric])

lemma pair_true_false[simp]: "Pair True ` x \<inter> Pair False ` y = {}" by auto
lemma pair_false_true[simp]: "Pair False ` x \<inter> Pair True ` y = {}" by auto

lemma rules_with_id_intersect_rules[simp]:
  assumes "rm_inj m"
  shows "set (rules_with id (intersect_rules rs m)) = set (rules_with id m) \<inter> set rs"
  using values_intersect_rules[OF assms, of rs]
  unfolding values_rules_with_conv Int_Un_distrib2 Int_Un_distrib 
    image_Int[OF inj_Pair1, symmetric] 
    by auto

lemma rules_with_Not_intersect_rules[simp]:
  assumes "rm_inj m"
  shows "set (rules_with Not (intersect_rules rs m)) = set (rules_with Not m) \<inter> set rs"
  using values_intersect_rules[OF assms, of rs]
  unfolding values_rules_with_conv Int_Un_distrib2 Int_Un_distrib 
    image_Int[OF inj_Pair1, symmetric] 
    by auto

lemma in_rules_with_id_is_Var_False[simp]:
  "rm_inj m \<Longrightarrow> (l, r) \<in> set (rules_with id m) \<Longrightarrow> is_Var l \<Longrightarrow> False"
  using in_values_Var_False[of m _ l r]
  unfolding values_rules_with_conv
  by auto

lemma in_rules_with_Not_is_Var_False[simp]:
  "rm_inj m \<Longrightarrow> (l, r) \<in> set (rules_with Not m) \<Longrightarrow> is_Var l \<Longrightarrow> False"
  using in_values_Var_False[of m _ l r]
  unfolding values_rules_with_conv
  by auto

end
