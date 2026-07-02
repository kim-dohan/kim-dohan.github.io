theory Tree_Automata_Containment_Impl
  imports
  Tree_Automata_Containment
  Tree_Automata_Autoref_Setup
  Tree_Automata_Det_Impl
begin

notation fun_rel_syn (infixr "\<rightarrow>" 60)

text \<open>Auxiliaries\<close>

fun order_of_comp_res where
  "order_of_comp_res EQUAL = Eq"
| "order_of_comp_res LESS = Lt"
| "order_of_comp_res GREATER = Gt"

lemma order_of_comp_res_cancel [simp]:
  "order_of_comp_res x = Eq \<longleftrightarrow> x = EQUAL" "Eq = order_of_comp_res x \<longleftrightarrow> x = EQUAL"
  "order_of_comp_res x = Lt \<longleftrightarrow> x = LESS" "Lt = order_of_comp_res x \<longleftrightarrow> x = LESS"
  "order_of_comp_res x = Gt \<longleftrightarrow> x = GREATER" "Gt = order_of_comp_res x \<longleftrightarrow> x = GREATER"
  by (cases x; simp)+

lemma ta_rule_autoref'[autoref_rules, param]:
  "(r_root, r_root) \<in> \<langle>F, Q\<rangle>ta_rule_rel \<rightarrow> F"
  by (auto simp: ta_rule_rel_def)

definition "univ_order a b = order_of_comp_res (univ_cmp a b)"

lemma comparator_univ_order:
  "comparator univ_order"
proof -
  interpret eq_linorder_on UNIV univ_cmp by (rule univ_eq_linorder)
  show ?thesis
    apply (unfold_locales)
    subgoal for x y
      by (cases "univ_order x y"; simp only: invert_order.simps) (auto simp: univ_order_def lt_eq)
    by (auto simp: univ_order_def intro: trans(1))
qed

lemma set_rel_mono [relator_props]:
  assumes "R' \<subseteq> R"
  shows "\<langle>R'\<rangle>set_rel \<subseteq> \<langle>R\<rangle>set_rel"
  using subsetD[OF assms]
  by (auto simp: set_rel_def) blast+

text \<open>autoref setup for xoption\<close>

definition xoption_rel_def_internal:
  "xoption_rel R = {(XNone, XNone)} \<union> {(XSome x', XSome x) |x' x. (x', x) \<in> R}"

lemma xoption_rel_def [refine_rel_defs]:
  "\<langle>R\<rangle>xoption_rel = {(XNone, XNone)} \<union> {(XSome x', XSome x) |x' x. (x', x) \<in> R}"
  by (simp add: xoption_rel_def_internal relAPP_def)

consts i_xoption :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of xoption_rel i_xoption]

lemma xoption_rel_sv [relator_props]:
  assumes "single_valued R"
  shows "single_valued (\<langle>R\<rangle>xoption_rel)"
  using assms by (auto simp: xoption_rel_def single_valued_def)

lemma xoption_rel_id [relator_props]:
  assumes "R = Id"
  shows "\<langle>R\<rangle>xoption_rel = Id"
  using assms xoption.exhaust by (auto simp: xoption_rel_def)

lemma xoption_rel_id_simp [simp]:
  shows "\<langle>Id\<rangle>xoption_rel = Id" by tagged_solver

lemma xoption_rel_mono [relator_props]:
  assumes "R' \<subseteq> R"
  shows "\<langle>R'\<rangle>xoption_rel \<subseteq> \<langle>R\<rangle>xoption_rel"
  using assms by (auto simp: xoption_rel_def)

(*
lemma xoption_rel_range [relator_props]:
  assumes "Range R = UNIV"
  shows "Range (\<langle>R\<rangle>xoption_rel) = UNIV"
  using assms xoption.exhaust
  apply (auto simp: xoption_rel_def)
  sorr y
*)

lemma xoption_relI:
  "(XNone, XNone) \<in> \<langle>R\<rangle>xoption_rel"
  "(a, a') \<in> R \<Longrightarrow> (XSome a, XSome a') \<in> \<langle>R\<rangle>xoption_rel"
  by (auto simp: xoption_rel_def)

lemma xoption_relE:
  assumes "(x,x') \<in> \<langle>R\<rangle>xoption_rel"
  obtains "x = XNone" and "x' = XNone"
  | a a' where "x = XSome a" and "x' = XSome a'" and "(a, a')\<in>R"
  using assms by (auto simp: xoption_rel_def)

lemma xoption_rel_simp [simp]:
  "(XNone, a) \<in> \<langle>R\<rangle>xoption_rel \<longleftrightarrow> a = XNone"
  "(c, XNone) \<in> \<langle>R\<rangle>xoption_rel \<longleftrightarrow> c = XNone"
  "(XSome x, XSome y) \<in> \<langle>R\<rangle>xoption_rel \<longleftrightarrow> (x, y) \<in> R"
  by (auto intro: xoption_relI elim: xoption_relE)

lemma xoption_autoref [autoref_rules, param]:
  "(XNone, XNone) \<in> \<langle>R\<rangle>xoption_rel"
  "(XSome, XSome) \<in> R \<rightarrow> \<langle>R\<rangle>xoption_rel"
  "(case_xoption, case_xoption) \<in> R \<rightarrow> (R' \<rightarrow> R) \<rightarrow> \<langle>R'\<rangle>xoption_rel \<rightarrow> R"
  "(map_xoption, map_xoption) \<in> (A \<rightarrow> B) \<rightarrow> \<langle>A\<rangle>xoption_rel \<rightarrow> \<langle>B\<rangle>xoption_rel"
  by (auto simp: xoption_rel_def fun_rel_def)

subsection \<open>autoref setup of @{type status}}\<close>

definition status_rel_def_internal:
  "status_rel Rf Rq = {(Done t', Done t) |t' t. (t', t) \<in> \<langle>\<langle>Rf, Rq\<rangle>term_rel\<rangle>xoption_rel} \<union> {(Changed, Changed)} \<union> {(Unchanged, Unchanged)}"

lemma status_rel_def [refine_rel_defs]:
  "\<langle>Rf, Rq\<rangle>status_rel = {(Done t', Done t) |t' t. (t', t) \<in> \<langle>\<langle>Rf, Rq\<rangle>term_rel\<rangle>xoption_rel} \<union> {(Changed, Changed)} \<union> {(Unchanged, Unchanged)}"
  by (simp add: status_rel_def_internal relAPP_def)

consts i_status :: "interface \<Rightarrow> interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of status_rel i_status]

lemma status_rel_sv [relator_props]:
  assumes "single_valued Rf" "single_valued Rq"
  shows "single_valued (\<langle>Rf, Rq\<rangle>status_rel)"
  using xoption_rel_sv[OF term_rel_sv[OF assms]]
  by (auto simp: single_valued_def status_rel_def)

lemma status_rel_id [relator_props]:
  assumes "Rf = Id" "Rq = Id"
  shows "\<langle>Rf, Rq\<rangle>status_rel = Id"
  using xoption_rel_id[OF term_rel_id[OF assms]] status.exhaust
  by (auto simp: status_rel_def)

lemma term_rel_id_simp [simp]:
  shows "\<langle>Id, Id\<rangle>status_rel = Id" by tagged_solver

lemma status_rel_mono [relator_props]:
  assumes "Rf' \<subseteq> Rf" "Rq' \<subseteq> Rq"
  shows "\<langle>Rf', Rq'\<rangle>status_rel \<subseteq> \<langle>Rf, Rq\<rangle>status_rel"
  using xoption_rel_mono[OF term_rel_mono[OF assms]]
  by (auto simp: status_rel_def)

(*
lemma status_rel_range [relator_props]:
  assumes "Range Rf = UNIV" "Range Rq = UNIV"
  shows "Range (\<langle>Rf, Rq\<rangle>status_rel) = UNIV"
  using xoption_rel_range[OF term_rel_range[OF assms]]
  apply (auto simp: status_rel_def)
  sorr y
*)

lemma status_autoref [autoref_rules, param]:
  "(Done, Done) \<in> \<langle>\<langle>Rf, Rq\<rangle>term_rel\<rangle>xoption_rel \<rightarrow> \<langle>Rf, Rq\<rangle>status_rel"
  "(Changed, Changed) \<in> \<langle>Rf, Rq\<rangle>status_rel"
  "(Unchanged, Unchanged) \<in> \<langle>Rf, Rq\<rangle>status_rel"
  by (auto simp: status_rel_def)

lemma status_result_autoref [autoref_rules, param]:
  "(status_result, status_result) \<in> \<langle>Rf, Rq\<rangle>status_rel \<rightarrow> \<langle>\<langle>Rf, Rq\<rangle>term_rel\<rangle>xoption_rel"
  by (auto simp: status_rel_def)

lemma case_status_autoref [autoref_rules, param]:
  "(case_status, case_status) \<in> (\<langle>\<langle>Rf, Rq\<rangle>term_rel\<rangle>xoption_rel \<rightarrow> R) \<rightarrow> R \<rightarrow> R \<rightarrow> \<langle>Rf, Rq\<rangle>status_rel \<rightarrow> R"
  by (auto simp: status_rel_def fun_rel_def)

text \<open>autoref setup for @{type entry}\<close>

definition entry_rel_def_internal:
  "entry_rel R = {((A,A'), entry (B,B')) |A A' B B'. (A, B) \<in> \<langle>R\<rangle>comp_rs_rel \<and> (A', B') \<in> \<langle>R\<rangle>comp_rs_rel}"

lemma entry_rel_def [refine_rel_defs]:
  "\<langle>R\<rangle>entry_rel = {((A,A'), entry (B,B')) |A A' B B'. (A, B) \<in> \<langle>R\<rangle>comp_rs_rel \<and> (A', B') \<in> \<langle>R\<rangle>comp_rs_rel}"
  by (simp add: entry_rel_def_internal relAPP_def)

consts i_entry :: "interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of entry_rel i_entry]

(*
lemma entry_rel_mono [relator_props]:
  assumes "R' \<subseteq> R"
  shows "\<langle>R'\<rangle>entry_rel \<subseteq> \<langle>R\<rangle>entry_rel"
*)

lemma entry_autoref [autoref_rules, param]:
  "(id, entry) \<in> \<langle>R\<rangle>comp_rs_rel \<times>\<^sub>r \<langle>R\<rangle>comp_rs_rel \<rightarrow> \<langle>R\<rangle>entry_rel"
  by (auto simp: entry_rel_def)

lemma from_entry_autoref [autoref_rules, param]:
  "(id, from_entry) \<in> \<langle>R\<rangle>entry_rel \<rightarrow> \<langle>R\<rangle>comp_rs_rel \<times>\<^sub>r \<langle>R\<rangle>comp_rs_rel"
  by (auto simp: entry_rel_def)

lemma case_entry_autoref [autoref_rules, param]:
  "(id, case_entry) \<in> (\<langle>R\<rangle>comp_rs_rel \<times>\<^sub>r \<langle>R\<rangle>comp_rs_rel \<rightarrow> R') \<rightarrow> \<langle>R\<rangle>entry_rel \<rightarrow> R'"
  by (auto simp: entry_rel_def fun_rel_def prod_rel_def)

text \<open>comparing entries: we need a total order that, on finite sets, agrees with comparing
  the corresponding sorted, distinct lists. Fortunately, there is already a universal order,
  @{term univ_order}.\<close>

instantiation entry :: (compare_order)compare
begin

fun compare_entry where
  "compare_entry (entry (A :: (_ :: compare_order) set, A')) (entry (B, B')) =
  (if finite A \<and> finite A' \<and> finite B \<and> finite B' then compare (sorted_list_of_set A, sorted_list_of_set A') (sorted_list_of_set B, sorted_list_of_set B') else
   if finite A \<and> finite A' then Lt else
   if finite B \<and> finite B' then Gt else univ_order (A, A') (B, B'))"

interpretation uord:
  comparator "univ_order :: (_ :: compare_order) set \<times> _ \<Rightarrow> _" by (rule comparator_univ_order)

instance
  apply (standard, unfold_locales)
  subgoal for x y
    by (cases "(x, y)" rule: compare_entry.cases)
      (auto intro!: Comparator.comparator.sym[OF comparator_compare] uord.sym)
  subgoal for x y
    by (cases "(x, y)" rule: compare_entry.cases)
      (auto simp: sorted_list_of_set_inj_aux dest!: Comparator.comparator.weak_eq[OF comparator_compare] uord.weak_eq split: if_splits)
  subgoal for x y z
    by (cases "(x, y)" rule: compare_entry.cases; cases "(y, z)" rule: compare_entry.cases)
      (auto dest: Comparator.comparator.comp_trans[OF comparator_compare] uord.comp_trans split: if_splits)
  done
end

instantiation entry :: (compare_order)compare_order
begin

definition "less_eq_entry = le_of_comp (compare :: _ entry \<Rightarrow> _)"
definition "less_entry = lt_of_comp (compare :: _ entry \<Rightarrow> _)"

instance
  by (standard) (auto simp: less_eq_entry_def less_entry_def)

end

fun key_of_entry' where
  "key_of_entry' (A, A') = (RBT_Impl.keys A, RBT_Impl.keys A')"

lemma [autoref_rules]:
  "(\<lambda>A B. key_of_entry' A < key_of_entry' B, (<)) \<in> \<langle>Id\<rangle>entry_rel \<rightarrow> \<langle>Id\<rangle>entry_rel \<rightarrow> bool_rel"
  oops

lemma comp_res_of_order_cancel [simp]:
  "comp_res_of_order x = EQUAL \<longleftrightarrow> x = Eq"
  "comp_res_of_order x = LESS \<longleftrightarrow> x = Lt"
  "comp_res_of_order x = GREATER \<longleftrightarrow> x = Gt"
  by (cases x; simp)+

lemma comp_res_rel_unfold:
  "comp_res_rel = {(LESS, LESS), (EQUAL, EQUAL), (GREATER, GREATER)}"
  using comp_res.exhaust by auto

(*
lemma entry_rel_imp_finite [simp]:
  "((A, A'), entry (B, B')) \<in> \<langle>Id\<rangle>entry_rel \<Longrightarrow> finite B"
  "((A, A'), entry (B, B')) \<in> \<langle>Id\<rangle>entry_rel \<Longrightarrow> finite B'"
  by (auto simp: entry_rel_def)

lemma entry_rel_imp_sorted [simp]:
  "((A, A'), entry (B, B' :: (_ :: compare_order) set)) \<in> \<langle>Id\<rangle>entry_rel \<Longrightarrow> is_rbt A"
  "((A, A'), entry (B, B')) \<in> \<langle>Id\<rangle>entry_rel \<Longrightarrow> is_rbt A'"
  by (auto simp: entry_rel_def map2set_rel_def rbt_map_rel_def rbt_map_rel'_def br_def ord.is_rbt_rbt_sorted)
*)

lemma rbt_lookup_into_class: "ord.rbt_lookup (<) = RBT_Impl.rbt_lookup"
  by (simp add: ord.rbt_lookup_def RBT_Impl.rbt_lookup_def)

lemma rbt_sorted_into_class: "ord.rbt_sorted (<) = rbt_sorted"
  by (simp add: ord.rbt_sorted_def rbt_sorted_def rbt_less_prop ord.rbt_less_prop rbt_greater_prop
    ord.rbt_greater_prop)

lemma sorted_list_of_set_from_comp_rs_rel:
  assumes "(A, B :: ('a :: compare_order) set) \<in> \<langle>Id\<rangle>comp_rs_rel"
  shows "RBT_Impl.keys A = sorted_list_of_set B"
  using assms sorted_list_of_set.idem_if_sorted_distinct[of "map fst (RBT_Impl.entries A)"] linorder_class.distinct_entries[of A]
  by (auto simp: map2set_rel_def rbt_map_rel_def rbt_map_rel'_def RBT_Impl.keys_def rbt_sorted_entries br_def rbt_lookup_keys
    distinct_entries lt_of_comp_post_simp ord_defs rbt_lookup_into_class intro!: sorted_list_of_set.idem_if_sorted_distinct is_rbt_rbt_sorted)

lemma [autoref_rules]:
  "(\<lambda>A B. compare_res (key_of_entry' A) (key_of_entry' B), compare_res) \<in> \<langle>Id\<rangle>entry_rel \<rightarrow> \<langle>Id\<rangle>entry_rel \<rightarrow> comp_res_rel"
  apply (intro fun_relI)
  subgoal for a a' b b'
    by (cases a; cases b; cases a'; cases b'; cases "compare_res a' b'")
      (auto simp: compare_res_def sorted_list_of_set_from_comp_rs_rel entry_rel_def)
  done

abbreviation (input)
  "state_rel \<equiv> \<langle>\<langle>Id\<rangle>entry_rel, \<langle>Id,Id\<rangle>term_rel\<rangle>comp_rm_rel"

lemma [autoref_rules]:
  "(RBT_Impl.map (\<lambda>_ _. ()), dom) \<in> \<langle>Rk :: (_ \<times> _ :: compare_order) set, Rv\<rangle>comp_rm_rel \<rightarrow> \<langle>Rk\<rangle>comp_rs_rel"
proof -
  have *: "(RBT_Impl.map (\<lambda>_ _. ()) x, RBT_Impl.map (\<lambda>_ _. ()) y) \<in> \<langle>Rk, unit_rel\<rangle>rbt_rel"
    if "(x, y) \<in> \<langle>Rk, Rv\<rangle>rbt_rel" for x y using that
    by (induct x arbitrary: y) (auto intro!: rbt_rel_intros elim!: rbt_rel_elims)
  have x: "class.linorder (comp2le (compare_res :: _ :: compare_order \<Rightarrow> _)) (comp2lt compare_res)"
    unfolding eq_linorder_class_conv[symmetric] by (rule compare_to_eq_linorder)
  show ?thesis
    unfolding map2set_rel_def rbt_map_rel_def O_assoc
    apply (intro fun_relI, elim relcompE)
    subgoal for _ _ x y z
    unfolding prod.inject
    apply (simp only: )
    apply (rule relcompI[OF *], assumption)
    apply (rule relcompI[of _ "ord.rbt_lookup (comp2lt compare_res) (RBT_Impl.map (\<lambda>_ _. ()) y)"])
       using linorder.rbt_lookup_map[OF x, of "\<lambda>_ _. ()" y]
       apply (auto simp:   rbt_map_rel'_def br_def  ord.map_is_rbt)
      done
    done
qed

lemma get_wit_conv:
  "get_wit = snd"
  by auto

lemma snd_q_conv:
  "snd_q = esnd \<circ> fst"
  by (force simp: comp_def from_entry_def split: entry.splits)

lemma fst_q_conv:
  "fst_q = efst \<circ> fst"
  by (force simp: comp_def from_entry_def split: entry.splits)

lemma [autoref_rules]:
  "(is_busy, is_busy) \<in> \<langle>Rf, Rq\<rangle>status_rel \<rightarrow> bool_rel"
  by (auto simp: status_rel_def)

lemma entries_rbt_rel:
  "(RBT_Impl.entries, RBT_Impl.entries) \<in> \<langle>K, V\<rangle>rbt_rel \<rightarrow> \<langle>K \<times>\<^sub>r V\<rangle>list_rel"
  using param_append[of "K \<times>\<^sub>r V"] refine_list(2)[of "K \<times>\<^sub>r V"]
  apply (intro fun_relI)
  subgoal for x y by (induct x arbitrary: y; case_tac y) (auto elim: rbt_rel_cases dest!: fun_relD)
  done

text \<open>see also @{term PREFER_id}\<close>
definition [simp]: "REL_IS_compare_res R \<equiv> R = compare_res"
abbreviation "PREFER_compare_res \<equiv> PREFER REL_IS_compare_res"
lemma REL_IS_compare_res_trigger: "R = compare_res \<Longrightarrow> REL_IS_compare_res R" by simp
declaration \<open>Tagged_Solver.add_triggers 
  "Relators.relator_props_solver" @{thms REL_IS_compare_res_trigger}\<close>

lemma [autoref_rules]:
  assumes "PREFER_compare_res (R :: _ :: compare_order \<Rightarrow> _)"
  shows "(RBT_Impl.entries, map_to_set) \<in> \<langle>K, V\<rangle>(rbt_map_rel (comp2lt R)) \<rightarrow> \<langle>K \<times>\<^sub>r V\<rangle>list_set_rel"
  unfolding list_set_rel_def rbt_map_rel_def assms[simplified]
proof (intro fun_relI, elim relcompE, simp only: prod.inject)
  have *: "class.linorder (comp2le (compare_res :: _ :: compare_order \<Rightarrow> _)) (comp2lt compare_res)"
    unfolding eq_linorder_class_conv[symmetric] by (rule compare_to_eq_linorder)
  fix x y z
  assume "(x, y) \<in> \<langle>K, V\<rangle>rbt_rel"
  moreover assume "(y, z) \<in> rbt_map_rel' (comp2lt compare_res)"
  then have "(RBT_Impl.entries y, map_to_set z) \<in> br set distinct"
    using linorder.map_to_set_lookup_entries[OF *, of y] linorder.distinct_entries[OF *, of y]
    by (auto simp: distinct_mapI lt_of_comp_post_simp ord_defs rbt_map_rel'_def br_def
      ord.is_rbt_def is_rbt_def rbt_lookup_into_class rbt_sorted_into_class)
  ultimately show "(RBT_Impl.entries x, map_to_set z) \<in> \<langle>K \<times>\<^sub>r V\<rangle>list_rel O br set distinct"
    using entries_rbt_rel by (auto intro: relcompI[of _ "RBT_Impl.entries y"] dest: fun_relD)
qed

lemma listset_by_product_lists:
  "listset (map set xss) = set (product_lists xss)"
  by (induct xss) (auto simp: set_Cons_def)

subsection \<open>experiments\<close>

lemma [autoref_rules]:
  shows "(product_lists, listset) \<in> \<langle>\<langle>R\<rangle>list_set_rel\<rangle>list_rel \<rightarrow> \<langle>\<langle>R\<rangle>list_rel\<rangle>list_set_rel"
  unfolding list_set_rel_def list_rel_compp
proof (intro fun_relI, elim relcompE, simp only: prod.inject)
  fix x y z
  assume "(x, y) \<in> \<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel"
  then have "(product_lists x, product_lists y) \<in> \<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel"
    by (induct x arbitrary: y)
      (auto simp: list_rel_split_right_iff intro!: fun_relD[OF param_concat] fun_relD[OF fun_relD[OF param_map]])
  moreover assume yz: "(y, z) \<in> \<langle>br set distinct\<rangle>list_rel"
  { have "distinct (product_lists y)" using yz
      by (intro distinct_product_lists, induct y arbitrary: z) (auto simp: list_rel_split_right_iff br_def)
    moreover have "set (product_lists y) = listset z" using yz
      by (induct y arbitrary: z) (auto simp: list_rel_split_right_iff br_def set_Cons_def, force)
    ultimately have "(product_lists y, listset z) \<in> br set distinct"
      by (auto simp: br_def)
  } ultimately show "(product_lists x, listset z) \<in> \<langle>\<langle>R\<rangle>list_rel\<rangle>list_rel O br set distinct"
    by auto
qed

lemma next_reach_impl:
  "next_reach A = (let eps = memo_rtrancl (ta_eps A) in
     (\<lambda>qs f. \<Union>((eps \<circ> r_rhs) ` {r \<in> ta_rules A . r_root r = f \<and> list_all2 (\<in>) (r_lhs_states r) qs})))"
  by (force simp: next_reach_def[abs_def] memo_rtrancl_def[abs_def] r_rhs_def intro!: ext split: ta_rule.split_asm)

schematic_goal [autoref_rules]:
   "(?f, next_reach) \<in> dflt_ta_rel \<rightarrow> \<langle>\<langle>Id\<rangle>comp_rs_rel\<rangle>list_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  unfolding next_reach_impl
  by autoref

schematic_goal process_function_symbol_ref:
  notes param_replicate[autoref_rules]
  shows "(?f, process_function_symbol) \<in> dflt_ta_rel \<rightarrow> dflt_ta_rel \<rightarrow> state_rel \<rightarrow> 
   Id \<times>\<^sub>r nat_rel \<rightarrow> state_rel \<times>\<^sub>r \<langle>Id, Id\<rangle>status_rel \<rightarrow> \<langle>state_rel \<times>\<^sub>r \<langle>Id, Id\<rangle>status_rel\<rangle>nres_rel"
  unfolding process_function_symbol_def critical_def get_wit_conv snd_q_conv fst_q_conv continue_condition_def
    map_to_set_def[symmetric]
  by autoref

lemma [autoref_rules]:
  "(adapt_vars, adapt_vars) \<in> \<langle>Id,Id\<rangle>term_rel \<rightarrow> \<langle>Id,Id\<rangle>term_rel"
  by auto

lemma [autoref_rules]:
  "PREFER_id R \<Longrightarrow> (r_sym, r_sym) \<in> R"
  by auto

schematic_goal ta_lang_containment_ref:
  notes process_function_symbol_ref[autoref_rules]
  shows "(?f, ta_lang_containment) \<in> dflt_ta_rel \<rightarrow> dflt_ta_rel \<rightarrow> \<langle>\<langle>\<langle>Id, Id\<rangle>term_rel\<rangle>xoption_rel\<rangle>nres_rel"
  unfolding ta_lang_containment_def check_abort_def process_function_symbols_def
    critical_def get_wit_conv snd_q_conv fst_q_conv
    continue_condition_def ta_syms_def
  by autoref

schematic_goal ta_lang_containment_ref2:
  notes ta_lang_containment_ref[autoref_rules]
  assumes [autoref_rules]: "(A', A) \<in> dflt_ta_rel" "(B', B) \<in> dflt_ta_rel"
  shows "?f \<le> \<Down>(\<langle>\<langle>Id, Id\<rangle>term_rel\<rangle>xoption_rel) (ta_lang_containment A B)"
  by (autoref_monadic)

concrete_definition ta_lang_containment_impl uses ta_lang_containment_ref2

no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

end
