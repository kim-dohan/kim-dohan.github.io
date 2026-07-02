theory SegToLts
  imports
    Closed_Checker
    Lts_of_Graph
begin

(* TODO: is the import of Closed_Checker needed? detangle Closed_Checker and SegToLts *)

context graph_exec'
begin

definition all_var_names where
  "all_var_names = (let
    vars = map fst \<circ> vars_formula_list \<circ> kb \<circ> snd
    in remdups (concat (map vars nodes_asm_list)))"

definition all_pv_names where
  "all_pv_names = (let
    pvs = Mapping.ordered_keys \<circ> stack \<circ> snd
    in remdups (concat (map pvs nodes_asm_list)))"

fun find_pv' where
  "find_pv' (n#ns) (x#xs) lv =
     (case (Mapping.lookup as n) of Some asm \<Rightarrow>
       (case Mapping.lookup (stack asm) x of Some lv' \<Rightarrow> (if lv = lv' then x else find_pv' (n#ns) xs lv)
                                          | None \<Rightarrow> find_pv' (n#ns) xs lv))"
| "find_pv' (n#ns) [] lv = find_pv' ns all_pv_names lv"
| "find_pv' [] xs lv = undefined"

definition lv_to_pv where "lv_to_pv n = find_pv' [n] all_pv_names"

definition lts_rule_of_edge' :: "_ \<Rightarrow> _ \<Rightarrow> (IA.sig, _, IA.ty, 'n) transition_rule option"
  where
  "lts_rule_of_edge' n m = do {
     asm\<^sub>1 \<leftarrow> Mapping.lookup as n;
     asm\<^sub>2 \<leftarrow> Mapping.lookup as m;
     let \<mu> = renaming_of_edge' (n, m);
     let kb\<^sub>1 = kb asm\<^sub>1;
     let kb\<^sub>2 = kb asm\<^sub>2;
     let stack\<^sub>1 = stack asm\<^sub>1;
     let stack\<^sub>2 = stack asm\<^sub>2;
     let pre_f = pre_post_mapping Pre Intermediate (Mapping.lookup stack\<^sub>1 \<circ> lv_to_pv n) (sorted_list_of_set (Mapping_values stack\<^sub>1));
     let kb1_f = rename_vars Intermediate kb\<^sub>1;
     let post_f = pre_post_mapping Post (Intermediate o \<mu>) (Mapping.lookup stack\<^sub>2 \<circ> lv_to_pv m) (sorted_list_of_set (Mapping_values stack\<^sub>2));
     let kb2_f = rename_vars (Intermediate o \<mu>) kb\<^sub>2;
     Some (Transition n m (pre_f \<and>\<^sub>f post_f \<and>\<^sub>f kb1_f \<and>\<^sub>f kb2_f))}"

definition transitions where
  "transitions = mapM (\<lambda>(x,y). lts_rule_of_edge' x y) edges_list"

definition seg_impl_to_lts_impl where
  "seg_impl_to_lts_impl = transitions \<bind> (\<lambda>ts. Some (Lts_Impl [initial_node seg]
  (map (\<lambda>(x,y). (show x, y)) (List.enumerate 0 ts)) []))"

end

fun showsl_trans_var_aprove where
  "showsl_trans_var_aprove (Pre v) = showsl v o showsl_lit (STR ''_pre'')"
| "showsl_trans_var_aprove (Post v) = showsl v o showsl_lit (STR ''_post'')" \<comment> \<open>single quote\<close>
| "showsl_trans_var_aprove (Intermediate v) = showsl v o showsl_lit (STR ''_trans'')"

fun showsl_var_aprove where
  "showsl_var_aprove (v,_) = showsl_trans_var_aprove v"

fun showsl_term_aprove where
  "showsl_term_aprove (Var a) = showsl_var_aprove a"
| "showsl_term_aprove (Fun IA.LessF a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' < '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_term_aprove (Fun IA.LeF a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' <= '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_term_aprove (Fun (IA.SumF _) a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' + '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_term_aprove (Fun (IA.ConstF i) a) = showsl i"
| "showsl_term_aprove (Fun (IA.ProdF _) a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' * '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_term_aprove (Fun IA.EqF a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' = '') (STR '')'') (map showsl_term_aprove a)"

fun showsl_not_term_aprove where
  "showsl_not_term_aprove (Var a) = showsl_var_aprove a"
| "showsl_not_term_aprove (Fun IA.LessF a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' >= '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_not_term_aprove (Fun IA.LeF a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' > '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_not_term_aprove (Fun (IA.SumF _) a) =  showsl_list_gen id (STR '''') (STR ''('') (STR '' + '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_not_term_aprove (Fun (IA.ConstF i) a) = showsl i"
| "showsl_not_term_aprove (Fun (IA.ProdF _) a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' * '') (STR '')'') (map showsl_term_aprove a)"
| "showsl_not_term_aprove (Fun IA.EqF a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' != '') (STR '')'') (map showsl_term_aprove a)"


fun showsl_formula_aprove where
  "showsl_formula_aprove (Atom a) = showsl_term_aprove a"
| "showsl_formula_aprove (NegAtom a) = showsl_lit (STR ''('') o showsl_not_term_aprove a o showsl_lit (STR '')'')"
| "showsl_formula_aprove (Conjunction a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' && '') (STR '')'') (map showsl_formula_aprove a)"
| "showsl_formula_aprove (Disjunction a) = showsl_list_gen id (STR '''') (STR ''('') (STR '' || '') (STR '')'') (map showsl_formula_aprove a)"


locale showsl_transition
begin
fun showsl_transition :: "(IA.sig,_,_,_) transition_rule \<Rightarrow> showsl" where
  "showsl_transition (Transition s t \<phi>) = (
    let ss = (\<lambda>f. showsl_list_gen f (STR '''') (STR '''') (STR '', '') (STR ''''));
        pres = ss showsl_trans_var_aprove (filter (\<lambda>x. case x of Pre _ \<Rightarrow> True | _ \<Rightarrow> False) (remdups (map fst (vars_formula_list \<phi>))));
        posts = ss showsl_trans_var_aprove (filter (\<lambda>x. case x of Post _ \<Rightarrow> True | _ \<Rightarrow> False) (remdups (map fst (vars_formula_list \<phi>))))
    in showsl s o showsl_lit (STR ''('') \<circ> pres \<circ> showsl_lit (STR '') -> '')
     \<circ> showsl t \<circ> showsl_lit (STR ''('')\<circ> posts \<circ> showsl_lit (STR '') ['')
     \<circ> showsl_formula_aprove \<phi> \<circ> showsl_lit (STR '']'')
   )"

fun showsl_labeled_transition :: "('tr :: showl \<times> (IA.sig,_,_,_) transition_rule) \<Rightarrow> showsl" where
  "showsl_labeled_transition (lab, tran) = showsl_transition tran"

fun showsl_lts :: "(IA.sig,_,_,_,_)lts_impl \<Rightarrow> showsl" where
  "showsl_lts (Lts_Impl I tran lc) = showsl_sep showsl_labeled_transition showsl_nl tran"
    (*
    o showsl_lit (STR ''\<newline>Location conditions'')
     o showsl_sep (\<lambda> (l,f). showsl l o showsl_lit (STR '': '') o showsl f) showsl_nl lc o showsl_nl"
*)


end

declare showsl_transition.showsl_transition.simps[code]
declare showsl_transition.showsl_labeled_transition.simps[code]
declare showsl_transition.showsl_lts.simps[code]

definition seg_impl_to_lts_impl_str where
  "seg_impl_to_lts_impl_str seg =
    graph_exec'.seg_impl_to_lts_impl seg
    \<bind> Some \<circ> showsl_transition.showsl_lts"

lemma map_filter_sorted_list_of_set:
  assumes "finite A"
  shows "set (List.map_filter f (sorted_list_of_set A)) = (the \<circ> f) ` {x \<in> A. f x \<noteq> None}"
  using assms by (auto simp add: image_def Misc.set_map_filter)

lemma set_enumerate:
  "(\<exists>n. (n,b) \<in> set (List.enumerate m xs)) \<longleftrightarrow> b \<in> set xs"
  by (induction xs arbitrary: m) (auto intro: set_zip_rightD)

lemma Mapping_values_ran: "Mapping_values m = ran (Mapping.lookup m)"
 by (auto simp add: Mapping_values_def keys_dom_lookup ran_alt_def)+

context graph_exec'
begin


lemma seg_impl_to_lts_impl_eq_lts_of_graph:
  assumes "seg_impl_to_lts_impl = Some lt"
  shows "lts_of lt = lts_of_graph lv_to_pv id {initial_node seg}"
proof -
  have a: "(v, w) \<in> set (nodes_as seg) \<Longrightarrow> \<exists>x\<in>set (nodes_as seg). v = fst x" for v w
    by force
  have "\<exists>x\<in>edges. \<forall>x1 x2. x = (x1, x2) \<longrightarrow> b = lts_rule_of_edge lv_to_pv id x1 x2"
    if "Option_Monad.mapM (\<lambda>(x, y). lts_rule_of_edge' x y) edges_list = Some xs"
       "(a, b) \<in> set (List.enumerate 0 xs)" for xs a b
  proof -
    have "b \<in> set xs"
      using set_enumerate that by fast
    then have "\<exists>x\<^sub>1 x\<^sub>2. (x\<^sub>1, x\<^sub>2) \<in> set edges_list \<and> lts_rule_of_edge' x\<^sub>1 x\<^sub>2 = Some b"
      using mapM_Some that by (fastforce split: prod.splits)
    then obtain x\<^sub>1 x\<^sub>2 where x\<^sub>1: "(x\<^sub>1, x\<^sub>2) \<in> set edges_list" "lts_rule_of_edge' x\<^sub>1 x\<^sub>2 = Some b"
      by blast
    have "b = lts_rule_of_edge lv_to_pv id x\<^sub>1 x\<^sub>2"
      using x\<^sub>1 unfolding lts_rule_of_edge'_def lts_rule_of_edge_def
      by (auto split: Option.bind_splits simp add: asm_to_as_simps Mapping_values_ran)
    then show ?thesis
      using x\<^sub>1 unfolding edges_list_def using assms by (fastforce simp add: edges_def edges_list_def)
  qed
  moreover have "\<exists>x\<in>set (List.enumerate 0 xs). lts_rule_of_edge lv_to_pv id a b = snd x"
    if a: "Option_Monad.mapM (\<lambda>(x, y). lts_rule_of_edge' x y) edges_list = Some xs" "(a, b) \<in> edges"
    for xs a b
  proof -
    have "(a, b) \<in> set edges_list"
      using assms that unfolding edges_list_def edges_def by blast

    then obtain y where y: "lts_rule_of_edge' a b = Some y" "y \<in> set xs"
      using mapM_Some a by force
    then have "lts_rule_of_edge lv_to_pv id a b = y"
      unfolding lts_rule_of_edge'_def lts_rule_of_edge_def
      by (auto split: Option.bind_splits simp add: asm_to_as_simps Mapping_values_ran)
    then show ?thesis
      using y set_enumerate by (metis prod.sel(2))
  qed
  ultimately show ?thesis
  unfolding lts_of_def lts_of_graph_def image_set using assms
  by (fastforce simp add: nodes_list_def assertion_of_def seg_impl_to_lts_impl_def
      transitions_def image_def nodes_def
      split: Option.bind_splits prod.splits intro: a)
qed

end

declare graph_exec'.all_var_names_def[code]
declare graph_exec'.all_pv_names_def[code]
declare graph_exec'.find_pv'.simps[code]
declare graph_exec'.lv_to_pv_def[code]
declare graph_exec'.lts_rule_of_edge'_def[code]
declare graph_exec'.transitions_def[code]
declare graph_exec'.seg_impl_to_lts_impl_def[code]

end