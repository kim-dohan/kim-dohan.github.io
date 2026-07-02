theory Tree_Automata_Autoref_Setup
imports
  Collections.Refine_Dflt
  Deriving.Compare_Order_Instances
  Deriving.RBT_Comparator_Impl
  "Transitive-Closure.Transitive_Closure_RBT_Impl"
  Tree_Automata
  First_Order_Terms.Option_Monad
begin

section \<open>Autoref setup for tree automata and related types, like terms and contexts.\<close>

text \<open>
  Disable the code_printing for some theories that are imported by ICF/Autoref, but are not required
  in our formalization. In particular the code_printing "Array" is problematic, since it is not
  compatible with IsaFoR's code generations setup. (It seems to require separate Haskell modules for
  each theory).
\<close>

code_printing code_module "Array" \<rightharpoonup> (Haskell)
code_printing code_module "STArray" \<rightharpoonup> (SML)
code_printing code_module "DiffArray" \<rightharpoonup> (Scala)

code_printing code_module "Uint" \<rightharpoonup> (SML)
code_printing code_module "Uint" \<rightharpoonup> (Haskell)
code_printing code_module "Uint" \<rightharpoonup> (OCaml)
code_printing code_module "Uint" \<rightharpoonup> (Scala)

code_printing code_module "Uint32" \<rightharpoonup> (SML)
code_printing code_module "Uint32" \<rightharpoonup> (Haskell)
code_printing code_module "Uint32" \<rightharpoonup> (OCaml)
code_printing code_module "Uint32" \<rightharpoonup> (Scala)

code_printing code_module "Bits_Integer" \<rightharpoonup> (SML)
code_printing code_module "Data_Bits" \<rightharpoonup> (Haskell)
code_printing code_module "Bits_Integer" \<rightharpoonup> (OCaml)
code_printing code_module "Bits_Integer" \<rightharpoonup> (Scala)

subsection \<open>Autoref setup for sets\<close>

text \<open>Refine sets to comparison based red-black trees by default.\<close>

fun comp_res_of_order where
  "comp_res_of_order Eq = EQUAL"
| "comp_res_of_order Lt = LESS"
| "comp_res_of_order Gt = GREATER"

definition "compare_res x y \<equiv> comp_res_of_order (compare x y)"

text \<open>Use compare to resolve ordering side conditions instead of the default order.\<close>

declare class_to_eq_linorder[autoref_ga_rules del]
lemma compare_to_eq_linorder[autoref_ga_rules]: "eq_linorder compare_res"
proof -
  have inv:
    "compare y x = Lt \<Longrightarrow> compare x y = Gt"
    "compare y x = Gt \<Longrightarrow> compare x y = Lt" for x y :: 'a
  by (simp_all add: comparator.Gt_lt_conv comparator.Lt_lt_conv comparator_compare)
  have trans:
    "compare x y = Lt \<Longrightarrow> compare y z = Lt \<Longrightarrow> compare x z = Lt" for x y z :: 'a
  using comparator_compare[unfolded comparator_def] by blast
  show ?thesis
  by (unfold_locales) (auto elim!: comp_res_of_order.elims simp: compare_res_def dest: inv trans)
qed

text \<open>Add post simplification rules that replace operations on red black trees with corresponding
  ones that use @{const compare} more efficiently.\<close>

lemma lt_of_comp_post_simp:
  "comp2lt compare_res = lt_of_comp compare"
by (auto simp: fun_eq_iff comp2lt_def lt_of_comp_def compare_res_def split: order.splits )

lemmas rbt_comp_post_simps[autoref_post_simps] =
  lt_of_comp_post_simp
  rbt_comp_simps[OF comparator_compare, symmetric]
  map2set_insert_def[abs_def]
  map2set_memb_def[abs_def]
  ord.rbt_union_def
  ord.rbt_inter_def

text \<open>Delete default relators for sets and maps.\<close>

declare tyrel_dflt[autoref_tyrel del]

text \<open>Remove the refinement rules for the default comparison operator, which are to restrictive
 and cause failures when refining certain sets over polymorphic types.\<close>

declare autoref_prod_cmp_dflt_id[autoref_rules_raw del]
declare dflt_cmp_id[autoref_rules_raw del]

text \<open>Install a refinement rule for comparison based ordering.\<close>
(* TODO: prove a less restrictive variant, requiring R to be single valued should be enough. *)

lemma dflt_comp_id[autoref_rules]:
  "PREFER_id R \<Longrightarrow> (compare_res, compare_res) \<in> R \<rightarrow> R \<rightarrow> Id"
by simp

text \<open>Relator for comparison based red black trees.\<close>

abbreviation "comp_rm_rel \<equiv> rbt_map_rel (comp2lt compare_res)"
abbreviation "comp_rs_rel \<equiv> map2set_rel comp_rm_rel"

text \<open>Delete the priorities of the provided relators for sets and maps, and register comparison
  based red-black trees instead.\<close>

local_setup \<open>
  let open Autoref_Fix_Rel in
    delete_prio "Gen-AHM-map-hashable" #>
    delete_prio "Gen-RBT-map-linorder" #>
    delete_prio "Gen-AHM-map" #>
    delete_prio "Gen-RBT-map" #>
    delete_prio "Gen-List-Set" #>
    delete_prio "Gen-List-Map"
  end
\<close>

local_setup \<open>
  let open Autoref_Fix_Rel in
    declare_prio "Gen-RBT-set-compare" @{term "\<langle>R\<rangle>comp_rs_rel"} PR_LAST #>
    declare_prio "Gen-RBT-map-compare" @{term "\<langle>Rk,Rv\<rangle>comp_rm_rel"} PR_LAST
  end
\<close>

subsection \<open>Auxiliary lemmas concerning RBTs and @{class compare_order}\<close>

lemma color_rel_id[simp]:
  "color_rel = Id"
using color.exhaust color_rel.simps by (auto dest: color_rel.cases)

lemma rbt_rel_id[simp]:
  "\<langle>Id, Id\<rangle>rbt_rel = Id" (is "?L = ?R")
proof (standard)
  show "?L \<subseteq> ?R"
  proof (standard)
    fix x and y assume "(x, y) \<in> ?L"
    then show "(x, y) \<in> Id" by (induction rule: rbt_rel_induct) (auto simp: color_rel.simps)
  qed
  show "?R \<subseteq> ?L"
  proof (standard)
    fix x y assume "(x, y) \<in> ?R"
    then have x: "x = y" by simp
    show "(x, y) \<in> ?L" unfolding x by (induction y) (auto intro!: rbt_rel_intros)
  qed
qed

lemma is_rbt_dflt_order[simp]:
  "ord.is_rbt (<) = is_rbt"
unfolding
  fun_eq_iff
  ord.is_rbt_def ord.rbt_sorted_def ord.rbt_less_prop ord.rbt_greater_prop
  is_rbt_def rbt_sorted_def rbt_less_prop rbt_greater_prop
by simp

lemma is_rbt_compare_order[simp]:
  "ord.is_rbt (comp2lt (compare_res::'a::compare_order \<Rightarrow> _ \<Rightarrow> _)) = is_rbt"
unfolding
  fun_eq_iff
  lt_of_comp_post_simp
  ord_defs
  is_rbt_dflt_order
by simp

lemma rbt_comp_lookup_compare_order:
  "rbt_comp_lookup (compare :: 'a::compare_order \<Rightarrow> _) = rbt_lookup"
unfolding
  fun_eq_iff
  rbt_comp_lookup[OF comparator_compare]
  ord.rbt_lookup_def
  rbt_lookup_def 
  lt_of_comp_post_simp
  ord_defs
by simp

lemmas rbt_map_rel_simps = map2set_rel_def rbt_map_rel_def rbt_map_rel'_def br_def relcomp_unfold

lemma is_rbt_compare_refine_spec:
  assumes "RETURN x \<le> \<Down> (\<langle>Id, Id\<rangle>comp_rm_rel) (RES y)"
    shows "is_rbt (x :: ('a::compare_order,_) RBT_Impl.rbt) "
using assms by (simp add: RETURN_RES_refine_iff rbt_map_rel_simps)

lemma is_rbt_compare_refine_spec':
  assumes code: "RETURN x \<le> i"
  assumes impl: "i \<le> \<Down>(\<langle>Id, Id\<rangle>comp_rm_rel) f"
  assumes spec: "f \<le> RES s"
    shows "is_rbt (x :: ('a::compare_order,_) RBT_Impl.rbt) "
proof -
  note code
  also note impl
  also note spec
  finally show ?thesis by (simp add: RETURN_RES_refine_iff rbt_map_rel_simps)
qed

lemma is_rbt_mapE:
  assumes "is_rbt rbt"
  obtains m where "(rbt,m::'a::compare_order \<Rightarrow> _) \<in> \<langle>Id,Id\<rangle>comp_rm_rel"
using assms by (auto simp: rbt_map_rel_simps)

subsection \<open>Natural relator for @{typ "('f,'v)term"} \<close>

inductive_set term_rel_aux for Rs Rv where
  Var: "(x,x') \<in> Rv  \<Longrightarrow> (Var x, Var x') \<in> term_rel_aux Rs Rv"
| Fun: "\<lbrakk> (f,f') \<in> Rs;  list_all2 (\<lambda>t t'. (t, t') \<in> term_rel_aux Rs Rv) ts ts' \<rbrakk>
          \<Longrightarrow> (Fun f ts, Fun f' ts') \<in> term_rel_aux Rs Rv"

definition term_rel_def_internal: "term_rel \<equiv> term_rel_aux"
lemma term_rel_def[refine_rel_defs]: 
  "\<langle>Rs, Rv\<rangle>term_rel \<equiv> term_rel_aux Rs Rv"
by (simp add: term_rel_def_internal relAPP_def)

lemma term_rel_unfold:
  "list_all2 (\<lambda>t t'. (t, t') \<in> term_rel_aux F V) t t' \<longleftrightarrow> (t,t') \<in> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel"
unfolding term_rel_def list_rel_def by blast

lemma term_rel_unfold':
  "list_all2 (\<lambda>t t'. (t, t') \<in> term_rel_aux F V \<and> P t t') t t' \<longleftrightarrow> (t,t') \<in> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel \<and> list_all2 P t t'"
unfolding term_rel_def list_rel_def list_all2_conv_all_nth by auto

lemmas term_rel_Var[intro] = Var[folded term_rel_def]
lemmas term_rel_Fun[intro] = Fun[unfolded term_rel_unfold, folded term_rel_def]
lemmas term_rel_simps = term_rel_aux.simps[unfolded term_rel_unfold, folded term_rel_def]
lemmas term_rel_cases = term_rel_aux.cases[unfolded term_rel_unfold, folded term_rel_def]
lemmas term_rel_induct = term_rel_aux.induct[unfolded term_rel_unfold', folded term_rel_def]

lemma term_rel_aux_simps[simp]:
  "(Var x, Fun f ts) \<notin> \<langle>F,V\<rangle>term_rel"
  "(Fun f ts, Var x) \<notin> \<langle>F,V\<rangle>term_rel"
by (auto simp: term_rel_simps)

lemma term_relE1:
  assumes "(Var x, t) \<in> \<langle>F,V\<rangle>term_rel"
  obtains x' where "t = Var x'" "(x,x') \<in> V"
using assms by (auto simp: term_rel_simps)

lemma term_relE2:
  assumes "(t, Var x) \<in> \<langle>F,V\<rangle>term_rel"
  obtains x' where "t = Var x'" "(x',x) \<in> V"
using assms by (auto simp: term_rel_simps)

lemma term_relE3:
  assumes "(t, Fun f ts) \<in> \<langle>F,V\<rangle>term_rel"
  obtains f' ts' where "t = Fun f' ts'" "(f',f) \<in> F" "(ts',ts) \<in> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel"
using assms by (auto simp: term_rel_simps)

lemma term_relE4:
  assumes "(Fun f ts, t) \<in> \<langle>F,V\<rangle>term_rel"
  obtains f' ts' where "t = Fun f' ts'" "(f,f') \<in> F" "(ts,ts') \<in> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel"
using assms by (auto simp: term_rel_simps)

lemmas term_relE = term_relE1 term_relE2 term_relE3 term_relE4

lemma term_rel_sv[relator_props]:
  assumes "single_valued Rs" "single_valued Rv"
  shows "single_valued (\<langle>Rs, Rv\<rangle>term_rel)"
proof (intro single_valuedI allI impI)
  fix x y z
  assume *: "(x, y) \<in> \<langle>Rs, Rv\<rangle>term_rel" and "(x, z) \<in> \<langle>Rs, Rv\<rangle>term_rel"
  then show "y = z"
  proof (induction arbitrary: z rule: term_rel_induct[OF *])
    case (1 x x')
      with assms[THEN single_valuedD] show ?case by (auto simp: term_rel_simps)
    next
    case (2 f f' ts ts')
      note Fun = this
      from Fun(4) obtain fz tz where
        z: "z = Fun fz tz" and tz: "(ts,tz) \<in> \<langle>\<langle>Rs,Rv\<rangle>term_rel\<rangle>list_rel" by (auto simp: term_rel_simps)
      from Fun(2) tz have "ts' = tz" by (simp add: nth_equalityI list_rel_def list_all2_conv_all_nth z) 
      with Fun assms[THEN single_valuedD] show ?case by (auto simp: term_rel_simps z)
  qed
qed

lemma term_rel_id[relator_props]:
  assumes "Rs = Id" and "Rv = Id"
    shows "\<langle>Rs, Rv\<rangle>term_rel = Id"
proof(simp only: assms, rule)
  show "\<langle>Id, Id\<rangle>term_rel \<subseteq> Id"
  proof
    fix x y :: "('f, 'v) term"
    assume *: "(x,y) \<in> \<langle>Id, Id\<rangle>term_rel"
    have "x = y" by (induction rule: term_rel_induct[OF *], simp_all add: list_all2_eq)
    then show "(x,y) \<in> Id" by blast
  qed
  show "Id \<subseteq> \<langle>Id, Id\<rangle>term_rel"
  proof
    fix x y :: "('f, 'v) term"
    assume "(x,y) \<in> Id"
    moreover have "(x,x) \<in> \<langle>Id, Id\<rangle>term_rel" by (induction x, auto simp: list_rel_def list_all2_same)
    ultimately show "(x,y) \<in> \<langle>Id, Id\<rangle>term_rel" by simp
  qed
qed

lemma term_rel_id_simp[simp]:
  shows "\<langle>Id, Id\<rangle>term_rel = Id" by tagged_solver

lemma term_rel_mono[relator_props]:
  assumes "Rs \<subseteq> Rs'" and "Rv \<subseteq> Rv'"
  shows "\<langle>Rs, Rv\<rangle>term_rel \<subseteq> \<langle>Rs', Rv'\<rangle>term_rel"
proof
  fix x y
  assume *: "(x,y) \<in> \<langle>Rs, Rv\<rangle>term_rel"
  from assms show "(x,y) \<in> \<langle>Rs', Rv'\<rangle>term_rel"
  by (induction rule: term_rel_induct[OF *], auto simp: list_rel_def list_all2_conv_all_nth)
qed

lemma term_rel_range[relator_props]:
  assumes sym: "Range Rs = UNIV" and vars: "Range Rv = UNIV"
    shows "Range (\<langle>Rs, Rv\<rangle>term_rel) = UNIV"
proof
  show "Range (\<langle>Rs, Rv\<rangle>term_rel) \<subseteq> UNIV" by blast
  show "UNIV \<subseteq> Range (\<langle>Rs, Rv\<rangle>term_rel)"
  proof
    fix x
    from assms show "x \<in> Range (\<langle>Rs, Rv\<rangle>term_rel)" unfolding Range_iff proof (induction x)
      case (Fun f ts)
        then have "\<forall>t . \<exists>t'. t \<in> set ts \<longrightarrow> (t', t) \<in> \<langle>Rs, Rv\<rangle>term_rel" by blast
        from choice[OF this] obtain ts' where ts': "\<And>x. x \<in> set ts \<Longrightarrow> (ts' x, x) \<in> \<langle>Rs, Rv\<rangle>term_rel" by blast
        moreover from sym obtain f' where "(f',f) \<in> Rs" by auto
        ultimately show ?case by (intro exI[of _ "Fun f' (map ts' ts)"], auto simp: list_rel_def list_all2_conv_all_nth)
    qed (auto simp add: term_rel_simps)
  qed
qed

lemma term_autoref[autoref_rules, param]:
  "(Var, Var) \<in> V \<rightarrow> \<langle>F,V\<rangle>term_rel"
  "(Fun, Fun) \<in> F \<rightarrow> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel \<rightarrow> \<langle>F,V\<rangle>term_rel"
  "(case_term, case_term) \<in> (V \<rightarrow> X) \<rightarrow> (F \<rightarrow> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel \<rightarrow> X) \<rightarrow> \<langle>F,V\<rangle>term_rel \<rightarrow> X"
by (force split: term.split simp: term_rel_simps dest: fun_relD)+

lemma rec_term_autoref[autoref_rules, param]:
  "(rec_term, rec_term) \<in> (V \<rightarrow> X) \<rightarrow> (F \<rightarrow> \<langle>\<langle>F,V\<rangle>term_rel \<times>\<^sub>r X\<rangle>list_rel \<rightarrow> X) \<rightarrow> \<langle>F,V\<rangle>term_rel \<rightarrow> X"
proof (intro fun_relI, goal_cases)
case (1 v v' l l' t t')
  then show ?case proof (induction t arbitrary: t')
    case (Var x)
      from this obtain x' where t': "t' = Var x'" "(x,x') \<in> V" by (auto simp: term_rel_simps)
      with Var show ?case unfolding t' by (auto dest: fun_relD)
    next
    case (Fun f ts)
      let ?r = "rec_term v l" and ?r' = "rec_term v' l'"
      from Fun obtain f' ts' where t': "t' = Fun f' ts'" and f: "(f,f') \<in> F"
        and ts: "(ts, ts') \<in> \<langle>\<langle>F,V\<rangle>term_rel\<rangle>list_rel" by (auto simp: term_rel_simps)
      then have "length ts = length ts'" by (auto simp: list_rel_def dest: list_all2_lengthD)
      then have all: "list_all2 (\<lambda>t t'. (?r t, ?r' t') \<in> X) ts ts'"
        using Fun ts by (auto simp: list_rel_def list_all2_conv_all_nth)
      then have "(map (\<lambda>t. (t, ?r t)) ts, map (\<lambda>t'. (t', ?r' t')) ts') \<in> \<langle>\<langle>F, V\<rangle>term_rel \<times>\<^sub>r X\<rangle>list_rel"
        using ts by (induction rule: list_all2_induct, simp_all)
      then show ?case by (simp add: t', rule fun_relD[OF Fun.prems(2) f, THEN fun_relD])
  qed
qed

lemma map_rec_term: "map_term ff fv t = rec_term (Var o fv) (\<lambda>f ts. Fun (ff f) (map snd ts)) t"
by (induction t, auto)

lemma map_term_autoref[autoref_rules, param]:
  "(map_term, map_term) \<in> (F \<rightarrow> F') \<rightarrow> (V \<rightarrow> V') \<rightarrow> \<langle>F,V\<rangle>term_rel \<rightarrow> \<langle>F',V'\<rangle>term_rel"
by (intro fun_relI, unfold map_rec_term, parametricity)

lemma param_map_induct1:
  assumes "(xs,xs') \<in> \<langle>R1\<rangle>list_rel"
      and "\<And>x y. x \<in> set xs \<Longrightarrow> (x,y) \<in> R1 \<Longrightarrow> (f x, f' y) \<in> R2"
    shows "(map f xs, map f' xs')\<in> \<langle>R2\<rangle>list_rel"
using assms by (induction xs xs' rule: list_rel_induct) auto

(* make a definition out of the abbreviation *)
definition "Subst_apply_term = subst_apply_term" 

lemma Subst_apply_term_autoref[autoref_rules, param]:
  "(Subst_apply_term, Subst_apply_term) \<in> \<langle>F,V\<rangle>term_rel \<rightarrow> (V \<rightarrow> \<langle>F,W\<rangle>term_rel) \<rightarrow> \<langle>F,W\<rangle>term_rel"
proof (intro fun_relI, goal_cases)
  note [param] = param_map_induct1
  case (1 t t')
  then show ?case unfolding Subst_apply_term_def by (induction t arbitrary: t'; elim term_relE, simp, parametricity)
qed

consts i_term :: "interface \<Rightarrow> interface \<Rightarrow> interface"
lemmas [autoref_rel_intf] = REL_INTFI[of term_rel i_term]

lemma [autoref_itype]:
  "Var ::\<^sub>i V \<rightarrow>\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term"
  "Fun ::\<^sub>i F \<rightarrow>\<^sub>i \<langle>\<langle>F,V\<rangle>\<^sub>ii_term\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term"
  "case_term ::\<^sub>i  (V \<rightarrow>\<^sub>i X) \<rightarrow>\<^sub>i (F \<rightarrow>\<^sub>i \<langle>\<langle>F,V\<rangle>\<^sub>ii_term\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i X) \<rightarrow>\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term \<rightarrow>\<^sub>i X"
  "rec_term ::\<^sub>i (V \<rightarrow>\<^sub>i X) \<rightarrow>\<^sub>i (F \<rightarrow>\<^sub>i \<langle>\<langle>\<langle>F,V\<rangle>\<^sub>ii_term, X\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i X) \<rightarrow>\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term \<rightarrow>\<^sub>i X"
  "map_term ::\<^sub>i (F \<rightarrow>\<^sub>i F') \<rightarrow>\<^sub>i (V \<rightarrow>\<^sub>i V') \<rightarrow>\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term \<rightarrow>\<^sub>i \<langle>F',V'\<rangle>\<^sub>ii_term"
  "Subst_apply_term ::\<^sub>i \<langle>F,V\<rangle>\<^sub>ii_term \<rightarrow>\<^sub>i (V \<rightarrow>\<^sub>i  \<langle>F,W\<rangle>\<^sub>ii_term) \<rightarrow>\<^sub>i \<langle>F,W\<rangle>\<^sub>ii_term"
by simp_all

subsection \<open>Natural relator for @{typ "('f,'v)ctxt"}\<close>

inductive_set actxt_rel_aux for Rs Rv where
  Hole[intro,simp]: "(\<box>, \<box>) \<in> actxt_rel_aux Rs Rv"
| More:"\<lbrakk> (f,f') \<in> Rs; 
         (ss1, ss1') \<in> \<langle>Rv\<rangle>list_rel;
         (C,C') \<in> actxt_rel_aux Rs Rv;
         (ss2, ss2') \<in> \<langle>Rv\<rangle>list_rel\<rbrakk>
         \<Longrightarrow> (More f ss1 C ss2, More f' ss1' C' ss2') \<in> actxt_rel_aux Rs Rv"

definition actxt_rel_def_internal: "actxt_rel \<equiv> actxt_rel_aux"
lemma actxt_rel_def[refine_rel_defs]: 
  "\<langle>Rs, Rv\<rangle>actxt_rel \<equiv> actxt_rel_aux Rs Rv"
by (simp add: actxt_rel_def_internal relAPP_def)

lemma actxt_relE1:
  "(\<box>, C) \<in> \<langle>F,V\<rangle>actxt_rel \<Longrightarrow> (C = \<box> \<Longrightarrow> P) \<Longrightarrow> P"
by (auto simp: actxt_rel_def elim: actxt_rel_aux.cases)

lemma actxt_relE2:
  "(C, \<box>) \<in> \<langle>F,V\<rangle>actxt_rel \<Longrightarrow> (C = \<box> \<Longrightarrow> P) \<Longrightarrow> P"
by (auto simp: actxt_rel_def elim: actxt_rel_aux.cases)

lemma actxt_relE3:
  assumes "(More f ss1 c ss2, C) \<in> \<langle>F,V\<rangle>actxt_rel"
  obtains f' ss1' c' ss2' where "C = More f' ss1' c' ss2'" "(f,f') \<in> F" "(c,c') \<in> \<langle>F,V\<rangle>actxt_rel"
    "(ss1, ss1') \<in> \<langle>V\<rangle>list_rel" "(ss2, ss2') \<in> \<langle>V\<rangle>list_rel"
using assms by (auto simp: actxt_rel_def elim: actxt_rel_aux.cases)

lemma actxt_relE4:
  assumes "(C, More f ss1 c ss2) \<in> \<langle>F,V\<rangle>actxt_rel"
  obtains f' ss1' c' ss2' where "C = More f' ss1' c' ss2'" "(f',f) \<in> F" "(c',c) \<in> \<langle>F,V\<rangle>actxt_rel"
    "(ss1', ss1) \<in> \<langle>V\<rangle>list_rel" "(ss2', ss2) \<in> \<langle>V\<rangle>list_rel"
using assms by (auto simp: actxt_rel_def elim: actxt_rel_aux.cases)

lemmas actxt_relE = actxt_relE1 actxt_relE2 actxt_relE3 actxt_relE4

lemma actxt_rel_sv[relator_props]:
  assumes "single_valued Rs" "single_valued Rv"
  shows "single_valued (\<langle>Rs, Rv\<rangle>actxt_rel)"
unfolding actxt_rel_def proof (intro single_valuedI allI impI)
  fix x y z
  assume "(x, y) \<in> actxt_rel_aux Rs Rv" and "(x, z) \<in> actxt_rel_aux Rs Rv"
  then show "y = z"
  proof (induction arbitrary: z)
    case More
      note sv_intros = single_valuedD list_rel_sv term_rel_sv More.IH More.hyps
      from More.prems assms show ?case by (auto elim!: actxt_rel_aux.cases[of _ z] intro: sv_intros)
  qed (auto elim: actxt_rel_aux.cases)
qed

lemma actxt_rel_id[relator_props]:
  assumes "Rs = Id" and "Rv = Id"
    shows "\<langle>Rs, Rv\<rangle>actxt_rel = Id"
unfolding actxt_rel_def proof(simp only: assms, rule)
  show "actxt_rel_aux Id Id \<subseteq> Id"
  proof
    fix x y :: "('f, 'v) actxt"
    assume "(x,y) \<in> actxt_rel_aux Id Id"
    then have "x = y" by (induction, simp_all add: list_rel_id)
    then show "(x,y) \<in> Id" by blast
  qed
  show "Id \<subseteq> actxt_rel_aux Id Id"
  proof
    fix x y :: "('f, 'v) actxt"
    assume "(x,y) \<in> Id"
    moreover have "(x,x) \<in> actxt_rel_aux Id Id" by (induction x, auto intro: More)
    ultimately show "(x,y) \<in> actxt_rel_aux Id Id" by simp
  qed
qed

lemma actxt_rel_id_simp[simp]:
  shows "\<langle>Id, Id\<rangle>actxt_rel = Id" by tagged_solver

lemma actxt_rel_mono[relator_props]:
  assumes "F \<subseteq> F'" and "V \<subseteq> V'"
  shows "\<langle>F, V\<rangle>actxt_rel \<subseteq> \<langle>F', V'\<rangle>actxt_rel"
unfolding actxt_rel_def proof
  fix x y
  assume "(x, y) \<in> actxt_rel_aux F V"
  then show "(x, y) \<in> actxt_rel_aux F' V'" proof (induction)
    case More
      with assms show ?case by (intro actxt_rel_aux.More, auto dest: list_rel_mono)
  qed simp
qed

lemma actxt_rel_range[relator_props]:
  assumes sym: "Range F = UNIV" and V: "Range V = UNIV"
    shows "Range (\<langle>F, V\<rangle>actxt_rel) = UNIV"
unfolding actxt_rel_def proof
  show "Range (actxt_rel_aux F V) \<subseteq> UNIV" by blast
  show "UNIV \<subseteq> Range (actxt_rel_aux F V)"
  proof
    fix x
    show "x \<in> Range (actxt_rel_aux F V)" unfolding Range_iff proof (induction x)
      case (More f ss1 C ss2)
        note range = list_rel_range[OF V]
        from sym obtain f' where "(f',f) \<in> F" by blast
        moreover from range obtain ss1' ss2' where
          "(ss1',ss1) \<in> \<langle>V\<rangle>list_rel" "(ss2',ss2) \<in> \<langle>V\<rangle>list_rel" by blast
        moreover from More.IH obtain C' where "(C', C) \<in> actxt_rel_aux F V" by blast
        ultimately show ?case by (intro exI[of _ "More f' ss1' C' ss2'"], auto intro: actxt_rel_aux.More)
    qed (intro exI[of _ \<box>], simp)
  qed
qed

lemma actxt_rel_autoref[autoref_rules, param]:
  "(\<box>,\<box>) \<in> \<langle>F,V\<rangle>actxt_rel"
  "(More,More) \<in> F \<rightarrow> \<langle>V\<rangle>list_rel \<rightarrow> \<langle>F,V\<rangle>actxt_rel \<rightarrow> \<langle>V\<rangle>list_rel\<rightarrow> \<langle>F,V\<rangle>actxt_rel"
  "(case_actxt,case_actxt) \<in> X \<rightarrow> (F \<rightarrow> \<langle>V\<rangle>list_rel \<rightarrow> \<langle>F,V\<rangle>actxt_rel \<rightarrow> \<langle>V\<rangle>list_rel \<rightarrow> X) \<rightarrow> \<langle>F,V\<rangle>actxt_rel \<rightarrow> X"
unfolding actxt_rel_def
by (force intro: More split: actxt.split elim: actxt_rel_aux.cases dest: fun_relD)+

lemma actxt_compose_autoref[autoref_rules, param]:
  "((\<circ>\<^sub>c), (\<circ>\<^sub>c)) \<in> \<langle>F,V\<rangle>actxt_rel \<rightarrow> \<langle>F,V\<rangle>actxt_rel \<rightarrow> \<langle>F,V\<rangle>actxt_rel"
proof (intro fun_relI, goal_cases)
  case (1 a a')
  then show ?case by (induction a arbitrary: a' rule: actxt.induct; elim actxt_relE, simp, parametricity?)
qed

lemma intp_actxt_autoref[autoref_rules, param]:
  "(intp_actxt, intp_actxt) \<in> (F \<rightarrow> \<langle>V\<rangle>list_rel \<rightarrow> V) \<rightarrow> \<langle>F,V\<rangle>actxt_rel \<rightarrow> V \<rightarrow> V"
proof (intro fun_relI, goal_cases)
  case (1 I I' C C' a a')
  then show ?case by (induction C arbitrary: C' rule: actxt.induct; elim actxt_relE, simp, parametricity?)
qed

subsection \<open>Autoref setup for @{typ "('q,'f) ta_rule"}\<close>

definition ta_rule_rel :: "_ \<Rightarrow> _ \<Rightarrow> ((_,_) ta_rule \<times> (_,_) ta_rule) set" where ta_rule_rel_def':
  "ta_rule_rel R_sym R_states \<equiv> {(TA_rule f qs q, TA_rule f' qs' q') | f f' qs qs' q q'.
    (f, f') \<in> R_sym \<and>
    (qs, qs') \<in> \<langle>R_states\<rangle>list_rel \<and>
    (q, q') \<in> R_states}"

lemma ta_rule_rel_def[refine_rel_defs]: 
  "\<langle>R_sym, R_states\<rangle>ta_rule_rel \<equiv> {(TA_rule f qs q, TA_rule f' qs' q') | f f' qs qs' q q'.
    (f, f') \<in> R_sym \<and>
    (qs, qs') \<in> \<langle>R_states\<rangle>list_rel \<and>
    (q, q') \<in> R_states }"    
  by (simp add: ta_rule_rel_def' relAPP_def)

lemma ta_rule_rel_sv[relator_props]:
  assumes "single_valued R_sym" and states: "single_valued R_states"
  shows "single_valued (\<langle>R_sym, R_states\<rangle>ta_rule_rel)"
using assms states[THEN list_rel_sv]
by (auto simp add: ta_rule_rel_def intro: single_valuedI dest: single_valuedD)

lemma ta_rule_rel_id[relator_props]:
  assumes "R_sym = Id" and "R_states = Id"
    shows "\<langle>R_sym, R_states\<rangle>ta_rule_rel = Id"
using assms by (auto simp add: ta_rule_rel_def intro: ta_rule.exhaust)

lemma ta_rule_rel_id_simp[simp]:
  shows "\<langle>Id, Id\<rangle>ta_rule_rel = Id" by tagged_solver

lemma ta_rule_rel_mono[relator_props]:
  assumes "R_sym \<subseteq> R_sym'" and states: "R_states \<subseteq> R_states'"
  shows "\<langle>R_sym, R_states\<rangle>ta_rule_rel \<subseteq> \<langle>R_sym', R_states'\<rangle>ta_rule_rel"
using assms states[THEN list_rel_mono] by (auto simp add: ta_rule_rel_def)

lemma ta_rule_rel_range[relator_props]:
  assumes "Range R_sym = UNIV" and states: "Range R_states = UNIV"
    shows "Range (\<langle>R_sym, R_states\<rangle>ta_rule_rel) = UNIV"
proof (rule set_eqI, clarsimp)
  fix x
  show "x \<in> Range (\<langle>R_sym, R_states\<rangle>ta_rule_rel)"
  using assms states[THEN list_rel_range] by (cases x, auto simp add: ta_rule_rel_def Range_iff)
qed

lemma ta_rule_autoref[autoref_rules, param]:
  "(TA_rule, TA_rule) \<in> F \<rightarrow> \<langle>Q\<rangle>list_rel \<rightarrow> Q \<rightarrow> \<langle>F, Q\<rangle>ta_rule_rel"
  "(case_ta_rule, case_ta_rule) \<in> (F \<rightarrow> \<langle>Q\<rangle>list_rel \<rightarrow> Q \<rightarrow> X) \<rightarrow> \<langle>F, Q\<rangle>ta_rule_rel \<rightarrow> X"
  "(r_rhs, r_rhs) \<in> \<langle>F, Q\<rangle>ta_rule_rel \<rightarrow> Q"
  "(r_lhs_states, r_lhs_states) \<in> \<langle>F, Q\<rangle>ta_rule_rel \<rightarrow> \<langle>Q\<rangle>list_rel"
by (force simp: ta_rule_rel_def dest: fun_relD)+

consts i_ta_rule :: "interface => interface => interface"
lemmas [autoref_rel_intf] = REL_INTFI[of ta_rule_rel i_ta_rule]

lemma [autoref_itype]:
  "TA_rule ::\<^sub>i F \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Q \<rightarrow>\<^sub>i \<langle>F,Q\<rangle>\<^sub>ii_ta_rule"
  "case_ta_rule ::\<^sub>i (F \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_list \<rightarrow>\<^sub>i Q \<rightarrow>\<^sub>i X) \<rightarrow>\<^sub>i \<langle>F,Q\<rangle>\<^sub>ii_ta_rule \<rightarrow>\<^sub>i X"
  "r_rhs ::\<^sub>i \<langle>F,Q\<rangle>\<^sub>ii_ta_rule \<rightarrow>\<^sub>i Q"
  "r_lhs_states ::\<^sub>i \<langle>F,Q\<rangle>\<^sub>ii_ta_rule \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_list"
by simp_all

lemma transfer_term[refine_transfer]:
  assumes "\<And>x. \<alpha> (fa x) \<le> Fa x"
  assumes "\<And>x y. \<alpha> (fb x y) \<le> Fb x y"
  shows "\<alpha> (case_term fa fb x) \<le> case_term Fa Fb x"
using assms by (auto split: term.split)

lemma transfer_ta_rule[refine_transfer]:
  assumes "\<And>x y z. \<alpha> (fa x y z) \<le> Fa x y z"
  shows "\<alpha> (case_ta_rule fa x) \<le> case_ta_rule Fa x"
using assms by (auto split: ta_rule.split)

subsection \<open>Autoref setup for @{typ "('q,'f) ta"}\<close>

definition ta_idx :: "(_,_)ta \<Rightarrow> _"  where
  "ta_idx TA \<equiv> \<lambda>(f,n).
    let rs = {(qs,q) | f' qs q. TA_rule f qs q \<in> ta_rules TA \<and> f' = f \<and> length qs = n}
    in if rs = {} then None else Some rs"

abbreviation "dflt_ta_idx_rel \<equiv> \<langle>Id \<times>\<^sub>r nat_rel, \<langle>\<langle>Id\<rangle>list_rel \<times>\<^sub>r Id\<rangle>comp_rs_rel\<rangle>comp_rm_rel"

(* FIXME: move *)
derive compare_order ta_rule

definition dflt_ta_rel :: "(_ \<times> ('q::compare_order, 'f::compare_order) ta) set" where
  "dflt_ta_rel \<equiv> {((F,R,E,rhss,idx,det,efcl,eicl),TA).
    (F, ta_final TA) \<in> \<langle>Id\<rangle>comp_rs_rel \<and> 
    (R, ta_rules TA) \<in> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel \<and>
    (E, ta_eps TA) \<in> \<langle>Id \<times>\<^sub>r Id\<rangle>list_set_rel \<and>
    (rhss, ta_rhs_states TA) \<in> \<langle>Id\<rangle>comp_rs_rel \<and>
    (idx, ta_idx TA) \<in> dflt_ta_idx_rel \<and>
    (det, ta_det TA) \<in> Id \<and>
    (efcl, \<lambda>q. {p. (q, p) \<in> (ta_eps TA)\<^sup>*}) \<in> \<langle>Id,\<langle>Id\<rangle>comp_rs_rel\<rangle>fun_rel \<and>
    (eicl, \<lambda>q. {p. (p, q) \<in> (ta_eps TA)\<^sup>*}) \<in> \<langle>Id,\<langle>Id\<rangle>comp_rs_rel\<rangle>fun_rel}"

fun ta_final_impl where "ta_final_impl (F,R,E,rhs,idx,det,efcl,eicl) = F"
fun ta_rules_impl where "ta_rules_impl (F,R,E,rhs,idx,det,efcl,eicl) = R"
fun ta_eps_impl where "ta_eps_impl (F,R,E,rhs,idx,det,efcl,eicl) = E"
fun ta_eps_cl_impl where "ta_eps_cl_impl (F,R,E,rhs,idx,det,efcl,eicl) q = efcl q"
fun ta_eps_icl_impl where "ta_eps_icl_impl (F,R,E,rhs,idx,det,efcl,eicl) q = eicl q"
fun ta_rhs_states_impl where "ta_rhs_states_impl (F,R,E,rhs,idx,det,efcl,eicl) = rhs"
fun ta_idx_impl where "ta_idx_impl (F,R,E,rhs,idx,det,efcl,eicl) = idx"
fun ta_det_impl where "ta_det_impl (F,R,E,rhs,idx,det,x) = det"

lemma ta_impl_autoref[autoref_rules]:
  "(ta_final_impl, ta_final) \<in> dflt_ta_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  "(ta_rules_impl, ta_rules) \<in> dflt_ta_rel \<rightarrow> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel"
  "(ta_eps_impl, ta_eps) \<in> dflt_ta_rel \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>list_set_rel"
  "(ta_rhs_states_impl, ta_rhs_states) \<in> dflt_ta_rel \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  "(ta_idx_impl, ta_idx) \<in> dflt_ta_rel \<rightarrow> dflt_ta_idx_rel"
  "(ta_det_impl, ta_det) \<in> dflt_ta_rel \<rightarrow> Id"
by (auto simp: dflt_ta_rel_def)

definition [simp]: "op_ta_eps_cl (TA::(_,_)ta) q \<equiv> {p. (q, p) \<in> (ta_eps TA)\<^sup>*}"
definition [simp]: "op_ta_eps_icl (TA::(_,_)ta) q \<equiv> {p. (p, q) \<in> (ta_eps TA)\<^sup>*}"

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "{p. (q, p) \<in> (ta_eps TA)\<^sup>*} \<equiv> op_ta_eps_cl$TA$q"
  "{p. (p, q) \<in> (ta_eps TA)\<^sup>*} \<equiv> op_ta_eps_icl$TA$q"
by simp_all
end

lemma eps_cl_refine[autoref_rules]:
  "(ta_eps_cl_impl, op_ta_eps_cl) \<in> dflt_ta_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  "(ta_eps_icl_impl, op_ta_eps_icl) \<in> dflt_ta_rel \<rightarrow> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  by (auto simp: dflt_ta_rel_def dest: fun_relD)

consts i_TA :: "interface"
lemmas [autoref_rel_intf] = REL_INTFI[of dflt_ta_rel i_TA]

lemma [autoref_itype]:
  "op_ta_eps_cl ::\<^sub>i i_TA \<rightarrow>\<^sub>i Q \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_set"
  "op_ta_eps_icl ::\<^sub>i i_TA \<rightarrow>\<^sub>i Q \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_set"
  "ta_rules ::\<^sub>i i_TA \<rightarrow>\<^sub>i \<langle>\<langle>F,Q\<rangle>\<^sub>ii_ta_rule\<rangle>\<^sub>ii_set"
  "ta_eps ::\<^sub>i i_TA \<rightarrow>\<^sub>i \<langle>\<langle>Q,Q\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_set"
  "ta_final ::\<^sub>i i_TA \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_set"
  "ta_rhs_states ::\<^sub>i i_TA \<rightarrow>\<^sub>i \<langle>Q\<rangle>\<^sub>ii_set"
  "ta_idx ::\<^sub>i i_TA \<rightarrow>\<^sub>i \<langle>\<langle>Q,i_nat\<rangle>\<^sub>ii_prod, \<langle>\<langle>\<langle>Q\<rangle>\<^sub>ii_list,Q\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_set\<rangle>\<^sub>ii_map"
by simp_all

subsection \<open>Auxiliary lemmas and autoref setup for some basic functions\<close>

lemma finite_dom_rbt_lookup [simp, intro!]: "finite (dom (ord.rbt_lookup (comp2lt compare_res) t))"
proof (induct t)
  case Empty then show ?case by (simp add: ord.rbt_lookup.simps)
next
  case (Branch color t1 a b t2)
  let ?lu = "ord.rbt_lookup (comp2lt compare_res)"
  let ?A = "Set.insert a (dom (?lu t1) \<union> dom (?lu t2))"
  have "dom (?lu (Branch color t1 a b t2)) \<subseteq> ?A"
  using comparator.nGt_le_conv comparator.nLt_le_conv comparator_compare 
  by (fastforce
      split: if_splits comp_res.splits
      simp: ord.rbt_lookup.simps comp2lt_def comp2le_def compare_res_def
      elim!: comp_res_of_order.elims)
  moreover from Branch have "finite (insert a (dom (?lu t1) \<union> dom (?lu t2)))" by simp
  ultimately show ?case by (rule finite_subset)
qed

lemma finite_comp_rm_rel[simp, intro!]:
  "(c, a) \<in> \<langle>Rk, Rv\<rangle>comp_rm_rel \<Longrightarrow> finite (dom a)"
by (auto simp: rbt_map_rel_def rbt_map_rel'_def br_def)

lemma finite_comp_rs_rel[simp, intro]:
  "(c, a) \<in> \<langle>A\<rangle>comp_rs_rel \<Longrightarrow> finite a"
by (auto simp add: map2set_rel_def)

lemma option_bind_ref[autoref_rules, param]:
  "(Option.bind, Option.bind) \<in>  \<langle>Ra\<rangle>option_rel \<rightarrow> (Ra \<rightarrow> \<langle>Rb\<rangle>option_rel) \<rightarrow> \<langle>Rb\<rangle>option_rel"
unfolding Option.bind_def by parametricity

lemma option_mapm_ref[autoref_rules, param]:
  "(mapM, mapM) \<in> (Ra \<rightarrow> \<langle>Rb\<rangle>option_rel) \<rightarrow> \<langle>Ra\<rangle>list_rel \<rightarrow> \<langle>\<langle>Rb\<rangle>list_rel\<rangle>option_rel"
proof (intro fun_relI, goal_cases)
  case (1 f f' l l')
  then show ?case by (induction l' arbitrary: l, auto elim!: list_relE option_relE) parametricity
qed

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "\<forall>x\<in>set l. P x \<equiv> list_all_rec$P$l"
by (simp add: list_all_rec_eq)
end

lemma list_all_rec_autoref[autoref_rules]:
  "(list_all_rec, list_all_rec) \<in> (A \<rightarrow> bool_rel) \<rightarrow> \<langle>A\<rangle>list_rel \<rightarrow> bool_rel"
unfolding list_all_rec_def
by parametricity

fun list_all2_rec where
  "list_all2_rec f (x#xs) (y#ys) = ((f x y) \<and> list_all2_rec f xs ys)"
| "list_all2_rec f [] ys = (ys = [])"
| "list_all2_rec f xs [] = (xs = [])"

lemma list_all2_autoref[autoref_rules]:
  "(list_all2, list_all2) \<in> (J \<rightarrow> K \<rightarrow> bool_rel) \<rightarrow> \<langle>J\<rangle>list_rel \<rightarrow> \<langle>K\<rangle>list_rel \<rightarrow> bool_rel"
proof (intro fun_relI, goal_cases)
case (1 f f' l1 l1' l2 l2')
  then show ?case proof (induction f l1 l2 arbitrary: l1' l2' rule: list_all2_rec.induct)
  case prems: (1 f x xs y ys)
    from this obtain x' xs' y' ys' where
      xs: "l1' = x'#xs'" "(xs,xs') \<in> \<langle>J\<rangle>list_rel" and x: "(x,x') \<in> J" and 
      ys: "l2' = y'#ys'" "(ys,ys') \<in> \<langle>K\<rangle>list_rel" and y: "(y,y') \<in> K" by (auto elim!: list_relE3)
    with prems have "(list_all2 f xs ys, list_all2 f' xs' ys') \<in> bool_rel" by blast
    with prems x y show ?case by (simp only: list.simps xs ys, parametricity)
  qed auto
qed

definition [simp]: "op_union_image S f \<equiv> \<Union>(f ` S)"
definition "union_image_ref S f \<equiv> FOREACH S (\<lambda>s r. RETURN (f s \<union> r)) {}"

context begin interpretation autoref_syn .
lemma [autoref_op_pat]: 
  "\<Union>(f ` S) \<equiv> op_union_image$S$f"
by simp_all
end

lemma union_image_ref:
  assumes "finite S"
    shows "union_image_ref S f \<le> RETURN(op_union_image S f)"
unfolding union_image_ref_def
by (refine_vcg FOREACH_rule[where I = "\<lambda>it r. r = op_union_image (S - it) f"], auto intro: assms)

(* FIXME: provide generic implementation by using GEN_OP et al. *)
schematic_goal union_image_rs_aux:
  assumes [autoref_rules]: "(S',S) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(f',f) \<in> Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel"
  shows "(?f::?'a, union_image_ref S f) \<in> ?R"
unfolding union_image_ref_def[abs_def]
by (autoref_monadic (plain))

concrete_definition union_image_rs_code uses union_image_rs_aux

lemma union_image_rs_autoref[autoref_rules]:
  assumes "PREFER_id A" "PREFER_id B"
    shows "(union_image_rs_code,op_union_image) \<in> \<langle>A\<rangle>comp_rs_rel \<rightarrow> (A \<rightarrow> \<langle>B\<rangle>comp_rs_rel) \<rightarrow> \<langle>B\<rangle>comp_rs_rel"
proof (intro fun_relI, goal_cases)
  have[simp]: "ord.rbt_lookup (<) = rbt_lookup"  unfolding ord.rbt_lookup_def rbt_lookup_def ..
  from assms have id[simp]: "A = Id" "B = Id" by simp_all
  case rel: (1 S S')
    then have fin: "finite S'" by blast
    note union_image_rs_code.refine[OF rel[unfolded id], THEN nres_relD]
    also note union_image_ref[OF fin]
    finally show ?case by simp
qed

lemmas fun_relD1' = fun_relD
lemmas fun_relD2' = fun_relD1'[THEN fun_relD]
lemmas fun_relD3' = fun_relD2'[THEN fun_relD]
lemmas fun_relD4' = fun_relD3'[THEN fun_relD]
lemmas fun_relD5' = fun_relD4'[THEN fun_relD]
lemmas fun_relD6' = fun_relD5'[THEN fun_relD]

(* FIXME: move? where? *)
lemma swap_converse: "prod.swap ` A = A\<inverse>" by auto

subsection \<open>Refinement of the ta record constructor (aka ta.make)\<close>

definition ta_idx_rhs_init where
  "ta_idx_rhs_init rs det efcl \<equiv>
    FOREACH rs (\<lambda>r (idx,det,rhs). RETURN (case r of TA_rule f qs q \<Rightarrow>
      let n = length qs in
        (case idx (f,n) of
          None \<Rightarrow> (idx((f,n) \<mapsto> {(qs,q)}), det, efcl q \<union> rhs)
        | Some rs \<Rightarrow>
            (idx((f,n) \<mapsto> insert (qs,q) rs),
            if det then \<forall>(qs',q') \<in> rs. qs \<noteq> qs' else False,
            efcl q \<union> rhs)))
    ) (Map.empty, det, {})"

definition "memo_rtrancl_rel Q \<equiv> Q \<rightarrow> \<langle>Q\<rangle>comp_rs_rel"

schematic_goal ta_idx_rhs_init_aux:
  "(?f, ta_idx_rhs_init) \<in>
    \<langle>\<langle>Id, Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel \<rightarrow>
    bool_rel \<rightarrow> (Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel) \<rightarrow> \<langle>dflt_ta_idx_rel \<times>\<^sub>r bool_rel \<times>\<^sub>r \<langle>Id\<rangle>comp_rs_rel\<rangle>nres_rel"
  unfolding ta_idx_rhs_init_def[abs_def] by (autoref (keep_goal))

lemma r_rhs_unfold: "r_rhs = case_ta_rule (\<lambda>_ _ q. q)" by (auto simp: fun_eq_iff split: ta_rule.split)

lemma ta_diff_aux_simps[simp]:
  "ta_idx (ta_diff TA (ta_rules TA)) = Map.empty"
  "ta_det (ta_diff TA (ta_rules TA)) = (ta_eps TA = {})"
unfolding ta_diff_def ta_idx_def ta_det_def by auto

lemma ta_det_it:
  assumes "TA_rule f qs q \<in> it" "it \<subseteq> ta_rules TA"
    shows "ta_det (ta_diff TA (it - {TA_rule f qs q})) =
            (ta_det (ta_diff TA it) \<and>
              (case (ta_idx (ta_diff TA it)) (f, length qs) of
                None \<Rightarrow> True 
              | Some rs \<Rightarrow> \<forall>(qs',q') \<in> rs. qs \<noteq> qs'))"
using assms by (simp add: it_step_insert_iff ta_det_def ta_idx_def ta_diff_rules, auto) blast

lemma ta_idx_it_none:
  assumes "TA_rule f qs q \<in> it" "it \<subseteq> ta_rules TA"
      and "ta_idx (ta_diff TA it) (f, length qs) = None"
    shows "ta_idx (ta_diff TA (it - {TA_rule f qs q})) =
            (ta_idx (ta_diff TA it))((f, length qs) \<mapsto> {(qs,q)})"
using assms by (auto simp: it_step_insert_iff ta_idx_def ta_diff_rules fun_eq_iff split: if_splits)

lemma ta_idx_it_some:
  assumes "TA_rule f qs q \<in> it" "it \<subseteq> ta_rules TA"
      and "ta_idx (ta_diff TA it) (f, length qs) = Some rs"
    shows "ta_idx (ta_diff TA (it - {TA_rule f qs q})) =
            (ta_idx (ta_diff TA it))((f, length qs) \<mapsto> insert (qs,q) rs)"
using assms by (auto simp: it_step_insert_iff ta_idx_def ta_diff_rules fun_eq_iff split: if_splits)

lemma ta_rhs_states_it:
  assumes "TA_rule f qs q \<in> it" "it \<subseteq> ta_rules TA"
    shows "ta_rhs_states (ta_diff TA (it - {TA_rule f qs q})) =
            ta_rhs_states (ta_diff TA it) \<union> op_ta_eps_cl TA q"
using assms by (auto simp: it_step_insert_iff ta_rhs_states_def ta_diff_rules)

lemma ta_idx_rhs_init:
  assumes fin: "finite (ta_rules TA)"
      and eps: "\<And>q. efcl q \<equiv> op_ta_eps_cl TA q"
    shows "ta_idx_rhs_init (ta_rules TA) (ta_eps TA = {}) efcl \<le> RETURN(ta_idx TA, ta_det TA, ta_rhs_states TA)"
proof -
  note rules =
    FOREACH_rule[where I = 
        "\<lambda>it (idx,det,rhs).
          let TA = (ta_diff TA it) in
            idx = ta_idx TA \<and> det = ta_det TA \<and> rhs = ta_rhs_states TA", OF fin, unfolded Let_def]
  note simps = Let_def ta_det_it ta_idx_it_none ta_idx_it_some ta_rhs_states_it
  note splits = ta_rule.splits option.splits if_splits
  show ?thesis unfolding ta_idx_rhs_init_def eps
  by (refine_vcg rules; auto simp: simps split: splits)
qed

concrete_definition ta_idx_rhs_init_impl uses ta_idx_rhs_init_aux
lemmas [autoref_rules] = ta_idx_rhs_init_impl.refine

schematic_goal ta_idx_rhs_init_transfer_aux: 
  "RETURN ?c \<le> ta_idx_rhs_init_impl rs det efcl"
unfolding ta_idx_rhs_init_impl_def
by (refine_transfer (post))

concrete_definition ta_idx_rhs_init_code for rs efcl uses ta_idx_rhs_init_transfer_aux
lemmas [refine_transfer] = ta_idx_rhs_init_code.refine

definition memo_rtrancl where
  "memo_rtrancl S x \<equiv> {y. (x, y) \<in> S\<^sup>*}"

lemma memo_rtrancl_autoref[autoref_rules]:
  fixes R :: "('a::compare_order \<times> 'a) set"
  assumes "PREFER_id R"             
  shows "(\<lambda>r s. RBT.impl_of (memo_rbt_rtrancl r s), memo_rtrancl) \<in> \<langle>R \<times>\<^sub>r R\<rangle>list_set_rel \<rightarrow> R \<rightarrow> \<langle>R\<rangle>comp_rs_rel"
using memo_rbt_rtrancl comparator_compare assms
by (auto simp: memo_rtrancl_def[abs_def] rbt_map_rel_simps rbt_comp_post_simps icf_rec_unf 
                lookup.rep_eq rs_sbm.\<alpha>_def rbt_comp_lookup_compare_order list_set_rel_def)
   (simp add: ord_defs)

definition ta_make where
  "ta_make F R E \<equiv>
    let efcl = memo_rtrancl E in do {
    (idx,det,rhs) \<leftarrow> ta_idx_rhs_init R (E = {}) efcl;
      RETURN
      (F, R, E,
        rhs, idx, det,
        efcl, memo_rtrancl (prod.swap ` E))
    }"

lemma ta_make_correct:
  assumes "finite R"
  shows "ta_make F R E \<le>
          SPEC(\<lambda>(F',R',E',rhs,idx,det,efcl,eicl). let TA = ta.make F R E in
            F = F' \<and> R = R' \<and> E = E' \<and>
            rhs = ta_rhs_states TA \<and> idx = ta_idx TA \<and> det = ta_det TA \<and>
            efcl = op_ta_eps_cl TA \<and> eicl = op_ta_eps_icl TA)"
proof -
  note ta.make_def[simp]
  from assms have fin: "finite (ta_rules (ta.make F R E))" by simp
  have eps: "\<And>q. memo_rtrancl E q \<equiv> op_ta_eps_cl (ta.make F R E) q" by (simp add: memo_rtrancl_def)
  note rule = ta_idx_rhs_init[OF fin eps, simplified]
  show ?thesis unfolding ta_make_def
  by (refine_vcg rule[THEN order_trans], auto simp: memo_rtrancl_def[abs_def] swap_converse)
     (auto simp: fun_eq_iff intro: rtrancl_converseI dest: rtrancl_converseD)
qed

schematic_goal ta_make_aux:
  assumes [autoref_rules]: "(F',F) \<in> \<langle>Id\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(R',R) \<in> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel"
  assumes [autoref_rules]: "(E',E::('b::compare_order\<times>_) set) \<in> \<langle>Id \<times>\<^sub>r Id\<rangle>list_set_rel"
  shows "(?f, ta_make F R E) \<in> \<langle>
      \<langle>Id\<rangle>comp_rs_rel \<times>\<^sub>r \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel \<times>\<^sub>r \<langle>Id \<times>\<^sub>r Id\<rangle>list_set_rel \<times>\<^sub>r
      \<langle>Id\<rangle>comp_rs_rel \<times>\<^sub>r dflt_ta_idx_rel \<times>\<^sub>r Id \<times>\<^sub>r
      (Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel) \<times>\<^sub>r (Id \<rightarrow> \<langle>Id\<rangle>comp_rs_rel)
    \<rangle>nres_rel"
unfolding ta_make_def[abs_def] prod.swap_def[abs_def] Let_def
by (autoref_monadic (plain))

concrete_definition ta_make_code uses ta_make_aux

lemma ta_make_autoref[autoref_rules]:
  shows "(ta_make_code, ta.make) \<in> \<langle>Id\<rangle>comp_rs_rel \<rightarrow> \<langle>\<langle>Id,Id\<rangle>ta_rule_rel\<rangle>comp_rs_rel \<rightarrow> \<langle>Id \<times>\<^sub>r Id\<rangle>list_set_rel \<rightarrow> dflt_ta_rel"
proof (intro fun_relI, goal_cases)
  case rel: (1 _ _ R R')
    then have fin: "finite R'" by simp
    note ta_make_code.refine[OF rel[unfolded rel], THEN nres_relD]
    also note ta_make_correct[OF fin]
    finally show ?case
      by (auto simp add: dflt_ta_rel_def RETURN_RES_refine_iff Let_def ta.make_def elim!: prod_relE)
         (auto dest!: fun_relD)
qed

lemma [autoref_itype]:
  "ta.make ::\<^sub>i \<langle>Q\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>\<langle>F,Q\<rangle>\<^sub>ii_ta_rule\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i \<langle>\<langle>Q,Q\<rangle>\<^sub>ii_prod\<rangle>\<^sub>ii_set \<rightarrow>\<^sub>i i_TA"
by simp

end
