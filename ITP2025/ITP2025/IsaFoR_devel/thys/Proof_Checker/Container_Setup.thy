(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015)
Author:  Makarius Wenzel <makarius@sketis.net> (2013)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Container_Setup
imports 
  "Abstract-Rewriting.SN_Order_Carrier"
  Simplex.Simplex
  Containers.Containers
(*  Algebraic_Numbers.Complex_Algebraic_Numbers *)
  Jordan_Normal_Form.Matrix_IArray_Impl
  Ord.Linear_Polynomial
  TRS.Forbidden_Patterns
  TA.Tree_Automata_Det_Container
  LTS.Cooperation_Program
  Ord.Integer_Arithmetic
  Sem_Lab.Labelings_Impl
  TRS.Ground_Context_Impl
  Polynomial_Interpolation.Is_Rat_To_Rat
  Ord.Argument_Filter
begin

  
(* LTS *)
derive compare IA.sig IA.ty
derive ccompare sharp formula trans_var transition_rule IA.sig IA.ty IA.val
derive (rbt) mapping_impl sharp formula trans_var transition_rule IA.sig IA.ty IA.val
derive (eq) ceq sharp formula trans_var transition_rule IA.sig IA.ty IA.val
derive (rbt) set_impl sharp formula trans_var transition_rule IA.sig IA.ty
derive (dlist) set_impl IA.val
derive (no) cenum sharp formula trans_var transition_rule IA.sig IA.ty IA.val

(* term, etc *)
derive (eq) ceq 
  lab "term" mctxt actxt gctxt location l_poly ta_rule rat arctic arctic_delta
derive compare (* for these types there is already an order defined, so no compare_order poss. *) 
  mctxt arctic arctic_delta
derive compare_order
  actxt location l_poly
derive (linorder) compare rat real
derive (compare) ccompare real
derive (rbt) set_impl real
derive (eq) ceq real
derive (compare) ccompare 
  lab "term" mctxt actxt gctxt location l_poly rat arctic arctic_delta
(* Note that the powerset construction uses sets to represent states. Since we cannot instantiate
 * compare for sets, it's necessary to derive a ccompare instance for ta_rule that does not
 * require compare. *)
derive ccompare 
  ta_rule
derive (rbt) set_impl 
  lab "term" mctxt actxt gctxt location l_poly ta_rule rat arctic arctic_delta
derive (no) cenum 
  lab "term" mctxt actxt gctxt location l_poly ta_rule rat real arctic arctic_delta
derive (rbt) mapping_impl
  lab

instantiation lab :: (type,type)card_UNIV
begin
definition "card_UNIV = Phantom(('a,'b)lab) 0"
definition "finite_UNIV = Phantom(('a,'b)lab) False"
instance
  by (intro_classes, auto simp: finite_UNIV_lab_def card_UNIV_lab_def infinite_lab)
end


instantiation lab :: (compare,compare)cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: ('a,'b)lab option) _ . False)"
instance by (intro_classes, auto simp: infinite_lab)
end


instantiation ta_rule :: (type,type)finite_UNIV
begin
definition "finite_UNIV = Phantom(('a,'b)ta_rule) False"
instance
  by (intro_classes, unfold finite_UNIV_ta_rule_def, simp)
end

instantiation ta_rule :: (ccompare,ccompare)cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: ('a,'b)ta_rule option) _ . False)"
instance by (intro_classes, auto)
end


lemma infinite_term_UNIV[simp, intro]: "infinite (UNIV :: ('f,'v)term set)"
proof -
  fix f :: 'f and v :: 'v
  let ?inj = "\<lambda>n. Fun f (replicate n (Var v))"
  have "inj ?inj" unfolding inj_on_def by auto
  from infinite_super[OF _ range_inj_infinite[OF this]]
  show ?thesis by blast
qed

instantiation "term" :: (type,type)finite_UNIV
begin
definition "finite_UNIV = Phantom(('a,'b)term) False"
instance
  by (intro_classes, unfold finite_UNIV_term_def, simp)
end

instantiation "term" :: (compare,compare)cproper_interval
begin
definition "cproper_interval = (\<lambda> ( _ :: ('a,'b)term option) _ . False)"
instance by (intro_classes, auto)
end

derive (eq) ceq atom QDelta
derive (linorder) compare_order QDelta
derive compare_order atom
derive ccompare atom QDelta
derive (rbt) set_impl atom QDelta

text \<open>code equation to handle @{term Union}\<close>
lemma un_foldr[code_unfold]: "\<Union> (set xs) = foldr (\<union>) xs {}"
  by (induct xs, auto)

declare Lcm_fin.set_eq_fold[code_unfold]


lemma in_ints_code_unfold[code_unfold]: "(x \<in> \<int>) = is_int_rat x"
  by simp

derive compare_order IA.ty

lemma ty_UNIV:  "UNIV = {IA.BoolT, IA.IntT}"
  by (auto intro: IA.ty.exhaust) 

instantiation IA.ty :: card_UNIV
begin
definition "card_UNIV = Phantom(IA.ty) 2"
definition "finite_UNIV = Phantom(IA.ty) True"
instance
  by (intro_classes) ( auto simp: finite_UNIV_ty_def card_UNIV_ty_def ty_UNIV)
end

instantiation IA.ty :: proper_interval begin
fun proper_interval_ty :: "IA.ty proper_interval" where
  "proper_interval_ty (Some x) (Some y) \<longleftrightarrow> False"
| "proper_interval_ty (Some x) None \<longleftrightarrow> (x = IA.BoolT)"
| "proper_interval_ty None (Some y) \<longleftrightarrow> (y = IA.IntT)"
| "proper_interval_ty None None = True"
instance 
proof -
  have a: "comparator_ty z IA.BoolT = Lt \<Longrightarrow> False"  for z
    by (cases z) auto
  have b: "comparator_ty IA.IntT z = Lt \<Longrightarrow> False"  for z
    by (cases z) auto
  have c: "comparator_ty z IA.IntT = Lt \<Longrightarrow> comparator_ty IA.BoolT z = Lt \<Longrightarrow> False" for z :: IA.ty
    by (cases z) auto
  have d: "proper_interval None (Some y) = (\<exists>z. z < y)" for y :: IA.ty
    using a by(cases y)
      (auto simp add:  less_ty_def lt_of_comp_def compare_ty_def intro: exI[of _ IA.BoolT]
        split: order.splits)
  have e: "proper_interval (Some y) None = (\<exists>z. y < z)" for y :: IA.ty
    using b
    by(cases y)
      (auto simp add:  less_ty_def lt_of_comp_def compare_ty_def intro: exI[of _ IA.IntT]
        split: order.splits)
  have f: "proper_interval (Some x) (Some y) = (\<exists>z>x. z < y)" for x y :: IA.ty
    using a b c
    by (cases x, cases y) 
      (auto split: order.splits simp add:  less_ty_def lt_of_comp_def compare_ty_def)
  show "OFCLASS(IA.ty, proper_interval_class)"
    using d e f by intro_classes
      (auto simp add:  less_ty_def lt_of_comp_def compare_ty_def intro: IA.ty.induct)
qed
end

instantiation IA.ty :: cproper_interval begin
definition "cproper_interval_ty = (proper_interval :: IA.ty proper_interval)"
instance 
proof -
  have "class.proper_interval ((<)::IA.ty \<Rightarrow> IA.ty \<Rightarrow> bool) proper_interval"
    using proper_interval_class.axioms by simp
  then show "OFCLASS(IA.ty, cproper_interval_class)"
    using proper_interval_class.axioms
    by(intro_classes)
      (auto simp add: cproper_interval_ty_def ID_def less_ty_def  ccompare_ty_def compare_ty_def)
qed
end

lemma finite_UNIV_trans_var:
  shows "finite (UNIV::'a trans_var set) \<longleftrightarrow> finite (UNIV::'a set)"
proof -
  have "infinite (UNIV::'a trans_var set)" if "infinite (UNIV::'a set)"
  proof -
    have "x \<notin> range Intermediate \<Longrightarrow> x \<notin> range Post \<Longrightarrow> x \<in> range Pre" for x::"'a trans_var"
      by (cases x) auto
    then have a: "range Pre \<subseteq> (UNIV::'a trans_var set)"
      by auto
    have "untrans_var ` (range Pre) = (UNIV::'a set)"
      by (auto simp add: image_image)
    then have b: "infinite (range Pre::'a trans_var set)"
      using that by (metis finite_imageI)
    show ?thesis
      using a b rev_finite_subset by auto
  qed
  moreover have "finite (UNIV::'a trans_var set)" if "finite (UNIV::'a set)" 
  proof -
    have "x \<notin> range Intermediate \<Longrightarrow> x \<notin> range Post \<Longrightarrow> x \<in> range Pre" for x::"'a trans_var"
      by (cases x) auto
    then have a: "(UNIV::'a trans_var set) = range Pre \<union> range Post \<union> range Intermediate"
      by auto
    show ?thesis
      unfolding a using that by blast 
  qed
  ultimately show ?thesis
    by blast
qed

instantiation trans_var :: (finite_UNIV)finite_UNIV
begin
definition "finite_UNIV = Phantom(('a)trans_var) (of_phantom (finite_UNIV :: 'a finite_UNIV))"
instance
  by  (intro_classes) (simp add: finite_UNIV_trans_var_def finite_UNIV finite_UNIV_trans_var)
end

derive "show" sharp lab

derive ceq filtered
derive ccompare filtered


instantiation filtered :: (set_impl) set_impl begin
definition "SET_IMPL('a filtered) = Phantom('a filtered) (of_phantom SET_IMPL('a))"
instance ..
end

end
