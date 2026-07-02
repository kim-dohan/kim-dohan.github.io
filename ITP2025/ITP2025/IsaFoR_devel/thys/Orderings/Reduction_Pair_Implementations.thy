(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Reduction_Pair_Implementations
imports
  Matrix_Poly
  Argument_Filter
  Poly_Order
  Poly_Order_Neg
  CoWPO_Impl
  RPO_Impl
  SPO_Impl
  SCNP_Impl
  List_Order_Implementations
  Weighted_Path_Order.Multiset_Extension2_Impl
  KBO_Impl
  Ackbo_Impl
  WPO_Impl
  GWPO_Impl
  Monotone_Algebra
  Max_Polynomial_Impl
  Max_Monus_Impl
  Sqrt_Babylonian.Sqrt_Babylonian
  Auxx.Map_Choice
  Matrix_TRS_Impl
begin

hide_const (open) Transcendental.pi 
hide_const (open) DAList_Multiset.join
hide_const (open) Almost_Full.af

datatype (dead 'f) redtriple_impl =
    Int_carrier "('f, int) lpoly_interL"
    | Int_nl_carrier "('f, int) poly_inter_list"
    | Neg_Integer_Poly "('f, int) poly_inter_list"
  | Rat_carrier "('f, rat) lpoly_interL"
  | Rat_nl_carrier rat "('f, rat) poly_inter_list"
  | Real_carrier "('f, real) lpoly_interL"
  | Real_nl_carrier real "('f, real) poly_inter_list"
  | Arctic_carrier "('f, arctic) lpoly_interL"
  | Arctic_rat_carrier "('f, rat arctic_delta) lpoly_interL"
  | Int_mat_carrier nat nat "('f, int mat) lpoly_interL"
  | Rat_mat_carrier nat nat "('f, rat mat) lpoly_interL"
  | Real_mat_carrier nat nat "('f, real mat) lpoly_interL"
  | Core_matrix "'f core_matrix_inter" 
  | Arctic_mat_carrier nat "('f, arctic mat) lpoly_interL"
  | Arctic_rat_mat_carrier nat "('f, rat arctic_delta mat) lpoly_interL"
  | RPO "'f status_prec_repr" "'f afs_list"
  | KBO "'f prec_weight_repr" "'f afs_list"
  | ACKBO "'f prec_weight_ac_repr" "'f afs_list"
  | WPO "'f wpo_params" "'f redtriple_impl"
  | GWPO "'f gwpo_params" "'f redtriple_impl"
  | MSPO "'f redtriple_impl"
  | COWPO "'f wpo_params" "'f redtriple_impl"
  | Max_poly "('f, max_poly.sig) encoder_inter"
  | Max_monus "('f, max_monus.sig) encoder_inter"
  | Filtered_Redtriple "'f afs_list" "'f redtriple_impl"
  | SCNP list_order_type "'f scnp_af" "'f redtriple_impl"

definition faulty_non_inf_order :: "String.literal \<Rightarrow> 'a \<Rightarrow> ('f :: showl, 'v :: showl) non_inf_order"
where
  "faulty_non_inf_order s F = \<lparr>
    non_inf_order.valid = error (showsl_lit s),
    ns = \<lambda> _. succeed,
    cc = \<lambda> _. succeed,
    af = \<lambda> _ _. Wild,
    desc = id \<rparr>"

lemma faulty_non_inf_order: "generic_non_inf_order_impl faulty_non_inf_order"
  by (unfold_locales) (simp add: faulty_non_inf_order_def)

fun filter_prec_weight_repr :: "('f \<times> nat \<Rightarrow> af_entry) \<Rightarrow> 'f prec_weight_repr \<Rightarrow> 'f filtered prec_weight_repr"
where
 "filter_prec_weight_repr \<pi> (prw, w0) = (
    let
      fprw = filter (\<lambda> (fn, e). case \<pi> fn of Collapse _ \<Rightarrow> False | AFList _ \<Rightarrow> True) prw;
      mprw = map (\<lambda> ((f, n), e).
        ((FPair f n, case \<pi> (f, n) of AFList l \<Rightarrow> length l | Collapse _ \<Rightarrow> 0), e)) fprw
    in (mprw, w0))"

fun filter_prec_weight_ac_repr :: "('f \<times> nat \<Rightarrow> af_entry) \<Rightarrow> 'f prec_weight_ac_repr \<Rightarrow> 'f filtered prec_weight_ac_repr"
where
 "filter_prec_weight_ac_repr \<pi> (prw, w0) = (
    let
      fprw = filter (\<lambda> (fn, e). case \<pi> fn of Collapse _ \<Rightarrow> False | AFList _ \<Rightarrow> True) prw;
      mprw = map (\<lambda> ((f, n), e).
        ((FPair f n, case \<pi> (f, n) of AFList l \<Rightarrow> length l | Collapse _ \<Rightarrow> 0), e)) fprw
    in (mprw, w0))"

fun prec_repr_to_pr :: "'f status_prec_repr \<Rightarrow> ('f :: compare_order) filtered \<times> nat \<Rightarrow> nat"
where
  "prec_repr_to_pr prs = (
    let m = ceta_map_of prs in (\<lambda> (fp,n).
      (case fp of 
        FPair f a \<Rightarrow>
        (case m (f, a) of
          None \<Rightarrow> 0
        | Some x \<Rightarrow> fst x))))" 

fun prec_repr_to_status :: "'f status_prec_repr \<Rightarrow> ('f :: compare_order) filtered \<times> nat \<Rightarrow> order_tag"
where
  "prec_repr_to_status prs = (
    let m = ceta_map_of prs in (\<lambda> (fp,n).
      (case fp of
        FPair f a \<Rightarrow>
        (case m (f, a) of
          None \<Rightarrow> Lex
        | Some x \<Rightarrow> snd x))))"

primrec get_rel_impl :: "('f :: {compare_order, showl}) redtriple_impl \<Rightarrow> ('f, string) rel_impl"
where 
  "get_rel_impl (Int_carrier I) = int_rel_impl I" 
| "get_rel_impl (Neg_Integer_Poly I) = create_negpoly_rel_impl (do {_ \<leftarrow> check_poly_inter_list_neg I; return ()}) (0 :: int) (>) True I" 
| "get_rel_impl (Int_nl_carrier I) = create_nlpoly_rel_impl succeed (1 :: int) (>) True True I"
| "get_rel_impl (Rat_carrier I) = delta_rel_impl 1 I"
| "get_rel_impl (Rat_nl_carrier d I) = delta_nl_rel_impl d I"
| "get_rel_impl (Real_carrier I) = delta_rel_impl 1 I" 
| "get_rel_impl (Real_nl_carrier d I) = delta_nl_rel_impl d I"
| "get_rel_impl (Arctic_carrier I) = arctic_rel_impl I"
| "get_rel_impl (Arctic_rat_carrier I) = arctic_delta_rel_impl I"
| "get_rel_impl (Int_mat_carrier n sd I) = int_mat_rel_impl n sd I"
| "get_rel_impl (Rat_mat_carrier n sd I) = delta_mat_rel_impl n sd 1 I"
| "get_rel_impl (Real_mat_carrier n sd I) = delta_mat_rel_impl n sd 1 I"
| "get_rel_impl (Arctic_mat_carrier n I) = arctic_mat_rel_impl n I"
| "get_rel_impl (Core_matrix mI) = create_core_matrix_rel_impl mI"
| "get_rel_impl (Arctic_rat_mat_carrier n I) = arctic_delta_mat_rel_impl n I" 
| "get_rel_impl (Max_poly alist) = max_poly_rel_impl (Max_Poly_Impl BB_Solver alist)"
| "get_rel_impl (Max_monus alist) = max_monus_rel_impl (Max_Monus_Impl BB_Solver alist)"
| "get_rel_impl (RPO prec\<tau> pi) =
    filtered_rel_impl pi (create_RPO_rel_impl
      (\<lambda> pr. (prec_repr_to_pr pr, prec_repr_to_status pr)) prec\<tau>)"
| "get_rel_impl (KBO precw pi) =
    filtered_rel_impl pi (create_KBO_rel_impl (filter_prec_weight_repr (afs_of' pi)) precw)"
| "get_rel_impl (ACKBO precw pi) =
    filtered_rel_impl pi (create_ACKBO_rel_impl (filter_prec_weight_ac_repr (afs_of' pi)) precw)"
| "get_rel_impl (WPO params rp) = wpo_rel_impl (get_rel_impl rp) params"
| "get_rel_impl (GWPO params rp) = gwpo_rel_impl (get_rel_impl rp) params"
| "get_rel_impl (MSPO rp) = mspo_rel_impl (get_rel_impl rp)"
| "get_rel_impl (COWPO params rp) = cowpo_rel_impl (get_rel_impl rp) params"
| "get_rel_impl (Filtered_Redtriple alist rp) = 
    filtered_rel_impl_af alist (get_rel_impl rp)"
| "get_rel_impl (SCNP type af rp) = 
     generate_scnp_rp (list_ext (scnp_arity af) type) (showsl_lit (list_ext_name type)) af (get_rel_impl rp)" 

lemma get_rel_impl: "rel_impl (get_rel_impl rp)" 
proof (induct rp)
  case Int_carrier
  show ?case unfolding get_rel_impl.simps by (rule int_rel_impl)
next
  case Int_nl_carrier
  interpret mono_matrix_carrier "(>)" 1 nat int_mono by (rule int_complexity)
  have carr: "cpx_poly_order_carrier (1 :: int) (>) True True nat" ..
  show ?case unfolding get_rel_impl.simps
    by (intro poly_order_carrier_with_create_nlpoly_rel_impl[OF carr])
next
  case (Neg_Integer_Poly I)
  interpret order_pair_neg "(>)::int\<Rightarrow>int\<Rightarrow>bool" UNIV 
    by (simp add: order_pair_neg_def)
  show ?case unfolding get_rel_impl.simps
    by (intro poly_order_neg_carrier_with_create_nlpoly_rel_impl[OF poly_order_neg_lemmma refl], auto)
next
  case Rat_carrier
  show ?case unfolding get_rel_impl.simps
    by (rule create_poly_rel_impl[OF class_lpoly_order[OF delta_weak_complexity]])
next
  case Rat_nl_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro poly_order_carrier_with_create_nlpoly_rel_impl[OF delta_cpx_poly_order_carrier],
      simp add: check_def_pos_def)
next
  case Real_carrier
  show ?case unfolding get_rel_impl.simps
    by (rule create_poly_rel_impl[OF class_lpoly_order[OF delta_weak_complexity]])
next
  case Real_nl_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro poly_order_carrier_with_create_nlpoly_rel_impl[OF delta_cpx_poly_order_carrier],
      simp add: check_def_pos_def)
next
  case Arctic_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro create_poly_rel_impl[OF class_arc_lpoly_order[OF arctic_weak_carrier]])
next
  case Arctic_rat_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro create_poly_rel_impl[OF class_arc_lpoly_order[OF arctic_delta_weak_carrier]])
next
  case Int_mat_carrier
  show ?case unfolding get_rel_impl.simps by (rule int_mat_rel_impl)
next
  case Rat_mat_carrier
  show ?case unfolding get_rel_impl.simps
    by (rule create_poly_rel_impl[OF mat_lpoly_order[OF delta_weak_complexity]])
next
  case Real_mat_carrier
  show ?case unfolding get_rel_impl.simps
    by (rule create_poly_rel_impl[OF mat_lpoly_order[OF delta_weak_complexity]])
next
  case Arctic_mat_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro create_poly_rel_impl[OF mat_arc_lpoly_order[OF arctic_weak_carrier]])
next
  case Arctic_rat_mat_carrier
  show ?case unfolding get_rel_impl.simps
    by (intro create_poly_rel_impl[OF mat_arc_lpoly_order[OF arctic_delta_weak_carrier]])
next
  case RPO
  show ?case unfolding get_rel_impl.simps
    by (intro filtered_rel_impl create_RPO_rel_impl)
next
  case KBO
  show ?case unfolding get_rel_impl.simps
    by (intro filtered_rel_impl create_KBO_rel_impl)
next
  case ACKBO
  show ?case unfolding get_rel_impl.simps
    by (intro filtered_rel_impl create_ACKBO_rel_impl)
next
  case *: WPO
  show ?case unfolding get_rel_impl.simps
    by (intro wpo_rel_impl *)
next
  case *: GWPO
  show ?case unfolding get_rel_impl.simps
    by (intro gwpo_rel_impl *)
next
  case *: MSPO
  show ?case unfolding get_rel_impl.simps
    by (intro mspo_rel_impl *)
next
  case *: COWPO
  show ?case unfolding get_rel_impl.simps
    by (intro cowpo_rel_impl *)
next
  case Max_poly
  show ?case unfolding get_rel_impl.simps
    by (intro max_poly_rel_impl)
next
  case Max_monus
  show ?case unfolding get_rel_impl.simps
    by (intro max_monus_rel_impl)
next
  case *: Filtered_Redtriple
  show ?case unfolding get_rel_impl.simps
    by (intro filtered_rel_impl_af, rule *)
next
  case *: SCNP
  show ?case unfolding get_rel_impl.simps
    by (rule generate_scnp_rp[OF * list_ext])
next
  case *: Core_matrix
  show ?case unfolding get_rel_impl.simps
    by (rule create_core_matrix_rel_impl)
qed

lift_definition default_rel_impl :: "('f :: {compare_order, showl},string,'f redtriple_impl)rel_impl_type" is get_rel_impl
  by (rule get_rel_impl)

definition sqrt_real :: "real \<Rightarrow> real list"
  where
    "sqrt_real x = (if x \<ge> 0 then let y = sqrt x in remdups [y, -y] else [])"

lemma sqrt_real[simp]: "set (sqrt_real x) = {y. y * y = x}"
  unfolding sqrt_real_def Let_def 
  by (cases "x \<ge> 0", auto)

fun
  get_non_inf_order ::
    "('f :: {compare_order, showl}) redtriple_impl \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f,'v :: {showl,linorder}) non_inf_order"
where 
  "get_non_inf_order (Int_nl_carrier I) =
    create_nlpoly_non_inf_order succeed (1 :: int) (>) True True sqrt_int I"
| "get_non_inf_order (Rat_nl_carrier d I) = delta_non_inf_order d sqrt_rat I"
| "get_non_inf_order (Real_nl_carrier d I) = delta_non_inf_order d sqrt_real I"
| "get_non_inf_order _ =
    faulty_non_inf_order (STR ''only integers, rationals and reals are supported for non-inf orders'')"

lemma get_non_inf_order:
  "generic_non_inf_order_impl get_non_inf_order"
proof
  fix rp :: "('f :: {compare_order, showl}) redtriple_impl"
    and F and ns_list :: "('f, 'v :: {showl, linorder}) rules" and cc
  let ?rp = "get_non_inf_order rp F :: ('f, 'v) non_inf_order"
  assume v: "isOK (non_inf_order.valid ?rp)"
    and cc: "isOK (check_allm (non_inf_order.cc ?rp) cc)"
    and NS: "isOK (check_allm (non_inf_order.ns ?rp) ns_list)"
  show "\<exists> S NS.
    non_inf_order_trs S NS (set F) (non_inf_order.af ?rp) \<and>
    set ns_list \<subseteq> NS \<and> Ball (set cc) (cc_satisfied (set F) S NS)"
  proof (cases rp)
    case (Int_nl_carrier I)
    then have id: "?rp = (create_nlpoly_non_inf_order succeed (1 :: int) (>) True True sqrt_int) I F"
      (is "_ = ?I I F") by simp
    have "non_inf_poly_order_carrier (1 :: int) (>) True True" 
      by (unfold_locales, insert non_inf_int_gt, auto simp: mult_right_mono_neg)
    from non_inf_poly_order_carrier_to_generic_non_inf_order[OF this]
      have rp: "generic_non_inf_order_impl ?I" .
    show ?thesis by (simp only: id, rule generic_non_inf_order_impl.generate_non_inf_order[of ?I, OF rp  v[simplified id] NS[simplified id] cc[simplified id]]) 
  next
    case (Rat_nl_carrier d I)
    then have id: "?rp = (delta_non_inf_order d sqrt_rat) I F" by simp
    show ?thesis unfolding id
      by (rule generic_non_inf_order_impl.generate_non_inf_order[OF delta_non_inf_order], insert NS v cc id, auto) 
  next
    case (Real_nl_carrier d I)
    then have id: "?rp = (delta_non_inf_order d sqrt_real) I F" by simp
    show ?thesis unfolding id
      by (rule generic_non_inf_order_impl.generate_non_inf_order[OF delta_non_inf_order], insert NS v cc id, auto) 
  qed (insert v, auto simp: faulty_non_inf_order_def)
qed

end
