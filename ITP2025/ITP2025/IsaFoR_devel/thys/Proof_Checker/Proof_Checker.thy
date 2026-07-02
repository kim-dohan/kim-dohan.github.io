(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory Proof_Checker
  imports
    Check_Termination
    Check_Nontermination
    Check_CRP
    Check_Conditional_CRP
    Check_Completion_Proof
    Check_Equational_Proof
    Check_Complexity
    Check_Quasi_Reductive
    Check_AC_Termination
    LTS.IA_Instance  
    Ceta_Problem_Spec
begin

hide_const (open) eq_object.eq

datatype (dead 'f, dead 'l, dead 'v) "proof" =
  TRS_Termination_Proof "('f, 'l, 'v) trs_termination_proof"
| Complexity_Proof "('f,'l,'v) complexity_proof"
| DP_Termination_Proof "('f, 'l, 'v) dp_termination_proof"
| DP_Nontermination_Proof "('f, 'l, 'v) dp_nontermination_proof"
| TRS_Nontermination_Proof "('f, 'l, 'v) trs_nontermination_proof"
| FP_Termination_Proof "('f,'l,'v) fptrs_termination_proof"
| FP_Nontermination_Proof "('f, 'l, 'v) fp_trs_nontermination_proof"
| Relative_TRS_Nontermination_Proof "('f, 'l, 'v) reltrs_nontermination_proof"
| TRS_Confluence_Proof "('f, 'l, 'v) cr_proof"
| TRS_Non_Confluence_Proof "('f, 'l, 'v, 'v) ncr_proof"
| TRS_Non_Commutation_Proof "('f, 'l, 'v, 'v) ncomm_proof"
| TRS_Commutation_Proof "('f,'l, 'v) comm_proof"
| Completion_Proof "('f, 'l, 'v) completion_proof"
| Ordered_Completion_Proof "(('f,'l) lab, 'v) ordered_completion_proof"
| Equational_Proof "('f, 'l, 'v) equational_proof"
| Equational_Disproof "('f, 'l, 'v) equational_disproof"
| Quasi_Reductive_Proof "('f, 'l, 'v) quasi_reductive_proof"
| Conditional_CR_Proof "('f, 'l, 'v, ('f,'l) lab redtriple_impl) conditional_cr_proof"
| Conditional_Non_CR_Proof "('f, 'l, 'v, 'v, ('f,'l) lab redtriple_impl) conditional_ncr_proof"
| Tree_Automata_Closed_Proof "string ta_relation"
| AC_Termination_Proof "('f,'l,'v) ac_termination_proof"
| LTS_Termination_Proof "(IA.sig, 'v, IA.ty, string, string, la_solver_type) termination_proof"
| LTS_Safety_Proof "(IA.sig, 'v, IA.ty, string, string, string, la_solver_type) safety_proof"
| Infeasibility_Proof "('f, 'v, ('f,'l) lab redtriple_impl, 'l) infeasibility_proof"
| Feasibility_Proof "(('f,'l) lab, 'v) feasibility_proof"
| Unknown_Proof "('f,'l,'v) unknown_proof"
| Unknown_Disproof "('f,'l,'v) neg_unknown_proof"

definition "proof_to_string proof =
  (case proof of
    TRS_Termination_Proof _ \<Rightarrow> STR ''TRS termination proof''
  | Complexity_Proof _ \<Rightarrow> STR ''complexity proof''
  | DP_Termination_Proof _ \<Rightarrow> STR ''DP termination proof''
  | DP_Nontermination_Proof _ \<Rightarrow> STR ''DP nontermination proof''
  | TRS_Nontermination_Proof _ \<Rightarrow> STR ''TRS nontermination proof''
  | FP_Termination_Proof _ \<Rightarrow> STR ''FP TRS termination proof''
  | FP_Nontermination_Proof _ \<Rightarrow> STR ''FP TRS nontermination proof''
  | Relative_TRS_Nontermination_Proof _ \<Rightarrow> STR ''relative TRS nontermination proof''
  | TRS_Confluence_Proof _ \<Rightarrow> STR ''TRS confluence proof''
  | TRS_Non_Confluence_Proof _ \<Rightarrow> STR ''TRS nonconfluence proof''
  | TRS_Non_Commutation_Proof _ \<Rightarrow> STR ''TRS noncommutation proof''
  | TRS_Commutation_Proof _ \<Rightarrow> STR ''TRS commutation proof''
  | Completion_Proof _ \<Rightarrow> STR ''completion proof''
  | Ordered_Completion_Proof _ \<Rightarrow> STR ''ordered completion proof''
  | Equational_Proof _ \<Rightarrow> STR ''equational proof''
  | Equational_Disproof _ \<Rightarrow> STR ''equational disproof''
  | Quasi_Reductive_Proof _ \<Rightarrow> STR ''quasi-reductive proof''
  | Conditional_CR_Proof _ \<Rightarrow> STR ''conditional confluence proof''
  | Conditional_Non_CR_Proof _ \<Rightarrow> STR ''conditional nonconfluence proof''
  | Tree_Automata_Closed_Proof _ \<Rightarrow> STR ''tree automata closed proof''
  | AC_Termination_Proof _ \<Rightarrow> STR ''AC termination proof''
  | LTS_Termination_Proof _ \<Rightarrow> STR ''LTS termination proof''
  | LTS_Safety_Proof _ \<Rightarrow> STR ''LTS safety proof''
  | Infeasibility_Proof _ \<Rightarrow> STR ''Infeasibility proof''
  | Feasibility_Proof _ \<Rightarrow> STR ''Feasibility proof''
  | Unknown_Proof _ \<Rightarrow> STR ''unknown proof''
  | Unknown_Disproof _ \<Rightarrow> STR ''unknown disproof'')"


primrec cert_assms :: "bool \<Rightarrow> ('f, 'l, 'v) proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "cert_assms a (TRS_Termination_Proof p) = sn_assms a p"
| "cert_assms a (FP_Termination_Proof p) = sn_fp_assms a p"
| "cert_assms a (TRS_Confluence_Proof p) = cr_assms a p"
| "cert_assms a (TRS_Non_Confluence_Proof p) = ncr_assms a p"
| "cert_assms a (Completion_Proof p) = completion_assms a p"
| "cert_assms a (Ordered_Completion_Proof p) = []"
| "cert_assms a (DP_Termination_Proof p) = dp_assms a p"
| "cert_assms a (Equational_Proof p) = equational_assms a p"
| "cert_assms a (Equational_Disproof p) = equational_dis_assms a p"
| "cert_assms a (Quasi_Reductive_Proof p) = quasi_reductive_assms a p"
| "cert_assms a (Conditional_CR_Proof p) = conditional_cr_assms a p"
| "cert_assms a (Conditional_Non_CR_Proof p) = conditional_ncr_assms a p"
| "cert_assms a (Unknown_Proof p) = unknown_assms a p"
| "cert_assms a (Unknown_Disproof p) = neg_unknown_assms a p"
| "cert_assms a (Relative_TRS_Nontermination_Proof p) = neg_rel_sn_assms a p"
| "cert_assms a (TRS_Nontermination_Proof p) = neg_sn_assms a p"
| "cert_assms a (FP_Nontermination_Proof p) = neg_fp_assms a p"
| "cert_assms a (DP_Nontermination_Proof p) = neg_dp_assms a p"
| "cert_assms a (Complexity_Proof p) =  complexity_assms a p"
| "cert_assms a (LTS_Termination_Proof _) = []"
| "cert_assms a (LTS_Safety_Proof _) = []"
| "cert_assms a (Infeasibility_Proof _) = []"
| "cert_assms a (Feasibility_Proof _) = []"
| "cert_assms a (Tree_Automata_Closed_Proof _) =  []"
| "cert_assms a (AC_Termination_Proof _) =  []"
| "cert_assms a (TRS_Non_Commutation_Proof p) = []"
| "cert_assms a (TRS_Commutation_Proof p) = comm_assms a p"


lemma cert_assms_False[simp]: "cert_assms False p = []" by (cases p) simp_all

datatype cert_result = Certified | Unsupported String.literal | Error String.literal

context fixes
  I :: "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops" and
  J :: "('dpp, ('f, label_type) lab, string) dpp_ops" and
  K :: "('ac_tp, ('f, label_type) lab, string) ac_tp_ops" and
  L :: "('ac_dpp, ('f, label_type) lab, string) ac_dpp_ops"
begin

definition check_cert
where "check_cert a input property answer proof \<equiv>
  let mismatch = showsl_lit (STR ''\<newline>the combination of input <'' + input_to_string input + 
    STR ''> and property <'' + property_to_string property +
    STR ''> and answer <'' + answer_to_string answer +
    STR ''> and proof <'' + proof_to_string proof +
    STR ''> is not supported by CeTA\<newline>'' 
  );
      triple = (input, property, answer)
  in
  case proof of TRS_Termination_Proof prf \<Rightarrow>
     (case triple of 
     (Inn_TRS_input Q R S, Termination, Decision True)
        \<Rightarrow> check_trs_termination_proof I J a (showsl_lit (STR ''1'')) (tp_ops.mk I (strategy_to_nfs Q) (strategy_to_Q Q R) R S) prf
    | _ \<Rightarrow> error mismatch)
  | TRS_Nontermination_Proof prf \<Rightarrow>
     (case triple of 
       (Inn_TRS_input Q R S, Termination, Decision False) \<Rightarrow>       
              check (S = []) mismatch \<then>
              check_trs_nontermination_proof I J a (showsl_lit (STR ''1'')) (tp_ops.mk I (strategy_to_nfs Q) (strategy_to_Q Q R) R []) prf
       | (FP_TRS_input strat R, Termination, Decision False) \<Rightarrow> 
              trs_nontermination_proof_to_fp prf \<bind>
              \<comment> \<open>switch assumption flag to False, since currently there are no assumptions below fp-non-term proof\<close>
              check_fp_nontermination_proof I J False (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl strat R, R)
       | _ \<Rightarrow> error mismatch)
  | Relative_TRS_Nontermination_Proof prf \<Rightarrow>
     (case triple of 
       (Inn_TRS_input Q R S, Termination, Decision False) \<Rightarrow>       
          check_reltrs_nontermination_proof I J a (showsl_lit (STR ''1'')) (tp_ops.mk I (strategy_to_nfs Q) (strategy_to_Q Q R) R S) prf
      | _ \<Rightarrow> error mismatch)
  | TRS_Confluence_Proof prf \<Rightarrow>
     (case triple of 
       (Single_TRS_input F R, Confluence, Decision True) \<Rightarrow>
          check_cr_proof a (showsl_lit (STR ''1'')) I J R prf
      | _ \<Rightarrow> error mismatch)
  | TRS_Non_Confluence_Proof prf \<Rightarrow>
     (case triple of 
       (Single_TRS_input F R, Confluence, Decision False) \<Rightarrow>
          check_ncr_proof a (showsl_lit (STR ''1'')) I J R prf
      | _ \<Rightarrow> error mismatch)
  | TRS_Commutation_Proof prf \<Rightarrow>
     (case triple of 
       (Two_TRS_input F R S, Commutation, Decision True) \<Rightarrow>
          check_comm_proof I J a (showsl_lit (STR ''1'')) R S prf
      | _ \<Rightarrow> error mismatch)
  | TRS_Non_Commutation_Proof prf \<Rightarrow>
     (case triple of 
       (Two_TRS_input F R S, Commutation, Decision False) \<Rightarrow>
          check_ncomm_proof (showsl_lit (STR ''1'')) F R S prf
      | _ \<Rightarrow> error mismatch)
  | Complexity_Proof prf \<Rightarrow>
     (case triple of 
       (Inn_TRS_input Q R S, Complexity cm, Upperbound_Poly n) \<Rightarrow>
          check_complexity_proof I a (showsl_lit (STR ''1'')) (tp_ops.mk I (strategy_to_nfs Q) (strategy_to_Q Q (R @ S)) R S, 
            complexity_measure_of R S cm, Comp_Poly n) prf
      | _ \<Rightarrow> error mismatch)
  | DP_Termination_Proof prf \<Rightarrow>
     (case triple of 
       (DP_input m P Q R, Termination, Decision True) \<Rightarrow>
          check_dp_termination_proof I J a (showsl_lit (STR ''1'')) (dpp_ops.mk J (strategy_to_nfs Q) m P [] (strategy_to_Q Q R) [] R) prf
      | _ \<Rightarrow> error mismatch)
  | DP_Nontermination_Proof prf \<Rightarrow>
     (case triple of 
       (DP_input m P Q R, Termination, Decision False) \<Rightarrow>
        check_dp_nontermination_proof I J a (showsl_lit (STR ''1'')) (dpp_ops.mk J (strategy_to_nfs Q) m P [] (strategy_to_Q Q R) [] R) prf
    | _ \<Rightarrow> error mismatch)
  | Completion_Proof prf \<Rightarrow>
     (case triple of 
       (EQ_input E, Completion, Completed_System R) \<Rightarrow>
        check_completion_proof a (showsl_lit (STR ''1'')) I J E R prf
    | _ \<Rightarrow> error mismatch)
  | Ordered_Completion_Proof prf \<Rightarrow>
     (case triple of 
       (EQ_RO_input E\<^sub>0 ord, Completion, Order_Completed_System E R) \<Rightarrow>
          check_ordered_completion_proof_ext (showsl_lit (STR ''1'')) E\<^sub>0 E R ord prf
    | _ \<Rightarrow> error mismatch)
  | FP_Termination_Proof prf \<Rightarrow>
     (case triple of 
       (FP_TRS_input strat R, Termination, Decision True) \<Rightarrow>
       check_fptrs_termination_proof I J a (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl strat R, R) prf
    | _ \<Rightarrow> error mismatch)
  | FP_Nontermination_Proof prf \<Rightarrow>
     (case triple of 
       (FP_TRS_input strat R, Termination, Decision False) \<Rightarrow>       
           check_fp_nontermination_proof I J a (showsl_lit (STR ''1'')) (fp_strategy_to_fp_impl strat R, R) prf
       | _ \<Rightarrow> error mismatch)
  | Equational_Proof prf \<Rightarrow>
     (case triple of 
       (EQ_reasoning_input E eq, Entailment, Decision True) \<Rightarrow>
       check_equational_proof a (showsl_lit (STR ''1'')) I J E eq prf
    | _ \<Rightarrow> error mismatch)
  | Equational_Disproof prf \<Rightarrow>
     (case triple of 
       (EQ_reasoning_input E eq, Entailment, Decision False) \<Rightarrow>
       check_equational_disproof a (showsl_lit (STR ''1'')) I J E eq prf
    | _ \<Rightarrow> error mismatch)
  | Quasi_Reductive_Proof prf \<Rightarrow>
     (case triple of 
       (CTRS_input R, Termination, Decision True) \<Rightarrow>
         check_quasi_reductive_proof a (showsl_lit (STR ''1'')) I J R prf
    | _ \<Rightarrow> error mismatch)
  | Conditional_CR_Proof prf \<Rightarrow>
     (case triple of 
       (CTRS_input R, Confluence, Decision True) \<Rightarrow>
         check_conditional_cr_proof a (showsl_lit (STR ''1'')) I J R prf
    | _ \<Rightarrow> error mismatch)
  | Conditional_Non_CR_Proof prf \<Rightarrow>
     (case triple of 
       (CTRS_input R, Confluence, Decision False) \<Rightarrow>
         check_conditional_ncr_proof a (showsl_lit (STR ''1'')) I J R prf
    | _ \<Rightarrow> error mismatch)
  | AC_Termination_Proof prf \<Rightarrow>
     (case triple of 
       (AC_input R A C, Termination, Decision True) \<Rightarrow>
         check_ac_termination_proof L K (showsl_lit (STR ''1'')) (ac_tp_ops.mk K R A C) prf
    | _ \<Rightarrow> error mismatch)
  | LTS_Termination_Proof prf \<Rightarrow>
     (case triple of 
       (LTS_input r, Termination, Decision True) \<Rightarrow>
         IA.check_termination r prf
    | _ \<Rightarrow> error mismatch)
  | Tree_Automata_Closed_Proof prf \<Rightarrow>
     (case triple of 
       (TA_input ta R, Closed_Under_Rewriting, Decision True) \<Rightarrow>
         tree_aut_trs_closed ta prf R
    | _ \<Rightarrow> error mismatch)
  | LTS_Safety_Proof prf \<Rightarrow>
     (case triple of 
       (LTS_safety_input r e, Safety, Decision True) \<Rightarrow>
         IA.check_safety r e prf
    | _ \<Rightarrow> error mismatch)
  | Infeasibility_Proof prf \<Rightarrow>
     (case triple of 
       (Infeasibility_input r cs, Infeasibility, Decision True) \<Rightarrow>
         check_infeasible' a (showsl_lit (STR ''1'')) I J r cs prf
    | _ \<Rightarrow> error mismatch)
  | Feasibility_Proof prf \<Rightarrow>
     (case triple of 
       (Infeasibility_input r cs, Infeasibility, Decision False) \<Rightarrow>
         check_feasibility_proof r cs prf
    | _ \<Rightarrow> error mismatch)
  | Unknown_Proof prf \<Rightarrow>
     (case triple of 
       (Unknown_input ur, Unknown_Property, _) \<Rightarrow>
         check_unknown_proof I J a (showsl_lit (STR ''1'')) ur prf
    | _ \<Rightarrow> error mismatch)
  | Unknown_Disproof prf \<Rightarrow>
     (case triple of 
       (Unknown_input ur, Unknown_Property, _) \<Rightarrow>
         check_unknown_disproof I J a (showsl_lit (STR ''1'')) ur prf
    | _ \<Rightarrow> error mismatch)"
(* a last catch all is not possible since all cases have been covered before
  | _ \<Rightarrow> error mismatch" *)

definition "certify_cert_problem a input property answer proof \<equiv>
  case check_cert a input property answer proof of
    Inl err \<Rightarrow> Error (err (STR ''''))
  | _ \<Rightarrow> Certified"

context
  assumes I: "tp_spec I" and J: "dpp_spec J" and K: "ac_tp_spec K" and L: "ac_dpp_spec L"
begin

lemma check_cert_with_assms_sound:
  assumes check: "isOK (check_cert a input property answer proof)"
      and a: "\<forall>p\<in>set (cert_assms a proof). holds p"
  shows "desired_property input property answer"
proof-
  let ?i = "showsl_lit (STR ''1'')"
  note [simp] = check_cert_def desired_property_def
  obtain idx where [simp]: "showsl_lit (STR ''1'') = idx" by auto
  interpret tp_spec I by fact
  interpret J: dpp_spec J by fact
  interpret K: ac_tp_spec K by fact
  show ?thesis
  proof (cases "proof")
    case [simp]: (TRS_Termination_Proof pr)
    obtain Q R S where [simp]: "input = Inn_TRS_input Q R S" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_trs_termination_proof I J a idx (mk (strategy_to_nfs Q) (strategy_to_Q Q R) R S) pr)" 
      by auto
    from check_trs_termination_proof_with_assms[OF I J check] a
    show ?thesis by auto 
  next
    case [simp]: (Complexity_Proof pr)
    obtain Q R S where [simp]: "input = Inn_TRS_input Q R S" using check by (cases input, auto)
    obtain cm where [simp]: "property = Complexity cm" using check by (cases property, auto)
    obtain n where [simp]: "answer = Upperbound_Poly n" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have 
      check: "isOK (check_complexity_proof I a idx (mk (strategy_to_nfs Q) (strategy_to_Q Q (R @ S)) R S, 
        complexity_measure_of R S cm, Comp_Poly n) pr)" 
      by auto
    from check_complexity_proof_with_assms[OF I infinite_lab check] a
    show ?thesis by auto
  next
    case [simp]: (DP_Termination_Proof pr)
    obtain m R Q S where [simp]: "input = DP_input m R Q S" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have
      check: "isOK (check_dp_termination_proof I J a idx (J.mk (strategy_to_nfs Q) m R [] (strategy_to_Q Q S) [] S) pr)" 
      by auto
    from check_dp_termination_proof_with_assms[OF I J check] a
    show ?thesis by simp
  next
    case [simp]: (DP_Nontermination_Proof pr)
    obtain m R Q S where [simp]: "input = DP_input m R Q S" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have
      check: "isOK (check_dp_nontermination_proof I J a idx (J.mk (strategy_to_nfs Q) m R [] (strategy_to_Q Q S) [] S) pr)" 
      by auto
    from check_dp_nontermination_proof_with_assms[OF I J _ check] a
    show ?thesis by simp
  next
    case [simp]: (TRS_Nontermination_Proof pr)
    obtain strat Q R S where input: "input = Inn_TRS_input Q R S \<or> input = FP_TRS_input strat R" using check by (cases input, auto)
    from input show ?thesis
    proof
      assume [simp]: "input = Inn_TRS_input Q R S" 
      have [simp]: "property = Termination" using check by (cases property, auto)
      have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
      from check[simplified] have 
        check: "isOK (check_trs_nontermination_proof I J a idx (mk (strategy_to_nfs Q) (strategy_to_Q Q R) R []) pr)" 
        and [simp]: "S = []" 
        by auto
      from check_trs_nontermination_proof_with_assms[OF I J _ check] a
      show ?thesis by auto 
    next
      assume [simp]: "input = FP_TRS_input strat R" 
      have [simp]: "property = Termination" using check by (cases property, auto)
      have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
      let ?prf = "trs_nontermination_proof_to_fp pr" 
      from check obtain prof where [simp]: "?prf = return prof" by (cases ?prf, auto)
      from check[simplified]
      have check: "isOK (check_fp_nontermination_proof I J False idx (fp_strategy_to_fp_impl strat R, R) prof)" by simp
      from check_fp_nontermination_proof[OF I J this] 
      have nSN: "\<not> SN_fpstep (mk_fptp_set (fp_strategy_to_fp_impl strat R, R))" .
      thus ?thesis using ostep_iff_fpstep_impl[of "map fst R",simplified] 
        by (cases strat, auto simp add: fp_strategy_to_fp_impl_def SN_fpstep_def csstep_iff_fpstep_impl)
    qed
  next
    case [simp]: (FP_Nontermination_Proof pr)
    obtain strat R where [simp]: "input = FP_TRS_input strat R" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_fp_nontermination_proof I J a idx (fp_strategy_to_fp_impl strat R, R) pr)" by auto
    from check_fp_nontermination_proof_with_assms[OF I J _ check] a
    have "\<not> SN_fpstep (mk_fptp_set (fp_strategy_to_fp_impl strat R, R))" by auto
    thus ?thesis using ostep_iff_fpstep_impl[of "map fst R",simplified] 
      by (cases strat, auto simp add: fp_strategy_to_fp_impl_def SN_fpstep_def csstep_iff_fpstep_impl)
  next
    case [simp]: (FP_Termination_Proof pr)
    obtain strat R where [simp]: "input = FP_TRS_input strat R" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_fptrs_termination_proof I J a idx (fp_strategy_to_fp_impl strat R, R) pr)" 
      by auto
    from check_fptrs_termination_proof_with_assms[OF I J check] a 
    have "SN_fpstep (set (fp_strategy_to_fp_impl strat R), set R)" by auto
    thus ?thesis using ostep_iff_fpstep_impl[of "map fst R",simplified] 
      by (cases strat, auto simp add: fp_strategy_to_fp_impl_def SN_fpstep_def csstep_iff_fpstep_impl)
  next
    case [simp]: (Relative_TRS_Nontermination_Proof pr)
    obtain Q R S where [simp]: "input = Inn_TRS_input Q R S" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_reltrs_nontermination_proof I J a idx (mk (strategy_to_nfs Q) (strategy_to_Q Q R) R S) pr)" 
      by auto
    from check_reltrs_nontermination_proof_with_assms[OF I J _ check] a
    show ?thesis by auto 
  next
    case [simp]: (TRS_Confluence_Proof pr)
    obtain F R where [simp]: "input = Single_TRS_input F R" using check by (cases input, auto)
    have [simp]: "property = Confluence" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_cr_proof a idx I J R pr)" by auto
    from check_cr_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by auto
  next
    case [simp]: (TRS_Non_Confluence_Proof pr)
    obtain F R where [simp]: "input = Single_TRS_input F R" using check by (cases input, auto)
    have [simp]: "property = Confluence" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_ncr_proof a idx I J R pr)" by auto
    from check_ncr_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by auto
  next
    case [simp]: (TRS_Non_Commutation_Proof pr)
    obtain F R S where [simp]: "input = Two_TRS_input F R S" using check by (cases input, auto)
    have [simp]: "property = Commutation" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] obtain idx where 
      check: "isOK (check_ncomm_proof idx F R S pr)" 
      by auto
    from check_ncomm_proof_sound[OF check] 
    show ?thesis by auto
  next
    case [simp]: (TRS_Commutation_Proof pr)
    obtain F R S where [simp]: "input = Two_TRS_input F R S" using check by (cases input, auto)
    have [simp]: "property = Commutation" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_comm_proof I J a idx R S pr)" by auto
    from check_comm_proof_with_assms_sound[OF I J check] a
    show ?thesis by (auto intro!: commute_imp_sig_commute)
  next
    case [simp]: (Completion_Proof pr)
    obtain E where [simp]: "input = EQ_input E" using check by (cases input, auto)
    have [simp]: "property = Completion" using check by (cases property, auto)
    obtain R where [simp]: "answer = Completed_System R" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_completion_proof a idx I J E R pr)" by auto
    from check_completion_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by auto
  next
    case [simp]: (Ordered_Completion_Proof pr)
    obtain E0 ord where [simp]: "input = EQ_RO_input E0 ord" using check by (cases input, auto)
    have [simp]: "property = Completion" using check by (cases property, auto)
    obtain E R where [simp]: "answer = Order_Completed_System E R" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_ordered_completion_proof_ext idx E0 E R ord pr)" by auto
    from check_ordered_completion_proof_ext_sound[OF check]
    show ?thesis by simp
  next
    case [simp]: (Equational_Proof pr)
    obtain E eq where [simp]: "input = EQ_reasoning_input E eq" using check by (cases input, auto)
    have [simp]: "property = Entailment" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_equational_proof a idx I J E eq pr)" by auto
    from check_equational_proof_with_assms_entails[OF I J _ this] a
    show ?thesis by (cases eq, auto)
  next
    case [simp]: (Equational_Disproof pr)
    obtain E eq where [simp]: "input = EQ_reasoning_input E eq" using check by (cases input, auto)
    have [simp]: "property = Entailment" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_equational_disproof a idx I J E eq pr)" by auto
    from check_equational_disproof_with_assms_sound[OF I J _ check] a
    show ?thesis by (cases eq, auto simp: birkhoff)
  next
    case [simp]: (Quasi_Reductive_Proof pr)
    obtain R where [simp]: "input = CTRS_input R" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_quasi_reductive_proof a idx I J R pr)" by auto
    from check_quasi_reductive_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by (auto intro: quasi_reductive_SN)
  next
    case [simp]: (Conditional_CR_Proof pr)
    obtain R where [simp]: "input = CTRS_input R" using check by (cases input, auto)
    have [simp]: "property = Confluence" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_conditional_cr_proof a idx I J R pr)" by auto
    from check_conditional_cr_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by auto
  next
    case [simp]: (Conditional_Non_CR_Proof pr)
    obtain R where [simp]: "input = CTRS_input R" using check by (cases input, auto)
    have [simp]: "property = Confluence" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_conditional_ncr_proof a idx I J R pr)" by auto
    from check_conditional_ncr_proof_with_assms_sound[OF I J _ check] a
    show ?thesis by auto
  next
    case [simp]: (Tree_Automata_Closed_Proof pr)
    obtain ta R where [simp]: "input = TA_input ta R" using check by (cases input, auto)
    have [simp]: "property = Closed_Under_Rewriting" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (tree_aut_trs_closed ta pr R)" by auto
    from tree_aut_trs_closed[OF check]
    show ?thesis by auto
  next
    case [simp]: (AC_Termination_Proof pr)
    obtain r a c where [simp]: "input = AC_input r a c" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_ac_termination_proof L K idx (K.mk r a c) pr)" by auto
    from check_ac_termination_proof[OF L K check]
    show ?thesis by auto
  next
    case [simp]: (LTS_Termination_Proof pr)
    obtain r where [simp]: "input = LTS_input r" using check by (cases input, auto)
    have [simp]: "property = Termination" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (IA.check_termination r pr)" by auto
    from IA.check_termination[OF this]
    show ?thesis by auto
  next
    case [simp]: (LTS_Safety_Proof pr)
    obtain r e where [simp]: "input = LTS_safety_input r e" using check by (cases input, auto)
    have [simp]: "property = Safety" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (IA.check_safety r e pr)" by auto
    from IA.check_safety[OF this]
    show ?thesis by auto
  next
    case [simp]: (Infeasibility_Proof pr)
    obtain r cs where [simp]: "input = Infeasibility_input r cs" using check by (cases input, auto)
    have [simp]: "property = Infeasibility" using check by (cases property, auto)
    have [simp]: "answer = Decision True" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_infeasible' a idx I J r cs pr)" by auto
    from check_infeasible'[OF I J this]
    show ?thesis by (auto simp: conds_sat_conds_n_sat)
  next
    case [simp]: (Feasibility_Proof pr)
    obtain r cs where [simp]: "input = Infeasibility_input r cs" using check by (cases input, auto)
    have [simp]: "property = Infeasibility" using check by (cases property, auto)
    have [simp]: "answer = Decision False" using check by (cases answer, auto split: bool.splits)
    from check[simplified] have check: "isOK (check_feasibility_proof r cs pr)" by auto
    from check_feasibility_proof[OF this]
    show ?thesis by (auto simp: conds_sat_conds_n_sat)
  next
    case [simp]: (Unknown_Proof pr)
    obtain unk where [simp]: "input = Unknown_input unk" using check by (cases input, auto)
    have [simp]: "property = Unknown_Property" using check by (cases property, auto)
    from check[simplified] have check: "isOK (check_unknown_proof I J a idx unk pr)" by simp
    from check_unknown_proof_with_assms[OF I J check] a
    show ?thesis by auto
  next
    case [simp]: (Unknown_Disproof pr)
    obtain unk where [simp]: "input = Unknown_input unk" using check by (cases input, auto)
    have [simp]: "property = Unknown_Property" using check by (cases property, auto)
    from check[simplified] have check: "isOK (check_unknown_disproof I J a idx unk pr)" by simp
    from check_unknown_disproof_with_assms[OF I J check] a
    show ?thesis by auto
  qed
qed

lemma certify_cert_problem_sound:
  assumes answer: "certify_cert_problem False input property answer proof = Certified"
  shows "desired_property input property answer"
  using answer
  by (cases "check_cert False input property answer proof", auto simp: certify_cert_problem_def intro: check_cert_with_assms_sound)

end
end
end
