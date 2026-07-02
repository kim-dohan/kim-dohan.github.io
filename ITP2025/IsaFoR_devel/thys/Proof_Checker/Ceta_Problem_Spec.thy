(*
Author:  Akihisa Yamada and René Thiemann
License: LGPL (see file COPYING.LESSER)
*)
theory Ceta_Problem_Spec
imports
  CTRS.Conditional_Rewriting_Impl
  Ord.Integer_Arithmetic
  LTS.LTS
  Processors
  TRS.Context_Sensitive_Impl
begin

hide_const (open) eq_object.eq

interpretation IA: lts
  where I = IA.I
    and type_of_fun = IA.type_of_fun
    and Values_of_type = IA.Values_of_type
    and Bool_types = "{IA.BoolT}"
    and to_bool = IA.to_bool
    and type_fixer = "TYPE(_)".

datatype (dead 'f, dead 'v) strategy =
  No_Strategy
| Innermost bool 
| Innermost_Q bool "('f, 'v) term list"

primrec strategy_to_Q :: "('f, 'v) strategy \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term list" where
  "strategy_to_Q No_Strategy _ = []"
| "strategy_to_Q (Innermost _) R = remdups (map fst R)"
| "strategy_to_Q (Innermost_Q _ Q) _ = Q"

definition "default_nfs_flag = False" 

primrec strategy_to_nfs :: "('f,'v)strategy \<Rightarrow> bool" where
  "strategy_to_nfs No_Strategy = default_nfs_flag" 
| "strategy_to_nfs (Innermost nfs) = nfs" 
| "strategy_to_nfs (Innermost_Q nfs _) = nfs" 

datatype (dead 'f, dead 'v) fp_strategy =
  Outermost
| Context_Sensitive "'f muL"
| Forbidden_Patterns "('f, 'v) forb_pattern list"

definition "fp_strategy_to_fp_impl strat R \<equiv> case strat of
    Outermost \<Rightarrow> o_to_fp_impl (map fst R)
  | Context_Sensitive \<mu> \<Rightarrow> mu_to_fp_impl \<mu>
  | Forbidden_Patterns fp \<Rightarrow> fp"

definition "fp_strategy_to_string strat \<equiv> case strat of
    Outermost \<Rightarrow> ''outermost''
  | Context_Sensitive _ \<Rightarrow> ''context-sensitive''
  | Forbidden_Patterns _ \<Rightarrow> ''forbidden-pattern''"

datatype (dead 'f, dead 'v) input =
  DP_input bool "('f, 'v) rules" "('f, 'v) strategy" "('f, 'v) rules"
| Inn_TRS_input "('f, 'v) strategy" "('f, 'v) rules" "('f, 'v) rules"
| FP_TRS_input "('f, 'v) fp_strategy" "('f, 'v) rules"
| AC_input "('f,'v) rules" "'f list" "'f list"
| LTS_input "(IA.sig, 'v, IA.ty, string, string) lts_impl"
| LTS_safety_input "(IA.sig, 'v, IA.ty, string, string) lts_impl" "string list"
| CTRS_input "('f, 'v) crules"
| EQ_input "('f, 'v) equation list" 
| EQ_RO_input "('f, 'v) equation list" "'f reduction_order_input"
| EQ_reasoning_input "('f, 'v) equation list" "('f, 'v) equation"
| TA_input "(string,'f)tree_automaton" "('f,'v)rules"
| Infeasibility_input "('f, 'v) crules" "('f, 'v) rules"
| Single_TRS_input "'f sig_list" "('f,'v) rules"  (* for confluence, ground confluence, ... *)
| Two_TRS_input "'f sig_list" "('f,'v) rules" "('f,'v)rules" 
| Unknown_input unknown_info

primrec input_to_string :: "(_,_)input \<Rightarrow> String.literal" where
  "input_to_string (DP_input _ _ _ _) = STR ''dependency pair problem''" 
| "input_to_string (Inn_TRS_input _ _ _) = STR ''(innermost) (relative) rewrite system(s)''" 
| "input_to_string (FP_TRS_input _ _) = STR ''rewrite system with evaluation strategy''" 
| "input_to_string (AC_input _ _ _) = STR ''AC rewrite system''"
| "input_to_string (LTS_input _) = STR ''integer transition system''"
| "input_to_string (LTS_safety_input _ _) = STR ''integer transition system with potential error states''" 
| "input_to_string (CTRS_input _) = STR ''conditional TRS''"
| "input_to_string (EQ_input _) = STR ''equational system''"
| "input_to_string (EQ_RO_input _ _) = STR ''equational system and reduction order''"
| "input_to_string (EQ_reasoning_input _ _) = STR ''equational system and explicit equation''"
| "input_to_string (TA_input _ _) = STR ''tree automation and rewrite system''"
| "input_to_string (Infeasibility_input _ _) = STR ''conditional TRS and list of term pairs''" 
| "input_to_string (Two_TRS_input _ _ _) = STR ''two rewrite systems with signature''"
| "input_to_string (Single_TRS_input _ _) = STR ''rewrite system with signature''"
| "input_to_string (Unknown_input _) = STR ''unspecified input''"

type_synonym ('f, 'v) inn_fp_strategy = "('f, 'v) strategy + ('f, 'v) fp_strategy"

datatype ('f,'v) complexityMeasure = Derivational "('f \<times> nat) list option" | Runtime "(('f \<times> nat) list \<times> ('f \<times> nat)list) option"

definition "complexity_measure_of R S cm \<equiv>
  let F = funas_trs_list (R @ S) in
  let D = defined_list (R @ S) in
  let C = filter (\<lambda>f. f \<notin> set D) F in
  case cm of
    Derivational None \<Rightarrow> Derivational_Complexity F
  | Derivational (Some f) \<Rightarrow> Derivational_Complexity f
  | Runtime None \<Rightarrow> Runtime_Complexity C D
  | Runtime (Some (c,d)) \<Rightarrow> Runtime_Complexity c d"

datatype (dead 'f, dead 'v) property =
    Termination
  | Confluence
  | Commutation
  | Completion
  | Safety
  | Entailment
  | Complexity "('f,'v) complexityMeasure"
  | Closed_Under_Rewriting
  | Infeasibility
  | Unknown_Property

primrec property_to_string :: "(_,_)property \<Rightarrow> String.literal" where
  "property_to_string Termination = STR ''termination''" 
| "property_to_string Confluence = STR ''confluence''" 
| "property_to_string Commutation  = STR ''commutation''"
| "property_to_string Completion = STR ''completion''"
| "property_to_string Safety = STR ''safety''"
| "property_to_string Entailment = STR ''entailment''"
| "property_to_string (Complexity _)  = STR ''upperbound on complexity''"
| "property_to_string Closed_Under_Rewriting = STR ''closed under rewriting''"
| "property_to_string Infeasibility = STR ''infeasibility''"
| "property_to_string Unknown_Property = STR ''unknown property''"

datatype (dead 'f, dead 'v) answer = 
    Decision bool 
    | Upperbound_Poly nat
    | Completed_System "('f,'v)rules" 
    | Order_Completed_System "('f, 'v) equation list" "('f, 'v) rules"

primrec answer_to_string :: "(_,_) answer \<Rightarrow> String.literal" where
  "answer_to_string (Decision b) = (if b then STR ''YES'' else STR ''NO'')" 
| "answer_to_string (Upperbound_Poly _) = (STR ''O(n^something)'')"
| "answer_to_string (Completed_System _) = (STR ''some complete TRS'')"
| "answer_to_string (Order_Completed_System _ _) = (STR ''some order-complete system (E,R)'')"


definition desired_property :: "('f::compare_order, 'v) input \<Rightarrow> ('f,'v) property \<Rightarrow> ('f,'v) answer \<Rightarrow> bool" where
"desired_property input property answer \<equiv>
  case (input,property,answer) of
  \<comment> \<open>Termination of various formats\<close>
    (Inn_TRS_input Q R S, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN_qrel (strategy_to_nfs Q, set (strategy_to_Q Q R), set R, set S)
  | (AC_input r a c, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN (relation_ac_tp (set r, set a, set c))
  | (FP_TRS_input Outermost R, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN (ostep (lhss (set R)) (set R))
  | (FP_TRS_input (Forbidden_Patterns P) R, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN (fpstep (set P) (set R))
  | (FP_TRS_input (Context_Sensitive \<mu>) R, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN (csstep (mu_of \<mu>) (set R))
  | (LTS_input r, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN_on (IA.transition (lts_of r)) (IA.initial_states (lts_of r))
  | (CTRS_input ctrs, Termination, Decision b) \<Rightarrow> b \<longleftrightarrow> SN (cstep (set ctrs))
  \<comment> \<open>for DP-problems, termination and non-termination are not dual!\<close> 
  | (DP_input m P Q R, Termination, Decision True) \<Rightarrow> finite_dpp (strategy_to_nfs Q, m, set P, {}, set (strategy_to_Q Q R), {}, set R)
  | (DP_input m P Q R, Termination, Decision False) \<Rightarrow> infinite_dpp (strategy_to_nfs Q, set P, set (strategy_to_Q Q R), set R)
  \<comment> \<open>complexity\<close>
  | (Inn_TRS_input Q R S, Complexity cm, Upperbound_Poly ub) \<Rightarrow> 
      deriv_bound_measure_class (rel_qrstep (strategy_to_nfs Q, set (strategy_to_Q Q (R @ S)), set R, set S)) (complexity_measure_of R S cm) (Comp_Poly ub)
  \<comment> \<open>confluence and commutation\<close>
  | (Single_TRS_input F R, Confluence, Decision b) \<Rightarrow> b \<longleftrightarrow> CR (rstep (set R))
  | (Two_TRS_input F R S, Commutation, Decision b) \<Rightarrow> b \<longleftrightarrow> sig_commute (set F) (set R) (set S)
  | (CTRS_input ctrs, Confluence, Decision b) \<Rightarrow> b \<longleftrightarrow> CR (cstep (set ctrs))
  \<comment> \<open>safety\<close>
  | (LTS_safety_input r e, Safety, Decision b) \<Rightarrow> b \<longleftrightarrow> IA.lts_safe (lts_of r) (set e)
  \<comment> \<open>completion\<close>
  | (EQ_input E, Completion, Completed_System R) \<Rightarrow> completed_rewrite_system (set E) (set R)
  | (EQ_RO_input E\<^sub>0 ro, Completion, Order_Completed_System E R) \<Rightarrow> ordered_completed_rewrite_system (set E\<^sub>0) (set E) (set R) ro
  \<comment> \<open>equational consequences\<close>
  | (EQ_reasoning_input E eq, Consequence, Decision b) \<Rightarrow> b \<longleftrightarrow> entails (TYPE(('f,'v)term set)) (set E) eq
  \<comment> \<open>closed under rewriting\<close>  
  | (TA_input ta R, Closed_Under_Rewriting, Decision b) \<Rightarrow> b \<longleftrightarrow> (rstep (set R))^* `` ta_lang (ta_of_ta ta) \<subseteq> ta_lang (ta_of_ta ta)
  \<comment> \<open>infeasibility\<close>  
  | (Infeasibility_input c p, Infeasibility, Decision b) \<Rightarrow> b \<longleftrightarrow> (\<not> (\<exists>\<sigma>. conds_sat (set c) p \<sigma>))
  \<comment> \<open>unknown inputs\<close>  
  | (Unknown_input unk, Unknown_Property, _) \<Rightarrow> unknown_satisfied unk
  | _ \<Rightarrow> False"

end
