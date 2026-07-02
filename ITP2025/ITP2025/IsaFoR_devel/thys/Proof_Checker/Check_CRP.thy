(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2013-2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_CRP
  imports
    Check_Termination
    CR.LS_Persistence_Impl
    CR.Equational_Reasoning_Impl
    CR.Orthogonality_Impl
    CR.Critical_Pair_Closure_Impl
    CR.Parallel_Closed_Impl
    CR.Strongly_Closed_Impl
    CR.Development_Closed_Impl
    CR.Parallel_Critical_Pairs_Impl
    CR.Non_Confluence_Impl
    CR.Non_Commutation_Impl
    CR.Rule_Labeling_Impl
    CR.Redundant_Rules_Impl
    Auxx.RenamingN_String
begin

subsection \<open>Proving confluence of TRSs\<close>

datatype (dead 'f, dead 'l, dead 'v) cr_proof =
    SN_WCR "(('f, 'l) lab, 'v) join_info" "('f, 'l, 'v) trs_termination_proof"
  | Weakly_Orthogonal
  | Strongly_Closed "nat"
  | Rule_Labeling "(('f, 'l) lab, 'v) rule_lab_repr" "(('f,'l)lab,'v)crit_pair_info list" "('f, 'l, 'v) trs_termination_proof option"
  | Rule_Labeling_Conv "(('f, 'l) lab, 'v) rule_lab_repr" "(('f, 'l) lab ,string) crit_pair_info list" "(nat \<times> ('f, 'l, 'v) trs_termination_proof) option"
  | Redundant_Rules "('f, 'l, 'v) trsLL" "nat" "(('f, 'l) lab, 'v) term list list" "('f, 'l, 'v) cr_proof"
  | Compositional_PCP "('f, 'l, 'v) trsLL" "(('f,'l)lab,'v)cp_join_hints" "('f, 'l, 'v) cr_proof"
  | Compositional_PCP_Rule_Lab "('f, 'l, 'v) trsLL" "(('f,'l)lab,'v) pcp_rule_lab_com" "('f, 'l, 'v) cr_proof"
  | Parallel_Closed "nat option"
  | PCP_Closed "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints"
  | PCP_Rule_Lab "(('f,'l)lab,'v) pcp_rule_lab" 
  | Development_Closed "nat option"
  | Critical_Pair_Closing_System "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trs_termination_proof" "nat"
  | Compositional_PCPS "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints" "('f, 'l, 'v) trs_termination_proof" "('f, 'l, 'v) cr_proof"
  | Persistent_Decomposition "(('f, 'l) lab \<times> (string list \<times> string)) list" "(('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) cr_proof) list"

definition "swap_cp_info info = Crit_Pair_Info 
    (cp_right info) 
    (cp_peak info) 
    (cp_left info) 
    (rev (cp_join info)) 
    (cp_poss info) 
    (map_option prod.swap (cp_labels info))" 

(* add swapped join information for root overlaps, so that these only have to be listed once in the certificate *)
definition "symmetric_cp_infos infos = infos @ map swap_cp_info (filter (\<lambda> info. cp_poss info \<in> set [None, Some []]) infos)"

primrec
  check_cr_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow>
     (('f,label_type)lab,string) rules \<Rightarrow>
     ('f, label_type, string) cr_proof \<Rightarrow>
     showsl check"
where
  "check_cr_proof a i I J R (SN_WCR joins_i prf) = debug i (STR ''SN_WCR'') (do {
         let tp = tp_ops.mk I False [] R [];
         check_trs_termination_proof I J a (add_index i 1) tp prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization + wcr\<newline>'')
             \<circ> s);
         check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving local confluence of '') \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s)
   })"
| "check_cr_proof a i I J R Weakly_Orthogonal = debug i (STR ''Weakly Orthogonal'') ( do {
           check_weakly_orthogonal string_rename R
         }  <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking weakly orthogonality of the '') \<circ> showsl_trs R
             \<circ> s))"
| "check_cr_proof a i I J R (Strongly_Closed n) = debug i (STR ''Strongly Closed'') ( do {
           check_strongly_closed string_rename R n
         }  <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking strong closedness for the '') \<circ> showsl_trs R
             \<circ> s))"
| "check_cr_proof a i I J R (Compositional_PCP C hints prf) = debug i (STR ''Compositional PCP'') ( do {
           check_compositional_parallel_pairs string_renameN R C hints
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking compositional parallel critical pairs to switch to TRS C = \<newline>'')
               o showsl_trs C o showsl_nl 
               \<circ> s);
          check_cr_proof a (add_index i 1) I J C prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in proving confluence of sub TRS C\<newline>'') \<circ> showsl_trs C \<circ> showsl_nl o s)
     })"
| "check_cr_proof a i I J R (Compositional_PCPS C P hintsP hints sn_prf cr_prf) = debug i (STR ''Compositional PCPS'') ( do {
         let tp = tp_ops.mk I False [] P R;
           check_compositional_PCPS string_renameN R C P hintsP hints
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking compositional parallel critical system to switch to TRS C = \<newline>'')
               o showsl_trs C o showsl_nl 
               \<circ> s);
         check_trs_termination_proof I J a (add_index i 1) tp sn_prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below relative termination proof of compositional CPCS\<newline>'')
             \<circ> s);
          check_cr_proof a (add_index i 2) I J C cr_prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in proving confluence of sub TRS C\<newline>'') \<circ> showsl_trs C \<circ> showsl_nl o s)
     })"
| "check_cr_proof a i I J R (Compositional_PCP_Rule_Lab C hints prf) = debug i (STR ''Compositional PCP Rule Labeling'') ( do {
         check_compositional_pcp_rule_lab string_renameN R C hints
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking compositional parallel critical pairs \<newline>'') \<circ> s);
          check_cr_proof a (add_index i 1) I J C prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in proving confluence of sub TRS C\<newline>'') \<circ> showsl_trs C \<circ> showsl_nl o s)
     })"
| "check_cr_proof a i I J R (PCP_Closed hints_cp hints_pcp) = debug i (STR ''PCP Closed'') ( do {
           check_parallel_critical_pairs_closed_CR string_renameN R hints_cp hints_pcp
         }  <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking parallel critical pair closure criterion\<newline>'')
             \<circ> s))"
| "check_cr_proof a i I J R (PCP_Rule_Lab hints) = debug i (STR ''PCP Rule Labeling'') ( do {
       check_pcp_rule_lab string_renameN R hints
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving confluence by rule labeling with parallel critical pairs\<newline>'') o s)})"
| "check_cr_proof a i I J R (Rule_Labeling rl joins prf) = debug i (STR ''Rule Labeling'') ( do {
           (case prf of
             None \<Rightarrow> check_linear_trs R
           | Some prf \<Rightarrow> do {
             check_left_linear_trs R;
             let (Rnd, Rd) = List.partition (\<lambda>lr. linear_term (snd lr)) R;
             let tp = tp_ops.mk I False [] Rd Rnd;
             check_trs_termination_proof I J a (add_index i 1) tp prf
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below relative termination for rule labeling\<newline>'') \<circ> s)
             }
           );
           check_rule_labeling_eld string_rename R rl (symmetric_cp_infos joins)
             <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking decreasingness of CPs using rule labeling for the '')
             \<circ> showsl_trs R \<circ> s)
           })"
| "check_cr_proof a i I J R (Rule_Labeling_Conv rl convs nprf) = debug i (STR ''Rule Labeling'') ( do {
           (case nprf of
             None \<Rightarrow> do {
             check_linear_trs R;
             check_rule_labeling_eldc string_rename R rl (symmetric_cp_infos convs) None
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking decreasingness of CPs using rule labeling for the '')
               \<circ> showsl_trs R \<circ> s)
             }
           | Some (n, prf) \<Rightarrow> do {
             check_left_linear_trs R;
             let (Rnd, Rd) = List.partition (\<lambda>lr. linear_term (snd lr)) R;
             let tp = tp_ops.mk I False [] Rd Rnd;
             check_trs_termination_proof I J a (add_index i 1) tp prf
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below relative termination for rule labeling\<newline>'') \<circ> s);
             check_rule_labeling_eldc string_rename R rl (symmetric_cp_infos convs) (Some n)
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking decreasingness of CPs using rule labeling for the '')
               \<circ> showsl_trs R \<circ> s)
             }
           )})"
| "check_cr_proof a i I J R (Redundant_Rules RS n convs prf) = debug i (STR ''Redundant Rules'') (do {
         check_cr_proof a (add_index i 1) I J RS prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below confluence of modified TRS\<newline>'') \<circ> showsl_trs RS \<circ> s);
         check_redundant_rules R RS n convs
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking redundant rules transformation of the '')
                  \<circ> showsl_trs R \<circ> showsl_lit (STR ''transformed to the '') \<circ> showsl_trs RS \<circ> s)
         })"
| "check_cr_proof a i I J R (Parallel_Closed n) = debug i (STR ''Parallel Closed'') ( do {
           check_parallel_closed string_rename R n
         }  <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking parallel closedness for the '') \<circ> showsl_trs R
             \<circ> s))"
| "check_cr_proof a i I J R (Development_Closed n) = debug i (STR ''Development Closed'') ( do {
           check_development_closed string_rename R n
         }  <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking development closedness for the '') \<circ> showsl_trs R
             \<circ> s))"
| "check_cr_proof a i I J R (Critical_Pair_Closing_System C prf n) = debug i (STR ''Critical-Pair-Closing System'') ( do {
         let tp = tp_ops.mk I False [] C [];
         check_trs_termination_proof I J a (add_index i 1) tp prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization of CPCS\<newline>'')
             \<circ> s);
         check_critical_pair_closing string_rename R C n
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when closing critical pairs of '') \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s)
   })"
| "check_cr_proof a i I J R (Persistent_Decomposition sig ps) = debug i (STR ''Persistent Decomposition'') ( do {
         let checks = map (map_prod id (\<lambda>prf i p. check_cr_proof a i I J p prf)) ps; \<comment> \<open>make primrec happy\<close>
         check_allm (\<lambda>(n, (prf, f)). f (add_index i n) prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error while checking confluence of subproblems\<newline>'') \<circ> s)
         ) (List.enumerate 1 checks);
         check_persistence_cr sig R (map fst ps)
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking persistent decomposition of '')
             \<circ> showsl_trs R \<circ> s)
   })"

fun cr_assms :: "bool \<Rightarrow> ('f, 'l, 'v) cr_proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "cr_assms a (SN_WCR _ p) = sn_assms a p"
| "cr_assms a Weakly_Orthogonal = []"
| "cr_assms a (Strongly_Closed _) = []"
| "cr_assms a (PCP_Closed _ _) = []"
| "cr_assms a (PCP_Rule_Lab _) = []" 
| "cr_assms a (Rule_Labeling _ _ (Some p)) = sn_assms a p"
| "cr_assms a (Rule_Labeling _ _ None) = []"
| "cr_assms a (Rule_Labeling_Conv _ _ (Some (n, p))) = sn_assms a p"
| "cr_assms a (Rule_Labeling_Conv _ _ None) = []"
| "cr_assms a (Redundant_Rules _ _ _ p) = cr_assms a p"
| "cr_assms a (Compositional_PCP _ _ p) = cr_assms a p"
| "cr_assms a (Compositional_PCPS _ _ _ _ sp p) = sn_assms a sp @ cr_assms a p"
| "cr_assms a (Compositional_PCP_Rule_Lab _ _ p) = cr_assms a p"
| "cr_assms a (Parallel_Closed _) = []"
| "cr_assms a (Development_Closed _) = []"
| "cr_assms a (Critical_Pair_Closing_System _ p _) = sn_assms a p"
| "cr_assms a (Persistent_Decomposition _ ps) = concat (map (cr_assms a \<circ> snd) ps)"

lemma check_cr_proof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (cr_assms a prf). holds p" (is "?P a prf")
    and ok: "isOK (check_cr_proof a i I J R prf)"
  shows "CR (rstep (set R))"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i R)
    case (SN_WCR joins_i prof i)
    from SN_WCR(1)
    have cp: "isOK(check_critical_pairs R (critical_pairs_impl string_rename R R) joins_i)"
      and ok: "isOK(check_trs_termination_proof I J a (add_index i 1) (mk False [] R []) prof)" by (auto simp: Let_def)
    from SN_WCR(2) have a: "\<forall> a \<in> set (sn_assms a prof). holds a" by auto
    from check_critical_pairs[OF cp] have WCR: "WCR (rstep (set R))" .
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set R))" by simp
    from Newman[OF SN WCR] show ?case .
  next
    case Weakly_Orthogonal
    then have "isOK(check_weakly_orthogonal string_rename R)" by auto
    from check_weakly_orthogonal[OF this] show ?case by simp
  next
    case (Strongly_Closed n)
    then have "isOK(check_strongly_closed string_rename R n)" by auto
    from check_strongly_closed[OF this] show ?case .
  next
    case (Compositional_PCP C hints p)
    then have ok: "isOK(check_compositional_parallel_pairs string_renameN R C hints)" by auto
    show ?case 
    proof (rule check_compositional_parallel_pairs[OF ok])
      show "CR (rstep (set C))" using Compositional_PCP by auto
    qed
  next
    case (Compositional_PCP_Rule_Lab C hints p)
    hence check: "isOK(check_compositional_pcp_rule_lab string_renameN R C hints)" by auto
    show ?case 
    proof (rule check_compositional_pcp_rule_lab[OF check])
      show "CR (rstep (set C))" using Compositional_PCP_Rule_Lab check by auto
    qed
  next
    case (Compositional_PCPS C P hintsP hints sn_prf cr_prf)
    hence check: "isOK(check_compositional_PCPS string_renameN R C P hintsP hints)" and 
      SN: "isOK (check_trs_termination_proof I J a (add_index i (Suc 0)) (mk False [] P R) sn_prf)" and
      ass: "\<forall> a \<in> set (sn_assms a sn_prf). holds a" by auto
    show ?case 
    proof (rule check_compositional_PCPS[OF check])
      show "CR (rstep (set C))" using Compositional_PCPS check by auto
      have "SN_qrel (qreltrs (mk False [] P R))"  
        using check_trs_termination_proof_with_assms[OF I J SN ass] .
      thus "SN (relto (rstep (set P)) (rstep (set R)))" 
        unfolding qreltrs_sound by (auto intro: SN_rel_imp_SN_relto)
    qed
  next
    case (PCP_Closed hints_cp hints_pcp)
    then have "isOK(check_parallel_critical_pairs_closed_CR string_renameN R hints_cp hints_pcp)" by auto
    from check_parallel_critical_pairs_closed_CR[OF this] show ?case by simp
  next
    case (PCP_Rule_Lab hints)
    then have "isOK(check_pcp_rule_lab string_renameN R hints)" by auto
    from check_pcp_rule_lab[OF this] show ?case by simp
  next
    case (Rule_Labeling rl joins p)
    let ?RndRd = "List.partition (\<lambda>lr. linear_term (snd lr)) R"
    let ?Rnd = "fst ?RndRd"
    let ?Rd = "snd ?RndRd"
    from Rule_Labeling(1) have dec:"isOK(check_rule_labeling_eld string_rename R rl (symmetric_cp_infos joins))" by (auto simp: Let_def)
    have "SN_rel (rstep (R_d (set R))) (rstep (R_nd (set R))) \<and> left_linear_trs (set R)"
    proof (cases p)
      case (Some prof)
      with Rule_Labeling(1) have
        sn:"isOK(check_trs_termination_proof I J a (add_index i 1) (mk False [] ?Rd ?Rnd) prof)"
        and ll: "left_linear_trs (set R)"
        by (auto simp: Let_def)
      from Rule_Labeling(2) Some have a:"\<forall> a \<in> set (sn_assms a prof). holds a" by auto
      have "set ?Rd = R_d (set R)" and "set ?Rnd = R_nd (set R)"
        unfolding R_d_def R_nd_def by auto
      with check_trs_termination_proof_with_assms[OF I J sn a] ll
      show ?thesis by auto
    next
      case None
      with Rule_Labeling(1) have "linear_trs (set R)" by auto
      with linear_imp_SN_rel_d_nd show ?thesis
        unfolding linear_trs_def left_linear_trs_def by auto
    qed
    with check_rule_labeling_eld[OF dec] show ?case by auto
  next
    case (Rule_Labeling_Conv rl convs p)
    let ?RndRd = "List.partition (\<lambda>lr. linear_term (snd lr)) R"
    let ?Rnd = "fst ?RndRd"
    let ?Rd = "snd ?RndRd"
    show ?case
    proof (cases p)
      case None
      with Rule_Labeling_Conv(1) have "isOK(check_rule_labeling_eldc string_rename R rl (symmetric_cp_infos convs) None)"
        and "linear_trs (set R)"
        by (auto simp: Let_def)
      with check_rule_labeling_eldc linear_imp_SN_rel_d_nd show ?thesis
        unfolding linear_trs_def left_linear_trs_def by blast
    next
      case (Some p')
      then obtain n  pr where p':"p' = (n, pr)" by (cases p') auto
      with Some Rule_Labeling_Conv(1) have eldc:"isOK(check_rule_labeling_eldc string_rename R rl (symmetric_cp_infos convs) (Some n))"
        by (auto simp: Let_def)
      from Some p' Rule_Labeling_Conv(1) have
        sn:"isOK(check_trs_termination_proof I J a (add_index i 1) (mk False [] ?Rd ?Rnd) pr)"
        and ll: "left_linear_trs (set R)"
        by (auto simp: Let_def)
      from Rule_Labeling_Conv(2) Some p' have a:"\<forall> a \<in> set (sn_assms a pr). holds a" by auto
      have "set ?Rd = R_d (set R)" and "set ?Rnd = R_nd (set R)"
        unfolding R_d_def R_nd_def by auto
      with check_trs_termination_proof_with_assms[OF I J sn a]
      have "SN_rel (rstep (R_d (set R))) (rstep (R_nd (set R)))" by auto
      from check_rule_labeling_eldc[OF eldc this ll] show ?thesis by auto
    qed
  next
    case (Redundant_Rules RS n convs prof)
    then have "CR (rstep (set RS))" by auto
    moreover from Redundant_Rules have "isOK(check_redundant_rules R RS n convs)" by auto
    ultimately show ?case using check_redundant_rules by blast
  next
    case (Parallel_Closed n)
    then have "isOK(check_parallel_closed string_rename R n)" by auto
    from check_parallel_closed[OF this] show ?case .
  next
    case (Development_Closed n)
    then have "isOK(check_development_closed string_rename R n)" by auto
    from check_development_closed[OF this] show ?case .
  next
    case (Critical_Pair_Closing_System C prof n)
    from Critical_Pair_Closing_System(1)
    have cp: "isOK(check_critical_pair_closing string_rename R C n)"
      and ok: "isOK(check_trs_termination_proof I J a (add_index i 1) (mk False [] C []) prof)" by (auto simp: Let_def)
    from Critical_Pair_Closing_System(2) have a: "\<forall> a \<in> set (sn_assms a prof). holds a" by auto
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set C))" by simp
    from check_critical_pair_closing[OF cp SN] show ?case .
  next
    case (Persistent_Decomposition sig ps)
    have *: "isOK (check_persistence_cr sig R (map fst ps))"
      using Persistent_Decomposition(2) by auto
    have x: "p \<in> set ps \<Longrightarrow> \<exists>i. (i, f p) \<in> set (List.enumerate (Suc 0) (map f ps))" for f p ps
      by (force simp: in_set_conv_nth nth_enumerate_eq)
    have **:
      "p \<in> set ps \<Longrightarrow> \<exists>i. isOK (check_cr_proof a i I J (fst p) (snd p))" for p
      using Persistent_Decomposition(2) x[of p ps "\<lambda>(x, y). (x, \<lambda>i p. check_cr_proof a i I J p y)"]
      by (fastforce split: prod.splits simp: Ball_def map_prod_def Fun.comp_def)
    have "p \<in> set ps \<Longrightarrow> CR (rstep (set (fst p)))" for p
      using **[of p] Persistent_Decomposition(1)[of p "snd p"] Persistent_Decomposition(3)
      by (auto simp: snds.simps)
    then show ?case
      using isOK_check_persistence_cr[OF *] by (force simp: rstep_eq_rstep')
  qed
qed

lemma cr_assms_False[simp]: "cr_assms False prf = []"
  by (induct False "prf" rule: cr_assms.induct) auto

lemma check_cr_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
  and ok: "isOK (check_cr_proof False i I J R prf)"
  shows "CR (rstep (set R))"
  by (rule check_cr_proof_with_assms_sound[OF I J _ ok], simp)

datatype (dead 'f, dead 'l, dead 'v, 'q) ncr_proof =
  SN_NWCR "('f, 'l, 'v) trs_termination_proof"
| Non_Join
    "(('f, 'l) lab, 'v) term"
    "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v, 'q, ('f,'l)lab redtriple_impl) non_join_info"
| NCR_Disj_Subtrs "(('f, 'l)lab, 'v) rules" "('f, 'l, 'v, 'q) ncr_proof"
| NCR_Redundant_Rules "('f, 'l, 'v) trsLL" "nat" "('f, 'l, 'v, 'q) ncr_proof"
| NCR_Persistent_Decomposition "(('f, 'l) lab \<times> (string list \<times> string)) list" "('f, 'l, 'v) trsLL" "('f, 'l, 'v, 'q) ncr_proof"
| NCR_Rule_Removal 
     "('f, 'l, 'v) trsLL" 
     "(((('f,'l)lab,'v)rule) \<times> (('f,'l)lab,'v) rseq) list" 
     "('f, 'l, 'v, 'q) ncr_proof"

datatype (dead 'f, dead 'l, dead 'v, 'q) ncomm_proof =
 Non_Join_Comm
    "(('f, 'l) lab, 'v) term"
    "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v) rseq" "(('f, 'l) lab, 'v, 'q, ('f,'l)lab redtriple_impl) non_join_info"
| Swap_Not_Comm
    "('f, 'l, 'v, 'q) ncomm_proof" 

primrec
  check_ncomm_proof ::
    "showsl \<Rightarrow> 'f lt sig_list \<Rightarrow> (('f ::{showl, compare_order,countable},label_type)lab,string) rules \<Rightarrow>
     ('f lt,string) rules \<Rightarrow> ('f, label_type, string, string) ncomm_proof \<Rightarrow>
     showsl check"
where
  "check_ncomm_proof i F R S (Non_Join_Comm s seq1 seq2 prf) = debug i (STR ''Non_Join'') (do {
         check_non_commute (set F) R S s seq1 seq2 prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when disproving commutation of R: '') 
             \<circ> showsl_trs R \<circ> showsl_nl \<circ> showsl_lit (STR ''and S: '') o showsl_nl o showsl_trs S \<circ> showsl_nl o s)
   })"
| "check_ncomm_proof i F R S (Swap_Not_Comm prf) = debug i (STR ''Swap_Not_Comm'') (do {
         check_ncomm_proof (add_index i 1) F S R prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below swap TRSs'') 
             \<circ> showsl_nl \<circ> s)
   })"

lemma check_ncomm_proof_sound:
  assumes ok: "isOK (check_ncomm_proof i F R S prf)"
  shows "\<not> sig_commute (set F) (set R) (set S)"
  using assms
proof (induction "prf" arbitrary: i F R S)
  case (Non_Join_Comm s seq1 seq2 p i F R S)
  then show ?case using check_non_commute[of "set F" R S s seq1 seq2] by auto
next
  case *: (Swap_Not_Comm "prf")
  from *(2) obtain i where "isOK (check_ncomm_proof i F S R prf)" by auto
  from *(1)[OF this] show ?case using sig_commute_swap by auto
qed

datatype (dead 'f, dead 'l, dead 'v) comm_proof =
  Parallel_Closed_Comm "nat option"
  | Development_Closed_Comm "nat option"
  | PCP_Closed_Comm "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints" 
  | PCP_Rule_Lab_Comm "(('f,'l)lab,'v) pcp_rule_lab_com" 
  | PCP_Compositional_Rule_Lab_Comm "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "(('f,'l)lab,'v) pcp_rule_lab_com" "('f,'l,'v) comm_proof"
  | Compositional_PCPS_Comm "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "('f, 'l, 'v) trsLL" "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints" "(('f,'l)lab,'v)cp_join_hints" "('f, 'l, 'v) trs_termination_proof" "('f, 'l, 'v) comm_proof"
  | Swap_Comm "('f,'l,'v) comm_proof" 
  | CR_Proof "('f,'l,'v) cr_proof"

fun comm_assms :: "bool \<Rightarrow> ('f, 'l, 'v) comm_proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "comm_assms a (Parallel_Closed_Comm _ ) = []"
| "comm_assms a (Development_Closed_Comm _) = []"
| "comm_assms a (PCP_Closed_Comm _ _) = []"
| "comm_assms a (PCP_Rule_Lab_Comm _) = []"
| "comm_assms a (PCP_Compositional_Rule_Lab_Comm _ _ _ p) = comm_assms a p"
| "comm_assms a (Swap_Comm p) = comm_assms a p"
| "comm_assms a (Compositional_PCPS_Comm _ _ _ _ _ _ _ sp p) = sn_assms a sp @ comm_assms a p"
| "comm_assms a (CR_Proof p) = cr_assms a p"

lemma comm_assms_False[simp]: "comm_assms False p = []" 
  by (induct p, auto)

lemma sig_commute_UNIV[simp]: "sig_commute UNIV R S = commute (rstep R) (rstep S)" 
proof 
  show "commute (rstep R) (rstep S) \<Longrightarrow> sig_commute UNIV R S" by (rule commute_imp_sig_commute)
  show "sig_commute UNIV R S \<Longrightarrow> commute (rstep R) (rstep S)" 
    by (intro commuteI, auto)
qed

context 
  fixes I :: "('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops" 
  and J :: "('dpp, ('f, label_type) lab, string) dpp_ops" 
  and a :: bool
begin
primrec
  check_comm_proof ::
    "showsl \<Rightarrow> (('f ::{showl, compare_order,countable},label_type)lab, string) rules \<Rightarrow>
     (('f,label_type)lab,string) rules \<Rightarrow> ('f, label_type,string) comm_proof \<Rightarrow>
     showsl check"
where
  "check_comm_proof i R S (Parallel_Closed_Comm n) = debug i (STR ''Parallel_Closed_Comm'') (
       check_parallel_closed_comm string_rename R S n
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving commutation by almost parallel closed criterion\<newline>'') o s)
   )"
| "check_comm_proof i R S (Development_Closed_Comm n) = debug i (STR ''Development_Closed_Comm'') (
       check_development_closed_comm string_rename R S n
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving commutation by almost development closed criterion\<newline>'') o s)
   )"
| "check_comm_proof i R S (PCP_Closed_Comm hints_cp hints_pcp) = debug i (STR ''PCP_Closed_Comm'') (
       check_parallel_critical_pairs_closed_comm string_renameN R S hints_cp hints_pcp
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving commutation by parallel critical pair closure criterion\<newline>'') o s)
   )"
| "check_comm_proof i R S (PCP_Rule_Lab_Comm hints) = debug i (STR ''PCP_Rule_Lab_Comm'') (
       check_pcp_rule_lab_com string_renameN R S hints
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving commutation by rule labeling with parallel critical pairs\<newline>'') o s)
   )"
| "check_comm_proof i R S (PCP_Compositional_Rule_Lab_Comm C D hints prf) = debug i (STR ''Compositional PCP Rule Labeling'') ( do {
          check_compositional_pcp_rule_lab_comm string_renameN R S C D hints
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking compositional parallel critical pairs \<newline>'') \<circ> s);
          check_comm_proof (add_index i 1) C D prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in proving commutation of sub TRS C\<newline>'') \<circ> showsl_trs C \<circ> showsl_nl o
                showsl_lit (STR '' and sub TRS D of S\<newline>'') o showsl_trs D o showsl_nl o s)
     })"
| "check_comm_proof i R S (Compositional_PCPS_Comm C D P hintsP_RS hintsP_SR hintsRS hintsSR sn_prf com_prf) = debug i (STR ''Compositional PCPS'') ( do {
         let tp = tp_ops.mk I False [] P (remdups (R @ S));
           check_compositional_PCPS_com string_renameN R S C D P hintsP_RS hintsP_SR hintsRS hintsSR
               <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking compositional parallel critical system to switch to TRSs C = \<newline>'')
               o showsl_trs C o showsl_nl 
               o showsl_lit (STR '' and D = \<newline>'')
               o showsl_trs D o showsl_nl 
               \<circ> s);
         check_trs_termination_proof I J a (add_index i 1) tp sn_prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below relative termination proof of compositional CPCS\<newline>'')
             \<circ> s);
          check_comm_proof (add_index i 2) C D com_prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in proving commutation of sub TRSs C and D\<newline>'') \<circ> showsl_trs C \<circ> showsl_nl o showsl_trs D o s)
     })"
| "check_comm_proof i R S (Swap_Comm prf) = debug i (STR ''Swap_Comm'')
       (check_comm_proof (add_index i 1) S R prf)" 
| "check_comm_proof i R S (CR_Proof prf) = debug i (STR ''CR_proof'') (do {
       check_variants_trs R S <+? (\<lambda> err. err o showsl_lit (STR ''\<newline>the TRSs do not coincide''));
       check_variants_trs S R <+? (\<lambda> err. err o showsl_lit (STR ''\<newline>the TRSs do not coincide''));       
       check_cr_proof a (add_index i 1) I J R prf
      })"     

  
lemma check_comm_proof_with_assms_sound:
  assumes  IJ: "tp_spec I" "dpp_spec J" and
    ok: "isOK (check_comm_proof i R S prf)"     
    and ass: "\<forall>p\<in>set (comm_assms a prf). holds p" (is "?P a prf")
  shows "commute (rstep (set R)) (rstep (set S))"
  using ok ass
proof (induction "prf" arbitrary: i R S)
  case (Parallel_Closed_Comm p i R S)
  then show ?case using check_parallel_closed_comm[of _ R S _ UNIV] by auto
next
  case (Development_Closed_Comm p i R S)
  then show ?case using check_development_closed_comm[of _ R S _ UNIV] by auto
next
  case (PCP_Closed_Comm p h1 h2 R S)
  then show ?case using check_parallel_critical_pairs_closed_comm[of _ R S] by simp
next
  case (PCP_Rule_Lab_Comm p h R S)
  then show ?case using check_pcp_rule_lab_com[of _ R S] by simp
next
  case (Swap_Comm p i R S)
  from sig_commute_swap[of UNIV "set S" "set R"]
  show ?case using Swap_Comm by force
next
  case *: (PCP_Compositional_Rule_Lab_Comm C D h p i R S)
  hence "isOK(check_compositional_pcp_rule_lab_comm string_renameN R S C D h)" by auto
  with check_compositional_pcp_rule_lab_comm[OF this] *
  show ?case by auto
next
  case *: (Compositional_PCPS_Comm C D P hP_RS hP_SR hRS hSR sn_prf cr_prf i R S)
  from *
  have check: "isOK (check_compositional_PCPS_com string_renameN R S C D P hP_RS hP_SR hRS hSR)" 
    and IH: "commute (rstep (set C)) (rstep (set D))"
    and sn_prf: "isOK (check_trs_termination_proof I J a (add_index i (Suc 0)) (tp_ops.mk I False [] P (remdups (R @ S))) sn_prf)" 
    and ass: "\<forall>assm\<in>set (sn_assms a sn_prf). holds assm" by auto
  interpret tp_spec I by fact
  show ?case
  proof (rule check_compositional_PCPS_com[OF check IH])
    from check_trs_termination_proof_with_assms[OF IJ sn_prf ass]
    have SN: "SN_qrel (tp_ops.qreltrs I (tp_ops.mk I False [] P (remdups (R @ S))))" .
    thus "SN (relto (rstep (set P)) (rstep (set R \<union> set S)))" 
      unfolding qreltrs_sound by (auto intro: SN_rel_imp_SN_relto)
  qed
next
  case *: (CR_Proof cr_prf i R S)
  from * have "isOK(check_variants_trs R S)" "isOK(check_variants_trs S R)" 
      and cr: "isOK (check_cr_proof a (add_index i (Suc 0)) I J R cr_prf)" by auto
  from check_variants_trs_rstep[OF this(1)] check_variants_trs_rstep[OF this(2)]
  have "rstep (set S) = rstep (set R)" by auto
  hence "commute (rstep (set R)) (rstep (set S)) = CR (rstep (set R))" 
    by (simp add: CR_iff_self_commute)
  also have \<dots> using check_cr_proof_with_assms_sound[OF IJ _ cr] * by auto
  finally show ?case .    
qed
end

lemma check_comm_proof_sound:
  assumes  IJ: "tp_spec I" "dpp_spec J" and
    ok: "isOK (check_comm_proof I J False i R S prf)"     
  shows "commute (rstep (set R)) (rstep (set S))"
  by (rule check_comm_proof_with_assms_sound[OF IJ ok], auto)


primrec
  check_ncr_proof ::
    "bool \<Rightarrow> showsl \<Rightarrow>
     ('tp, ('f::{showl, compare_order,countable}, label_type) lab, string) tp_ops \<Rightarrow>
     ('dpp, ('f, label_type) lab, string) dpp_ops \<Rightarrow> (('f,label_type)lab,string) rules \<Rightarrow>
     ('f, label_type, string, string) ncr_proof \<Rightarrow>
     showsl check"
where
  "check_ncr_proof a i I J R (SN_NWCR prf) = debug i (STR ''SN_NWCR'') (do {
         let tp = tp_ops.mk I False [] R [];
         check_trs_termination_proof I J a (add_index i 1) tp prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error below strong normalization + wcr\<newline>'')
             \<circ> s);
         check (\<not> isOK(check_critical_pairs_NF R (critical_pairs_impl string_rename R R))) (showsl_lit (STR ''all critical pairs are joinable''))
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when disproving local confluence of '') \<circ> showsl_tp I tp \<circ> showsl_nl \<circ> s)
   })"
| "check_ncr_proof a i I J R (Non_Join s seq1 seq2 prf) = debug i (STR ''Non_Join'') (do {
         check_non_cr R s seq1 seq2 prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when disproving CR of '') \<circ> showsl_trs R \<circ> showsl_nl \<circ> s)
   })"
| "check_ncr_proof a i I J R (NCR_Disj_Subtrs R' prf) = debug i (STR ''Modularity'') (do {
      check_modularity_ncr R R'
          <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when applying modularity to switch to '') \<circ> showsl_trs R' \<circ> showsl_nl \<circ> s);
      check_ncr_proof a (add_index i 1) I J R' prf
        <+? (\<lambda> s. i \<circ> showsl_lit (STR '': error below the modular decomposition\<newline>'') \<circ> s)
    })"
| "check_ncr_proof a i I J R (NCR_Redundant_Rules RS n prf) = debug i (STR ''Redundant Rules'') (do {
         check_ncr_proof a (add_index i 1) I J RS prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error when proving nonconfluence of modified TRS\<newline>'') \<circ> showsl_trs RS \<circ> s);
         check_redundant_rules_ncr R RS n
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking redundant rules transformation of the TRS\<newline>'') \<circ> showsl_trs R \<circ> s)
    })"
| "check_ncr_proof a i I J R (NCR_Rule_Removal R_del infos prf) = debug i (STR ''Rule Removal'') (do {
      let S = list_diff R R_del;
      check_ncr_proof a (add_index i 1) I J S prf
         <+? (\<lambda>e. i \<circ> showsl_lit (STR '': error when proving nonconfluence of modified TRS\<newline>'') \<circ> showsl_trs S \<circ> showsl_nl o e);
      check_rule_removal infos R R_del S
           <+? (\<lambda>e. i \<circ> showsl_lit (STR '': error in checking rule removal on the TRS\<newline>'') \<circ> showsl_trs R \<circ> 
            showsl_lit (STR ''\<newline>to switch to TRS\<newline>'') o showsl_trs S o showsl_nl o e)
    })"
| "check_ncr_proof a i I J R (NCR_Persistent_Decomposition sig S prf) = debug i (STR ''Persistent Decomposition'') (do {
         check_ncr_proof a (add_index i 1) I J S prf
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error while proving nonconfluence of resulting TRS\<newline>'') \<circ> showsl_trs S \<circ> s);
         check_persistence_not_cr sig R S
           <+? (\<lambda>s. i \<circ> showsl_lit (STR '': error in checking persistent decomposition of '')
             \<circ> showsl_trs R \<circ> s)
    })"

primrec ncr_assms :: "bool \<Rightarrow> ('f, 'l, 'v, 'q) ncr_proof \<Rightarrow> (('f, 'l, 'v) assm) list" where
  "ncr_assms a (SN_NWCR p) = sn_assms a p"
| "ncr_assms a (NCR_Disj_Subtrs _ p) = ncr_assms a p"
| "ncr_assms a (Non_Join _ _ _ _)  = []"
| "ncr_assms a (NCR_Redundant_Rules _ _ p) = ncr_assms a p"
| "ncr_assms a (NCR_Rule_Removal _ _ p) = ncr_assms a p"
| "ncr_assms a (NCR_Persistent_Decomposition _ _ p) = ncr_assms a p"

lemma check_ncr_proof_with_assms_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
    and fin: "\<forall>p\<in>set (ncr_assms a prf). holds p"
    and ok: "isOK (check_ncr_proof a i I J R prf)"
  shows "\<not> CR (rstep (set R))"
proof -
  interpret tp_spec I by fact
  from ok fin show ?thesis
  proof (induct "prf" arbitrary: i R)
    case (SN_NWCR prof i)
    from SN_NWCR(2) have a: "\<forall> a \<in> set (sn_assms a prof). holds a" by auto
    from SN_NWCR(1)
    have cp: "\<not> isOK(check_critical_pairs_NF R (critical_pairs_impl string_rename R R))"
      and ok: "isOK(check_trs_termination_proof I J a (add_index i 1) (mk False [] R []) prof)" by (auto simp: Let_def)
    from check_trs_termination_proof_with_assms[OF I J ok a] have SN: "SN (rstep (set R))" by simp
    from check_critical_pairs_NF_SN[OF SN] cp show ?case by simp
  next
    case (Non_Join s seq1 seq2 prof)
    then have ok: "isOK (check_non_cr R s seq1 seq2 prof)" by simp
    from check_non_cr[OF ok] show ?case .
  next
    case (NCR_Disj_Subtrs R' prof)
    note IH = this
    from IH(3) have a: "\<forall>p\<in>set (ncr_assms a prof). holds p" by auto
    from IH(2) have ok: "isOK (check_modularity_ncr R R')" by simp
    show ?case
      by (rule check_modularity_ncr[OF ok IH(1)[OF _ a] infinite_lab],
      insert IH(2), auto)
  next
    case (NCR_Redundant_Rules RS n prof)
    then have "\<not> CR (rstep (set RS))" by auto
    moreover from NCR_Redundant_Rules have "isOK(check_redundant_rules_ncr R RS n)" by auto
    ultimately show ?case using check_redundant_rules_ncr by auto
  next
    case *: (NCR_Rule_Removal Rdel info prof)
    let ?S = "list_diff R Rdel" 
    from * obtain i where "isOK(check_ncr_proof a i I J ?S prof)" by auto
    from *(1)[OF this] *(3) have ncr: "\<not> CR (rstep (set ?S))" by auto
    from *[simplified] have ok: "isOK (check_rule_removal info R Rdel ?S)" by auto
    from check_rule_removal[OF _ _ this ncr]
    show ?case by auto
  next
    case (NCR_Persistent_Decomposition sig S prof)
    then have "\<not> CR (rstep (set S))" by auto
    moreover from NCR_Persistent_Decomposition have "isOK (check_persistence_not_cr sig R S)" by auto
    ultimately show ?case by (auto simp: rstep_eq_rstep' isOK_check_persistence_not_cr)
  qed
qed

lemma ncr_assms_False[simp]: "ncr_assms False prf = []"
  by (induct "prf") simp_all

lemma check_ncr_proof_sound:
  assumes I: "tp_spec I" and J: "dpp_spec J"
  and ok: "isOK (check_ncr_proof False i I J R prf)"
  shows "\<not> CR (rstep (set R))"
  by (rule check_ncr_proof_with_assms_sound[OF I J _ ok], simp)

definition default_grd_fun :: "((string,'l)lab,string)term \<Rightarrow> ((string,'l)lab,string)term \<Rightarrow> ((string,'l)lab,string)subst"
  where "default_grd_fun s t \<equiv> let
           F = funs_rule_list (s,t);
           m = fold (\<lambda> f m. case f of Sharp (UnLab g) \<Rightarrow> max (length g) m | _ \<Rightarrow> m) F 0;
           suffix = replicate (Suc m) (CHR ''a'')
         in (\<lambda> x. Fun (Sharp (UnLab (x @ suffix))) [])"

abbreviation Tcap_Not_Unif :: "((string, 'l) lab, string, string,(string, 'l) lab redtriple_impl) non_join_info"
where
  "Tcap_Not_Unif \<equiv> Tcap_Non_Unif default_grd_fun"

end
