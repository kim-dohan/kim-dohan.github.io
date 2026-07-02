(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Check_Termination_Common
  imports
    Not_SN.Nontermination_Processors
    SN.Termination_Processors
    Ord.Reduction_Pair_Implementations
    Sem_Lab.Semantic_Labeling_Carrier
begin

instantiation list :: (type) default
begin
definition "default_list \<equiv> []"
instance ..
end

instantiation lab :: (default, type) default
begin
definition "default_lab = UnLab default_class.default"
instance ..
end

type_synonym ('f, 'l, 'v) ruleLL  = "(('f, 'l) lab, 'v) rule"
type_synonym ('f, 'l, 'v) trsLL   = "(('f, 'l) lab, 'v) rules"
type_synonym ('f, 'l, 'v) termsLL = "(('f, 'l) lab, 'v) term list"
type_synonym ('f, 'l, 'v) rseqL   = "((('f, 'l) lab, 'v) rule \<times> (('f, 'l) lab, 'v) rseq) list"
type_synonym ('f, 'l, 'v) dppLL   =
  "bool \<times> bool \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL \<times>
  ('f, 'l, 'v) termsLL \<times>
  ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) qreltrsLL =
  "bool \<times> ('f, 'l, 'v) termsLL \<times> ('f, 'l, 'v) trsLL \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) qtrsLL =
  "bool \<times> ('f, 'l, 'v) termsLL \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) fptrsLL =
  "(('f, 'l)lab, 'v) forb_pattern list \<times> ('f, 'l, 'v) trsLL"

type_synonym ('f, 'l, 'v) prob = "('f, 'l, 'v) qreltrsLL + ('f, 'l, 'v) dppLL"

type_synonym ('f, 'l, 'v) complexityLL =
  "('f, 'l, 'v) termsLL \<times> 
   ('f, 'l, 'v) trsLL \<times> 
   ('f, 'l, 'v) trsLL \<times> 
   (('f,'l)lab,'v) complexity_measure \<times>
   complexity_class"

fun mk_dpp_set where
  "mk_dpp_set (nfs, m, p, pw, q, r, rw) = (nfs, m, set p, set pw, set q, set r, set rw)"

fun mk_dpp_nt_set where
  "mk_dpp_nt_set (nfs, m, p, pw, q, r, rw) = (nfs, set p \<union> set pw, set q, set r \<union> set rw)"

fun mk_tp_set where
  "mk_tp_set (nfs, q, r, rw) = (nfs, set q, set r, set rw)"

fun mk_tp_nt_set where
  "mk_tp_nt_set (nfs, q, r) = (nfs, set q, set r, {})"

fun mk_fptp_set where
  "mk_fptp_set (fp, r) = (set fp, set r)"

type_synonym unknown_info = string

datatype (dead 'f, dead 'l, dead 'v)problem = 
  SN_TRS "('f,'l,'v)qreltrsLL"
| SN_FP_TRS "('f,'l,'v)fptrsLL" 
| Finite_DPP "('f,'l,'v) dppLL"
| Unknown_Problem unknown_info
| Not_SN_TRS "('f,'l,'v)qtrsLL" 
| Not_RelSN_TRS "('f,'l,'v)qreltrsLL" 
| Infinite_DPP "('f,'l,'v) dppLL"
| Not_SN_FP_TRS "('f,'l,'v)fptrsLL" 
| Complexity_Problem "('f,'l,'v)complexityLL"

consts unknown_satisfied :: "unknown_info \<Rightarrow> bool"

definition "SN_fpstep fptrs \<equiv> case fptrs of (p,r) \<Rightarrow> SN (fpstep p r)"

fun satisfied :: "('f,'l,'v)problem \<Rightarrow> bool" where
  "satisfied (SN_TRS t) = SN_qrel (mk_tp_set t)"
| "satisfied (SN_FP_TRS t) = SN_fpstep (mk_fptp_set t)"
| "satisfied (Finite_DPP d) = finite_dpp (mk_dpp_set d)"
| "satisfied (Unknown_Problem s) = unknown_satisfied s"
| "satisfied (Not_SN_TRS (nfs,q,r)) = (\<not> SN (qrstep nfs (set q) (set r)))"
| "satisfied (Not_RelSN_TRS (nfs,q,r,rw)) = (\<not> SN_qrel (nfs, set q, set r, set rw))"
| "satisfied (Infinite_DPP d) = infinite_dpp (mk_dpp_nt_set d)"
| "satisfied (Not_SN_FP_TRS t) = (\<not> SN_fpstep (mk_fptp_set t))"
| "satisfied (Complexity_Problem (q,s,w,cm,cc)) = deriv_bound_measure_class (rel_qrstep (False, set q, set s, set w)) cm cc"

datatype (dead 'f, dead 'l, dead 'v)assm = 
  SN_assm "('f,'l,'v)problem list" "('f,'l,'v)qreltrsLL" 
| SN_FP_assm "('f,'l,'v)problem list" "('f,'l,'v)fptrsLL"
| Finite_assm "('f,'l,'v)problem list" "('f,'l,'v)dppLL"
| Unknown_assm "('f,'l,'v)problem list" unknown_info
| Not_SN_assm "('f,'l,'v)problem list" "('f,'l,'v)qtrsLL" 
| Not_RelSN_assm "('f,'l,'v)problem list" "('f,'l,'v)qreltrsLL" 
| Not_SN_FP_assm "('f,'l,'v)problem list" "('f,'l,'v)fptrsLL"
| Infinite_assm "('f,'l,'v)problem list" "('f,'l,'v)dppLL"
| Complexity_assm "('f,'l,'v)problem list" "('f,'l,'v)complexityLL"

primrec holds :: "('f, 'l, 'v) assm \<Rightarrow> bool" where
  "holds (SN_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (SN_TRS p))"
| "holds (SN_FP_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (SN_FP_TRS p))"
| "holds (Finite_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Finite_DPP p))"
| "holds (Unknown_assm as s) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> unknown_satisfied s)"
| "holds (Not_SN_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Not_SN_TRS p))"
| "holds (Not_RelSN_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Not_RelSN_TRS p))"
| "holds (Infinite_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Infinite_DPP p))"
| "holds (Not_SN_FP_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Not_SN_FP_TRS p))"
| "holds (Complexity_assm as p) = ((\<forall> a \<in> set as. satisfied a) \<longrightarrow> satisfied (Complexity_Problem p))"

datatype (dead 'f,dead 'l,dead 'v,'a,'b,'c,'d,'e)generic_assm_proof = 
  SN_assm_proof "('f,'l,'v)qreltrsLL" 'a
| Finite_assm_proof "('f,'l,'v)dppLL" 'b
| SN_FP_assm_proof "('f,'l,'v)fptrsLL" 'c
| Not_SN_assm_proof "('f,'l,'v)qtrsLL" 'a
| Infinite_assm_proof "('f,'l,'v)dppLL" 'b
| Not_RelSN_assm_proof "('f,'l,'v)qreltrsLL" 'c
| Not_SN_FP_assm_proof "('f,'l,'v)fptrsLL" 'd
| Complexity_assm_proof "('f,'l,'v)complexityLL" 'a
| Unknown_assm_proof unknown_info 'e

primrec assm_proof_to_problem :: "('f,'l,'v,'a,'b,'c,'d,'e) generic_assm_proof \<Rightarrow> ('f,'l,'v) problem" where
  "assm_proof_to_problem (SN_assm_proof t prf) = SN_TRS t"
| "assm_proof_to_problem (SN_FP_assm_proof t prf) = SN_FP_TRS t"
| "assm_proof_to_problem (Finite_assm_proof d prf) = Finite_DPP d"
| "assm_proof_to_problem (Unknown_assm_proof p prf) = Unknown_Problem p"
| "assm_proof_to_problem (Not_SN_assm_proof t prf) = Not_SN_TRS t"
| "assm_proof_to_problem (Not_RelSN_assm_proof t prf) = Not_RelSN_TRS t"
| "assm_proof_to_problem (Infinite_assm_proof d prf) = Infinite_DPP d"
| "assm_proof_to_problem (Not_SN_FP_assm_proof t prf) = Not_SN_FP_TRS t"
| "assm_proof_to_problem (Complexity_assm_proof t prf) = Complexity_Problem t"

type_synonym dummy_prf = unit

type_synonym ('f,'l,'v,'a,'b,'c,'d)assm_proof = "('f,'l,'v,'a,'b,'c,dummy_prf,'d)generic_assm_proof"
type_synonym ('f,'l,'v,'a)cpx_assm_proof = "('f,'l,'v,'a,dummy_prf,dummy_prf,dummy_prf,dummy_prf)generic_assm_proof"

definition missing :: "String.literal \<Rightarrow> showsl \<Rightarrow> showsl"
  where
    "missing s x = showsl (STR ''the '') \<circ> showsl s \<circ> showsl (STR '' '') \<circ> x \<circ> showsl (STR '' is missing'')"

definition toomuch :: "String.literal \<Rightarrow> showsl \<Rightarrow> showsl"
  where
    "toomuch s x = showsl_lit (STR ''superfluous '') \<circ> showsl_lit s \<circ> showsl_lit (STR '' '') \<circ> x"

end
