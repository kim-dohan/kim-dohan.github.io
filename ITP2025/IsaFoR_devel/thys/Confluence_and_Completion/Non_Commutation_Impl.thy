(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2022)
License: LGPL (see file COPYING.LESSER)
*)
theory Non_Commutation_Impl
  imports 
    Commutation
    Non_Confluence_Impl
begin

definition check_non_commute :: "'f lt sig \<Rightarrow> (('f :: {compare_order,showl})lt,string)rules \<Rightarrow> ('f lt,string)rules \<Rightarrow> ('f lt,string)term \<Rightarrow> ('f lt,string)rseq \<Rightarrow> ('f lt,string)rseq \<Rightarrow>
     ('f lt,string,'q :: {showl,compare_order},_)non_join_info \<Rightarrow> showsl check"
  where "check_non_commute F R S s seq1 seq2 reason \<equiv> do {             
             check_funas_term F s;
             let chk = (\<lambda> name R seq. check_rsteps_last R s seq <+? 
               (\<lambda> e. showsl_lit (STR ''problem when checking rewrite steps with TRS '') 
                   o showsl_lit name o showsl_nl o showsl_trs R o showsl_nl o e));
             chk (STR ''S'') S seq1;
             chk (STR ''R'') R seq2;
             check_non_join R S (rseq_last s seq1) (rseq_last s seq2) reason
        }"

lemma check_non_commute: assumes ok: "isOK(check_non_commute F R S s seq1 seq2 prf)"
  shows "\<not> sig_commute F (set R) (set S)"
proof 
  let ?R = "rstep (set R)"
  let ?S = "rstep (set S)"
  assume comm: "sig_commute F (set R) (set S)"
  note ok = ok[unfolded check_non_commute_def Let_def, simplified]
  let ?last = "rseq_last s" 
  let ?l1 = "?last seq1"
  let ?l2 = "?last seq2"
  from check_rsteps_last_sound ok have s1: "(s,?l1) \<in> ?S^*" by auto  
  from check_rsteps_last_sound ok have s2: "(s,?l2) \<in> ?R^*" by auto
  from ok have s: "funas_term s \<subseteq> F" by auto
  from ok have "isOK (check_non_join R S ?l1 ?l2 prf)" by auto
  from sig_commuteD[OF comm s s1 s2] check_non_join[OF this] show False by auto
qed

end
