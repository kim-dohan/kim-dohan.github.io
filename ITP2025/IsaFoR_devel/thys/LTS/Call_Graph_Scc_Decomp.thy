theory Call_Graph_Scc_Decomp
imports
  Auxx.Gabow_SCC_RBT
  Cooperation_Program
  Show.Shows_Literal
begin
      
locale call_graph_indexed_rewriting = indexed_rewriting induce for
  induce :: "'a \<Rightarrow> ('b \<times> 'b)set" + 
  fixes call_locs :: "'a \<Rightarrow> 'l \<times> 'l"     
  and loc :: "'b \<Rightarrow> 'l"
  and call_graph :: "'a set \<Rightarrow> ('l \<times> 'l)set" 
assumes call_rel: "(b1,b2) \<in> induce a \<Longrightarrow> call_locs a = (loc b1, loc b2)" 
  and call_graph: "call_graph as = call_locs ` as" 
begin
  
lemma cooperation_SN_on_decomposition:  
  assumes SN: "\<And> C. is_scc (call_graph P) C 
    \<Longrightarrow> C \<times> C \<subseteq> (call_graph P)^+ 
    \<Longrightarrow> cooperation_SN_on R ({a . a \<in> P \<and> call_locs a \<in> C \<times> C}) I" 
  shows "cooperation_SN_on R P I" 
proof 
  fix seq
  assume I: "seq 0 \<in> I" and chain: "cooperation_chain R P seq" 
  from cooperation_chainE[OF chain] obtain P' cp where 
    P': "P' \<subseteq> P" and rec: "recurring P' (shift seq cp)" and R: "\<And>i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R" 
    by metis
  define ss where "ss = shift seq cp" 
  let ?loc = "\<lambda> i. loc (ss i)" 
  define L where "L = (\<lambda> i. loc (ss i))" 
  have locP': "(?loc i, ?loc (Suc i)) \<in> call_graph P'" for i using recurring_imp_chain[OF rec[folded ss_def], rule_format, of i]
    unfolding call_graph using call_rel by force
  then have locP: "(L i, L (Suc i)) \<in> call_graph P" for i using P' unfolding call_graph L_def by auto
  define C where "C = range ?loc"
  have Cne: "C \<noteq> {}" unfolding C_def by auto
  have "C \<times> C \<subseteq> (call_graph P)^+" 
  proof
    fix a b
    assume "(a,b) \<in> C \<times> C" 
    then have a: "a \<in> C" "b \<in> C" by auto
    from a(1)[unfolded C_def] obtain i where ai: "a = L i" by (auto simp: L_def)
    from a(2)[unfolded C_def] obtain j where bj: "b = L j" by (auto simp: L_def)
    {
      from recurring_imp_chain[OF rec, folded ss_def, rule_format, of j] obtain tau where 
        tau: "tau \<in> P'" and step: "(ss j, ss (Suc j)) \<in> induce tau" by auto
      from recurring_imp_INFM[OF rec tau, unfolded INFM_nat, rule_format, of i, folded ss_def]
        obtain J where iJ: "i < J" and step': "(ss J, ss (Suc J)) \<in> induce tau" by auto
      from call_rel[OF step] call_rel[OF step'] bj have "b = L J" by (auto simp: L_def)
      with iJ have "\<exists> j. i < j \<and> b = L j" by auto  
    }
    then obtain j where ij: "i < j" and bj: "b = L j" by auto
    show "(a,b) \<in> (call_graph P)^+" unfolding ai bj using ij locP
      using chain_imp_trancl by blast
  qed
  from get_scc_from_component[OF Cne this] obtain S where 
    CS: "C \<subseteq> S" and scc: "is_scc (call_graph P) S" "S \<times> S \<subseteq> (call_graph P)^+" by auto
  let ?P' = "{a \<in> P. call_locs a \<in> S \<times> S}" 
  have P': "P' \<subseteq> ?P'" 
  proof
    fix tau
    assume tau: "tau \<in> P'" 
    from recurring_imp_INFM[OF rec this, folded ss_def] obtain i where "(ss i, ss (Suc i)) \<in> induce tau" 
      unfolding INFM_nat_le by auto
    from call_rel[OF this] have "call_locs tau \<in> C \<times> C" unfolding C_def by auto
    with CS P' tau  
    show "tau \<in> ?P'" by auto
  qed
  from SN[OF scc] have SN: "cooperation_SN_on R ?P' I" .
  show False
  proof (rule cooperation_SN_onE[OF SN, of seq, OF I])
    show "cooperation_chain R ?P' seq" 
      by (rule cooperation_chainI[of P' _ _ cp, OF P' rec], rule R)
  qed
qed
end

type_synonym 'l scc_repr = "'l list"  
type_synonym 'l scc_decomposition_info = "'l scc_repr list"  

context lts
begin
lemma call_graph: "call_graph_indexed_rewriting (transition_step lc) (\<lambda> tau. (source tau, target tau)) location (\<lambda> taus. { (source \<tau>, target \<tau>) | \<tau>. \<tau> \<in> taus})"  
  by (unfold_locales, auto)

definition "call_graph_sharp_impl R = remdups [(source (snd \<tau>), target (snd \<tau>)). \<tau> \<leftarrow> transitions_impl R, is_sharp_transition (snd \<tau>)]"

definition scc_decomposition :: "('f,'v,'ty,'l :: {showl,compare_order} sharp,'tr) lts_impl \<Rightarrow> 'l sharp scc_decomposition_info \<Rightarrow> showsl + _" where
  "scc_decomposition CP sccs_info = do {
      let CG = call_graph_sharp_impl CP;
      let sccs = scc_decomp CG;
      check_allm (\<lambda> C. check (\<exists> D \<in> set sccs_info. set C = set D) 
        (showsl_lit (STR ''could not find SCC '') o showsl C o showsl_lit (STR '' in provided decomposition'')))
        sccs;
      let trans = lts_impl.transitions_impl CP;
      let (sharp, flat) = partition (\<lambda> tau. is_sharp_transition (snd tau)) trans;
      let CPs = map (\<lambda> C. let L = set C in 
        Lts_Impl (lts_impl.initial CP) (flat @ filter (\<lambda> tau. source (snd tau) \<in> L \<and> target (snd tau) \<in> L) sharp) 
          (assertion_impl CP)) sccs_info
      in return CPs <+? (\<lambda> s. showsl_lit (STR ''error is SCC-decomposition w.r.t. sccs_info\<newline>'') o showsl sccs_info o showsl_nl o s)
    }" 
  
lemma scc_decomposition: assumes SN: "\<And> C. C \<in> set CPs \<Longrightarrow> cooperation_SN_impl C" 
  and ret: "scc_decomposition CP sccs_info = return CPs" 
shows "cooperation_SN_impl CP" 
proof -
  note ret = ret[unfolded scc_decomposition_def, simplified, unfolded]
  show ?thesis 
  proof (intro cooperation_SN_implI)
    assume CP: "lts_impl CP"
    show "indexed_rewriting.cooperation_SN_on (transition_step_lts (lts_of CP)) (flat_transitions_of (lts_of CP)) (sharp_transitions_of (lts_of CP)) (initial_states (lts_of CP))"      
    proof (rule call_graph_indexed_rewriting.cooperation_SN_on_decomposition[OF call_graph], goal_cases)
      case (1 C)
      let ?CG = "{(source \<tau>, target \<tau>) |\<tau>. \<tau> \<in> sharp_transitions_of (lts_of CP)}" 
      have CG: "?CG = set (call_graph_sharp_impl CP)" unfolding call_graph_sharp_impl_def 
        by (cases CP, auto)
      from 1 have "C \<in> {C. is_scc (set (call_graph_sharp_impl CP)) C \<and> C \<times> C \<subseteq> (set (call_graph_sharp_impl CP))\<^sup>+}" 
        unfolding CG by auto
      from this[folded scc_decomp] 
      obtain CC where "set CC = C" and "CC \<in> set (scc_decomp (call_graph_sharp_impl CP))" by auto
      with ret obtain D where DC: "set D = C" and D: "D \<in> set sccs_info" by auto
      let ?Q = "Lts_Impl (lts_impl.initial CP)
            ([tau\<leftarrow>transitions_impl CP . \<not> is_sharp_transition (snd tau)] @
             [tau\<leftarrow>transitions_impl CP . is_sharp_transition (snd tau) \<and> source (snd tau) \<in> C \<and> target (snd tau) \<in> C])
            (assertion_impl CP)" 
      have subI: "sub_lts_impl ?Q CP" by (cases CP, auto simp: mset_filter subseteq_mset_def)
      note sub = sub_lts_impl_sub_lts[OF subI]
      from SN D DC ret have SN: "cooperation_SN_impl ?Q" by (auto simp: o_def)
      from sub_lts_impl[OF subI CP(1)] have lts: "lts_impl ?Q" .
      with SN have SN: "cooperation_SN (lts_of ?Q)" by(elim cooperation_SN_implE)
      also have "flat_transitions_of (lts_of ?Q) = flat_transitions_of (lts_of CP)" by force
      also have "initial_states (lts_of ?Q) = initial_states (lts_of CP)" 
        by (auto simp: initial_states_def assertion_of_def)
      also have "sharp_transitions_of (lts_of ?Q) = {a \<in> sharp_transitions_of (lts_of CP). (source a, target a) \<in> C \<times> C}"
        by auto
      finally show ?case by (simp add: assertion_of_def)
    qed
  qed
qed

lemma length_scc_decomposition: assumes "scc_decomposition cp infos = return xs" 
  shows "length infos = length xs" 
  using assms unfolding scc_decomposition_def Let_def by auto

end

  
declare lts.call_graph_sharp_impl_def[code]
declare lts.scc_decomposition_def[code]
  
end
