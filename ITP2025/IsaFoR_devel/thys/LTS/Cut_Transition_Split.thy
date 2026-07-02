text \<open>If we have a standard cooperation problem with left-part R (flat \<rightarrow> flat), middle part CT
  (flat \<rightarrow> sharp) and right part P (sharp \<rightarrow> sharp), then we can split the problem into several
  ones (R, CTi, P). It only has to be guaranteed that each transition flat \<rightarrow> sharp of CT must
  be covered by some CTi, whenever the sharp-location occurs in P.\<close>
  
theory Cut_Transition_Split
  imports Cooperation_Program
begin
  
text \<open>First, the abstract setting.\<close>  
context indexed_rewriting
begin

lemma cut_transition_split: assumes S: "\<And> b1 b2. (b1,b2) \<in> Induce P \<Longrightarrow> f b1 \<in> S'"
  and S_CT: "\<And> ct b1 b2. ct \<in> R \<Longrightarrow> (b1,b2) \<in> induce ct \<Longrightarrow> f b2 \<in> S' \<Longrightarrow> ct \<in> CT" 
  and S_R: "\<And> b1 b2. (b1,b2) \<in> Induce R \<Longrightarrow> f b1 \<notin> S" 
  and RR: "\<And> aR b1 b2. aR \<in> R \<Longrightarrow> (b1,b2) \<in> induce aR \<Longrightarrow> f b2 \<notin> S \<Longrightarrow> aR \<in> RR" 
  and I: "f ` I \<inter> S = {}" 
  and S': "S' \<subseteq> S" 
  and SN: "\<And> ct. ct \<in> CT \<Longrightarrow> \<exists> RRR. insert ct RR \<subseteq> RRR \<and> cooperation_SN_on RRR P I" 
shows "cooperation_SN_on R P I" 
proof 
  fix seq
  assume I0: "seq 0 \<in> I" and chain: "cooperation_chain R P seq" 
  from cooperation_chainE[OF chain] obtain cp P' where P': "P' \<subseteq> P" 
    and rec: "recurring P' (shift seq cp)" 
    and R: "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R" by metis
  from recurring_imp_chain[OF rec, rule_format, of 0] P'
  have "(seq cp, seq (Suc cp)) \<in> Induce P" by auto
  from S[OF this] have fS: "f (seq cp) \<in> S'" .
  from I0 I this S' have cp0: "cp \<noteq> 0" by auto
  with R[of "cp - 1"] obtain ct where 
    "ct \<in> R" and cut_step: "(seq (cp - 1), seq cp) \<in> induce ct" by auto
  from S_CT[OF this fS] have ct: "ct \<in> CT" .
  from SN[OF this] obtain RRR where RRR: "insert ct RR \<subseteq> RRR" and SN: "cooperation_SN_on RRR P I" by auto
  have "cooperation_chain RRR P seq" 
  proof (intro cooperation_chainI[OF P' rec])
    fix i
    assume i: "i < cp" 
    then show "(seq i, seq (Suc i)) \<in> Induce RRR"
    proof (cases "i = cp - 1")
      case True
      with RRR cut_step cp0 show ?thesis by auto
    next
      case False
      with i have "Suc i < cp" by auto
      from S_R[OF R[OF this]] have fS: "f (seq (Suc i)) \<notin> S" by auto
      from R[OF i] obtain r where "r \<in> R" "(seq i, seq (Suc i)) \<in> induce r" by auto
      from RR[OF this fS] RRR this(2) show ?thesis by auto
    qed
  qed
  from cooperation_SN_onE[OF SN I0 this] show False .
qed
end

text \<open>Next, the application to cooperation programs.\<close>
context lts
begin

lemma cut_transition_split_cooperation_SN: assumes S: "source ` (sharp_transitions_of P) = S"
  and S_CT: "\<And> ct. ct \<in> flat_transitions_of P \<Longrightarrow> target ct \<in> S \<Longrightarrow> ct \<in> CT"  
  and RR: "\<And> r. r \<in> flat_transitions_of P \<Longrightarrow> \<not> is_sharp (target r) \<Longrightarrow> r \<in> RR" 
  and I: "\<And> l. l \<in> lts.initial P \<Longrightarrow> \<not> is_sharp l" 
  and SN: "\<And> ct. ct \<in> CT \<Longrightarrow> 
    \<exists> RRR. insert ct RR \<subseteq> RRR \<and> indexed_rewriting.cooperation_SN_on (transition_step_lts P) RRR (sharp_transitions_of P) (initial_states P)"
shows "cooperation_SN P" 
proof -
  let ?R = "transition_step_lts P"
  interpret indexed_rewriting ?R .
  show ?thesis
  proof (rule indexed_rewriting.cut_transition_split[of _ _ location S _ CT "range Sharp" RR, OF _ _ _ _ _ _ SN], goal_cases)
    case (1 b1 b2)    
    then obtain r where "(b1,b2) \<in> ?R r" and r: "r \<in> sharp_transitions_of P" by auto
    then have id: "location b1 = source r" by (cases b1, cases b2, cases r, auto)
    have "location b1 \<in> source ` sharp_transitions_of P" unfolding id using r by auto
    with S show "location b1 \<in> S" by auto
  next
    case (2 ct b1 b2)
    from 2(1-2) have "target ct = location b2" by (cases b1, cases b2, cases ct, auto)
    from S_CT[OF 2(1) 2(3)[folded this]] show "ct \<in> CT" .
  next
    case (3 b1 b2)
    then obtain r where "(b1,b2) \<in> ?R r" and r: "r \<in> flat_transitions_of P" by auto
    then have id: "location b1 = source r" by (cases b1, cases b2, cases r, auto)
    show ?case unfolding id using r by auto
  next
    case (4 r b1 b2)
    then have id: "location b2 = target r" by (cases b1, cases b2, cases r, auto)
    from RR[OF 4(1)] 4(3) show ?case unfolding id by (cases "target r", auto)
  next
    case 5
    show ?case using I unfolding initial_states_def by force
  next
    case 6 
    show "S \<subseteq> range Sharp" unfolding S[symmetric] by (metis (no_types, lifting) image_Collect_subsetI is_sharp.elims(2) range_eqI)
  qed 
qed

lemma cut_transition_split_main: assumes 
    flat_sharp: "\<And> ct. ct \<in> flat_transitions_of P \<Longrightarrow> is_sharp (target ct) \<Longrightarrow> \<exists> i \<le> (n :: nat). ct \<in> Q i"   
  and Q0: "\<And> ct ct'. ct \<in> Q 0 \<Longrightarrow> ct' \<in> sharp_transitions_of P \<Longrightarrow> target ct \<noteq> source ct'" 
  and R: "\<And> r. r \<in> flat_transitions_of P \<Longrightarrow> \<not> is_sharp (target r) \<Longrightarrow> r \<in> R" 
  and I: "\<And> l. l \<in> lts.initial P \<Longrightarrow> \<not> is_sharp l" 
  and SN: "\<And> i. 1 \<le> i \<Longrightarrow> i \<le> n \<Longrightarrow>  
    indexed_rewriting.cooperation_SN_on (transition_step_lts P) (Q i \<union> R) (sharp_transitions_of P) (initial_states P)"
shows "cooperation_SN P" 
proof -
  let ?CT = "\<Union> (Q ` {1 .. n})" 
  show ?thesis
  proof (rule cut_transition_split_cooperation_SN[OF refl _ R I, where CT = ?CT])
    fix ct
    assume ct: "ct \<in> flat_transitions_of P" "target ct \<in> source ` sharp_transitions_of P" 
    then have "is_sharp (target ct)" by auto
    from flat_sharp[OF ct(1) this] obtain i where i: "i \<le> n" "ct \<in> Q i" by auto
    {
      from ct obtain ct' where ct': "ct' \<in> sharp_transitions_of P" "target ct = source ct'" by auto
      assume "i = 0" 
      with i have "ct \<in> Q 0" by auto
      from Q0[OF this ct'(1)] ct'(2) have False by auto
    }
    then have i1: "1 \<le> i" by (cases i, auto)
    then show "ct \<in> \<Union> (Q ` {1..n})" using i by auto
  next
    fix ct
    assume "ct \<in> ?CT" 
    then obtain i where "1 \<le> i" "i \<le> n" and ct: "ct \<in> Q i" by auto
    from SN[OF this(1-2)]
    have "indexed_rewriting.cooperation_SN_on (transition_step_lts P) (Q i \<union> R) (sharp_transitions_of P) (initial_states P)" .
    with ct show "\<exists>RRR. insert ct R \<subseteq> RRR \<and>
                indexed_rewriting.cooperation_SN_on (transition_step_lts P) RRR (sharp_transitions_of P) (initial_states P)"
      by (intro exI[of _ "Q i \<union> R"], auto)
  qed
qed
end
  
text \<open>Next, an executable checker.\<close>
type_synonym 'l cut_transition_split_repr = "'l list" 
datatype 'l cut_transition_split_info = Cut_Transition_Split_Info "'l cut_transition_split_repr list" 
  (* list of cut-transition sets *)
  
fun cut_transition_split where
  "cut_transition_split (Cut_Transition_Split_Info ct_ids) CP = do {
       let (P,R) = partition (is_sharp_transition o snd) (transitions_impl CP);
       let (CT,RR) = partition (is_sharp o target o snd) R; 
       let Slist = map (source o snd) P; 
       let S = set Slist;
       let CT_ids = set (concat ct_ids);
       check_allm (\<lambda> l. check (\<not> is_sharp l) 
          (showsl_lit (STR ''initial state '') o showsl l o showsl_lit (STR '' must not be sharped''))) (initial CP); 
       check_allm (\<lambda> (t_id, ct). check (target ct \<in> S \<longrightarrow> t_id \<in> CT_ids) 
          (showsl_lit (STR ''did not find cut-transition '') o showsl t_id o 
           showsl_lit (STR '' in partition\<newline>relevant cut-points are: '') o showsl_list Slist)) CT;
       let RRP = RR @ P;
       return (map (\<lambda> ct_ids'. 
         Lts_Impl (initial CP) ((filter (\<lambda> ct. fst ct \<in> set ct_ids') CT) @ RRP) (assertion_impl CP)) ct_ids)
    } <+? (\<lambda> s. showsl_lit (STR ''error in splitting cut transitions on LTS\<newline>'') o s)" 

context lts
begin
lemma cut_transition_split: assumes SN: "\<And> CP'. CP' \<in> set CPs \<Longrightarrow> cooperation_SN_impl CP'"
  and res: "cut_transition_split info CP = return CPs" 
shows "cooperation_SN_impl CP"
proof (cases info)
  case (Cut_Transition_Split_Info ct_ids) note * = this
  let ?CP = "lts_of CP"
  obtain R P where p1: "partition (is_sharp_transition \<circ> snd) (transitions_impl CP) = (P,R)" by auto
  from arg_cong[OF p1, of fst, unfolded partition_filter1]
  have P: "P = filter (is_sharp_transition o snd) (transitions_impl CP)" by auto
  from arg_cong[OF p1, of snd, unfolded partition_filter2]
  have R: "R = filter (Not o is_sharp_transition o snd) (transitions_impl CP)" by (auto simp: o_def)
  then have RR: "snd ` set R = flat_transitions_of ?CP" by auto
  have PP: "snd ` set P = sharp_transitions_of ?CP" unfolding P by auto
  then have S: "source ` sharp_transitions_of ?CP = source ` snd ` set P" by auto
  obtain RR CT where p2: "partition (is_sharp \<circ> target \<circ> snd) R = (CT,RR)" by auto
  note CT_RR = partition_filter_conv[of "(is_sharp \<circ> target \<circ> snd)" R, unfolded p2]
  then have CT: "CT = filter (is_sharp \<circ> target \<circ> snd) R" and RRR: "RR = filter (Not o is_sharp \<circ> target o snd) R" 
    by (auto simp: o_def)
  note res = res[unfolded * cut_transition_split.simps Let_def p1 p2 split, simplified]
  from res have init: "\<And> l. l \<in> lts.initial (lts_of CP) \<Longrightarrow> \<not> is_sharp l" by auto
  let ?n = "length ct_ids" 
  let ?Q = "\<lambda> j. if j = 0 then { t. \<exists> i. (i,t) \<in> set CT \<and> i \<notin> set (concat ct_ids)} 
     else { t. \<exists> i. (i,t) \<in> set CT \<and> i \<in> set (ct_ids ! (j - 1))}" 
  define Q where "Q = ?Q" 
  show ?thesis
  proof (intro cooperation_SN_implI cut_transition_split_main[OF _ _ _ init, of _ ?n Q "snd ` set RR"]; (unfold RR[symmetric])?)
    fix r
    assume "r \<in> snd ` set R" "\<not> is_sharp (target r)" 
    then show "r \<in> snd ` set RR" using CT_RR by auto
  next
    fix ct
    assume *:  "ct \<in> snd ` set R" "is_sharp (target ct)"  
    then have ct: "ct \<in> snd ` set CT" unfolding CT unfolding P R by auto
    then obtain t_id where tid: "(t_id,ct) \<in> set CT" by auto
    show "\<exists>i\<le>?n. ct \<in> Q i" 
    proof (cases "t_id \<in> set (concat ct_ids)")
      case False
      with tid show ?thesis by (intro exI[of _ 0], auto simp: Q_def)
    next
      case True
      then obtain cts where "t_id \<in> set cts" and "cts \<in> set ct_ids" by auto
      from this(2)[unfolded set_conv_nth] this(1) obtain j where "j < ?n" "t_id \<in> set (ct_ids ! j)" by auto
      with tid show ?thesis by (intro exI[of _ "Suc j"], auto simp: Q_def)
    qed
  next
    fix j :: nat
    let ?j = "j - 1"
    let ?cts = "ct_ids ! ?j" 
    assume j: "1 \<le> j" "j \<le> ?n" and CP: "lts_impl CP" 
    then have "?j < ?n" by auto
    then have ct_ids: "ct_ids ! ?j \<in> set ct_ids" unfolding set_conv_nth by auto
    let ?NR = "Lts_Impl (lts_impl.initial CP) ([ct\<leftarrow>CT . fst ct \<in> set ?cts] @ RR @ P) (assertion_impl CP)" 
    let ?N = "lts_of ?NR" 
    from res ct_ids
    have NR: "?NR \<in> set CPs" by auto
    have sub: "sub_lts_impl ?NR CP"  unfolding RRR P R CT by (cases CP, auto simp: mset_filter subseteq_mset_def)
    from sub_lts_impl[OF sub CP] have lts: "lts_impl ?NR".
    from SN[OF NR, unfolded cooperation_SN_impl_def, rule_format, OF lts]
    have SN: "cooperation_SN ?N" .
    also have "transition_step_lts ?N = transition_step_lts ?CP"
      by (cases CP, auto simp: assertion_of_def)
    also have "initial_states ?N = initial_states ?CP"
      by (cases CP, auto simp: assertion_of_def initial_states_def)
    also have "sharp_transitions_of ?N = sharp_transitions_of ?CP"
      unfolding PP[symmetric] by (cases CP, auto simp: P RRR R CT)
    also have "flat_transitions_of ?N = Q j \<union> snd ` set RR" 
      unfolding CT RRR R P Q_def using j by (cases CP, auto)
    finally 
    show "indexed_rewriting.cooperation_SN_on (transition_step_lts (lts_of CP)) (Q j \<union> snd ` set RR) 
       (sharp_transitions_of (lts_of CP)) (initial_states (lts_of CP))" .
  next
    fix ct ct'
    assume ct: "ct \<in> Q 0" "ct' \<in> sharp_transitions_of (lts_of CP)" 
    from this[unfolded Q_def] obtain t_id where "(t_id,ct) \<in> set CT" "t_id \<notin> set (concat ct_ids)" by auto
    with res have "target ct \<notin> (source \<circ> snd) ` set P" by auto
    with ct(2) show "target ct \<noteq> source ct'" unfolding P by (auto simp: o_def)
  qed
qed

end
  
lemma length_cut_transition_split: assumes "cut_transition_split (Cut_Transition_Split_Info infos) cp = return xs" 
  shows "length infos = length xs" 
  using assms by auto
    
declare cut_transition_split.simps[simp del]
end
