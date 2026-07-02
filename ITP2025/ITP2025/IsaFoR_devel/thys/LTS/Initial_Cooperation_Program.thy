theory Initial_Cooperation_Program
imports 
  Cooperation_Program
  Auxx.Cut_Points
begin

context lts
begin
definition exists_cut :: "('f,'v,'t,'l) cooperation_problem \<Rightarrow> 'l \<Rightarrow> bool" where
"exists_cut P l \<equiv>
  (\<exists> \<tau> \<in> transition_rules P. source \<tau> = Flat l \<and> target \<tau> = Sharp l \<and> skip_transition \<tau>)"

lemma cut_transition:
  assumes cut: "exists_cut P l"
  and \<alpha>: "assignment \<alpha>" "\<alpha> \<Turnstile> assertion P (Flat l)"
  and lc: "assertion P (Flat l) = assertion P (Sharp l)" 
shows "(State \<alpha> (Flat l), State \<alpha> (Sharp l)) \<in> transition P"
proof -
  from assms[unfolded exists_cut_def] obtain \<tau> where *: "\<tau> \<in> transition_rules P" 
    "source \<tau> = Flat l" "target \<tau> = sharp.Sharp l" "skip_transition \<tau>" by auto
  from skip_transition[OF *(1) *(4), of \<alpha>] \<alpha> lc
  show ?thesis unfolding *(2-3) by auto
qed

definition "copy_prog P R l \<equiv>
  lts.initial P = Flat ` (lts.initial R) \<and>   
  exists_cut P l \<and>
  (\<forall> \<tau> \<in> transition_rules R. flat_transition \<tau> \<in> transition_rules P \<and> sharp_transition \<tau> \<in> transition_rules P) \<and>
  (assertion P = assertion R \<circ> natural)"
  
definition "copy_progs Ps R CP \<equiv>  
  cut_points (call_graph_of_lts R) CP \<and> 
  (\<forall> l \<in> CP. \<exists> P \<in> Ps. copy_prog P R l)"
  
context fixes P :: "('f,'v,'t,'l sharp)lts" and R :: "('f,'v,'t,'l) lts" and l :: "'l" assumes copy: "copy_prog P R l" begin

private lemmas * = copy[unfolded copy_prog_def]

lemma copy_progD1: "lts.initial P = Flat ` (lts.initial R)" by (insert *, auto)
lemma copy_progD2: "exists_cut P l" by (insert *, auto)
lemma copy_progD3:
  assumes "\<tau> \<in> transition_rules R"
  shows "flat_transition \<tau> \<in> transition_rules P" and "sharp_transition \<tau> \<in> transition_rules P"
  by (insert assms *, auto)
lemma copy_progD4: "assertion P = assertion R \<circ> natural" by (insert *, auto)
end

lemmas copy_progD[dest] = copy_progD1 copy_progD2 copy_progD3 copy_progD4

lemma copy_progI[intro]:
  assumes "lts.initial P = Flat ` (lts.initial R)"
      and "exists_cut P l"
      and "\<And>\<tau>. \<tau> \<in> transition_rules R \<Longrightarrow> flat_transition \<tau> \<in> transition_rules P"
      and "\<And>\<tau>. \<tau> \<in> transition_rules R \<Longrightarrow> sharp_transition \<tau> \<in> transition_rules P"
      and "assertion P = assertion R \<circ> natural" 
  shows "copy_prog P R l" unfolding copy_prog_def using assms by auto

lemma initial_states_copy_prog[simp]: assumes "copy_prog P R l"
  shows "initial_states P = flat_state ` initial_states R"
proof -
  from assms
  have "initial_states P \<supseteq> flat_state ` initial_states R" 
    by (auto simp: initial_states_def image_def copy_progD1 copy_progD4)
  moreover
  {
    fix s
    assume "s \<in> initial_states P" 
    from this[unfolded initial_states_def copy_progD1[OF assms]] obtain l where
      loc: "location s = Flat l"  and l: "l \<in> lts.initial R"
       and s: "state_lts P s" by auto
    then have "s \<in> flat_state ` initial_states R" unfolding initial_states_def image_def
      unfolding copy_progD4[OF assms]
      by (cases s, auto intro: exI[of _ "State _ _"])
  }
  ultimately show ?thesis by auto
qed
 

definition cut_chain where "cut_chain (cutpoint::nat) seq i \<equiv>
  if i \<le> cutpoint then flat_state (seq i)
  else sharp_state (seq (i-1))"

lemma cut_chain_simps[simp]:
  "i \<le> cp \<Longrightarrow> cut_chain cp seq i = flat_state (seq i)"
  "\<not> (i \<le> cp) \<Longrightarrow> cut_chain cp seq i = sharp_state (seq (i-1))"
  unfolding cut_chain_def by auto
    
lemma shift_cut_chain:
  "n > cp \<Longrightarrow> shift (cut_chain cp seq) n = sharp_state \<circ> shift seq (n-1)"
  by(auto simp: cut_chain_def)

lemma sharp_chain:
  assumes chain: "chain (transitions_step lc \<tau>s) seq"
  shows "chain (transitions_step (lift_state_conditions lc) (sharp_transition ` \<tau>s)) (sharp_state \<circ> seq)"
proof
  let ?seq = "sharp_state \<circ> seq"
  let ?lc = "lift_state_conditions lc"
  fix i
  from chain obtain \<tau>
    where \<tau>: "\<tau> \<in> \<tau>s" and step: "(seq i, seq (Suc i)) \<in> transition_step lc \<tau>" by force
  from step have "(?seq i, ?seq (Suc i)) \<in> transition_step ?lc (sharp_transition \<tau>)"
    by (auto intro!: sharp_transition)
  with \<tau> show "(?seq i, ?seq (Suc i)) \<in> transitions_step ?lc (sharp_transition ` \<tau>s)" by auto
qed

lemma initial_cooperation_program:
  assumes fin: "finite (transition_rules R)"
      and copy: "copy_progs Ps R CP"
      and lts: "lts R"
      and SN: "\<And> P. P \<in> Ps \<Longrightarrow> cooperation_SN P"
  shows "lts_termination R"
proof (rule ccontr)
  let ?transition_step = "transition_step_lts R" 
  let ?lifted_step = "transition_step (lift_state_conditions (state_lts R))"

  interpret indexed_rewriting ?transition_step .

  assume "\<not> lts_termination R"
  then obtain seq
    where init: "seq 0 \<in> initial_states R" and chain: "chain (transition R) seq" by auto
  from chain_imp_recurring[OF fin chain[unfolded transition_def]]
  obtain m \<tau>s where \<tau>s: "\<tau>s \<subseteq> transition_rules R" and rec: "recurring \<tau>s (shift seq m)" by auto
  interpret sharp_morphism: rule_morphism sharp_state \<tau>s sharp_transition ?transition_step ?lifted_step
    by (standard, auto simp: sharp_transition)
  interpret flat_morphism: rule_morphism flat_state \<tau>s flat_transition ?transition_step ?lifted_step
    by (standard, auto simp: flat_transition)
  {
    fix i
    assume "i \<ge> m" 
    then have "i = m + (i - m)" by auto
    with recurring_imp_chain[OF rec, rule_format, of "i - m"] have 
      "(seq i, seq (Suc i)) \<in> \<Union> (?transition_step ` \<tau>s)" by auto
  } note steps = this
  define L where "L = { location (seq k) | k. k \<ge> m}"   
  {
    fix l1 l2 
    assume l1: "l1 \<in> L" and l2: "l2 \<in> L" 
    from l1[unfolded L_def] obtain k1 where kl1: "location (seq k1) = l1" and k1: "k1 \<ge> m" by auto
    from l2[unfolded L_def] obtain k2 where kl2: "location (seq k2) = l2" and k2: "k2 \<ge> m" by auto
    from steps[OF k2] obtain \<tau> where step: "(seq k2, seq (Suc k2)) \<in> ?transition_step \<tau>"
      and tau: "\<tau> \<in> \<tau>s" by auto
    with kl2 have tau_l2: "source \<tau> = l2"  by (cases \<tau>, auto)
    from recurring_imp_INFM[OF rec tau, unfolded INFM_nat_le, rule_format, of "Suc k1"]
    obtain n where *: "n \<ge> Suc k1" "(seq (n + m), seq (Suc (n + m))) \<in> ?transition_step \<tau>" by auto
    define k2 where "k2 = n + m"       
    from * have k2: "k2 > k1" and step: "(seq k2, seq (Suc k2)) \<in> ?transition_step \<tau>" 
      unfolding k2_def by auto
    then have kl2: "location (seq k2) = l2" using tau_l2 by auto
    define diff where "diff = k2 - k1" 
    from k2 have k2: "k2 = k1 + diff" "diff > 0" unfolding diff_def by auto
    let ?CG = "call_graph_of_lts R \<restriction> L" 
    have "(location (seq k1), location (seq (k1 + diff))) \<in> ?CG^^diff"
    proof (induct diff)
      case (Suc diff)
      let ?a = "seq (k1 + diff)" let ?b = "seq (Suc (k1 + diff))" 
      have "(location ?a, location ?b) \<in> ?CG" 
      proof -
        from k1 have m: "k1 + diff \<ge> m" by auto
        from steps[OF m] obtain \<tau> where *: "\<tau> \<in> \<tau>s" "(?a, ?b) \<in> ?transition_step \<tau>" by auto
        from *(1) \<tau>s have tau: "\<tau> \<in> transition_rules R" by auto
        have "(location ?a, location ?b) \<in> call_graph_of_lts R" 
          unfolding call_graph_of_lts_def
          by (standard, intro exI, rule conjI[OF _ tau], insert *(2), cases \<tau>, auto)            
        moreover have "location ?a \<in> L" "location ?b \<in> L" using m unfolding L_def by auto
        ultimately show ?thesis by auto
      qed
      with Suc show ?case by auto
    qed auto
    then have "(location (seq k1), location (seq k2)) \<in> ?CG^+" unfolding k2(1)[symmetric] using k2(2)
      using trancl_power by blast
    then have "(l1,l2) \<in> (call_graph_of_lts R \<restriction> L)\<^sup>+" unfolding kl1 kl2 . 
  } 
  then have L_component: "L \<times> L \<subseteq> (call_graph_of_lts R \<restriction> L)\<^sup>+" by auto
  have L_empty: "L \<noteq> {}" unfolding L_def by auto
  note copy = copy[unfolded copy_progs_def]
  from copy have "cut_points (call_graph_of_lts R) CP" by auto
  from this[unfolded cut_points_def, rule_format, OF L_empty L_component] obtain l where
    lCP: "l \<in> CP" and "l \<in> L" by auto  
  from this(2)[unfolded L_def] obtain n where ln: "l = location (seq n)" and nm: "n \<ge> m" by auto
  from copy lCP obtain P where P: "P \<in> Ps" and copy: "copy_prog P R l" by auto
  let ?transition_stepP = "transition_step_lts P" 
  interpret P: indexed_rewriting ?transition_stepP .
  note lift = copy_progD4[OF copy]
  have rec: "recurring \<tau>s (shift seq n)" using recurring_shift[OF rec, of "n - m"] nm
    by auto    
  let ?\<tau>s = "sharp_transition ` \<tau>s"
  let ?seq = "cut_chain n seq"
  from SN[OF P] show False
  proof (elim indexed_rewriting.cooperation_SN_onE)
    show "?seq 0 \<in> initial_states P"  using init copy by auto
    show "P.cooperation_chain (flat_transitions_of P) (sharp_transitions_of P) ?seq"
    proof
      show "P.recurring ?\<tau>s (shift ?seq (Suc n))" (is "P.recurring _ ?s'")
        using sharp_morphism.recurring_morphism[OF rec]
        by(subst shift_cut_chain, auto simp: lift lift_state_conditions_def o_def)
    next
      fix i assume i: "i < Suc n"
      show "(?seq i, ?seq (Suc i)) \<in> \<Union> (transition_step_lts P ` flat_transitions_of P)"
      proof (cases "i = n")
        case True
          obtain \<alpha> where 1: "seq n = State \<alpha> l" using ln by (cases "seq n", auto)
          have 2: "(seq n, seq (Suc n)) \<in> transition R" using chain by auto
          from 2 have "state_lts R (State \<alpha> l)" by (auto simp: 1)
          then have "(flat_state (seq n), sharp_state (seq n)) \<in> transition P"
            unfolding 1 relabel_state.simps
            by (intro cut_transition[OF copy_progD2[OF copy], of "\<alpha>"], auto simp: lift o_def)
          then obtain \<tau>
          where \<tau>: "\<tau> \<in> transition_rules P"
            and step: "(flat_state (seq n), sharp_state (seq n)) \<in> ?transition_stepP \<tau>" by (unfold transition_def, auto)
          then have "source \<tau> = Flat l" unfolding 1 by auto
          with \<tau> step True show ?thesis by (auto intro: exI[of _ \<tau>])
      next
        case False
          with i have i: "i < n" by auto
          from chain obtain \<tau>
          where \<tau>: "\<tau> \<in> transition_rules R" and *: "(seq i, seq (Suc i)) \<in> ?transition_step \<tau>" by (unfold transition_def, auto)
          from \<tau> copy have "flat_transition \<tau> \<in> flat_transitions_of P" by auto
          with \<tau> flat_transition[OF *, unfolded lift] i
          show ?thesis by (auto intro!: exI[of _ "flat_transition \<tau>"] simp:lift_state_conditions_def o_def lift)
      qed
    next
      show "sharp_transition ` \<tau>s \<subseteq> sharp_transitions_of P"
      proof
        fix \<tau>' assume "\<tau>' \<in> sharp_transition ` \<tau>s"
        then obtain \<tau> where "\<tau> \<in> \<tau>s" "\<tau>' = sharp_transition \<tau>" by auto
        with \<tau>s copy_progD(4)[OF copy]
        show "\<tau>' \<in> sharp_transitions_of P" by auto
      qed
    qed
  qed
qed

end


fun make_copy_prog where
   "make_copy_prog (Lts_Impl init \<tau>s lc) cutpoints =
    Lts_Impl (map Flat init)
      (map (\<lambda>(tr,\<tau>). (Flat tr, flat_transition \<tau>)) \<tau>s @ cutpoints @
       map (\<lambda>(tr,\<tau>). (Sharp tr, sharp_transition \<tau>)) \<tau>s)
      (map (\<lambda>(tr,\<tau>). (Flat tr, \<tau>)) lc @ map (\<lambda>(tr,\<tau>). (Sharp tr, \<tau>)) lc) "

type_synonym ('f,'v,'t,'l,'tr)initial_cp_proof =  
  "('tr sharp \<times> ('f, 'v, 't, 'l sharp) transition_rule) list" (* list of skip-transitions for cutpoints *)

context pre_lts_checker
begin

definition "check_exists_cut taus n =
  check (\<exists>\<tau> \<in> set taus.
    source \<tau> = Flat n \<and> target \<tau> = Sharp n \<and> isOK(check_skip_transition \<tau>))
  (showsl_lit (STR ''missing skip transition for '') o showsl n)"
    
definition check_copy_prog where 
  "check_copy_prog Pi Cp = do {
  check_allm (check_exists_cut (map snd (transitions_impl Pi))) Cp
  }"

definition create_initial_cp_prog where
  "create_initial_cp_prog P cp_trans_list = 
    check_return (
    do {
      let cp_trans = concat cp_trans_list;
      let cut_points = remdups (map (\<lambda>(tr,\<tau>). natural (source \<tau>)) cp_trans); 
      check_cut_points (call_graph_impl P) (set cut_points) 
       <+? (\<lambda> s. showsl_lit (STR ''problem in ensuring validity of cutpoints\<newline>'') o s);
      check_allm (\<lambda> (n,cp). check (transition_rule cp) 
        (showsl n o showsl_lit (STR '' is non valid transition rule''))) cp_trans;
      check_allm (check_exists_cut (map snd cp_trans)) cut_points
    }) (map (\<lambda> cp_trans. (make_copy_prog P cp_trans)) cp_trans_list)"

end

declare pre_lts_checker.check_copy_prog_def[code]
declare pre_lts_checker.check_exists_cut_def[code]
declare pre_lts_checker.create_initial_cp_prog_def[code]

context lts_checker begin

lemma transition_rule_flat_transition[simp]: "transition_rule (flat_transition t) = transition_rule t" 
  by (cases t, auto)

lemma transition_rule_sharp_transition[simp]: "transition_rule (sharp_transition t) = transition_rule t" 
  by (cases t, auto)

lemma create_initial_cp_prog:
  assumes ok: "create_initial_cp_prog P cp_trans_list = return CPs"
      and cSN: "\<And> CP. CP \<in> set CPs \<Longrightarrow> cooperation_SN_impl CP"
      and P: "lts_impl P"
  shows "lts_termination (lts_of P)"
proof -
  define all_cp_trans where "all_cp_trans \<equiv> concat cp_trans_list"
  note ok = ok[unfolded create_initial_cp_prog_def Let_def all_cp_trans_def[symmetric], simplified]
  from ok have "\<And> n y. (n, y) \<in> set all_cp_trans \<Longrightarrow> transition_rule y" by auto
  then have cp_trans: "\<And> cp_trans tr \<tau>. cp_trans \<in> set cp_trans_list \<Longrightarrow> (tr, \<tau>) \<in> set cp_trans \<Longrightarrow> transition_rule \<tau>"
    by (auto simp: all_cp_trans_def)
  define CP where "CP = ((\<lambda>(tr, \<tau>). natural (source \<tau>)) ` set all_cp_trans)" 
  from ok have "isOK (check_cut_points (call_graph_impl P) CP)" by (auto simp: CP_def)
  from check_cut_points[OF this] have "cut_points (call_graph_of_lts (lts_of P)) CP" by simp
  show ?thesis
  proof (rule initial_cooperation_program[OF _ _ lts_impl[OF P]]; (unfold copy_progs_def, intro conjI ballI)?)
    show "finite (transition_rules (lts_of P))" by auto
    show "cut_points (call_graph_of_lts (lts_of P)) CP" by fact
    fix l
    assume "l \<in> CP"
    with ok have "isOK(check_exists_cut (map snd all_cp_trans) l)" unfolding CP_def by auto
    from this[unfolded all_cp_trans_def check_exists_cut_def, simplified] 
    obtain cp_trans where mem: "cp_trans \<in> set cp_trans_list" 
      and cut: "exists_cut (lts_of (make_copy_prog P cp_trans)) l" 
      unfolding exists_cut_def by (cases P, auto simp: all_cp_trans_def dest!: check_skip_transition intro!: cp_trans)
    define R where "R = make_copy_prog P cp_trans" 
    note cut = cut[folded R_def]
    have lc: "assertion (lts_of R) = assertion (lts_of P) o natural"
    proof (cases P)
      case (Lts_Impl a b lc)
      note d = map_of_default_def lookup_default_def lookup_of_alist
      let ?lc = "map (\<lambda>(tr, y). (Flat tr, y)) lc @ map (\<lambda>(tr, y). (sharp.Sharp tr, y)) lc" 
      have id: "?thesis = (map_of_default True\<^sub>f ?lc = (\<lambda>x. map_of_default True\<^sub>f lc (natural x)))" (is "_ = (?l = ?r)")
        unfolding Lts_Impl R_def by (simp add: o_def assertion_of_def)
      have id2: "map_of ?lc l = map_of lc (natural l)" for l 
      proof (cases l)
        case (Flat ll)
        have None: "map_of (map (\<lambda>(tr, y). (sharp.Sharp tr, y)) lc) l = None" unfolding Flat map_of_eq_None_iff by auto
        have "map_of ?lc l = map_of (map (\<lambda>(tr, y). (Flat tr, y)) lc) l" 
          unfolding map_of_append 
          by (rule map_add_left_None, rule None)
        also have "\<dots> = map_of lc ll" unfolding Flat by (induct lc, auto)
        finally show ?thesis unfolding Flat by simp
      next
        case (Sharp ll)
        have None: "map_of (map (\<lambda>(tr, y). (sharp.Flat tr, y)) lc) l = None" unfolding Sharp map_of_eq_None_iff by auto
        have "map_of ?lc l = map_of (map (\<lambda>(tr, y). (Sharp tr, y)) lc) l" 
          unfolding map_of_append 
          by (rule map_add_find_left, rule None)
        also have "\<dots> = map_of lc ll" unfolding Sharp by (induct lc, auto)
        finally show ?thesis unfolding Sharp by simp
      qed
      show ?thesis unfolding id d using id2 by (intro ext, auto split: option.splits)
    qed
    from ok have mem: "R \<in> set CPs" using mem unfolding R_def by auto
    have "copy_prog (lts_of R) (lts_of P) l"
      by (intro copy_progI[OF _ cut _ _ lc], unfold R_def, (cases P, auto)+)
    with mem show "\<exists> R \<in> lts_of ` set CPs. copy_prog R (lts_of P) l" by auto
  next
    fix R
    assume "R \<in> lts_of ` set CPs"
    then obtain RR where mem: "RR \<in> set CPs" and R: "R = lts_of RR" by auto
    from ok mem obtain cp_trans where mem': "cp_trans \<in> set cp_trans_list"
      and RR: "RR = make_copy_prog P cp_trans" by auto
    have lts: "lts_impl RR" unfolding RR by (insert P mem' cp_trans, cases P, auto)
    with cSN[OF mem] show "cooperation_SN R" unfolding R by (elim cooperation_SN_implE, auto)
  qed
qed

end

end
