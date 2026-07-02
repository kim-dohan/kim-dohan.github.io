theory Tree_Automata_Containment
  imports 
  Tree_Automata_Wit
begin

lemma list_all2_conv_all_nth': 
  "list_all2 P xs ys =
  (length xs = length ys \<and> (\<forall>i < length ys. P (xs!i) (ys!i)))"   
  unfolding list_all2_conv_all_nth by auto
    
definition next_reach :: "('q, 'f)ta \<Rightarrow> 'q set list \<Rightarrow> 'f \<Rightarrow> 'q set" where
  "next_reach A Qs f = { q | qs q' q. f qs \<rightarrow> q' \<in> ta_rules A \<and> (q',q) \<in> (ta_eps A)\<^sup>* \<and> list_all2 (\<in>) qs Qs}"

definition next_reach_const :: "('q, 'f)ta \<Rightarrow> 'f \<Rightarrow> 'q set" where
  "next_reach_const A f = { q | q' q. f [] \<rightarrow> q' \<in> ta_rules A \<and> (q',q) \<in> (ta_eps A)\<^sup>*}"
  
lemma next_reach_const: "next_reach_const A f = next_reach A [] f" unfolding next_reach_def next_reach_const_def by auto

(* The autoref package tends to get confused about options as data (which should be preserved during
 * refinement) and options for partial functions (which become a lookup table), so we provide a
 * copy of the 'option' type that is only used for data *)
datatype 'a xoption = XNone | XSome (xthe: 'a)

datatype ('f,'q)status = Done "('f,'q)term xoption" | Changed | Unchanged

fun status_result where
  "status_result (Done t) = t"
| "status_result _ = XNone"

fun is_busy :: "('f,'q)status \<Rightarrow> bool" where
  "is_busy (Done _) = False"
| "is_busy _ = True"   

(* We are using pairs of sets of states as keys into a map inside the TA containment procedure.
 * We hide this detail inside a datatype to make the later refinement easier. *)
datatype 'q entry = entry (from_entry : "'q set \<times> 'q set")
abbreviation "efst \<equiv> fst \<circ> from_entry"
abbreviation "esnd \<equiv> snd \<circ> from_entry"
type_synonym ('f,'q) state = "'q entry \<rightharpoonup> ('f,'q)term" 
type_synonym ('f,'q) full_state = "('f,'q) state \<times> ('f,'q) status" 

definition continue_condition :: "('f,'q) full_state \<Rightarrow> bool" where
  "continue_condition Qres = is_busy (snd Qres)" 

context
  fixes A B :: "('q,'f)ta"
begin
  
definition critical :: "'q entry \<Rightarrow> bool" where
  "critical qa_qb = (case qa_qb of entry (qa,qb) \<Rightarrow> qa \<inter> ta_final A \<noteq> {} \<and> qb \<inter> ta_final B = {})" 

definition considered_main :: "'f \<Rightarrow> nat \<Rightarrow> 'q entry list \<Rightarrow> ('f,'q) state \<Rightarrow> bool"  where 
  "considered_main f n qs Q = (next_reach A (map efst qs) f \<noteq> {} \<longrightarrow> 
         entry (next_reach A (map efst qs) f, next_reach B (map esnd qs) f) \<in> dom Q)" 
  
definition considered_aux :: "'f sig \<Rightarrow> ('f,'q) state \<Rightarrow> 'q entry list set \<Rightarrow> ('f,'q) state \<Rightarrow> bool" where
  "considered_aux F Qs No Q = (\<forall> f n qs. (f,n) \<in> F \<longrightarrow> qs \<in> listset (replicate n (dom Qs)) - No \<longrightarrow> 
     considered_main f n qs Q)" 

definition considered :: "'f sig \<Rightarrow> ('f,'q) state \<Rightarrow> ('f,'q) state \<Rightarrow> bool" where
  "considered F Qs Q = considered_aux F Qs {} Q" 
  
  
definition invariant :: "('f,'q) full_state \<Rightarrow> bool" where
  "invariant Qres = (case Qres of (Q,state) \<Rightarrow> (\<forall> qsa qsb t. Q (entry (qsa,qsb)) = Some t \<longrightarrow> 
    (ta_res A t = qsa \<and> ta_res B t = qsb \<and> ground t)) 
  \<and> finite (dom Q)
  \<and> (\<forall> t. state = Done (XSome t) \<longrightarrow> (\<exists> p \<in> dom Q. Q p = Some t \<and> critical p))
  \<and> (state \<in> {Unchanged, Changed, Done XNone} \<longrightarrow> (\<forall> p \<in> dom Q. \<not> critical p))
  \<and> (state = Done XNone \<longrightarrow> (considered (ta_syms A) Q Q)))" 

definition invariant0 :: "'q entry \<Rightarrow> ('f,'q) full_state \<Rightarrow> bool" where
  "invariant0 pp Qres = (case Qres of (Q,state) \<Rightarrow> (\<forall> qsa qsb t. Q (entry (qsa,qsb)) = Some t \<longrightarrow> 
    (ta_res A t = qsa \<and> ta_res B t = qsb \<and> ground t))
  \<and> finite (dom Q)
  \<and> (\<forall> t. state = Done (XSome t) \<longrightarrow> (\<exists> p \<in> dom Q. Q p = Some t \<and> critical p))
  \<and> (state \<in> {Unchanged, Changed, Done XNone} \<longrightarrow> (\<forall> p \<in> dom Q - {pp}. \<not> critical p))
  \<and> (state = Done XNone \<longrightarrow> (considered (ta_syms A) Q Q)))" 
 
lemma invariant0_insert: "res \<in> {Changed, Unchanged} \<Longrightarrow> invariant (Q,res) \<Longrightarrow> ta_res A t = qs \<Longrightarrow> ta_res B t = qs' \<Longrightarrow> ground t \<Longrightarrow>
  invariant0 (entry (qs,qs')) (Q(entry (qs,qs') := Some t), res)" 
  unfolding invariant_def invariant0_def split by auto
    
definition invariant2 :: "('f,'q) state \<Rightarrow> ('f,'q) full_state \<Rightarrow> bool" where
  "invariant2 Qold Qnew \<equiv> invariant Qnew \<and> (case Qnew of (Q,state) \<Rightarrow> 
    (state = Unchanged \<longrightarrow> Q = Qold) \<and> (state = Changed \<longrightarrow> dom Qold \<subset> dom Q))" 
  
fun fst_q :: "('q entry \<times> ('f,'q)term) \<Rightarrow> 'q set" where
  "fst_q (entry (a,b),t) = a" 

fun snd_q :: "('q entry \<times> ('f,'q)term) \<Rightarrow> 'q set" where
  "snd_q (entry (a,b),t) = b" 

fun get_wit :: "('q entry \<times> ('f,'q)term) \<Rightarrow> ('f,'q)term" where
  "get_wit (_,t) = t" 

fun get_entry :: "('q entry \<times> ('f,'q)term) \<Rightarrow> 'q entry" where
  "get_entry (ab,t) = ab" 

definition invariant3 :: "('f,'q) state \<Rightarrow> 'f sig \<Rightarrow> ('f,'q) full_state \<Rightarrow> bool" where
  "invariant3 Qbegin Sig_missing Qnew \<equiv> invariant2 Qbegin Qnew \<and> (continue_condition Qnew \<longrightarrow> 
    considered (ta_syms A - Sig_missing) Qbegin (fst Qnew))" 
  
definition invariant4 :: "'f \<Rightarrow> nat \<Rightarrow> ('f,'q) state \<Rightarrow> ('f,'q) state \<Rightarrow> ('q entry \<times> ('f,'q)term) list set \<Rightarrow> ('f,'q) full_state \<Rightarrow> bool" where
  "invariant4 f n Qbegin Qold Qs Qnew \<equiv> invariant2 Qbegin Qnew \<and> (continue_condition Qnew \<longrightarrow> 
    dom Qold \<subseteq> dom (fst Qnew) \<and> considered_aux {(f,n)} Qbegin (map get_entry ` Qs) (fst Qnew))" 

definition process_function_symbol :: "('f,'q)state \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f,'q)full_state \<Rightarrow> ('f,'q)full_state nres"  where
  "process_function_symbol Q = (\<lambda> (f,n) (Qold, state). let Qolds = listset (replicate n { (pair,t) . Q pair = Some t}) in 
               FOREACHci (invariant4 f n Q Qold) Qolds continue_condition
               (\<lambda> Qs (Q, res). let AQs = map fst_q Qs; AQ = next_reach A AQs f in
                  if AQ = {} then RETURN (Q,res) else 
                    let BQs = map snd_q Qs; BQ = next_reach B BQs f; t = Fun f (map get_wit Qs)
                   in (do {
                      ASSERT (invariant0 (entry (AQ,BQ)) (Q (entry (AQ,BQ) \<mapsto> t), res)); 
                      if entry (AQ,BQ) \<in> dom Q then RETURN (Q,res) 
                      else if critical (entry (AQ,BQ)) then RETURN (Q (entry (AQ,BQ) \<mapsto> t), Done (XSome t)) 
                      else RETURN (Q (entry (AQ,BQ) \<mapsto> t), Changed)})) 
              (Qold, state))"

lemma dom_translate: "{(pair, t). a pair = Some t} = (\<lambda> x. (x,the (a x))) ` dom a" by auto

lemma map_fst_get_entry: "map (efst o get_entry) qs = map fst_q qs"
  by (induct qs) (auto simp: from_entry_def split: entry.split)
lemma map_snd_get_entry: "map (esnd o get_entry) qs = map snd_q qs"
  by (induct qs) (auto simp: from_entry_def split: entry.split)

lemma get_entry: "map get_entry ` listset (replicate n {(pair, t). Q1 pair = Some t}) = listset (replicate n (dom Q1))"
proof -
  have ge: "get_entry = (\<lambda> (a,b). a)" by (intro ext, auto)
  {
    fix x n and Q1 :: "('f,'q)state" 
    assume "\<forall>i<length x. x ! i \<in> dom Q1" "n = length x"
    then have "\<exists>xa. x = map (\<lambda>(a, b). a) xa \<and> length xa = length x \<and> (\<forall>i<length x. xa ! i \<in> (\<lambda>x. (x, the (Q1 x))) ` dom Q1)" 
      by (intro exI[of _ "map (\<lambda> x. (x, the (Q1 x))) x"], auto simp: o_def)
  }
  then show ?thesis
    unfolding dom_translate unfolding listset length_replicate image_Collect ge by auto
qed

lemma process_function_symbol: assumes Qbegin: "invariant (Qbegin,res_begin)" 
  and inv3: "invariant3 Qbegin Sig (Q,res)" "continue_condition (Q, res)"
  shows "process_function_symbol Qbegin (f,n) (Q,res) \<le> SPEC (invariant3 Qbegin (Sig - {(f,n)}))"
proof -
  note d = invariant_def invariant2_def invariant3_def
  note cd = considered_def considered_aux_def considered_main_def    
  show ?thesis 
    unfolding process_function_symbol_def split Let_def
  proof (refine_vcg, goal_cases)
    case 1
    let ?set = "(\<lambda>x. (x, the (Qbegin x))) ` dom Qbegin" 
    from Qbegin[unfolded d] have "finite ?set" by auto
    from finite_list[OF this] obtain qq where Q: "?set = set qq" by auto
    have id: "listset (replicate n ?set) = listset (map set (replicate n qq))" unfolding Q
      map_replicate by simp 
    show "finite (listset (replicate n {(pair, t). Qbegin pair = Some t}))" 
      unfolding dom_translate id concat_lists_listset[symmetric] by (rule finite_set)
  next
    case 2
    show ?case using inv3 by (simp add: invariant4_def invariant3_def cd(1-2) get_entry)
  next
    case (3 qs Qs s3 Q3 res3)
    then have inv: "invariant2 Qbegin (Q3, res3)" unfolding invariant4_def by auto
    from 3 have 4: "invariant4 f n Qbegin Q Qs s3" "continue_condition s3" "s3 = (Q3, res3)"
      "next_reach A (map fst_q qs) f = {}" by auto
    from 4 have cons: "qs \<in> listset (replicate n (dom Qbegin)) \<Longrightarrow> qs \<notin> map get_entry ` Qs \<Longrightarrow> considered_main f n qs Q3" for qs
      by (auto simp: invariant4_def cd)
    {
      fix qst
      assume "qst \<in> listset (replicate n (dom Qbegin))" 
        "qst \<notin> map get_entry ` (Qs - {qs})"
      from cons[OF this(1)] this(2) have qst: "qst \<noteq> map get_entry qs \<Longrightarrow> considered_main f n qst Q3" by auto      
      then have "considered_main f n qst Q3" using 4(4)
        by (cases "qst = map get_entry qs", auto simp: map_fst_get_entry cd)
    } note * = this
    show ?case unfolding invariant4_def
      by (rule conjI[OF inv], insert 4, simp add: invariant4_def cd(1-2) * )
  next
    case (4 qst Qs s3 Q3 res3) 
    with inv3 Qbegin
    have inv: "invariant (Q3,res3)" "invariant (Q,res)"  "invariant (Qbegin,res_begin)" 
      and qst: "qst \<in> listset (replicate n {(pair, t). Qbegin pair = Some t})" 
      unfolding invariant2_def invariant3_def invariant4_def by auto
    from qst[unfolded listset length_replicate] 
    have qst: "length qst = n" "\<And> i. i < n \<Longrightarrow> case qst ! i of (pair, t) \<Rightarrow> Qbegin pair = Some t" by auto
    {
      fix i
      assume i: "i < n" obtain qa qb t where qsi: "qst ! i = (entry (qa,qb),t)"
        by (metis entry.exhaust prod.exhaust)
      from qst(2)[OF i] qsi have "Qbegin (entry (qa,qb)) = Some t" by auto
      with inv(3)[unfolded d split] have t: "ta_res A t = qa \<and> ta_res B t = qb \<and> ground t" by auto
      have qa: "qa = map fst_q qst ! i" using qsi i qst(1) by auto
      have qb: "qb = map snd_q qst ! i" using qsi i qst(1) by auto
      have tt: "t = map get_wit qst ! i" using qsi i qst(1) by auto
      from t i qst(1) have 
        "map (ta_res A) (map get_wit qst) ! i = map fst_q qst ! i" 
        "map (ta_res B) (map get_wit qst) ! i = map snd_q qst ! i" 
        "ground (map get_wit qst ! i)" unfolding qa qb tt by auto
    } note ti = this
    let ?tt = "Fun f (map (\<lambda> i. map get_wit qst ! i) [0 ..< n])" 
    let ?t = "Fun f (map get_wit qst)" 
    from qst(1) have tt: "?t = ?tt" by (auto intro: nth_equalityI)
    have grd: "ground ?t" using ti(3) unfolding tt by auto      
    show ?case
    proof (rule invariant0_insert[OF _ inv(1) _ _ grd])
      show "ta_res A ?t = next_reach A (map fst_q qst) f" 
        unfolding ta_res.simps next_reach_def list_all2_conv_all_nth length_map length_upt qst(1)
          using ti(1)  by auto
      show "ta_res B ?t = next_reach B (map snd_q qst) f" 
        unfolding ta_res.simps next_reach_def list_all2_conv_all_nth length_map length_upt qst(1)
        using ti by auto
      from 4 have "continue_condition (Q3, res3)"  by auto
      then show "res3 \<in> {Changed, Unchanged}" unfolding continue_condition_def by (cases res3, auto)
    qed
  next
    case (5 qs Qs s3 Q3 res3)
    then have inv2: "invariant2 Qbegin (Q3, res3)" unfolding invariant4_def by auto
    from 5 have dom: "dom Q \<subseteq> dom Q3" by (auto simp: invariant4_def)
    from 5 have inv4: "considered_aux {(f, n)} Qbegin (map get_entry ` Qs) Q3"
      and qs: "entry (next_reach A (map fst_q qs) f, next_reach B (map snd_q qs) f) \<in> dom Q3" 
      by (auto simp: invariant4_def)
    {
      fix qst
      assume "qst \<in> listset (replicate n (dom Qbegin))" 
        "qst \<notin> map get_entry ` (Qs - {qs})"
      from inv4[unfolded cd(1-2)] this 
      have qst: "qst \<noteq> map get_entry qs \<Longrightarrow> considered_main f n qst Q3" by auto
      then have "considered_main f n qst Q3" using qs
        by (cases "qst = map get_entry qs", auto simp: map_fst_get_entry map_snd_get_entry cd)
    } note * = this
    show ?case unfolding invariant4_def fst_conv
      by (rule conjI[OF inv2], intro conjI impI, rule dom, insert *, auto simp: cd(1-2))
  next
    case (6 qs Qs s3 Q3 res3)
    then have "res3 \<in> {Changed, Unchanged}" unfolding continue_condition_def by (cases res3, auto)
    with 6
    have inv: "invariant2 Qbegin
     (Q3 (entry (next_reach A (map fst_q qs) f, next_reach B (map snd_q qs) f) \<mapsto> Fun f (map get_wit qs)), Done (XSome (Fun f (map get_wit qs))))" 
      unfolding d split invariant4_def invariant0_def by force
    then show ?case unfolding invariant4_def 
      by (auto simp: continue_condition_def)
  next 
    case (7 qs Qs s3 Q3 res3)
    let ?Q = "Q3 (entry (next_reach A (map fst_q qs) f, next_reach B (map snd_q qs) f) \<mapsto> Fun f (map get_wit qs))" 
    from 7 have inv: "invariant (?Q, Changed)" 
      unfolding d invariant0_def continue_condition_def by (cases res3, auto)
    from 7 have inv4: "invariant4 f n Qbegin Q Qs (Q3,res3)" "continue_condition (Q3,res3)" 
      and "invariant2 Qbegin (Q3,res3)"  
      "entry (next_reach A (map fst_q qs) f, next_reach B (map snd_q qs) f) \<notin> dom Q3" 
      "continue_condition (Q3,res3)" unfolding invariant4_def by auto
    with inv have inv2: "invariant2 Qbegin (?Q, Changed)" 
      unfolding invariant2_def split continue_condition_def by (cases res3, auto)
    have dom: "dom Q \<subseteq> dom ?Q" and cons: "considered_aux {(f, n)} Qbegin (map get_entry ` Qs) Q3" 
      using inv4[unfolded invariant4_def] by auto
    from cons have cons: "considered_aux {(f,n)} Qbegin (map get_entry ` Qs) ?Q" 
      unfolding cd by auto
    show ?case unfolding invariant4_def fst_conv
    proof (rule conjI[OF inv2], intro conjI impI, rule dom)
      {
        fix qst
        assume "qst \<in> listset (replicate n (dom Qbegin))" 
          "qst \<notin> map get_entry ` (Qs - {qs})"
        with cons[unfolded cd(1-2)] this 
        have qst: "qst \<noteq> map get_entry qs \<Longrightarrow> considered_main f n qst ?Q" by auto
        then have "considered_main f n qst ?Q" 
          by (cases "qst = map get_entry qs", auto simp: map_fst_get_entry map_snd_get_entry cd)
      } note * = this
      then show "considered_aux {(f,n)} Qbegin (map get_entry ` (Qs - {qs})) ?Q" unfolding cd(1-2) by blast
    qed
  next
    case (8 s3)
    then have inv: "invariant2 Qbegin s3" unfolding invariant4_def invariant3_def by auto
    show ?case unfolding invariant3_def cd(1-2)
    proof (rule conjI[OF inv], intro impI allI)
      fix g m qs
      assume "(g,m) \<in> ta_syms A - (Sig - {(f,n)})" and qs: "qs \<in> listset (replicate m (dom Qbegin)) - {}" 
      then have "(g,m) \<in> ta_syms A - Sig \<or> (g,m) = (f,n)" by auto
      then show "considered_main g m qs (fst s3)" 
      proof
        assume "(g,m) \<in> ta_syms A - Sig" 
        moreover note inv3
        moreover from 8[unfolded invariant4_def] have "dom Q \<subseteq> dom (fst s3)" by auto
        ultimately show ?thesis unfolding invariant3_def using qs by (force simp: cd)
      next
        assume "(g,m) = (f,n)" 
        then have "g = f" "m = n" by auto
        moreover from 8 have "invariant4 f n Qbegin Q {} s3" "continue_condition s3" by auto
        ultimately show ?thesis unfolding invariant4_def using qs by (auto simp: cd)
      qed
    qed
  next
    case 9
    then show ?case unfolding invariant4_def invariant3_def by simp
  qed
qed

  
definition process_function_symbols :: "('f,'q) state \<Rightarrow> 'f sig \<Rightarrow> ('f,'q)full_state \<Rightarrow> ('f,'q)full_state nres" where
  "process_function_symbols Q SigD = FOREACHc SigD continue_condition (process_function_symbol Q)" 

lemma process_function_symbols: assumes Qbegin: "invariant (Qbegin,res_begin)" 
  and inv3: "invariant3 Qbegin (Sig \<union> SigD) s" 
  and fin: "finite SigD" 
shows "process_function_symbols Qbegin SigD s \<le> SPEC (invariant3 Qbegin Sig)"
  unfolding process_function_symbols_def
proof (refine_vcg FOREACHc_rule[where I ="(\<lambda> S. invariant3 Qbegin (Sig \<union> S))"], goal_cases)
  case (3 fn S s3)
  obtain Q3 res3 where s3: "s3 = (Q3,res3)" by force
  from process_function_symbol[OF Qbegin 3(3-)[unfolded s3], of "fst fn" "snd fn"] 
  have "process_function_symbol Qbegin fn s3 \<le> SPEC (invariant3 Qbegin (Sig \<union> S - {fn}))"
    unfolding s3 by auto
  also have "\<dots> \<le> SPEC (invariant3 Qbegin (Sig \<union> (S - {fn})))" unfolding invariant3_def considered_def considered_aux_def
    by auto
  finally show ?case .
qed (insert fin inv3, auto simp: invariant3_def)
  
definition check_abort :: "('f,'q)full_state \<Rightarrow> ('f,'q)full_state" where
  "check_abort s = (case s of (Qnew, Unchanged) \<Rightarrow> (Qnew, Done XNone)
     | _ \<Rightarrow> s)"  
      
definition ta_lang_containment :: "('f,'v)term xoption nres" where
  "ta_lang_containment = (do {
      let Qinit = Map.empty;
      let Afin = ta_final A;
      let Bfin = ta_final B;
      let Sig = ta_syms A;
      res \<leftarrow> WHILEIT invariant continue_condition (\<lambda> (Q,_). do {
         S \<leftarrow> process_function_symbols Q Sig (Q,Unchanged);
         RETURN (check_abort S)
         })
        (Qinit, Changed);
      RETURN (map_xoption adapt_vars (status_result (snd res)))
    })" 
      
lemma ta_lang_containment: assumes fin: "ta_finite A" "ta_finite B" 
  shows "ta_lang_containment \<le> SPEC (\<lambda> wit_opt. case wit_opt of XNone \<Rightarrow> (ta_lang A :: ('f,'v)term set) \<subseteq> ta_lang B
    | XSome t \<Rightarrow> t \<in> (ta_lang A :: ('f,'v)term set) - ta_lang B)"
proof -
  note d = invariant_def invariant2_def
  note cd = considered_def considered_aux_def considered_main_def
  obtain Dom where dom: "dom = (Dom :: ('f,'q) state \<Rightarrow> 'q entry set)" by auto
  let ?QA = "ta_states A"
  let ?QB = "ta_states B"
  let ?Pow = "entry ` (Pow ?QA \<times> Pow ?QB)"
  have "finite ?QA" by (rule finite_states[OF fin(1)])
  then have "finite (Pow ?QA)" by simp
  moreover have "finite ?QB" by (rule finite_states[OF fin(2)])
  then have "finite (Pow ?QB)" by simp
  ultimately have finPow: "finite ?Pow" by simp
  let ?m1 = "\<lambda> (Q,s). if is_busy s then 1 else 0" 
  let ?m2 = "\<lambda> (Q,s). card (?Pow - dom Q)" 
  let ?m = "measures [?m1,?m2]"
  show ?thesis unfolding ta_lang_containment_def Let_def
  proof (refine_vcg WHILEIT_rule[where R = "?m"], goal_cases)
    case 1
    show "wf ?m" by simp
  next 
    case 2
    show "invariant (Map.empty, Changed)" unfolding d by auto
  next
    case (3 s Q res) 
    then have inv: "invariant (Q,res)" "continue_condition (Q,res)" and s: "s = (Q,res)" by auto
    then have "invariant2 Q (Q, Unchanged)" unfolding invariant2_def split 
      by (cases res, auto simp: d continue_condition_def)
    then have inv3: "invariant3 Q ({} \<union> ta_syms A) (Q, Unchanged)" 
      unfolding invariant3_def cd invariant2_def by auto
    have "finite (ta_syms A)" using fin(1) unfolding ta_syms_def by (simp add: ta_finiteD(1))
    from process_function_symbols[OF inv(1) inv3 this]
    have "process_function_symbols Q (ta_syms A) (Q, Unchanged) \<le> SPEC (invariant3 Q {})" .
    also have "\<dots> \<le> SPEC (\<lambda>S. RETURN (check_abort S)
                 \<le> SPEC (\<lambda>s'. invariant s' \<and> (s', s) \<in> ?m))" 
    proof -
      {
        fix Qnew :: "('f,'q)state" and res1 :: "('f,'q) status"
        assume inv3: "invariant3 Q {} (Qnew, res1)" 
        have busy: "is_busy res" using inv unfolding continue_condition_def by auto
        have "RETURN (check_abort (Qnew, res1)) \<le> SPEC (\<lambda>s'. invariant s' \<and> (s', s) \<in> ?m)" (is "?l \<le> ?r")
        proof (cases "res1 = Unchanged")
          case True
          then have inv: "invariant (Qnew, Done XNone)" using inv3 unfolding d invariant3_def invariant2_def continue_condition_def 
            by auto
          with True show ?thesis using busy by (simp add: s check_abort_def)
        next
          case False
          then have l: "?l = RETURN (Qnew,res1)" by (cases res1, auto simp: check_abort_def)          
          have inv: "invariant (Qnew,res1)" using inv3 unfolding invariant3_def invariant2_def by auto
          moreover have "((Qnew,res1), (Q,res)) \<in> ?m"
          proof (cases "is_busy res1")
            case False
            with busy show ?thesis by auto
          next
            case True
            with False have res1: "res1 = Changed" by (cases res1, auto)
            from inv3[unfolded invariant2_def invariant3_def split] res1 
            have sub: "dom Q \<subset> dom Qnew" by auto
            from finPow have fin: "finite (?Pow - dom Q)" by auto 
            have "card (?Pow - dom Qnew) < card (?Pow - dom Q)"
            proof (rule psubset_card_mono[OF fin])
              have "dom Qnew \<subseteq> ?Pow"
              proof
                fix e assume a: "e \<in> dom Qnew"
                then obtain qa qb where e: "e = entry (qa, qb)" by (cases e) auto
                with a inv[unfolded d split] obtain t where 
                  res: "ta_res A t = qa" "ta_res B t = qb" and t: "ground t" by auto
                from ta_res_states[OF t] res 
                show "e \<in> ?Pow" by (auto simp: e)
              qed
              then show "?Pow - dom Qnew \<subset> ?Pow - dom Q" using sub unfolding dom by auto
            qed
            then show ?thesis using busy by auto
          qed
          ultimately show ?thesis unfolding l s by auto
        qed
      }
      then show ?thesis by auto
    qed
    finally show ?case .
  next
    case (4 s)
    let ?A = "ta_lang A :: ('f,'v)term set" 
    obtain Q res where s: "s = (Q,res)" by force
    with 4(2)[unfolded continue_condition_def] have "\<not> is_busy res" by auto
    then obtain answer where res: "res = Done answer" by (cases res, auto)
    have "case answer of XNone \<Rightarrow> ?A \<subseteq> ta_lang B | XSome t \<Rightarrow> adapt_vars t \<in> ?A - ta_lang B"
    proof (cases answer)
      case (XSome t)
      with 4(1)[unfolded s res d split critical_def] have 
        *: "ground t" "ta_final A \<inter> ta_res A t \<noteq> {}" "ta_final B \<inter> ta_res B t = {}"
        by (auto split: entry.split_sel_asm prod.split_asm) (auto simp: from_entry_def split: entry.split_asm)
      let ?t = "adapt_vars t :: ('f,'v)term" 
      from *(1,2) have "?t \<in> ta_lang A" unfolding ta_lang_def by blast
      moreover have "?t \<notin> ta_lang B"
      proof
        assume "?t \<in> ta_lang B" 
        from ta_langE[OF this] obtain t' q where 
          **: "ground t'" "?t = adapt_vars t'" "q \<in> ta_res B t'" "q \<in> ta_final B" 
          by blast
        from this(1-2) *(1) have "t = t'"  by (metis adapt_vars_adapt_vars)
        with **(3-4) * show False by auto
      qed
      ultimately show ?thesis unfolding XSome by auto
    next
      case XNone
      with 4[unfolded s res] have "invariant (Q, Done XNone)" by auto
      from this[unfolded d split]
      have non_crit: "(\<forall>p\<in> dom Q. \<not> critical p)" 
        and closed: "\<And> f n qs. (f, n) \<in> ta_syms A \<Longrightarrow>
         qs \<in> listset (replicate n (dom Q)) \<Longrightarrow> considered_main f n qs Q" by (auto simp: cd(1-2))
      {
        fix t
        assume "ground t" "ta_res A t \<noteq> {}" 
        then have "entry (ta_res A t, ta_res B t) \<in> dom Q" 
        proof (induct t)
          case (Fun f ts)
          let ?n = "length ts" 
          from Fun(3)[unfolded ta_res.simps] have non_empty: "\<And> t. t \<in> set ts \<Longrightarrow> ta_res A t \<noteq> {}" 
            unfolding set_conv_nth by auto
          with Fun(1-2) have "\<And> t. t \<in> set ts \<Longrightarrow> entry (ta_res A t, ta_res B t) \<in> dom Q" by auto
          then have IH: "\<And> i. i < ?n \<Longrightarrow> entry (ta_res A (ts ! i), ta_res B (ts ! i)) \<in> dom Q" unfolding set_conv_nth by auto
          from Fun(3) have f: "(f,?n) \<in> ta_syms A" by (force simp: ta_syms_def)
          note closed = closed[OF this]
          have ta_res: "ta_res A (Fun f ts) = next_reach A (map (ta_res A) ts) f" 
            for ts and A :: "('q,'f)ta"
            unfolding ta_res.simps next_reach_def list_all2_conv_all_nth' length_map by blast
          let ?list = "map (\<lambda>i. entry (ta_res A (ts ! i), ta_res B (ts ! i))) [0..< ?n]" 
          have A: "map (ta_res A) ts = map efst ?list" 
            by (auto simp: o_def map_upt_len_same_len_conv) 
          have B: "map (ta_res B) ts = map esnd ?list" 
            by (auto simp: o_def map_upt_len_same_len_conv) 
          show ?case unfolding ta_res A B
          proof (rule closed[unfolded cd, rule_format])
            show "next_reach A (map efst ?list) f \<noteq> {}" 
              unfolding A[symmetric] ta_res[symmetric] using Fun(3) .
            show "?list \<in> listset (replicate ?n (dom Q))" unfolding listset length_replicate
              using IH by auto
          qed
        qed auto
      } note closure = this
      have "?A \<subseteq> ta_lang B"
      proof
        fix t
        assume "t \<in> ?A" 
        from ta_langE[OF this] obtain s q where s: "ground s" 
          and q: "q \<in> ta_final A" "q \<in> ta_res A s" and ts: "t = adapt_vars s" .
        from closure[OF s] q have "entry (ta_res A s, ta_res B s) \<in> dom Q" by auto
        with non_crit q have "ta_res B s \<inter> ta_final B \<noteq> {}" unfolding critical_def
          apply auto
          by (metis (mono_tags, lifting) IntI \<open>entry (ta_res A s, ta_res B s) \<in> dom Q\<close> case_prodI empty_iff entry.case)
        with s ts
        show "t \<in> ta_lang B" unfolding ta_lang_def by auto
      qed
      then show ?thesis unfolding XNone by auto
    qed
    then show ?case unfolding s res snd_conv status_result.simps by (cases answer, auto)
  qed
qed

definition ta_lang_containment_unrolled :: "('f,'v)term xoption nres" where
  "ta_lang_containment_unrolled = (do {
      let Qinit = Map.empty;
      let Afin = ta_final A;
      let Bfin = ta_final B;
      let Sig = ta_syms A;
      S \<leftarrow> process_function_symbols Qinit Sig (Qinit,Unchanged);
      let S2 = check_abort S;
      res \<leftarrow> WHILEIT invariant continue_condition ((\<lambda> (Q,_). do {
         S \<leftarrow> process_function_symbols Q Sig (Q,Unchanged);
         RETURN (check_abort S)
         }))
        S2;
      RETURN (map_xoption adapt_vars (status_result (snd res)))
    })" 
  
lemma ta_lang_containment_unrolled: "ta_lang_containment_unrolled \<le> \<Down> Id ta_lang_containment" 
proof -
  let ?S = "(Map.empty, Changed)" 
  have inv: "(invariant ?S) = True" "continue_condition ?S = True" 
    unfolding invariant_def continue_condition_def by auto
  show ?thesis
  unfolding ta_lang_containment_unrolled_def ta_lang_containment_def Let_def
    WHILEIT_unfold[of invariant continue_condition _ "(Map.empty, Changed)", unfolded inv if_True]
    split nres_monad3 imonad1 
    by (intro bind_refine[where R = Id and R' = Id] WHILET_refine, auto)
qed
  
lemma RES_singleton_bind: "(RES {a} \<bind> (\<lambda> xs. f xs)) = f a"
  by (simp add: RES_sng_eq_RETURN)
    
lemma FOREACHc_singleton: "FOREACHc {a} c f s = (
      if c s then f a s else RETURN s)"
proof -
  have id: "(\<lambda>xs. distinct xs \<and> {a} = set xs \<and> sorted_wrt (\<lambda>_ _. True) xs)
    = (\<lambda> xs. xs = [a])" 
  proof (intro ext, goal_cases)
    case (1 xs)
    then show ?case by (cases xs, auto)
  qed
  have body: "FOREACH_body f ([a], s) = f a s \<bind> (\<lambda>\<sigma>'. RETURN ([], \<sigma>'))"
    by (simp add: FOREACH_body_def)
  show ?thesis unfolding FOREACHc_def FOREACHci_def FOREACHoci_def id 
    by (simp add: RES_singleton_bind WHILEIT_unfold[of _ _ _ "([a], s)"] FOREACH_cond_def body, 
      intro impI Refine_Basic.bind_cong, auto simp: WHILEIT_unfold)
qed

definition process_function_symbol_no_inv :: "('f,'q)state \<Rightarrow> 'f \<times> nat \<Rightarrow> ('f,'q)full_state \<Rightarrow> ('f,'q)full_state nres"  where
  "process_function_symbol_no_inv Q = (\<lambda> (f,n) (Qold, state). let Qolds = listset (replicate n { (pair,t) . Q pair = Some t}) in 
               FOREACHc Qolds continue_condition
               (\<lambda> Qs (Q, res). let AQs = map fst_q Qs; AQ = next_reach A AQs f in
                  if AQ = {} then RETURN (Q,res) else 
                    let BQs = map snd_q Qs; BQ = next_reach B BQs f; t = Fun f (map get_wit Qs)
                   in (do {
                      if entry (AQ,BQ) \<in> dom Q then RETURN (Q,res) 
                      else if critical (entry (AQ,BQ)) then RETURN (Q (entry (AQ,BQ) \<mapsto> t), Done (XSome t)) 
                      else RETURN (Q (entry (AQ,BQ) \<mapsto> t), Changed)})) 
              (Qold, state))"
  
lemma process_function_symbol_no_inv: "process_function_symbol_no_inv Q fn s \<le> \<Down> Id (process_function_symbol Q fn s)" 
proof -
  obtain f n where fn: "fn = (f,n)" by force
  obtain QQ res where s: "s = (QQ,res)" by force
  show ?thesis unfolding process_function_symbol_no_inv_def process_function_symbol_def fn split s Let_def
    by (refine_vcg FOREACHci_refine_rcg'[of "\<lambda> x. x"], auto)
qed 
  
definition process_constant :: "'f \<Rightarrow> ('f,'q)full_state \<Rightarrow> ('f,'q)full_state nres" where
  "process_constant f = (\<lambda> (Q, res). let AQ = next_reach_const A f in
                  if AQ = {} then RETURN (Q,res) else 
                    let BQ = next_reach_const B f; t = (Fun f [] :: ('f,'q)term)
                   in (do {
                      if entry (AQ,BQ) \<in> dom Q then RETURN (Q,res) 
                      else if critical (entry (AQ,BQ)) then RETURN (Q (entry (AQ,BQ) \<mapsto> t), Done (XSome t)) 
                      else RETURN (Q (entry (AQ,BQ) \<mapsto> t), Changed)}))"
  
definition process_constants :: "'f sig \<Rightarrow> ('f,'q)full_state \<Rightarrow> ('f,'q)full_state nres" where
  "process_constants SigD = FOREACHc SigD continue_condition 
    (\<lambda>(f, n). if n = 0 then \<lambda>(Qold, state). if is_busy state then process_constant f (Qold, state) else RETURN (Qold, state)
               else RETURN)" 

lemma process_constants: 
  shows "process_constants Sig s \<le> \<Down> Id (process_function_symbols Map.empty Sig s)"  
proof -  
  define body where "body = (\<lambda> f Qs (Q, res). let AQs = map fst_q Qs; AQ = next_reach A AQs f in
                  if AQ = {} then RETURN (Q,res) else 
                    let BQs = map snd_q Qs; BQ = next_reach B BQs f; t = Fun f (map get_wit Qs)
                   in (do {
                      if entry (AQ,BQ) \<in> dom Q then RETURN (Q,res) 
                      else if critical (entry (AQ,BQ)) then RETURN (Q (entry (AQ,BQ) \<mapsto> t), Done (XSome t)) 
                      else RETURN (Q (entry (AQ,BQ) \<mapsto> t), Changed)}))"
  { 
    fix f n
    have id: "listset (replicate n {}) = (if n = 0 then {[]} else {})" for n by (cases "n = 0", auto simp: listset)
    have "process_function_symbol_no_inv Map.empty (f,n) = (\<lambda> (Qold, state). let Qolds = (if n = 0 then {[]} else {}) in 
               FOREACHc Qolds continue_condition
                (body f)
         (Qold, state))" unfolding body_def process_function_symbol_no_inv_def Let_def by (simp add: id)
    also have "\<dots> = (if n = 0 then (\<lambda> (Qold, state). FOREACHc {[]} continue_condition
                (body f)
         (Qold, state)) else (\<lambda> (Qold, state). FOREACHc {} continue_condition
                (body f)
         (Qold, state)))" unfolding Let_def by auto
    also have "\<dots> = (if n = 0 then \<lambda>(Qold, state). FOREACHc {[]} continue_condition (body f) (Qold, state)
      else RETURN)" 
      unfolding FOREACHc_emp by auto
    also have "\<dots> = (if n = 0 then \<lambda>(Qold, state). 
     if continue_condition (Qold, state) then body f [] (Qold, state) else RETURN (Qold, state)
     else RETURN)" unfolding FOREACHc_singleton by auto
    also have "\<dots> = (if n = 0 then \<lambda>(Qold, state). 
     if is_busy state then process_constant f (Qold, state) else RETURN (Qold, state)
     else RETURN)" unfolding body_def process_constant_def Let_def continue_condition_def next_reach_const by auto
    finally have "process_function_symbol_no_inv Map.empty (f, n) =
      (if n = 0 then \<lambda>(Qold, state). if is_busy state then process_constant f (Qold, state) else RETURN (Qold, state) else RETURN)" .
  }
  then have fun_sym: "process_function_symbol_no_inv Map.empty = (\<lambda> (f, n).
    (if n = 0 then \<lambda>(Qold, state). if is_busy state then process_constant f (Qold, state) else RETURN (Qold, state) else RETURN))" 
    by auto
  have "process_constants Sig s = FOREACH\<^sub>C Sig continue_condition (process_function_symbol_no_inv Map.empty) s"
    unfolding process_constants_def fun_sym by auto
  also have "\<dots> \<le> \<Down> Id (process_function_symbols Map.empty Sig s)" 
    unfolding process_function_symbols_def
    by (refine_vcg FOREACHc_refine_rcg[of "\<lambda> x. x"], insert process_function_symbol_no_inv[of "Map.empty :: ('f,'q)state"], auto)
  finally show ?thesis .
qed

definition ta_lang_containment_constants :: "('f,'v)term xoption nres" where
  "ta_lang_containment_constants = (do {
      let Qinit = Map.empty;
      let Afin = ta_final A;
      let Bfin = ta_final B;
      let Sig = ta_syms A;
      S \<leftarrow> process_constants Sig (Qinit,Unchanged);
      let S2 = check_abort S;
      res \<leftarrow> WHILEIT invariant continue_condition ((\<lambda> (Q,_). do {
         S \<leftarrow> process_function_symbols Q Sig (Q,Unchanged);
         RETURN (check_abort S)
         }))
        S2;
      RETURN (map_xoption adapt_vars (status_result (snd res)))
    })" 

lemma ta_lang_containment_constants: "ta_lang_containment_constants \<le> \<Down> Id ta_lang_containment_unrolled" 
  unfolding ta_lang_containment_constants_def ta_lang_containment_unrolled_def Let_def
  by (intro bind_refine[where R = Id and R' = Id] process_constants, auto)
    
 
end
    
hide_const (open) invariant invariant0 invariant2 invariant3 invariant4

end
