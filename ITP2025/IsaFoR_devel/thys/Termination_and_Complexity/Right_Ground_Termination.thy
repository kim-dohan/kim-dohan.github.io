(* Authors: 
   Ismael Kira
   René Thiemann
*)

theory Right_Ground_Termination
  imports
    TRS.Q_Restricted_Rewriting
    Not_SN.Nontermination (* for loop-implies-nontermination *)
    Auxx.Multiset2
    "Decreasing-Diagrams-II.Decreasing_Diagrams_II"
begin


fun right_ground :: "('f,'v) rule \<Rightarrow> bool" where
  "right_ground (l,r) = ground r"

definition right_ground_TRS :: "('f, 'v) trs \<Rightarrow> bool" where 
  "right_ground_TRS x = Ball x (right_ground)"

lemma rg_SN_on_rhss_imp_SN:
  assumes "SN_on (qrstep nfs Q R) (rhss R)"
    and rg: "right_ground_TRS R" 
  shows "SN_on (qrstep nfs Q R) UNIV"
proof (rule ccontr)
  let ?R = "qrstep nfs Q R" 
  assume "\<not> SN ?R"
  from this have "\<not>SN_on ?R UNIV" by blast  
  from this have *: "\<exists>f. f 0 \<in> UNIV \<and> chain ?R f" by (simp add: SN_on_def)
  {
    from not_SN_imp_Tinf[OF \<open>\<not> SN ?R\<close>] obtain t where "t \<in> Tinf ?R" by auto
    from Tinf_imp_SN_nr_first_root_step[of t, OF this]
    obtain s u where "(s,u) \<in> rqrstep nfs Q R" and nSN: "\<not> SN_on ?R {u}" by auto
    then obtain l r \<sigma> where lr: "(l,r) \<in> R" and u: "u = r \<cdot> \<sigma>" by (metis rqrstepE)
    from lr rg have "ground r" by (auto simp: right_ground_TRS_def)
    hence "u = r" unfolding u by (metis ground_subst_apply)
    with nSN have "\<not> SN_on ?R {r}" by auto
    moreover have "r \<in> rhss R" using lr by auto
    ultimately show False using assms(1) unfolding SN_defs by auto
  }
qed

lemma termination_implies_cycle: "finite R \<Longrightarrow> \<not> SN (qrstep nfs Q R) \<Longrightarrow> right_ground_TRS R \<Longrightarrow> \<exists> l r C. (l,r) \<in> R \<and> ((r, C \<langle> r \<rangle>) \<in> (qrstep nfs Q R)^+)"
proof (induct "card R" arbitrary: R)
  case (Suc n R)
  let ?QR = "qrstep nfs Q R" 
  from rg_SN_on_rhss_imp_SN[OF _ \<open>right_ground_TRS R\<close>] \<open>\<not> SN ?QR\<close> 
  have "\<not> SN_on ?QR (rhss R)" by auto
  then obtain l r where "\<not> SN_on ?QR {r}" and lr: "(l,r) \<in> R" 
    unfolding SN_on_def by force
  then obtain f where chain: "chain ?QR f" and start: "f 0 = r" by auto
  let ?RR = "R - {(l,r)}" 
  let ?QRR = "qrstep nfs Q ?RR" 
  have "n = card ?RR" "finite ?RR" "right_ground_TRS ?RR" using Suc(2,3,5) lr 
    by (auto simp: right_ground_TRS_def)
  note IH = Suc(1)[OF this(1-2) _ this(3)] (* only \<not> SN ?QRR is missing *)
    (* consider the two cases that the sub-trs ?RR is terminating or not *)
  show ?case
  proof (cases "SN ?QRR")
    case False

    from IH[OF this] obtain la ra Ca where "(la,ra) \<in> ?RR \<and> (ra,Ca\<langle>ra\<rangle>) \<in> ?QRR^+"
      by blast
    hence "(la,ra) \<in> R \<and> (ra,Ca\<langle>ra\<rangle>) \<in> ?QR^+" using trancl_mono_mp[OF qrstep_mono[of ?RR R Q Q nfs]]
      by blast
    thus ?thesis by auto
  next
    case True
    hence "\<not> chain ?QRR f" by auto
    with chain obtain i where "(f i, f (Suc i)) \<in> ?QR - ?QRR" by auto
        (* hence the applied rule must be (l,r) *)
        (* and from this with the initial f 0 = r you get the desired rule *)
    hence "(f i, f (Suc i)) \<in> qrstep nfs Q {(l,r)}" by force
    from this obtain C \<sigma> where "f (Suc i) = C\<langle>r \<cdot> \<sigma>\<rangle>" by auto
    have "ground r" using Suc.prems(3) lr right_ground.simps right_ground_TRS_def by blast
    hence "r \<cdot> \<sigma> = r" by (simp add: ground_subst_apply)
    hence "(r, C\<langle>r\<rangle>) \<in> ?QR^+"
      by (metis \<open>f (Suc i) = C\<langle>r \<cdot> \<sigma>\<rangle>\<close> chain chain_imp_trancl start zero_less_Suc)
    thus ?thesis using lr by blast
  qed
qed auto


fun is_subterm :: "('f,'v) rule \<Rightarrow> bool" where
  "is_subterm (s,t) = s \<unlhd> t"

context
  fixes rewr :: "('f,'v)term \<Rightarrow> ('f,'v)term list" 
begin

fun rg_init :: "('f,'v) rules \<Rightarrow> ('f,'v) rules" where
  "rg_init R = remdups [ (r, s). (l,r) \<leftarrow> R, s \<leftarrow> rewr r] "

fun advance_sequence :: "('f,'v) rules \<Rightarrow> ('f,'v) rules" where
  "advance_sequence xs = remdups [(r,s). (r,t) \<leftarrow> xs, s \<leftarrow> rewr t]"


text \<open>Use partial function, then termination does not need to be proven
  at this point.\<close>

partial_function (tailrec) right_ground_termination_step ::
  "('f, 'v) rules \<Rightarrow> bool" where
  "right_ground_termination_step S = 
  (if S = []
  then True
  else
    (if (find is_subterm S) = None
    then right_ground_termination_step (advance_sequence S)
    else False
    ) 
  )"

definition right_ground_termination :: "('f, 'v) rules \<Rightarrow> bool" where
  "right_ground_termination R = right_ground_termination_step (rg_init R)" 

lemma rgts_code[code]: "right_ground_termination_step S = 
  (case S of Nil \<Rightarrow> True
    | _ \<Rightarrow> (case find is_subterm S of 
              None \<Rightarrow> right_ground_termination_step ( advance_sequence S)
            | _ \<Rightarrow> False))" 
  unfolding right_ground_termination_step.simps[of S]
  by (cases S, auto)

context 
  fixes nfs :: bool and Q :: "('f,'v)terms" and R :: "('f,'v)rules" 
  assumes rg: "right_ground_TRS (set R)"
  and rewr[simp]: "set (rewr s) = {t. (s,t) \<in> qrstep nfs Q (set R)}"  
begin

lemma advance_sequence: "set (advance_sequence xs) = { (s,u) | s t u. (s,t) \<in> set xs \<and> (t,u) \<in> qrstep nfs Q (set R)}"
  by auto

lemma advance_sequence_init: "set ((advance_sequence^^n)(rg_init R))
  = { (r,t) | l r t . (l,r) \<in> set R \<and> (r,t) \<in> (qrstep nfs Q (set R))^^(Suc n)}" 
proof (induction n)
  case (Suc n)
  note advance_sequence.simps[simp del] 
  note rg_init.simps[simp del]
  show ?case 
    apply (simp)
    apply (simp add: advance_sequence)
    apply (simp add: Suc)
    by (auto) blast+
qed auto

lemma rg_init[simp]: "set (rg_init R) = { (r,s) | l r s. (l,r) \<in> set R \<and> (r,s) \<in> qrstep nfs Q (set R)}" 
  by simp blast

declare rg_init.simps[simp del]
declare advance_sequence.simps[simp del]

lemma find_advance_seq: assumes "find is_subterm ((advance_sequence^^n) (rg_init R)) \<noteq> None" 
  shows "\<not> SN (qrstep nfs Q (set R))" 
proof - 
  from assms[unfolded find_None_iff, simplified]
  obtain r t where 
    adv: "(r, t) \<in> set ((advance_sequence ^^ n) (rg_init R))" and
    subt: "t \<unrhd> r" by auto
  from adv[unfolded advance_sequence_init, simplified]
  obtain l where lr: "(l,r) \<in> set R" and
    steps: "(r,t) \<in> (qrstep nfs Q (set R))^^Suc n" by auto
  hence steps: "(r,t) \<in> (qrstep nfs Q (set R))^+"
    using trancl_power by blast
  obtain C where "t = C \<langle> r \<rangle>" using supteq_ctxt_conv subt by blast
  with steps have steps: "(r, C \<langle> r \<rangle>) \<in> (qrstep nfs Q (set R))^+" by auto 
  with loop_imp_not_SN_on_qrstep[of r Var nfs Q "set R"]
  have "\<not> SN_on (qrstep nfs Q (set R)) {r}" by auto
  thus ?thesis unfolding SN_on_def by blast
qed


lemma advance_applied_to_empty: "advance_sequence [] = []"
  by (smt (verit, ccfv_SIG) advance_sequence empty_Collect_eq in_set_simps(3) set_empty)


lemma staying_empty: assumes "(advance_sequence^^n) S = []"
  shows "(advance_sequence^^(Suc n)) S = []"
  using advance_applied_to_empty assms by simp

lemma chain_guarantees_step: assumes "(r, f (Suc n)) \<in> set ((advance_sequence ^^ n) S)" and "chain (qrstep nfs Q (set R)) f"
  shows "(r,f(Suc(Suc n))) \<in> set ((advance_sequence^^(Suc n)) S)"
  using advance_sequence assms(1) assms(2) rg by auto


lemma chain_guarantees_steps: assumes "(r, f (Suc 0)) \<in> set ((advance_sequence ^^ 0)  S)" and "chain (qrstep nfs Q (set R)) f"
  shows "(r,f (Suc i)) \<in> set ((advance_sequence ^^i) S)"
  by (induction i, insert chain_guarantees_step assms, auto)

lemma no_chain: assumes "(advance_sequence^^(Suc n)) S = []" and "(f 0, f 1) \<in> set S"
  shows "\<not>chain (qrstep nfs Q (set R)) f"
proof (rule ccontr)
  assume 0: "\<not>\<not>chain (qrstep nfs Q (set R)) f"
  from this and assms have "(f 0, f (Suc n)) \<in> set ((advance_sequence^^ n) S)"  by (metis One_nat_def funpow_0 chain_guarantees_steps)
  from this and assms have "\<not> chain (qrstep nfs Q (set R)) f" by (metis One_nat_def empty_iff funpow_0 list.set(1) chain_guarantees_steps)
  from this and 0 have "False" by simp
  show "False" using "0" \<open>\<not> (\<forall>i. (f i, f (Suc i)) \<in> qrstep nfs Q (set R))\<close> by auto
qed

lemma advance_sequence_empty: assumes "(advance_sequence^^ n) (rg_init R) = []"
  shows "SN_on (qrstep nfs Q (set R)) (rhss (set R))" 
  using no_chain[OF staying_empty[OF assms], unfolded rg_init] by fastforce

lemma advance_sequence_empty_2: assumes "(advance_sequence^^ n) (rg_init R) = []"
  shows "SN (qrstep nfs Q (set R))"
  using advance_sequence_empty assms rg_SN_on_rhss_imp_SN[OF _ rg] by blast

lemma advance_sequence_empty_3: assumes "\<exists>n.(advance_sequence^^ n) (rg_init R) = []"
  shows "SN (qrstep nfs Q (set R))"
  using advance_sequence_empty assms rg_SN_on_rhss_imp_SN[OF _ rg] by blast

lemma advance_Suc: "advance_sequence ((advance_sequence ^^ n) S)
  = (advance_sequence ^^ (Suc n)) S" by simp

lemma termination_step_recursion: assumes "right_ground_termination_step ((advance_sequence^^n) (rg_init R)) = False"
  shows "i \<le> n \<Longrightarrow> right_ground_termination_step ((advance_sequence^^(n-i)) (rg_init R)) = False"
proof (induction i)
  case 0
  then show ?case by (simp add: assms)
next
  case (Suc i)  
  hence id: "Suc (n - Suc i) = n - i" by auto
  from Suc show ?case using staying_empty[of _ "rg_init R"]
    apply (subst right_ground_termination_step.simps)
    apply (unfold advance_Suc id) 
    by (metis Suc_leD id right_ground_termination_step.simps)
qed

lemma rstep_exists_first_step: assumes "(s,t) \<in> (qrstep nfs Q (set R))^+" and "(s,t) \<notin> qrstep nfs Q (set R)"
  shows "\<exists>u. (s,u) \<in> qrstep nfs Q (set R) \<and> (u,t) \<in> (qrstep nfs Q (set R))^+"
  by (meson assms(1) assms(2) converse_tranclE)

lemma aS_steps: assumes "(r,s) \<in> set( (advance_sequence^^n) pairs)" and "(s,t) \<in> (qrstep nfs Q (set R))^+"
  shows "\<exists>m. (r,t) \<in> set( (advance_sequence^^((Suc^^m) n)) pairs)"
  using assms(2,1)
proof (induct s t)
  case (r_into_trancl s t)
  then show ?case by (intro exI[of _ 1], auto simp: advance_sequence)
next
  case (trancl_into_trancl s t u)
  then obtain m where "(r, t) \<in> set ((local.advance_sequence ^^ (Suc ^^ m) n) pairs)" by auto
  then show ?case using trancl_into_trancl(3) 
    by (intro exI[of _ "Suc m"], auto simp: advance_sequence)
qed
   
lemma sometime_empty_steps:  assumes "SN (qrstep nfs Q (set R))" 
shows "\<exists>n. (advance_sequence^^n) xs = []" 
proof -
  let ?R = "qrstep nfs Q (set R)"  
  from assms have "wf (?R^-1)" by (rule SN_imp_wf)
  hence "wf (mult (?R^-1))" by (rule wf_mult)
  hence wf: "wf (inv_image (mult (?R^-1)) (mset o map snd) :: (('f,'v)rules rel))" (is "wf ?Rel") by blast
  show ?thesis
  proof (induct xs rule: wf_induct[OF wf])
    case (1 xs)
    define ys where "ys = advance_sequence xs" 
    show ?case
    proof (cases "ys = []")
      case True
      thus ?thesis unfolding ys_def by (intro exI[of _ 1], auto)
    next
      case False
      hence xs: "xs \<noteq> []" unfolding ys_def by (cases xs, auto simp: advance_applied_to_empty)
      have "(ys,xs) \<in> ?Rel"
        apply (simp)
        apply (intro pairwise_imp_mult)
        subgoal using xs by simp
        subgoal proof (clarsimp, goal_cases)
          case (1 r t)
          from this[unfolded ys_def advance_sequence, simplified]
          obtain s where "(r,s) \<in> set xs" and "(s,t) \<in> ?R" by auto
          thus ?case by (intro bexI[of _ "(r,s)"], auto)
        qed
        done
      from 1[rule_format, OF this] obtain n where "(advance_sequence^^n) ys = []" by auto
      thus ?thesis unfolding ys_def by (intro exI[of _ "Suc n"], simp add: funpow_swap1)
    qed
  qed
qed


lemma algGivesTrue: assumes "SN (qrstep nfs Q (set R))"
  shows "right_ground_termination R = True" 
proof - 
  have find: "find is_subterm ((advance_sequence ^^n)(rg_init R)) = None" for n
    by (meson assms(1) find_advance_seq)
  {
    fix n
    assume adv: "(advance_sequence ^^n)(rg_init R) = []" 
    have "right_ground_termination_step ((advance_sequence^^0) (rg_init R))"
    proof (induct rule: zero_induct[of _ n])
      case 1
      show ?case using adv by (metis right_ground_termination_step.simps)
    next
      case (2 n)
      thus ?case 
        apply (subst right_ground_termination_step.simps)
        apply (unfold advance_Suc find)
        by metis
    qed
    hence "right_ground_termination R" unfolding right_ground_termination_def using assms by auto
  }
  then show ?thesis
    using assms(1) sometime_empty_steps by blast
qed

lemma rhs_in_init: assumes "(r,s) \<in> qrstep nfs Q (set R)" and "(l,r) \<in> set R" and "right_ground_TRS (set R)"
  shows "(r,s) \<in> set (rg_init R)" using assms(1) assms(2) assms(3) by auto

lemma algGivesFalse: assumes "\<not>SN (qrstep nfs Q (set R))" 
  shows "right_ground_termination R = False"
proof -
  obtain l r C where "(l,r) \<in> (set R) \<and> ((r, C \<langle> r \<rangle>) \<in> (qrstep nfs Q (set R))^+)" using termination_implies_cycle[OF _ assms rg]
    by blast
  then show ?thesis
  proof (cases "(r, C\<langle>r\<rangle>) \<in> qrstep nfs Q (set R)")
    case True
    have "(r, C\<langle>r\<rangle>) \<in> set (rg_init R)"
      using True \<open>(l, r) \<in> set R \<and> (r, C\<langle>r\<rangle>) \<in> (qrstep nfs Q (set R))\<^sup>+\<close> rg rhs_in_init by blast
    hence "find is_subterm ((advance_sequence ^^0)(rg_init R)) \<noteq> None"
      by (metis find_None_iff funpow_0 is_subterm.simps supteq_ctxt_conv)
    hence "right_ground_termination_step (rg_init R) = False" 
      by (metis advance_sequence_empty_2 assms(1) funpow_0 right_ground_termination_step.simps)
    then show ?thesis by (simp add: right_ground_termination_def)
  next
    case False
    from this obtain u where "(r,u) \<in> qrstep nfs Q (set R) \<and> (u,C\<langle>r\<rangle>) \<in> (qrstep nfs Q (set R))^+"
      using \<open>(l, r) \<in> set R \<and> (r, C\<langle>r\<rangle>) \<in> (qrstep nfs Q (set R))\<^sup>+\<close> rstep_exists_first_step by blast
    from this obtain n where "(r,C\<langle>r\<rangle>) \<in> set ((advance_sequence ^^n) (rg_init R))"
      by (metis \<open>(l, r) \<in> set R \<and> (r, C\<langle>r\<rangle>) \<in> (qrstep nfs Q (set R))\<^sup>+\<close> aS_steps rg funpow_0 rhs_in_init)
    hence "find is_subterm ((advance_sequence ^^n)(rg_init R)) \<noteq> None"
      by (metis find_None_iff is_subterm.simps supteq_ctxt_conv)
    hence "right_ground_termination_step (((advance_sequence ^^n)(rg_init R))) = False"
      by (meson advance_sequence_empty_3 assms(1) right_ground_termination_step.simps)
    from termination_step_recursion[OF this le_refl]
    have "right_ground_termination_step (rg_init R) = False" by auto
    then show ?thesis by (simp add: right_ground_termination_def)
  qed
qed    

lemma right_ground_termination: "right_ground_termination R = SN (qrstep nfs Q (set R))" 
proof (cases "SN (qrstep nfs Q (set R))")
  case True
  from algGivesTrue[OF True] True show ?thesis by auto
next
  case False
  from algGivesFalse[OF False] False show ?thesis by auto
qed
end
end
end
