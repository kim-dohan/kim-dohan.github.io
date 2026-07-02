section\<open>Fresh variable addition\<close>

theory Fresh_Variable_Addition
  imports Cooperation_Program Show_LTS
begin

  
lemma range_lookup_default_of_alist: "range (Mapping.lookup_default d (Mapping.of_alist xs)) \<subseteq> insert d (snd ` set xs)" 
proof
  fix y
  assume "y \<in> range (Mapping.lookup_default d (Mapping.of_alist xs))" 
  then obtain x where y: "y = Mapping.lookup_default d (Mapping.of_alist xs) x" by auto
  show "y \<in> insert d (snd ` set xs)" 
  proof (cases "Mapping.lookup (Mapping.of_alist xs) x")
    case None
    then show ?thesis unfolding y Mapping.lookup_default_def by auto
  next
    case (Some z)
    then have y: "y = z" unfolding Mapping.lookup_default_def y by auto
    from Some have "(x,z) \<in> set xs" unfolding lookup_of_alist by (metis map_of_SomeD)
    then show ?thesis unfolding y by auto
  qed
qed

context lts begin

lemma transition_rule_refine_transition_formula: "transition_rule (refine_transition_formula tau f) = 
  (transition_rule tau \<and> formula f)" by (cases tau, auto)
    
lemma assignment_update[intro]:
  "assignment \<alpha> \<Longrightarrow> a \<in> Values_of_type ty \<Longrightarrow> assignment (\<alpha>((x,ty):=a))"
  unfolding assignment_def by auto

definition update_state ("_ |\<^sub>s _ := _")
  where "update_state s x a = State ((valuation s)(x:=a)) (location s)"

lemma location_update[simp]: "location (s |\<^sub>s x := a) = location s"
  and valuation_update[simp]: "valuation (s |\<^sub>s x := a) = (valuation s)(x:=a)"
  by (auto simp: update_state_def)

lemma state_update:
  "state s \<Longrightarrow> a \<in> Values_of_type ty \<Longrightarrow> state (s |\<^sub>s (x,ty):=a)"
  unfolding state_def valuation_update by(rule assignment_update)

definition change_fresh :: "'v \<Rightarrow> 't \<Rightarrow> (('v,'t,'d,'l) state \<times> ('v,'t,'d,'l) state) set"
where "change_fresh x ty \<equiv> { (s, s |\<^sub>s (x,ty) := a ) | s a. state s \<and> a \<in> Values_of_type ty }"

lemma mem_change_freshI[intro]:
  assumes a: "a \<in> Values_of_type ty"
      and s: "state s"
      and l: "location s = location t"
      and v: "valuation t = (valuation s)((x,ty):=a)"
  shows "(s,t) \<in> change_fresh x ty"
  unfolding change_fresh_def mem_Collect_eq prod.inject
proof(intro exI conjI)
  show "t = (s |\<^sub>s (x, ty) := a)" unfolding update_state_def l v[symmetric] by auto
qed (insert a s, auto)

lemma mem_change_freshD[dest]:
  assumes "(s,t) \<in> change_fresh x ty"
  shows "location s = location t"
    and "state s"
    and "state t"
    and "\<exists>a \<in> Values_of_type ty. valuation t = (valuation s)((x,ty):=a)"
  using assms[unfolded change_fresh_def] state_update by auto

lemma change_fresh_sym:
  assumes "(s,t) \<in> change_fresh x ty"
  shows "(t,s) \<in> change_fresh x ty"
proof
  from assms obtain a
  where a: "a \<in> Values_of_type ty" and ts: "valuation t = (valuation s)((x,ty):=a)" by auto
  with assms
  show "state t"
   and "valuation s = (valuation t)((x,ty):= valuation s (x,ty))"
   and "location t = location s" by auto
  from assms have "state s" by auto
  then show "valuation s (x, ty) \<in> Values_of_type ty" by auto
qed

lemma change_fresh_refl_on:
  shows "refl_on (Collect state :: ('v, 't, 'd, 'l) state set) (change_fresh x ty)"
proof(rule refl_onI)
  fix s :: "('v, 't, 'd, 'l) state" assume s: "s \<in> Collect state"
  show "(s,s) \<in> change_fresh x ty"
  proof
    from s show "state s" by auto
    then show "valuation s (x,ty) \<in> Values_of_type ty" by auto
  qed auto
qed auto

lemma change_fresh_trans: "trans (change_fresh x ty)" (is "trans ?S")
proof(rule transI)
  fix s t u assume st: "(s,t) \<in> ?S" and tu: "(t,u) \<in> ?S"
  show "(s,u) \<in> ?S"
  proof
    from tu show "valuation u (x,ty) \<in> Values_of_type ty" by auto
  qed(insert mem_change_freshD[OF st] mem_change_freshD[OF tu], auto)
qed

definition "fresh_variable_cond P P' x ty \<equiv>
  lts.initial P' = lts.initial P \<and> assertion P' = assertion P \<and>
  (\<forall> l. (x,ty) \<notin> vars_formula (assertion P l)) \<and>
  (\<forall> l r \<phi>. Transition l r \<phi> \<in> transition_rules P \<longrightarrow>
    (\<exists> \<phi>'. Transition l r \<phi>' \<in> transition_rules P' \<and>
       (\<forall>\<alpha>. assignment \<alpha> \<longrightarrow> \<alpha> \<Turnstile> \<phi> \<longrightarrow> (\<exists>a \<in> Values_of_type ty. \<alpha>((Post x,ty) := a) \<Turnstile> \<phi>')))) \<and>
  (\<forall> \<tau>' \<in> transition_rules P'. \<forall> (s,t) \<in> transition_step_lts P \<tau>'. \<forall> a \<in> Values_of_type ty.
   \<exists> b \<in> Values_of_type ty. (s |\<^sub>s (x,ty):=a, t |\<^sub>s (x,ty):=b) \<in> transition_step_lts P \<tau>')"

lemma fresh_variable_condD:
  assumes "fresh_variable_cond P P' x ty"
  shows "lts.initial P' = lts.initial P"
    and "\<And>l r \<phi>. Transition l r \<phi> \<in> transition_rules P \<Longrightarrow> \<exists>\<phi>'. Transition l r \<phi>' \<in> transition_rules P' \<and>
        (\<forall>\<alpha>. assignment \<alpha> \<longrightarrow> \<alpha> \<Turnstile> \<phi> \<longrightarrow> (\<exists>a \<in> Values_of_type ty. \<alpha>((Post x,ty) := a) \<Turnstile> \<phi>'))"
    and "\<And>\<tau>' s t a. \<tau>' \<in> transition_rules P' \<Longrightarrow> (s,t) \<in> transition_step_lts P \<tau>' \<Longrightarrow> a \<in> Values_of_type ty \<Longrightarrow>
   \<exists> b \<in> Values_of_type ty. (s |\<^sub>s (x,ty):=a, t |\<^sub>s (x,ty):=b) \<in> transition_step_lts P \<tau>'"
    and "assertion P' = assertion P" 
    and "\<And> l. (x,ty) \<notin> vars_formula (assertion P l)" 
  using assms[unfolded fresh_variable_cond_def] by (atomize(full), force)

lemma fresh_variable_cond_imp_step:
  assumes "fresh_variable_cond P P' x ty" and "\<tau> \<in> transition_rules P"
  shows "\<exists>\<tau>' \<in> transition_rules P'.
    source \<tau>' = source \<tau> \<and>
    target \<tau>' = target \<tau> \<and>
    (\<forall>(s,t) \<in> transition_step_lts P \<tau>. \<exists>a \<in> Values_of_type ty. (s, t |\<^sub>s (x,ty):=a) \<in> transition_step_lts P \<tau>')"
proof(cases \<tau>)
  case \<tau>: (Transition l r \<phi>)
  let ?ppi = "\<lambda>s t. pre_post_inter  (valuation s) (valuation t)"
  from \<tau> fresh_variable_condD(2)[OF assms[unfolded \<tau>]] obtain \<phi>'
  where 1: "Transition l r \<phi>' \<in> transition_rules P'"
    and 2: "\<And>\<alpha>. assignment \<alpha> \<Longrightarrow> \<alpha> \<Turnstile> \<phi> \<Longrightarrow> (\<exists>a \<in> Values_of_type ty. \<alpha>((Post x, ty) := a) \<Turnstile> \<phi>')" by auto
  note lc = fresh_variable_condD(5)[OF assms(1)]
  show ?thesis
  proof (intro bexI[OF _ 1] conjI ballI2)
    fix s t assume "(s,t) \<in> transition_step_lts P \<tau>"
    with \<tau> obtain \<alpha>
    where \<alpha>: "assignment \<alpha>"
      and s: "state s"
      and t: "state t"
      and 3: "?ppi s t \<alpha> \<Turnstile> \<phi>" (is "?a \<Turnstile> _")
      and 4: "state_lts P s" "state_lts P t" 
      and [simp]: "l = location s" "r = location t" by auto
    from s t \<alpha> have "assignment ?a" by auto
    from 2[OF this 3] obtain a
      where a: "a \<in> Values_of_type ty" and *: "?a((Post x, ty) := a) \<Turnstile> \<phi>'" by auto
    from 4(2) fresh_variable_condD(5)[OF assms(1), of r]
    have lct: "(valuation t)((x, ty) := a) \<Turnstile> assertion P (location t)" by auto
    note *
    also have "(?a((Post x, ty) := a)) xx = ?ppi s (t |\<^sub>s (x,ty):=a) \<alpha> xx" for xx by(cases xx, cases "fst xx",auto)
    then have "?a((Post x, ty) := a) = ?ppi s (t |\<^sub>s (x,ty):=a) \<alpha>" by auto
    finally have "... \<Turnstile> \<phi>'" by auto
    with s t \<alpha> a 4 lct show "\<exists>a\<in>Values_of_type ty. (s, t |\<^sub>s (x, ty) := a) \<in> transition_step_lts P (Transition l r \<phi>')"
      by (intro bexI[OF _ a] mem_transition_stepI, auto simp: lc)
  qed (insert \<tau>, auto)
qed



context
  fixes P P' :: "('f,'v,'t,'l sharp) lts" and x :: 'v and ty :: 't
  assumes fv: "fresh_variable_cond P P' x ty"
begin
    
interpretation indexed_rewriting "transition_step_lts P" .
        
lemma change_fresh_O_transition_step:
  assumes \<tau>': "\<tau>' \<in> transition_rules P'"
  shows "change_fresh x ty O transition_step_lts P \<tau>' \<subseteq> transition_step_lts P \<tau>' O change_fresh x ty" (is "?L \<subseteq> ?R")
proof
  fix s u assume L: "(s,u) \<in> ?L"
  then obtain t where st: "(s,t) \<in> change_fresh x ty" and tu: "(t,u) \<in> transition_step_lts P \<tau>'" by auto
  let ?a = "valuation s (x,ty)"
  from st have s: "assignment (valuation s)" and t: "assignment (valuation t)" by auto
  then have a': "?a \<in> Values_of_type ty" by auto
  from tu have u: "assignment (valuation u)" by auto
  from st obtain a where "valuation t = (valuation s)((x,ty):=a)" by auto
  moreover have "...((x,ty):= valuation s (x,ty)) = valuation s" by auto
  moreover from st have "location t = location s" by auto
  ultimately have "(t |\<^sub>s (x,ty) := ?a) = s" unfolding update_state_def by (cases t, auto)
  from fresh_variable_condD(3)[OF fv \<tau>' tu a', unfolded this]
  obtain b where b: "b \<in> Values_of_type ty" and sv: "(s, u |\<^sub>s (x, ty) := b) \<in> transition_step_lts P \<tau>'" by auto
  from b u have vu: "(u |\<^sub>s (x, ty) := b, u) \<in> change_fresh x ty" by (subst change_fresh_sym, auto)
  from sv vu show "(s,u) \<in> ?R" by auto
qed

lemma change_fresh_push:
  assumes \<tau>': "\<tau>' \<in> transition_rules P'"
  shows "change_fresh x ty O transition_step_lts P \<tau>' \<subseteq> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*" (is "?L \<subseteq> ?R O ?S\<^sup>*")
proof-
  from change_fresh_O_transition_step[OF assms]
  have "?L \<subseteq> ?R O ?S".
  also have "... \<subseteq> ?R O ?S\<^sup>*" by auto
  finally show ?thesis.
qed

lemma change_fresh_O_traverse:
  assumes \<tau>s': "\<tau>s' \<subseteq> transition_rules P'"
  shows "change_fresh x ty O traverse \<tau>s' \<subseteq> traverse \<tau>s' O (change_fresh x ty)\<^sup>*" (is "?S O ?R \<subseteq> _")
proof-
  have "?S O ?R \<subseteq> ?S\<^sup>* O ?R" by auto
  also have "... \<subseteq> ?R O ?S\<^sup>*" using \<tau>s' by (intro traverse_push change_fresh_push, auto)
  finally show ?thesis .
qed

lemma change_fresh_O_flat_transitions:
  shows "change_fresh x ty O transitions_step_lts P (flat_transitions_of P') \<subseteq> transitions_step_lts P (flat_transitions_of P') O (change_fresh x ty)\<^sup>*"
    (is "?L \<subseteq> ?R")
proof
  fix s t assume "(s,t) \<in> ?L"
  then obtain \<tau>
  where *: "\<tau> \<in> flat_transitions_of P'" "(s,t) \<in> change_fresh x ty O transition_step_lts P \<tau>" by auto
  then have "\<tau> \<in> transition_rules P'" by auto
  from * change_fresh_O_transition_step[OF this] have "(s,t) \<in> transition_step_lts P \<tau> O change_fresh x ty" by auto
  with * show "(s,t) \<in> ?R" by auto
qed


lemma transition_simulate:
  assumes \<tau>: "\<tau> \<in> transition_rules P"
  shows "\<exists> \<tau>' \<in> transition_rules P'.
    source \<tau>' = source \<tau> \<and>
    target \<tau>' = target \<tau> \<and>
    transition_step_lts P \<tau> \<subseteq> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*"
proof-
  from fresh_variable_cond_imp_step[OF fv \<tau>]
  obtain \<tau>'
  where \<tau>': "\<tau>' \<in> transition_rules P'"
    and [simp]: "source \<tau>' = source \<tau>" "target \<tau>' = target \<tau>"
    and *: "\<forall>(s,t) \<in> transition_step_lts P \<tau>. \<exists>a\<in>Values_of_type ty.
      (s, t |\<^sub>s (x, ty) := a) \<in> transition_step_lts P \<tau>'" by auto
  { fix s t assume st: "(s,t) \<in> transition_step_lts P \<tau>"
    from st have vs: "assignment (valuation s)" and vt: "assignment (valuation t)" by auto
    then have a': "valuation t (x,ty) \<in> Values_of_type ty" by auto
    from * st obtain a
    where a: "a \<in> Values_of_type ty" and st': "(s, t |\<^sub>s (x,ty) := a) \<in> transition_step_lts P \<tau>'" by auto
    moreover with vt have "(t |\<^sub>s (x,ty) := a, t) \<in> change_fresh x ty"
      by (intro mem_change_freshI[OF a'] state_update, auto)
    ultimately have "(s,t) \<in> transition_step_lts P \<tau>' O change_fresh x ty" by auto
    also have "... \<subseteq> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*" by auto
    finally have "(s,t) \<in> ...".
  }
  then show ?thesis by(intro bexI[OF _ \<tau>'],auto)
qed

lemma flat_transitions_simulate:
  shows "transitions_step_lts P  (flat_transitions_of P) \<subseteq> transitions_step_lts P (flat_transitions_of P') O (change_fresh x ty)\<^sup>*"
    (is "?L \<subseteq> ?R")
proof
  fix s t assume "(s,t) \<in> ?L"
  then obtain \<tau> where *: "\<tau> \<in> flat_transitions_of P" "(s,t) \<in> transition_step_lts P \<tau>" by auto
  with transition_simulate obtain \<tau>'
  where 1: "\<tau>' \<in> transition_rules P'"
    and 2: "transition_step_lts P \<tau> \<subseteq> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*" by auto
  from * 2 have 3: "(s,t) \<in> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*" by auto
  then have "source \<tau>' = location s" by auto
  moreover from * have "\<not> is_sharp (location s)" by auto
  ultimately have "\<not> is_sharp_transition \<tau>'" by auto
  with 1 have "\<tau>' \<in> flat_transitions_of P'" by auto
  with 3 show "(s,t) \<in> ?R" by auto
qed

lemma sharp_transition_simulate:
  assumes \<tau>: "\<tau> \<in> sharp_transitions_of P"
  shows "\<exists> \<tau>' \<in> sharp_transitions_of P'. transition_step_lts P \<tau> \<subseteq> transition_step_lts P \<tau>' O (change_fresh x ty)\<^sup>*"
    (is "\<exists> \<tau>' \<in> _. ?goal \<tau>'")
proof-
  from \<tau> have "\<tau> \<in> transition_rules P" by auto
  from transition_simulate[OF this] obtain \<tau>'
  where 1: "\<tau>' \<in> transition_rules P'"
    and 2: "source \<tau>' = source \<tau>"
    and 3: "?goal \<tau>'" by auto
  from \<tau> 1 2 have "\<tau>' \<in> sharp_transitions_of P'" by auto
  with 3 show ?thesis by auto
qed

lemma sharp_transition_simulate_fun:
  "\<exists>f. \<forall>\<tau> \<in> sharp_transitions_of P.
   f \<tau> \<in> sharp_transitions_of P' \<and> transition_step_lts P \<tau> \<subseteq> transition_step_lts P (f \<tau>) O (change_fresh x ty)\<^sup>*"
  using sharp_transition_simulate by (intro bchoice, auto)

lemma sharp_traverse_simulate:
  assumes \<tau>s: "\<tau>s \<subseteq> sharp_transitions_of P" and nonemp: "\<tau>s \<noteq> {}"
  shows "\<exists>\<tau>s' \<subseteq> sharp_transitions_of P'. \<tau>s' \<noteq> {} \<and> traverse \<tau>s \<subseteq> traverse \<tau>s' O (change_fresh x ty)\<^sup>*"
proof-
  let ?S = "change_fresh x ty"
  interpret I': indexed_rewriting "(\<lambda>\<tau>'. transition_step_lts P \<tau>' O ?S\<^sup>* )".

  from sharp_transition_simulate_fun obtain f
  where dom: "\<forall>\<tau> \<in> sharp_transitions_of P. f \<tau> \<in> sharp_transitions_of P'"
  and mono: "\<forall>\<tau> \<in> sharp_transitions_of P. transition_step_lts P \<tau> \<subseteq> transition_step_lts P (f \<tau>) O ?S\<^sup>*" by auto
  with transition_simulate
  interpret rule_morphism id "sharp_transitions_of P" f "transition_step_lts P"  "(\<lambda>\<tau>'. transition_step_lts P \<tau>' O ?S\<^sup>* )"
    by (unfold_locales,auto)

  note recurring_morphism

  interpret I: indexed_rewriting "(\<lambda>\<tau>. transition_step_lts P (f \<tau>) O ?S\<^sup>* )".

  have *: "I.traversed \<tau>s seq i \<Longrightarrow> I'.traversed (f ` \<tau>s) seq i" for seq i
    by(induct rule: I.traversed.induct, unfold image_empty image_insert; intro I'.traversed.intros)

  show ?thesis
  proof (intro exI conjI)
    from \<tau>s dom show "f ` \<tau>s \<subseteq> sharp_transitions_of P'" by auto
    have "traverse \<tau>s \<subseteq> I.traverse \<tau>s" apply(rule traverse_mono) using mono assms by auto
    also have "... \<subseteq> I'.traverse (f ` \<tau>s)" unfolding I'.traverse_def I.traverse_def using * by auto
    also have "... \<subseteq> traverse (f ` \<tau>s) O ?S\<^sup>*"
      apply(rule traverse_push2[OF change_fresh_push]) using dom assms by auto
    finally show "traverse \<tau>s \<subseteq> ...".
  qed (insert nonemp, auto)
qed

end

context
  fixes P P' :: "('f,'v,'t,'l sharp) lts" and x :: 'v and ty :: 't
  assumes fv: "fresh_variable_cond P P' x ty"
begin

lemma fresh_variable_addition:
  assumes "cooperation_SN P'"
  shows "cooperation_SN P"
  unfolding indexed_rewriting.cooperation_SN_on_as_SN_on_traverse
proof(intro allI impI)
  fix \<tau>s assume \<tau>s: "\<tau>s \<subseteq> sharp_transitions_of P" "\<tau>s \<noteq> {}"

  let ?S = "change_fresh x ty"
  let ?F = "transitions_step_lts P (flat_transitions_of P)"
  let ?F' = "transitions_step_lts P (flat_transitions_of P')"
  from fresh_variable_condD(4)[OF fv] 
  have lc: "assertion P' = assertion P" .
  have ts: "transition_step_lts P' = transition_step_lts P" 
    by (intro ext, auto simp: lc)
  from fresh_variable_condD(1)[OF fv]
  have [simp]: "initial_states P' = initial_states P" by (auto simp: initial_states_def lc)
  interpret indexed_rewriting "transition_step_lts P" .

  from sharp_traverse_simulate[OF fv \<tau>s] obtain \<tau>s'
  where \<tau>s': "\<tau>s' \<subseteq> sharp_transitions_of P'"
    and nonemp: "\<tau>s' \<noteq> {}"
    and sim: "traverse \<tau>s \<subseteq> traverse \<tau>s' O (change_fresh x ty)\<^sup>*" (is "?T \<subseteq> ?T' O _") by auto
  from \<tau>s' nonemp assms[unfolded ts, unfolded cooperation_SN_on_as_SN_on_traverse]
  have "SN_on ?T' (?F'\<^sup>* `` initial_states P)" by auto
  from SN_on_Image_push[OF change_fresh_O_traverse this, OF fv] \<tau>s' SN_on_mono
  have SN: "SN_on ?T' ((?F'\<^sup>* O ?S\<^sup>* ) `` initial_states P)" by (auto simp: relcomp_Image)
  from flat_transitions_simulate[OF fv] have "?F\<^sup>* \<subseteq> (?F' O ?S\<^sup>* )\<^sup>*" by (intro rtrancl_mono,auto)
  also have "... \<subseteq> (?S \<union> ?F')\<^sup>*" by regexp
  also have "... = (?F')\<^sup>* O ?S\<^sup>*" unfolding rtrancl_U_push[OF change_fresh_O_flat_transitions[OF fv]]..
  finally have "?F\<^sup>* \<subseteq> ?F'\<^sup>* O ?S\<^sup>*" by auto
  from SN_on_subset2[OF Image_mono[OF this] SN, OF subset_refl]
  have "SN_on ?T' (?F\<^sup>* `` initial_states P)" by auto
  from SN_on_O_push[OF change_fresh_O_traverse, OF fv _ this] \<tau>s'
  have "SN_on (?T' O ?S\<^sup>* ) (?F\<^sup>* `` initial_states P)" by auto
  from SN_on_mono[OF this sim]
  show "SN_on ?T (?F\<^sup>* `` initial_states P)" by auto
qed

end 

end 

datatype ('f,'v,'ty,'tr) fresh_variable_addition_info =  Fresh_Variable_Addition_Info 
  'v (* variable *)
  'ty (* type of variable *)
  "('tr \<times> ('f,'v trans_var, 'ty) exp formula) list" (* additional formulas *)
  
locale pre_transition_definability_checker =
  lts where type_fixer = "TYPE('f\<times>'t\<times>'d)" +
  pre_definability_checker where type_fixer = "TYPE('f\<times>'v trans_var\<times>'t\<times>'d)" +
  showsl_transition sa sa2
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd) itself"
  and sa :: "('f,'v,'t) exp \<Rightarrow> showsl"
  and sa2 :: "('f,'v trans_var,'t)exp \<Rightarrow> showsl"
begin

definition fresh_variable_checker :: 
  "('f,'v,'t,'l :: showl,'tr :: showl) lts_impl \<Rightarrow> ('tr \<Rightarrow> ('f, 'v trans_var, 't) exp formula) \<Rightarrow> 'v \<Rightarrow> 't \<Rightarrow> showsl check" where 
  "fresh_variable_checker P f x ty \<equiv> do {
    check_allm (\<lambda> (l, f). check ((x,ty) \<notin> vars_formula f) 
      (showsl x o showsl_lit (STR '' is not fresh, it occurs in location condition of '') o showsl l))
      (assertion_impl P);
    check_allm (\<lambda> (tr,\<tau>). let \<psi> = f tr in 
      (check (formula \<psi>) (showsl_lit (STR ''new transition formula seems to be not well-formed'')) \<then>
      (case \<tau>
      of Transition l r \<phi> \<Rightarrow>
        do {definability_checker (Post x) ty \<psi>;
         check ((Post x,ty) \<notin> vars_formula \<phi>) (showsl_lit (STR ''Post x in transition formula'') o T.showsl_formula \<phi>);
         check ((Pre x, ty) \<notin> vars_formula \<phi>) (showsl_lit (STR ''Pre x in transition formula'') o T.showsl_formula \<phi>)
        })
      <+? (\<lambda> s. showsl_lit (STR ''problem in transition formula of transition '') o showsl tr o showsl_nl o s))) 
     (transitions_impl P)
  }
  <+? (\<lambda> s. showsl_lit (STR ''fresh_variable_checker failed\<newline>'') o s)"

fun fresh_variable_addition :: "('f,'v,'t,'l :: showl,'tr :: showl) lts_impl \<Rightarrow> ('f, 'v, 't, 'tr) fresh_variable_addition_info 
  \<Rightarrow> showsl + ('f, 'v, 't, 'l, 'tr) lts_impl" where
  "fresh_variable_addition P (Fresh_Variable_Addition_Info x ty forms) = (let 
      m = Mapping.of_alist forms;
      f = Mapping.lookup_default form_True m in 
    check_return (do {
      check_allm (\<lambda> f. check (formula f) (showsl f o showsl_lit (STR '' is not a valid formula''))) (map snd forms);
      fresh_variable_checker P f x ty
    } <+? (\<lambda> s. showsl_lit (STR ''problem in adding fresh variable '') o showsl x o showsl_nl o s) )
    (refine_transition_formulas P f))" 
end

declare pre_transition_definability_checker.fresh_variable_checker_def[code]
declare pre_transition_definability_checker.fresh_variable_addition.simps[code]

locale transition_definability_checker =
  pre_transition_definability_checker + definability_checker where type_fixer = "TYPE(_)"
begin

lemma fresh_variable_checker:
  assumes ok: "isOK (fresh_variable_checker P f x ty)"
  shows "fresh_variable_cond (lts_of P) (lts_of (refine_transition_formulas P f)) x ty"
    (is "fresh_variable_cond _ ?P x ty")
proof(unfold fresh_variable_cond_def, intro conjI ballI2 ballI allI impI)
  note ok = ok[unfolded fresh_variable_checker_def, simplified]
  from ok show "lts.initial ?P = lts.initial (lts_of P)" by auto
  { fix l r \<phi>
    assume \<tau>: "Transition l r \<phi> \<in> transition_rules (lts_of P)"
    then obtain tr where tr: "(tr, Transition l r \<phi>) \<in> set (transitions_impl P)" by auto
    with ok
    have 1: "isOK (definability_checker (Post x) ty (f tr))"
     and 2: "(Post x, ty) \<notin> vars_formula \<phi>" by auto
    show "\<exists>\<phi>'.
            Transition l r \<phi>' \<in> transition_rules ?P \<and>
            (\<forall>\<alpha>. assignment \<alpha> \<longrightarrow> \<alpha> \<Turnstile> \<phi> \<longrightarrow> (\<exists>a \<in> Values_of_type ty. \<alpha>((Post x, ty) := a) \<Turnstile> \<phi>'))"
    proof(intro exI conjI allI impI)
      from tr show "Transition l r (\<phi> \<and>\<^sub>f f tr) \<in> transition_rules ?P" by (unfold refine_transition_formulas_def, force)
      fix \<alpha>
      assume \<alpha>: "assignment \<alpha>"
         and 4: "\<alpha> \<Turnstile> \<phi>"
      from definability_checker[OF 1 \<alpha>] obtain a
      where 5: "a \<in> Values_of_type ty"
        and 6: "\<alpha>((Post x, ty) := a) \<Turnstile> f tr" by auto
      from 2 4 have "\<alpha>((Post x, ty) := a) \<Turnstile> \<phi>" by auto
      with 6 have "\<alpha>((Post x, ty) := a) \<Turnstile> \<phi> \<and>\<^sub>f f tr" by auto
      with 5 show "\<exists>a \<in> Values_of_type ty. \<alpha>((Post x, ty) := a) \<Turnstile> (\<phi> \<and>\<^sub>f f tr)" by auto
    qed
  }
  show "assertion (lts_of (refine_transition_formulas P f)) =
    assertion (lts_of P)" 
    by (cases P, auto simp: refine_transition_formulas_def assertion_of_def)
  from ok have lc: "\<And> l f. (l,f) \<in> set (assertion_impl P) \<Longrightarrow> (x,ty) \<notin> vars_formula f" by auto
  show lc: "(x, ty) \<notin> vars_formula (assertion (lts_of P) l)" for l 
    by (unfold lts_of_simps assertion_of_def, rule map_of_defaultI[OF lc], auto)
  { fix \<tau>' s t a
    assume \<tau>': "\<tau>' \<in> transition_rules ?P"
       and st: "(s,t) \<in> transition_step_lts (lts_of P) \<tau>'"
       and a: "a \<in> Values_of_type ty"
    let ?s = "s |\<^sub>s (x,ty) := a"
    show "\<exists>b \<in> Values_of_type ty. (?s, t |\<^sub>s (x, ty) := b) \<in> transition_step_lts (lts_of P) \<tau>'"
    proof(cases \<tau>')
      case (Transition l r \<phi>')
      from \<tau>'[unfolded this, simplified] obtain tr
      where tr: "(tr, Transition l r \<phi>') \<in> set (transitions_impl (refine_transition_formulas P f))"
        by auto
      from Transition_mem_refine_transition_formulas[OF this] obtain \<phi>
      where "(tr, Transition l r \<phi>) \<in> set (transitions_impl P)" and \<phi>': "\<phi>' = (\<phi> \<and>\<^sub>f f tr)" by auto
      with ok
      have 1: "isOK (definability_checker (Post x) ty (f tr))"
       and 2: "(Post x, ty) \<notin> vars_formula \<phi>"
       and 3: "(Pre x, ty) \<notin> vars_formula \<phi>" by auto
      let ?ppi = "pre_post_inter"
      let ?\<alpha> = "valuation s"
      let ?\<beta> = "valuation t"
      from \<tau>' st \<phi>' Transition obtain \<gamma>
        where \<gamma>: "assignment \<gamma>" and "?ppi ?\<alpha> ?\<beta> \<gamma> \<Turnstile> \<phi> \<and>\<^sub>f f tr" 
        and lc': "state_lts (lts_of P) s" "state_lts (lts_of P) t" by auto
      then have 5: "?ppi ?\<alpha> ?\<beta> \<gamma> \<Turnstile> \<phi>" and 6: "?ppi ?\<alpha> ?\<beta> \<gamma> \<Turnstile> f tr" by auto
      have ass: "assignment ((?ppi (valuation ?s) ?\<beta> \<gamma>))" unfolding assignment_pre_post_inter
      proof (intro conjI \<gamma>)
        show "assignment ?\<beta>" using st by auto
        from st have "assignment ?\<alpha>" by auto
        with a 
        show "assignment (valuation s |\<^sub>s (x, ty) := a)" by auto
      qed
      from definability_checker[OF 1 this] obtain b
      where b: "b \<in> Values_of_type ty"
        and *: "(?ppi (valuation ?s) ?\<beta> \<gamma>)((Post x, ty) := b) \<Turnstile> f tr" by blast
      let ?t = "t |\<^sub>s (x,ty) := b"
      from 5 have "(?ppi ?\<alpha> ?\<beta> \<gamma>)((Pre x, ty) := a) \<Turnstile> \<phi>"
        unfolding satisfies_with_fresh_var[OF 3] by auto
      then have "?ppi (valuation ?s) ?\<beta> \<gamma> \<Turnstile> \<phi>" by auto
      then have "(?ppi (valuation ?s) ?\<beta> \<gamma>)((Post x, ty) := b) \<Turnstile> \<phi>"
        unfolding satisfies_with_fresh_var[OF 2] by auto
      then have "?ppi (valuation ?s) (valuation ?t) \<gamma> \<Turnstile> \<phi>" by auto
      with * have "?ppi (valuation ?s) (valuation ?t) \<gamma> \<Turnstile> \<phi>'" by (auto simp: \<phi>')
      with \<gamma> a st b lc' lc have "(?s,?t) \<in> transition_step_lts (lts_of P) \<tau>'" by (auto simp: Transition)
      with b show ?thesis by auto
    qed
  }
qed 

lemma fresh_variable_addition_impl:
  assumes ok: "isOK (fresh_variable_checker P f x ty)"
  and SN: "cooperation_SN_impl (refine_transition_formulas P f)"
  shows "cooperation_SN_impl P"
proof
  assume P: "lts_impl P"
  have "lts_impl (refine_transition_formulas P f)" 
    by (rule lts_impl_refine_transition_formulas[OF P], insert ok[unfolded fresh_variable_checker_def], auto)
  then show "cooperation_SN (lts_of P)"
  using SN fresh_variable_addition[OF fresh_variable_checker[OF ok]]
  by auto
qed

lemma check_fresh_variable_addition:
  assumes fva: "fresh_variable_addition P info = return Q"
  and SN: "cooperation_SN_impl Q"
shows "cooperation_SN_impl P"
proof (cases info)
  case (Fresh_Variable_Addition_Info x ty forms)
  from fva[unfolded this] obtain f where ok: "isOK(fresh_variable_checker P f x ty)"
    and Q: "Q = refine_transition_formulas P f"
    and f: "f = Mapping.lookup_default form_True (Mapping.of_alist forms)" by (auto simp: Let_def)
  show ?thesis using fresh_variable_addition_impl ok Q SN by auto
qed 
end

end
