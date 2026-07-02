(*
Author:  Dohan Kim and René Thiemann
*)

section \<open>Implementation of PCPs and Their Applications\<close>
theory Parallel_Critical_Pairs_Impl
  imports
    Parallel_Critical_Pairs
    Check_Joins
    Critical_Pairs_Impl
    Commutation
    Auxx.Finite_Renaming
begin

context
  fixes ren :: "'v :: infinite renamingN" 
begin

abbreviation (input) ren2 where "ren2 \<equiv> renaming2 ren" 

definition crit_rules :: "('f,'v)rules \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)rules" where
  "crit_rules R lp = filter (\<lambda> lr. mgu_vd ren2 (fst lr) lp \<noteq> None) R" 

fun potential_overlaps :: "('f,'v)rules \<Rightarrow> ('f,'v)term \<Rightarrow> (('f,'v)mctxt \<times> (('f,'v)rule \<times> ('f,'v)term)list) list" where
  "potential_overlaps R (Var x) = [(MVar x, [])]" 
| "potential_overlaps R (Fun f ts) = (let 
      lp = Fun f ts; 
      root_os = crit_rules R lp; 
      merge = (\<lambda> oss. (MFun f (map fst oss), concat (map snd oss)));
      rec_oss = concat_lists (map (potential_overlaps R) ts)
      in map merge rec_oss @
         map (\<lambda> lr. (MHole, [(lr, lp)])) root_os)"

lemma potential_overlaps_complete: "l =\<^sub>f (C, map snd list)
  \<Longrightarrow> \<forall>rl lp. (rl, lp) \<in> set list \<longrightarrow> rl \<in> set (crit_rules R lp)
  \<Longrightarrow> hole_poss C \<subseteq> fun_poss l
  \<Longrightarrow> (C, list) \<in> set (potential_overlaps R l) \<and> num_holes C = length list"       
proof (induct C arbitrary: l list)
  case (MHole l list)
  from eqf_MHoleE[OF MHole(1)] obtain rule where list: "list = [(rule,l)]" by auto
  from MHole(2) list have rule: "rule \<in> set (crit_rules R l)" by auto
  from MHole(3) obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  show ?case using rule unfolding list l by (auto simp: Let_def)
next
  case (MVar x l list)
  from eqfE[OF MVar(1)] have "l = Var x" "list = []" by auto
  thus ?case by auto
next
  case (MFun f Cs l list)
  let ?n = "length Cs" 
  define lists where "lists = partition_holes list Cs"
  define ls where "ls = map (\<lambda>i. fill_holes (Cs ! i) (map snd (lists ! i))) [0..< ?n]" 
  from eqfE[OF MFun(2)]
  have "l = fill_holes (MFun f Cs) (map snd list)" 
    and num: "num_holes (MFun f Cs) = length list" by auto
  have list: "list = concat (map ((!) lists) [0..<length Cs])" using num unfolding lists_def
    by simp (metis concat_partition_by length_partition_holes map_nth)
  have "l = fill_holes (MFun f Cs) (map snd list)" by fact
  also have "\<dots> = Fun f (map (\<lambda>i. fill_holes (Cs ! i) (map snd (lists ! i))) [0..< ?n])" 
    unfolding partition_holes_fill_holes_conv lists_def by simp
  finally have l: "l = Fun f ls" unfolding ls_def .
  have len: "length ls = ?n" "length lists = ?n" unfolding ls_def lists_def by auto
  {
    fix i
    assume i: "i < ?n"
    have eq: "ls ! i = fill_holes (Cs ! i) (map snd (lists ! i))" unfolding ls_def using i by auto
    have mem: "Cs ! i \<in> set Cs" using i by auto
    have eqF: "ls ! i =\<^sub>f (Cs ! i, map snd (lists ! i))" 
      by (intro eqfI[OF eq], unfold length_map lists_def, insert i num, auto)
    have "hole_poss (Cs ! i) \<subseteq> fun_poss (ls ! i)" using i MFun(4) len unfolding l by auto
    note IH = MFun(1)[OF mem eqF _ this]
    have "set (lists ! i) \<subseteq> set list" unfolding list using i by auto
    with MFun(3) have "\<forall>rl lp. (rl, lp) \<in> set (lists ! i) \<longrightarrow> rl \<in> set (crit_rules R lp)" by auto
    from IH[OF this]
    have "(Cs ! i, lists ! i) \<in> set (potential_overlaps R (ls ! i))" "num_holes (Cs ! i) = length (lists ! i)" by auto      
  } note IH = this
  show ?case unfolding l potential_overlaps.simps Let_def set_map set_append
      set_concat_lists
    apply (intro conjI UnI1, intro image_eqI[where x = "map (\<lambda> i. (Cs ! i, lists ! i)) [0 ..< ?n]"]) 
    subgoal using IH(1) len list by (auto simp: o_def intro: nth_equalityI)
    subgoal using IH(1) len by auto
    subgoal using IH(2) len list by (auto simp: length_concat intro!: arg_cong[of _ _ sum_list] nth_equalityI) 
    done
qed

lemma potential_overlaps_sound: "(C, list) \<in> set (potential_overlaps R l) \<Longrightarrow> 
  l =\<^sub>f (C, map snd list) \<and> hole_poss C \<subseteq> fun_poss l \<and> fst ` set list \<subseteq> set R \<and> num_holes C = length list" 
proof (induct l arbitrary: C list)
  case (Fun f ts C list)
  show ?case
  proof (cases "(C, list) \<in> (\<lambda>lr. (MHole, [(lr, Fun f ts)])) ` set (crit_rules R (Fun f ts))")
    case True
    thus ?thesis unfolding crit_rules_def by auto
  next
    case False
    with Fun(2)
    obtain as where len: "length as = length ts" 
      and rec: "\<And> i. i < length ts \<Longrightarrow> as ! i \<in> set (potential_overlaps R (ts ! i))" 
      and C: "C = MFun f (map fst as)" 
      and list: "list =  concat (map snd as)" 
      by (auto simp: Let_def)
    define Cs where "Cs = map fst as" 
    define lists where "lists = map snd as" 
    have len: "length as = length ts" 
      "length lists = length ts" 
      "length Cs = length ts" unfolding Cs_def lists_def using len by auto 
    {
      fix i
      assume i: "i < length ts" 
      hence mem: "ts ! i \<in> set ts" by auto
      from rec[OF i] have "(Cs ! i, lists ! i) \<in> set (potential_overlaps R (ts ! i))" 
        unfolding Cs_def lists_def using i len by auto
      from Fun(1)[OF mem this]
      have "ts ! i =\<^sub>f (Cs ! i, map snd (lists ! i))" "hole_poss (Cs ! i) \<subseteq> fun_poss (ts ! i)" 
       "fst ` set (lists ! i) \<subseteq> set R" " num_holes (Cs ! i) = length (lists ! i)" 
        by auto
    }
    note IH = this
    show ?thesis
    proof (intro conjI)
      show "fst ` set list \<subseteq> set R" 
        unfolding list lists_def[symmetric] using IH(3) unfolding len(2)[symmetric]
        by (auto simp: set_conv_nth[of lists])
      show "Fun f ts =\<^sub>f (C, map snd list)" unfolding C Cs_def[symmetric] list map_concat map_map o_def
        by (intro eqf_MFunI, insert len IH(1), auto simp: lists_def)
      show "hole_poss C \<subseteq> fun_poss (Fun f ts)" unfolding C Cs_def[symmetric] using IH(2) len by auto
      show "num_holes C = length list" 
        unfolding C list length_concat Cs_def[symmetric] lists_def[symmetric] 
        using IH(4) len by (auto intro!: arg_cong[of _ _ sum_list] nth_equalityI)
    qed
  qed
qed auto

definition parallel_critical_peaks_of_rule_impl :: "('f,'v)rules \<Rightarrow> ('f,'v) rule \<Rightarrow> (('f,'v)mctxt \<times> 
  ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)term \<times> ('f,'v)rules) list" where
  "parallel_critical_peaks_of_rule_impl R lr = (case lr of (l,r) \<Rightarrow>
      let pot_overlaps = filter (\<lambda> (_,rule_lp). rule_lp \<noteq> []) (potential_overlaps R l)
      in concat (map (\<lambda> (C, rule_lp). case mgu_vd_list ren (map (\<lambda> (rl,lp). (fst rl, lp)) rule_lp) of None \<Rightarrow> []
         | Some (\<sigma>, \<tau>) \<Rightarrow> [(C \<cdot>mc \<tau>, fill_holes (C \<cdot>mc \<tau>) (map (\<lambda> ((rl,_),\<sigma>i). snd rl \<cdot> \<sigma>i) (zip rule_lp \<sigma>)), l \<cdot> \<tau>, r \<cdot> \<tau>, map fst rule_lp)]) pot_overlaps))" 

lemma parallel_critical_peaks_of_rule_impl[simp]: "set (parallel_critical_peaks_of_rule_impl R lr) = 
  parallel_critical_peaks_of_rule ren (set R) lr" 
proof (intro set_eqI)
  fix peak
  obtain l r where lr: "lr = (l,r)" by force
  show "(peak \<in> set (parallel_critical_peaks_of_rule_impl R lr)) =
         (peak \<in> parallel_critical_peaks_of_rule ren (set R) lr)" 
  proof
    assume "peak \<in> parallel_critical_peaks_of_rule ren (set R) lr" 
    from this[unfolded parallel_critical_peaks_of_rule_def lr split]
    obtain C lps rls \<sigma> \<tau>
      where eqf: "l =\<^sub>f (C, lps)" and
         hp: "hole_poss C \<subseteq> fun_poss l" and
         nh: "num_holes C \<noteq> 0" and
         rls: "set rls \<subseteq> set R" and
         len: "length rls = num_holes C" and
         mgu: "mgu_vd_list ren (map2 (\<lambda>x. Pair (fst x)) rls lps) = Some (\<sigma>, \<tau>)" 
      and peak: "peak = (C \<cdot>mc \<tau>, fill_holes (C \<cdot>mc \<tau>) (map2 (\<lambda>x. (\<cdot>) (snd x)) rls \<sigma>), l \<cdot> \<tau>, r \<cdot> \<tau>, rls)" 
      by auto
    let ?unif = "(map2 (\<lambda>x. Pair (fst x)) rls lps)" 
    define list where "list = zip rls lps" 
    let ?n = "num_holes C" 
    from eqfE[OF eqf] len have len: "length rls = ?n" "length lps = ?n" 
      by auto
    have lps: "lps = map snd list" using len unfolding list_def by auto
    have "(C, list) \<in> set (potential_overlaps R l) \<and> num_holes C = length list"
    proof (rule potential_overlaps_complete[OF eqf[unfolded lps] _ hp], intro allI impI)
      fix lp rl
      assume "(rl, lp) \<in> set list" 
      then obtain i where i: "i < ?n" and lp: "lp = snd (list ! i)" and rl: "rl = fst (list ! i)" 
        using len unfolding set_conv_nth unfolding list_def by auto 
      from i have i': "i < length ?unif" using len by auto
      from mgu_vd_list_sound(1)[OF mgu i']
      have "fst (?unif ! i) \<cdot> \<sigma> ! i = snd (?unif ! i) \<cdot> \<tau>" .
      also have "fst (?unif ! i) = fst rl" using i len unfolding rl list_def by auto
      also have "snd (?unif ! i) = lp" using i len unfolding lp list_def by auto
      finally have "fst rl \<cdot> \<sigma> ! i = lp \<cdot> \<tau>" by auto
      from mgu_vd_complete[OF this, of ren2]
      have mgu: "mgu_vd ren2 (fst rl) lp \<noteq> None" by auto
      from rl i have "rl \<in> set rls" unfolding list_def using len by auto
      with rls have rl: "rl \<in> set R" by auto
      show "rl \<in> set (crit_rules R lp)" unfolding crit_rules_def
        using mgu rl by auto
    qed
    hence CList: "(C, list) \<in> set (filter (\<lambda>(C, rule_lp). rule_lp \<noteq> []) (potential_overlaps R l))" 
      using nh by auto
    have id: "map (\<lambda>(rl, y). (fst rl, y)) list = map2 (\<lambda>x. Pair (fst x)) rls lps" 
      unfolding list_def using len by (intro nth_equalityI, auto split: prod.splits)
  
    show "peak \<in> set (parallel_critical_peaks_of_rule_impl R lr)" 
      unfolding parallel_critical_peaks_of_rule_impl_def lr split Let_def set_concat set_map peak
      apply (intro UnionI image_eqI, rule refl, rule refl, rule CList)
      apply (unfold split id mgu, insert len, 
          auto simp: list_def intro!: arg_cong[of _ _ "fill_holes _"] nth_equalityI split: prod.splits)
      done
  next
    assume "peak \<in> set (parallel_critical_peaks_of_rule_impl R lr)"
    from this[unfolded parallel_critical_peaks_of_rule_impl_def lr split Let_def set_concat set_map]
    obtain C rule_lp \<sigma> \<tau> where pot_over: "(C, rule_lp) \<in> set (potential_overlaps R l)"
      and mgu: "mgu_vd_list ren (map (\<lambda>(rl, y). (fst rl, y)) rule_lp) = Some (\<sigma>, \<tau>)" 
      and peak: "peak = (C \<cdot>mc \<tau>, fill_holes (C \<cdot>mc \<tau>) (map2 (\<lambda>(rl, _). (\<cdot>) (snd rl)) rule_lp \<sigma>), l \<cdot> \<tau>, r \<cdot> \<tau>,
                  map fst rule_lp)" 
      and nonempty: "rule_lp \<noteq> []" 
      by force
    from mgu_vd_list_sound(2)[OF mgu] have len: "length \<sigma> = length rule_lp" by auto
    from potential_overlaps_sound[OF pot_over] 
    have eqf: "l =\<^sub>f (C, map snd rule_lp)" and hp: "hole_poss C \<subseteq> fun_poss l" and 
      rls: "fst ` (set rule_lp) \<subseteq> set R" and unifC: "num_holes C = length rule_lp" 
      by auto
    have id1: "map2 (\<lambda>(rl, _). (\<cdot>) (snd rl)) rule_lp \<sigma> = map2 (\<lambda>x. (\<cdot>) (snd x)) (map fst rule_lp) \<sigma>" 
      using len by (auto intro!: nth_equalityI split: prod.splits)
    have id2: "map2 (\<lambda>x. Pair (fst x)) (map fst rule_lp) (map snd rule_lp) = map (\<lambda>(rl, y). (fst rl, y)) rule_lp"
      using len by (auto intro!: nth_equalityI split: prod.splits)
    show "peak \<in> parallel_critical_peaks_of_rule ren (set R) lr" 
      unfolding parallel_critical_peaks_of_rule_def lr split peak
      apply (intro CollectI, rule exI[of _ C], rule exI[of _ "map snd rule_lp"], rule exI[of _ "map fst rule_lp"], rule exI[of _ \<sigma>], rule exI[of _ \<tau>])
      apply (unfold id1 id2 unifC)
      by (intro conjI eqf hp refl mgu, insert nonempty rls, auto)
  qed
qed

definition "nontriv_ordinary_cps_impl R S = 
   filter (\<lambda> tu. fst tu \<noteq> snd tu) (map snd (critical_pairs_impl ren2 R S))" 

lemma nontriv_ordinary_cps_impl[simp]: "set (nontriv_ordinary_cps_impl R S) = 
  nontriv_ordinary_cps ren (set R) (set S)" 
  unfolding nontriv_ordinary_cps_impl_def nontriv_ordinary_cps_def by auto

definition "nonroot_parallel_peaks_impl R S = [(C, t, s, u) . 
  lr \<leftarrow> S, 
  (C, t, s, u, rls) \<leftarrow> parallel_critical_peaks_of_rule_impl R lr, 
  C \<noteq> MHole \<and> t \<noteq> u]" 

lemma nonroot_parallel_peaks_impl[simp]: "set (nonroot_parallel_peaks_impl R S)
  = nonroot_parallel_peaks ren (set R) (set S)" 
  unfolding nonroot_parallel_peaks_def nonroot_parallel_peaks_impl_def by force

definition "critical_parallel_rule_peaks_impl R S \<phi> \<psi> =
   [(C, t, s, u, max_list (map \<phi> rls), \<psi> lr). 
    lr \<leftarrow> S,
    (C, t, s, u, rls) \<leftarrow> parallel_critical_peaks_of_rule_impl R lr,
    t \<noteq> u]" 

lemma critical_parallel_rule_peaks_impl[simp]: "set (critical_parallel_rule_peaks_impl R S \<phi> \<psi>)
  = critical_parallel_rule_peaks ren (set R) (set S) \<phi> \<psi> " 
  unfolding critical_parallel_rule_peaks_impl_def critical_parallel_rule_peaks_def by force

definition "parallel_critical_pairs_impl R S = [(t, u).  lr \<leftarrow> S,
    (C, t, s, u, rls) \<leftarrow> parallel_critical_peaks_of_rule_impl R lr,
    t \<noteq> u]" 

lemma parallel_critical_pairs_impl[simp]: "set (parallel_critical_pairs_impl R S)
  = parallel_critical_pairs ren (set R) (set S)" 
  unfolding parallel_critical_pairs_impl_def parallel_critical_pairs_def by force

end (* context fixing renaming function *)

context
  fixes ren :: "'v :: {showl, infinite} renamingN" 
begin

definition check_cp_parstep_steps_sequence_comm :: 
  "('f :: showl,'v)rules \<Rightarrow> String.literal \<Rightarrow> ('f,'v)rules \<Rightarrow> String.literal \<Rightarrow>
   ('f,'v)crit_pair_info list \<Rightarrow> showsl check" where
  "check_cp_parstep_steps_sequence_comm R R' S S' cps = do {
      check_allm (\<lambda> cp. check_par_rsteps_join_sequence R R' S S' (cp_left cp) (cp_right cp) (cp_join cp))
        cps; \<comment> \<open>the joining sequences are okay\<close>
      check_allm (\<lambda> cp. check (\<exists> cp' \<in> set cps. instance_rule cp (cp_left cp', cp_right cp'))
        (showsl_lit (STR ''could not find critical pair '') o showsl cp)) 
        (nontriv_ordinary_cps_impl ren R S) \<comment> \<open>all critical pairs occur (mod. var-renaming)\<close>
    }"

lemma check_cp_parstep_steps_sequence_comm: assumes "isOK(check_cp_parstep_steps_sequence_comm R R' S S' cps)" 
  shows "cp_parstep_steps_joinable ren (set R) (set S)" 
  unfolding cp_parstep_steps_joinable_def
proof (intro allI impI)
  note check = assms[unfolded check_cp_parstep_steps_sequence_comm_def, simplified]
  fix s u
  assume "(s, u) \<in> nontriv_ordinary_cps ren (set R) (set S)" 
  with check obtain cp where cp: "cp \<in> set cps" and inst: "instance_rule (s, u) (cp_left cp, cp_right cp)" 
    by auto
  from cp check have "isOK (check_par_rsteps_join_sequence R R' S S' (cp_left cp) (cp_right cp) (cp_join cp))" 
    by auto
  from check_par_rsteps_join_sequence[OF this] obtain v where 
    join: "(cp_left cp, v) \<in> par_rstep (set R)" "(cp_right cp, v) \<in> (rstep (set S))\<^sup>*" 
    by auto
  from inst[unfolded instance_rule_def] obtain \<sigma> where su: "s = cp_left cp \<cdot> \<sigma>" "u = cp_right cp \<cdot> \<sigma>" by auto
  show "\<exists>v. (s, v) \<in> par_rstep (set R) \<and> (u, v) \<in> (rstep (set S))\<^sup>*" unfolding su
    by (intro exI[of _ "v \<cdot> \<sigma>"] conjI subst_closed_par_rstep join rsteps_closed_subst)
qed

(* figure out whether (internally computed) critical peak matches a given critical peak in the certificate *)
definition matching_cp where 
  "matching_cp cp given = (case cp of (C,s,t,u) \<Rightarrow> 
       let real_cp = [s,t,u]; cert_cp = [cp_left given, cpPeak given, cp_right given]
        in \<not> is_None (match_list Var (zip real_cp cert_cp))
         \<and> \<not> is_None (match_list Var (zip cert_cp real_cp))
         \<and> (case cp_poss given of Some ps \<Rightarrow> set ps = hole_poss C | None \<Rightarrow> False)
         )" 

(* assumes that the input term-pairs (fsts and snds) are identical modulo renaming *)
definition get_renaming_substs :: "(('f :: showl,'v)term \<times> ('f,'v)term) list \<Rightarrow> showsl + (('v \<Rightarrow> 'v) \<times> ('v \<Rightarrow> 'v))" where
  "get_renaming_substs pairs = (let 
       vfst = List.maps (vars_term_list o fst) pairs;
       vsnd = List.maps (vars_term_list o snd) pairs;
       xs = remdups (zip vfst vsnd)
      in do {
       \<comment> \<open>check should not be required, but eases soundness proof\<close>
       check (distinct (map fst xs) \<and> distinct (map snd xs)) (showsl_lit STR ''internal error in get_renamings (not distinct)\<newline>'' o showsl pairs); 
       case extend_finite_map xs of (sig, inv_sig)
        \<Rightarrow> do {
          \<comment> \<open>check should not be required, but eases soundness proof\<close>
         check_allm (\<lambda> (l,r). check (l \<cdot> (Var o sig) = r) (showsl_lit STR ''internal error in get_renamings (wrong subst)\<newline>'' o showsl pairs)) pairs;              
         return (sig, inv_sig)
       }
    })" 

lemma get_renaming_substs: assumes "get_renaming_substs pairs = return (sigma, inv_sigma)" 
  (* and forall (l,r) : set pairs. l sigma = r and l = r gamma for some substitution sigma and gamma *)
  shows "sigma (inv_sigma x) = x" "inv_sigma (sigma y) = y" "(l,r) \<in> set pairs \<Longrightarrow> r = l \<cdot> (Var o sigma)" 
proof -
  define xs where "xs = remdups (zip (List.maps (vars_term_list \<circ> fst) pairs) (List.maps (vars_term_list \<circ> snd) pairs))" 
  obtain sig isig where ext: "extend_finite_map xs = (sig,isig)" by force
  from assms[unfolded get_renaming_substs_def Let_def, folded xs_def, unfolded ext split, simplified]
  have dist: "distinct (map fst xs)" "distinct (map snd xs)" 
    and id: "sigma = sig" "inv_sigma = isig" 
    and match: "(l, r) \<in>set pairs \<Longrightarrow> l \<cdot> (Var \<circ> sig) = r" 
    by auto
  from extend_finite_map[OF dist ext] match
  show "sigma (inv_sigma x) = x" "inv_sigma (sigma y) = y" "(l,r) \<in> set pairs \<Longrightarrow> r = l \<cdot> (Var o sigma)"
    unfolding id by auto
qed
  

(* here an explicit variable renaming has to be computed *)
definition check_toyama_pcp_sequence_comm ::
  "('f :: showl,'v)rules \<Rightarrow> String.literal \<Rightarrow> ('f,'v)rules \<Rightarrow> String.literal \<Rightarrow>
   ('f,'v)crit_pair_info list \<Rightarrow> showsl check" where
  "check_toyama_pcp_sequence_comm R R' S S' cps = do {
      check_allm (\<lambda> cp. check (\<not> is_None (cp_peak cp)) (showsl_lit STR ''some peak has not been specified in PCP'')) cps;
      check_allm (\<lambda> (C,s,t,u). case find (matching_cp (C,s,t,u)) cps of 
          None \<Rightarrow> error (showsl_lit STR ''could not find the following critical peak in the certificate:\<newline>'' o showsl s o showsl_lit (STR ''<-||-'') o showsl t o showsl_lit (STR ''->'')
                   o showsl u o showsl_lit (STR ''\<newline>with parallel positions\<newline>'') o showsl_sep showsl_pos (showsl (STR ''; '')) (sorted_list_of_set (hole_poss C)))
        | Some cp \<Rightarrow> do {
              (sig, inv_sig) \<leftarrow> get_renaming_substs [(cp_left cp, s), (cpPeak cp, t), (cp_right cp, u)];
              check_toyama_pcp_join_sequence R R' S S' (inv_sig ` vars_mctxt C) (cp_left cp) (cp_right cp) (cp_join cp)}
          )
        (nonroot_parallel_peaks_impl ren R S)}"


lemma check_toyama_pcp_sequence_comm: assumes "isOK(check_toyama_pcp_sequence_comm R R' S S' cps)" 
  shows "toyama_pcp_condition ren (set R) (set S)" 
  unfolding toyama_pcp_condition_def
proof (intro ballI impI, clarify)
  fix C s t u
  assume "(C,s,t,u) \<in> nonroot_parallel_peaks ren (set R) (set S)" 
  note assms = assms[unfolded check_toyama_pcp_sequence_comm_def, simplified, THEN conjunct2, rule_format, OF this, simplified]  
  obtain cp where "find (matching_cp (C, s, t, u)) cps = Some cp" 
    using assms by (auto split: option.splits)
  note assms = assms[unfolded this option.simps Let_def]
  from assms obtain sig isig where substs: "get_renaming_substs [(cp_left cp, s), (cpPeak cp, t), (cp_right cp, u)] = Inr (sig, isig)" 
    (is "?e = _") by (cases ?e, auto)
  from assms[unfolded substs]
  have check: "isOK (check_toyama_pcp_join_sequence R R' S S' (isig ` vars_mctxt C) (cp_left cp) (cp_right cp)
               (cp_join cp))" by auto
  define \<sigma> :: "('a,'v)subst" where "\<sigma> = Var o sig" 
  note substs = get_renaming_substs[OF substs, simplified]
  have  id: "s = cp_left cp \<cdot> (Var \<circ> sig)" 
    "t = cpPeak cp \<cdot> (Var \<circ> sig)" 
    "u = cp_right cp \<cdot> (Var \<circ> sig)" 
    using substs by auto   
  from check_toyama_pcp_join_sequence[OF check]
  obtain v where joins: "(cp_left cp, v) \<in> (rstep (set S))\<^sup>*" 
    "(cp_right cp, v) \<in> par_rstep_var_restr (set R) (isig ` vars_mctxt C)" 
    by auto
  show "\<exists>v. (s, v) \<in> (rstep (set S))\<^sup>* \<and> (u, v) \<in> par_rstep_var_restr (set R) (vars_mctxt C)" unfolding id \<sigma>_def[symmetric]
  proof (intro exI[of _ "v \<cdot> \<sigma>"] conjI rsteps_closed_subst joins par_rstep_var_restr_subst, rule joins)
    show "\<sigma> x \<cdot> (Var \<circ> isig) = Var x" for x using substs(1-2) unfolding \<sigma>_def by simp
  qed
qed
end

(* figure out whether (internally computed) critical peak matches a given critical peak in the certificate *)
definition matching_peak where 
  "matching_peak cp given = (case cp of (C,s,t,u,k,m) \<Rightarrow> 
        cp_labels given = Some (k,m) \<and>
       (let real_cp = [s,t,u]; cert_cp = [cp_left given, cpPeak given, cp_right given]
        in \<not> is_None (match_list Var (zip real_cp cert_cp))
         \<and> \<not> is_None (match_list Var (zip cert_cp real_cp))
         \<and> (case cp_poss given of Some ps \<Rightarrow> set ps = hole_poss C | None \<Rightarrow> False)
         ))" 

context
  fixes ren :: "'v :: {showl, infinite} renamingN" 
begin

fun check_cp_parstep_steps_joinable where
 "check_cp_parstep_steps_joinable R R' S S' (CP_Auto n) = 
  check_allm (\<lambda> (s, t). do {
    check (is_par_rsteps_join R S (Some n) s t)
      (showsl_lit (STR ''the ordinary critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <-'' + S' + STR ''- . -'' + R' + STR ''-> '') \<circ> showsl t \<circ>
       showsl_lit (STR '' is not closed by the Gramlich's cp condition within '') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
    }) (nontriv_ordinary_cps_impl ren R S)"
| "check_cp_parstep_steps_joinable R R' S S' (CP_Sequences seqs) =
     check_cp_parstep_steps_sequence_comm ren R R' S S' seqs" 

lemma check_cp_parstep_steps_joinable: "isOK(check_cp_parstep_steps_joinable R R' S S' hints) \<Longrightarrow>
  cp_parstep_steps_joinable ren (set R) (set S)" 
  by (cases hints, auto dest: check_cp_parstep_steps_sequence_comm simp: cp_parstep_steps_joinable_def)

fun check_toyama_pcp_condition where
 "check_toyama_pcp_condition R R' S S' (CP_Auto n) = 
  check_allm(\<lambda> (C,s,peak,t). do {
    check (is_toyama_par_rstep_join n R S C s peak t)
      (showsl_lit (STR ''the parallel critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' <-||,'' + R' + STR ''- . -'' + S' + STR ''-> '') \<circ> showsl t \<circ>
       showsl_lit (STR '' is not closed by the  Toyama's pcp condition within'') \<circ> showsl n \<circ> showsl_lit (STR '' steps.''))
     }) (nonroot_parallel_peaks_impl ren R S)"
| "check_toyama_pcp_condition R R' S S' (CP_Sequences seqs) = 
     check_toyama_pcp_sequence_comm ren R R' S S' seqs" 

lemma check_toyama_pcp_condition: "isOK (check_toyama_pcp_condition R R' S S' hints) \<Longrightarrow>
  toyama_pcp_condition ren (set R) (set S)"
  by (cases hints, force simp: toyama_pcp_condition_def, force dest: check_toyama_pcp_sequence_comm)

definition check_parallel_critical_pairs_closed_comm where
 "check_parallel_critical_pairs_closed_comm R S hints_cp hints_pcp = do {
  check_left_linear_trs R;
  check_left_linear_trs S;
  check_cp_parstep_steps_joinable R (STR ''R'') S (STR ''S'') hints_cp;  
  check_toyama_pcp_condition R (STR ''R'') S (STR ''S'') hints_pcp
  } <+? (\<lambda>s. showsl_lit (STR ''failed to apply PCP-closed criterion for commutation of R and S\<newline>\<newline>'') o s \<circ> showsl_lit (STR ''\<newline>\<newline>R: '') \<circ> 
        showsl_trs R o showsl_lit (STR ''\<newline>\<newline>S: '') o showsl_trs S)"

lemma check_parallel_critical_pairs_closed_comm: 
  "isOK(check_parallel_critical_pairs_closed_comm R S hints_cp hints_pcp) \<Longrightarrow> commute (rstep (set R)) (rstep (set S))" 
  unfolding check_parallel_critical_pairs_closed_comm_def
  by (intro toyama_parallel_critical_pair_condition_commute, auto dest: check_cp_parstep_steps_joinable check_toyama_pcp_condition)

definition check_parallel_critical_pairs_closed_CR where
 "check_parallel_critical_pairs_closed_CR R hints_cp hints_pcp = do {
  check_left_linear_trs R;
  check_cp_parstep_steps_joinable R (STR ''R'') R (STR ''R'') hints_cp;  
  check_toyama_pcp_condition R (STR ''R'') R (STR ''R'') hints_pcp
  } <+? (\<lambda>s. showsl_lit (STR ''failed to apply PCP-closed criterion for proving CR of R\<newline>\<newline>'') o s \<circ> showsl_lit (STR ''\<newline>\<newline>R: '') \<circ> 
        showsl_trs R)"

lemma check_parallel_critical_pairs_closed_CR: 
  "isOK(check_parallel_critical_pairs_closed_CR R hints_cp hints_pcp) \<Longrightarrow> CR (rstep (set R))" 
  unfolding check_parallel_critical_pairs_closed_CR_def
  by (intro toyama_parallel_critical_pair_condition_CR, auto dest: check_cp_parstep_steps_joinable check_toyama_pcp_condition)
end


definition RS_conv_impl:: "('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> (('f,'v)rule \<Rightarrow> nat)
\<Rightarrow> nat \<Rightarrow> ('f,'v)rules" where
  "RS_conv_impl R S \<phi> \<psi> k = [(r, l) . (l, r) \<leftarrow> R ,  \<phi> (l, r) < k] @ [(l, r) . (l, r) \<leftarrow> S ,  \<psi> (l, r) < k]"

lemma RS_conv_impl_sound:
  "set (RS_conv_impl R S \<phi> \<psi> k) = RS_conv (set R) (set S) \<phi> \<psi> k"
  unfolding RS_conv_def RS_conv_impl_def by auto

definition R_le_impl :: "('f,'v)rules \<Rightarrow> (('f,'v)rule \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> ('f,'v)rules" where
  "R_le_impl R \<phi> k = [lr . lr \<leftarrow> R, \<phi> lr \<le> k]" 

lemma R_le_impl_sound[simp]:
  "set (R_le_impl R \<psi> k) = R_le (set R) \<psi> k" 
  unfolding R_le_def R_le_impl_def by auto

lemma RS_conv_inv:
  "(RS_conv R S \<phi> \<psi> k)^-1 = RS_conv S R \<psi> \<phi> k"
  unfolding RS_conv_def by auto

lemma rstep_inv_star:
  assumes "(s, t) \<in> (rstep (RS_conv R S \<phi> \<psi> k))^*"
  shows "(t, s) \<in> (rstep (RS_conv S R \<psi> \<phi> k))^*"
  unfolding RS_conv_def 
  by (metis (no_types, lifting) Collect_cong RS_conv_def RS_conv_inv assms converseI rstep_converse rtrancl_converse)

definition split_num :: "nat \<Rightarrow> (nat \<times> nat \<times> nat \<times> nat)list" where
  "split_num n = [ (n1, n2, n3, n4) . n1 \<leftarrow> [0..<Suc n], n2 \<leftarrow> [0..< Suc (n - n1)], n3 \<leftarrow> [0 ..< Suc (n - n2 - n1)],
                  n4 \<leftarrow> [0 ..< Suc (n - n1 - n2 -n3)]]" 

fun is_decreasing_steps where
  "is_decreasing_steps n R S C s peak t \<phi> \<psi> k m = (\<exists> (n1,n2,n3,n4) \<in> set (split_num n). 
          \<exists>u1 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> k) s n1).
          \<exists>u2 \<in> set (parallel_rewrite (R_le_impl S \<psi> m) u1).
          \<exists>u3 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> (max k m)) u2 n2).
          \<exists>u5 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> m) t n3).
          \<exists>u4 \<in> set (parallel_rewrite (R_le_impl R \<phi> k) u5).
          u3 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> (max k m)) u4 n4) \<and>
          (u5, u4) \<in> par_rstep_var_restr (set (R_le_impl R \<phi> k)) (vars_mctxt C))"

context
  fixes ren :: "'v :: {showl, infinite} renamingN" 
begin

definition check_is_decreasing_auto where
 "check_is_decreasing_auto n R S \<phi> \<psi> lf = 
  check_allm(\<lambda> (C, s, peak, t, k, m). do {
    check (lab_filter lf k m \<longrightarrow> is_decreasing_steps n R S C s peak t \<phi> \<psi> k m)
      (showsl_lit (STR ''the parallel critical pair '') \<circ> showsl s \<circ> showsl_lit (STR '' R<-||- . ->S '') \<circ> showsl t \<circ>
       showsl_lit (STR '' is not closed by the rule labeling criteria (auto mode) within the specified steps.'') \<circ> showsl n \<circ> showsl_lit (STR ''''))
     }) (critical_parallel_rule_peaks_impl ren R S \<phi> \<psi>)"

lemma check_is_decreasing_auto:
  assumes "isOK(check_is_decreasing_auto n R S \<phi> \<psi> lf)"
  shows "is_decreasing ren (set R) (set S) \<phi> \<psi> lf"
  unfolding is_decreasing_def
proof (intro allI impI)
  let ?R = "set R" let ?S = "set S" 
  fix C s peak t k m
  assume asm:"(C, s, peak, t, k, m) \<in> critical_parallel_rule_peaks ren (set R) (set S) \<phi> \<psi>"
    and lf: "lab_filter lf k m " 
  from assms asm lf have "is_decreasing_steps n R S C s peak t \<phi> \<psi> k m" 
    unfolding is_decreasing_def check_is_decreasing_auto_def
       is_decreasing_steps.simps by auto
  then have "(\<exists> (n1,n2,n3,n4) \<in> set (split_num n). 
    \<exists>u1 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> k) s n1).
    \<exists>u2 \<in> set (parallel_rewrite (R_le_impl S \<psi> m) u1).
    \<exists>u3 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> (max k m)) u2 n2).
    \<exists>u5 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> m) t n3).
    \<exists>u4 \<in> set (parallel_rewrite (R_le_impl R \<phi> k) u5).
    u3 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> (max k m)) u4 n4) \<and>
    (u5, u4) \<in> par_rstep_var_restr (R_le ?R \<phi> k) (vars_mctxt C))" by simp
  then obtain n1 n2 n3 n4 u1 u2 u3 u4 u5 where 
    "(n1,n2,n3,n4) \<in> set (split_num n)" and 
    u1:"u1 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> k) s n1)" and
    u2: "u2 \<in> set (parallel_rewrite (R_le_impl S \<psi> m) u1)" and
    u3:"u3 \<in> set (reachable_terms (RS_conv_impl R S \<phi> \<psi> (max k m)) u2 n2)" and
    u5:"u5 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> m) t n3)" and
    u4:"u4 \<in> set (parallel_rewrite (R_le_impl R \<phi> k) u5)" and
    u3': "u3 \<in> set (reachable_terms (RS_conv_impl S R \<psi> \<phi> (max k m)) u4 n4)" and
    u54:"(u5, u4) \<in> par_rstep_var_restr (R_le ?R \<phi> k) (vars_mctxt C)" by blast
  then have su1:"(s, u1) \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> k))^*" 
    by (metis RS_conv_impl_sound reachable_terms)
  moreover have u12: "(u1, u2) \<in> par_rstep (R_le ?S \<psi> m)" unfolding R_le_impl_def
    using parallel_rewrite_par_step[OF u2] R_le_impl_sound by metis
  moreover have u23:"(u2, u3) \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> (max k m)))^*" 
    using  RS_conv_impl_sound reachable_terms[OF u3] by metis
  moreover have u43:"(u4, u3) \<in> (rstep (RS_conv ?S ?R \<psi> \<phi> (max k m)))^*"
    using  RS_conv_impl_sound reachable_terms[OF u3'] by metis
  moreover have u34: "(u3, u4) \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> (max k m)))^*"
    using  RS_conv_impl_sound rstep_inv_star[OF u43] by simp 
  moreover have u24:"(u2, u4) \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> (max k m)))^*"
    using u23 u34 by simp
  moreover have "(u5, u4) \<in> par_rstep_var_restr (R_le ?R \<phi> k) (vars_mctxt C)" by fact
  moreover have "(t, u5)  \<in> (rstep (RS_conv ?S ?R \<psi> \<phi> m))^*" 
    using RS_conv_impl_sound reachable_terms[OF u5] by metis
  ultimately show "(s, t) \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> k))^* O 
    par_rstep (R_le ?S \<psi> m) O 
    (rstep (RS_conv ?R ?S \<phi> \<psi> (max k m)))^* O
    (par_rstep_var_restr (R_le ?R \<phi> k) (vars_mctxt C))^-1 O
    (rstep (RS_conv ?R ?S \<phi> \<psi> m))^*"
    by (meson converseI relcomp.relcompI rstep_inv_star)
qed

fun check_decreasing ::
  "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
   _ \<Rightarrow> _ \<Rightarrow> _ \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_decreasing R S \<phi> \<psi> lf (CP_Auto n) = check_is_decreasing_auto n R S \<phi> \<psi> lf"
| "check_decreasing R S \<phi> \<psi> lf (CP_Sequences cps) = (let Rl = map (\<lambda> x. (x, \<phi> x)) R; Sl = map (\<lambda> x. (x, \<psi> x)) S;
        Sle = (\<lambda> k. map fst (filter (\<lambda> x. snd x \<le> k) Sl));
        Rle = (\<lambda> k. map fst (filter (\<lambda> x. snd x \<le> k) Rl));
        RSconv = (\<lambda> k. map fst (filter (\<lambda> x. snd x < k) Sl) @ map (prod.swap o fst) (filter (\<lambda> x. snd x < k) Rl)) in
     do {check_allm (\<lambda> cp. check (\<not> is_None (cp_peak cp)) (showsl_lit STR ''some peak has not been specified in PCP'')) cps;
      check_allm (\<lambda> (C,s,t,u,k,m). if lab_filter lf k m then case find (matching_peak (C,s,t,u,k,m)) cps of 
          None \<Rightarrow> error (showsl_lit STR ''could not find the following critical peak in the certificate:\<newline>'' o showsl s o showsl_lit (STR ''<-||-'') o showsl t o showsl_lit (STR ''->'')
                   o showsl u o showsl_lit (STR ''\<newline>with labels (max-left,right) = '') o showsl (k,m) 
                   o showsl_lit (STR ''\<newline> and with parallel positions\<newline>'') o showsl_sep showsl_pos (showsl (STR ''; '')) (sorted_list_of_set (hole_poss C)))
        | Some cp \<Rightarrow> 
           (do {
              (sig, inv_sig) \<leftarrow> get_renaming_substs [(cp_left cp, s), (cpPeak cp, t), (cp_right cp, u)];
              let RSk = RSconv k; Sm = Sle m; RSkm = RSconv (max k m); Rk = Rle k; RSm = RSconv m in 
              check_rl_par_decreasing_sequence RSk Sm RSkm Rk RSm (inv_sig ` vars_mctxt C) (cp_left cp) (cp_right cp) (cp_join cp)}
          ) else return ()) 
        (critical_parallel_rule_peaks_impl ren R S \<phi> \<psi>)})"

lemma check_decreasing: assumes "isOK(check_decreasing R S \<phi> \<psi> lf hints)" 
  shows "is_decreasing ren (set R) (set S) \<phi> \<psi> lf" 
proof (cases hints)
  case (CP_Sequences cps)
  let ?R = "set R" let ?S = "set S" 
  show ?thesis unfolding is_decreasing_def
  proof (intro allI impI)
    fix C s t u k m
    define Rl where "Rl = map (\<lambda>x. (x, \<phi> x)) R" 
    define Sl where "Sl = map (\<lambda>x. (x, \<psi> x)) S" 
    define Sle where "Sle = (\<lambda>k. map fst (filter (\<lambda>x. snd x \<le> k) Sl))" 
    define Rle where "Rle = (\<lambda>k. map fst (filter (\<lambda>x. snd x \<le> k) Rl))" 
    define RSconv where "RSconv = (\<lambda>k. map fst (filter (\<lambda>x. snd x < k) Sl) @ map (prod.swap \<circ> fst) (filter (\<lambda>x. snd x < k) Rl))" 
    note assms = assms[unfolded CP_Sequences check_decreasing.simps, 
        folded Rl_def Sl_def, unfolded Let_def[of Rl] Let_def[of Sl],
        folded Sle_def Rle_def RSconv_def]
    assume "(C,s,t,u,k,m) \<in> critical_parallel_rule_peaks ren ?R ?S \<phi> \<psi>" "lab_filter lf k m" 
    note assms = assms[simplified, THEN conjunct2, rule_format, OF this(1), simplified]  this(2)
    obtain cp where "find (matching_peak (C, s, t, u, k, m)) cps = Some cp" 
      using assms by (auto split: option.splits)
    note assms = assms[unfolded this option.simps Let_def]

    from assms obtain sig isig where substs: "get_renaming_substs [(cp_left cp, s), (cpPeak cp, t), (cp_right cp, u)] = Inr (sig, isig)" 
      (is "?e = _") by (cases ?e, auto)
    from assms[unfolded substs]
    have check: "isOK
      (check_rl_par_decreasing_sequence (RSconv k) (Sle m) (RSconv (max k m)) (Rle k) (RSconv m)
        (isig ` vars_mctxt C) (cp_left cp) (cp_right cp) (cp_join cp))" 
      by auto
    define \<sigma> :: "('a,'v)subst" where "\<sigma> = Var o sig" 
    note substs = get_renaming_substs[OF substs, simplified]
    have  id: "s = cp_left cp \<cdot> (Var \<circ> sig)" 
      "t = cpPeak cp \<cdot> (Var \<circ> sig)" 
      "u = cp_right cp \<cdot> (Var \<circ> sig)" 
      using substs by auto   
 
    have sets: "set (RSconv k) = RS_conv ?R ?S \<phi> \<psi> k" 
      "set (Sle k) = R_le ?S \<psi> k"  
      "set (Rle k) = R_le ?R \<phi> k" for k 
      unfolding RSconv_def RS_conv_def Rl_def Sl_def Sle_def R_le_def R_le_def Rle_def by force+
    let ?x0 = "cp_left cp" 
    let ?x5 = "cp_right cp" 
    from check_rl_par_decreasing_sequence[OF check]
    obtain x1 x2 x3 x4 where joins: "(?x0, x1) \<in> (rstep (set (RSconv k)))\<^sup>*" 
      "(x1, x2) \<in> par_rstep (set (Sle m))" 
      "(x2, x3) \<in> (rstep (set (RSconv (max k m))))\<^sup>*" 
      "(x4, x3) \<in> (par_rstep_var_restr (set (Rle k)) (isig ` vars_mctxt C))" 
      "(x4, ?x5) \<in> (rstep (set (RSconv m)))\<^sup>*" 
      by auto
    show "(s, u)
       \<in> (rstep (RS_conv ?R ?S \<phi> \<psi> k))\<^sup>* O
          par_rstep (R_le ?S \<psi> m) O
          (rstep (RS_conv ?R ?S \<phi> \<psi> (max k m)))\<^sup>* O
          (par_rstep_var_restr (R_le ?R \<phi> k) (vars_mctxt C))\<inverse> O (rstep (RS_conv ?R ?S \<phi> \<psi> m))\<^sup>*" 
      unfolding id sets[symmetric]
      apply (intro relcompI converseI)
          apply (rule rsteps_closed_subst[OF joins(1)])
         apply (rule subst_closed_par_rstep[OF joins(2)])
        apply (rule rsteps_closed_subst[OF joins(3)])
       apply (rule par_rstep_var_restr_subst[OF joins(4)], use substs in force)
      apply (rule rsteps_closed_subst[OF joins(5)])
      done
  qed
next
  case CP_Auto
  thus ?thesis using assms
    by (intro check_is_decreasing_auto, auto)
qed


fun check_compositional_pcps_convertable ::
  "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_pcps_convertable R C (CP_Auto n) = check_allm (\<lambda> (t,u). 
      check (is_rsteps_conversion C C n t u) (showsl_lit (STR ''\<newline>could not find conversion of parallel critical pair '')
       o showsl t o showsl_lit (STR ''<-||- . -root->'') o showsl u ))
       (parallel_critical_pairs_impl ren R R)"
| "check_compositional_pcps_convertable R C (CP_Sequences cps) = do {
      check_allm (\<lambda> cp. check_conversion_sequence C (cp_left cp) (cp_right cp) (cp_join cp))
        cps; \<comment> \<open>the sequences are okay\<close>
      check_allm (\<lambda> cp. check (\<exists> cp' \<in> set cps. 
         instance_rule cp (cp_left cp', cp_right cp') \<or> instance_rule cp (cp_right cp', cp_left cp'))
        (showsl_lit (STR ''could not find parallel critical pair '') o showsl cp)) 
        (parallel_critical_pairs_impl ren R R) \<comment> \<open>all critical pairs occur (mod. var-renaming and direction)\<close>
    }"

definition check_compositional_pcps_joinable ::
  "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_pcps_joinable R C hints = do {
      checker \<leftarrow> is_rsteps_join_one C hints;
      check_allm checker (parallel_critical_pairs_impl ren R R)}"

text \<open>a more generic version of @{const check_compositional_pcps_joinable} which is not strictly more generic, 
  as it does not support direction symmetry\<close>
definition check_compositional_pcps_joinable_generic ::
  "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_pcps_joinable_generic R S C D hints = do {
     checker \<leftarrow> is_rsteps_join_two C D hints;
     check_allm checker (parallel_critical_pairs_impl ren R S)}"


lemma check_compositional_pcps_convertable: assumes "isOK(check_compositional_pcps_convertable R C hints)"
  shows "parallel_critical_pairs ren (set R) (set R) \<subseteq> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*" 
proof
  fix t u
  assume tu: "(t, u) \<in> parallel_critical_pairs ren (set R) (set R)" 
  show "(t, u) \<in> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*" 
  proof (cases hints)
    case (CP_Auto n)
    from assms[unfolded CP_Auto] tu show ?thesis by auto
  next
    case (CP_Sequences h)
    from assms[unfolded CP_Sequences] tu
    obtain cp where check: "isOK (check_conversion_sequence C (cp_left cp) (cp_right cp) (cp_join cp))" 
      and inst: "instance_rule (t,u) (cp_left cp, cp_right cp) \<or> instance_rule (t,u) (cp_right cp, cp_left cp)" by force
    from check_conversion_sequence[OF check] 
    have conv: "(cp_left cp, cp_right cp) \<in> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*" .
    from inst have "\<exists> cl cr. instance_rule (t,u) (cl,cr) \<and> (cl,cr) \<in> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*" 
    proof
      assume "instance_rule (t, u) (cp_left cp, cp_right cp)" 
      with conv show ?thesis by auto
    next
      assume inst: "instance_rule (t, u) (cp_right cp, cp_left cp)" 
      from conv have "(cp_right cp, cp_left cp) \<in> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*"
        by (simp add: conversion_inv)
      with inst show ?thesis by auto
    qed
    then obtain cl cr where inst: "instance_rule (t,u) (cl,cr)" 
      and conv: "(cl,cr) \<in> (rstep (set C))\<^sup>\<leftrightarrow>\<^sup>*" by auto
    from inst[unfolded instance_rule_def] obtain \<sigma> where
      id: "t = cl \<cdot> \<sigma>" "u = cr \<cdot> \<sigma>" by auto
    show ?thesis unfolding id using conv by (rule conversion_subst_closed)
  qed
qed

lemma check_compositional_pcps_joinable: assumes "isOK(check_compositional_pcps_joinable R C hints)"
  shows "parallel_critical_pairs ren (set R) (set R) \<subseteq> (rstep (set C))\<^sup>\<down>" 
proof
  fix t u
  assume tu: "(t, u) \<in> parallel_critical_pairs ren (set R) (set R)" 
  note ass = assms[unfolded check_compositional_pcps_joinable_def, simplified]
  from ass obtain checker where checker: "is_rsteps_join_one C hints = return checker" 
    by auto
  note ass = ass[unfolded checker, simplified, rule_format, OF tu]
  from ass have ok: "isOK (checker (t, u))" by auto
  from is_rsteps_join_one[OF checker ok]
  show "(t, u) \<in> (rstep (set C))\<^sup>\<down>" by blast
qed

lemma check_compositional_pcps_joinable_generic: assumes "isOK(check_compositional_pcps_joinable_generic R S C D hints)"
  shows "parallel_critical_pairs ren (set R) (set S) \<subseteq> join'' (rstep (set C)) (rstep (set D))" 
proof
  fix t u
  assume tu: "(t, u) \<in> parallel_critical_pairs ren (set R) (set S)" 
  note ass = assms[unfolded check_compositional_pcps_joinable_generic_def, simplified]
  from ass obtain checker where checker: "is_rsteps_join_two C D hints = return checker" 
    by auto
  note ass = ass[unfolded checker, simplified, rule_format, OF tu]
  from ass have ok: "isOK (checker (t, u))" by auto
  from is_rsteps_join_two[OF checker ok]
  show "(t, u) \<in> join'' (rstep (set C)) (rstep (set D))" by auto
qed

definition check_compositional_parallel_pairs :: "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_parallel_pairs R C hints = do {
     check_left_linear_trs R;
     check_subseteq C R <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') o showsl_rule lr o 
       showsl_lit (STR '' of C in R''));
     check_compositional_pcps_convertable R C hints     
   } <+? (\<lambda> e. showsl_lit (STR ''problem in compositional parallel critical pair application\<newline>'') o e)" 

lemma check_compositional_parallel_pairs: assumes "isOK(check_compositional_parallel_pairs R C hints)" 
  and "CR (rstep (set C))" 
shows "CR (rstep (set R))" 
  apply (intro compositional_parallel_critical_pairs[OF _ _ assms(2), of _ ren] check_compositional_pcps_convertable)
  using assms(1)[unfolded check_compositional_parallel_pairs_def]
  by auto
end

datatype ('f,'v) pcp_rule_lab = PCP_Sequences "('f,'v)rule \<Rightarrow> nat" "('f,'v) cp_join_hints" 
datatype ('f,'v) pcp_rule_lab_com = PCP_Sequences_Com 
  "('f,'v)rule \<Rightarrow> nat" 
  "(('f,'v)rule \<Rightarrow> nat) option" (* if the second label function is missing, then the first is used twice *)
  "('f,'v) cp_join_hints" 
  "('f,'v) cp_join_hints"

context
  fixes ren :: "'v :: {showl, infinite} renamingN" 
begin

fun check_pcp_rule_lab where 
  "check_pcp_rule_lab R (PCP_Sequences \<phi> cps) = do {
        check_left_linear_trs R;
        check_decreasing ren R R \<phi> \<phi> No_Lab_Filter cps
     }"

fun check_pcp_rule_lab_com where 
  "check_pcp_rule_lab_com R S (PCP_Sequences_Com \<phi> \<psi> cpsRS cpsSR) = (
       let \<chi> = (case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>) in 
     do {
        check_left_linear_trs R;
        check_left_linear_trs S;
        check_decreasing ren R S \<phi> \<chi> No_Lab_Filter cpsRS;
        check_decreasing ren S R \<chi> \<phi> No_Lab_Filter cpsSR
     })"

lemma check_pcp_rule_lab: assumes "isOK(check_pcp_rule_lab R prf)" 
  shows "CR (rstep (set R))" 
proof (cases "prf")
  case (PCP_Sequences \<phi> cps)
  note assms = assms[unfolded this, simplified]
  show ?thesis
  proof (rule rule_labeling_pcp_CR, unfold is_decreasing_trs)
    show "left_linear_trs (set R)" using assms by auto
    show "is_decreasing ren (set R) (set R) \<phi> \<phi> No_Lab_Filter" using assms 
      by (intro check_decreasing, auto)
  qed
qed

lemma check_pcp_rule_lab_com: assumes "isOK(check_pcp_rule_lab_com R S prf)" 
  shows "commute (rstep (set R)) (rstep (set S))" 
proof (cases "prf")
  case (PCP_Sequences_Com \<phi> \<psi> cpsRS cpsSR)
  note assms = assms[unfolded this, simplified]
  let ?\<chi> = "(case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>)" 
  show ?thesis
  proof (rule rule_labeling_pcp_commutation)
    show "left_linear_trs (set R)" using assms by auto
    show "left_linear_trs (set S)" using assms by auto
    show "is_decreasing ren (set R) (set S) \<phi> ?\<chi> No_Lab_Filter" using assms 
      by (intro check_decreasing, auto)
    show "is_decreasing ren (set S) (set R) ?\<chi> \<phi> No_Lab_Filter" using assms 
      by (intro check_decreasing, auto)
  qed
qed

fun check_compositional_pcp_rule_lab where 
  "check_compositional_pcp_rule_lab R C (PCP_Sequences_Com \<phi> \<psi> cpsPhiPsi cpsPsiPhi) = (
       let \<chi> = (case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>); R_0 = R_le_impl R \<phi> 0; R_0' = R_le_impl R \<chi> 0 in 
     do {
        check_left_linear_trs R;
        check_same_set R_0 C <+? (\<lambda> lr. showsl_lit (STR ''0-labelled TRSs is not identical to C because of rule '') o showsl_rule lr);
        check_same_set R_0' C <+? (\<lambda> lr. showsl_lit (STR ''0-labelled TRSs is not identical to C because of rule '') o showsl_rule lr);
        check_decreasing ren R R \<phi> \<chi> Zero_Zero_Filter cpsPhiPsi;        
        case \<psi> of None \<Rightarrow> return () | _ \<Rightarrow> check_decreasing ren R R \<chi> \<phi> Zero_Zero_Filter cpsPsiPhi
     })"

lemma check_compositional_pcp_rule_lab: assumes "isOK(check_compositional_pcp_rule_lab R C prf)" 
  and "CR (rstep (set C))" 
shows "CR (rstep (set R))" 
proof (cases "prf")
  case *: (PCP_Sequences_Com \<phi> \<psi> h1 h2)
  define \<chi> where "\<chi> = (case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>)" 
  from assms[unfolded *, simplified] obtain h
    where ll: "left_linear_trs (set R)" 
    and decr: "isOK (check_decreasing ren R R \<phi> \<chi> Zero_Zero_Filter h1)" 
       "isOK (check_decreasing ren R R \<chi> \<phi> Zero_Zero_Filter h)" 
    and R_phi: "R_le (set R) \<phi> 0 = set C" 
    and R_psi: "R_le (set R) \<chi> 0 = set C" 
    by (auto simp: \<chi>_def Let_def split: option.splits)
  show ?thesis using assms(2) R_phi R_psi by (intro compositional_rule_labeling_pcp_cr[OF ll 
        check_decreasing[OF decr(1)] check_decreasing[OF decr(2)]], auto)
qed

fun check_compositional_pcp_rule_lab_comm where 
  "check_compositional_pcp_rule_lab_comm R S C D (PCP_Sequences_Com \<phi> \<psi> cpsPhiPsi cpsPsiPhi) = (
       let \<chi> = (case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>); R_0 = R_le_impl R \<phi> 0; S_0 = R_le_impl S \<chi> 0 in 
     do {
        check_left_linear_trs R;
        check_left_linear_trs S;
        check_same_set R_0 C <+? (\<lambda> lr. showsl_lit (STR ''0-labelled TRSs R is not identical to C because of rule '') o showsl_rule lr);
        check_same_set S_0 D <+? (\<lambda> lr. showsl_lit (STR ''0-labelled TRSs S is not identical to D because of rule '') o showsl_rule lr);
        check_decreasing ren R S \<phi> \<chi> Zero_Zero_Filter cpsPhiPsi;
        check_decreasing ren S R \<chi> \<phi> Zero_Zero_Filter cpsPsiPhi        
     })"

lemma check_compositional_pcp_rule_lab_comm: assumes "isOK(check_compositional_pcp_rule_lab_comm R S C D prf)" 
  and "commute (rstep (set C)) (rstep (set D))" 
shows "commute (rstep (set R)) (rstep (set S))" 
proof (cases "prf")
  case *: (PCP_Sequences_Com \<phi> \<psi> h1 h2)
  define \<chi> where "\<chi> = (case \<psi> of None \<Rightarrow> \<phi> | Some \<chi> \<Rightarrow> \<chi>)" 
  from assms * 
  have ll: "left_linear_trs (set R)" "left_linear_trs (set S)" 
    and decr: "isOK (check_decreasing ren R S \<phi> \<chi> Zero_Zero_Filter h1)" 
       "isOK (check_decreasing ren S R \<chi> \<phi> Zero_Zero_Filter h2)" 
    and R_0: "set C = R_le (set R) \<phi> 0" 
    and S_0: "set D = R_le (set S) \<chi> 0" 
    by (auto simp: \<chi>_def Let_def)
  show ?thesis using assms(2) R_0 S_0 by (intro compositional_rule_labeling_pcp_comm[OF ll 
        check_decreasing[OF decr(1)] check_decreasing[OF decr(2)]], auto)
qed

  
definition check_PCPS_com :: "('f :: showl, 'v) rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
  ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)cp_join_hints \<Rightarrow> showsl check" where
  "check_PCPS_com P R S C D hints = do {
     checker \<leftarrow> is_rsteps_conversion' D C hints <+?
       (\<lambda> err. showsl_lit (STR ''error in checking hints for proving that certains PCPS-elements are not in P\<newline>'') o err);
     check_allm (\<lambda> (t,s,u). if t = u \<or> (\<exists> lr \<in> set P.  instance_rule (s,t) lr) \<and> (\<exists> lr \<in> set P. instance_rule (s,u) lr)
         then succeed 
         else checker t u <+? (\<lambda> err. 
        (showsl_lit (STR ''P does not contain PCPS for crit pair '') 
         o showsl t o showsl_lit (STR '' <-||- '') o showsl s o showsl_lit (STR '' -root-> '') o showsl u
         o showsl_nl o err))) 
        [(t,s,u) . lr \<leftarrow> S, (_,t,s,u,_) \<leftarrow> parallel_critical_peaks_of_rule_impl ren R lr]}" 

lemma check_PCPS_comm: assumes "isOK(check_PCPS_com P R S C D hints)" 
  shows "rstep (PCPS_com ren (set R) (set S) (set C) (set D)) \<subseteq> rstep (set P)" 
proof -
  note ok = assms[unfolded check_PCPS_com_def, simplified]
  from ok obtain checker where checker: "is_rsteps_conversion' D C hints = return checker" 
    by force
  note ok = ok[unfolded checker, simplified]
  {
    fix lr E t s u rls
    assume "(E, t, s, u, rls) \<in> parallel_critical_peaks_of_rule ren (set R) lr" 
      "lr \<in> set S" 
    with ok have "t = u \<or> (\<exists>rl1\<in>set P. instance_rule (s, t) rl1) \<and> (\<exists>rl2 \<in> set P. instance_rule (s, u) rl2) \<or>
           isOK(checker t u)" by auto 
    with is_rsteps_conversion'[OF checker] 
    have "(t, u) \<in> conv'' (rstep (set D)) (rstep (set C)) \<or> (\<exists>rl1\<in>set P. instance_rule (s, t) rl1) \<and> (\<exists>rl2\<in>set P. instance_rule (s, u) rl2)" by auto
  } note check = this
  show ?thesis 
    unfolding rstep_subset_characterization
  proof (intro allI impI)
    fix l r
    assume "(l,r) \<in> PCPS_com ren (set R) (set S) (set C) (set D)" 
    from this[unfolded PCPS_com_def] check obtain lr' where 
      mem: "lr'\<in>set P" and inst: "instance_rule (l,r) lr'" by blast
    obtain l' r' where lr': "lr' = (l',r')" by force
    from inst[unfolded instance_rule_def lr'] obtain \<sigma> where
      id: "l = l' \<cdot> \<sigma>" "r = r' \<cdot> \<sigma>" by auto
    show "\<exists>l' r' C \<sigma>. (l', r') \<in> set P \<and> l = C\<langle>l' \<cdot> \<sigma>\<rangle> \<and> r = C\<langle>r' \<cdot> \<sigma>\<rangle>" 
      using mem unfolding id lr' by (intro exI[of _ Hole] exI, auto)
  qed
qed


definition check_compositional_PCPS :: "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> 
  ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_PCPS R C P hintsP hintsPCP = do {
     check_left_linear_trs R;
     check_subseteq C R <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') o showsl_rule lr o 
       showsl_lit (STR '' of C in R''));
     check_compositional_pcps_joinable ren R R hintsPCP;
     \<comment> \<open>check that P contains all rules of PCPS C R\<close>
     check_PCPS_com P R R C C hintsP
   } <+? (\<lambda> e. showsl_lit (STR ''problem in compositional parallel critical pair systems application\<newline>'') o e)" 

lemma check_compositional_PCPS: assumes ok: "isOK(check_compositional_PCPS R C P hintsP hintsPCP)" 
  and C: "CR (rstep (set C))" 
  and SN: "SN (relto (rstep (set P)) (rstep (set R)))" 
shows "CR (rstep (set R))" 
proof -
  note ok = ok[unfolded check_compositional_PCPS_def, simplified]
  have ll: "left_linear_trs (set R)" and sub: "set C \<subseteq> set R"
    and comp: "isOK (check_compositional_pcps_joinable ren R R hintsPCP)"
    using ok by auto
  show ?thesis
    apply (rule compositional_PCPS[OF ll C sub check_compositional_pcps_joinable[OF comp] _ refl])
    apply (rule SN_subset[OF SN relto_mono[OF _ subset_refl]])
    apply (unfold PCPS_is_PCPS_com)
    apply (rule check_PCPS_comm)
    using ok by auto
qed

definition check_compositional_PCPS_com :: "('f :: showl,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
  ('f,'v) cp_join_hints \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> ('f,'v) cp_join_hints \<Rightarrow> showsl check" where
  "check_compositional_PCPS_com R S C D P hintsP_RS hintsP_SR hintsRS hintsSR = do {
     check_left_linear_trs R;
     check_left_linear_trs S;
     check_subseteq C R <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') o showsl_rule lr o 
       showsl_lit (STR '' of C in R''));
     check_subseteq D S <+? (\<lambda> lr. showsl_lit (STR ''could not find rule '') o showsl_rule lr o 
       showsl_lit (STR '' of D in S''));
     check_compositional_pcps_joinable_generic ren R S S R hintsRS;
     check_compositional_pcps_joinable_generic ren S R R S hintsSR;
     \<comment> \<open>check that P contains all rules of PCPS w.r.t. R S and C D, in both directions\<close>
     check_PCPS_com P R S C D hintsP_RS;
     check_PCPS_com P S R D C hintsP_SR
   } <+? (\<lambda> e. showsl_lit (STR ''problem in compositional parallel critical pair systems application\<newline>'') o e)" 

lemma check_compositional_PCPS_com: assumes ok: "isOK(check_compositional_PCPS_com R S C D P hintsP_RS hintsP_SR hintsRS hintsSR)" 
  and com: "commute (rstep (set C)) (rstep (set D))" 
  and SN: "SN (relto (rstep (set P)) (rstep (set R \<union> set S)))" 
shows "commute (rstep (set R)) (rstep (set S))" 
proof -
  note ok = ok[unfolded check_compositional_PCPS_com_def, simplified]
  have ll: "left_linear_trs (set R)" "left_linear_trs (set S)" and sub: "set C \<subseteq> set R" "set D \<subseteq> set S" 
    and comp: "isOK (check_compositional_pcps_joinable_generic ren R S S R hintsRS)"
      "isOK (check_compositional_pcps_joinable_generic ren S R R S hintsSR)"
    using ok by auto
  show ?thesis
    apply (rule compositional_PCPS_com[OF ll sub _ _ refl com])
      apply (rule check_compositional_pcps_joinable_generic[OF comp(1)])
     apply (rule check_compositional_pcps_joinable_generic[OF comp(2)])
    apply (rule SN_subset[OF SN relto_mono[OF _ subset_refl]])
    apply (unfold rstep_union, rule Un_least; rule check_PCPS_comm)
    using ok by auto
qed

end
end