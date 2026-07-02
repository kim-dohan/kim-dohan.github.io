(*
Author:  Christina Kirk (Kohl) <christina.kirk@uibk.ac.at> (2023-2024)
License: LGPL (see file COPYING.LESSER)
*)
theory Okui_Criterion
imports
  Proof_Terms_Term_Rewriting.Redex_Patterns   
  TRS.Mgu_generic
  TRS.More_Abstract_Rewriting
begin

(*Avoid confusion with supremum of Lattices. '\<squnion>' is only used for join on proof terms in this file.*)
no_notation sup (infixl "\<squnion>" 65) 

text\<open>Only take redexes from A which have overlap with proof term B.\<close> 
definition get_overlapping_part :: "('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm \<Rightarrow> ('f, 'v) pterm option"
  where "get_overlapping_part A B \<equiv> 
    let As = filter (\<lambda> A'. measure_ov A' B \<noteq> 0) (single_steps A) in \<Squnion> As" 

locale ren =
  fixes ren :: "'v :: infinite renamingN" 
    and R :: "('f, 'v) trs"
begin

definition "rename_list ss = 
    map (\<lambda> (i, s). (map_vars_term ((rename_many' ren) i) s)) (zip [0 ..< length ss] ss)" 

definition "rename_redex_patterns redexes =
    map (\<lambda> (i, (\<alpha>, p)). ((map_vars_term ((rename_many' ren) i) (lhs \<alpha>)), p)) (zip [0 ..< length redexes] redexes)"

text\<open>Define simultaneous critical peak (A,B) as pair of proof terms. Requirements:
\<^item> first proof term (A) represents multistep 
\<^item> second proof term (B) represents single step
\<^item> all redexe patterns of A overlap with the redex pattern in B
\<^item> either the redex in B or one of the redexes in A are at the root
\<^item> there exists an mgu between all of the (renamed) lhss in A and the (renamed) lhs in B 
\<^item> the proof terms A and B are obtained from combining the mgu with the corresponding rule symbols 
\<close>
definition sim_cp where
  "sim_cp = { (A, B) | \<tau> rdp_A l \<beta> q A B As renamed_lhs_\<alpha>s. 
    A \<in> wf_pterm R \<and> B \<in> wf_pterm R \<and> 
    redex_patterns A = rdp_A \<and> redex_patterns B = [(\<beta>, q)] \<and> 
    renamed_lhs_\<alpha>s = rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A) \<and>
    get_overlapping_part A B = Some A \<and> 
    (q = [] \<or> snd (hd rdp_A) = []) \<and>     
    l = replace_at (hd renamed_lhs_\<alpha>s) q (map_vars_term (ren_l ren) (lhs \<beta>)) \<and>
    is_mgu \<tau> (set (map2 (\<lambda> lhs_\<alpha> p. (lhs_\<alpha>, l|_p)) renamed_lhs_\<alpha>s (map snd rdp_A))) \<and> 
    As = map (\<lambda>((\<alpha>i, pi), i). replace_at (to_pterm (l \<cdot> \<tau>)) pi (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))) (zip rdp_A [0..<length rdp_A]) \<and>
    join_list As = Some A \<and>
    B = replace_at (to_pterm (l \<cdot> \<tau>)) q (Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> (ren_l ren)) (var_rule \<beta>))) }"

lemma sim_cpI:
  assumes "A \<in> wf_pterm R" and "B \<in> wf_pterm R" 
    and "redex_patterns A = rdp_A" "redex_patterns B = [(\<beta>, q)]"
    and "renamed_lhs_\<alpha>s = rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A)"
    and "get_overlapping_part A B = Some A"
    and "l = replace_at (hd renamed_lhs_\<alpha>s) q (map_vars_term (ren_l ren) (lhs \<beta>))"
    and "q = [] \<or> snd (hd rdp_A) = []" 
    and "is_mgu \<tau> (set (map2 (\<lambda> lhs_\<alpha> p. (lhs_\<alpha>, l|_p)) renamed_lhs_\<alpha>s (map snd rdp_A)))"
    and "As = map (\<lambda>((\<alpha>i, pi), i). replace_at (to_pterm (l \<cdot> \<tau>)) pi (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))) (zip rdp_A [0..<length rdp_A])" 
    and "join_list As = Some A"
    and "B = replace_at (to_pterm (l \<cdot> \<tau>)) q (Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> (ren_l ren)) (var_rule \<beta>)))" 
  shows "(A, B) \<in> sim_cp" 
  using assms unfolding sim_cp_def mem_Collect_eq by blast

lemma sim_cp_A_not_empty:
  assumes "(A, B) \<in> sim_cp"
  shows "\<not> is_empty_step A"
proof-
  from assms obtain As s \<tau> rdp_A where "join_list As = Some A" and rdp:"rdp_A = redex_patterns A" and
    As:"As = map (\<lambda>((\<alpha>i, pi), i). replace_at s pi (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))) (zip rdp_A [0..<length rdp_A])"
    using sim_cp_def by auto 
  then show ?thesis
    by (metis (no_types, lifting) join_list.simps(1) length_nth_simps(1) list.simps(8) 
     option.distinct(1) redex_patterns_to_pterm source_empty_step upt_0 zip.simps(1)) 
qed

lemma rename_redex_patterns_eq_rename_list:
  "map fst (rename_redex_patterns rs) = rename_list (map (\<lambda> (\<alpha>, p). lhs \<alpha>) rs)" 
proof(induct rs rule:rev_induct)
  case Nil
  then show ?case unfolding rename_redex_patterns_def rename_list_def by simp
next
  case (snoc x xs)
  have *:"zip [0..<length (xs @ [x])] (xs @ [x]) = zip [0..<length xs] xs @ [(length xs, x)]" by simp 
  have 1:"map fst (rename_redex_patterns (xs @ [x])) = (map fst (rename_redex_patterns xs)) @ [map_vars_term (rename_many' ren (length xs)) (lhs (fst x))]"
    unfolding rename_redex_patterns_def * map_append list.map by (simp add: case_prod_beta)
  have *:"zip [0..<length (xs @ [x])] (map (\<lambda>(\<alpha>, p). lhs \<alpha>) (xs @ [x])) = zip [0..<length xs] (map (\<lambda>(\<alpha>, p). lhs \<alpha>) xs) @ [(length xs, lhs (fst x))]" 
    unfolding map_append list.map by (simp add: case_prod_beta) 
  have 2:"rename_list (map (\<lambda> (\<alpha>, p). lhs \<alpha>) (xs @ [x])) = rename_list (map (\<lambda> (\<alpha>, p). lhs \<alpha>) xs) @ [(map_vars_term (rename_many' ren (length xs)) (lhs (fst x)))]"
    unfolding rename_list_def length_map * unfolding map_append list.map by simp
  show ?case unfolding 1 2 snoc by simp
qed

lemma distinct_linear_renamed_vars:
  assumes "\<forall>s \<in> set ss. linear_term s" 
  shows "distinct (concat (map vars_term_list (rename_list ss)))"
  using assms proof(induct ss rule:rev_induct)
  case Nil
  then show ?case unfolding rename_list_def zip.simps list.map by simp
next
  case (snoc s ss)
  then have IH:"distinct (concat (map vars_term_list (rename_list ss)))"
    by simp
  let ?s_renamed="map_vars_term ((rename_many' ren) (length ss)) s"
  from snoc(2) have "linear_term s" by simp
  then have distinct_s:"distinct (vars_term_list ?s_renamed)"
    using renameN(3) by (metis distinct_map inj_map_vars_term_the_inv linear_term_distinct_vars vars_map_vars_term)
  have *:"zip [0..<length (ss @ [s])] (ss @ [s]) = zip [0..<length ss] ss @ [(length ss, s)]" by simp 
  {fix x assume "x \<in> set (concat (map vars_term_list (rename_list ss)))"
    then obtain i where "x \<in> set (map vars_term_list (map2 (\<lambda>i. map_vars_term (rename_many' ren i)) [0..<length ss] ss) ! i)" and i:"i < length ss" 
      unfolding rename_list_def set_concat by (smt (verit) UN_E in_set_idx length_map map_nth map_snd_zip) 
    then have "x \<in> set (vars_term_list (map_vars_term ((rename_many' ren) i) (ss!i)))"
      by simp
    with i have "x \<notin> vars_term ?s_renamed"
      using renameN(2) by (smt (verit) Collect_mem_eq Int_Collect dual_order.irrefl emptyE image_iff rangeI set_vars_term_list term.set_map(2))
  }
  then have "set (concat (map vars_term_list (rename_list ss))) \<inter> set (vars_term_list ?s_renamed) = {}"
    by auto 
  with distinct_s IH show ?case 
    unfolding rename_list_def * map_append by simp
qed

lemma disjoint_concat_renamed_vars:
  shows "set (concat (map vars_term_list (rename_list ss))) \<inter> set (vars_term_list (map_vars_term (rename_single ren) t)) = {}"
proof(induct ss rule:rev_induct)
  case Nil
  then show ?case unfolding rename_list_def by simp
next
  case (snoc s ss)
  {fix x assume "x \<in> set (concat (map vars_term_list (rename_list (ss@[s]))))"
    then obtain i where "x \<in> set (map vars_term_list (map2 (\<lambda>i. map_vars_term (rename_many' ren i)) [0..<Suc (length ss)] (ss@[s]))!i)" 
      and i:"i < Suc (length ss)" 
      unfolding rename_list_def set_concat by (smt (verit, best) UN_E in_set_idx length_append_singleton length_map map_nth map_snd_zip) 
    then have "x \<in> set (vars_term_list (map_vars_term ((rename_many' ren) i) ((ss@[s])!i)))"
      by (metis (no_types, lifting) add.left_neutral case_prod_conv length_append_singleton length_map map_nth map_snd_zip nth_map nth_upt nth_zip)
    then have "x \<notin> set (vars_term_list (map_vars_term (rename_single ren) t))"
      using renameN(1) by (smt (verit, best) disjoint_iff imageE rangeI set_vars_term_list term.set_map(2))
  }
  then show ?case by auto
qed

end

locale ren_wf_trs = ren + left_lin_wf_trs
begin

lemma sim_cp_co_init:
  assumes "(A, B) \<in> sim_cp"
  shows "source A = source B" 
proof-
  from assms obtain \<tau> rdp_A l \<beta> q As renamed_lhs_\<alpha>s 
    where ren_\<alpha>s:"renamed_lhs_\<alpha>s = rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A)" 
      and l:"l = (ctxt_of_pos_term q (hd renamed_lhs_\<alpha>s))\<langle>map_vars_term (rename_single ren) (lhs \<beta>)\<rangle>" 
      and mgu:"is_mgu \<tau> (set (map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s (map snd rdp_A)))"
      and As:"As = map2 (\<lambda>(\<alpha>i, pi) i. (ctxt_of_pos_term pi (to_pterm (l \<cdot> \<tau>)))\<langle>Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))\<rangle>)
          rdp_A [0..<length rdp_A]" 
      and A:"\<Squnion> As = Some A" 
      and B:"B = (ctxt_of_pos_term q (to_pterm (l \<cdot> \<tau>)))\<langle>Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> rename_single ren) (var_rule \<beta>))\<rangle>" 
      and B_wf:"B \<in> wf_pterm R" and rdp_B:"redex_patterns B = [(\<beta>, q)]" 
      and A_wf:"A \<in> wf_pterm R" and rdp_A:"redex_patterns A = rdp_A"
      and root:"q = [] \<or> snd (hd rdp_A) = []" 
      and overlap:"get_overlapping_part A B = Some A"
    unfolding sim_cp_def by blast
  have len:"length As = length rdp_A" 
    unfolding rdp_A As by simp
  have B_single:"B = ll_single_redex (source B) q \<beta>" 
    using single_steps_singleton[OF B_wf] rdp_B by simp
  moreover from rdp_B B_wf have "q \<in> poss (source B)" 
    using left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by fastforce 
  moreover from rdp_B B_wf have \<beta>:"to_rule \<beta> \<in> R"
    by (simp add: left_lin_no_var_lhs.redex_pattern_rule_symbol ll_no_var_lhs) 
  ultimately have possL_B:"possL B = {q @ q' |q'. q' \<in> fun_poss (lhs \<beta>)}"
    using single_redex_possL by fastforce 
  from assms As A have len:"length rdp_A > 0" 
    by force 
  then obtain \<alpha>0 p0 rdps where rdp_A':"rdp_A = (\<alpha>0, p0)#rdps"
    by (metis length_greater_0_conv list.collapse split_pairs)
  have ind:"[0..<length rdp_A] = 0 # map (\<lambda>i. (Suc i)) [0..<length rdps]"  
    unfolding rdp_A' length_Cons using map_upt_Suc[of id "length rdps"] by auto
  then have hd_ren_\<alpha>:"hd renamed_lhs_\<alpha>s = map_vars_term (rename_many' ren 0) (lhs \<alpha>0)" 
    unfolding ren_\<alpha>s rename_list_def length_map ind unfolding rdp_A' by simp 
  {fix i \<alpha>i pi assume i:"i < length rdp_A" and \<alpha>ipi:"rdp_A ! i = (\<alpha>i, pi)"
    then have Ai:"single_steps A ! i = ll_single_redex (source A) pi \<alpha>i" 
      unfolding rdp_A by simp
    moreover from rdp_A A_wf \<alpha>ipi i have "pi \<in> poss (source A)" 
      using left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs nth_mem by fastforce 
    moreover from rdp_B B_wf have \<alpha>i:"to_rule \<alpha>i \<in> R"
      using left_lin_no_var_lhs.redex_pattern_rule_symbol ll_no_var_lhs by (metis A_wf \<alpha>ipi i nth_mem rdp_A) 
    ultimately have possL_A:"possL (single_steps A ! i) = {pi @ p' |p'. p' \<in> fun_poss (lhs \<alpha>i)}" 
      using single_redex_possL by fastforce 
    have "measure_ov (single_steps A ! i) B \<noteq> 0" proof-
      let ?As="filter (\<lambda>A'. measure_ov A' B \<noteq> 0) (single_steps A)" 
      from overlap have "\<Squnion> ?As = Some A" 
        unfolding get_overlapping_part_def by simp
      then have "set (single_steps A) =  \<Union> (set (map (set \<circ> single_steps) ?As))"
        by (metis (no_types, lifting) A_wf filter_is_subset in_mono single_step_wf single_steps_join_list) 
      moreover have "\<Union> (set (map (set \<circ> single_steps) ?As)) = set ?As" proof-
        {fix Ai assume Ai:"Ai \<in> set ?As"
          from Ai have src:"source Ai = source A"
            by (metis A_wf filter_set member_filter source_single_step) 
          from Ai obtain \<alpha>i pi where Ai':"Ai = ll_single_redex (source A) pi \<alpha>i" and "(\<alpha>i, pi) \<in> set (redex_patterns A)"  
            by auto
          then have *:"redex_patterns Ai = [(\<alpha>i, pi)]" 
            using A_wf left_lin_no_var_lhs.redex_patterns_single left_lin_no_var_lhs.redex_pattern_rule_symbol 
              left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast 
          have "(set \<circ> single_steps) Ai = {Ai}"
            unfolding comp_apply * list.map case_prod_conv using Ai' src by simp
        }
        then show ?thesis unfolding set_map
          by (smt (verit, ccfv_threshold) Inf.INF_cong UN_singleton)
      qed
      ultimately have "single_steps A ! i \<in> set ?As" 
        using i by (metis (no_types, lifting) length_map nth_mem rdp_A) 
      then show ?thesis
        by simp 
    qed
    then have possL:"{pi @ p' |p'. p' \<in> fun_poss (lhs \<alpha>i)} \<inter> {q @ q' |q'. q' \<in> fun_poss (lhs \<beta>)} \<noteq> {}" 
      unfolding possL_A possL_B by force
    with possL_B possL_A consider "q \<le>\<^sub>p pi" | "pi <\<^sub>p q"
      by (smt (verit, ccfv_threshold) card_eq_0_iff disjoint_iff less_eq_pos_simps(1) mem_Collect_eq pos_cases pos_less_eq_append_not_parallel) 
    then have "(\<exists>q'. q@q' = pi \<and> q' \<in> fun_poss (lhs \<beta>)) \<or> (\<exists>p'. pi@p' = q \<and> p' \<in> fun_poss (lhs \<alpha>i))"
    proof(cases)
      case 1
      then obtain q' where q':"pi = q@q'"
        using prefix_pos_diff by metis
      have "is_Fun (lhs \<beta>)" 
        using \<beta> using no_var_lhs.no_var_lhs no_var_lhs_axioms by fastforce
      with possL have "q' \<in> fun_poss (lhs \<beta>)" 
        unfolding q' using fun_poss_append_poss' by fastforce
      with q' show ?thesis by simp
    next
      case 2
      then obtain p' where p':"q = pi@p'"
        using less_pos_def' by blast 
      have "is_Fun (lhs \<alpha>i)" 
        using \<alpha>i using no_var_lhs.no_var_lhs no_var_lhs_axioms by fastforce
      with possL have "p' \<in> fun_poss (lhs \<alpha>i)" 
        unfolding p' using fun_poss_append_poss' by fastforce
      with p' show ?thesis by simp
    qed
  }note poss_q_p=this
  have q:"q \<in> poss (lhs \<alpha>0)" proof-
    consider "q = []" | "p0 = []" 
      using root rdp_A' by fastforce
    then show ?thesis proof(cases)
      case 1
      then show ?thesis by simp
    next
      case 2
      have 0:"0 < length rdp_A" "rdp_A ! 0 = (\<alpha>0, p0)" 
        unfolding rdp_A' by simp_all
      consider "(\<exists>q'. q @ q' = [] \<and> q' \<in> fun_poss (lhs \<beta>))" | "(\<exists>p'. [] @ p' = q \<and> p' \<in> fun_poss (lhs \<alpha>0))"
        using poss_q_p[OF 0] unfolding 2 by auto
      then show ?thesis by(cases, simp_all add: fun_poss_imp_poss)
    qed
  qed
  {fix i assume i:"i < length rdp_A" 
    let ?\<alpha>i="fst (rdp_A ! i)" and ?pi="snd (rdp_A ! i)"
    have \<alpha>ipi:"(?\<alpha>i, ?pi) \<in> set rdp_A"
      using i by simp  
    from A_wf \<alpha>ipi have 1:"to_rule ?\<alpha>i \<in> R" 
      using rdp_A using left_lin_no_var_lhs.redex_pattern_rule_symbol ll_no_var_lhs by blast 
    have 2:"?pi \<in> poss l" proof(cases i)
      case 0
      then have 0:"?pi = p0"
        using rdp_A' by auto 
      consider "q = []" | "p0 = []"
        using rdp_A' root by fastforce 
      then show ?thesis proof(cases)
        case 1
        from poss_q_p[OF i, unfolded 1] consider "p0 = []" | "p0 \<in> fun_poss (lhs \<beta>)"
          by (metis "0" Nil_is_append_conv append_self_conv2 prod.collapse)   
        then show ?thesis by(cases, simp_all add: 0 1 l fun_poss_imp_poss)
      qed (simp add: 0)
    next
      case (Suc n)
      then have "q <\<^sub>p ?pi" proof-
        consider (p0_less_pi) "p0 <\<^sub>p ?pi" | (p0_par) "p0 \<bottom> ?pi" 
          using left_lin_no_var_lhs.redex_patterns_order[OF ll_no_var_lhs] A_wf Suc i
          by (metis nth_Cons_0 parallel_pos_sym pos_cases prod.collapse rdp_A rdp_A' zero_less_Suc)
        note cases1=this
        from poss_q_p[of 0, unfolded rdp_A'] consider (q_less) "q \<le>\<^sub>p p0" | (p0_less_q) "\<exists>p'. p0@p' = q \<and> p' \<in> fun_poss (lhs \<alpha>0)"
          by force
        note cases2=this
        from poss_q_p[OF i] consider "q <\<^sub>p ?pi" | (pi_less_q) "?pi \<le>\<^sub>p q"
          by (metis less_eq_pos_simps(1) order_pos.less_le prod.collapse)
        note cases3=this
        from cases3 show ?thesis proof(cases)
          case pi_less_q
          from cases1 show ?thesis proof(cases)
            case p0_less_pi
            with cases2 show ?thesis proof(cases)
              case p0_less_q
              then obtain p' where p':"p0@p' = q" "p' \<in> fun_poss (lhs \<alpha>0)" by auto
              from p0_less_pi obtain p'' where "p0@p'' = ?pi" "p'' \<notin> fun_poss (lhs \<alpha>0)"  
                using redex_patterns_below[OF A_wf]
                by (metis \<alpha>ipi len less_pos_def' nth_Cons_0 nth_mem rdp_A rdp_A')  
              with p' pi_less_q show ?thesis
                by (metis fun_poss_append_poss' less_eq_pos_simps(2) prefix_pos_diff)
            qed simp
          next
            case p0_par
            with cases2 show ?thesis proof(cases)
              case q_less
              with p0_par pi_less_q show ?thesis
                using order_pos.order.trans parallel_pos by blast
            next
              case p0_less_q
              with p0_par show ?thesis
                using rdp_A' root by force 
            qed
          qed
        qed simp
      qed
      with poss_q_p[OF i] obtain q' where "q @ q' = ?pi" and "q' \<in> fun_poss (lhs \<beta>)"
        by (metis less_pos_simps(5) prod.collapse) 
      then show ?thesis unfolding l hd_ren_\<alpha> using q
        by (metis fun_poss_imp_poss hole_pos_ctxt_of_pos_term hole_pos_poss poss_append_poss poss_map_vars_term subt_at_hole_pos)
    qed
    note 1 and 2
  }note rdp_i=this
  {fix Ai assume "Ai \<in> set As" 
    then obtain i where i:"i < length As" and Ai:"Ai = As ! i"
      by (meson in_set_idx)
    then have i:"i < length rdp_A" 
      unfolding As by auto
    then obtain \<alpha>i pi where \<alpha>ipi:"rdp_A ! i = (\<alpha>i, pi)"
      by fastforce 
    then have pi:"pi \<in> poss (l \<cdot> \<tau>)" and \<alpha>i:"to_rule \<alpha>i \<in> R"
      using rdp_i i len nth_mem by fastforce+
    from i have "i < length (zip rdp_A [0..<length rdp_A])" by auto
    moreover then have "zip rdp_A [0..<length rdp_A] ! i = ((\<alpha>i, pi), i)"
      by (simp add: \<alpha>ipi)
    ultimately have Ai':"Ai = (ctxt_of_pos_term pi (to_pterm (l \<cdot> \<tau>)))\<langle>Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))\<rangle>"
      unfolding As Ai by simp
    have "Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))) \<in> wf_pterm R" 
      using to_pterm_wf_pterm \<alpha>i by (simp add: wf_pterm.intros(3)) 
    then have "Ai \<in> wf_pterm R"
      unfolding Ai' using ctxt_wf_pterm[OF to_pterm_wf_pterm[of "(l \<cdot> \<tau>)"] p_in_poss_to_pterm[OF pi]] by simp 
  }note as_wf=this
  have src_A:"source A = l \<cdot> \<tau>" proof-
    from As obtain A0 As' where As:"As = A0 # As'" 
      and A0:"A0 = (ctxt_of_pos_term p0 (to_pterm (l \<cdot> \<tau>)))\<langle>Prule \<alpha>0 (map (to_pterm \<circ> \<tau>) (map (rename_many' ren 0) (var_rule \<alpha>0)))\<rangle>"
      unfolding ind unfolding rdp_A' by simp
    have p0:"p0 \<in> poss l"
      using rdp_A' rdp_i(2) by force 
    let ?es="set (map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s (map snd rdp_A))"
    have "(map_vars_term (rename_many' ren 0) (lhs \<alpha>0), l |_ p0) \<in> ?es" 
      unfolding ren_\<alpha>s length_map rename_list_def ind unfolding rdp_A' by simp
    moreover have "\<tau> \<in> unifiers ?es" 
      using mgu is_mgu_def by blast 
    ultimately have "l |_ p0 \<cdot> \<tau> = map_vars_term (rename_many' ren 0) (lhs \<alpha>0) \<cdot> \<tau>" 
      by fastforce
    then have "l \<cdot> \<tau> |_ p0 = lhs \<alpha>0 \<cdot> \<langle>map (\<tau> \<circ> rename_many' ren 0) (var_rule \<alpha>0)\<rangle>\<^sub>\<alpha>0"
      using p0 by (metis apply_subst_map_vars_term empty_pos_in_poss lhs_subst_var_rule subt_at.simps(1) subt_at_subst vars_term_subt_at) 
    then have "source A0 = l \<cdot> \<tau>" 
      unfolding A0 using p0 by (metis (no_types, lifting) context_source list.map_comp poss_imp_subst_poss replace_at_ident 
          source.simps(2) source.simps(3) source_to_pterm term.inject(2) to_pterm.simps(2) to_pterm_ctxt_of_pos_apply_term) 
    then show ?thesis 
      using left_lin_no_var_lhs.source_join_list[OF ll_no_var_lhs] A as_wf As by simp
  qed
  have src_B:"source B = l \<cdot> \<tau>" proof-
    from q have q2:"q \<in> poss l" 
      unfolding l by (metis hd_ren_\<alpha> hole_pos_ctxt_of_pos_term hole_pos_poss poss_map_vars_term) 
    have "l \<cdot> \<tau> |_ q = map_vars_term (rename_single ren) (lhs \<beta>) \<cdot> \<tau>" 
      unfolding l subst_apply_term_ctxt_apply_distrib
      by (metis hd_ren_\<alpha> hole_pos_ctxt_of_pos_term hole_pos_subst poss_map_vars_term q subt_at_hole_pos)
    then have "l \<cdot> \<tau> |_ q = lhs \<beta> \<cdot> \<langle>map (\<tau> \<circ> rename_single ren) (var_rule \<beta>)\<rangle>\<^sub>\<beta>"
      by (smt (verit, ccfv_SIG) comp_def eval_eq_map_vars eval_term.simps(1) lhs_subst_var_rule vars_term_poss_subt_at vars_term_subt_at) 
    then have "source (Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> rename_single ren) (var_rule \<beta>))) = l \<cdot> \<tau> |_ q"
      unfolding source.simps map_map comp_apply source_to_pterm by simp
    then show ?thesis unfolding B using q2
      by (simp add: replace_at_ident source_to_pterm_ctxt to_pterm_ctxt_at_pos)
  qed
  from src_A src_B show ?thesis by simp
qed

end

hide_const (open) FuncSet.compose

locale tau =
  fixes ss :: "('f, 'v) term list" and t :: "('f, 'v) term"
    and ps :: "pos list" 
  assumes l:"length ss = length ps"
    and lin_t:"linear_term t" and lin_s:"\<forall>s \<in> set ss. linear_term s"
    and poss:"\<forall>p \<in> set ps. p \<in> poss t" 
    and disj:"\<forall>s \<in> set ss. vars_term s \<inter> vars_term t = {}" "\<forall>i j. i < j \<and> j < length ss \<longrightarrow> vars_term (ss!i) \<inter> vars_term (ss!j) = {}" 
begin

definition "\<tau>s = (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)"

definition "\<tau> = compose (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)" 

(*The slightly awkward introduction of \<tau>' is used in one of the lemmas for Okui's theorem. 
For more explanation see the comment for lemma \<sigma>_\<tau>'_y below.*)
lemma apply_tau_t_var: 
  assumes tau:"\<tau>' = compose (drop k (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps))"
    and k:"k \<le> length ss"
    and r:"r \<in> var_poss t" "t|_r = Var x" 
  shows "\<tau>' x = Var x \<or> (\<exists>i r'. i < length ss \<and> ps!i @ r' = r \<and> r' \<in> poss (ss!i) \<and> \<tau>' x = ss!i|_r')" 
proof-
  from r have x:"x \<in> vars_term t"
    by (metis vars_term_var_poss_iff) 
  {assume tau_x:"\<tau>' x \<noteq> Var x" 
    from assms(2) l have k:"k \<le> length (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss ps)" by simp
    let ?\<tau>s="drop k (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)"
    obtain i where i:"i < length ?\<tau>s" "\<forall>j < i. (?\<tau>s!j) x = Var x" "(?\<tau>s!i) x \<noteq> Var x"  
      using compose_exists_subst[OF tau_x[unfolded tau]] by blast 
    then have ik:"i + k < length (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)" by auto
    let ?\<tau>1="compose (take i ?\<tau>s)"
    let ?\<tau>2="compose (drop (i+1) ?\<tau>s)" 
    have tau_decomp:"\<tau>' = compose [?\<tau>1, ?\<tau>s!i, ?\<tau>2]" 
      using i(1) unfolding tau by (metis (no_types, lifting) Cons_nth_drop_Suc Suc_eq_plus1 append_self_conv append_take_drop_id compose_append compose_simps(3)) 
    from disj have 1:"vars_term (ss ! (i+k)) \<inter> vars_term (t |_ ps ! (i+k)) = {}"
      by (metis (no_types, lifting) Int_left_commute ik inf.orderE inf_bot_right length_map length_zip min_less_iff_conj nth_mem poss vars_term_subt_at)
    from lin_s i(1) have 2:"linear_term (ss ! (i+k))" by simp
    from lin_t i(1) l poss have 3:"linear_term (t|_(ps!(i+k)))" by (simp add: subt_at_linear)
    from i(1) have drop_k:"drop k (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss ps) ! i = (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss ps) ! (i+k)"
      by (metis (no_types, lifting) Cons_nth_drop_Suc drop_drop nth_via_drop) 
    from x disj i(1) poss have "x \<notin> vars_term (ss!(i+k))" by auto
    then obtain u where u:"(?\<tau>s!i) x = u" "(x,u) \<in> set (right_substs (ss!(i+k)) (t|_(ps!(i+k))))" 
      using i(3) ik linear_unifier_obtain_binding[OF 1 2 3] unfolding drop_k by auto  
    obtain q where q:"q \<in> poss (ss!(i+k))" "q \<in> poss (t |_ ps ! (i+k))" "t |_ ps ! (i+k) |_ q = Var x" 
      and tau_i: "(?\<tau>s!i) x = (ss!(i+k))|_q"
      using right_substs_imp_props[OF u(2)] using fun_poss_imp_poss u(1) by blast
    from i(2) have tau_1:"?\<tau>1 x = Var x" using compose_exists_subst i(1) by force  
    (*Show that ss!i_q is not affected by any of the taus afterwards*)
    have "(ss!(i+k))|_q \<cdot> ?\<tau>2 = (ss!(i+k))|_q" proof-
      {fix \<tau>j assume tau_j:"\<tau>j \<in> set (drop (i+1) ?\<tau>s)" 
        then have "i+1 < length ?\<tau>s" using not_less_less_Suc_eq by fastforce  
        with tau_j obtain j where j:"j < length ?\<tau>s" "i < j" "\<tau>j = ?\<tau>s!j" 
          by (smt (verit) Suc_eq_plus1 add.commute drop_eq_nths in_set_conv_nth length_drop lessI less_diff_conv less_imp_le_nat nth_drop trans_less_add2) 
        then have jk':"j + k < length (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss ps)" by auto
        then have jk:"k + j < length (zip ss ps)" by auto
        then have zip:"(zip ss ps)!(j+k) = (ss!(j+k), ps!(j+k))" by simp
        then have tau_j_eq:"\<tau>j = linear_unifier (ss!(j+k)) (t|_(ps!(j+k)))"
          unfolding j(3) nth_drop[OF k] nth_map[OF jk] by (simp add: add.commute)
        from j disj(2) have "vars_term (ss!(i+k)) \<inter> vars_term (ss!(j+k)) = {}" by simp 
        then have "set (map fst (left_substs (ss!(j+k)) (t|_(ps!(j+k))))) \<inter> vars_term (ss!(i+k)) = {}" 
          using map_fst_left_substs by fastforce
        moreover have "set (map fst (right_substs (ss!(j+k)) (t|_(ps!(j+k))))) \<inter> vars_term (ss!(i+k)) = {}" 
          using map_fst_right_substs disj(1) j jk' l nth_mem poss vars_term_subt_at by fastforce
        ultimately have "(ss!(i+k)) \<cdot> \<tau>j = ss!(i+k)" unfolding tau_j_eq subst_of_append subst_compose
          by (smt (verit, del_insts) disjoint_iff eval_same_vars_cong eval_term.simps(1) not_elem_subst_of subst_apply_term_empty)
      }
      then show ?thesis
        by (smt (verit, ccfv_threshold) compose_exists_subst eval_same_vars eval_term.simps(1) nth_mem q(1) subst_apply_term_empty subt_at_subst vars_term_poss_subt_at)
    qed
    then have "\<tau>' x = (ss!(i+k))|_q" 
      unfolding tau_decomp compose_simps subst_compose tau_1 eval_term.simps tau_i by force 
    moreover from q lin_t r have "ps!(i+k) @ q = r"
      by (metis (no_types, lifting) ik l length_map length_zip linear_term_unique_vars min.idem nth_mem pos_append_poss poss subt_at_append var_poss_imp_poss)
    ultimately have "\<exists>i r'. i < length ss \<and> ps!i @ r' = r \<and> r' \<in> poss (ss!i) \<and> \<tau>' x = ss!i|_r'"
      using ik q by auto
  }
  then show ?thesis by blast 
qed

lemma apply_tau_t_var': 
  assumes r:"r \<in> var_poss t" "t|_r = Var x" 
  shows "\<tau> x = Var x \<or> (\<exists>i r'. i < length ss \<and> ps!i @ r' = r \<and> r' \<in> poss (ss!i) \<and> \<tau> x = ss!i|_r')" 
proof-
  have *:"\<tau> = compose (drop 0 (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps))"
    by (simp add: \<tau>_def) 
  show ?thesis using apply_tau_t_var[OF * le0 r] by simp 
qed

lemma apply_tau_ss_var: 
  assumes i:"i < length ss"
    and x:"x \<in> vars_term (ss!i)" and r:"r \<in> var_poss (ss!i)" "(ss!i)|_r = Var x" 
  shows "\<tau> x = Var x \<or> (r \<in> poss (t|_(ps!i)) \<and> \<tau> x = t|_(ps!i) |_ r \<cdot> compose (drop (Suc i) (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)))" 
proof-
  {assume tau_x:"\<tau> x \<noteq> Var x" 
    from i l have i:"i < length (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss ps)" by simp
    let ?\<tau>s="map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps"
    let ?\<tau>1="compose (take i ?\<tau>s)"
    let ?\<tau>2="compose (drop (Suc i) ?\<tau>s)" 
    have tau_decomp:"\<tau> = compose [?\<tau>1, ?\<tau>s!i, ?\<tau>2]" 
      using i by (metis (mono_tags, lifting) Cons_nth_drop_Suc \<tau>_def append_take_drop_id compose_append compose_simps(1) compose_simps(3) subst_monoid_mult.mult_1_right) 
    have "\<forall>j < length ss. j \<noteq> i \<longrightarrow> (?\<tau>s!j) x = Var x" proof-
      {fix j assume j:"j < length ss" "j \<noteq> i" 
        from disj(2) j i x have "x \<notin> vars_term (ss!j)"
          using nat_neq_iff by auto
        moreover from disj(1) i x poss have "x \<notin> vars_term (t|_(ps!j))"
          by (metis (mono_tags, lifting) assms(1) disjoint_iff in_mono j(1) l nth_mem vars_term_subt_at)
        moreover from j i have "?\<tau>s!j = linear_unifier (ss!j) (t|_(ps!j))" by (simp add: l) 
        ultimately have "(?\<tau>s!j) x = Var x"
          by (smt (verit) add_lessD1 assms(1) canonically_ordered_monoid_add_class.lessE disj(1) inf.absorb_iff1 inf_bot_right inf_left_commute 
              j l lin_s lin_t linear_unifier_obtain_binding nth_mem poss subt_at_linear vars_term_subt_at) 
      }
      then show ?thesis by simp
    qed note tau_i_x=this
    then have tau1_x:"?\<tau>1 x = Var x"
      using i by (smt (verit, best) compose_exists_subst length_map length_take length_zip min_less_iff_conj nth_take) 
    from tau_i_x i have "\<forall>j < length (drop (Suc i) ?\<tau>s). (?\<tau>s!(j + Suc i)) x = Var x" by simp
    then have tau2_x:"?\<tau>2 x = Var x" 
      using i by (metis (no_types, lifting) Suc_leI add.commute compose_exists_subst nth_drop)  
    from disj have 1:"vars_term (ss ! i) \<inter> vars_term (t |_ ps ! i) = {}"
      by (metis (no_types, lifting) Int_left_commute i inf.orderE inf_bot_right length_map length_zip min_less_iff_conj nth_mem poss vars_term_subt_at)
    from lin_s i have 2:"linear_term (ss ! i)" by simp
    from lin_t i l poss have 3:"linear_term (t|_(ps!i))" by (simp add: subt_at_linear)
    from tau_x tau1_x tau2_x have "(?\<tau>s!i) x \<noteq> Var x"
      by (metis (no_types, lifting) \<tau>_def compose_exists_subst length_map length_zip min_less_iff_conj tau_i_x) 
    then obtain u where tau_i:"(?\<tau>s!i) x = u" and xu:"(x,u) \<in> set (left_substs (ss!i) (t|_(ps!i)))" 
      using i linear_unifier_obtain_binding[OF 1 2 3] x 1 by auto
    then have r:"r \<in> poss (t|_(ps!i))" and u:"u = t|_(ps!i) |_r " 
      using left_substs_imp_props[OF xu] r lin_s i linear_term_unique_vars var_poss_imp_poss by fastforce+
    from tau1_x have "\<tau> x = (?\<tau>s!i) x \<cdot> ?\<tau>2" 
      unfolding tau_decomp compose_simps by (simp add: subst_compose)  
    then have "r \<in> poss (t|_(ps!i)) \<and> \<tau> x = t|_(ps!i) |_ r \<cdot> ?\<tau>2" 
      unfolding tau_i u using assms(1) l poss r by auto 
  }
  then show ?thesis by blast 
qed

lemma apply_tau_var: 
  assumes "\<forall>i < length ss. x \<notin> vars_term (ss!i)" and "x \<notin> vars_term t"
  shows "\<tau> x = Var x" 
proof-
  from assms(1) l poss disj have "(compose (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)) x = Var x" 
  proof(induct "length ss" arbitrary:ss ps)
    case (Suc n)
    then obtain s ss' where ss:"ss = s#ss'"
      by (metis length_Suc_conv) 
    from Suc obtain p ps' where ps:"ps = p#ps'"
      by (metis length_Suc_conv) 
    let ?\<tau>="compose (map2 (\<lambda>x y. linear_unifier x (t |_ y)) ss' ps')" 
    have tau:"(compose (map2 (\<lambda> s p. linear_unifier s (t|_p)) ss ps)) = linear_unifier s (t|_p) \<circ>\<^sub>s ?\<tau>" 
      unfolding ss ps by simp
    from Suc(1)[of ss' ps'] have IH:"?\<tau> x = Var x"
      by (smt (verit, del_insts) Suc Suc_leI le_imp_less_Suc length_Suc_conv list.inject list.set_intros(2) nth_Cons_Suc ps ss) 
    have "(linear_unifier s (t|_p)) x = Var x" proof-
      from Suc(3) have "x \<notin> vars_term s" unfolding ss by auto
      moreover have "x \<notin> (vars_term (t|_p))" 
        using assms(2) using Suc.prems(3) ps vars_ctxt_pos_term by auto 
      ultimately show ?thesis 
        using linear_unifier_id by metis 
    qed
    with IH show ?case unfolding tau
      by (simp add: subst_compose)
  qed simp
  then show ?thesis
    using \<tau>_def by presburger 
qed

lemma var_at_t_tau:
  assumes "t \<cdot> \<tau> |_ r = Var x" "r \<in> poss (t \<cdot> \<tau>)" 
  shows "(r \<in> poss t \<and> t |_ r = Var x) \<or> 
  (\<exists>i r1 r2 y. r = ps!i@r1@r2 \<and> r1 \<in> poss (ss ! i) \<and> r2 \<in> poss (ss!i |_ r1) \<and> ps!i @ r1 \<in> poss t \<and> 
    t |_ (ps!i@r1) = Var y \<and> \<tau> y |_ r2 = Var x \<and> \<tau> y = ss!i |_ r1 \<and> i < length ss)" 
proof(cases "r \<in> poss t \<and> t |_ r = Var x")
  case False
  with assms obtain r1 r2 y where r:"r = r1@r2" and r1:"r1 \<in> poss t" "t |_ r1 = Var y" and r2:"r2 \<in> poss (\<tau> y)" "\<tau> y |_ r2 = Var x"
    by (smt (verit, best) is_FunE poss_subst_choice subst_apply_eq_Var subt_at_subst term.distinct(1))
  then obtain i r' where "i < length ss" "ps ! i @ r' = r1" "r' \<in> poss (ss ! i)" "\<tau> y = ss ! i |_ r'" 
    using apply_tau_t_var' by (smt (verit, ccfv_SIG) False append.right_neutral poss_append_poss subt_at.simps(1) var_pos_maximal var_poss_iff)
  then show ?thesis
    by (metis append_assoc r r1 r2)
qed simp

lemma tau_is_unifier:
  assumes ts:"unify (zip ss (map (\<lambda>p. t|_p) ps)) [] = Some ts" 
    and \<tau>':"subst_of ts = \<tau>'"
    and "\<And>i j r. i < j \<Longrightarrow> j < length ps \<Longrightarrow> \<not> (ps ! i @ r) \<bottom> ps ! j \<Longrightarrow> r \<in> var_poss (t|_(ps!i)) \<Longrightarrow> r \<notin> fun_poss (ss!i)" 
  shows "\<tau> = \<tau>'"
proof-
  have \<tau>_alt:"\<tau> = compose (subst_of [] # map2 linear_unifier ss (map ((|_) t) ps))"
    unfolding \<tau>_def by (simp add: map_zip_map2)
  have lin:"\<forall>t\<in>set (map fst (zip ss (map ((|_) t) ps))) \<union> set (map snd (zip ss (map ((|_) t) ps))). linear_term t" 
    using lin_t lin_s l poss subt_at_linear by fastforce 
  {fix i j \<sigma>i assume i:"i < j" and j:"j < length (zip ss (map ((|_) t) ps))" 
      and "\<sigma>i = linear_unifier (fst (zip ss (map ((|_) t) ps) ! i)) (snd (zip ss (map ((|_) t) ps) ! i))"
    then have \<sigma>i:"\<sigma>i = linear_unifier (ss ! i) (t |_ (ps ! i))"
      by auto 
    obtain ssj tj where ssj_tj:"zip ss (map ((|_) t) ps) ! j = (ssj, tj)"
      by force 
    have vars_subst_\<sigma>i:"vars_subst \<sigma>i \<subseteq> vars_term (ss ! i) \<union> vars_term (t |_ (ps!i))"
      unfolding \<sigma>i using vars_subst_linear_unifier by simp
    have "ssj \<cdot> \<sigma>i = ssj" proof-
      from vars_subst_\<sigma>i have "vars_term ssj \<inter> vars_subst \<sigma>i = {}" 
        using disj i j ssj_tj  by (smt (verit, ccfv_threshold) Un_iff disjoint_iff dual_order.strict_trans 
            fst_conv in_mono l length_zip min_less_iff_conj nth_mem nth_zip poss vars_term_subt_at)
      then show ?thesis
        by (simp add: boolean_algebra.conj_disj_distrib subst_apply_term_ident vars_subst_def)
    qed
    moreover have "tj \<cdot> \<sigma>i = tj" proof-
      {fix y assume y:"y \<in> vars_term tj" "\<sigma>i y \<noteq> Var y" 
        then have "y \<in> vars_subst \<sigma>i"
          by (metis UnCI notin_subst_domain_imp_Var vars_subst_def)
        with vars_subst_\<sigma>i have y_in_ti:"y \<in> vars_term (t |_ (ps!i))" 
          using ssj_tj disj(1) i j l nth_mem poss vars_term_subt_at y(1) by fastforce
        have vars_term_disj:"vars_term (ss ! i) \<inter> vars_term (t |_ (ps ! i)) = {}" 
          using i disj(1) j poss vars_term_subt_at by fastforce 
        from i j have lin_ssi:"linear_term (ss ! i)"
          using lin_s by auto 
        from i j have lin_ti:"linear_term (t |_ ps ! i)"
          by (simp add: lin_t poss subt_at_linear) 
        obtain u where u:"(y, u) \<in> set (right_substs (ss ! i) (t |_ (ps ! i)))" "\<sigma>i y = u"
          using linear_unifier_obtain_binding[OF vars_term_disj lin_ssi lin_ti] y(2)[unfolded \<sigma>i] y_in_ti \<sigma>i vars_term_disj by force  
        then obtain r where r:"r \<in> fun_poss (ss ! i)" "(ss ! i) |_ r = u" "r \<in> poss (t |_ ps ! i)" "(t |_ ps ! i) |_ r = Var y"   
          using right_substs_imp_props by metis
        {assume "(ps ! i @ r) \<bottom> ps ! j" 
          then have False using lin_t r(3,4) y_in_ti
            by (smt (verit, best) disjoint_iff dual_order.strict_trans i j l length_map linear_subterms_disjoint_vars map_nth_conv map_snd_zip nth_mem 
                pos_append_poss poss snd_conv ssj_tj subt_at_append term.set_intros(3) vars_term_poss_subt_at vars_term_subt_at y(1)) 
        }
        then have not_orth:"\<not> (ps ! i @ r) \<bottom> ps ! j" 
          by fastforce 
        from j have j:"j < length ps"
          by simp 
        from assms(3)[OF i j not_orth] r have False
          using var_poss_iff by blast
      }
      then show ?thesis
        using term_subst_eq by force
    qed
    ultimately have "fst (zip ss (map ((|_) t) ps) ! j) \<cdot> \<sigma>i = fst (zip ss (map ((|_) t) ps) ! j) \<and>
                     snd (zip ss (map ((|_) t) ps) ! j) \<cdot> \<sigma>i = snd (zip ss (map ((|_) t) ps) ! j)"
      using ssj_tj by simp
  } moreover 
  {fix i assume i:"i < length (zip ss (map ((|_) t) ps))" 
    then have "vars_term (fst (zip ss (map ((|_) t) ps) ! i)) = vars_term (ss ! i)"
      by simp 
    moreover have "vars_term (snd (zip ss (map ((|_) t) ps) ! i)) \<subseteq> vars_term t"
      by (metis i l length_zip min_less_iff_conj nth_map nth_mem nth_zip snd_conv tau.poss tau_axioms vars_term_subt_at) 
    ultimately have "vars_term (fst (zip ss (map ((|_) t) ps) ! i)) \<inter> vars_term (snd (zip ss (map ((|_) t) ps) ! i)) = {}" 
      using disj(1) i by force
  }
  ultimately show ?thesis 
    using unify_linear_terms[OF ts \<tau>_alt[symmetric] lin] \<tau>' by presburger  
qed

lemma ss_i_\<tau>_eq_t_\<tau>:
  assumes "\<exists>ts. unify (zip ss (map (\<lambda>p. t|_p) ps)) [] = Some ts"  
  and i:"i < length ss"
  and "\<And>i j r. i < j \<Longrightarrow> j < length ps \<Longrightarrow> \<not> (ps ! i @ r) \<bottom> ps ! j \<Longrightarrow> r \<in> var_poss (t|_(ps!i)) \<Longrightarrow> r \<notin> fun_poss (ss!i)" 
  shows "ss!i \<cdot> \<tau> = t |_ (ps!i) \<cdot> \<tau>"
proof-
  from assms(1) obtain ts where ts:"unify (zip ss (map (\<lambda>p. t|_p) ps)) [] = Some ts"
    by force 
  let ?es="zip ss (map (\<lambda>p. t|_p) ps)"
  have ss_i:"ss ! i = fst (?es ! i)"
    using i l by auto 
  have t_at_pi:"t |_ (ps ! i) = snd (?es ! i)"
    using i l by force 
  obtain \<tau>' where \<tau>':"subst_of ts = \<tau>'"
    by simp 
  then have "is_imgu \<tau>' (set ?es)" 
    using unify_sound[OF ts] by simp
  then have *:"ss!i \<cdot> \<tau>' = t |_ (ps!i) \<cdot> \<tau>'" 
    unfolding ss_i t_at_pi by (metis i in_unifiersE is_imgu_def l length_map length_zip min_less_iff_conj nth_mem) 
  from tau_is_unifier[OF ts \<tau>' assms(3)] have "\<tau> = \<tau>'" .
  with * show ?thesis
    by auto 
qed

lemma linear_term_t_tau:
  shows "linear_term (t \<cdot> \<tau>)" 
proof- 
  {fix r1 r2 x assume r1:"r1 \<in> poss (t \<cdot> \<tau>)" "t \<cdot> \<tau> |_ r1 = Var x" 
                  and r2:"r2 \<in> poss (t \<cdot> \<tau>)" "t \<cdot> \<tau> |_ r2 = Var x"
                  and r1r2:"r1 \<noteq> r2" 
  have False proof(cases "r1 \<in> poss t \<and> t|_r1 = Var x")
    case True
    then have x:"x \<in> vars_term t"
      by (metis var_poss_iff vars_term_var_poss_iff)
    show ?thesis proof(cases "r2 \<in> poss t \<and> t|_r2 = Var x")
      case True
      with \<open>r1 \<in> poss t \<and> t|_r1 = Var x\<close> show ?thesis 
        using r1r2 lin_t by (meson linear_term_unique_vars)
    next 
      case False
      then obtain i p1 p2 y where "p1 \<in> poss (ss ! i)" "p2 \<in> poss (ss ! i |_ p1)" "\<tau> y |_ p2 = Var x" 
        "\<tau> y = ss ! i |_ p1" and i:"i < length ss"
        using var_at_t_tau[OF r2(2) r2(1)] by auto
      then have "x \<in> vars_term (ss!i)"
        by (metis (no_types, lifting) subsetD term.set_intros(3) vars_term_subt_at) 
      with x show ?thesis 
        using disj(1) i by (meson disjoint_iff nth_mem)
    qed
  next
    case False
    then obtain i p1 p2 y where p1:"p1 \<in> poss (ss ! i)" "t |_ (ps ! i @ p1) = Var y" "ps!i @ p1 \<in> poss t"
        and p2:"p2 \<in> poss (ss ! i |_ p1)" "ss ! i |_ p1 |_ p2 = Var x" 
        and i:"i < length ss" and r1':"r1 = ps ! i @ p1 @ p2" 
      using var_at_t_tau[OF r1(2) r1(1)] by metis
    then have x:"x \<in> vars_term (ss!i)"
      by (metis (no_types, lifting) subsetD term.set_intros(3) vars_term_subt_at)
    show ?thesis proof(cases "r2 \<in> poss t \<and> t |_ r2 = Var x")
      case True
      then have "x \<in> vars_term t"
        by (metis subsetD term.set_intros(3) vars_term_subt_at) 
      with x show ?thesis 
        using disj(1) i by (meson disjoint_iff nth_mem)
    next
      case False
      then obtain j q1 q2 z where q1:"q1 \<in> poss (ss ! j)" "t |_ (ps ! j @ q1) = Var z" "ps!j @ q1 \<in> poss t"
        and q2:"q2 \<in> poss (ss ! j |_ q1)" "ss ! j |_ q1 |_ q2 = Var x" 
        and j:"j < length ss" and r2':"r2 = ps ! j @ q1 @ q2" 
        using var_at_t_tau[OF r2(2) r2(1)] by metis
      then have x2:"x \<in> vars_term (ss!j)" 
        by (metis (no_types, lifting) subsetD term.set_intros(3) vars_term_subt_at)
      show ?thesis proof(cases "i = j")
        case True
        then show ?thesis proof(cases "p1 = q1")
          case True
          have "linear_term (ss!i)" 
            using lin_s i nth_mem by blast
          moreover from p1 p2 have "ss!i |_ (p1 @ p2) = Var x" "p1 @ p2 \<in> poss (ss!i)" by simp_all
          moreover from q1 q2 \<open>i=j\<close> \<open>p1=q1\<close> have "ss!i |_ (p1 @ q2) = Var x" "p1 @ q2 \<in> poss (ss!i)" by simp_all
          ultimately show ?thesis 
            using linear_term_unique_vars by (metis True \<open>i = j\<close> r1' r1r2 r2')
        next
          case False
          with p1 q1 have "p1 \<bottom> q1" 
            unfolding True using var_poss_parallel by (smt (verit, ccfv_threshold) subterm_poss_conv var_poss_iff) 
          then have "p1 @ p2 \<noteq> q1 @ q2"
            by (metis less_eq_pos_simps(1) pos_less_eq_append_not_parallel) 
          moreover have "linear_term (ss!i)" 
            using lin_s i nth_mem by blast
          ultimately show ?thesis 
            using p1 p2 q1 q2 linear_term_unique_vars True by fastforce
        qed
      next
        case False
        with x x2 show ?thesis 
          using disj(2) i j by (meson disjoint_iff_not_equal linorder_neqE_nat)  
      qed
    qed 
  qed
  }
  then show ?thesis using distinct_vars_linear_term Proof_Term_Utils.distinct_vars by metis
qed

end

context ren_wf_trs
begin

(*Helper lemma*)
lemma source_subst_renamed_lhs:
  assumes rdp:"(\<alpha>, p) \<in> set (redex_patterns A)" and A_wf:"A \<in> wf_pterm R"
    and "lhs' = map_vars_term (rename_many' ren n) (lhs \<alpha>)" 
    and sigma_vars:"\<forall>i < length (var_poss_list lhs'). \<sigma> (vars_term_list lhs'!i) = (source A)|_(p@(var_poss_list lhs'!i))" 
  shows "lhs' \<cdot> \<sigma> = (source A)|_p" 
proof-
  let ?xs="map source (map (to_pterm \<circ> (\<lambda>pi. (source A) |_ (p @ pi))) (var_poss_list (lhs \<alpha>)))"
  let ?R="{}"
  have ll:"left_lin ?R"
    by (simp add: left_lin.intro left_linear_trs_def)
  from rdp have "to_rule \<alpha> \<in> R" 
    using A_wf by (metis labeled_source_to_term labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs poss_term_lab_to_term) 
  then have lin:"linear_term (lhs \<alpha>)"
    using left_lin using left_linear_trs_def by fastforce
  from rdp A_wf have p:"p \<in> poss (source A)"
    using left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast
  have "source (ll_single_redex (source A) p \<alpha>) = source A"
    using A_wf rdp using left_lin_wf_trs.source_single_step left_lin_wf_trs_axioms by auto
  then have "(lhs \<alpha>) \<cdot> \<langle>?xs\<rangle>\<^sub>\<alpha>  = (source A)|_p" 
    unfolding ll_single_redex_def using left_lin.source_ctxt_apply_term[OF ll] replace_at_subt_at[OF p] 
    by (smt (verit) p p_in_poss_to_pterm source.simps(3) source_ctxt_to_pterm to_pterm_trs_ctxt) 
  then have "lhs' \<cdot> (mk_subst Var (zip (vars_distinct lhs') ?xs)) = (source A)|_p"
    using mk_subst_rename renameN(3) by (metis (mono_tags, lifting) assms(3) lin length_map length_var_poss_list linear_term_var_vars_term_list)  
  with sigma_vars show ?thesis using substitution_subterm_at
    by (metis length_var_poss_list p subt_at_append)
qed

end

locale overlapping_part = ren_wf_trs +
  fixes rdp_A A B s As \<alpha>1 p1 \<beta> q
  assumes A_wf:"A \<in> wf_pterm R" 
    and rdp_A:"rdp_A = filter (\<lambda>(\<alpha>, p). measure_ov (ll_single_redex s p \<alpha>)  B \<noteq> 0) (redex_patterns A)" 
    and As:"As = map (\<lambda>(\<alpha>, p). ll_single_redex s p \<alpha>) rdp_A" 
    and \<alpha>1p1:"(\<alpha>1, p1) = hd rdp_A" 
    and not_empty:"rdp_A \<noteq> []"
    and s:"source A = s" "source B = s"
    and B:"B = ll_single_redex s q \<beta>" and q:"q \<in> poss s" and \<beta>:"to_rule \<beta> \<in> R"
begin
abbreviation "\<Delta>1 \<equiv> ll_single_redex s p1 \<alpha>1"

definition "renamed_lhs_\<alpha>s = rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A)"
definition "renamed_lhs_\<alpha>1 = map_vars_term (rename_many' ren 0) (lhs \<alpha>1)"
definition "renamed_lhs_\<beta> = map_vars_term (ren_l ren) (lhs \<beta>)" 
definition "p = (if q <\<^sub>p p1 then q else p1)"
definition "l = replace_at renamed_lhs_\<alpha>1 (pos_diff q p) renamed_lhs_\<beta>"
definition "ss = (renamed_lhs_\<alpha>1 |_ (pos_diff q p)) # (tl renamed_lhs_\<alpha>s)"
definition "ps = (pos_diff p1 p) # (map (\<lambda>pi. pos_diff pi q) (map snd (tl rdp_A)))" 
definition "\<tau> = tau.\<tau> ss renamed_lhs_\<beta> ps"
definition "\<tau>s = tau.\<tau>s ss renamed_lhs_\<beta> ps" 
definition "\<sigma>_vars = concat (map vars_term_list renamed_lhs_\<alpha>s) @ vars_term_list renamed_lhs_\<beta>"
definition "\<sigma>_terms = concat (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A)) 
                     @ (map ((|_) (s |_ q)) (var_poss_list renamed_lhs_\<beta>))"
definition "\<sigma> = mk_subst Var (zip \<sigma>_vars \<sigma>_terms)"
definition "B' = replace_at (to_pterm (l \<cdot> \<tau>)) (pos_diff q p) (Prule \<beta> (map (to_pterm \<circ> \<tau>) (vars_term_list renamed_lhs_\<beta>)))"
definition "As' = map (\<lambda>((\<alpha>i, pi), i). replace_at (to_pterm (l \<cdot> \<tau>)) (pos_diff pi p) (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))) (zip rdp_A [0..<length rdp_A])" 

lemma length_renamed_lhs_\<alpha>s: "length renamed_lhs_\<alpha>s = length rdp_A" 
  unfolding renamed_lhs_\<alpha>s_def rename_list_def by simp

lemma length_rdp_A:"length rdp_A = length As"
  by (simp add: As) 

lemma As_i_wf:
  assumes "Ai \<in> set As" 
  shows "Ai \<in> wf_pterm R"
proof-
  from assms obtain \<alpha> p where "(\<alpha>, p) \<in> set (redex_patterns A)" and "Ai = ll_single_redex s p \<alpha>"
    unfolding As rdp_A by force
  then have "Ai \<in> set (single_steps A)"
    using s(1) by auto 
  with A_wf show ?thesis
    using single_step_wf by blast 
qed

lemma rdp_A_subs_A:"set rdp_A \<subseteq> set (redex_patterns A)"
  unfolding rdp_A by simp

lemma sorted_rdp_A:"sorted_wrt (ord.lexordp (<)) (map snd rdp_A)" 
proof-
  have "sorted_wrt (ord.lexordp (<)) (map snd (redex_patterns A))"
    using left_lin_no_var_lhs.redex_patterns_sorted[OF ll_no_var_lhs A_wf] by simp
  then show ?thesis 
    unfolding rdp_A using sorted_wrt_filter sorted_wrt_map by blast 
qed

lemma order_rdp_A: 
  assumes "i < j" and "j < length rdp_A" 
    and "rdp_A ! i = (\<alpha>i, pi)" and "rdp_A ! j = (\<alpha>j, pj)" 
  shows "\<not> pj \<le>\<^sub>p pi" 
proof-
  from sorted_rdp_A have "(ord.lexordp (<)) pi pj " 
    using assms sorted_wrt_nth_less by fastforce 
  then show ?thesis
    by (metis less_eq_pos_def lexord_linorder.less_le_not_le ord.lexordp_eq_pref)     
qed

lemma As'_not_empty: "As' \<noteq> []" 
  unfolding As'_def using not_empty by simp

lemma \<alpha>1p1_in_rdpA: "(\<alpha>1, p1) \<in> set rdp_A"
  by (simp add: \<alpha>1p1 not_empty) 

lemma \<Delta>1: "\<Delta>1 \<in> set (single_steps A)"
  using \<alpha>1p1_in_rdpA rdp_A_subs_A s(1) by fastforce

lemma pi_poss:
  assumes rdp_i:"(\<alpha>i, pi) \<in> set rdp_A"
  shows "pi \<in> poss s"
  using A_wf left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs rdp_A_subs_A rdp_i s(1) by blast

lemma \<alpha>i_in_R:
  assumes rdp_i:"(\<alpha>i, pi) \<in> set rdp_A"
  shows "to_rule \<alpha>i \<in> R"
  using A_wf labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs rdp_A_subs_A rdp_i by fastforce 

lemma overlap:
  assumes rdp_i:"(\<alpha>i, pi) \<in> set rdp_A"
    and \<Delta>:"\<Delta> = ll_single_redex s pi \<alpha>i" 
  shows "measure_ov \<Delta> B \<noteq> 0"
  using \<Delta> rdp_A rdp_i by auto 

lemma overlap_\<Delta>1:"measure_ov \<Delta>1 B \<noteq> 0"
  using \<alpha>1p1_in_rdpA overlap by blast

lemma pq:"q <\<^sub>p p1 \<or> p1 \<le>\<^sub>p q" 
proof-
  from overlap_\<Delta>1 obtain r where r:"r \<in> possL \<Delta>1" "r \<in> possL B"
    by (metis card.empty disjoint_iff) 
  from r(1) obtain r1 where r1:"r = p1 @ r1" 
    using single_redex_possL \<alpha>1p1_in_rdpA \<alpha>i_in_R pi_poss by auto 
  from r(2) obtain r2 where r2:"r = q @ r2" 
    using single_redex_possL[OF \<beta>] using B q by auto 
  from r1 r2 show ?thesis
    by (metis less_eq_pos_simps(1) pos_cases pos_less_eq_append_not_parallel)
qed

lemma pq_pos_diff:"p @ pos_diff q p = q"
  using p_def pq by fastforce

lemma p_poss:"p \<in> poss s" 
  unfolding p_def using q \<alpha>1p1_in_rdpA pi_poss by(cases "q <\<^sub>p p1") auto

lemma diff_q_p_poss_\<alpha>1: "pos_diff q p \<in> poss (lhs \<alpha>1)" 
proof(cases "q <\<^sub>p p1")
  case True
  then show ?thesis 
    by (metis (mono_tags, lifting) append_self_conv empty_pos_in_poss p_def pq_pos_diff)
next
  case False
  then have le:"p1 \<le>\<^sub>p q" using pq by auto 
  moreover have "possL \<Delta>1 = {p1 @ r |r. r \<in> fun_poss (lhs \<alpha>1)}" 
    using single_redex_possL \<alpha>1p1_in_rdpA pi_poss \<alpha>i_in_R by auto 
  moreover have "possL B = {q @ r |r. r \<in> fun_poss (lhs \<beta>)}"
    using single_redex_possL B \<beta> q by auto 
  ultimately obtain r1 r2 where "r1 \<in> fun_poss (lhs \<alpha>1)" "r2 \<in> fun_poss (lhs \<beta>)" "p1@r1 = q@r2"
    using overlap_\<Delta>1 by (smt (verit, best) card.empty disjoint_iff mem_Collect_eq) 
  with le show ?thesis
    by (metis False append.assoc fun_poss_imp_poss p_def poss_append_poss pq_pos_diff same_append_eq)
qed

lemma diff_q_p_poss_renamed_\<alpha>1: "pos_diff q p \<in> poss renamed_lhs_\<alpha>1"  
  using diff_q_p_poss_\<alpha>1 unfolding renamed_lhs_\<alpha>1_def by simp

lemma diff_q_p_poss_l: "pos_diff q p \<in> poss (to_pterm l)"
proof-
  have "pos_diff q p \<in> poss renamed_lhs_\<alpha>1" 
    using diff_q_p_poss_\<alpha>1 unfolding renamed_lhs_\<alpha>1_def by simp
  then show ?thesis  
    unfolding l_def using p_in_poss_to_pterm by (metis (mono_tags, lifting) hole_pos_ctxt_of_pos_term hole_pos_poss) 
qed

lemma lin_lhs_\<alpha>i:
  assumes i:"i < length rdp_A" 
  shows "linear_term (lhs (fst (rdp_A!i)))"
proof-
  from i obtain \<alpha>i pi where rdp:"rdp_A ! i = (\<alpha>i, pi)" by force 
  with i have "to_rule \<alpha>i \<in> R"
    by (metis \<alpha>i_in_R nth_mem) 
  then have lin:"linear_term (lhs \<alpha>i)"
    using left_lin left_linear_trs_def by fastforce 
  with i rdp show ?thesis by simp
qed

lemma renamed_lhs_\<alpha>i:
  assumes i:"i < length rdp_A"
  shows "renamed_lhs_\<alpha>s!i = map_vars_term (rename_many' ren i) (lhs (fst (rdp_A!i)))" 
proof-
  from i have "zip [0..<length rdp_A] (map (\<lambda>(\<alpha>, p). lhs \<alpha>) (map (\<lambda>(\<alpha>, p'). (\<alpha>, p')) rdp_A)) ! i = (i, lhs (fst (rdp_A!i)))" 
    using split_beta by simp
  with i show ?thesis
    unfolding renamed_lhs_\<alpha>s_def rename_list_def by simp
qed

lemma lin_renamed_lhs_\<alpha>i:
  assumes "lhs_\<alpha>i \<in> set renamed_lhs_\<alpha>s"
  shows "linear_term lhs_\<alpha>i" 
  using lin_lhs_\<alpha>i renameN(3) renamed_lhs_\<alpha>i linear_term_map_inj_on_linear_term length_renamed_lhs_\<alpha>s
  by (smt (verit, best) all_nth_imp_all_set assms inj_on_def the_inv_f_f) 

lemma ren_lhs_\<alpha>1_alt:"renamed_lhs_\<alpha>1 = hd renamed_lhs_\<alpha>s"
  by (metis \<alpha>1p1 fst_eqD hd_conv_nth length_greater_0_conv length_renamed_lhs_\<alpha>s not_empty renamed_lhs_\<alpha>1_def renamed_lhs_\<alpha>i) 

lemma lin_renamed_\<beta>: "linear_term renamed_lhs_\<beta>" 
proof-
  have "linear_term (lhs \<beta>)" 
    using \<beta> left_lin left_linear_trs_def by fastforce
  then show ?thesis
    unfolding renamed_lhs_\<beta>_def using Mgu_generic.renameN(4) linear_term_map_inj_on_linear_term inj_on_subset by blast
qed
  
lemma linear_l: "linear_term l"proof-
  have lin1:"linear_term renamed_lhs_\<alpha>1"
    by (metis hd_in_set length_0_conv length_renamed_lhs_\<alpha>s lin_renamed_lhs_\<alpha>i not_empty ren_lhs_\<alpha>1_alt) 
  have "vars_term renamed_lhs_\<alpha>1 \<inter> vars_term renamed_lhs_\<beta> = {}" 
    unfolding renamed_lhs_\<alpha>1_def renamed_lhs_\<beta>_def
    using renameN(1) by (smt (verit, ccfv_threshold) disjoint_iff imageE rangeI term.set_map(2)) 
  then show ?thesis 
    unfolding l_def using linear_ctxt_of_pos_term[OF lin1 lin_renamed_\<beta>] using diff_q_p_poss_renamed_\<alpha>1 by auto
qed

lemma pi_below_q:
  assumes i:"i < length rdp_A" "i > 0" 
    and \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i" 
  shows "q <\<^sub>p pi"
proof-
  have \<alpha>1:"to_rule \<alpha>1 \<in> R"
    using \<alpha>1p1_in_rdpA \<alpha>i_in_R by blast 
  have \<alpha>i:"to_rule \<alpha>i \<in> R"
    by (metis \<alpha>i_in_R \<alpha>ipi i(1) nth_mem) 
  have p1:"p1 \<in> poss s"
    by (metis \<alpha>1p1_in_rdpA pi_poss)  
  have pi:"pi \<in> poss s"
    by (metis \<alpha>ipi i(1) nth_mem pi_poss)  
  have pos:"\<not> pi \<le>\<^sub>p p1"
    using order_rdp_A i by (metis \<alpha>1p1 \<alpha>ipi hd_conv_nth not_empty)
  have "measure_ov (ll_single_redex s pi \<alpha>i) B \<noteq> 0"
    using \<alpha>ipi i(1) overlap by force 
  moreover have ai:"possL (ll_single_redex s pi \<alpha>i) = {pi @ r |r. r \<in> fun_poss (lhs \<alpha>i)}" 
    using single_redex_possL[OF \<alpha>i pi] by simp
  moreover from single_redex_possL[OF \<beta> q] have b:"possL B = {q @ r |r. r \<in> fun_poss (lhs \<beta>)}" 
    unfolding B by simp
  ultimately consider "pi \<le>\<^sub>p q" | "q <\<^sub>p pi"
    by (smt (verit, ccfv_SIG) card_eq_0_iff disjoint_iff less_eq_pos_simps(1) mem_Collect_eq order_pos.less_le pos_append_cases)
  then show ?thesis proof(cases)
    case 1
    from single_redex_possL[OF \<alpha>1 p1] have a1:"possL \<Delta>1 = {p1 @ r |r. r \<in> fun_poss (lhs \<alpha>1)}" by simp
    from pos consider (less) "p1 <\<^sub>p pi" | (par) "p1 \<bottom> pi"  
      using parallel_pos by force
    then show ?thesis proof(cases)
      case less
      with overlap_\<Delta>1 a1 b 1 have q2:"q \<in> possL \<Delta>1" 
        using p_def pq_pos_diff
        by (smt (verit, ccfv_threshold) append_assoc append_eq_append_conv fun_poss_append_poss' card_eq_0_iff 
            disjoint_iff mem_Collect_eq order_pos.less_le prefix_pos_diff) 
      from i have \<Delta>i:"ll_single_redex s pi \<alpha>i \<in> set (single_steps A)"
        using \<alpha>ipi rdp_A_subs_A s(1) by force
      have "measure_ov \<Delta>1 (ll_single_redex s pi \<alpha>i) = 0"
        using single_steps_measure[OF \<Delta>1 \<Delta>i A_wf] less by (simp add: order_pos.less_le p1 pi single_redex_neq)
      moreover from ai have "pi \<in> possL (ll_single_redex s pi \<alpha>i)" proof-
        have "[] \<in> fun_poss (lhs \<alpha>i)" 
          using \<alpha>i no_var_lhs by fastforce 
        then show ?thesis using ai by simp
      qed
      ultimately have "pi \<notin> possL \<Delta>1"
        by (meson card_eq_0_iff disjoint_iff finite_Int finite_possL) 
      with 1 have "q \<notin> possL \<Delta>1" unfolding a1
        by (smt (z3) fun_poss_append_poss' less_eq_pos_simps(1) mem_Collect_eq pos pos_append_cases prefix_pos_diff)
      with q2 show ?thesis by simp
    next
      case par 
      then have False
        using 1 by (metis less_eq_pos_def order_pos.dual_order.trans order_pos.less_imp_le pos_less_eq_append_not_parallel pq) 
      then show ?thesis by simp
    qed
  qed simp
qed

section\<open>Properties for substitution \<tau>\<close>

lemma len_ss_ps: "length ss = length ps" 
  unfolding ss_def ps_def rename_list_def length_Cons length_tl length_map length_zip renamed_lhs_\<alpha>s_def
  using not_empty Suc_diff_1 by simp

lemma ps_in_poss_ren_\<beta>:
  assumes "pi \<in> set ps" 
  shows "pi \<in> poss renamed_lhs_\<beta>" 
proof-
  from assms obtain i where i:"i < length ps" and pi:"ps!i = pi"
    by (metis in_set_idx) 
  then show ?thesis proof(cases i)
    case 0
    have "(pos_diff p1 p) \<in> poss renamed_lhs_\<beta>" proof(cases "q <\<^sub>p p1")
      case False
      then show ?thesis
        unfolding p_def by (metis empty_pos_in_poss order_pos.order_refl prefix_pos_diff self_append_conv) 
    next
      case True
      moreover have "possL \<Delta>1 = {p1 @ r |r. r \<in> fun_poss (lhs \<alpha>1)}" 
        using single_redex_possL using \<alpha>1p1_in_rdpA \<alpha>i_in_R pi_poss by force
      moreover have "possL B = {q @ r |r. r \<in> fun_poss (lhs \<beta>)}"
        using single_redex_possL B \<beta> q by auto 
      ultimately obtain r1 r2 where "r1 \<in> fun_poss (lhs \<alpha>1)" "r2 \<in> fun_poss (lhs \<beta>)" "p1@r1 = q@r2"
        using overlap_\<Delta>1 by (smt (verit, best) card.empty disjoint_iff mem_Collect_eq) 
      with True show ?thesis
        unfolding p_def by (metis (mono_tags) fun_poss_imp_poss less_eq_pos_simps(1) less_eq_pos_simps(2) 
        order_pos.less_le_not_le poss_append_poss poss_map_vars_term prefix_pos_diff renamed_lhs_\<beta>_def)
    qed
    then show ?thesis
      using "0" pi ps_def by fastforce 
  next
    case (Suc n)
    let ?pi="snd (rdp_A ! i)"
    let ?\<alpha>i="fst (rdp_A ! i)"
    let ?\<Delta>i="ll_single_redex s ?pi ?\<alpha>i"
    have \<alpha>ipi:"(?\<alpha>i, ?pi) \<in> set rdp_A"
      using i not_empty ps_def by auto
    from i have pi:"ps!i = pos_diff ?pi q" 
      unfolding Suc ps_def by (simp add: nth_tl)
    have "possL ?\<Delta>i = {?pi @ r |r. r \<in> fun_poss (lhs ?\<alpha>i)}" 
      using single_redex_possL \<alpha>ipi \<alpha>i_in_R pi_poss by blast
    moreover have "possL B = {q @ r |r. r \<in> fun_poss (lhs \<beta>)}"
      using single_redex_possL B \<beta> q by auto 
    moreover have "measure_ov ?\<Delta>i B \<noteq> 0"
      using \<alpha>ipi overlap by blast 
    ultimately obtain r1 r2 where "r1 \<in> fun_poss (lhs ?\<alpha>i)" "r2 \<in> fun_poss (lhs \<beta>)" "?pi@r1 = q@r2"
      by (smt (verit, best) card.empty disjoint_iff mem_Collect_eq) 
    moreover have "q <\<^sub>p ?pi" 
      using pi_below_q by (metis Suc bot_nat_0.not_eq_extremum hd_Cons_tl i length_map length_nth_simps(2) 
          lessI less_nat_zero_code prod.collapse ps_def not_empty)
    ultimately have "pos_diff ?pi q \<in> poss renamed_lhs_\<beta>"
      by (metis ctxt_supt_id fun_poss_imp_poss less_eq_pos_simps(1) less_eq_pos_simps(2) order_pos.dual_order.strict_implies_order 
          poss_map_vars_term prefix_pos_diff renamed_lhs_\<beta>_def replace_at_below_poss)    
    then show ?thesis using pi \<open>ps!i = pi\<close> by simp
  qed 
qed

lemma vars_term_disjoint:
  assumes "ss_i \<in> set ss"
  shows "vars_term ss_i \<inter> vars_term renamed_lhs_\<beta> = {}"
proof-
  from assms obtain i where i:"i < length ss" and ss_i:"ss!i = ss_i"
    by (metis in_set_idx)
  show ?thesis proof(cases i)
    case 0
    then have *:"ss_i = renamed_lhs_\<alpha>1 |_ (pos_diff q p)" 
      unfolding ss_def ss_i[symmetric] by simp
    have "vars_term renamed_lhs_\<alpha>1 \<inter> vars_term renamed_lhs_\<beta> = {}" 
      unfolding renamed_lhs_\<alpha>1_def renamed_lhs_\<beta>_def using renameN(1)
      by (smt (verit) disjoint_iff imageE rangeI term.set_map(2)) 
    then show ?thesis 
      unfolding * using vars_term_subt_at[OF diff_q_p_poss_renamed_\<alpha>1] by blast
  next
    case (Suc n)
    then have "ss_i = renamed_lhs_\<alpha>s!i"
      unfolding ss_i[symmetric] using i nth_tl ss_def by auto 
    then obtain u where "ss_i = map_vars_term (rename_many' ren i) u" 
      using renamed_lhs_\<alpha>i i len_ss_ps length_renamed_lhs_\<alpha>s by (simp add: not_empty ss_def) 
    then show ?thesis using renameN(1)
      by (smt (verit, best) disjoint_iff imageE rangeI renamed_lhs_\<beta>_def term.set_map(2))
  qed
qed

lemma vars_term_disjoint_ss:
  assumes i:"i < j" and j:"j < length ss"
  shows "vars_term (ss!i) \<inter> vars_term (ss!j) = {}"
proof-
  from i j have "ss!j = renamed_lhs_\<alpha>s!j"
    unfolding ss_def by (metis hd_Cons_tl length_0_conv length_renamed_lhs_\<alpha>s less_imp_Suc_add nth_Cons_Suc not_empty) 
  then obtain u where u:"ss!j = map_vars_term (rename_many' ren j) u" 
    unfolding ss_def using renamed_lhs_\<alpha>i j len_ss_ps length_renamed_lhs_\<alpha>s by (simp add: ps_def not_empty) 
  then show ?thesis proof(cases i)
    case 0
    then have *:"ss!i = renamed_lhs_\<alpha>1 |_ (pos_diff q p)" 
      unfolding ss_def by simp
    have "vars_term renamed_lhs_\<alpha>1 \<inter> vars_term (ss!j) = {}" 
      unfolding u unfolding renamed_lhs_\<alpha>1_def using renameN(2)[of i j] using i unfolding 0 by (simp add: rename_many_disj)
    then show ?thesis 
      unfolding * using vars_term_subt_at[OF diff_q_p_poss_renamed_\<alpha>1] by blast
  next
    case (Suc n)
    then have "ss!i = renamed_lhs_\<alpha>s!i"
      unfolding ss_def by (metis hd_Cons_tl length_0_conv length_nth_simps(4) length_renamed_lhs_\<alpha>s not_empty) 
    then obtain u' where u':"ss!i = map_vars_term (rename_many' ren i) u'" 
      using renamed_lhs_\<alpha>i i j len_ss_ps length_renamed_lhs_\<alpha>s by (simp add: ss_def)
    from i show ?thesis
      unfolding u u' using renameN(2) by (simp add: rename_many_disj)
  qed
qed

lemma tau:"tau ss renamed_lhs_\<beta> ps"
proof-
  have lin_ss:"\<forall>s\<in>set ss. linear_term s" 
    unfolding ss_def using lin_renamed_lhs_\<alpha>i diff_q_p_poss_renamed_\<alpha>1
    by (metis hd_Cons_tl hd_in_set length_0_conv length_renamed_lhs_\<alpha>s list.set_intros(2) not_empty ren_lhs_\<alpha>1_alt set_ConsD subt_at_linear) 
  show ?thesis
    using tau.intro[OF len_ss_ps lin_renamed_\<beta> lin_ss] ps_in_poss_ren_\<beta> lin_renamed_lhs_\<alpha>i vars_term_disjoint_ss vars_term_disjoint by simp
qed

lemma renamed_lhs_\<alpha>1_\<tau>:
  assumes x:"x \<in> vars_ctxt (ctxt_of_pos_term (pos_diff q p) renamed_lhs_\<alpha>1)"
  shows "\<tau> x = Var x" 
proof-
  {fix i assume i:"i < length ss"
    have "x \<notin> vars_term (ss!i)" proof(cases i)
      case 0
      have "linear_term renamed_lhs_\<alpha>1"
        using lin_renamed_lhs_\<alpha>i ren_lhs_\<alpha>1_alt by (metis hd_in_set length_0_conv length_renamed_lhs_\<alpha>s not_empty) 
      with x show ?thesis unfolding 0 nth_Cons_0
        using diff_q_p_poss_renamed_\<alpha>1 linear_term_ctxt ss_def by fastforce
    next
      case (Suc n)
      from x have "x \<in> vars_term renamed_lhs_\<alpha>1"
        using diff_q_p_poss_renamed_\<alpha>1 by (simp add: vars_ctxt_pos_term)
      then show ?thesis using tau.disj(2)[OF tau] unfolding Suc
        by (metis Int_iff Suc emptyE hd_Cons_tl i length_nth_simps(1) length_nth_simps(2) length_renamed_lhs_\<alpha>s less_numeral_extra(3) 
            nth_Cons_Suc not_empty rename_many_disj renamed_lhs_\<alpha>1_def renamed_lhs_\<alpha>i ss_def zero_less_Suc) 
    qed
  }
  moreover have "x \<notin> vars_term renamed_lhs_\<beta>"
    unfolding renamed_lhs_\<beta>_def using x by (metis ctxt_of_pos_term_hole_pos disjoint_iff hole_pos_poss 
        l_def linear_l linear_term_ctxt renamed_lhs_\<beta>_def replace_at_subt_at)
  ultimately show ?thesis
    using tau.apply_tau_var[OF tau] \<tau>_def by presburger
qed

lemma l_\<tau>:"l \<cdot> \<tau> = (ctxt_of_pos_term (pos_diff q p) renamed_lhs_\<alpha>1)\<langle>renamed_lhs_\<beta> \<cdot> \<tau>\<rangle>" 
proof- 
  have "ctxt_of_pos_term (pos_diff q p) renamed_lhs_\<alpha>1 \<cdot>\<^sub>c \<tau> = ctxt_of_pos_term (pos_diff q p) renamed_lhs_\<alpha>1"
    using ctxt_subst_eq ctxt_subst_id renamed_lhs_\<alpha>1_\<tau> by force
  then show ?thesis using l_def by auto 
qed

lemma linear_l_tau:"linear_term (l \<cdot> \<tau>)" 
proof-
 have lin_ren_lhs_\<beta>:"linear_term (renamed_lhs_\<beta> \<cdot> \<tau>)" 
    using tau.linear_term_t_tau[OF tau] \<tau>_def by presburger
  have lin_\<alpha>1:"linear_term renamed_lhs_\<alpha>1"
    by (metis hd_in_set length_0_conv length_renamed_lhs_\<alpha>s lin_renamed_lhs_\<alpha>i not_empty ren_lhs_\<alpha>1_alt) 
  {fix r1 r2 x assume r1:"r1 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r1 = Var x" "\<not> pos_diff q p \<le>\<^sub>p r1"
      and r2:"r2 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r2 = Var x" "\<not> pos_diff q p \<le>\<^sub>p r2"
      and r1r2:"r1 \<noteq> r2" 
    from r1 have par1:"pos_diff q p \<bottom> r1"
      by (metis diff_q_p_poss_renamed_\<alpha>1 l_\<tau> less_pos_def' order_pos.le_less pos_cases replace_at_below_poss var_pos_maximal) 
    then have 1:"l \<cdot> \<tau> |_ r1 = renamed_lhs_\<alpha>1 |_ r1" 
      by (metis diff_q_p_poss_renamed_\<alpha>1 l_\<tau> parallel_poss_replace_at parallel_replace_at_subt_at r1(1)) 
    from r2 have par2:"pos_diff q p \<bottom> r2"
      by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau> less_pos_def' pos_cases var_pos_maximal) 
    then have 2:"l \<cdot> \<tau> |_ r2 = renamed_lhs_\<alpha>1 |_ r2" 
      by (metis diff_q_p_poss_renamed_\<alpha>1 l_\<tau> parallel_poss_replace_at parallel_replace_at_subt_at r2(1)) 
    from 1 2 par1 par2 have False
      by (metis diff_q_p_poss_renamed_\<alpha>1 l_\<tau> lin_\<alpha>1 linear_term_unique_vars parallel_poss_replace_at r1(1,2) r1r2 r2(1,2))
  } moreover 
  {fix r1 r2 x assume r1:"r1 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r1 = Var x" "pos_diff q p \<le>\<^sub>p r1"
                  and r2:"r2 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r2 = Var x" "\<not> pos_diff q p \<le>\<^sub>p r2"
                  and r1r2:"r1 \<noteq> r2" 
    from r2 have par2:"pos_diff q p \<bottom> r2"
      by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau> less_pos_def' pos_cases var_pos_maximal) 
    then have r2_pos:"r2 \<in> poss renamed_lhs_\<alpha>1"
      using diff_q_p_poss_renamed_\<alpha>1 l_\<tau> parallel_poss_replace_at r2(1) by auto 
    from par2 have 2:"l \<cdot> \<tau> |_ r2 = renamed_lhs_\<alpha>1 |_ r2" 
      unfolding l_\<tau> using parallel_replace_at_subt_at diff_q_p_poss_renamed_\<alpha>1 l_\<tau> parallel_poss_replace_at r2(1) by fastforce
    with r2(2) r2_pos have x:"x \<in> vars_term renamed_lhs_\<alpha>1"
      by (simp add: vars_ctxt_pos_term)        
    from r1 obtain r1' where r1':"r1 = pos_diff q p @ r1'"
      using less_eq_pos_def by auto
    with r1(1) have r1'_pos:"r1' \<in> poss (renamed_lhs_\<beta> \<cdot> \<tau>)"
      by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_subt_at) 
    have at_r1':"renamed_lhs_\<beta> \<cdot> \<tau> |_ r1' = Var x"
      by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau> r1' r1(2) replace_at_subt_at subt_at_append) 
    have False proof(cases "r1' \<in> poss renamed_lhs_\<beta> \<and> renamed_lhs_\<beta> |_ r1' = Var x")
      case True
      with r1'_pos have "x \<in> vars_term renamed_lhs_\<beta>"
        by (metis subsetD term.set_intros(3) vars_term_subt_at)
      with x show ?thesis
        by (smt (verit, best) Mgu_generic.renameN(1) disjoint_iff imageE rangeI renamed_lhs_\<alpha>1_def renamed_lhs_\<beta>_def term.set_map(2))
    next
      case False
      then obtain r11 r12 y where y:"renamed_lhs_\<beta>|_r11 = Var y" and r11:"r11 \<in> var_poss renamed_lhs_\<beta>" and r11r12:"r1' = r11 @ r12"
        by (smt (verit, best) at_r1' eval_term.simps(2) is_FunE poss_subst_choice r1'_pos subt_at_subst term.distinct(1) var_poss_iff)
      then have *:"renamed_lhs_\<beta> \<cdot> \<tau> |_ r1' = \<tau> y |_ r12" 
        by (simp add: var_poss_iff) 
      from y r11 r11r12 False have "x \<noteq> y"
        by (metis "2" append_Nil2 diff_q_p_poss_renamed_\<alpha>1 l_def par2 parallel_poss_replace_at parallel_replace_at_subt_at poss_append_poss r1'_pos r2(2) 
            r2_pos subt_at_subst var_pos_maximal var_poss_imp_poss)
      then have "\<tau> y \<noteq> Var y" 
        using y r11 r1(1,2) False at_r1' r1'_pos r11r12 var_poss_iff by fastforce
      then obtain i r' where i:"i < length ss" "ps ! i @ r' = r11" and r':"r' \<in> poss (ss ! i)" and \<tau>y:"\<tau> y = ss ! i |_ r'" 
        using tau.apply_tau_t_var'[OF tau r11 y] \<tau>_def by auto
      with * have **:"ss ! i |_ r' |_ r12 = Var x"
        using at_r1' by presburger 
      with i r' \<tau>y * have x2:"x \<in> vars_term (ss!i)"
        by (smt (verit, ccfv_SIG) eval_term.simps(1) pos_append_poss r1'_pos r11 r11r12 subt_at_subst subterm_poss_conv var_poss_iff vars_term_var_poss_iff y)
      then show ?thesis proof(cases i)
        case 0      
        with x x2 2 show ?thesis
          using diff_q_p_poss_renamed_\<alpha>1 lin_\<alpha>1 linear_subterms_disjoint_vars par2 r2(2) r2_pos ss_def by fastforce
      next
        case (Suc n)
        have "vars_term (ss!i) \<inter> vars_term renamed_lhs_\<alpha>1 = {}"
          by (metis Suc Zero_neq_Suc hd_Cons_tl i(1) length_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s nth_Cons_Suc not_empty rename_many_disj renamed_lhs_\<alpha>1_def renamed_lhs_\<alpha>i ss_def) 
        with x x2 show ?thesis by blast
      qed
    qed
  } moreover 
  {fix r1 r2 x assume r1:"r1 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r1 = Var x" "pos_diff q p \<le>\<^sub>p r1"
                  and r2:"r2 \<in> poss (l\<cdot>\<tau>)" "l \<cdot> \<tau> |_ r2 = Var x" "pos_diff q p \<le>\<^sub>p r2"
                  and r1r2:"r1 \<noteq> r2" 
    from r1 obtain r1' where r1':"r1 = pos_diff q p @ r1'"
      using less_eq_pos_def by auto
    with r1(1) have r1'_pos:"r1' \<in> poss (renamed_lhs_\<beta> \<cdot> \<tau>)"
      by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_subt_at)
    have at_r1':"renamed_lhs_\<beta> \<cdot> \<tau> |_ r1' = Var x"
      by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau> r1' r1(2) replace_at_subt_at subt_at_append) 
    from r2 obtain r2' where r2':"r2 = pos_diff q p @ r2'"
      using less_eq_pos_def by auto
    with r2(1) have r2'_pos:"r2' \<in> poss (renamed_lhs_\<beta> \<cdot> \<tau>)"
      by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_subt_at)
    have at_r2':"renamed_lhs_\<beta> \<cdot> \<tau> |_ r2' = Var x"
      by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau> r2' r2(2) replace_at_subt_at subt_at_append) 
    have r1'r2':"r1' \<noteq> r2'" 
      using r1r2 r1' r2' by auto
    have False using lin_ren_lhs_\<beta>
      by (meson at_r1' at_r2' linear_term_unique_vars r1'_pos r1'r2' r2'_pos)   
  }
  ultimately show ?thesis
    using distinct_vars_linear_term Proof_Term_Utils.distinct_vars by metis
qed

section\<open>Substitution \<sigma> maps to subterms of s\<close>

lemma distinct_vars_renamed_lhs_\<alpha>:
  "distinct (concat (map vars_term_list renamed_lhs_\<alpha>s))"
  using distinct_linear_renamed_vars
  by (metis (mono_tags, lifting) in_set_conv_nth length_map lin_lhs_\<alpha>i map_nth_eq_conv renamed_lhs_\<alpha>s_def split_beta) 

lemma distinct_vars_ren_\<beta>: "distinct (vars_term_list renamed_lhs_\<beta>)"
  using lin_renamed_\<beta> by (simp add: linear_term_distinct_vars)

lemma distinct_\<sigma>_vars: "distinct \<sigma>_vars"
  unfolding \<sigma>_vars_def using distinct_vars_ren_\<beta> distinct_vars_renamed_lhs_\<alpha> distinct_append
  by (metis ren.disjoint_concat_renamed_vars renamed_lhs_\<alpha>s_def renamed_lhs_\<beta>_def)

lemma length_vars_term_list_i:
  assumes i:"i < length renamed_lhs_\<alpha>s"
  shows "length (map vars_term_list renamed_lhs_\<alpha>s!i) = length (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A)!i)" 
proof-
  from i obtain u p' where *:"(rename_redex_patterns rdp_A) ! i = (u, p')"
    by fastforce 
  with i have "renamed_lhs_\<alpha>s!i = u"
     unfolding renamed_lhs_\<alpha>s_def rename_redex_patterns_eq_rename_list[symmetric] by simp
  moreover from * i have "map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A)!i = map ((|_) (s |_p' )) (var_poss_list u)"
    unfolding renamed_lhs_\<alpha>s_def rename_list_def length_map rename_redex_patterns_def by fastforce 
  ultimately show ?thesis
    using length_var_poss_list by (metis (no_types, lifting) i length_map nth_map) 
qed

lemma \<sigma>_y:
  assumes j:"j < length (vars_term_list renamed_lhs_\<beta>)" 
    and yj:"yj = vars_term_list renamed_lhs_\<beta> ! j"
    and qj:"qj = var_poss_list renamed_lhs_\<beta> ! j"
  shows "\<sigma> yj = s|_(q@qj)" 
proof- 
  have length:"length (map vars_term_list renamed_lhs_\<alpha>s) = length (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A))"
    unfolding renamed_lhs_\<alpha>s_def rename_list_def length_map rename_redex_patterns_def by simp
  with length_vars_term_list_i have length_concat_vars_terms:"length (concat (map vars_term_list renamed_lhs_\<alpha>s)) = length (concat (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A)))"
    unfolding renamed_lhs_\<alpha>s_def length_concat by (smt (verit, ccfv_SIG) list.map_comp map_eq_imp_length_eq map_equality_iff map_nth nth_map)
  have zip_sigma_alt:"zip \<sigma>_vars \<sigma>_terms = zip (concat (map vars_term_list renamed_lhs_\<alpha>s)) 
                         (concat (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A))) 
                         @ (zip (vars_term_list renamed_lhs_\<beta>) (map ((|_) (s |_ q)) (var_poss_list renamed_lhs_\<beta>)))" 
    unfolding \<sigma>_vars_def \<sigma>_terms_def using zip_append[OF length_concat_vars_terms] by presburger 
  have "yj \<notin> set (concat (map vars_term_list renamed_lhs_\<alpha>s))" proof-
    {fix i assume "i < length renamed_lhs_\<alpha>s"
      then obtain u where "renamed_lhs_\<alpha>s!i = map_vars_term (rename_many' ren i) u" 
        using renamed_lhs_\<alpha>i by (simp add: length_renamed_lhs_\<alpha>s)
      then have "yj \<notin> set (vars_term_list (renamed_lhs_\<alpha>s!i))" 
        using renameN(1) by (smt (verit, del_insts) disjoint_iff image_iff j nth_mem rangeI renamed_lhs_\<beta>_def set_vars_term_list term.set_map(2) yj) 
    }
    then show ?thesis unfolding set_concat
      by (smt (verit, best) UN_iff in_set_conv_nth length_map nth_map) 
  qed
  then have *:"\<sigma> yj = mk_subst Var (zip (vars_term_list renamed_lhs_\<beta>) (map ((|_) (s |_ q)) (var_poss_list renamed_lhs_\<beta>))) yj"
    using mk_subst_concat unfolding \<sigma>_def zip_sigma_alt by (metis (no_types, lifting) length_concat_vars_terms map_fst_zip)
  show ?thesis 
    unfolding * using mk_subst_distinct[OF distinct_vars_ren_\<beta> j]
    by (smt (verit, ccfv_SIG) j length_map length_var_poss_list nth_map q qj subt_at_append yj)
qed

lemma ren_lhs_\<beta>_\<sigma>: "renamed_lhs_\<beta> \<cdot> \<sigma> = s|_q"
proof-
  let ?ys="map source (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>)))"
  have length:"length (var_rule \<beta>) = length (var_poss_list (lhs \<beta>))"
    by (metis \<beta> length_var_poss_list length_var_rule) 
  have "(lhs \<beta>) \<cdot> \<langle>?ys\<rangle>\<^sub>\<beta>  = s|_q" 
    using B unfolding ll_single_redex_def using source_ctxt_apply_term
    by (metis (no_types, lifting) p_in_poss_to_pterm q replace_at_subt_at s(2) source.simps(3) source_ctxt_to_pterm to_pterm_trs_ctxt)
  then have "renamed_lhs_\<beta> \<cdot> (mk_subst Var (zip (vars_distinct renamed_lhs_\<beta>) ?ys)) = s|_q"
    unfolding renamed_lhs_\<beta>_def using length mk_subst_rename[of "lhs \<beta>" ?ys] renameN(4) unfolding length_map by metis
  with \<sigma>_y show ?thesis using substitution_subterm_at
    by (metis (no_types, lifting) q subt_at_append)
qed

lemma \<sigma>_x:
  assumes i:"i < length renamed_lhs_\<alpha>s"
    and \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i"
    and j:"j < length (vars_term_list (renamed_lhs_\<alpha>s!i))"
    and xj:"xj = vars_term_list (renamed_lhs_\<alpha>s!i) ! j"
    and pj:"pj = var_poss_list (renamed_lhs_\<alpha>s!i) ! j"
  shows "\<sigma> xj = s|_(pi@pj)"
proof- 
  have length:"length (map vars_term_list renamed_lhs_\<alpha>s) = length (map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A))"
    unfolding renamed_lhs_\<alpha>s_def rename_list_def length_map rename_redex_patterns_def by simp
  from j have j2:"j < length (var_poss_list (renamed_lhs_\<alpha>s!i))"
    by (simp add: length_var_poss_list) 
  let ?x_vars="map vars_term_list renamed_lhs_\<alpha>s"
  let ?x_terms="(map (\<lambda>(lhs_\<alpha>i, pi). (map ((|_) (s |_pi )) (var_poss_list lhs_\<alpha>i))) (rename_redex_patterns rdp_A))"
  have l_x:"length ?x_vars = length ?x_terms" 
    unfolding renamed_lhs_\<alpha>s_def length_map rename_list_def rename_redex_patterns_def by simp
  {fix k assume "k < length rdp_A" 
    then have "length (?x_vars!k) = length (?x_terms!k)"
      using length_vars_term_list_i length_renamed_lhs_\<alpha>s by presburger
  }note length_x_at_i=this
  with l_x have x_map_length:"map length ?x_vars = map length ?x_terms" 
    using list_eq_iff_nth_eq by (smt (verit, best) length_map length_vars_term_list_i nth_map) 
  then have x_map_length_i:"map length (take i ?x_vars) = map length (take i ?x_terms)"
    by (metis take_map) 
  let ?k="sum_list (map length (take i ?x_vars)) + j"
  have k2:"?k = sum_list (map length (take i ?x_terms)) + j" 
    using x_map_length_i by simp
  from i j have k_less:"?k < length (concat ?x_vars)"
    by (simp add: concat_nth_length) 
  moreover from i j have "concat ?x_vars ! ?k = xj" 
    by (simp add: concat_nth xj) 
  ultimately have 1:"\<sigma>_vars ! ?k = xj" 
    unfolding nth_append \<sigma>_vars_def by presburger 
  from k_less x_map_length have k_less2:"?k < length (concat ?x_terms)"
    by (simp add: length_concat)
  moreover have "concat ?x_terms ! ?k = s|_(pi@pj)" proof-
    have concat_k:"concat ?x_terms ! ?k = ?x_terms ! i ! j" 
      using j length_x_at_i concat_nth unfolding k2
      by (metis (no_types, lifting) i length length_vars_term_list_i list.map_comp map_equality_iff nth_map) 
    have i3:"i < length (rename_redex_patterns rdp_A)" 
      unfolding rename_redex_patterns_def length_map length_zip using i length_renamed_lhs_\<alpha>s by auto 
    from i3 have "rename_redex_patterns rdp_A ! i = (map fst (rename_redex_patterns rdp_A) ! i, map snd (rename_redex_patterns rdp_A) ! i)"
      by simp 
    moreover have "map snd (rename_redex_patterns rdp_A) ! i = pi"
      unfolding nth_map[OF i3] unfolding rename_redex_patterns_def using \<alpha>ipi i unfolding length_renamed_lhs_\<alpha>s
      by (metis (no_types, lifting) case_prod_conv length_map length_zip map_nth min.idem nth_map nth_zip old.prod.inject prod.collapse)
    ultimately have "rename_redex_patterns rdp_A ! i = (renamed_lhs_\<alpha>s!i, pi)"
      unfolding rename_redex_patterns_eq_rename_list renamed_lhs_\<alpha>s_def by simp
    then have at_i:"?x_terms ! i = map ((|_) (s |_ pi)) (var_poss_list (renamed_lhs_\<alpha>s!i))" 
      unfolding nth_map[OF i3] by simp  
    show ?thesis 
      unfolding concat_k at_i nth_map[OF j2] by (metis \<alpha>ipi i length_renamed_lhs_\<alpha>s nth_mem pi_poss pj subt_at_append)
  qed
  ultimately have 2:"\<sigma>_terms ! ?k = s|_(pi@pj)" 
    unfolding nth_append by (simp add: \<sigma>_terms_def nth_append)
  show ?thesis
    by (metis "1" "2" \<sigma>_def \<sigma>_terms_def \<sigma>_vars_def distinct_\<sigma>_vars k_less k_less2 length_append mk_subst_distinct trans_less_add1)
qed

lemma renamed_lhs_\<alpha>i_\<sigma>:
  assumes i:"i < length renamed_lhs_\<alpha>s"
    and pi:"pi = snd (rdp_A ! i)"
  shows "renamed_lhs_\<alpha>s!i \<cdot> \<sigma> = s|_pi"
proof-
  let ?\<alpha>i="fst (rdp_A ! i)" 
  from i pi have elem:"(?\<alpha>i, pi) \<in> set (redex_patterns A)"
    using length_renamed_lhs_\<alpha>s rdp_A_subs_A by auto
  from i have "zip [0..<length rdp_A] (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A) ! i = (i, lhs ?\<alpha>i)" 
    unfolding renamed_lhs_\<alpha>s_def rename_list_def length_zip length_map using nth_zip by (simp add: split_beta) 
  then have ren_i:"renamed_lhs_\<alpha>s!i = map_vars_term (rename_many' ren i) (lhs ?\<alpha>i)" 
    unfolding renamed_lhs_\<alpha>s_def rename_list_def using i length_renamed_lhs_\<alpha>s by auto
  show ?thesis
    using source_subst_renamed_lhs[OF elem A_wf ren_i] \<sigma>_x[OF i]
    by (simp add: length_var_poss_list pi s(1) split_pairs)
qed

section\<open>Composition of \<sigma> after \<tau> maps to subterms of s\<close>
(*The slightly awkward introduction of \<tau>' is necessary, because later we want to be able to use 
this lemma for lemma \<sigma>_\<tau>_x. A variable x of lhs(\<alpha>\<^sub>i) is first mapped to some subterm of lhs(\<beta>) by 
some component \<tau>\<^sub>j of \<tau>. Then the remaining \<tau>\<^sub>j\<^sub>+\<^sub>1 \<cdots> \<tau>\<^sub>n (hence the \<open>\<tau>' = compose (drop \<dots>\<close>)  
map every variable of that subterm of lhs(\<beta>) to appropriate subterms of s.*)
lemma \<sigma>_\<tau>'_y:
  assumes i:"i \<le> length ss"
    and \<tau>':"\<tau>' = compose (drop i (map2 (\<lambda>x y. linear_unifier x (renamed_lhs_\<beta> |_ y)) ss ps))"
    and j:"j < length (vars_term_list renamed_lhs_\<beta>)" 
    and yj:"yj = vars_term_list renamed_lhs_\<beta> ! j" and qj:"qj = var_poss_list renamed_lhs_\<beta> ! j" 
  shows "(\<tau>' \<circ>\<^sub>s \<sigma>) yj = s|_(q@qj)"
proof-
  consider "\<tau>' yj = Var yj" | "(\<exists>i r'. i < length ss \<and> r' \<in> poss (ss ! i) \<and> ps ! i @ r' = qj \<and> \<tau>' yj = ss ! i |_ r')"
   using tau.apply_tau_t_var[OF tau \<tau>' i] by (metis j length_var_poss_list nth_mem qj var_poss_list_sound vars_term_list_var_poss_list yj) 
  then show ?thesis proof(cases)
    case 1
    then show ?thesis 
      using j \<sigma>_y qj yj by (simp add: subst_compose)
  next
    case 2
    then obtain i r where i:"i < length ss" and r:"r \<in> poss (ss ! i)" "ps ! i @ r = qj" "\<tau>' yj = ss ! i |_ r" 
      by blast
    then have i2:"i < length rdp_A"
      by (simp add: length_renamed_lhs_\<alpha>s not_empty ss_def) 
    show ?thesis proof(cases i)
      case 0
      then have pi:"ps!i = pos_diff p1 p"
        unfolding ps_def by auto
      have "renamed_lhs_\<alpha>1 \<cdot> \<sigma> = s |_ p1 "
        by (metis "0" \<alpha>1p1 hd_conv_nth i2 length_0_conv length_renamed_lhs_\<alpha>s not_empty ren_lhs_\<alpha>1_alt renamed_lhs_\<alpha>i_\<sigma> snd_conv) 
      then have "ss ! i \<cdot> \<sigma> = s |_ p1 |_ (pos_diff q p)" 
        unfolding 0 by (metis diff_q_p_poss_renamed_\<alpha>1 nth_Cons_0 ss_def subt_at_subst)
      then have "(\<tau>' yj) \<cdot> \<sigma> = s |_ p1 |_ (pos_diff q p) |_ r" 
        unfolding r(3) by (metis r(1) subt_at_subst) 
      then show ?thesis
        by (smt (verit, best) \<alpha>1p1_in_rdpA append_eq_appendI append_self_conv order_pos.eq_refl order_pos.less_imp_le 
        overlapping_part.pi_poss overlapping_part_axioms p_def pi pq_pos_diff prefix_pos_diff q r(2) subst_compose_def subt_at_append)
    next
      case (Suc n)
      then have "ps!i = map (\<lambda>pi. pos_diff pi q) (map snd (tl rdp_A)) ! n"
        using ps_def by force
      with i have "ps!i = map (\<lambda>pi. pos_diff pi q) (map snd rdp_A) ! i"
        by (metis Suc hd_Cons_tl map_is_Nil_conv map_tl nth_Cons_Suc not_empty)
      with i have "ps!i = pos_diff (map snd rdp_A ! i) q"
        using i2 by auto
      moreover have "q \<le>\<^sub>p (map snd rdp_A ! i)" 
        using pi_below_q[OF i2] Suc i2 by (metis nth_map order_pos.less_le prod.collapse zero_less_Suc)
      ultimately have pi:"q @ (ps!i) = (map snd rdp_A ! i)"
        using prefix_pos_diff by presburger
      have "ss!i = renamed_lhs_\<alpha>s!i "
        using Suc i nth_tl ss_def by auto
      then have "ss ! i \<cdot> \<sigma> = s |_ ((map snd rdp_A) ! i)" 
        using renamed_lhs_\<alpha>i_\<sigma> i2  by (simp add: length_renamed_lhs_\<alpha>s)
      then have "(\<tau>' yj) \<cdot> \<sigma> = s |_ ((map snd rdp_A) ! i) |_ r" 
        unfolding r(3) by (metis r(1) subt_at_subst) 
      moreover have "((map snd rdp_A) ! i) @ r = q @ qj"
        using pi by (metis append_assoc r(2))
      ultimately show ?thesis
        by (metis i len_ss_ps nth_mem pi pos_append_poss poss_imp_subst_poss ps_in_poss_ren_\<beta> q ren_lhs_\<beta>_\<sigma> subst_compose subt_at_append)
    qed
  qed
qed

lemma renamed_lhs_\<beta>_\<tau>'_\<sigma>:
  assumes i:"i \<le> length ss" 
    and \<tau>':"\<tau>' = compose (drop i (map2 (\<lambda>x y. linear_unifier x (renamed_lhs_\<beta> |_ y)) ss ps))"
  shows "renamed_lhs_\<beta> \<cdot> (\<tau>' \<circ>\<^sub>s \<sigma>) = s|_q" 
proof-
  let ?ys="map source (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>)))"
  have length:"length (var_rule \<beta>) = length (var_poss_list (lhs \<beta>))"
    by (metis \<beta> length_var_poss_list length_var_rule) 
  have "(lhs \<beta>) \<cdot> \<langle>?ys\<rangle>\<^sub>\<beta>  = s|_q" 
    using B unfolding ll_single_redex_def using source_ctxt_apply_term
    by (smt (verit, best) context_source q replace_at_subt_at s(2) source.simps(3) source_to_pterm to_pterm_ctxt_of_pos_apply_term)
  then have "renamed_lhs_\<beta> \<cdot> (mk_subst Var (zip (vars_distinct renamed_lhs_\<beta>) ?ys)) = s|_q"
    using length mk_subst_rename[of "lhs \<beta>" ?ys] renameN(4) unfolding length_map renamed_lhs_\<beta>_def by metis
  with \<sigma>_\<tau>'_y[OF i \<tau>'] show ?thesis 
    using substitution_subterm_at by (metis q subt_at_append)
qed

lemma renamed_lhs_\<beta>_\<tau>_\<sigma>:
  shows "renamed_lhs_\<beta> \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) = s|_q" 
using renamed_lhs_\<beta>_\<tau>'_\<sigma>[of 0] using \<tau>_def tau tau.\<tau>_def by force 

lemma \<sigma>_\<tau>_x:
  assumes i:"i < length renamed_lhs_\<alpha>s" 
    and j:"j < length (vars_term_list (renamed_lhs_\<alpha>s!i))"
    and pi:"pi = snd (rdp_A ! i)" 
    and xj:"xj = vars_term_list (renamed_lhs_\<alpha>s!i)!j"
    and pj:"pj = var_poss_list (renamed_lhs_\<alpha>s!i)!j"
  shows "(\<tau> \<circ>\<^sub>s \<sigma>) xj = s|_(pi@pj)" 
proof- 
  let ?\<tau>'="compose (drop (Suc i) (map2 (\<lambda>x y. linear_unifier x (renamed_lhs_\<beta> |_ y)) ss ps))"
  from xj j have xj_vars_term:"xj \<in> vars_term (renamed_lhs_\<alpha>s!i)"
    using nth_mem by fastforce 
  show ?thesis proof(cases i)
    case 0
    then have at_i:"renamed_lhs_\<alpha>s ! i = renamed_lhs_\<alpha>1"
      using hd_conv_nth i ren_lhs_\<alpha>1_alt by force 
    from xj pj have x_at_pj:"renamed_lhs_\<alpha>1 |_ pj = Var xj"
      using at_i j vars_term_list_var_poss_list by auto
    have lin_lhs_\<alpha>1:"linear_term renamed_lhs_\<alpha>1"
      using "0" i lin_renamed_lhs_\<alpha>i ren_lhs_\<alpha>1_alt by auto 
    from 0 have ss_i:"ss!i = renamed_lhs_\<alpha>1 |_ (pos_diff q p)" 
      unfolding ss_def by simp
    show ?thesis proof(cases "pos_diff q p \<le>\<^sub>p pj")
      case True
      then obtain pj' where *:"(ss!i) |_ pj' = Var xj" "pj' \<in> poss (ss!i)" and pj':"pj = pos_diff q p @ pj'"
        unfolding ss_i using less_eq_pos_def x_at_pj
        by (metis at_i j length_var_poss_list nth_mem pj subterm_poss_conv var_poss_iff var_poss_list_sound)
      from * have 1:"xj \<in> vars_term (ss ! i)" 
        using vars_term_subt_at by fastforce 
      from * have 2:"pj' \<in> var_poss (ss ! i)"
        by (simp add: var_poss_iff) 
      consider "\<tau> xj = Var xj" | "pj' \<in> poss (renamed_lhs_\<beta> |_ (ps!i)) \<and> \<tau> xj = renamed_lhs_\<beta> |_ (ps!i) |_ pj' \<cdot> ?\<tau>'"
        using tau.apply_tau_ss_var[OF tau] * 0 1 2 \<tau>_def ss_def by fastforce
      then show ?thesis proof(cases)
        case 1
        then show ?thesis unfolding xj using \<sigma>_x
          by (metis (mono_tags, lifting) "0" \<alpha>1p1 eval_term.simps(1) hd_conv_nth i j pi pj not_empty snd_eqD subst_compose_def) 
      next
        case 2
        from renamed_lhs_\<beta>_\<tau>'_\<sigma> have "renamed_lhs_\<beta> \<cdot> (?\<tau>' \<circ>\<^sub>s \<sigma>) = s|_q"
          using Suc_le_eq 0 ss_def by simp 
        then have "renamed_lhs_\<beta> |_ (ps!i) |_ pj' \<cdot> (?\<tau>' \<circ>\<^sub>s \<sigma>) = s|_q |_ (ps!i) |_ pj'"
          by (smt (verit, best) "0" "2" length_nth_simps(2) nth_mem ps_def ps_in_poss_ren_\<beta> subt_at_subst zero_less_Suc)
        with 2 have "(\<tau> \<circ>\<^sub>s \<sigma>) xj = s|_q |_ (ps!i) |_ pj'" 
          by (metis (mono_tags, lifting) subst_compose subst_subst_compose) 
        moreover have "q @ (ps!i) @ pj' = pi @ pj" proof-
          have "pi = p1"
            by (metis "0" \<alpha>1p1 hd_conv_nth pi not_empty snd_conv)
          moreover have "q @ (pos_diff p1 p) = p1 @ (pos_diff q p)"
            by (metis order_pos.dual_order.strict_implies_order order_pos.order_refl p_def pq prefix_pos_diff self_append_conv)
          ultimately show ?thesis 
            unfolding pj' ps_def using "0" by auto 
        qed
        ultimately show ?thesis unfolding xj
          by (metis "0" \<alpha>1p1_in_rdpA nth_Cons_0 order_pos.dual_order.refl order_pos.less_imp_le p_def pi_poss prefix_pos_diff ps_def q self_append_conv subt_at_append subterm_poss_conv)  
      qed
    next
      case False
      have x_not_in_b:"xj \<notin> vars_term renamed_lhs_\<beta>" 
        using xj j unfolding at_i renamed_lhs_\<alpha>1_def renamed_lhs_\<beta>_def
        by (metis (mono_tags, lifting) Mgu_generic.renameN(1) disjoint_iff imageE length_map nth_map rangeI term.set_map(2) vars_map_vars_term)  
      have "xj \<notin> vars_term (ss!0)" 
        unfolding ss_def by (smt (verit, ccfv_SIG) "0" False at_i diff_q_p_poss_renamed_\<alpha>1 j length_var_poss_list less_eq_pos_simps(1) lin_lhs_\<alpha>1 
            linear_term_unique_vars nth_mem pj pos_append_poss ss_def ss_i subt_at_append var_poss_iff var_poss_list_sound vars_term_poss_subt_at x_at_pj) 
      moreover 
      {fix k assume k:"k < length ss" "k > 0" 
        have x:"xj \<in> vars_term renamed_lhs_\<alpha>1"
          using at_i xj_vars_term by auto 
        obtain u where u:"ss!k = map_vars_term (rename_many' ren k) u"
          using k renamed_lhs_\<alpha>i unfolding ss_def
          by (metis "0" Suc_diff_1 hd_Cons_tl i length_greater_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s nth_Cons_Suc) 
        from x have "xj \<notin> vars_term (ss!k)"  
          unfolding u renamed_lhs_\<alpha>1_def using k by (metis disjoint_iff not_gr_zero rename_many_disj) 
      }
      ultimately have "\<tau> xj = Var xj" 
        using tau.apply_tau_var[OF tau] using x_not_in_b \<tau>_def by auto
      then show ?thesis unfolding xj using \<sigma>_x[OF i]
        by (metis (no_types, lifting) "0" \<alpha>1p1 eval_term.simps(1) hd_conv_nth j pi pj not_empty snd_eqD subst_compose_def) 
    qed 
  next
    case (Suc n)
    with i have ss_i:"renamed_lhs_\<alpha>s!i = ss!i"
      unfolding renamed_lhs_\<alpha>s_def by (simp add: nth_tl renamed_lhs_\<alpha>s_def ss_def) 
    have 1:"xj \<in> vars_term (ss ! i)" 
      unfolding xj using j nth_mem ss_i by fastforce 
    have 2:"pj \<in> var_poss (ss ! i)"
      unfolding pj by (metis j length_var_poss_list nth_mem ss_i var_poss_list_sound) 
    have 3:"ss ! i |_ pj = Var xj"
      unfolding xj pj using j ss_i vars_term_list_var_poss_list by auto 
    consider "\<tau> xj = Var xj" | "pj \<in> poss (renamed_lhs_\<beta> |_ (ps!i)) \<and> \<tau> xj = renamed_lhs_\<beta> |_ (ps!i) |_ pj \<cdot> ?\<tau>'"
      using tau.apply_tau_ss_var[OF tau] 1 2 3 \<tau>_def i length_renamed_lhs_\<alpha>s not_empty ss_def by auto 
    then show ?thesis proof(cases)
      case 1
      then show ?thesis unfolding xj using \<sigma>_x[OF i]
        by (metis (mono_tags, opaque_lifting) eval_term.simps(1) j pi pj prod.collapse subst_compose)
    next
      case 2
      from renamed_lhs_\<beta>_\<tau>'_\<sigma> have "renamed_lhs_\<beta> \<cdot> (?\<tau>' \<circ>\<^sub>s \<sigma>) = s|_q"
        using Suc_le_eq i ss_def by auto 
      then have "renamed_lhs_\<beta> |_ (ps!i) |_ pj \<cdot> (?\<tau>' \<circ>\<^sub>s \<sigma>) = s|_q |_ (ps!i) |_ pj"
        by (smt (verit) "2" hd_Cons_tl i len_ss_ps length_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s nth_mem ps_in_poss_ren_\<beta> not_empty ss_def subt_at_subst)
      with 2 have "(\<tau> \<circ>\<^sub>s \<sigma>) xj = s|_q |_ (ps!i) |_ pj" 
        by (metis (mono_tags, lifting) subst_compose subst_subst_compose) 
      moreover have "ps!i = pos_diff pi q"
        unfolding Suc ps_def pi by (metis Suc Suc_less_eq hd_Cons_tl i length_map length_nth_simps(2) length_renamed_lhs_\<alpha>s nth_Cons_Suc nth_map not_empty) 
      ultimately show ?thesis unfolding xj pj
        by (metis Suc i length_renamed_lhs_\<alpha>s nth_mem pi pi_below_q pi_poss prod.collapse q subt_at_append subt_at_pos_diff zero_less_Suc)
    qed
  qed
qed

lemma renamed_lhs_\<alpha>_\<tau>_\<sigma>:
  assumes i:"i < length renamed_lhs_\<alpha>s"
    and pi:"pi = snd (rdp_A ! i)" 
  shows "renamed_lhs_\<alpha>s!i \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) = s|_pi" 
proof- 
  let ?\<alpha>i="fst (rdp_A ! i)"
  from i have elem:"(?\<alpha>i, pi) \<in> set (redex_patterns A)"
    using length_renamed_lhs_\<alpha>s pi rdp_A_subs_A by auto
  from i have "zip [0..<length rdp_A] (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A) ! i = (i, lhs ?\<alpha>i)" 
    by (simp add: length_renamed_lhs_\<alpha>s split_beta) 
  then have ren_i:"renamed_lhs_\<alpha>s!i = map_vars_term (rename_many' ren i) (lhs ?\<alpha>i)"
    using i length_renamed_lhs_\<alpha>s renamed_lhs_\<alpha>i by fastforce 
  show ?thesis 
    using source_subst_renamed_lhs[OF elem A_wf ren_i] \<sigma>_\<tau>_x[OF i] by (metis length_var_poss_list pi s(1))
qed

lemma l_\<tau>_\<sigma>:
  shows "l \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) = s|_p" 
proof- 
  from renamed_lhs_\<alpha>_\<tau>_\<sigma> have "renamed_lhs_\<alpha>1 \<cdot> (\<tau> \<circ>\<^sub>s \<sigma>) = s|_p1"
    unfolding ren_lhs_\<alpha>1_alt by (metis \<alpha>1p1 hd_conv_nth length_greater_0_conv length_renamed_lhs_\<alpha>s not_empty snd_conv)
  with renamed_lhs_\<beta>_\<tau>_\<sigma> show ?thesis unfolding l_def using p_def
    by (smt (verit, ccfv_SIG) ctxt_supt_id diff_q_p_poss_renamed_\<alpha>1 less_eq_pos_simps(1) less_eq_pos_simps(5) p_poss 
      pq_pos_diff replace_at_subt_at subst_apply_term_ctxt_apply_distrib subt_at.simps(1) subt_at_append subt_at_subst) 
qed

lemma B'_wf:"B' \<in> wf_pterm R" 
proof-
  have len:"length (var_rule \<beta>) = length (vars_term_list renamed_lhs_\<beta>)"
    using \<beta> unfolding renamed_lhs_\<beta>_def by (metis length_map length_var_rule vars_map_vars_term) 
  have "Prule \<beta> (map (to_pterm \<circ> \<tau>) (vars_term_list renamed_lhs_\<beta>)) \<in> wf_pterm R" 
    using wf_pterm.intros(3)[OF \<beta>] len by simp  
  then show ?thesis using ctxt_wf_pterm[OF to_pterm_wf_pterm[of "l \<cdot> \<tau>" R]] diff_q_p_poss_l
    unfolding B'_def by (simp add: to_pterm_subst)
qed

lemma p_above_pi:
  assumes i:"i < length rdp_A"
    and pi:"pi = snd (rdp_A ! i)" 
  shows "p \<le>\<^sub>p pi"
  by (metis (no_types, lifting) Suc_pred \<alpha>1p1 hd_conv_nth i length_greater_0_conv less_Suc_eq_0_disj 
   less_eq_pos_simps(1) order_pos.dual_order.strict_trans2 order_pos.order.strict_implies_order order_pos.order_refl 
   p_def pi pi_below_q pq_pos_diff prod.collapse not_empty snd_conv) 

lemma pos_diff_pi_p:
  assumes i:"i < length rdp_A"
    and pi:"pi = snd (rdp_A ! i)" 
  shows "pos_diff pi p \<in> poss l" 
proof(cases i)
  case 0
  then have p1:"pi = p1"
    by (metis \<alpha>1p1 hd_conv_nth pi not_empty snd_conv)
  then show ?thesis proof(cases "p = p1")
    case True
    with p1 show ?thesis
      by (metis empty_pos_in_poss order_pos.dual_order.refl prefix_pos_diff self_append_conv)
  next
    case False
    then have *:"p = q" 
      unfolding p_def by presburger 
    then have "pos_diff p1 q \<in> poss renamed_lhs_\<beta>"
      by (simp add: ps_def ps_in_poss_ren_\<beta>)
    with * show ?thesis unfolding l_def p1
      by (metis empty_pos_in_poss pq_pos_diff replace_at_subt_at self_append_conv subt_at.simps(1)) 
  qed
next
  case (Suc n)
  let ?\<alpha>i="fst (rdp_A ! i)"
  have pi_poss_s:"pi \<in> poss s"
    by (metis i nth_mem pi pi_poss prod.exhaust_sel) 
  show ?thesis proof(cases "p = p1")
    case True
    have "q \<le>\<^sub>p pi"
      using pi_below_q i Suc order_pos.less_le pi prod.collapse by blast
    then obtain r where r:"pi = q@r"
      using less_eq_pos_def by metis 
    have possL_B:"possL B = {q @ r |r. r \<in> fun_poss (lhs \<beta>)}"
      using single_redex_possL B \<beta> q by force 
    have "to_rule ?\<alpha>i \<in> R"
      by (metis \<alpha>i_in_R i nth_mem prod.exhaust_sel)
    then have possL_i:"possL (ll_single_redex s pi ?\<alpha>i) = {pi @ r |r. r \<in> fun_poss (lhs ?\<alpha>i)}"
      using single_redex_possL pi_poss_s by auto
    have "measure_ov (ll_single_redex s pi ?\<alpha>i) B \<noteq> 0"
      using overlap i pi by simp
    then obtain r1 r2 where "r1 \<in> fun_poss (lhs ?\<alpha>i)" "r2 \<in> fun_poss (lhs \<beta>)" "pi@r1 = q@r2"
      unfolding possL_B possL_i by (smt (verit, best) card.empty disjoint_iff mem_Collect_eq) 
    then have "r \<in> fun_poss (lhs \<beta>)" 
      unfolding r using fun_poss_append_poss' by auto 
    then show ?thesis
      by (smt (verit, best) \<open>q \<le>\<^sub>p pi\<close> append.assoc append_eq_append_conv diff_q_p_poss_renamed_\<alpha>1 fun_poss_imp_poss 
          hole_pos_ctxt_of_pos_term hole_pos_poss_conv l_def order_pos.order_trans p_def poss_map_vars_term pq pq_pos_diff prefix_pos_diff r renamed_lhs_\<beta>_def) 
  next 
    case False
    then have pq:"p = q" 
      unfolding p_def by presburger 
    from i have i':"i < length (map snd rdp_A)"
      unfolding length_map by simp
    from Suc i have "ps!i = map (\<lambda>pi. pos_diff pi q) (map snd rdp_A) ! i"
      unfolding ps_def by (simp add: nth_tl) 
    also have "... = pos_diff pi q"
      using i pi by fastforce 
    finally have "pos_diff pi p = ps!i"
      unfolding pq by simp
    then show ?thesis using tau.poss[OF tau] i
      unfolding l_def by (metis diff_q_p_poss_renamed_\<alpha>1 hd_Cons_tl len_ss_ps length_0_conv length_renamed_lhs_\<alpha>s nth_mem 
          pq pq_pos_diff not_empty ren_lhs_\<alpha>1_alt replace_at_subt_at self_append_conv ss_def subt_at.simps(1)) 
  qed
qed

lemma As'_As:
  assumes i:"i < length rdp_A"
  shows "replace_at (to_pterm s) p (As'!i \<cdot> (to_pterm \<circ> \<sigma>)) = As!i"
proof-
  obtain pi \<alpha>i where redex_i:"(\<alpha>i, pi) = rdp_A!i"
    by (metis surj_pair) 
  with i have As_i:"As!i = ll_single_redex s pi \<alpha>i" 
    unfolding As by (metis case_prod_conv nth_map)  
  have pi:"p \<le>\<^sub>p pi" 
    using p_above_pi by (metis i redex_i snd_conv) 
  have pi_poss_s:"pi \<in> poss s"
    by (metis i nth_mem pi_poss redex_i)
  from i have pos_diff_pi_p':"pos_diff pi p \<in> poss (to_pterm (l \<cdot> \<tau>))"
    by (metis pos_diff_pi_p redex_i snd_conv p_in_poss_to_pterm poss_imp_subst_poss) 
  from pi have p_pi:"p @ pos_diff pi p = pi" by simp
  have A'_sigma:"As'!i \<cdot> (to_pterm \<circ> \<sigma>) = (ctxt_of_pos_term (pos_diff pi p) ((to_pterm s)|_p)) \<langle>As!i|_pi\<rangle>" proof-
    from i redex_i have zip1:"zip rdp_A [0..<length rdp_A] ! i = ((\<alpha>i, pi), i)" by simp
    then have A'_i:"As'!i = replace_at (to_pterm (l \<cdot> \<tau>)) (pos_diff pi p) (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))"
      using i As'_def by fastforce 
    have lhs_at_i:"renamed_lhs_\<alpha>s!i = map_vars_term (rename_many' ren i) (lhs \<alpha>i)"
      using renamed_lhs_\<alpha>i redex_i by (metis fst_conv i)
    moreover have lin_lhs:"linear_term (renamed_lhs_\<alpha>s!i)"
      by (simp add: i length_renamed_lhs_\<alpha>s lin_renamed_lhs_\<alpha>i) 
    ultimately have len:"length (var_rule \<alpha>i) = length (vars_term_list (renamed_lhs_\<alpha>s!i))"
      by (metis fst_eqD i length_map linear_term_var_vars_term_list overlapping_part.lin_lhs_\<alpha>i overlapping_part_axioms redex_i vars_map_vars_term)
    then have len2:"length (var_rule \<alpha>i) = length (var_poss_list (renamed_lhs_\<alpha>s!i))"
      by (simp add: length_var_poss_list)
    have var_poss_list:"var_poss_list (rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A) ! i) = var_poss_list (lhs \<alpha>i)"
      using lhs_at_i var_poss_list_map_vars_term renamed_lhs_\<alpha>s_def by auto
    let ?xs1="map (\<lambda>s. s \<cdot> (to_pterm \<circ> \<sigma>)) (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))"
    let ?xs2="map (to_pterm \<circ> (\<lambda>p'. s |_ (pi @ p'))) (var_poss_list (renamed_lhs_\<alpha>s!i))"
    {fix j assume j:"j < length (var_rule \<alpha>i)" 
      let ?x="map (rename_many' ren i) (var_rule \<alpha>i)!j" 
      have "?x = vars_term_list (renamed_lhs_\<alpha>s!i)!j" 
        using lhs_at_i by (metis fst_conv i lin_lhs_\<alpha>i linear_term_var_vars_term_list redex_i vars_map_vars_term)
      with j have *:"to_pterm (\<tau> ?x) \<cdot> (to_pterm \<circ> \<sigma>) = to_pterm (s|_(pi @ var_poss_list (renamed_lhs_\<alpha>s!i)!j))"
        using \<sigma>_\<tau>_x[of i j] i redex_i unfolding length_map len by (metis length_renamed_lhs_\<alpha>s snd_conv subst_compose to_pterm_subst) 
      then have "?xs1 ! j = ?xs2 ! j"
        using j len2 by force
    }
    then have "?xs1 = ?xs2"
      using len2 list_eq_iff_nth_eq[of ?xs1 ?xs2] unfolding length_map by simp
    then have "Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))) \<cdot> (to_pterm \<circ> \<sigma>) = Prule \<alpha>i ?xs2"
      unfolding eval_term.simps by simp
    then have *:"Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))) \<cdot> (to_pterm \<circ> \<sigma>) = As!i|_pi" 
      unfolding As_i unfolding ll_single_redex_def var_poss_list using pi_poss_s
      by (simp add: p_in_poss_to_pterm renamed_lhs_\<alpha>s_def replace_at_subt_at var_poss_list)
    have "to_pterm (l \<cdot> \<tau>) \<cdot> (to_pterm \<circ> \<sigma>) = to_pterm s |_ p" 
      using l_\<tau>_\<sigma> by (metis ctxt_eq ctxt_supt_id p_in_poss_to_pterm p_poss subst_subst_compose to_pterm_ctxt_of_pos_apply_term to_pterm_subst)
    then show ?thesis 
      unfolding A'_i unfolding subst_apply_term_ctxt_apply_distrib ctxt_of_pos_term_subst[OF pos_diff_pi_p', symmetric] * by simp
  qed 
  show ?thesis
    unfolding As_i A'_sigma using ctxt_apply_ctxt_apply p_poss p_pi
    by (metis (no_types, lifting) ctxt_supt_id ll_single_redex_def p_in_poss_to_pterm pi_poss_s replace_at_subt_at)
qed

lemma As'_wf:
  assumes "Ai' \<in> set As'"
  shows "Ai' \<in> wf_pterm R"
proof-
  obtain j where "j < length As'" and a:"As'!j = Ai'"
    by (metis assms in_set_idx) 
  then have j:"j < length rdp_A" 
    unfolding As'_def length_map length_zip by simp
  have "As!j = replace_at (to_pterm s) p (Ai' \<cdot> (to_pterm \<circ> \<sigma>))"
    using As'_As[OF j] a by force
  then have "replace_at (to_pterm s) p (Ai' \<cdot> (to_pterm \<circ> \<sigma>)) \<in> wf_pterm R" 
    using As_i_wf As j by (metis length_map nth_mem)
  then have "Ai' \<cdot> (to_pterm \<circ> \<sigma>) \<in> wf_pterm R" 
    using subt_at_is_wf_pterm p_poss by (metis hole_pos_poss subt_at_hole_pos)
  then show ?thesis
    using subst_imp_well_def by auto
qed

lemma unifier:"\<exists>ts. unify (zip ss (map ((|_) renamed_lhs_\<beta>) ps)) [] = Some ts" 
proof-
  {fix i assume i:"i < length (zip ss (map ((|_) renamed_lhs_\<beta>) ps))" 
    have "ss ! i \<cdot> \<sigma> = (map ((|_) renamed_lhs_\<beta>) ps)!i \<cdot> \<sigma>" 
    proof(cases i)
      case 0
      have "renamed_lhs_\<beta> |_ (pos_diff p1 p) \<cdot> \<sigma> = s |_ (q @ (pos_diff p1 p))" 
        using ren_lhs_\<beta>_\<sigma> by (metis list.set_intros(1) ps_def q subt_at_append subt_at_subst tau tau.poss)  
      moreover have "renamed_lhs_\<alpha>1 |_ pos_diff q p \<cdot> \<sigma> = s |_ (p1 @ pos_diff q p)" 
        using renamed_lhs_\<alpha>i_\<sigma> by (metis \<alpha>1p1 \<alpha>1p1_in_rdpA diff_q_p_poss_renamed_\<alpha>1 fst_conv hd_conv_nth length_pos_if_in_set 
        length_renamed_lhs_\<alpha>s pi_poss not_empty renamed_lhs_\<alpha>1_def renamed_lhs_\<alpha>i snd_conv subt_at_append subt_at_subst) 
      ultimately have "renamed_lhs_\<alpha>1 |_ pos_diff q p \<cdot> \<sigma> = renamed_lhs_\<beta> |_ (pos_diff p1 p) \<cdot> \<sigma>"
        by (metis order_pos.dual_order.refl order_pos.dual_order.strict_implies_order p_def pq prefix_pos_diff self_append_conv) 
      then show ?thesis unfolding ss_def ps_def 0 by simp
    next
      case (Suc n)
      have ssi:"ss!i = renamed_lhs_\<alpha>s ! i" 
        unfolding Suc by (metis hd_Cons_tl length_0_conv length_renamed_lhs_\<alpha>s nth_Cons_Suc not_empty ss_def) 
      from i have i':"i < length (rdp_A)"
        by (simp add: length_renamed_lhs_\<alpha>s not_empty ss_def) 
      then have psi:"ps ! i = (pos_diff (snd (rdp_A ! i)) q)" 
        unfolding Suc ps_def by (simp add: nth_tl)
      from i have i:"i < length ps"
        by simp 
      with psi have "(map ((|_) renamed_lhs_\<beta>) ps)!i \<cdot> \<sigma> = s |_ (snd (rdp_A ! i))" 
        using ren_lhs_\<beta>_\<sigma> ps_in_poss_ren_\<beta> unfolding nth_map[OF i]
        by (metis Suc i' nth_mem pi_below_q prod.exhaust_sel q subt_at_pos_diff subt_at_subst zero_less_Suc) 
      with ssi show ?thesis
        using renamed_lhs_\<alpha>i_\<sigma> i' length_renamed_lhs_\<alpha>s by presburger
    qed
  }
  then have "\<sigma> \<in> unifiers (set (zip ss (map ((|_) renamed_lhs_\<beta>) ps)))" 
    unfolding unifiers_def by (smt (verit, del_insts) in_set_zip len_ss_ps length_map map_snd_zip mem_Collect_eq) 
  then show ?thesis 
    using ex_unify_if_unifiers_not_empty by blast 
qed

(*Step 6*)
lemma unifier_no_conflict:
  assumes i:"i < j" and j:"j < length ps" 
    and not_orth:"\<not> (ps ! i @ r) \<bottom> ps ! j" 
    and r:"r \<in> var_poss (renamed_lhs_\<beta> |_ (ps ! i))" 
  shows "r \<notin> fun_poss (ss ! i)"
proof
  assume r2:"r \<in> fun_poss (ss ! i)"
  obtain \<alpha>i pi where \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i"
    by (meson prod.collapse) 
  with i j have \<alpha>ipi_in_rdp:"(\<alpha>i, pi) \<in> set rdp_A"
    using len_ss_ps length_renamed_lhs_\<alpha>s ss_def by auto 
  obtain \<Delta>i where \<Delta>i:"\<Delta>i = ll_single_redex s pi \<alpha>i"
    by simp 
  then have possLi:"possL \<Delta>i = {pi @ r |r. r \<in> fun_poss (lhs \<alpha>i)}" 
    using single_redex_possL using \<alpha>i_in_R \<alpha>ipi_in_rdp pi_poss by blast 
  obtain \<alpha>j pj where \<alpha>jpj:"(\<alpha>j, pj) = rdp_A ! j"
    by (meson prod.collapse) 
  with j have \<alpha>jpj_in_rdp:"(\<alpha>j, pj) \<in> set rdp_A"
    using len_ss_ps length_renamed_lhs_\<alpha>s ss_def by (simp add: not_empty)
  have is_fun:"is_Fun (lhs \<alpha>j)"
    using \<alpha>i_in_R \<alpha>jpj_in_rdp no_var_lhs by blast 
  have ps_j:"ps ! j = pos_diff pj q" using \<alpha>jpj i j unfolding ps_def
    by (smt (verit, best) Suc_less_eq length_map length_nth_simps(2) less_imp_Suc_add list.sel(3) nth_map nth_tl snd_conv)  
  obtain \<Delta>j where \<Delta>j:"\<Delta>j = ll_single_redex s pj \<alpha>j"
    by simp 
  then have possLj:"possL \<Delta>j = {pj @ r |r. r \<in> fun_poss (lhs \<alpha>j)}" 
    using single_redex_possL using \<alpha>i_in_R \<alpha>jpj_in_rdp pi_poss by blast  
  have src:"source \<Delta>j = s"
    unfolding \<Delta>j using \<alpha>jpj_in_rdp source_single_step
    by (metis (no_types, lifting) A_wf filter_set list.set_map member_filter pair_imageI rdp_A s(1)) 
  have "measure_ov \<Delta>j B = 0" proof(cases i)
    case 0
    then have p1:"pi = p1" 
      using \<alpha>ipi by (metis \<alpha>1p1 hd_conv_nth not_empty snd_eqD) 
    have ps_i:"ps ! i = pos_diff p1 p" 
      unfolding 0 ps_def by simp
    then have p_pi:"pi = p @ ps ! i"
      using p1 order_pos.dual_order.refl order_pos.less_imp_le p_def prefix_pos_diff by presburger
    from not_orth have not_orth:"\<not> (pi @ pos_diff q p @ r) \<bottom> pj"
      unfolding ps_i ps_j p1
      by (smt (verit) "0" \<alpha>jpj append_assoc i j len_ss_ps length_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s 
          less_eq_pos_simps(2) list.exhaust_sel order_pos.dual_order.strict_implies_order p1 p_def p_pi parallel_pos pi_below_q 
          pq_pos_diff prefix_pos_diff ps_i not_empty self_append_conv ss_def)
    then have "\<not> pi \<bottom> pj"
      by (meson less_eq_pos_simps(1) order_pos.dual_order.trans parallel_pos pos_less_eq_append_not_parallel)
    then have below:"pi <\<^sub>p pj" 
      using i j \<alpha>ipi \<alpha>jpj order_rdp_A
      by (metis One_nat_def Suc_pred \<alpha>jpj_in_rdp len_ss_ps length_nth_simps(2) length_pos_if_in_set length_renamed_lhs_\<alpha>s length_tl parallel_pos_sym pos_cases ss_def) 
    then obtain p' where p':"pj = pi @ p'"
      by (meson less_pos_def')  
    have "\<Delta>i \<noteq> \<Delta>j" 
      unfolding \<Delta>i \<Delta>j using below by (metis Pair_inject \<alpha>ipi_in_rdp \<alpha>jpj_in_rdp order_pos.less_le pi_poss single_redex_neq) 
    then have \<Delta>ij:"measure_ov \<Delta>i \<Delta>j = 0"
      using single_steps_measure unfolding \<Delta>i \<Delta>j using \<alpha>ipi_in_rdp \<alpha>jpj_in_rdp
      by (smt (verit, ccfv_SIG) A_wf list.set_map pair_imageI rdp_A_subs_A s(1) subsetD) 
    {fix r' assume r':"pi @ pos_diff q p @ r @ r' \<in> poss s" 
      have possL_B:"possL B = {q @ q' | q'. q' \<in> fun_poss (lhs \<beta>)}"
        by (simp add: B \<beta> q single_redex_possL) 
      have "ps ! i \<in> poss (lhs \<beta>)"
        using i j ps_in_poss_ren_\<beta> renamed_lhs_\<beta>_def by force 
      then have "(ps ! i) @ r @ r' \<notin> fun_poss (lhs \<beta>)" 
        using r unfolding renamed_lhs_\<beta>_def by (metis append.right_neutral fun_poss_fun_conv fun_poss_imp_poss 
        fun_poss_map_vars_term subterm_poss_conv term.distinct(1) var_pos_maximal var_poss_iff) 
      then have "pi @ pos_diff q p @ r @ r' \<notin> possL B" 
        unfolding p_pi possL_B by (smt (verit, ccfv_SIG) append_assoc mem_Collect_eq p1 p_def p_pi pq_pos_diff same_append_eq) 
    }note possL_B=this
    from r2 have "pos_diff q p @ r \<in> fun_poss renamed_lhs_\<alpha>1"
      by (metis "0" diff_q_p_poss_renamed_\<alpha>1 fun_poss_fun_conv fun_poss_imp_poss is_FunI nth_Cons_0 poss_append_poss poss_is_Fun_fun_poss ss_def subt_at_append) 
    then have "pos_diff q p @ r \<in> fun_poss (lhs \<alpha>i)" 
      using \<alpha>ipi 0 by (metis \<alpha>1p1 fst_conv fun_poss_map_vars_term hd_conv_nth not_empty renamed_lhs_\<alpha>1_def) 
    then have pi:"pi @ pos_diff q p @ r \<in> possL \<Delta>i" 
      unfolding possLi p1 by simp
    {assume "pj \<le>\<^sub>p pi @ pos_diff q p @ r" 
      then obtain p'' where p'':"pj @ p'' = pi @ pos_diff q p @ r"
        by (meson prefix_pos_diff) 
      then have r:"pos_diff q p @ r = p' @ p''" 
        unfolding p' by simp
      have pj:"pj \<in> possL \<Delta>j" 
        unfolding possLj using is_fun by (simp add: poss_is_Fun_fun_poss)
      from pi have "pj \<in> possL \<Delta>i" 
        unfolding possLi p' p'' p1 using fun_poss_append_poss' r by auto
      with pj have False 
        using \<Delta>ij by (simp add: disjoint_iff finite_labelposs)
    }
    then have "pi @ pos_diff q p @ r <\<^sub>p pj"
      using not_orth order_pos.less_le pos_cases by auto 
    then show ?thesis using possLj possL_B src 
      by (smt (verit, ccfv_SIG) append.assoc card.empty disjoint_iff_not_equal mem_Collect_eq 
      order_pos.dual_order.strict_implies_order possL_subset_poss_source prefix_pos_diff subsetD)
  next
    case (Suc n)
    have ps_i:"ps ! i = pos_diff pi q" 
      using \<alpha>ipi i j unfolding ps_def Suc
      by (metis Suc_lessD Suc_less_SucD hd_Cons_tl length_map length_nth_simps(2) less_trans_Suc nth_Cons_Suc nth_map not_empty snd_conv) 
    then have q_pi:"q @ (ps ! i) = pi"
      by (metis (mono_tags, lifting) Suc \<alpha>ipi hd_Cons_tl i j len_ss_ps length_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s 
          order.strict_trans order_pos.less_imp_le pi_below_q prefix_pos_diff not_empty ss_def zero_less_Suc)
    from not_orth have not_orth:"\<not> (pi@r) \<bottom> pj"
      unfolding ps_i ps_j by (smt (verit, ccfv_SIG) Suc \<alpha>ipi \<alpha>jpj append.assoc i j len_ss_ps length_0_conv length_nth_simps(2) length_renamed_lhs_\<alpha>s 
      less_eq_pos_simps(2) list.exhaust_sel order.strict_trans order_pos.le_less parallel_pos pi_below_q prefix_pos_diff not_empty ss_def zero_less_Suc) 
    then have "\<not> pi \<bottom> pj"
      by (metis less_eq_pos_simps(1) order_pos.order.trans parallel_pos pos_less_eq_append_not_parallel) 
    then have below:"pi <\<^sub>p pj" 
      using i j \<alpha>ipi \<alpha>jpj order_rdp_A
      by (metis len_ss_ps length_0_conv length_renamed_lhs_\<alpha>s list.collapse list.size(4) not_empty parallel_pos_sym pos_cases ss_def)
    then obtain p' where p':"pj = pi @ p'"
      by (meson less_pos_def')  
    have "\<Delta>i \<noteq> \<Delta>j" 
      unfolding \<Delta>i \<Delta>j using below by (metis Pair_inject \<alpha>ipi_in_rdp \<alpha>jpj_in_rdp order_pos.less_le pi_poss single_redex_neq) 
    then have \<Delta>ij:"measure_ov \<Delta>i \<Delta>j = 0"
      using single_steps_measure unfolding \<Delta>i \<Delta>j using \<alpha>ipi_in_rdp \<alpha>jpj_in_rdp
      by (smt (verit, ccfv_SIG) A_wf list.set_map pair_imageI rdp_A_subs_A s(1) subsetD) 
    {fix r' assume r':"pi @ r @ r' \<in> poss s" 
      have possL_B:"possL B = {q @ q' | q'. q' \<in> fun_poss (lhs \<beta>)}"
        by (simp add: B \<beta> q single_redex_possL) 
      have "ps ! i \<in> poss (lhs \<beta>)"
        using i j ps_in_poss_ren_\<beta> renamed_lhs_\<beta>_def by force 
      then have "(ps ! i) @ r @ r' \<notin> fun_poss (lhs \<beta>)" 
        using r unfolding renamed_lhs_\<beta>_def  by (metis append.right_neutral fun_poss_fun_conv fun_poss_imp_poss 
        fun_poss_map_vars_term subterm_poss_conv term.distinct(1) var_pos_maximal var_poss_iff) 
      then have "pi @ r @ r' \<notin> possL B" 
        unfolding q_pi[symmetric] possL_B by simp
    }note possL_B=this
    from r2 have "r \<in> fun_poss (renamed_lhs_\<alpha>s ! i)" 
      unfolding ss_def by (metis Suc hd_Cons_tl length_0_conv length_renamed_lhs_\<alpha>s nth_Cons_Suc not_empty)
    then have "r \<in> fun_poss (lhs \<alpha>i)" 
      using \<alpha>ipi by (metis Suc_diff_1 Suc_lessD \<alpha>1p1_in_rdpA fst_conv fun_poss_map_vars_term i j len_ss_ps 
          length_nth_simps(2) length_pos_if_in_set length_renamed_lhs_\<alpha>s length_tl less_trans_Suc renamed_lhs_\<alpha>i ss_def) 
    then have pi:"pi @ r \<in> possL \<Delta>i" 
      unfolding possLi by simp
    {assume "pj \<le>\<^sub>p pi @ r" 
      then obtain p'' where p'':"pj @ p'' = pi @ r"
        by (meson prefix_pos_diff) 
      then have r:"r = p' @ p''" 
        unfolding p' by simp
      have pj:"pj \<in> possL \<Delta>j" 
        unfolding possLj using is_fun by (simp add: poss_is_Fun_fun_poss)
      from pi have "pj \<in> possL \<Delta>i" 
        unfolding possLi p' p'' r using fun_poss_append_poss' by blast  
      with pj have False 
        using \<Delta>ij by (simp add: disjoint_iff finite_labelposs)
    }
    then have "pi @ r <\<^sub>p pj"
      using not_orth order_pos.less_le pos_cases by auto 
    then show ?thesis using possLj possL_B src
      by (smt (verit, ccfv_SIG) append.assoc card.empty disjoint_iff_not_equal mem_Collect_eq 
      order_pos.dual_order.strict_implies_order possL_subset_poss_source prefix_pos_diff subsetD)
  qed
  then show False 
    using overlap[OF \<alpha>jpj_in_rdp \<Delta>j] by simp
qed

lemma tau_is_mgu:
  shows "is_mgu \<tau> (set (map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s (map (\<lambda>(\<alpha>i, pi). pos_diff pi p) rdp_A)))"
proof-
  let ?q="pos_diff q p" 
  let ?p="pos_diff p1 p"
  let ?ps="map (\<lambda>(\<alpha>i, pi). pos_diff pi p) rdp_A"
  obtain ss' where ss':"unify (zip ss (map ((|_) renamed_lhs_\<beta>) ps)) [] = Some ss'" 
    using unifier by blast
  have "unify (map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s ?ps) [] = unify (zip ss (map ((|_) renamed_lhs_\<beta>) ps)) []" 
  proof-
    let ?zips1="map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s ?ps" 
    let ?zips2="zip ss (map ((|_) renamed_lhs_\<beta>) ps)" 
    have ctxt2:"l |_ ?p = replace_at renamed_lhs_\<alpha>1 ?q (renamed_lhs_\<beta> |_ pos_diff p1 p)"
      using  l_def by (metis empty_pos_in_poss order_pos.dual_order.refl p_def prefix_pos_diff replace_at_subt_at self_append_conv subt_at.simps(1))
    obtain tl1 where tl1:"renamed_lhs_\<alpha>s = renamed_lhs_\<alpha>1 # tl1" "tl1 = (tl renamed_lhs_\<alpha>s)"
      by (metis hd_Cons_tl length_0_conv length_renamed_lhs_\<alpha>s not_empty ren_lhs_\<alpha>1_alt) 
    obtain tl2 where tl2:"?ps = pos_diff p1 p # tl2" "tl2 = tl ?ps"
      using list.collapse[OF not_empty] unfolding \<alpha>1p1[symmetric] by (smt (verit, best) Cons_eq_map_conv case_prod_conv map_tl)
    have len:"length ?ps = length ps" 
      unfolding ps_def by (simp add: not_empty)
    {fix i assume i:"i < length rdp_A" "i > 0"
      then obtain j where j:"i = Suc j"
        using not0_implies_Suc by blast 
      let ?pi="map snd rdp_A ! i"
      obtain pi where pi:"pi = ?ps ! i" 
        by simp
      with i have pi_pos_diff:"pi = pos_diff ?pi p" 
        unfolding nth_map[OF i(1)] by (metis case_prod_conv prod.collapse)
      obtain pi' where pi':"pi' = ps ! i" 
        by simp
      from i(1) have pi'':"pi' = pos_diff ?pi q" 
        unfolding pi' ps_def j using tl2(1) by force 
      have "q \<le>\<^sub>p ?pi" 
        using pi_below_q[OF i] by (metis eq_snd_iff i(1) nth_map order_pos.le_less)
      then have "pi = (pos_diff q p) @ pi'" 
        unfolding pi'' pi_pos_diff by (metis append.assoc less_eq_pos_simps(1) pq_pos_diff prefix_pos_diff same_append_eq) 
      then have "l |_ pi =  renamed_lhs_\<beta> |_ pi'"
        unfolding l_def by (simp add: diff_q_p_poss_renamed_\<alpha>1 replace_at_below_poss replace_at_subt_at)
      then have "map ((|_) l) ?ps ! i = map ((|_) renamed_lhs_\<beta>) ps ! i"
        using i(1) len pi pi' by auto
    }
    then have "tl (map ((|_) l) ?ps) = tl (map ((|_) renamed_lhs_\<beta>) ps)" 
      using list_tl_eq not_empty len by (metis length_map)
    then have tl_zips:"tl ?zips1 = tl ?zips2" 
      unfolding tl1(1) tl2(1) ss_def ps_def zip_Cons_Cons list.map list.sel(3)
      using tl1(2) by (metis zip_map2)
    have "?zips1 = (renamed_lhs_\<alpha>1, l |_ ?p) # (tl ?zips1)"
      unfolding tl1(1) tl2(1) list.map zip_Cons_Cons by simp
    then have *:"?zips1 = (renamed_lhs_\<alpha>1, l |_ ?p) # (tl ?zips2)"
      using tl_zips by simp 
    show ?thesis using unify_ctxt_same unfolding * ss_def ps_def list.map zip_Cons_Cons list.sel(3) unfolding ctxt2
      by (metis diff_q_p_poss_renamed_\<alpha>1 replace_at_ident)
  qed
  then have "unify (map2 (\<lambda>x y. (x, l |_ y)) renamed_lhs_\<alpha>s ?ps) [] = Some ss'" 
    unfolding ss' by simp
  moreover have "\<tau> = subst_of ss'"
    using tau.tau_is_unifier[OF tau ss'] unifier_no_conflict unfolding \<tau>_def by blast 
  ultimately show ?thesis 
    by (metis is_imgu_imp_is_mgu unify_sound) 
qed


lemma fun_poss_l_tau:
  assumes r:"r \<in> fun_poss (l \<cdot> \<tau>)" 
  shows "p@r \<in> possL B \<or> (\<exists>A \<in> set As. p@r \<in> possL A)" 
proof(cases "r \<in> fun_poss l")
 case True
  then show ?thesis proof(cases "pos_diff q p \<le>\<^sub>p r")
    case True
    with \<open>r \<in> fun_poss l\<close> have "pos_diff r (pos_diff q p) \<in> fun_poss renamed_lhs_\<beta>"
      unfolding l_def by (metis diff_q_p_poss_renamed_\<alpha>1 fun_poss_in_ctxt hole_pos_ctxt_of_pos_term prefix_pos_diff) 
    then show ?thesis
      by (smt (verit, del_insts) B True \<beta> append.assoc fun_poss_map_vars_term mem_Collect_eq pq_pos_diff prefix_pos_diff q renamed_lhs_\<beta>_def single_redex_possL)
  next
    case False
    with \<open>r \<in> fun_poss l\<close> have "r \<in> fun_poss renamed_lhs_\<alpha>1"  
      unfolding l_def using diff_q_p_poss_renamed_\<alpha>1 replace_at_fun_poss_not_below by auto 
    then have "p@r \<in> possL (ll_single_redex s p1 \<alpha>1)"
      by (metis (mono_tags, lifting) False \<alpha>1p1_in_rdpA \<alpha>i_in_R append_self_conv fun_poss_map_vars_term less_eq_pos_code(1) 
          mem_Collect_eq overlapping_part.p_def overlapping_part_axioms pi_poss pq_pos_diff renamed_lhs_\<alpha>1_def single_redex_possL)
    then have "p@r \<in> possL (hd As)"
      by (metis As case_prod_conv hd_map overlapping_part.\<alpha>1p1 overlapping_part_axioms not_empty) 
    then show ?thesis
      using As not_empty hd_in_set by blast
  qed
next
  case False
  with r obtain r' where r':"r = (pos_diff q p) @ r'" and "r' \<in> fun_poss (renamed_lhs_\<beta> \<cdot> \<tau>)" 
    unfolding l_\<tau> using diff_q_p_poss_renamed_\<alpha>1 fun_poss_ctxt_apply_term hole_pos_ctxt_of_pos_term l_def by metis
  with False obtain r1 r2 y where r1:"renamed_lhs_\<beta>|_r1 = Var y" "r1 \<in> poss renamed_lhs_\<beta>" and r2:"r2 \<in> fun_poss (\<tau> y)" and r1r2:"r' = r1@r2"
    by (smt (verit, best) diff_q_p_poss_renamed_\<alpha>1 fun_poss_fun_conv fun_poss_imp_poss hole_pos_ctxt_of_pos_term hole_pos_poss is_FunI l_def 
        poss_append_poss poss_is_Fun_fun_poss poss_subst_choice replace_at_subt_at subt_at_append)
  from r1 have r1_poss:"r1 \<in> var_poss renamed_lhs_\<beta>"
    using var_poss_iff by blast 
  then obtain i r'' where i:"i < length ss" and ps_i:"ps ! i @ r'' = r1" "r'' \<in> poss (ss ! i)" "\<tau> y = ss ! i |_ r''"
    using tau.apply_tau_t_var'[OF tau r1_poss r1(1)] \<tau>_def r2 by auto
  with r2 have fun_poss:"r''@r2 \<in> fun_poss (ss!i)"
    by (smt (verit) fun_poss_fun_conv fun_poss_imp_poss is_FunI poss_append_poss poss_is_Fun_fun_poss subt_at_append)
  have poss:"r' = ps!i @ r'' @ r2" 
    using ps_i(1) r1r2 by simp
  have "p@r \<in> possL (As!i)" proof(cases i)
    case 0
    then have p0:"ps!i = pos_diff p1 p" unfolding ps_def by simp
    with poss have poss:"r' = pos_diff p1 p @ r'' @ r2" 
      by simp
    have "p@r \<in> possL (ll_single_redex s p1 \<alpha>1)" proof(cases "q <\<^sub>p p1")
      case True
      then have p:"p = q" unfolding p_def by simp
      from fun_poss have "r''@r2 \<in> fun_poss (lhs \<alpha>1)" 
        unfolding 0 p using fun_poss_map_vars_term p pq_pos_diff by (metis nth_Cons_0 renamed_lhs_\<alpha>1_def self_append_conv ss_def subt_at.simps(1)) 
      then show ?thesis unfolding p r' poss
        by (smt (verit, best) True \<alpha>1p1_in_rdpA \<alpha>i_in_R append_assoc mem_Collect_eq order_pos.dual_order.strict_implies_order p pi_poss pq_pos_diff prefix_pos_diff single_redex_possL)
    next
      case False
      then have p:"p = p1" unfolding p_def by simp
      from fun_poss have "r \<in> fun_poss (lhs \<alpha>1)"
        unfolding 0 p r' poss
        by (metis append_eq_append_conv2 diff_q_p_poss_renamed_\<alpha>1 fun_poss_fun_conv fun_poss_imp_poss fun_poss_map_vars_term nth_Cons_0 
            order_pos.dual_order.refl p pos_append_poss poss_is_Fun_fun_poss prefix_pos_diff renamed_lhs_\<alpha>1_def self_append_conv ss_def subt_at_append term.disc(2))
      then show ?thesis 
        using \<alpha>1p1_in_rdpA \<alpha>i_in_R p p_def p_poss single_redex_possL by force 
    qed
    then have "p@r \<in> possL (hd As)"
      by (metis As case_prod_conv hd_map overlapping_part.\<alpha>1p1 overlapping_part_axioms not_empty) 
    then show ?thesis
      by (simp add: "0" As not_empty hd_conv_nth)
  next
    case (Suc n)
    from i have i':"i < length ps"
      using length_renamed_lhs_\<alpha>s len_ss_ps by force 
    let ?pi="snd (rdp_A ! i)" and ?\<alpha>i="fst (rdp_A ! i)"
    have red_i:"(?\<alpha>i, ?pi) = rdp_A ! i" by simp
    have i'':"i < length rdp_A"
      using i length_renamed_lhs_\<alpha>s not_empty ss_def by fastforce
    then have \<alpha>i:"to_rule ?\<alpha>i \<in> R"
      by (metis \<alpha>i_in_R nth_mem red_i)
    from i' have pi:"ps!i = pos_diff ?pi q" 
      unfolding Suc nth_Cons_Suc ps_def by (simp add: nth_tl)
    have poss:"p@r = ?pi @ r'' @ r2" 
      unfolding r' pi poss
      by (metis Suc append_assoc i'' order_pos.dual_order.strict_implies_order pi_below_q pq_pos_diff prefix_pos_diff red_i zero_less_Suc)
    have ss_i:"ss ! i = renamed_lhs_\<alpha>s ! i" 
      using Suc i nth_tl ss_def by auto
    then have "r2 \<in> fun_poss (renamed_lhs_\<alpha>s ! i |_r'')" 
      using r2(1) ps_i(3) by auto
    then have "r'' @ r2 \<in> fun_poss (renamed_lhs_\<alpha>s ! i)"
      using ss_i fun_poss by presburger 
    then have "r''@ r2 \<in> fun_poss (lhs ?\<alpha>i)"
      by (simp add: fun_poss_map_vars_term i'' length_renamed_lhs_\<alpha>s renamed_lhs_\<alpha>i) 
    then have "p@r \<in> possL (ll_single_redex s ?pi ?\<alpha>i)" 
      unfolding poss using single_redex_possL[OF \<alpha>i] by (metis (mono_tags, lifting) i'' mem_Collect_eq nth_mem pi_poss red_i) 
    moreover from red_i i'' have "As!i = ll_single_redex s ?pi ?\<alpha>i" 
      by (metis (no_types, lifting) As nth_map split_beta)
    ultimately show ?thesis by simp
  qed
  with i show ?thesis
    using As not_empty length_rdp_A length_renamed_lhs_\<alpha>s ss_def
    by (metis One_nat_def Suc_pred add.right_neutral add_Suc_right length_greater_0_conv length_tl list.size(4) nth_mem)
qed

(*Step 7 of main proof*)
lemma renamed_lhs_\<alpha>i_\<tau>:
  assumes i:"i < length rdp_A"
    and pi:"pi = snd (rdp_A ! i)"  
  shows "renamed_lhs_\<alpha>s!i \<cdot> \<tau> = l|_(pos_diff pi p) \<cdot> \<tau>"
proof(cases i)
  case 0
  then have pi:"pi = p1" 
    unfolding pi by (metis \<alpha>1p1 hd_conv_nth not_empty snd_conv) 
  from 0 have \<alpha>1:"renamed_lhs_\<alpha>s ! i = renamed_lhs_\<alpha>1"
    by (metis hd_conv_nth i length_greater_0_conv length_renamed_lhs_\<alpha>s ren_lhs_\<alpha>1_alt) 
  have "renamed_lhs_\<alpha>1 |_ pos_diff q p \<cdot> \<tau> = renamed_lhs_\<beta> |_ (pos_diff p1 p) \<cdot> \<tau>"
    using tau.ss_i_\<tau>_eq_t_\<tau>[OF tau unifier] unifier_no_conflict \<tau>_def ps_def ss_def by force 
  then show ?thesis unfolding pi \<alpha>1 using l_\<tau>
    by (metis diff_q_p_poss_renamed_\<alpha>1 l_def order_pos.order_refl p_def prefix_pos_diff replace_at_ident replace_at_subt_at self_append_conv subst_apply_term_ctxt_apply_distrib subt_at.simps(1))
next
  case (Suc n)
  then have \<alpha>i:"renamed_lhs_\<alpha>s ! i = ss ! i"
    by (metis length_0_conv length_renamed_lhs_\<alpha>s list.collapse nth_Cons_Suc not_empty ss_def)
  have pi:"ps ! i = pos_diff pi q"
    unfolding ps_def Suc by (metis Suc Suc_less_eq i length_map length_nth_simps(2) length_nth_simps(4) list.collapse nth_map pi not_empty) 
  have below:"pos_diff q p \<le>\<^sub>p pos_diff pi p"
    by (metis Suc assms(2) i less_eq_pos_simps(2) order_pos.dual_order.strict_implies_order p_above_pi pi_below_q pq_pos_diff prefix_pos_diff prod.collapse zero_less_Suc)
  have "ss ! i \<cdot> \<tau> = renamed_lhs_\<beta> |_ (ps!i) \<cdot> \<tau>"
    using tau.ss_i_\<tau>_eq_t_\<tau>[OF tau unifier] unifier_no_conflict by (simp add: \<tau>_def i length_renamed_lhs_\<alpha>s not_empty ss_def) 
  then show ?thesis unfolding \<alpha>i l_def pi using below
    by (smt (verit, best) append.assoc assms(2) diff_q_p_poss_renamed_\<alpha>1 i l_def less_eq_pos_simps(1) overlapping_part.pos_diff_pi_p 
        overlapping_part_axioms p_above_pi poss_append_poss pq_pos_diff prefix_pos_diff replace_at_subt_at same_append_eq subt_at_append)
qed

lemma Ai'_single_redex:
  assumes i:"i < length rdp_A" and redex_i:"rdp_A ! i = (\<alpha>i, pi)"
  shows "As'!i = ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p) \<alpha>i" 
proof-
  from i redex_i have zip1:"zip rdp_A [0..<length rdp_A] ! i = ((\<alpha>i, pi), i)" by simp
  then have A'_i:"As'!i = replace_at (to_pterm (l \<cdot> \<tau>)) (pos_diff pi p) (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))"
    unfolding As'_def using i by fastforce
  have "to_rule \<alpha>i \<in> R"
    by (metis \<alpha>i_in_R i nth_mem redex_i)
  then have len:"length (var_rule \<alpha>i) = length (var_poss_list (lhs \<alpha>i))"
    by (metis length_var_poss_list length_var_rule)
  {fix j assume j:"j < length (var_rule \<alpha>i)"
    let ?xj="(rename_many' ren i) (var_rule \<alpha>i ! j)"
    let ?pj="pos_diff pi p @ (var_poss_list (lhs \<alpha>i) ! j)"
    have "renamed_lhs_\<alpha>s ! i = map_vars_term (rename_many' ren i) (lhs \<alpha>i)" 
      using renamed_lhs_\<alpha>i by (metis fst_conv i redex_i) 
    then have "\<tau> ?xj = l \<cdot> \<tau> |_ ?pj" using renamed_lhs_\<alpha>i_\<tau>
      by (smt (verit, ccfv_SIG) eval_term.simps(1) fst_conv i j len length_map lin_lhs_\<alpha>i linear_term_var_vars_term_list nth_map nth_mem 
      pos_diff_pi_p poss_imp_subst_poss redex_i snd_conv subt_at_append subt_at_subst var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound vars_map_vars_term vars_term_list_var_poss_list) 
    then have "map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)) ! j = map (to_pterm \<circ> (\<lambda>pia. l \<cdot> \<tau> |_ (pos_diff pi p @ pia))) (var_poss_list (lhs \<alpha>i)) ! j"
      using j len nth_map by simp
  }
  with len have "map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)) = map (to_pterm \<circ> (\<lambda>pia. l \<cdot> \<tau> |_ (pos_diff pi p @ pia))) (var_poss_list (lhs \<alpha>i))" 
    using list_eq_iff_nth_eq by (metis length_map)
  then show ?thesis 
    unfolding A'_i ll_single_redex_def by presburger
qed

lemma source_As'_i:
  assumes i:"i < length rdp_A"
  shows "source (As'!i) = l \<cdot> \<tau>" 
  using Ai'_single_redex 
proof-
  from assms obtain pi \<alpha>i where redex_i:"(\<alpha>i, pi) = rdp_A!i" 
    using prod.collapse by blast 
  with i have Ai'_single:"As'!i = ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p) \<alpha>i" 
    using Ai'_single_redex by auto
  have *:"pos_diff pi p \<in> poss (l \<cdot> \<tau>)" 
    using i redex_i by (metis pos_diff_pi_p poss_imp_subst_poss snd_eqD) 
  have ren_lhs_\<alpha>i_\<tau>:"renamed_lhs_\<alpha>s!i \<cdot> \<tau> = l \<cdot> \<tau> |_ (pos_diff pi p)"
    by (metis i pos_diff_pi_p redex_i renamed_lhs_\<alpha>i_\<tau> snd_conv subt_at_subst) 
  have "renamed_lhs_\<alpha>s!i \<cdot> \<tau> = lhs \<alpha>i \<cdot> \<langle>map (\<lambda>pia. l \<cdot> \<tau> |_ (pos_diff pi p @ pia)) (var_poss_list (lhs \<alpha>i))\<rangle>\<^sub>\<alpha>i" proof-
    let ?\<sigma>1="(\<lambda>x. Var ((rename_many' ren i) x)) \<circ>\<^sub>s \<tau>"
    let ?\<sigma>2="\<langle>map (\<lambda>pia. l \<cdot> \<tau> |_ (pos_diff pi p @ pia)) (var_poss_list (lhs \<alpha>i))\<rangle>\<^sub>\<alpha>i"
    {fix x assume "x \<in> vars_term (lhs \<alpha>i)" 
      then obtain j where j:"j < length (vars_term_list (lhs \<alpha>i))" "vars_term_list (lhs \<alpha>i) ! j = x"
        by (metis in_set_conv_nth set_vars_term_list) 
      then have j':"j < length (var_rule \<alpha>i)"
        by (metis \<alpha>i_in_R i length_var_rule nth_mem redex_i) 
      let ?pj="var_poss_list (lhs \<alpha>i) ! j"
      have x':"x = var_rule \<alpha>i ! j"
        by (metis i j(2) lin_lhs_\<alpha>i linear_term_var_vars_term_list prod.sel(1) redex_i)
      have "?\<sigma>2 x = l \<cdot> \<tau> |_ (pos_diff pi p @ ?pj)" 
        using j lhs_subst_var_i[OF x' j'] by (metis (no_types, lifting) length_map length_var_poss_list nth_map) 
      then have "?\<sigma>1 x = ?\<sigma>2 x" using ren_lhs_\<alpha>i_\<tau>
        by (smt (verit, ccfv_SIG) "*" fst_conv i j(1) j(2) length_var_poss_list nth_map nth_mem overlapping_part.renamed_lhs_\<alpha>i 
         overlapping_part_axioms redex_i subst_compose_def subt_at_append subt_at_subst var_poss_imp_poss 
         var_poss_list_map_vars_term var_poss_list_sound vars_map_vars_term vars_term_list_var_poss_list) 
    }  
    then show ?thesis
      by (smt (verit, best) fst_conv i map_vars_term_as_subst overlapping_part.renamed_lhs_\<alpha>i overlapping_part_axioms 
       redex_i subst_compose subst_subst_compose term_subst_eq) 
  qed
  then have "lhs \<alpha>i \<cdot> \<langle>map (\<lambda>pia. l \<cdot> \<tau> |_ (pos_diff pi p @ pia)) (var_poss_list (lhs \<alpha>i))\<rangle>\<^sub>\<alpha>i = l|_(pos_diff pi p) \<cdot> \<tau>" 
    using renamed_lhs_\<alpha>i_\<tau>[OF i] redex_i unfolding length_map length_zip by (simp add: split_pairs)
  then show ?thesis
    unfolding Ai'_single source_single_redex[OF *] by (metis "*" ctxt_supt_id i pos_diff_pi_p redex_i snd_conv subt_at_subst) 
qed

lemma rdp_Ai':
  assumes i:"i < length rdp_A"
    and \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i"
  shows "redex_patterns (As'!i) = [(\<alpha>i, pos_diff pi p)]"
proof-
  from assms have zip1:"zip rdp_A [0..<length rdp_A] ! i = ((\<alpha>i, pi), i)" by simp
  then have A'_i:"As'!i = replace_at (to_pterm (l \<cdot> \<tau>)) (pos_diff pi p) (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i))))"
    unfolding As'_def using i by fastforce
  have pos_pi:"(pos_diff pi p) \<in> poss (l \<cdot> \<tau>)"
    by (metis i pos_diff_pi_p poss_imp_subst_poss \<alpha>ipi snd_eqD) 
  have \<alpha>i:"to_rule \<alpha>i \<in> R"
    by (metis \<alpha>i_in_R \<alpha>ipi i nth_mem)
  have "redex_patterns (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))) = [(\<alpha>i, [])]"
    using left_lin_no_var_lhs.redex_patterns_prule[OF ll_no_var_lhs] \<alpha>i
    by (smt (verit, best) length_map length_var_poss_list length_var_rule list.map_comp)
  then have "redex_patterns (As'!i) = [(\<alpha>i, pos_diff pi p)]"
    unfolding A'_i left_lin_no_var_lhs.redex_patterns_context[OF ll_no_var_lhs pos_pi] by simp
  with \<alpha>ipi i show ?thesis by simp
qed

lemma single_steps_Ai':
  assumes i:"i < length rdp_A" 
  shows "single_steps (As'!i) = [As'!i]" 
proof-
  from assms obtain pi \<alpha>i where redex_i:"(\<alpha>i, pi) = rdp_A!i" 
    using prod.collapse by blast 
  with i have "As'!i = ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p) \<alpha>i" 
    using Ai'_single_redex by auto
  moreover have "redex_patterns (As'!i) = [(\<alpha>i, pos_diff pi p)]" 
    using rdp_Ai'[OF i redex_i] by simp 
  ultimately show ?thesis
    using redex_i i source_As'_i by force
qed

lemma B'_single_redex: "B' = ll_single_redex (l \<cdot> \<tau>) (pos_diff q p) \<beta>" 
proof-
 have ren_lhs_\<beta>_\<tau>:"renamed_lhs_\<beta> \<cdot> \<tau> = l \<cdot> \<tau> |_ (pos_diff q p)"
    by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_subt_at)
  {fix j assume j:"j < length (vars_term_list renamed_lhs_\<beta>)"
    let ?yj="vars_term_list renamed_lhs_\<beta> ! j"
    let ?pj="var_poss_list (lhs \<beta>) ! j"
    have pj:"var_poss_list renamed_lhs_\<beta> ! j = ?pj"
      by (simp add: renamed_lhs_\<beta>_def var_poss_list_map_vars_term) 
    with j have pj':"renamed_lhs_\<beta> |_ ?pj = Var ?yj"
      by (simp add: vars_term_list_var_poss_list) 
    with ren_lhs_\<beta>_\<tau> have "\<tau> ?yj = l \<cdot> \<tau> |_ (pos_diff q p) |_ ?pj"
      by (metis eval_term.simps(1) j length_var_poss_list nth_mem pj subt_at_subst var_poss_imp_poss var_poss_list_sound) 
    with j have "(to_pterm \<circ> \<tau>) ?yj = (to_pterm \<circ> (\<lambda>pi. l \<cdot> \<tau> |_ (pos_diff q p @ pi))) ?pj"
      by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_below_poss)
    then have "map (to_pterm \<circ> \<tau>) (vars_term_list renamed_lhs_\<beta>) ! j = map (to_pterm \<circ> (\<lambda>pi. l \<cdot> \<tau> |_ (pos_diff q p @ pi))) (var_poss_list (lhs \<beta>)) ! j" 
      using j unfolding renamed_lhs_\<beta>_def by (metis (mono_tags, lifting) length_map length_var_poss_list nth_map vars_map_vars_term)
  }
  then show ?thesis unfolding B'_def ll_single_redex_def renamed_lhs_\<beta>_def
    by (smt (verit) length_map length_var_poss_list nth_equalityI vars_map_vars_term) 
qed

lemma src_B':"source B' = l \<cdot> \<tau>" 
proof-
  have *:"pos_diff q p \<in> poss (l \<cdot> \<tau>)"
    by (metis diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau>)
  have ren_lhs_\<beta>_\<tau>:"renamed_lhs_\<beta> \<cdot> \<tau> = l \<cdot> \<tau> |_ (pos_diff q p)"
    by (simp add: diff_q_p_poss_renamed_\<alpha>1 l_\<tau> replace_at_subt_at)
  {fix y assume y:"y \<in> vars_term (lhs \<beta>)"
    then obtain j where j:"j < length (vars_term_list (lhs \<beta>))" "vars_term_list (lhs \<beta>) ! j = y"
      by (metis in_set_idx set_vars_term_list) 
    let ?pj="var_poss_list (lhs \<beta>) ! j"
    let ?\<sigma>1="(\<lambda>x. Var (rename_single ren x)) \<circ>\<^sub>s \<tau>"    
    let ?\<sigma>2="\<langle>map (\<lambda>pi. l \<cdot> \<tau> |_ (pos_diff q p @ pi)) (var_poss_list (lhs \<beta>))\<rangle>\<^sub>\<beta>"
    from j have pj:"lhs \<beta> |_ ?pj = Var y"
      using vars_term_list_var_poss_list by force
    have j':"j < length (var_rule \<beta>)"
      using j(1) \<beta> length_var_rule by auto 
    have y':"y = var_rule \<beta> ! j"
      by (metis \<beta> comp_eq_dest_lhs j(2) length_remdups_eq length_rev length_var_rule rev_rev_ident) 
    have "?\<sigma>2 y = l \<cdot> \<tau> |_ (pos_diff q p @ ?pj)" 
      using j lhs_subst_var_i[OF y' j'] by (metis (no_types, lifting) length_map length_var_poss_list nth_map) 
    then have "?\<sigma>1 y = ?\<sigma>2 y" using ren_lhs_\<beta>_\<tau>
      by (smt (verit, del_insts) "*" j(1) j(2) length_var_poss_list nth_map nth_mem renamed_lhs_\<beta>_def 
      subst_compose_def subt_at_append subt_at_subst var_poss_imp_poss var_poss_list_map_vars_term var_poss_list_sound 
      vars_map_vars_term vars_term_list_var_poss_list)
  }
  then have "renamed_lhs_\<beta> \<cdot> \<tau> = lhs \<beta> \<cdot> \<langle>map (\<lambda>pi. l \<cdot> \<tau> |_ (pos_diff q p @ pi)) (var_poss_list (lhs \<beta>))\<rangle>\<^sub>\<beta>"
    unfolding renamed_lhs_\<beta>_def map_vars_term_as_subst by (smt (verit, best) subst.cop_add term_subst_eq_conv)
  with ren_lhs_\<beta>_\<tau> show ?thesis unfolding B'_single_redex source_single_redex[OF *]
    by (simp add: "*" ctxt_supt_id)  
qed

lemma B'_in_B: "B = replace_at (to_pterm s) p (B' \<cdot> (to_pterm \<circ> \<sigma>))" 
proof-
  have B'_sigma:"B' \<cdot> (to_pterm \<circ> \<sigma>) = (ctxt_of_pos_term (pos_diff q p) ((to_pterm s)|_p)) \<langle>B|_q\<rangle>" proof-
    have *:"pos_diff q p \<in> poss (to_pterm (l \<cdot> \<tau>))"
      by (simp add: diff_q_p_poss_l to_pterm_subst)
    {fix i assume i:"i < length (vars_term_list renamed_lhs_\<beta>)" 
      let ?x="vars_term_list renamed_lhs_\<beta>!i" 
      have tau_alt:"\<tau> = compose (drop 0 (map2 (\<lambda>x y. linear_unifier x (renamed_lhs_\<beta> |_ y)) ss ps))"
        unfolding \<tau>_def using tau tau.\<tau>_def by fastforce 
      have "to_pterm (\<tau> ?x) \<cdot> (to_pterm \<circ> \<sigma>) = to_pterm ((\<tau> \<circ>\<^sub>s \<sigma>) ?x)"
        by (simp add: subst_compose_def to_pterm_subst)
      with i have "to_pterm (\<tau> ?x) \<cdot> (to_pterm \<circ> \<sigma>) = to_pterm (s|_(q @ var_poss_list (lhs \<beta>)!i))"
        using \<sigma>_\<tau>'_y[of 0] unfolding tau_alt by (simp add: renamed_lhs_\<beta>_def var_poss_list_map_vars_term)  
    }
    then have "Prule \<beta> (map (to_pterm \<circ> \<tau>) (vars_term_list renamed_lhs_\<beta>)) \<cdot> (to_pterm \<circ> \<sigma>) = Prule \<beta> (map (to_pterm \<circ> (\<lambda>pi. s |_ (q @ pi))) (var_poss_list (lhs \<beta>)))"
      unfolding eval_term.simps renamed_lhs_\<beta>_def by (smt (verit, ccfv_SIG) comp_apply length_map length_var_poss_list map_nth_eq_conv var_poss_list_map_vars_term)
    then show ?thesis unfolding B'_def unfolding subst_apply_term_ctxt_apply_distrib ctxt_of_pos_term_subst[OF *, symmetric] B ll_single_redex_def
      by (metis (no_types, lifting) ctxt_supt_id l_\<tau>_\<sigma> p_in_poss_to_pterm p_poss q replace_at_subt_at subst_subst_compose to_pterm_ctxt_of_pos_apply_term to_pterm_subst) 
  qed
  show ?thesis unfolding B B'_sigma using ctxt_apply_ctxt_apply p_poss pq_pos_diff
    by (metis (no_types, lifting) ctxt_supt_id ll_single_redex_def p_in_poss_to_pterm q replace_at_subt_at) 
qed

lemma join_As':
  assumes "a1 \<in> set As'" and "a2 \<in> set As'"
  shows "a1 \<squnion> a2 \<noteq> None"
proof- 
  from assms(1) obtain j where j:"j < length As'" and a1:"As'!j = a1" 
    by (metis (no_types, lifting) in_set_idx) 
  have length:"length As' = length rdp_A" 
    unfolding As'_def length_map length_zip by simp
  have as1:"As!j = replace_at (to_pterm s) p (a1 \<cdot> (to_pterm \<circ> \<sigma>))"
    using As'_As[OF j[unfolded length]] unfolding a1 by simp
  from length j have aj:"As!j \<in> set (single_steps A)"
    unfolding As using filter_ex_index in_set_conv_nth rdp_A s(1) by fastforce
  from assms(2) obtain i where i:"i < length As'" and a2:"As'!i = a2" 
    by (metis (no_types, lifting) in_set_idx) 
  have as2:"As!i = replace_at (to_pterm s) p (a2 \<cdot> (to_pterm \<circ> \<sigma>))"
    using As'_As[OF i[unfolded length]] unfolding a2 by simp
  from length i have ai:"As!i \<in> set (single_steps A)"
    unfolding As using filter_ex_index in_set_conv_nth rdp_A s(1) by fastforce
  have co_init:"source a1 = source a2"
    using source_As'_i a1 a2 i j unfolding length by fastforce
  show ?thesis proof(cases "i = j")
    case True
    then have "a1 = a2" 
      using a1 a2 by fastforce 
    then show ?thesis
      by (simp add: join_same)
  next
    case False
    have "As!i \<noteq> As!j" proof
      assume same:"As!i = As!j" 
      obtain i' j' where i':"i' < length (redex_patterns A)" "As!i = single_steps A ! i'"
        and j':"j' < length (redex_patterns A)" "As!j = single_steps A ! j'" and neq:"i' \<noteq> j'" 
        using filter_index_neq[OF False] i j unfolding As'_def unfolding rdp_A length_map length_zip
        by (smt (verit, best) As diff_zero length_upt min.idem nth_map prod.case_eq_if rdp_A s(1))
      from i' obtain \<alpha>i pi where at_i':"redex_patterns A ! i' = (\<alpha>i, pi)"
        using prod.exhaust_sel by blast 
      then have pi_pos:"pi \<in> poss (source A)"
        by (metis A_wf i'(1) left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs nth_mem) 
      from j' obtain \<alpha>j pj where at_j':"redex_patterns A ! j' = (\<alpha>j, pj)"
        using prod.exhaust_sel by blast 
      then have pj_pos:"pj \<in> poss (source A)"
        by (metis A_wf j'(1) left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs nth_mem) 
      have "redex_patterns A ! i' \<noteq> redex_patterns A ! j'" 
        using left_lin_no_var_lhs.distinct_snd_rdp[OF ll_no_var_lhs A_wf] neq i'(1) j'(1) using distinct_map nth_eq_iff_index_eq by blast 
      with same show False
        unfolding i'(2) j'(2) at_i' at_j' nth_map[OF i'(1)] nth_map[OF j'(1)] using single_redex_neq pj_pos pi_pos by fastforce
    qed
    then have "As!i \<bottom>\<^sub>p As!j"
      using single_steps_orth[OF ai aj A_wf] by blast
    moreover have "ctxt_of_pos_term p (to_pterm s) \<in> wf_pterm_ctxt R"
      using p_poss by (simp add: p_in_poss_to_pterm to_pterm_trs_ctxt) 
    ultimately have "a2 \<cdot> (to_pterm \<circ> \<sigma>) \<bottom>\<^sub>p a1 \<cdot> (to_pterm \<circ> \<sigma>)"
      unfolding as1 as2 using orthogonal_ctxt by presburger 
    then have "a2 \<bottom>\<^sub>p a1" 
      using left_lin_no_var_lhs.orthogonal_subst[OF ll_no_var_lhs] co_init As'_wf assms by presburger
    then show ?thesis using orth_imp_join_defined assms
      by (metis (mono_tags, lifting) As'_wf Residual_Join_Deletion.join_sym)
  qed
qed

lemma exists_A':"\<exists> A'. Some A'= \<Squnion> As' \<and> A' \<in> wf_pterm R" 
  using left_lin_no_var_lhs.join_list_defined[OF ll_no_var_lhs, of As'] join_As' As'_wf As'_not_empty by auto

lemma exists_p': "\<exists>p'. p' \<in> poss A \<and> source_ctxt (ctxt_of_pos_term p' A) = ctxt_of_pos_term p s" 
proof(cases "q <\<^sub>p p1")
  case True
  then have pq:"p = q" 
    unfolding p_def by simp
  have "get_label (labeled_source B |_ p) = Some (\<beta>, 0)" 
    using single_redex_at_p_label[OF p_poss] \<beta> pq using B no_var_lhs by fastforce
  then have p_posL_B:"p \<in> possL B"
    by (simp add: get_label_imp_labelposs pq q s(2))
  have "get_label (labeled_source A |_ p) = None" proof(rule ccontr)
    assume "get_label (labeled_source A |_ p) \<noteq> None" 
    then obtain \<alpha> n where "get_label (labeled_source A |_ p) = Some (\<alpha>, n)"
      by fastforce 
    then obtain Ai where Ai:"Ai \<in> set (single_steps A)" "get_label (labeled_source Ai |_ p) = Some (\<alpha>, n)" 
      using left_lin_no_var_lhs.label_single_step[OF ll_no_var_lhs] p_poss A_wf s(1) by force
    then have src_Ai:"source Ai = s"
      using A_wf s(1) source_single_step by blast
    with Ai have p:"p \<in> possL Ai"
      by (simp add: get_label_imp_labelposs p_poss) 
    from Ai(1) obtain \<beta> r where Ai_single:"Ai = ll_single_redex s r \<beta>" and rdp:"(\<beta>, r) \<in> set (redex_patterns A)" 
      using s(1) by auto
    then have r\<beta>:"r \<in> poss s" "to_rule \<beta> \<in> R"
      using A_wf labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs s(1) by fastforce+
    from p p_posL_B have ov:"measure_ov Ai B \<noteq> 0"
      by (meson card_eq_0_iff disjoint_iff finite_Int finite_labelposs)
    from Ai p obtain r' where r:"r' \<le>\<^sub>p p" "get_label (labeled_source Ai |_ r') = Some (\<alpha>, 0)"
      using As_i_wf append_take_drop_id less_eq_pos_simps(1) obtain_label_root
      by (metis (mono_tags, lifting) A_wf \<open>source Ai = s\<close> labeled_source_to_term poss_term_lab_to_term pq q single_step_wf)
    then have "(\<alpha>, r') \<in> set (redex_patterns Ai)"
      by (metis (no_types, lifting) A_wf Ai(1) left_lin_no_var_lhs.redex_patterns_label left_lin_wf_trs.single_step_wf 
          left_lin_wf_trs_axioms less_eq_pos_def ll_no_var_lhs map_eq_conv poss_append_poss pq q split_beta src_Ai)  
    with Ai_single r\<beta> have "\<beta> = \<alpha>" "r = r'" 
      using left_lin_no_var_lhs.redex_patterns_single[OF ll_no_var_lhs] by fastforce+
    then have "(\<alpha>, r') \<in> set rdp_A" unfolding rdp_A
      using Ai_single ov rdp by force
    with r(1) show False
      using True ll_no_var_lhs pq p_above_pi
      by (metis \<alpha>1p1 hd_conv_nth in_set_conv_nth linorder_neqE_nat not_empty not_less_zero order_pos.leD pi_below_q snd_conv) 
  qed
  then show ?thesis 
    using poss_labeled_source_None A_wf pq q s(1) by fastforce
next
  case False
  then have "p = p1" 
    unfolding p_def by simp
  then have "(\<alpha>1, p) \<in> set (redex_patterns A)"
    using \<alpha>1p1_in_rdpA rdp_A_subs_A by auto 
  then have "get_label (labeled_source A |_ p) = Some (\<alpha>1, 0)"
    using A_wf left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast 
  then show ?thesis
    using poss_labeled_source p_poss A_wf s(1) left_lin by force
qed


context 
  fixes A'
  assumes A':"Some A'= \<Squnion> As'" and A'_wf:"A' \<in> wf_pterm R"
begin

lemma rdp_A':"set (redex_patterns A') = \<Union> (set (map (set \<circ> redex_patterns) As'))" 
  using left_lin_no_var_lhs.redex_patterns_join_list[OF ll_no_var_lhs] by (simp add: A' As'_wf)

lemma rdp_A_eq_rdp_A':"set rdp_A = (\<lambda>(\<alpha>i, pi). (\<alpha>i, p@pi)) ` (set (redex_patterns A'))" 
proof-
  {fix \<alpha>i pi assume "(\<alpha>i, pi) \<in> set rdp_A"
    then obtain i where i:"rdp_A ! i = (\<alpha>i, pi)" "i < length rdp_A"
      using in_set_idx by force
    then have As'_i:"As'!i = (ctxt_of_pos_term (pos_diff pi p) (to_pterm (l \<cdot> \<tau>)))\<langle>Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))\<rangle>" 
      unfolding As'_def by simp
    from i have p:"pos_diff pi p  \<in> poss (l \<cdot> \<tau>)"
      using pos_diff_pi_p poss_imp_subst_poss by fastforce
    have "(\<alpha>i, []) \<in> set (redex_patterns (Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))))" 
      unfolding redex_patterns.simps by simp
    then have "(\<alpha>i, pos_diff pi p) \<in> set (redex_patterns (As'!i))"
      using rdp_Ai' i by fastforce
    moreover have "As'!i \<in> set As'"
      using i(2) unfolding As'_def by (smt (verit) in_set_conv_nth length_map map_nth zip_eq_conv)
    ultimately have "(\<alpha>i, pos_diff pi p) \<in> set (redex_patterns A')" 
      unfolding rdp_A' set_map o_apply using UN_iff by blast
    then have "(\<alpha>i, pi) \<in> (\<lambda>(\<alpha>i, pi). (\<alpha>i, p@pi)) ` (set (redex_patterns A'))"
      using i p_above_pi by force 
  } moreover
  {fix \<alpha>i pi assume "(\<alpha>i, pi) \<in> (\<lambda>(\<alpha>i, pi). (\<alpha>i, p@pi)) ` (set (redex_patterns A'))"
    then obtain pi' where p:"pi = p@pi'" and "(\<alpha>i, pi') \<in> set (redex_patterns A')" 
      by force
    then obtain Ai where Ai:"Ai \<in> set As'" "(\<alpha>i, pi') \<in> (set \<circ> redex_patterns) Ai" 
      unfolding rdp_A' using UN_iff[of "(\<alpha>i, pi')" "(set \<circ> redex_patterns)" "set As'"] unfolding set_map by blast
    then obtain i where i:"i < length As'" "As'!i = Ai"
      by (meson in_set_conv_nth) 
    then have i':"i < length rdp_A" unfolding As'_def by simp
    from rdp_Ai'[OF i'] Ai(2) have "redex_patterns (As'!i) = [(\<alpha>i, pi')]" 
      unfolding i(2) by (metis comp_apply in_set_simps(2) prod.collapse)
    then have "rdp_A ! i = (\<alpha>i, pi)" 
      using rdp_Ai'[OF i'] p i' p_above_pi by (metis fst_conv list.sel(1) prefix_pos_diff prod.collapse snd_conv) 
    then have "(\<alpha>i, pi) \<in> set rdp_A" 
      using i(1) using nth_mem by (metis i')
  }
  ultimately show ?thesis by (meson pred_equals_eq2) 
qed

lemma rdp_A_eq:"rdp_A = map (\<lambda>(\<alpha>i, pi). (\<alpha>i, p@pi)) (redex_patterns A')" (is "_ = ?rdp_A'") 
proof-
  have "sorted_wrt (ord.lexordp (<)) (map snd (redex_patterns A'))"
    using A'_wf left_lin_no_var_lhs.redex_patterns_sorted ll_no_var_lhs by blast 
  then have sorted_rdp_A':"sorted_wrt (ord.lexordp (<)) (map snd ?rdp_A')"
    by (smt (verit, del_insts) Pair_inject old.prod.case ord.lexordp_append_leftI prod.exhaust_sel sorted_wrt_iff_nth_less sorted_wrt_map) 
  have linord:"class.linorder (ord.lexordp_eq ((<) :: nat \<Rightarrow> nat \<Rightarrow> bool)) (ord.lexordp (<))"
    using linorder.lexordp_linorder[OF linorder_class.linorder_axioms] by simp
  then have map_snd:"map snd rdp_A = map snd ?rdp_A'" 
    using linorder.strict_sorted_equal[OF linord sorted_rdp_A sorted_rdp_A'] rdp_A_eq_rdp_A' by force
  have dist:"distinct (map snd rdp_A)"
    using lexord_linorder.strict_sorted_iff sorted_rdp_A by auto 
  {fix x y assume x:"x \<in> set rdp_A" and y:"y \<in> set ?rdp_A'" and xy:"snd x = snd y"
    {assume "x \<noteq> y"
      then have "fst x \<noteq> fst y" 
        using xy by (simp add: prod_eq_iff) 
      then have False 
        using x y xy dist rdp_A_eq_rdp_A' by (smt (verit, ccfv_threshold) distinct_conv_nth image_set in_set_idx length_map nth_map)
    }
    then have "x = y" by auto
  }
  then show ?thesis 
    using map_snd list.inj_map_strong by blast
qed 

lemma src_A':"source A' = l \<cdot> \<tau>" 
proof-
  obtain A' where "A' \<in> set As'" and "source A' = l \<cdot> \<tau>" 
    using As'_not_empty source_As'_i by (meson length_greater_0_conv nth_mem not_empty) 
  then show ?thesis 
    using left_lin_no_var_lhs.source_join_list[OF ll_no_var_lhs A'[symmetric]] As'_wf by force
qed

lemma lin_A':"linear_term A'"
  using linear_l_tau linear_source_imp_linear_pterm[OF A'_wf] src_A' by simp

lemma hd_rdp_A':"hd (redex_patterns A') = (\<alpha>1, pos_diff p1 p)"
proof-
  from rdp_A_eq obtain \<alpha>' p' where hd:"hd (redex_patterns A') = (\<alpha>', p')" and *:"(\<lambda>(\<alpha>i, pi). (\<alpha>i, p @ pi)) (\<alpha>', p') = (\<alpha>1, p1)"
    by (metis (no_types, lifting) \<alpha>1p1 hd_map map_is_Nil_conv prod.collapse not_empty) 
  then have "\<alpha>' = \<alpha>1"
    by fastforce 
  moreover have "p' = pos_diff p1 p" 
    using * by (metis case_prod_conv less_eq_pos_simps(1) prefix_pos_diff same_append_eq snd_conv) 
  ultimately show ?thesis 
    using hd by simp
qed

lemma single_steps_A':"single_steps A' = As'" 
proof-
  have "length (redex_patterns A') = length rdp_A"
    using rdp_A_eq by simp
  then have len:"length (redex_patterns A') = length As'" 
    unfolding length_map As'_def length_zip by simp
  {fix i assume i':"i < length As'" 
    then have i:"i < length rdp_A" 
      unfolding As'_def length_map length_zip by simp
    obtain \<alpha>i pi where \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i"
      by (metis surj_pair) 
    then have rdp_i:"redex_patterns A' ! i = (\<alpha>i, pos_diff pi p)" 
      using rdp_A_eq i by (smt (verit, del_insts) Pair_inject length_map nth_map old.prod.case p_above_pi prefix_pos_diff prod.collapse same_append_eq) 
    have "single_steps A' ! i = ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p) \<alpha>i" 
      unfolding nth_map[OF i'[unfolded len[symmetric]]] rdp_i src_A' by simp
    moreover have "As' ! i = ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p ) \<alpha>i" proof- 
      have *:"redex_patterns (As' ! i) = [(\<alpha>i, pos_diff pi p)]" 
        using rdp_Ai'[OF i \<alpha>ipi] by simp
      have "single_steps (As' ! i) = [ll_single_redex (l \<cdot> \<tau>) (pos_diff pi p) \<alpha>i]" 
        unfolding * source_As'_i[OF i] by simp
      then show ?thesis
        using single_steps_Ai'[OF i] by simp
    qed
    ultimately have "single_steps A' ! i = As' ! i" 
      by simp
  }
  with len show ?thesis
    by (simp add: list_eq_iff_nth_eq)
qed

(*Step 8 of main proof*)
context 
  fixes p'
  assumes p':"p' \<in> poss A" and ctxt_A:"source_ctxt (ctxt_of_pos_term p' A) = ctxt_of_pos_term p s"
begin 

definition "\<rho> = mk_subst Var (match_substs A' (A|_p'))"

lemma A'_rho:"A' \<cdot> \<rho> = A|_p'" 
proof-
  have A_at_p'_wf:"A|_p' \<in> wf_pterm R" 
    using p' A_wf subt_at_is_wf_pterm by blast 
  {fix \<alpha> r assume \<alpha>r:"(\<alpha>, r) \<in> set (redex_patterns A')" 
    from \<alpha>r have fun_poss:"r \<in> fun_poss (source A')"
      by (metis A'_wf get_label_imp_labelposs labeled_source_to_term labelposs_subs_fun_poss_source left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs option.distinct(1) poss_term_lab_to_term) 
    from \<alpha>r obtain ai where "ai \<in> set (As')" and rdp:"(\<alpha>, r) \<in> set (redex_patterns ai)" 
      unfolding rdp_A' using UN_iff[of "(\<alpha>, r)" "set \<circ> redex_patterns" "set As'"] by force
    then obtain i where i:"i < length As'" "ai = As'!i"
      by (meson in_set_idx)
    from i(1) have i':"i < length rdp_A" 
      unfolding As'_def length_map length_zip by force
    let ?\<alpha>i="fst (rdp_A ! i)" and ?pi="snd (rdp_A ! i)"
    from i(2) have set_rdp:"set (redex_patterns ai) = {(?\<alpha>i, pos_diff ?pi p)}"
      using i' rdp_Ai' by (metis list.simps(15) prod.collapse set_empty)
    have "(?\<alpha>i, ?pi) \<in> set (redex_patterns A)"
      using i' rdp_A_subs_A by auto
    then have "(?\<alpha>i, pos_diff ?pi p) \<in> set (redex_patterns (A|_p'))"
      using left_lin_no_var_lhs.redex_patterns_label[OF ll_no_var_lhs]
      by (smt (verit, best) s(1) A_wf A_at_p'_wf ctxt_A ctxt_supt_id i' label_source_ctxt labeled_source_to_term p' p_above_pi p_poss poss_term_lab_to_term prefix_pos_diff replace_at_subt_at subterm_poss_conv) 
    with rdp set_rdp fun_poss have "(\<alpha>, r) \<in> set (redex_patterns (A|_p')) \<and> r \<in> fun_poss (source A')"
      by simp
  } moreover 
  {fix \<alpha> r assume \<alpha>r:"(\<alpha>, r) \<in> set (redex_patterns (A|_p'))" and r:"r \<in> fun_poss (source A')"
    then have \<alpha>pr:"(\<alpha>, p@r) \<in> set (redex_patterns A)"
      using A_at_p'_wf s(1) A_wf ctxt_A ctxt_supt_id label_source_ctxt labeled_source_to_term left_lin_no_var_lhs.redex_patterns_label[OF ll_no_var_lhs]
      by (smt (verit, ccfv_threshold) p' p_poss poss_append_poss poss_term_lab_to_term replace_at_subt_at subt_at_append)
    have pr_poss:"p@r \<in> poss s"
      using s(1) A_wf \<alpha>pr left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs by blast
    have \<alpha>:"to_rule \<alpha> \<in> R"
      by (metis A_wf \<alpha>pr labeled_source_to_term labeled_wf_pterm_rule_in_TRS left_lin_no_var_lhs.redex_patterns_label ll_no_var_lhs poss_term_lab_to_term)
    then obtain f ts where lhs:"lhs \<alpha> = Fun f ts"
      using no_var_lhs by fastforce 
    have pr_possL:"p@r \<in> possL (ll_single_redex s (p@r) \<alpha>)"
      using single_redex_possL[OF \<alpha> pr_poss] unfolding lhs by simp
    from r have "r \<in> fun_poss (l \<cdot> \<tau>)"
      using src_A' by auto 
    then consider "p@r \<in> possL B" | "\<exists>a \<in> set As. p@r \<in> possL a" 
      using fun_poss_l_tau by blast
    then have "measure_ov (ll_single_redex s (p@r) \<alpha>) B \<noteq> 0" proof(cases)
      case 1
      then show ?thesis 
        using pr_possL by (meson card_eq_0_iff disjoint_iff finite_Int finite_possL)
    next
      case 2
      then obtain Ai where Ai:"Ai \<in> set As" "p@r \<in> possL Ai"
        by blast 
      then obtain \<alpha>i pi where Ai':"Ai = ll_single_redex s pi \<alpha>i" and pi:"pi \<in> poss s"
        using s(1) left_lin_no_var_lhs.redex_patterns_label[OF ll_no_var_lhs A_wf] using As rdp_A by auto
      moreover 
      {assume neq:"(\<alpha>i, pi) \<noteq> (\<alpha>, p@r)" 
        from Ai have "Ai \<in> set (single_steps A)"
          using As rdp_A_subs_A s(1) by force 
        moreover from \<alpha>pr have "ll_single_redex s (p@r) \<alpha> \<in> set (single_steps A)"
          using s(1) by fastforce 
        ultimately consider "Ai = ll_single_redex s (p@r) \<alpha>" | "measure_ov Ai (ll_single_redex s (p@r) \<alpha>) = 0" 
          using single_steps_measure A_wf by meson
        then have False proof(cases)
          case 1
          then show ?thesis unfolding Ai' using single_redex_neq[OF neq pi pr_poss] by simp
        next
          case 2
          then show ?thesis
            by (meson Ai(2) card_eq_0_iff disjoint_iff finite_Int finite_possL pr_possL)
        qed
      }
      ultimately have "Ai = ll_single_redex s (p@r) \<alpha>"
        by fastforce
      with Ai(1) show ?thesis 
        unfolding As using overlap by force
    qed
    with \<alpha>pr have "(\<alpha>, p@r) \<in> set rdp_A"
      using rdp_A by simp
    then have "(\<alpha>, r) \<in> set (redex_patterns A')" 
      using rdp_A_eq_rdp_A' by auto
  }
  moreover have "source A' \<cdot> \<sigma> = source (A|_p')"
    unfolding src_A' by (metis s(1) A_wf ctxt_A ctxt_eq ctxt_of_pos_term_well ctxt_supt_id l_\<tau>_\<sigma> p' p_poss source_ctxt_apply_term subst_subst_compose)
  ultimately show ?thesis
    unfolding \<rho>_def using left_lin_no_var_lhs.proof_term_matches[OF ll_no_var_lhs A'_wf A_at_p'_wf lin_A'] by blast
qed

lemma A_key_lemma:"A = (ctxt_of_pos_term p' A) \<langle>A' \<cdot> \<rho>\<rangle>"
  using A'_rho ctxt_supt_id[OF p'] by simp

lemma rho_x_wf:"\<rho> x \<in> wf_pterm R" 
proof(cases "x \<in> vars_term A'")
  case True
  then show ?thesis using A'_rho A_wf
    by (metis p' subst_well_def subt_at_is_wf_pterm) 
next
  case False
  then have "\<rho> x = Var x" 
    unfolding \<rho>_def match_substs_def by (simp add: mk_subst_not_mem) 
  then show ?thesis by simp
qed 

lemma source_rho:
  assumes "x \<in> vars_term (l \<cdot> \<tau>)"
  shows "(source \<circ> \<rho>) x = \<sigma> x" 
proof-
  have "source (A' \<cdot> \<rho>) = (source A') \<cdot> \<sigma>" proof-
    have "source (A' \<cdot> \<rho>) = s|_p"
      using A'_rho by (metis A_wf s(1) A_key_lemma ctxt_A ctxt_of_pos_term_well p' p_poss replace_at_subt_at source_ctxt_apply_term) 
    then show ?thesis  using l_\<tau>_\<sigma> src_A' by simp
  qed
  then have "\<forall> x \<in> vars_term A'. (source \<circ> \<rho>) x = \<sigma> x"
    using A'_wf source_apply_subst term_subst_eq_rev vars_term_source by fastforce
  then show ?thesis
    using A'_wf assms src_A' vars_term_source by force 
qed

lemma B'_src_\<rho>:"target B' \<cdot> (source \<circ> \<rho>) = target B' \<cdot> \<sigma>"
proof-
  have "vars_term B' = vars_term (l \<cdot> \<tau>)" 
    using vars_term_source[OF B'_wf] src_B' by simp
  then have "vars_term (target B') \<subseteq> vars_term (l \<cdot> \<tau>)" 
    using vars_term_target[OF B'_wf] by simp 
  with source_rho show ?thesis
    using term_subst_eq_conv by force 
qed

end

(*Step 9 of main proof*)
lemma overlap_As'_B':
  assumes "Ai' \<in> set As'"
  shows "measure_ov Ai' B' \<noteq> 0"
proof-
  from assms obtain i where i:"i < length As'" and Ai':"Ai' = As' ! i"
    by (meson in_set_idx) 
  from i have i':"i < length rdp_A" 
    unfolding As'_def length_map length_zip by simp
  obtain \<alpha>i pi where \<alpha>ipi:"(\<alpha>i, pi) = rdp_A ! i"
    by (meson prod.collapse) 
  let ?\<Delta>="ll_single_redex s pi \<alpha>i"
  have ctxt:"ctxt_of_pos_term p (source (to_pterm s)) = source_ctxt (ctxt_of_pos_term p (to_pterm s))"
    by (simp add: p_poss source_ctxt_to_pterm) 
  have possL1:"possL ?\<Delta> = {p @ q |q. q \<in> possL Ai'}" proof-
    have "(ctxt_of_pos_term p (to_pterm s))\<langle>Ai' \<cdot> (to_pterm \<circ> \<sigma>)\<rangle> = As ! i" 
      using As'_As[OF i'] Ai' by simp
    moreover have "As ! i = ?\<Delta>" 
      using As i' \<alpha>ipi by (metis case_prod_conv nth_map)  
    ultimately have \<Delta>1:"?\<Delta> = (ctxt_of_pos_term p (to_pterm s))\<langle>Ai' \<cdot> (to_pterm \<circ> \<sigma>)\<rangle>" 
      by simp
    have possL:"possL ?\<Delta> = {p @ q |q. q \<in> possL (Ai' \<cdot> (to_pterm \<circ> \<sigma>))}"
      using label_ctxt[OF to_pterm_wf_pterm[of s R] ctxt] p_poss 
      unfolding \<Delta>1 source_to_pterm labeled_source_simple_pterm by (simp add: p_in_poss_to_pterm)
    have wf:"Ai' \<cdot> (to_pterm \<circ> \<sigma>) \<in> wf_pterm R"
      by (simp add: As'_wf apply_subst_wf_pterm assms) 
    have "possL (Ai' \<cdot> (to_pterm \<circ> \<sigma>)) = possL Ai'" 
      using possL_apply_subst[OF wf] unfolding o_apply labeled_source_simple_pterm by auto
    with possL show ?thesis 
      by simp
  qed
  have possL2:"possL B = {p @ q |q. q \<in> possL B'}" proof-
    have possL:"possL B = {p @ q |q. q \<in> possL (B' \<cdot> (to_pterm \<circ> \<sigma>))}"
      using label_ctxt[OF to_pterm_wf_pterm[of s R] ctxt] p_poss 
      unfolding B'_in_B source_to_pterm labeled_source_simple_pterm by (simp add: p_in_poss_to_pterm)
    have wf:"B' \<cdot> (to_pterm \<circ> \<sigma>) \<in> wf_pterm R"
      by (simp add: B'_wf apply_subst_wf_pterm) 
    then have "possL (B' \<cdot> (to_pterm \<circ> \<sigma>)) = possL B'"
      using possL_apply_subst[OF wf] unfolding o_apply labeled_source_simple_pterm by auto
    with possL show ?thesis
      by simp
  qed
  from overlap have ov:"measure_ov ?\<Delta> B \<noteq> 0" 
    using i' \<alpha>ipi by simp
  show ?thesis proof(rule ccontr)
    assume "\<not> measure_ov Ai' B' \<noteq> 0" 
    then have "possL Ai' \<inter> possL B' = {}"
      by (simp add: finite_possL)  
    with ov show False unfolding possL1 possL2
      by (smt (verit, best) card.empty disjoint_iff mem_Collect_eq same_append_eq)
  qed
qed

lemma A'_B'_sim_cp:"(A', B') \<in> sim_cp" proof-
 obtain rdp_A' where rdp_A':"redex_patterns A' = rdp_A'"
    by simp 
  have rdp_B':"redex_patterns B' = [(\<beta>, pos_diff q p)]" 
    unfolding B'_single_redex using left_lin_no_var_lhs.redex_patterns_single[OF ll_no_var_lhs]
    by (metis \<beta> diff_q_p_poss_renamed_\<alpha>1 hole_pos_ctxt_of_pos_term hole_pos_poss l_\<tau>)
  obtain ren_lhs_\<alpha>s where ren_lhs_\<alpha>s:"ren_lhs_\<alpha>s = rename_list (map (\<lambda>(\<alpha>, p). lhs \<alpha>) rdp_A')"
    by simp
  have ren_lhs_\<alpha>s_alt:"ren_lhs_\<alpha>s = renamed_lhs_\<alpha>s" 
    unfolding ren_lhs_\<alpha>s renamed_lhs_\<alpha>s_def rdp_A'[symmetric] rename_list_def using rdp_A_eq
    by (simp add: map_nth_eq_conv split_beta)  
  then have hd_ren_lhs_\<alpha>s:"hd ren_lhs_\<alpha>s = renamed_lhs_\<alpha>1"
    by (simp add: ren_lhs_\<alpha>1_alt)
  let ?q="pos_diff q p" 
  let ?p="pos_diff p1 p"
  have p_hd:"?p = snd (hd rdp_A')"
    using hd_rdp_A' rdp_A' by force 
  obtain l' where l':"l' = replace_at (hd ren_lhs_\<alpha>s) ?q (map_vars_term (ren_l ren) (lhs \<beta>))"
    by simp 
  have l_alt:"l = l'"
    unfolding l_def l' renamed_lhs_\<beta>_def hd_ren_lhs_\<alpha>s by simp
  have overlap:"get_overlapping_part A' B' = Some A'" proof-
    have "filter (\<lambda>A''. measure_ov A'' B' \<noteq> 0) As' = As'" 
      using overlap_As'_B' by (smt (verit, best) filter_True in_set_idx) 
    then show ?thesis using A' single_steps_A' unfolding get_overlapping_part_def 
      by (smt (verit, ccfv_threshold) option.sel)
  qed
  have pq:"?q = [] \<or> snd (hd rdp_A') = []" proof(cases "p = q")
    case True
    show ?thesis unfolding True
      using prefix_pos_diff by blast
  next
    case False
    then have p:"p = p1" 
      unfolding p_def by auto
    then show ?thesis 
      using prefix_pos_diff by (metis hd_rdp_A' less_eq_pos_simps(5) order_pos.dual_order.eq_iff rdp_A' snd_eqD)
  qed
  have rdp_A'_alt:"map snd rdp_A' = map (\<lambda>(\<alpha>i, pi). pos_diff pi p) rdp_A" proof-
    have len:"length rdp_A' = length rdp_A"
      unfolding rdp_A' rdp_A_eq by simp 
    {fix i assume i:"i < length rdp_A'"
      then obtain \<alpha>i pi where \<alpha>ipi:"rdp_A' ! i = (\<alpha>i, pi)"
        by fastforce 
      with i have "(map (\<lambda>(\<alpha>i, pi). (\<alpha>i, p @ pi)) rdp_A') ! i = (\<alpha>i, p @ pi)"  
        by simp
      then have "map (\<lambda>(\<alpha>i, pi). pos_diff pi p) (map (\<lambda>(\<alpha>i, pi). (\<alpha>i, p @ pi)) rdp_A') ! i = pi"
        unfolding map_map nth_map[OF i] o_apply by (metis case_prod_conv less_eq_pos_simps(1) prefix_pos_diff same_append_eq)  
      with i have "(map snd rdp_A') ! i = map (\<lambda>(\<alpha>i, pi). pos_diff pi p) rdp_A ! i" 
        unfolding rdp_A' rdp_A_eq by (simp add: \<alpha>ipi)
    }
    with len show ?thesis
      by (metis length_map nth_equalityI)
  qed
  from tau_is_mgu have \<tau>:"is_mgu \<tau> (set (map2 (\<lambda>x y. (x, l' |_ y)) ren_lhs_\<alpha>s (map snd rdp_A')))"
    using rdp_A'_alt ren_lhs_\<alpha>s_alt l_alt by simp
  have As:"As' = map2 (\<lambda>(\<alpha>i, pi) i. (ctxt_of_pos_term pi (to_pterm (l' \<cdot> \<tau>)))
  \<langle>Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))\<rangle>) rdp_A' [0..<length rdp_A']"
  proof-
    have len:"length As' = length rdp_A'" 
      unfolding rdp_A'[symmetric] As'_def by (simp add: rdp_A_eq) 
    then have len':"length (zip rdp_A' [0..<length rdp_A']) = length As'" by simp
    {fix i assume i:"i < length As'" 
      then have i':"i < length (zip rdp_A [0..<length rdp_A])" 
        unfolding As'_def length_zip length_map by simp
      let ?\<alpha>i="fst (rdp_A' ! i)"
      let ?pi="snd (rdp_A' ! i)" 
      obtain \<alpha>i pi where \<alpha>ipi:"rdp_A' ! i = (\<alpha>i, pi)" "?\<alpha>i = \<alpha>i" "?pi = pi"
        by fastforce 
      then have "rdp_A ! i = (\<alpha>i, p @ pi)" 
        using rdp_A_eq i len unfolding rdp_A' by simp
      moreover then have "zip rdp_A [0..<length rdp_A] ! i = ((\<alpha>i, p @ pi), i)" 
        using i unfolding As'_def length_map length_zip by auto
      ultimately have "As' ! i = (ctxt_of_pos_term pi (to_pterm (l' \<cdot> \<tau>)))\<langle>Prule \<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule \<alpha>i)))\<rangle>" 
        using i unfolding As'_def l_alt rdp_A' length_map length_zip nth_map[OF i']
        by (metis (no_types, lifting) case_prod_conv min.strict_boundedE p_above_pi prefix_pos_diff same_append_eq snd_conv)
      then have "As' ! i = (ctxt_of_pos_term ?pi (to_pterm (l' \<cdot> \<tau>)))\<langle>Prule ?\<alpha>i (map (to_pterm \<circ> \<tau>) (map (rename_many' ren i) (var_rule ?\<alpha>i)))\<rangle>" 
        using \<alpha>ipi by simp
    }
    then show ?thesis
      using map_nth_eq_conv[OF len'] prod.collapse prod.simps(2)
      by (smt (verit, del_insts) add.left_neutral diff_zero len length_upt nth_upt nth_zip) 
  qed
  have join:"join_list As' = Some A'" using A' by simp
  have B':"B' = (ctxt_of_pos_term (pos_diff q p) (to_pterm (l' \<cdot> \<tau>)))\<langle>Prule \<beta> (map (to_pterm \<circ> \<tau> \<circ> rename_single ren) (var_rule \<beta>))\<rangle>"
    unfolding B'_def l_alt renamed_lhs_\<beta>_def
    by (smt (verit, best) \<beta> case_prodD left_lin left_linear_trs_def linear_term_var_vars_term_list map_vars_term_compose vars_map_vars_term) 
  show ?thesis 
    using sim_cpI[OF A'_wf B'_wf rdp_A' rdp_B' ren_lhs_\<alpha>s overlap l' pq \<tau> As join B'] .
qed

end

(*Helper lemma for Step 10*)
lemma target_B:"target B = (ctxt_of_pos_term p s)\<langle>target B' \<cdot> \<sigma>\<rangle>"
  unfolding B'_in_B unfolding to_pterm_ctxt_at_pos[OF p_poss] target_to_pterm_ctxt 
  using target_apply_subst[OF B'_wf] by (metis B'_wf target_to_pterm tgt_subst_simp to_pterm_subst)

end

context ren_wf_trs
begin

lemma okui_strongly_confluent:
 assumes closed:"\<And>A B. (A, B) \<in> sim_cp \<Longrightarrow> \<exists>v. (target A, v) \<in> (rstep R)\<^sup>* \<and> (target B, v) \<in> mstep R"
    and mstep:"(s,t) \<in> mstep R" and rstep:"(s, u) \<in> rstep R"
  shows "\<exists>v. (t, v) \<in> (mstep R)\<^sup>* \<and> (u, v) \<in> mstep R"
proof-
  from mstep obtain A where A:"source A = s \<and> target A = t" "A \<in> wf_pterm R"
    using mstep_to_pterm varcond by blast 
  (*also used in Step 2 of paper proof*)
  obtain B q \<beta> where B:"source B = s \<and> target B = u" "B = ll_single_redex s q \<beta>" and q:"q \<in> poss s" and \<beta>:"to_rule \<beta> \<in> R"
    using rstep_exists_single_redex[OF rstep] varcond left_lin by blast 
  have B_wf:"B \<in> wf_pterm R" 
    using single_redex_wf_pterm[OF \<beta>, of q s] q \<beta> left_lin unfolding B(2) left_linear_trs_def by fastforce  
  show ?thesis proof(cases "measure_ov A B")
    case 0
    with A B B_wf have "A re B \<noteq> None" 
      using orth_imp_residual_defined measure_zero_imp_orthogonal[OF ll_no_var_lhs ll_no_var_lhs] by simp 
    with A B B_wf obtain D where d:"A re B = Some D \<and> target B = source D \<and> D \<in> wf_pterm R"
      by (metis not_Some_eq residual_src_tgt residual_well_defined) 
    from 0 A B B_wf have "B re A \<noteq> None"
      using orth_imp_residual_defined measure_zero_imp_orthogonal[OF ll_no_var_lhs ll_no_var_lhs] measure_ov_symm by metis 
    with A B B_wf obtain C where c:"B re A = Some C \<and> target A = source C \<and> C \<in> wf_pterm R"
      by (metis not_Some_eq residual_src_tgt residual_well_defined) 
    from c d A B B_wf have "target C = target D" 
      using residual_tgt_tgt by blast 
    with c d A B show ?thesis 
      using pterm_to_mstep by (metis r_into_rtrancl)
  next
    case (Suc n)
    (*Step 1*)
    obtain rdp_A where rdp_A:"rdp_A = filter (\<lambda>(\<alpha>, p). measure_ov (ll_single_redex s p \<alpha>)  B \<noteq> 0) (redex_patterns A)"
      by blast
    obtain \<alpha>1 p1 where \<alpha>1p1:"(\<alpha>1, p1) = hd rdp_A"
      by (metis surj_pair) 
    from Suc have not_empty:"rdp_A \<noteq> []" 
      unfolding rdp_A by (smt (verit, del_insts) A(1) A(2) Zero_not_Suc case_prodI empty_filter_conv left_lin_no_var_lhs.measure_ov_imp_single_step_ov ll_no_var_lhs single_step_redex_patterns) 
    let ?As="map (\<lambda>(\<alpha>, p). ll_single_redex s p \<alpha>) rdp_A"
    have overlapping_part:"overlapping_part R rdp_A A B s ?As \<alpha>1 p1 \<beta> q"
      using overlapping_part.intro[OF ren_wf_trs_axioms] overlapping_part_axioms.intro[OF A(2) rdp_A] \<alpha>1p1 not_empty A B q \<beta> by force 
    (*Step 4*)
    let ?p="overlapping_part.p p1 q"
    let ?\<sigma>="overlapping_part.\<sigma> ren rdp_A s \<beta> q" 
    (*Step 7*)
    let ?B'="overlapping_part.B' ren rdp_A \<alpha>1 p1 \<beta> q"
    let ?As'="overlapping_part.As' ren rdp_A \<alpha>1 p1 \<beta> q"
    obtain A' where A':"Some A'= \<Squnion> ?As'" and A'_wf:"A' \<in> wf_pterm R" 
      using overlapping_part.exists_A'[OF overlapping_part] by auto
    (*Step 8*)
    from overlapping_part.exists_p'[OF overlapping_part] 
    obtain p' where p':"p' \<in> poss A" and ctxt_A:"source_ctxt (ctxt_of_pos_term p' A) = ctxt_of_pos_term ?p s"
      by blast
    let ?\<rho>="overlapping_part.\<rho> A A' p'" 
    (*step 9*)
    have "(A', ?B') \<in> sim_cp"
      using overlapping_part.A'_B'_sim_cp[OF overlapping_part A' A'_wf] by auto  
    (*step 10*)
    with closed obtain v' where seq:"(target A', v') \<in> (rstep R)\<^sup>*" and ms:"(target ?B', v') \<in> mstep R"
      by blast
    from ms obtain D' where D':"source D' = (target ?B')" "target D' = v'" "D' \<in> wf_pterm R"
      using mstep_to_pterm varcond by blast 
    let ?v="target (replace_at A p' (to_pterm v' \<cdot> ?\<rho>))"
    let ?D="replace_at A p' (D' \<cdot> ?\<rho>)" 
    have 1:"(t, ?v) \<in> (mstep R)\<^sup>*" proof-
      have "target A = target (ctxt_of_pos_term p' A)\<langle>to_pterm (target A') \<cdot> ?\<rho>\<rangle>" 
        using context_target[of "(ctxt_of_pos_term p' A)"] overlapping_part.A_key_lemma[OF overlapping_part A' A'_wf p' ctxt_A] 
          tgt_subst_simp[OF A'_wf] by metis
      then have "(target A, ?v) \<in> (rstep R)\<^sup>*" 
        using context_target rewrite_tgt[OF seq, of "(ctxt_of_pos_term p' A)" ?\<rho>] by simp
      with A(1) show ?thesis
        by (meson basic_trans_rules(31) rstep_mstep_subset rtrancl_mono) 
    qed
    have 2:"(u, ?v) \<in> mstep R" proof-
      have "source ?D = target B" proof-
        have ctxt_well:"ctxt_of_pos_term p' A \<in> wf_pterm_ctxt R" 
          using A(2) p' by (simp add: ctxt_of_pos_term_well) 
        have "target B = (ctxt_of_pos_term ?p s)\<langle>target ?B' \<cdot> ?\<sigma>\<rangle>"
          using overlapping_part.target_B[OF overlapping_part] .
        then show ?thesis 
          unfolding source_ctxt_apply_term[OF ctxt_well] source_apply_subst[OF D'(3)] D'(1) 
          unfolding overlapping_part.B'_src_\<rho>[OF overlapping_part A' A'_wf p' ctxt_A]
          using ctxt_A by auto
      qed
      moreover have "target ?D = ?v" 
        using D' by (metis (no_types, lifting) context_target tgt_subst_simp)
      moreover have "?D \<in> wf_pterm R" 
        using ctxt_wf_pterm[OF A(2) p'] apply_subst_wf_pterm[OF D'(3)] 
          overlapping_part.rho_x_wf[OF overlapping_part A' A'_wf p' ctxt_A] by force
      ultimately show ?thesis
        using B(1) pterm_to_mstep by fastforce 
    qed
    from 1 2 show ?thesis
      by auto
  qed
qed

end

section"Main Theorem"

theorem okui_imp_CR:
  assumes R_wf:"left_lin_wf_trs R"
  and closed:"\<And>A B. (A, B) \<in> ren.sim_cp ren R \<Longrightarrow> \<exists>v. (target A, v) \<in> (rstep R)\<^sup>* \<and> (target B, v) \<in> mstep R"
  shows "CR (rstep R)"
proof-
  from R_wf have R:"ren_wf_trs R" 
    by (simp add: ren_wf_trs_def)
  have "strongly_confluent (mstep R)" proof(rule strongly_confluentI)
    fix x y z assume m1:"(x, y) \<in> mstep R" and m2:"(x, z) \<in> mstep R"
    from m2 obtain n where "(x, z) \<in> (rstep R)^^n" 
      using rtrancl_imp_UN_relpow mstep_imp_rsteps by blast
    with m1 show "\<exists>u.(y, u) \<in> (mstep R)\<^sup>* \<and> (z, u) \<in> (mstep R)\<^sup>=" proof(induct n arbitrary: x y)
      case 0
      with m1 show ?case by auto
    next
      case (Suc n)
      then obtain x' where x':"(x, x') \<in> rstep R" "(x', z) \<in> (rstep R)^^n"
        by (meson relpow_Suc_D2) 
      from ren_wf_trs.okui_strongly_confluent[OF R] assms Suc(2) x'(1) obtain v where v:"(y, v) \<in> (mstep R)\<^sup>*" "(x', v) \<in> mstep R"
        by blast                                                     
      from Suc(1)[OF v(2) x'(2)] v(1) show ?case
        by (meson rtrancl_trans)
    qed 
  qed
  then show ?thesis
    by (meson CR_between_imp_CR mstep_rsteps_subset rstep_mstep_subset strong_confluence_imp_CR) 
qed

end
