text \<open>Implementation of Gabow_SCC via RBTs.\<close>
theory Gabow_SCC_RBT
imports 
  CAVA_Automata.Digraph_Impl
  Gabow_SCC.Gabow_SCC
  Auxx.Map_Choice
  Diff_Array_Code_Haskell
begin
  
text \<open>The following code has mainly been copied from code mainly copied from Gabow_SCC_Code where
  @{const dflt_ahm_rel} has been replaced by @{const dflt_rm_rel}.

  Moreover, we provide a list based interface to the SCC-algorithm.\<close>

consts i_node_state :: interface

definition "node_state_rel \<equiv> {(-1::int,DONE)} \<union> {(int k,STACK k) | k. True }"
lemma node_state_rel_simps[simp]:
  "(i,DONE)\<in>node_state_rel \<longleftrightarrow> i=-1"
  "(i,STACK n)\<in>node_state_rel \<longleftrightarrow> i = int n"
  unfolding node_state_rel_def
  by auto

lemma node_state_rel_sv[simp,intro!,relator_props]:
  "single_valued node_state_rel"
  unfolding node_state_rel_def
  by (auto intro: single_valuedI)

lemmas [autoref_rel_intf] = REL_INTFI[of node_state_rel i_node_state]

primrec is_DONE where
  "is_DONE DONE = True"
| "is_DONE (STACK _) = False"

lemma node_state_rel_refine[autoref_rules]:
  "(-1,DONE)\<in>node_state_rel"
  "(int,STACK)\<in>nat_rel\<rightarrow>node_state_rel"
  "(\<lambda>i. i<0,is_DONE)\<in>node_state_rel\<rightarrow>bool_rel"
  "((\<lambda>f g i. if i\<ge>0 then f (nat i) else g),case_node_state)
    \<in>(nat_rel \<rightarrow> R) \<rightarrow> R \<rightarrow> node_state_rel \<rightarrow> R"
  unfolding node_state_rel_def 
    apply auto [3]
    apply (fastforce dest: fun_relD)
    done

lemma [autoref_op_pat]: 
  "(x=DONE) \<equiv> is_DONE x"
  "(DONE=x) \<equiv> is_DONE x"
  apply (auto intro!: eq_reflection)
  apply ((cases x, simp_all) [])+
  done

(* TODO: Make changing the Autoref-config simpler, by concentrating
    everything here *)
consts i_node :: interface

(* TODO: Move generic part of this locale to Digraph_impl *)
locale fr_graph_impl_loc = fr_graph G
  for mrel and G_impl and G :: "('v::linorder,'more) graph_rec_scheme"
  +
  assumes G_refine: "(G_impl,G)\<in>\<langle>mrel,Id\<rangle>g_impl_rel_ext"
begin
abbreviation "node_rel \<equiv> Id :: ('v \<times> _) set"
abbreviation "map_rel \<equiv> dflt_rm_rel"
  term rbt_map_rel
  lemmas [autoref_rel_intf] = REL_INTFI[of node_rel i_node]

  lemmas [autoref_rules] = G_refine

  lemma locale_this: "fr_graph_impl_loc mrel G_impl G"
    by unfold_locales

  abbreviation "oGSi_rel \<equiv> \<langle>node_rel,node_state_rel\<rangle>map_rel"

  abbreviation "GSi_rel \<equiv> 
    \<langle>node_rel\<rangle>as_rel 
    \<times>\<^sub>r \<langle>nat_rel\<rangle>as_rel 
    \<times>\<^sub>r \<langle>node_rel,node_state_rel\<rangle>map_rel
    \<times>\<^sub>r \<langle>nat_rel \<times>\<^sub>r \<langle>node_rel\<rangle>list_set_rel\<rangle>as_rel"

  lemmas [autoref_op_pat] = GS.S_def GS.B_def GS.I_def GS.P_def

end

section \<open>Generating the Code\<close>

context fr_graph_impl_loc
begin
  schematic_goal push_code_aux: "(?c,push_impl)\<in>node_rel \<rightarrow> GSi_rel \<rightarrow> GSi_rel"
    unfolding push_impl_def_opt[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) push_code uses fr_graph_impl_loc.push_code_aux
  lemmas [autoref_rules] = push_code.refine[OF locale_this]
  
  schematic_goal pop_code_aux: "(?c,pop_impl)\<in>GSi_rel \<rightarrow> \<langle>GSi_rel\<rangle>nres_rel"
    unfolding pop_impl_def_opt[abs_def]
    unfolding GS.mark_as_done_def
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) pop_code uses fr_graph_impl_loc.pop_code_aux
  lemmas [autoref_rules] = pop_code.refine[OF locale_this]

  schematic_goal S_idx_of_code_aux: 
    notes [autoref_rules] = IdI[of "undefined::nat"] (* TODO: hack!*)
    shows "(?c,GS.S_idx_of)\<in>GSi_rel \<rightarrow> node_rel \<rightarrow> nat_rel"
    unfolding GS.S_idx_of_def[abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) S_idx_of_code 
    uses fr_graph_impl_loc.S_idx_of_code_aux
  lemmas [autoref_rules] = S_idx_of_code.refine[OF locale_this] 

  schematic_goal idx_of_code_aux:
    notes [autoref_rules] = IdI[of "undefined::nat"] (* TODO: hack!*)
    shows "(?c,GS.idx_of_impl)\<in> GSi_rel \<rightarrow> node_rel \<rightarrow> \<langle>nat_rel\<rangle>nres_rel"
    unfolding 
      GS.idx_of_impl_def[abs_def, unfolded GS.find_seg_impl_def GS.S_idx_of_def,
        THEN opt_GSdef, unfolded GS_sel_simps, abs_def]
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) idx_of_code uses fr_graph_impl_loc.idx_of_code_aux
  lemmas [autoref_rules] = idx_of_code.refine[OF locale_this] 

  schematic_goal collapse_code_aux: 
    "(?c,collapse_impl)\<in>node_rel \<rightarrow> GSi_rel \<rightarrow> \<langle>GSi_rel\<rangle>nres_rel"
    unfolding collapse_impl_def_opt[abs_def] 
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal))
    done
  concrete_definition (in -) collapse_code 
    uses fr_graph_impl_loc.collapse_code_aux
  lemmas [autoref_rules] = collapse_code.refine[OF locale_this] 

  schematic_goal select_edge_code_aux:
    "(?c,select_edge_impl) 
      \<in> GSi_rel \<rightarrow> \<langle>\<langle>node_rel\<rangle>option_rel \<times>\<^sub>r GSi_rel\<rangle>nres_rel"
    unfolding select_edge_impl_def_opt[abs_def] 

    using [[autoref_trace_failed_id]]
    using [[goals_limit=1]]
    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) select_edge_code 
    uses fr_graph_impl_loc.select_edge_code_aux
  lemmas [autoref_rules] = select_edge_code.refine[OF locale_this] 

  context begin interpretation autoref_syn .

    term fr_graph.pop_impl
    lemma [autoref_op_pat]: 
      "push_impl \<equiv> OP push_impl"
      "collapse_impl \<equiv> OP collapse_impl"
      "select_edge_impl \<equiv> OP select_edge_impl"
      "pop_impl \<equiv> OP pop_impl"
      by simp_all
  
  end

  schematic_goal skeleton_code_aux:
    "(?c,skeleton_impl) \<in> \<langle>oGSi_rel\<rangle>nres_rel"
    unfolding skeleton_impl_def[abs_def] initial_impl_def GS_initial_impl_def
    unfolding path_is_empty_impl_def is_on_stack_impl_def is_done_impl_def 
      is_done_oimpl_def
    unfolding GS.is_on_stack_impl_def GS.is_done_impl_def
    using [[autoref_trace_failed_id]]

    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) skeleton_code 
    uses fr_graph_impl_loc.skeleton_code_aux
  lemmas [autoref_rules] = skeleton_code.refine[OF locale_this] 
  

  schematic_goal pop_tr_aux: "RETURN ?c \<le> pop_code s"
    unfolding pop_code_def by refine_transfer
  concrete_definition (in -) pop_tr uses fr_graph_impl_loc.pop_tr_aux
  lemmas [refine_transfer] = pop_tr.refine[OF locale_this]

  schematic_goal select_edge_tr_aux: "RETURN ?c \<le> select_edge_code s"
    unfolding select_edge_code_def by refine_transfer
  concrete_definition (in -) select_edge_tr 
    uses fr_graph_impl_loc.select_edge_tr_aux
  lemmas [refine_transfer] = select_edge_tr.refine[OF locale_this]

  schematic_goal idx_of_tr_aux: "RETURN ?c \<le> idx_of_code v s"
    unfolding idx_of_code_def by refine_transfer
  concrete_definition (in -) idx_of_tr uses fr_graph_impl_loc.idx_of_tr_aux
  lemmas [refine_transfer] = idx_of_tr.refine[OF locale_this]

  schematic_goal collapse_tr_aux: "RETURN ?c \<le> collapse_code v s"
    unfolding collapse_code_def by refine_transfer
  concrete_definition (in -) collapse_tr uses fr_graph_impl_loc.collapse_tr_aux
  lemmas [refine_transfer] = collapse_tr.refine[OF locale_this]

  schematic_goal skeleton_tr_aux: "RETURN ?c \<le> skeleton_code g"
    unfolding skeleton_code_def by refine_transfer
  concrete_definition (in -) skeleton_tr uses fr_graph_impl_loc.skeleton_tr_aux
  lemmas [refine_transfer] = skeleton_tr.refine[OF locale_this]

end


(* next file *)
  
context fr_graph_impl_loc
begin
  schematic_goal last_seg_code_aux: 
    "(?c,last_seg_impl)\<in>GSi_rel \<rightarrow> \<langle>\<langle>node_rel\<rangle>list_set_rel\<rangle>nres_rel"
    unfolding last_seg_impl_def_opt[abs_def] 
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal,trace))
    done
  concrete_definition (in -) last_seg_code 
    uses fr_graph_impl_loc.last_seg_code_aux
  lemmas [autoref_rules] = last_seg_code.refine[OF locale_this]

  context begin interpretation autoref_syn .

    lemma [autoref_op_pat]: 
      "last_seg_impl \<equiv> OP last_seg_impl"
      by simp_all
  end

  schematic_goal compute_SCC_code_aux:
    "(?c,compute_SCC_impl) \<in> \<langle>\<langle>\<langle>node_rel\<rangle>list_set_rel\<rangle>list_rel\<rangle>nres_rel"
    unfolding compute_SCC_impl_def[abs_def] initial_impl_def GS_initial_impl_def
    unfolding path_is_empty_impl_def is_on_stack_impl_def is_done_impl_def 
      is_done_oimpl_def
    unfolding GS.is_on_stack_impl_def GS.is_done_impl_def
    using [[autoref_trace_failed_id]]
    apply (autoref (keep_goal,trace))
    done

  concrete_definition (in -) compute_SCC_code 
    uses fr_graph_impl_loc.compute_SCC_code_aux
  lemmas [autoref_rules] = compute_SCC_code.refine[OF locale_this] 

  schematic_goal last_seg_tr_aux: "RETURN ?c \<le> last_seg_code s"
    unfolding last_seg_code_def by refine_transfer
  concrete_definition (in -) last_seg_tr uses fr_graph_impl_loc.last_seg_tr_aux
  lemmas [refine_transfer] = last_seg_tr.refine[OF locale_this]

  schematic_goal compute_SCC_tr_aux: "RETURN ?c \<le> compute_SCC_code g"
    unfolding compute_SCC_code_def by refine_transfer
  concrete_definition (in -) compute_SCC_tr 
    uses fr_graph_impl_loc.compute_SCC_tr_aux
  lemmas [refine_transfer] = compute_SCC_tr.refine[OF locale_this]
end
  
  
section \<open>Correctness Theorem\<close>

theorem compute_SCC_tr_correct:
  \<comment> \<open>Correctness theorem for the constant we extracted to SML\<close>
  fixes Re
  fixes G :: "('a::linorder,'more) graph_rec_scheme"
  assumes A: "(G_impl,G)\<in>\<langle>Re,Id\<rangle>g_impl_rel_ext"
  assumes C: "fr_graph G"
  shows "RETURN (compute_SCC_tr G_impl) 
  \<le> \<Down>(\<langle>\<langle>Id\<rangle>list_set_rel\<rangle>list_rel) (fr_graph.compute_SCC_spec G)"
proof -
  from C interpret fr_graph G .
  have I: "fr_graph_impl_loc Re G_impl G"
    apply unfold_locales using A .
  then interpret fr_graph_impl_loc Re G_impl G .

  note compute_SCC_tr.refine[OF I]
  also note compute_SCC_code.refine[OF I, THEN nres_relD]
  also note compute_SCC_impl_refine
  also note compute_SCC_correct
  finally show ?thesis using A by simp
qed
  
  
section \<open>This part now presents a list based interface and only returns non-trivial SCCs, i.e., singleton
  nodes without loops are not returned.\<close>
  
definition edges_to_adj_fun :: "('a :: compare_order \<times> 'a)list \<Rightarrow> 'a \<Rightarrow> 'a list" where
  "edges_to_adj_fun E = precompute_fun (\<lambda> a. remdups [ snd e . e \<leftarrow> E, fst e = a]) (remdups (map fst E @ map snd E))" 
  
definition create_graph_impl :: "('a :: compare_order \<times> 'a)list \<Rightarrow> ('a \<Rightarrow> bool, 'a \<Rightarrow> 'a list, 'a list)gen_g_impl" where
  "create_graph_impl E = \<lparr> gi_V = (\<lambda> v. v \<in> set (map fst E @ map snd E)), 
     gi_E = edges_to_adj_fun E, gi_V0 = remdups (map fst E @ map snd E)\<rparr>" 

definition create_graph :: "('a \<times> 'a)list \<Rightarrow> 'a graph_rec" where
  "create_graph E = \<lparr> g_V = set (map fst E @ map snd E), g_E = set E, g_V0 = set (map fst E @ map snd E)\<rparr>" 
  
definition scc_decomp :: "('a :: compare_order \<times> 'a)list \<Rightarrow> 'a list list" where
  "scc_decomp E = filter (\<lambda> pre_scc. length pre_scc \<noteq> 1 \<or> (hd pre_scc, hd pre_scc) \<in> set E) (compute_SCC_tr (create_graph_impl E))" 

lemma scc_decomp_code[code]: 
  "scc_decomp E = (let EE = set E in filter (\<lambda> pre_scc. case pre_scc of [v] \<Rightarrow> (v,v) \<in> EE | _ \<Rightarrow> True) (compute_SCC_tr (create_graph_impl E)))" 
  unfolding scc_decomp_def Let_def
  by (rule filter_cong[OF refl], auto split: list.splits)
  
lemma fr_graph_create_graph: "fr_graph (create_graph E)" 
proof -
  note d = create_graph_def
  interpret graph "create_graph E" 
  proof
    show "g_V0 (create_graph E) \<subseteq> g_V (create_graph E)" unfolding d by auto
    show "g_E (create_graph E) \<subseteq> g_V (create_graph E) \<times> g_V (create_graph E)" unfolding d by auto
  qed
  show ?thesis
  proof
    show "finite reachable" 
      by (rule finite_subset[OF reachable_V], auto simp: d)
  qed
qed
  
lemma create_graph_impl: "(create_graph_impl E, create_graph E) \<in> \<langle>unit_rel, Id\<rangle>g_impl_rel_ext" 
  unfolding create_graph_impl_def create_graph_def g_impl_rel_ext_def gen_g_impl_rel_ext_def
    fun_set_rel_def build_rel_def slg_rel_def
proof (auto)
  show "(remdups (map fst E @ map snd E), fst ` set E \<union> snd ` set E) \<in> \<langle>Id\<rangle>list_set_rel" 
    by (auto simp: list_set_rel_def br_def)
next
  have id: "(\<forall> x \<in> Id. P x) = (\<forall> x. P (x,x))" for P by auto
  show "(edges_to_adj_fun E, set E)
    \<in> (Id \<rightarrow> \<langle>Id\<rangle>list_set_rel) O {(c, a). a = {(u, v). v \<in> c u}}" 
    unfolding list_set_rel_def br_def fun_rel_def id split
  proof (standard; standard, unfold split)
    let ?f = "\<lambda> u. set E `` {u}" 
    show "set E = {(u, v). v \<in> ?f u}" by auto
    show "\<forall>x. (edges_to_adj_fun E x, ?f x)
        \<in> \<langle>Id\<rangle>list_rel O {(c, a). a = set c \<and> distinct c}"
      by (auto simp: edges_to_adj_fun_def)
  qed
qed
  
lemma list_all2_eq[simp]: "list_all2 (=) xs ys = (xs = ys)" for xs ys
    unfolding list_all2_conv_all_nth by (auto intro: nth_equalityI)
 
lemma scc_decomp: "set ` set (scc_decomp E) = { C. is_scc (set E) C \<and> C \<times> C \<subseteq> (set E)^+}"
proof -
  let ?GI = "create_graph_impl E" 
  let ?G = "create_graph E" 
  let ?E = "g_E ?G" 
  have E: "?E = set E" unfolding create_graph_def by auto
  interpret fr_graph ?G by (rule fr_graph_create_graph)      
  have reach: "reachable = g_V ?G" 
  proof
    show "reachable \<subseteq> V" by (rule reachable_V)
    have "V \<subseteq> V0" unfolding create_graph_def by auto
    also have "\<dots> \<subseteq> reachable" by auto
    finally show "V \<subseteq> reachable" .
  qed
  have id: "{(xs, ys). xs = ys} = Id" by auto
  define sccs where "sccs = compute_SCC_tr (create_graph_impl E)" 
  from compute_SCC_tr_correct[of ?GI ?G, OF create_graph_impl fr_graph_create_graph]  
  have "RETURN (compute_SCC_tr ?GI)
      \<le> \<Down> (\<langle>\<langle>Id\<rangle>list_set_rel\<rangle>list_rel) (compute_SCC_spec)" .
  from this[unfolded reach compute_SCC_spec_def conc_fun_def scc_decomp_def[symmetric], 
      simplified, unfolded list_set_rel_def list_rel_def br_def, 
      simplified, unfolded list_all2_eq E id, simplified]
  obtain x where x: 
    "\<Union>(set x) = V" 
    "\<forall>C\<in>set x. is_scc (set E) C" 
    "list_all2 (\<lambda>x x'. x' = set x \<and> distinct x) sccs x" 
    unfolding sccs_def
    by blast
  from x(3)[unfolded list_all2_conv_all_nth] x(2) have 
    sccs: "\<Union>(set ` set sccs) = V" 
      "\<And> C. C \<in> set sccs \<Longrightarrow> is_scc (set E) (set C) \<and> distinct C" 
    unfolding set_conv_nth[of sccs] set_conv_nth[of x] x(1)[symmetric] by auto
  show ?thesis 
  proof (rule set_eqI, goal_cases)
    case (1 C)
    have "(C \<in> {C. is_scc (set E) C \<and> C \<times> C \<subseteq> (set E)\<^sup>+})
      = (is_scc (set E) C \<and> C \<times> C \<subseteq> (set E)^+)" by auto
    also have "\<dots> = (C \<in> set ` {x \<in> set sccs. length x \<noteq> 1 \<or> (hd x, hd x) \<in> set E})"
    proof
      assume "C \<in> set ` {x \<in> set sccs. length x \<noteq> 1 \<or> (hd x, hd x) \<in> set E}" 
      then obtain c where C: "C = set c" and c: "c \<in> set sccs" "length c \<noteq> 1 \<or> (hd c, hd c) \<in> set E" by auto
      from sccs(2)[OF c(1)] C have scc: "is_scc (set E) C" and dist: "distinct c" by auto
      have "C \<times> C \<subseteq> (set E)\<^sup>+" 
      proof (cases "length c = 1")
        case True
        then obtain v where cv: "c = [v]" by (cases c; cases "tl c"; auto)
        with c(2) have vv: "(v,v) \<in> (set E)^+" by auto
        from cv C have C: "C = {v}" by auto
        show ?thesis unfolding C using vv by auto
      next
        case False
        from scc have "C \<noteq> {}" by auto
        with False C obtain v w d where c: "c = v # w # d" by (cases c; cases "tl c"; auto)
        with dist have vw: "v \<noteq> w" by auto
        from C c have v: "v \<in> C" "w \<in> C" by auto
        note conn = is_scc_connected[OF scc] 
        from conn[OF v] have "(v,w) \<in> (set E)^*" .
        with vw have vw: "(v,w) \<in> (set E)^+" by (meson rtranclD)
        {
          fix a b
          assume "(a,b) \<in> C \<times> C" 
          then have a: "a \<in> C" "b \<in> C" by auto
          from conn[OF a(1) v(1)] vw conn[OF v(2) a(2)] have "(a,b) \<in> (set E)^+" by auto
        }
        then show ?thesis by auto
      qed
      with scc show "is_scc (set E) C \<and> C \<times> C \<subseteq> (set E)^+" by blast
    next
      assume "is_scc (set E) C \<and> C \<times> C \<subseteq> (set E)^+" 
      then have scc: "is_scc (set E) C" and CC: "C \<times> C \<subseteq> (set E)^+" by auto
      from scc have "C \<noteq> {}" by auto
      then obtain v where vC: "v \<in> C" by auto
      with CC have "(v,v) \<in> (set E)^+" by auto
      from tranclD[OF this] obtain w where vw: "(v,w) \<in> set E" and wv: "(w,v) \<in> (set E)^*" by auto
      then have "v \<in> V" unfolding create_graph_def by auto
      with sccs obtain D where D: "D \<in> set sccs" and vD: "v \<in> set D" by auto
      from sccs(2)[OF D] have "is_scc (set E) (set D)" ..
      from is_scc_unique[OF this scc vD vC] have C: "C = set D" by auto
      from vw have "(v,w) \<in> (set E)^*" by auto
      from is_scc_closed[OF scc vC this wv] have wC: "w \<in> C" by auto
      {
        assume "length D = 1" 
        with vD have D: "D = [v]" by (cases D, auto)
        with wC C have "w = v" by auto
        with D vw have "(hd D, hd D) \<in> set E" by auto
      }
      with C D show "C \<in> set ` {x \<in> set sccs. length x \<noteq> 1 \<or> (hd x, hd x) \<in> set E}" by auto
    qed
    also have "\<dots> = (C \<in> set ` set (scc_decomp E))" unfolding scc_decomp_def sccs_def by simp
    finally show ?case by simp
  qed
qed
    
lemma scc_decomp_empty: "scc_decomp E = [] \<longleftrightarrow> (\<forall> C. is_scc (set E) C \<longrightarrow> C \<times> C \<subseteq> (set E)^+ \<longrightarrow> False)" 
proof - 
  have id: "scc_decomp E = [] \<longleftrightarrow> set ` set (scc_decomp E) = {}" by simp
  show ?thesis unfolding id scc_decomp by auto
qed
  
lemma get_scc_from_component: assumes C: "C \<noteq> {}" "C \<times> C \<subseteq> E^+" 
  shows "\<exists> S. C \<subseteq> S \<and> is_scc E S \<and> S \<times> S \<subseteq> E^+" 
proof -
  from C(1) obtain v where vC: "v \<in> C" by auto
  with C(2) have vv: "(v,v) \<in> E^+" by auto
  from is_scc_ex[of E v] obtain S where S: "is_scc E S" and vS: "v \<in> S" by auto
  note conn = is_scc_connected[OF S]
  {
    fix w
    assume wC: "w \<in> C" 
    with vC C(2) have vw: "(v,w) \<in> E^*" "(w,v) \<in> E^*" by auto
    from is_scc_closed[OF S vS vw] have "w \<in> S" by auto
  } then have CS: "C \<subseteq> S" by auto
  {
    fix w u
    assume w: "w \<in> S" and u: "u \<in> S" 
    from conn[OF w vS] vv conn[OF vS u] have "(w,u) \<in> E^+" by auto
  } then have SS: "S \<times> S \<subseteq> E^+" by auto
  from CS SS S show ?thesis by blast
qed 
  
  
end
