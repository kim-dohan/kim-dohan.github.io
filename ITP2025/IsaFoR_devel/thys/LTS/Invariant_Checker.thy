theory Invariant_Checker
imports 
  Certification_Monads.Check_Monad
  "HOL-Library.RBT_Mapping"
  LTS
  Show_LTS
begin

text \<open>In this theory we provide an invariant checker which establishes the 
  @{const lts.invariant} property.\<close>

(* TODO: move *)
lemma is_ok_try_catch: "isOK (try e catch f) = (isOK(e) \<or> isOK( f (projl e)))" 
  by (cases e, auto simp: isOK_def)

subsection \<open>ART\<close>

datatype ('f,'v,'t,'l,'n) art_edge = is_cover_node: Cover 'n | Children "(('f,'v,'t,'l) transition_rule \<times> 'n) list"

record ('f,'v,'t,'l,'n) art =
  initial_nodes :: "'n list" 
  nodes :: "'n list"
  edge :: "'n \<Rightarrow> ('f,'v,'t,'l,'n) art_edge"
  node_location :: "'n \<Rightarrow> 'l"
  node_invariant :: "'n \<Rightarrow> ('f,'v,'t) exp formula"

fun (in prelogic) transition_entailment ::
  "('l \<Rightarrow> ('f,'v,'t) exp formula) \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> ('f,'v,'t,'l) transition_rule \<Rightarrow> ('f,'v,'t) exp formula \<Rightarrow> bool"
where
  "transition_entailment lc \<phi> (Transition l r \<chi>) \<psi> =
  (rename_vars Pre (lc l) \<and>\<^sub>f rename_vars Post (lc r) \<and>\<^sub>f rename_vars Pre \<phi> \<and>\<^sub>f \<chi> \<Longrightarrow>\<^sub>f rename_vars Post \<psi>)"

definition get_disj_invariant :: "('f,'v,'t,'l,'n) art \<Rightarrow> 'l \<Rightarrow> ('f,'v,'t) exp formula"
  where "get_disj_invariant A l \<equiv> Disjunction (map (node_invariant A) (filter (\<lambda>a. node_location A a = l \<and> \<not> is_cover_node (edge A a)) (nodes A)))"


record ('s,'l,'n,'tr) hinter =
  nodes :: "'n list"
  succ_trans_list :: "'l \<Rightarrow> 'tr list"
  cover_hints :: "'n \<Rightarrow> 's"
  transition_hints :: "'n \<Rightarrow> 's list option"

hide_const (open) nodes

locale pre_art_checker =
  pre_lts_checker
  where type_fixer = type_fixer
    and logic_checker = tc
    and showsl_atom = sa
    and normalize_lit = ne 
    and normalized_lit = ned + 
  tc2: pre_logic_checker
  where type_fixer = "TYPE('f \<times> 'v trans_var \<times> 't \<times> 'd \<times> 's)"
    and logic_checker = tc2
    and showsl_atom = sa2
    and normalize_lit = ne2
    and normalized_lit = ned2
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's::{default,showl}) itself"
  and tc tc2 sa sa2 ne ne2 ned ned2
begin

definition "art A \<equiv> \<forall>a \<in> set (nodes A). formula (node_invariant A a)"

lemma artD[dest]: "art A \<Longrightarrow> a \<in> set (nodes A) \<Longrightarrow> formula (node_invariant A a)" by (auto simp:art_def)
lemma artE[elim]:
  assumes "art A" "(\<And>a. a \<in> set (nodes A) \<Longrightarrow> formula (node_invariant A a)) \<Longrightarrow> thesis" shows thesis
  using assms by (auto simp: art_def)

definition "check_art A \<equiv> check (art A) (showsl_lit (STR ''ill-formed invariant''))"

lemma check_art[intro]: "isOK (check_art A) \<Longrightarrow> art A" unfolding check_art_def by auto

definition "initial_cond A \<equiv>
  set (initial_nodes A) \<subseteq> set (nodes A) \<and>
  (\<forall> a \<in> set (initial_nodes A). node_invariant A a = form_True)"

definition "simulation_cond A P \<equiv>
  lts.initial P \<subseteq> node_location A ` set (initial_nodes A) \<and>
  (\<forall> a children \<tau>.
    a \<in> set (nodes A)
    \<longrightarrow> edge A a = Children children
    \<longrightarrow> satisfiable (node_invariant A a)
    \<longrightarrow> \<tau> \<in> transition_rules P
    \<longrightarrow> source \<tau> = node_location A a
    \<longrightarrow> (\<exists> b \<in> set (nodes A). (\<tau>, b) \<in> set children \<and> node_location A b = target \<tau>))"

definition "cover_edges_cond A \<equiv> \<forall> a b.
    a \<in> set (nodes A)
    \<longrightarrow> edge A a = Cover b
    \<longrightarrow> b \<in> set (nodes A) \<and>
      node_location A a = node_location A b \<and>
      \<not> is_cover_node (edge A b) \<and>
      node_invariant A a \<Longrightarrow>\<^sub>f node_invariant A b"

definition "children_edges_cond A P \<equiv> \<forall> a children \<tau> b.
    a \<in> set (nodes A)
    \<longrightarrow> edge A a = Children children
    \<longrightarrow> \<tau> \<in> transition_rules P
    \<longrightarrow> b \<in> set (nodes A)
    \<longrightarrow> (\<tau>,b) \<in> set children
    \<longrightarrow> transition_entailment (assertion P) (node_invariant A a) \<tau> (node_invariant A b)"

definition "well_formed A P \<equiv>
  children_edges_cond A P \<and> cover_edges_cond A \<and> initial_cond A \<and> simulation_cond A P \<and> art A"

fun corresponds_to where
  "corresponds_to A (State \<alpha> l) a  = (node_location A a = l \<and> (\<alpha> \<Turnstile> node_invariant A a))"

lemma formula_node_invariant [intro]: "well_formed A P \<Longrightarrow> a \<in> set (nodes A) \<Longrightarrow> formula (node_invariant A a)"
  unfolding well_formed_def art_def by auto

lemma well_formed_imp_disj_invariant:
  assumes "well_formed A P"
  and lts: "lts P"
  shows "invariant P l (get_disj_invariant A l)" (is "invariant _ _ ?\<phi>")
proof (intro invariantI)
  note [intro] = formula_node_invariant[OF assms(1)]
  show "formula ?\<phi>" unfolding formula_ex get_disj_invariant_def by auto
  fix \<alpha>
  assume reach: "State \<alpha> l \<in> reachable_states P"
  from reachable_state[OF reach] have state: "state_lts P (State \<alpha> l)" . 
  then have \<alpha>: "assignment \<alpha>" by auto
  from reach obtain init
    where init: "init \<in> initial_states P"
      and steps: "(init, State \<alpha> l) \<in> (transition P)^*" by auto
  from assms[unfolded well_formed_def]
  have ic: "initial_cond A"
   and sc: "simulation_cond A P" and cec: "children_edges_cond A P"
   and cc: "cover_edges_cond A" and art: "art A" by auto
  obtain l0 \<alpha>0 where *: "init = State \<alpha>0 l0" by (cases init, auto)
  with init[unfolded initial_states_def]
  have **: "l0 \<in> lts.initial P" "state_lts P init" by auto
  from this(1) sc[unfolded simulation_cond_def] obtain n0 where "n0 \<in> set (initial_nodes A)" 
    "l0 = node_location A n0" by auto
  with ic **(2) * have ic: "n0 \<in> set (nodes A)" "corresponds_to A init n0"
    by (auto simp: initial_cond_def)
  {
    fix s1 s2 a1
    assume s1t1: "(s1,s2) \<in> transition P" and s1a1: "corresponds_to A s1 a1" and a1: "a1 \<in> set (nodes A)"
    from s1t1 have "\<exists> a2 \<in> set (nodes A). corresponds_to A s2 a2"
    proof(elim mem_transitionE, goal_cases)
      case (1 \<phi> \<gamma>)
      from 1(1,4) lts have \<phi>: "formula \<phi>" unfolding lts_def by auto
      let ?\<alpha> = "(pre_post_inter (valuation s1) (valuation s2) \<gamma>)"
      from 1 have ass: "assignment ?\<alpha>" 
        and lc: "valuation s1 \<Turnstile> assertion P (location s1)" "valuation s2 \<Turnstile> assertion P (location s2)" by auto
      have "\<exists> a1 tas. corresponds_to A s1 a1 \<and> edge A a1 = Children tas \<and> a1 \<in> set (nodes A)"
      proof (cases "edge A a1")
        case (Children tas)
        with s1a1 a1 show ?thesis by blast
      next
        case (Cover b)
        from cc[unfolded cover_edges_cond_def, rule_format, OF a1 Cover] obtain tas where
          b: "b \<in> set (nodes A)" and loc: "node_location A a1 = node_location A b"
          and edge: "edge A b = Children tas"
          and impl: "node_invariant A a1 \<Longrightarrow>\<^sub>f node_invariant A b" by (cases "edge A b", auto)
        show ?thesis
        proof (rule exI[of _ b], rule exI[of _ tas], intro conjI)
          from s1a1 loc
          have "node_location A b = location s1" and "valuation s1 \<Turnstile> node_invariant A a1" by (induct s1, auto)
          with impl 1 show "corresponds_to A s1 b" by (cases s1, auto simp: satisfies_Language)
        qed (insert b edge, auto)
      qed
      then obtain a1 tas where s1a1: "corresponds_to A s1 a1"
        and edge: "edge A a1 = Children tas"
        and a1: "a1 \<in> set (nodes A)" by blast
      from s1a1 have l1: "location s1 = node_location A a1"
        and \<alpha>1: "valuation s1 \<Turnstile> node_invariant A a1" by (induct s1, auto)
      let ?\<tau> = "Transition (location s1) (location s2) \<phi>"
      have "assignment (valuation s1)" using 1(2) state_def by blast
      with \<alpha>1 have "satisfiable (node_invariant A a1)" unfolding satisfiable_def by auto
      from sc[unfolded simulation_cond_def, THEN conjunct2, rule_format, OF a1 edge this 1(1)] trans l1 1
      obtain b where b: "b \<in> set (nodes A)" and mem: "(?\<tau>, b) \<in> set tas" and l2: "node_location A b = location s2" by auto
      have "valuation s2 \<Turnstile> node_invariant A b"
      proof(subst satisfies_rename_vars[symmetric])
        from cec[unfolded children_edges_cond_def, rule_format, OF a1 edge 1(1) b mem]
        have "transition_entailment (assertion P) (node_invariant A a1) ?\<tau> (node_invariant A b)".
        from this 1
        have *: "rename_vars Pre (assertion P (location s1)) 
          \<and>\<^sub>f rename_vars Post (assertion P (location s2)) 
          \<and>\<^sub>f rename_vars Pre (node_invariant A a1) \<and>\<^sub>f \<phi> \<Longrightarrow>\<^sub>f
          rename_vars Post (node_invariant A b)"
          by auto
        from \<alpha>1 1 \<phi> lc show "?\<alpha> \<Turnstile> ..." by (intro impliesD[OF * ass], auto)
      qed auto
      with l2 have "corresponds_to A s2 b" by (cases s2, simp)
      with b show ?thesis by blast
    qed
  } note one_step_simulation = this
  {
    fix s1 s2 a1
    assume t: "(s1,s2) \<in> (transition P)^*" and mem: "a1 \<in> set (nodes A)" and s1a1: "corresponds_to A s1 a1"
    from t have "\<exists> a2 \<in> set (nodes A). corresponds_to A s2 a2" 
    proof (induct rule: rtrancl_induct)
      case (step s2 s3)
      from step(3) obtain a2 where a2: "a2 \<in> set (nodes A)" and s2a2: "corresponds_to A s2 a2" by blast
      from one_step_simulation[OF step(2) s2a2 a2] show ?case .
    qed (insert s1a1 mem, auto)
  }
  from this[OF steps ic]
  obtain a where a: "a \<in> set (nodes A)" "corresponds_to A (State \<alpha> l) a" by blast
  then have "\<exists> a. a \<in> set (nodes A) \<and> corresponds_to A (State \<alpha> l) a \<and> \<not> is_cover_node (edge A a)" 
  proof (cases "edge A a")
    case (Children cs)
    with a show ?thesis by auto
  next
    case (Cover b)
    from cc[unfolded cover_edges_cond_def, rule_format, OF a(1) Cover] have
      b: "b \<in> set (nodes A)" and loc: "node_location A a = node_location A b"
        and nc: "\<not> is_cover_node (edge A b)"
        and impl: "node_invariant A a \<Longrightarrow>\<^sub>f node_invariant A b" by (cases "edge A b", auto)
    from a(2) impl loc \<alpha> have "corresponds_to A (State \<alpha> l) b" by (auto simp: satisfies_Language)
    with b nc show ?thesis by auto
  qed
  then show "\<alpha> \<Turnstile> ?\<phi>" by (auto simp: get_disj_invariant_def)
qed

sublocale showsl_transition sa sa2 .

definition check_simulation_cond where
  "check_simulation_cond A P H \<equiv> do {
    check (lts.initial P \<subseteq> set (map (node_location A) (initial_nodes A)))
      (showsl_lit (STR ''not all initial nodes of LTS are represented by initial nodes in ART''));
    check_allm (\<lambda> a.
      case edge A a
      of Cover _ \<Rightarrow> succeed
      | Children children \<Rightarrow>
          let l = node_location A a in
          try (check_allm
            (\<lambda> \<tau>.
              check (\<exists> (\<tau>',b) \<in> set children. \<tau>' = \<tau> \<and> node_location A b = target \<tau> \<and> b \<in> set (art.nodes A))
            (showsl_lit (STR ''could not find matching transition in ART for node '') \<circ>
             showsl a \<circ> showsl_lit (STR '' and transition '') \<circ> showsl (source \<tau>) \<circ> showsl_lit (STR '' --> '') \<circ> showsl (target \<tau>)))
            (succ_trans_list H l))
          catch (\<lambda> e1. 
            check_valid_formula default (\<not>\<^sub>f (node_invariant A a)) 
             <+? (\<lambda> e2. e1 o showsl_lit (STR ''\<newline>and could not prove unsatisfiability of the node invariant'')))
    ) (hinter.nodes H)
  } <+? (\<lambda> s. showsl_lit (STR ''could not ensure simulation condition of ART\<newline>'') o s)"

definition check_cover_edges_cond where
  "check_cover_edges_cond A P H \<equiv> let lc = assertion P in do {
     check_allm (\<lambda> a.
       case edge A a of Children _ \<Rightarrow> succeed
       | Cover b \<Rightarrow> do {
           check (b \<in> set (art.nodes A)) (showsl_lit (STR ''target node is not listed as art-node''));
           check (node_location A a = node_location A b) (showsl_lit (STR ''node-locations differ''));
           check (\<not> is_cover_node (edge A b)) (showsl_lit (STR ''target node must not have cover edge''));
           check_valid_formula (cover_hints H a) (Disjunction [
                node_invariant A b,
                \<not>\<^sub>f node_invariant A a
           ])
       } <+? (\<lambda> s. showsl_lit (STR ''problem in checking cover edge of node '') o showsl a o showsl_nl o s)
     ) (hinter.nodes H)
   } <+? (\<lambda> s. showsl_lit (STR ''could not ensure cover edge condition of ART\<newline>'') o s)" 

definition check_initial_cond where
  "check_initial_cond A \<equiv>
    check_allm (\<lambda> init. 
     do { check (init \<in> set (art.nodes A))
            (showsl_lit (STR ''initial node of A ('') o showsl init o showsl_lit (STR '') is not mentioned as node of ART'')
            );
          check (node_invariant A init = True\<^sub>f)
           (showsl_lit (STR ''the node invariant for the initial ART node ('') o showsl init o 
               showsl_lit (STR '') must be TRUE,  but it is '') o showsl_formula (node_invariant A init))}) 
    (initial_nodes A)
  "

definition check_children_edges_cond where
  "check_children_edges_cond A P H \<equiv> let lc = assertion P in do {
     check_allm (\<lambda> a.
       case edge A a of Cover _ \<Rightarrow> succeed
       | Children children \<Rightarrow> (
         case transition_hints H a of None \<Rightarrow>
           error (showsl_lit (STR ''not yet''))
         | Some hints \<Rightarrow> do {
           check (length hints = length children)
             (showsl_lit (STR ''the number of hints differs from the number of children''));
           check_allm (\<lambda> ((\<tau>,b),h).
             case \<tau> of Transition l r \<phi> \<Rightarrow>
               tc2.check_valid_formula h (Disjunction [
                  rename_vars Post (node_invariant A b),
                   \<not>\<^sub>f rename_vars Pre (node_invariant A a),
                   \<not>\<^sub>f rename_vars Pre (lc l),
                   \<not>\<^sub>f \<phi>
 \<comment> \<open>deactivated \<not> rename_vars Post (lc r) \<close>
                ])
                  <+? (\<lambda> s. showsl_lit (STR ''problem in checking edge '') o showsl a o showsl_lit (STR '' --> '') o showsl b o 
                  showsl_lit (STR '' for transition\<newline>'') o 
                  showsl_transition \<tau> o showsl_nl o s)
           ) (zip children hints)
         } <+? (\<lambda> s. showsl_lit (STR ''problem in checking transitions of node '') o showsl a o showsl_nl o s)
        )
     ) (hinter.nodes H)
   } <+? (\<lambda> s. showsl_lit (STR ''could not ensure transition edge condition of ART\<newline>'') o s)" 

definition check_art_invariants where
  "check_art_invariants A P H\<equiv> do {
      check_art A;
      check_initial_cond A;
      check_simulation_cond A P H;
      check_cover_edges_cond A P H;
      check_children_edges_cond A P H
   } <+? (\<lambda> s. showsl_lit (STR ''could not ensure validity of art-graph:\<newline>'') o s)"

end

locale art_checker =
  pre_art_checker where type_fixer = type_fixer +
  lts_checker
    where type_fixer = type_fixer
      and logic_checker = tc
      and showsl_atom = sa
      and normalize_lit = ne 
      and normalized_lit = ned 
  + tc2: logic_checker
    where type_fixer = "TYPE('f\<times>'v trans_var\<times>'t\<times>'d\<times>'s)"
      and logic_checker = tc2
      and showsl_atom = sa2
      and normalize_lit = ne2 
      and normalized_lit = ned2 
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 's::{default,showl}) itself"

locale art_checker_body =
  art_checker where type_fixer = "TYPE('f\<times>'v\<times>'t\<times>'d\<times>'s)"
  for type_fixer :: "('f::showl \<times> 'v::showl \<times> 't::showl \<times> 'd \<times> 'l::showl \<times> 'n::showl \<times> 's::{default,showl}) itself"
  and A :: "('f,'v,'t,'l,'n) art"
  and P :: "('f,'v,'t,'l) lts"
  and H :: "('s,'l,'n,_) hinter" +
  assumes ans: "set (hinter.nodes H) = set (art.nodes A)"
      and P: "lts P"
      and succ_trans_list: "\<And> l. set (succ_trans_list H l) = { \<tau> \<in> transition_rules P. source \<tau> = l }"
begin

lemma check_initial_cond[iff]: "isOK(check_initial_cond A) = initial_cond A"
  unfolding initial_cond_def check_initial_cond_def by auto

lemma check_cover_edges_cond[dest]:
  assumes ok: "isOK(check_cover_edges_cond A P H)" and A: "art A"
    shows "cover_edges_cond A"
  unfolding cover_edges_cond_def
proof (intro allI impI conjI)
  note * = ok[unfolded check_cover_edges_cond_def,simplified, unfolded ans]
  note [split] = art_edge.splits option.splits
  fix a b assume a: "a \<in> set (nodes A)" and ab: "edge A a = Cover b"
  from * a ab
  show "node_location A a = node_location A b"
   and b: "b \<in> set (nodes A)"
   and "\<not> is_cover_node (edge A b)" by auto
  from *[rule_format,OF a, unfolded ab,simplified]
  obtain hints where "isOK (check_valid_formula hints (Disjunction [node_invariant A b, \<not>\<^sub>f node_invariant A a ]))" by auto
  from check_valid_formula[OF this] artD[OF A] a b
  show "node_invariant A a \<Longrightarrow>\<^sub>f node_invariant A b" by (auto simp: valid_Language)
qed

lemma check_simulation_cond[dest]: assumes "isOK(check_simulation_cond A P H)" and A: "art A"
  shows "simulation_cond A P"
proof -
  note ok = assms(1)[unfolded check_simulation_cond_def, simplified, unfolded Let_def ans]
  show ?thesis
    unfolding simulation_cond_def
  proof (intro conjI allI impI)
    fix a tas \<tau>
    assume a: "a \<in> set (art.nodes A)"
    assume *: "edge A a = Children tas" "\<tau> \<in> transition_rules P" "source \<tau> = node_location A a" "satisfiable (node_invariant A a)" 
    note [simp] = is_ok_try_catch
    {
      from *(4) obtain \<alpha> where sat: "assignment \<alpha>" "\<alpha> \<Turnstile> node_invariant A a" unfolding satisfiable_def by auto
      from A[unfolded art_def] a have form: "formula (\<not>\<^sub>f node_invariant A a)" by auto
      assume "isOK (check_valid_formula default (\<not>\<^sub>f node_invariant A a))" 
      from check_valid_formula[OF this form] sat(1) sat(2) Language_not[of "node_invariant A a"]
      have False unfolding Language_def by auto
    }
    with conjunct2[OF ok, rule_format, OF a, unfolded *(1), simplified] *
    show "(\<exists>b \<in> set (art.nodes A). (\<tau>, b) \<in> set tas \<and> node_location A b = target \<tau>)" by (auto simp: succ_trans_list)
  qed (insert ok, auto)
qed

lemma check_children_edges_cond[dest]:
  assumes ok: "isOK(check_children_edges_cond A P H)" and A: "art A"
  shows "children_edges_cond A P"
  unfolding children_edges_cond_def
proof (intro allI impI)
  fix a children \<tau> b
  assume a: "a \<in> set (art.nodes A)"
    and edge: "edge A a = Children children"
    and \<tau>: "\<tau> \<in> transition_rules P"
    and b: "b \<in> set (art.nodes A)"
    and mem: "(\<tau>, b) \<in> set children"
  note ok = ok[unfolded check_children_edges_cond_def, simplified, unfolded ans, rule_format, OF a, 
    unfolded edge, simplified]
  from ok obtain hints where tr: "transition_hints H a = Some hints" and len: "length hints = length children"
    by (auto split: option.splits)
  from mem len obtain h where mem: "((\<tau>,b),h) \<in> set (zip children hints)" unfolding set_zip
    by (auto simp: set_conv_nth)
  note ok = ok[unfolded tr, simplified, THEN conjunct2, rule_format, OF mem]
  show "transition_entailment (assertion P) (node_invariant A a) \<tau> (node_invariant A b)"
  proof(cases \<tau>)
    case *: (Transition l r \<phi>)
    with A a b P \<tau> have "formula (node_invariant A b) \<and>
  formula (node_invariant A a) \<and> formula (assertion P l) \<and> formula \<phi>" by auto
    from tc2.check_valid_formula[OF ok[unfolded *, simplified],simplified, OF this]
    show ?thesis
      by (auto simp: * valid_Language)
  qed
qed

lemma check_art_invariants[dest]:
  assumes ok: "isOK(check_art_invariants A P H)" shows "well_formed A P"
proof-
  from ok have A: "art A" by (auto simp: check_art_invariants_def)
  with ok show ?thesis by (auto simp: well_formed_def check_art_invariants_def)
qed

end

datatype ('n,'tr,'s) art_edge_impl =
  Cover_Edge 'n 's
| Children_Edge "('tr \<times> 'n \<times> 's) list"

datatype ('f,'v,'t,'l,'n,'tr,'s) art_node_impl = Art_Node
  (name: 'n) (invariant: "('f,'v,'t) exp formula") (location: 'l) (edge: "('n,'tr,'s) art_edge_impl")

fun is_cover_node :: "('f,'v,'t,'l,'n,'tr,'s) art_node_impl \<Rightarrow> bool" where
  "is_cover_node (Art_Node _ _ _ (Cover_Edge _ _)) = True"
| "is_cover_node (Art_Node _ _ _ (Children_Edge _)) = False"

record ('f,'v,'t,'l,'n,'tr,'s) art_impl =
  initial_nodes :: "'n list" 
  nodes :: "('f,'v,'t,'l,'n,'tr,'s) art_node_impl list"
  
fun showsl_art_node :: "('f,'v,'t,'l :: showl,'n :: showl,'tr :: showl,'s) art_node_impl \<Rightarrow> showsl" where
  "showsl_art_node (Art_Node n _ l (Cover_Edge m _)) = showsl n o showsl_lit (STR ''(@ '') o showsl l o showsl_lit (STR ''): covered by '') o showsl m" 
| "showsl_art_node (Art_Node n _ l (Children_Edge ls)) = showsl n o showsl_lit (STR ''(@ '') o showsl l o showsl_lit (STR ''): goes to '') 
    o default_showsl_list (\<lambda> (tr,n,_). showsl_lit (STR ''-'') o showsl tr o showsl_lit (STR ''->'') o showsl n) ls" 
  
definition showsl_art :: "('f,'v,'t,'l :: showl,'n :: showl,'tr :: showl,'s) art_impl \<Rightarrow> showsl" where
  "showsl_art A = showsl_lit (STR ''ART:\<newline>Initial node: '') o showsl_list (initial_nodes A) o showsl_lit (STR ''\<newline>Arcs\<newline>'') 
     o showsl_sep showsl_art_node showsl_nl (nodes A) o showsl_nl" 
  

hide_const (open) nodes

definition art_nodes :: "('f,'v,'t,'l,'n,'tr,'s) art_impl \<Rightarrow> 'n list" where
  "art_nodes Ai = map name (art_impl.nodes Ai)"

context
  fixes Pi :: "('f,'v,'t,'l,'tr) lts_impl"
begin
fun art_edge_of :: "('n,'tr,'s) art_edge_impl \<Rightarrow> ('f,'v,'t,'l,'n) art_edge" where
  "art_edge_of (Cover_Edge an _) = Cover an"
| "art_edge_of (Children_Edge ans) = Children (map (\<lambda> (t,a,h). (transition_of Pi t, a)) ans)"

definition art_of :: "('f,'v,'t,'l,'n,'tr,'s) art_impl \<Rightarrow> ('f,'v,'t,'l,'n) art" where
  "art_of Ai \<equiv>
    let ans = art_impl.nodes Ai in \<lparr>
      art.initial_nodes = art_impl.initial_nodes Ai,
      art.nodes = art_nodes Ai,
      art.edge = (the o map_of (map (\<lambda> a. (name a, art_edge_of (edge a))) ans)),
      node_location = (the o map_of (map (\<lambda> a. (name a, location a)) ans)),
      node_invariant = (the o map_of (map (\<lambda> a. (name a, invariant a)) ans))
    \<rparr>"
  
lemma art_of_code[code]: "art_of Ai = (
    let ans = art_impl.nodes Ai in \<lparr>
      art.initial_nodes = art_impl.initial_nodes Ai,
      art.nodes = art_nodes Ai,
      art.edge = (map_of_total (\<lambda> a. showsl_lit (STR ''error in looking up art edge '') o showsl a) (map (\<lambda> a. (name a, art_edge_of (edge a))) ans)),
      node_location = (map_of_total (\<lambda> a. showsl_lit (STR ''error in looking up node location '') o showsl a) (map (\<lambda> a. (name a, location a)) ans)),
      node_invariant = (map_of_total (\<lambda> a. showsl_lit (STR ''error in looking up node invariant '') o showsl a) (map (\<lambda> a. (name a, invariant a)) ans))
    \<rparr>)"
  unfolding art_of_def Let_def by simp


lemma node_invariant_art_of[simp] :
  "node_invariant (art_of Ai) = the o map_of (map (\<lambda> a. (art_node_impl.name a, art_node_impl.invariant a)) (art_impl.nodes Ai))"
  by (simp add: art_of_def Let_def)

lemma nodes_art_of[simp]: "art.nodes (art_of Ai) = art_nodes Ai" by (simp add: art_of_def Let_def)

lemma node_location_art_of[simp]:
  "node_location (art_of Ai) = the o map_of (map (\<lambda> a. (name a, location a)) (art_impl.nodes Ai))"
  by (simp add: art_of_def Let_def)

definition cover_hints :: "('f,'v,'t,'l,'n,'tr,'s::default) art_impl \<Rightarrow> 'n \<Rightarrow> 's" where
  "cover_hints Ai =
    map_of_default default (map (\<lambda> a. (name a, case edge a of Cover_Edge _ h \<Rightarrow> h))
      (filter is_cover_node (art_impl.nodes Ai)))"

definition transition_hints :: "('f,'v,'t,'l,'n,'tr,'s) art_impl \<Rightarrow> 'n \<Rightarrow> 's list option" where
  "transition_hints Ai =
    map_of (map (\<lambda> a. (name a, case edge a of Children_Edge cs \<Rightarrow> map (\<lambda> (_,_,h). h) cs))
      (filter (\<lambda> a. \<not> is_cover_node a) (art_impl.nodes Ai)))"

end

context pre_art_checker begin

definition "make_hinter Pi Ai \<equiv> \<lparr>
  hinter.nodes = art_nodes Ai,
  succ_trans_list = succ_transitions Pi,
  cover_hints = cover_hints Ai,
  transition_hints = transition_hints Ai
\<rparr>"

definition check_art_invariants_impl where
  "check_art_invariants_impl Ai Pi \<equiv> check_art_invariants (art_of Pi Ai) (lts_of Pi) (make_hinter Pi Ai)"

definition unique_names where
"unique_names Ai \<equiv> distinct (map name (art_impl.nodes Ai))"

definition check_unique_names where
  "check_unique_names Ai \<equiv>
    check (distinct (map name (art_impl.nodes Ai)))
          (showsl_lit (STR ''Nodes in art graph must have unique names''))"

lemma check_unique_names[simp]: "isOK(check_unique_names Ai) = unique_names Ai"
  unfolding check_unique_names_def unique_names_def by auto

abbreviation post :: "('f,'v,'t) exp formula \<Rightarrow> ('f,'v trans_var,'t) exp formula" where
  "post f \<equiv> rename_vars Post f"


fun translate_f
where
  "translate_f is_cover f 0 = f 0" |
  "translate_f is_cover f (Suc n)
    = (if is_cover (f 1) then translate_f is_cover (shift f 2) n else translate_f is_cover (shift f 1) n)"

lemma translate_f_skips:
  assumes "\<And> n. is_cover (f n) \<Longrightarrow> \<not> is_cover (f (Suc n))"
  and "\<not> is_cover (f 0)"
  shows "\<not> is_cover (translate_f is_cover f n)"
using assms by (induct n arbitrary: f;cases "is_cover (f 1)";auto)

definition get_node where
  "get_node Ai = the o map_of (map (\<lambda> a. (name a, a)) (art_impl.nodes Ai))"

abbreviation node_exists where
  "node_exists Ai x \<equiv> x \<in> art_node_impl.name ` set (art_impl.nodes Ai)"

definition is_cover_state where
  "is_cover_state Ai = is_cover_node \<circ> get_node Ai o state.location"

lemma unique_names_eq:
  assumes "unique_names Ai"
          "name node = name a"
          "node \<in> set (art_impl.nodes Ai)"
          "a \<in> set (art_impl.nodes Ai)"
  shows "node = a"
using distinct_map_eq[OF assms(1)[unfolded unique_names_def] assms(2-4)].

abbreviation satisfies_invariant where
  "satisfies_invariant Ai s \<equiv>
  assignment (state.valuation s) \<and>
  node_exists Ai (state.location s) \<and>
  state.valuation s \<Turnstile> art_node_impl.invariant (get_node Ai (state.location s))"

lemma map_of_helper: (* Makes a great SIMP rule, but really slows down simp/force *)
  assumes "map_of (map (\<lambda>a. (f1 a, a)) lst) l = Some v"
  shows "map_of (map (\<lambda>a. (f1 a, f a)) lst) l = Some (f v)"
using assms by(induct lst;auto)

lemma get_node :
  assumes "node_exists Ai l"
  shows "get_node Ai l \<in> set (art_impl.nodes Ai)" (is ?t1)
        "name (get_node Ai l) = l" (is ?t2)
        "map_of (map (\<lambda>a. (name a, a)) (art_impl.nodes Ai)) l = Some (get_node Ai l)" (is ?t3)
proof -
  from assms weak_map_of_SomeI obtain a where a:"name a = l" "a \<in> set (art_impl.nodes Ai)" by auto
  then have ins:"(name a,a) \<in> set (map (\<lambda> a. (name a, a)) (art_impl.nodes Ai))" by auto
  obtain x where x:"map_of (map (\<lambda>a. (name a, a)) (art_impl.nodes Ai)) (name a) = Some x"
           using weak_map_of_SomeI[OF ins] by auto
  then have x_is:"x = get_node Ai l" unfolding get_node_def o_def a by simp
  from map_of_SomeD[OF x,unfolded a x_is] show ?t1 ?t2 by auto
  from x[unfolded x_is a] show ?t3 by auto
qed

lemma unique_get_node:
  assumes "unique_names Ai" "a \<in> set (art_impl.nodes Ai)"
  shows "get_node Ai (name a) = a"
  using assms(2) unique_names_eq[OF assms(1) get_node(2,1)[of "name a"] assms(2)] by blast

lemma is_cover_state:
  assumes "node_exists Ai (state.location x)" "is_cover_state Ai x"
  shows "\<exists>v. map_of (map (\<lambda>a. (name a, art_edge_of Pi (art_node_impl.edge a)))
                         (art_impl.nodes Ai)) (state.location x) = Some (Cover v)
              \<and> (\<exists> h. art_node_impl.edge (get_node Ai (state.location x)) = Cover_Edge v h)
              "
proof -
  let ?gn = "get_node Ai (state.location x)"
  note x[simp]= get_node(3)[OF assms(1)]
  from assms(2)[unfolded is_cover_state_def,simplified] show ?thesis
  by (cases ?gn;cases "edge ?gn";auto simp:map_of_helper)
qed
  
lemma no_cover_state:
  assumes "node_exists Ai (state.location x)" "\<not> is_cover_state Ai x"
  shows "\<exists>v. map_of (map (\<lambda>a. (name a, art_edge_of Pi (art_node_impl.edge a)))
                                       (art_impl.nodes Ai)) (state.location x) = Some (Children v)"
proof -
  have [simp]:"map_of (map (\<lambda>a. (name a, a)) (art_impl.nodes Ai)) (state.location x) =
        Some (get_node Ai (state.location x))"
    using get_node(3)[OF assms(1)].
  from assms(2)[unfolded is_cover_state_def,simplified] show ?thesis
  by (cases "(get_node Ai (state.location x))";cases "edge (get_node Ai (state.location x))"
     ;auto simp:map_of_helper)
qed

definition lts_transitions_of_art
 :: "('f, 'v, 't, 'l, 'tr) lts_impl \<Rightarrow> ('f, 'v, 't, 'l, 'n, 'tr, 'sintList) art_node_impl \<Rightarrow> ('f,'v,'t,'n,'tr option) transitions_impl"
where
  "lts_transitions_of_art Pi a = (case edge a of
        (Cover_Edge v _) \<Rightarrow> [(None, Transition (name a) v True\<^sub>f)] | \<comment> \<open> TODO: the formula True should be a skip \<close>
        (Children_Edge cs) \<Rightarrow> map (\<lambda> (nm,an,_). case transition_of Pi nm of
          Transition _ _ _ \<Rightarrow> (Some nm,Transition (name a) an (transition_formula (transition_of Pi nm)))) cs)"

fun renumber_rename :: "int \<Rightarrow> ('b option \<times> 'c) list \<Rightarrow> (('b + int) \<times> 'c) list" 
where
"renumber_rename i (Cons (a,v) rs)
  = Cons (case a of None \<Rightarrow> Inr i | Some l \<Rightarrow> Inl l,v) (renumber_rename (i+1) rs)" |
"renumber_rename i Nil = Nil"

lemma snd_rename [simp]:
  shows "map snd (renumber_rename n xs) = map snd xs"
by(induct xs arbitrary:n,auto)

lemma snd_set_rename [simp]:
  shows "snd ` set (renumber_rename n xs) = snd ` set xs"
using set_map[of snd xs, folded snd_rename[of n], unfolded set_map].

(* RT: did not update this part when adding assertion to LTS 
lemma lts_termination_renumber_rename:
  shows "lts_termination (lts_of (Lts_Impl i (renumber_rename n xs))) = lts_termination (lts_of (Lts_Impl i xs))"
by auto *)

fun relabel_transition where
  "relabel_transition f (Transition l r \<phi>) = Transition (f l) (f r) \<phi>"

(* RT: did not update this part when adding assertion to LTS  
definition lts_impl_of_art ::
  "('f,'v,'t,'l,'tr) lts_impl \<Rightarrow> ('f,'v,'t,'l,'n,'tr,'sintList) art_impl
  \<Rightarrow> ('f,'v,'t,'n,'tr + int) lts_impl"
 (* TODO: change resulting datatype s.t. transfer-labels are unique again:
          use "(art_node \<times> 'tr) + int" for instance, or part of the hintList? *)
where
  "lts_impl_of_art Pi Ai
    = (Lts_Impl (initial_nodes Ai) (renumber_rename 0
                                  (concat (map (lts_transitions_of_art Pi) (art_impl.nodes Ai)))))"
*)
end

context art_checker begin

lemma check_art_invariants_impl:
  assumes impl: "lts_impl Pi"
      and ok: "isOK (check_art_invariants_impl Ai Pi)"
    shows "invariant (lts_of Pi) l (get_disj_invariant (art_of Pi Ai) l)"
proof-
  note impl = lts_impl[OF impl]
  interpret body: art_checker_body
  where type_fixer = "TYPE(_)"
    and P = "lts_of Pi"
    and A = "art_of Pi Ai"
    and H = "make_hinter Pi Ai"
    using impl by (unfold_locales, auto simp: make_hinter_def)
  from ok
  have wf: "well_formed (art_of Pi Ai) (lts_of Pi)" by (intro body.check_art_invariants, unfold check_art_invariants_impl_def)
  from well_formed_imp_disj_invariant[OF this impl]
  show ?thesis.
qed
  
end

(* RT: did not update this part when adding assertion to LTS
context art_checker begin
lemma path_simulation:
  assumes step:"(x,y) \<in> transition (lts_of Pi)"
     and  sim:"pre_art_body.simulation_cond (lts_of Pi) (art_of Pi Ai)"
              "pre_art_body.children_edges_cond \<Lambda> (lts_of Pi) (art_of Pi Ai)"
     and  cov:"pre_art_body.cover_edges_cond \<Lambda> (art_of Pi Ai)"
     and  art:"pre_art_body.art \<Lambda> (art_of Pi Ai)"
     and  lts:"lts (lts_of Pi)"
     and  x_is_x:"relabel_state (location \<circ> get_node Ai) x' = x"
     and  sat:"satisfies_invariant Ai x'"
  shows "\<exists> y'. (x',y') \<in> (transition (lts_of (lts_impl_of_art Pi Ai)))^+
             \<and> (relabel_state (location \<circ> get_node Ai) y' = y
             \<and> satisfies_invariant Ai y')" (is "\<exists> y'. ?trancl x' y' \<and> ?x_is_x y' y \<and> ?sat y'")
proof-
  let ?x' = "(get_node Ai (state.location x'))"
  let ?A = "art_of Pi Ai"
  let ?path = "path (transition (lts_of (lts_impl_of_art Pi Ai)))"
  have x_in_Ai:"node_exists Ai (state.location x')" using sat by auto
  have xinnodes:"state.location x' \<in> nodes ?A"
    unfolding art_of_def art_nodes_def Let_def using x_in_Ai by auto
  obtain \<tau> where \<tau>:"\<tau> \<in> transition_rules (lts_of Pi)" and xy: "(x,y) \<in> transition_step \<tau>"
    using step unfolding transition_def by auto
  (* WLOG, we can assume that x is not a cover node *)
  have "\<exists> x1 i1. ?path x' i1 x1 \<and> ?x_is_x x1 x \<and> ?sat x1 \<and> \<not> is_cover_state Ai x1"
  proof(cases "is_cover_state Ai x'")
    case True
    obtain v h where v:"art.edge (art_of Pi Ai) (state.location x') = Cover v"
               "art_node_impl.edge (get_node Ai (state.location x')) = Cover_Edge v h"
        using is_cover_state[OF x_in_Ai True,of Pi] unfolding art_of_def Let_def o_def by auto
    let ?x1 = "State (state.valuation x') v"
    have res:"v \<in> nodes (art_of Pi Ai)"
         "node_location (art_of Pi Ai) (state.location x') = node_location (art_of Pi Ai) v"
         "\<not> art_edge.is_cover_node (art.edge (art_of Pi Ai) v)"
         "node_invariant (art_of Pi Ai) (state.location x') \<Longrightarrow>\<^sub>f node_invariant (art_of Pi Ai) v"
         using cov[unfolded pre_art_body.cover_edges_cond_def,rule_format,OF xinnodes v(1)] by auto
    hence v_loc:"v \<in> name ` set (art_impl.nodes Ai)" unfolding art_of_def Let_def art_nodes_def by auto
    {fix a
      have "art_edge.is_cover_node (art_edge_of Pi (art_node_impl.edge a)) = is_cover_node a"
      by(cases "art_node_impl.edge a";cases a;auto)
    } note [simp] = this
    have nc:"\<not> is_cover_state Ai ?x1"
      using map_of_helper[OF get_node(3)[OF v_loc],of "art_edge_of Pi \<circ> art_node_impl.edge"]
      res(3) unfolding is_cover_state_def art_of_def Let_def by auto
    have newl:"?x_is_x ?x1 x"
      using x_is_x res(2) get_node(3)[OF v_loc] get_node(3)[OF x_in_Ai]
      by (auto simp:map_of_helper art_of_def Let_def)
    have frml:"formula (node_invariant (art_of Pi Ai) (state.location x'))"
              "formula (node_invariant (art_of Pi Ai) v)"
      using art[unfolded pre_art_body.art_def,rule_format,OF xinnodes]
            art[unfolded pre_art_body.art_def,rule_format,OF res(1)] by auto
    have assg:"assignment (state.valuation x')"
              "valuation x' \<Turnstile> node_invariant (art_of Pi Ai) (state.location x')"
      using sat get_node[OF v_loc] get_node[OF x_in_Ai] by (auto simp:map_of_helper)
    have newsat:"satisfies_invariant Ai ?x1"
    using impliesD[OF res(4) assg] get_node[OF v_loc] assg(1) v_loc
      by (auto simp:map_of_helper)
    have path:"path (transition (lts_of (lts_impl_of_art Pi Ai))) x' [x'] ?x1"
    proof(rule path_prepend[OF _ path0], rule mem_transitionI)
      let ?x = "get_node Ai (state.location x')"
      have "(None, Skip (state.location x') v) \<in> set (lts_transitions_of_art Pi ?x)"
        using v(2) get_node(2)[OF x_in_Ai] by (auto simp: lts_transitions_of_art_def)
      from this get_node(1)[OF x_in_Ai]
      show "Skip (state.location x') v \<in> transition_rules (lts_of (lts_impl_of_art Pi Ai))"
        by (auto simp: lts_impl_of_art_def)
      show "(x', State (valuation x') v) \<in> transition_step (Skip (state.location x') v)"
        by (auto simp: assg)
     qed
    from nc newl newsat path show ?thesis by auto
  next
    case False 
    have "?path x' [] x'" by auto thus ?thesis using False x_is_x sat by blast
  qed
  then obtain x1 i1 where x1: "?path x' i1 x1" "?x_is_x x1 x" "?sat x1" "\<not> is_cover_state Ai x1"
       "state.location x1 \<in> nodes (art_of Pi Ai)"
    by (auto simp:art_nodes_def)
  have x1_in_Ai:"node_exists Ai (state.location x1)" using x1 by auto
      
  obtain v where v:"art.edge (art_of Pi Ai) (state.location x1) = Children v"
        using no_cover_state[OF x1_in_Ai x1(4),of Pi]
        unfolding art_of_def Let_def by auto
  then obtain lst where lst:
        "art_node_impl.edge (get_node Ai (state.location x1)) = Children_Edge lst"
        "v = map (\<lambda>(t, a, h). (transition_of Pi t, a)) lst"
        unfolding art_of_def Let_def o_def
        by (cases "art_node_impl.edge (get_node Ai (state.location x1))"
           ;auto simp:map_of_helper get_node(3)[OF x1_in_Ai])
  have "source \<tau> = node_location (art_of Pi Ai) (state.location x1)"
    using xy x1(2)
    by(auto simp:map_of_helper get_node(3)[OF x1_in_Ai] art_of_def Let_def)
  hence "(\<exists>b\<in>nodes (art_of Pi Ai). (\<tau>, b) \<in> set v \<and> node_location (art_of Pi Ai) b = target \<tau>)"
    using sim(1)[unfolded pre_art_body.simulation_cond_def] x1 v \<tau>
    by simp
  then obtain b where b:"b\<in>nodes (art_of Pi Ai)" "(\<tau>, b) \<in> set v"
                      "node_location (art_of Pi Ai) b = target \<tau>" by auto
  hence node_exists:"node_exists Ai b" unfolding art_of_def Let_def art_nodes_def by auto
  obtain t h where x:"\<tau> = (transition_of Pi t)" 
                     "(t, b, h) \<in> set lst"
    using b(2)[unfolded lst] by auto
  let ?y = "State (state.valuation y) b"
  let ?x2 = "get_node Ai (state.location x1)"
  have t:"transition_entailment (node_invariant (art_of Pi Ai) (state.location x1)) \<tau> 
                              (node_invariant (art_of Pi Ai) b)"
    using x1 v b \<tau>
    by(intro sim(2)[unfolded pre_art_body.children_edges_cond_def, rule_format], auto)
  show ?thesis
  proof(cases \<tau>)
    case (Transition l r \<phi>)
    from Transition xy lts[unfolded lts_def] have \<tau>_formula: "formula \<phi>" by auto
    from \<tau> xy Transition obtain \<gamma> where \<gamma>:
      "state x" "state y" "assignment \<gamma>" "source \<tau> = state.location x" "target \<tau> = state.location y"
      "\<delta> (valuation x) (valuation y) \<gamma> \<Turnstile> transition_formula \<tau>" by auto
    then have y:"node_location (art_of Pi Ai) b = state.location y" using b by auto
    have ea:"\<exists>\<gamma>. assignment \<gamma> \<and> \<delta> (valuation x1) (valuation y) \<gamma> \<Turnstile> transition_formula \<tau>"
      using \<gamma> x1(2) by auto
    let ?d = "\<delta> (valuation x) (valuation y) \<gamma>"
    have y_is_y:"?x_is_x ?y y" using y
      by(cases y;auto simp:art_of_def Let_def
                           map_of_helper get_node(3)[OF node_exists])
    have assg_d:"assignment ?d" using \<gamma> by auto
    let ?trans = "Transition (state.location x1) b (transition_formula \<tau>)"
    have "?trans
        \<in> snd ` (\<lambda>(nm, an, _).
                 case transition_of Pi nm of
                 Transition x xa xb \<Rightarrow>
                   (Some nm, Transition (name (get_node Ai (state.location x1))) an (transition_formula (transition_of Pi nm)))
                 | Skip x xa \<Rightarrow> (Some nm, Skip (state.location x1) an)) `
             set lst"
        using x(1,2) get_node(2)[OF x1_in_Ai] Transition by force
    hence "?trans \<in> snd ` set (lts_transitions_of_art Pi (get_node Ai (state.location x1)))"
       unfolding get_node(2)[OF x1_in_Ai] lts_transitions_of_art_def lst by simp
    then obtain p where p:"p\<in>set (lts_transitions_of_art Pi (get_node Ai (state.location x1)))"
                          "snd p = ?trans" by auto
    obtain \<gamma> where g:"?x2\<in>set (art_impl.nodes Ai)"
           "p\<in>set (lts_transitions_of_art Pi ?x2)"
           "assignment \<gamma>" "source (snd p) = state.location x1" "target (snd p) = b"
           "\<delta> (valuation x1) (valuation y) \<gamma> \<Turnstile> transition_formula (snd p)"
      using ea get_node(1)[OF x1_in_Ai] p by auto
    have "(x1, State (valuation y) b) \<in> transition (lts_of (lts_impl_of_art Pi Ai))"
    proof(rule mem_transitionI)
      show "snd p \<in> transition_rules (lts_of (lts_impl_of_art Pi Ai))" using g(1,2)
        unfolding lts_impl_of_art_def by (cases ?x2;auto)
      show "(x1, State (valuation y) b) \<in> transition_step (snd p)"
        using \<gamma>(2) p(2) g(3-) x1(3) by (cases "snd p";auto)
    qed
    hence path:"?path x' (i1@Cons x1 Nil) ?y" by(rule path_conc[OF x1(1) path_prepend[OF _ path0]])
    let ?pre = "rename_vars Pre (node_invariant (art_of Pi Ai) (state.location x1))"
    let ?post = "rename_vars Post (node_invariant (art_of Pi Ai) b)"
    have "valuation x1 \<Turnstile> art_node_impl.invariant (get_node Ai (state.location x1))" using x1(3) by auto
    hence "?d \<Turnstile> ?pre" using x1(2)
      by (auto simp:map_of_helper art_of_def Let_def get_node[OF x1_in_Ai])
    from this \<gamma>(6) have sc:"?d \<Turnstile> ?pre \<and>\<^sub>f transition_formula \<tau>" by auto
    have formula_post:"formula ?post" using art[unfolded pre_art_body.art_def] b(1) by auto
    have formula_pre:"formula (?pre \<and>\<^sub>f transition_formula \<tau>)"
      using art[unfolded pre_art_body.art_def] x1 \<tau>_formula Transition by auto
    from t[simplified] sc[simplified]
      have "valuation y \<Turnstile> the (map_of (map (\<lambda>a. (name a, art_node_impl.invariant a)) (art_impl.nodes Ai)) b)"
        unfolding Transition pre_post_inter_satisfies_rename_vars_pre transition_entailment.simps transition_formula.simps
        using impliesD[OF _ assg_d] pre_post_inter_satisfies_rename_vars_post
      by smt
    hence "?d \<Turnstile> ?post"  by (auto simp:transition_of_def )
    hence sat:"valuation y \<Turnstile> art_node_impl.invariant (get_node Ai b)" using get_node[OF node_exists]
      unfolding art_of_def Let_def by(auto simp:map_of_helper)
    have "?trancl x' ?y" "?x_is_x ?y y" "?sat ?y"
      using y_is_y node_exists sat \<gamma>(2) path_is_trancl[OF path] by auto
    thus ?thesis by blast
  next
    case (Skip l r)
    from xy[unfolded this]
    have \<gamma>: "state x" "state y" "l = state.location x" "r = state.location y"
      "valuation x = valuation y" by auto
    hence vs:"valuation x1 = valuation y" using x1 by auto
    have y':"location (get_node Ai b) = r"
      using b[unfolded Skip,simplified] get_node[OF node_exists]
      by (auto simp:map_of_helper)
    let ?y = "State (valuation y) b"
    let ?trans = "Skip (state.location x1) b"
    have "?trans
        \<in> snd ` (\<lambda>(nm, an, _).
                 case transition_of Pi nm of
                 Transition x xa xb \<Rightarrow>
                   (Some nm, Transition (name (get_node Ai (state.location x1))) an (transition_formula (transition_of Pi nm)))
                 | Skip x xa \<Rightarrow> (Some nm, Skip (state.location x1) an)) `
             set lst"
        using x(1,2) get_node(2)[OF x1_in_Ai] Skip by force
    hence "?trans \<in> snd ` set (lts_transitions_of_art Pi (get_node Ai (state.location x1)))"
       unfolding get_node(2)[OF x1_in_Ai] lts_transitions_of_art_def lst by simp
    then obtain p where p:"p\<in>set (lts_transitions_of_art Pi (get_node Ai (state.location x1)))"
                          "snd p = ?trans" by auto
    have g:"?x2\<in>set (art_impl.nodes Ai)"
           "p\<in>set (lts_transitions_of_art Pi ?x2)"
           "source (snd p) = state.location x1" "target (snd p) = b"
      using \<gamma> get_node(1)[OF x1_in_Ai] p by auto
    have c1:"(x', ?y) \<in> (transition (lts_of (lts_impl_of_art Pi Ai)))\<^sup>+"
    proof (rule path_is_trancl[OF path_conc[OF x1(1) path_prepend[OF mem_transitionI path0]]])
      show "snd p \<in> transition_rules (lts_of (lts_impl_of_art Pi Ai))" using g(1,2)
        unfolding lts_impl_of_art_def by auto
      show "(x1, State (valuation y) b) \<in> transition_step (snd p)"
        using \<gamma> p(2) g x1(3) vs by (cases "snd p";auto)
    qed auto
    have c2:"relabel_state (art_node_impl.location \<circ> get_node Ai) ?y = y" using x_is_x y' \<gamma> by auto
    have "art_node_impl.invariant (get_node Ai (state.location x1)) \<Longrightarrow>\<^sub>f art_node_impl.invariant (get_node Ai b)"
      using t[unfolded Skip,simplified] get_node(3)[OF x1_in_Ai] get_node(3)[OF node_exists]
      by (auto simp:map_of_helper)
    hence "state.valuation ?y \<Turnstile> art_node_impl.invariant (get_node Ai (state.location ?y))"
      using x1 sat \<gamma>(5) by auto
    hence c3:"satisfies_invariant Ai ?y" using \<gamma> x_is_x y' node_exists by auto
    show ?thesis using c1 c2 c3 by auto
  qed
qed

abbreviation sim_rel where
"sim_rel Ai x' x \<equiv> relabel_state ((art_node_impl.location \<circ>\<circ> get_node) Ai) x' = x \<and> satisfies_invariant Ai x'"

lemma path_simulation_simp:
  assumes wf:"pre_art_body.well_formed \<Lambda> (lts_of Pi) (art_of Pi Ai)"
      and lts:"lts (lts_of Pi)"
  shows "(x,y) \<in> transition (lts_of Pi) \<and> sim_rel Ai x' x \<Longrightarrow>
         \<exists> y'. (x',y') \<in> (transition (lts_of (lts_impl_of_art Pi Ai)))^+ \<and> sim_rel Ai y' y"
proof -
  assume ass:"(x,y) \<in> transition (lts_of Pi) \<and> sim_rel Ai x' x"
    hence tr:"(x,y) \<in> transition (lts_of Pi)"
      and sr: "relabel_state ((art_node_impl.location \<circ>\<circ> get_node) Ai) x' = x"
              "satisfies_invariant Ai x'" by auto
  from wf have sim:"pre_art_body.simulation_cond (lts_of Pi) (art_of Pi Ai)" and
               chld:"pre_art_body.children_edges_cond \<Lambda> (lts_of Pi) (art_of Pi Ai)" and
               cov:"pre_art_body.cover_edges_cond \<Lambda> (art_of Pi Ai)" and
               art:"pre_art_body.art \<Lambda> (art_of Pi Ai)" and
               ini:"pre_art_body.initial_cond (art_of Pi Ai)"
          unfolding pre_art_body.well_formed_def by auto
  from path_simulation[OF tr sim chld cov art lts sr]
  show "\<exists> y'. (x',y') \<in> (transition (lts_of (lts_impl_of_art Pi Ai)))^+ \<and> sim_rel Ai y' y"
   by auto
qed

fun f_mimic where
  "f_mimic f s R x' 0 = x'" |
  "f_mimic f s R x' (Suc n) = (SOME y'. (f_mimic f s R x' n,y') \<in> s \<and> R y' (f (Suc n)))"

lemma f_mimic:
  assumes "\<And> x y x'. (x,y) \<in> r \<and> R x' x \<Longrightarrow> \<exists> y'. (x',y') \<in> s \<and> R y' y"
          "R x' (f 0)"
          "\<forall>i. (f i, f (Suc i)) \<in> r"
  shows "R (f_mimic f s R x' i) (f i) \<and> (f_mimic f s R x' i, f_mimic f s R x' (Suc i)) \<in> s"
using assms proof(induct i arbitrary: f x')
  case (Suc n f x')
    let "?c y'" = "(f_mimic f s R x' n, y') \<in> s \<and> R y' (f (Suc n))"
    let ?sy = "(SOME y'. ?c y')"
    have c1:"(f n, f (Suc n)) \<in> r" using Suc by auto
    have c2:"R (f_mimic f s R x' n) (f n)" using Suc by auto
    have "\<exists> y'. (f_mimic f s R x' n, y') \<in> s \<and> R y' (f (Suc n))" using c1 c2  Suc(2) by simp
    from someI_ex[OF this]
    have r:"R (f_mimic f s R x' (Suc n)) (f (Suc n))" by auto
    have "\<exists> y'. ?c y'" using assms(1) c1 c2 by auto
    from someI_ex[OF this] have c2:"R ?sy (f (Suc n))" by auto
    have c1:"(f (Suc n), f (Suc (Suc n))) \<in> r" using Suc by auto
    have "\<exists> y'. (?sy,y') \<in> s \<and> R y' (f (Suc (Suc n)))"
      using c1 c2 assms(1) by blast
    from someI_ex[OF this] r
    show ?case by auto
qed (auto simp:some_eq_ex[symmetric])

lemma simulation_SN_on:
  assumes "\<And> x y x'. (x,y) \<in> r \<and> R x' x \<Longrightarrow> \<exists> y'. (x',y') \<in> s \<and> R y' y"
          "\<forall> x \<in> X. \<exists> x' \<in> X'. R x' x"
          "SN_on s X'"
  shows "SN_on r X"
using assms(3) unfolding SN_on_def proof(rule contrapos_nn)
  assume "\<exists>f. f 0 \<in> X \<and> (\<forall>i. (f i, f (Suc i)) \<in> r)" then obtain f where
    f:"f 0 \<in> X" "(\<forall>i. (f i, f (Suc i)) \<in> r)" by auto
  from assms(2) f(1) obtain x' where x:"x' \<in> X'" "R x' (f 0)" by auto
  from f_mimic[of r R s x' f,OF assms(1) x(2) f(2), of "\<lambda> x y z. x"] f(1) x(1)
  have "f_mimic f s R x' 0 \<in> X' \<and> (\<forall>i. (f_mimic f s R x' i, f_mimic f s R x' (Suc i)) \<in> s)" by auto
  thus "\<exists>f. f 0 \<in> X' \<and> (\<forall>i. (f i, f (Suc i)) \<in> s)" by blast
qed

lemma stuttering_simulation_SN_on:
  assumes "\<And> x y x'. (x,y) \<in> r \<and> R x' x \<Longrightarrow> \<exists> y'. (x',y') \<in> s\<^sup>+ \<and> R y' y"
          "\<forall> x \<in> X. \<exists> x' \<in> X'. R x' x" "SN_on s X'"
  shows "SN_on r X"
by(rule simulation_SN_on[OF assms(1,2) SN_on_trancl[OF assms(3)]])

lemma state_for_state_2:
  fixes Pi::"('f, 'v, 't, 'l, 'tr) lts_impl"
  assumes wf:"pre_art_body.well_formed (T::('f,'t,'d) logic) (lts_of Pi) (art_of Pi Ai)"
   and   lts:"lts (lts_of Pi)"
   and   x:"x \<in> initial_states (lts_of Pi)"
   shows "\<exists>x'\<in>initial_states (lts_of (lts_impl_of_art Pi Ai)).
            State (valuation x') (art_node_impl.location (get_node Ai (state.location x'))) = x
            \<and> satisfies_invariant Ai x'"
proof(standard,standard)
  from wf have sim:"pre_art_body.simulation_cond (lts_of Pi) (art_of Pi Ai)" and
               ini:"pre_art_body.initial_cond (art_of Pi Ai)"
          unfolding pre_art_body.well_formed_def by auto
  from x have ass:"assignment (valuation x)" "State (valuation x) (lts_impl.initial Pi) = x"
     unfolding initial_states_def by auto
  let ?x' = "State (valuation x) (initial_nodes Ai)"
  show "?x' \<in> initial_states (lts_of (lts_impl_of_art Pi Ai))"
     unfolding lts_impl_of_art_def by(auto simp:initial_states_def ass)

  have "art.initial_nodes (art_of Pi Ai) \<in> nodes (art_of Pi Ai)"
    using ini[unfolded pre_art_body.initial_cond_def] by auto
  hence ini_ex:"node_exists Ai (art.initial_nodes (art_of Pi Ai))"
    by(auto simp:art_nodes_def art_of_def Let_def)
  have "node_location (art_of Pi Ai) (art.initial_nodes (art_of Pi Ai)) = lts.initial (lts_of Pi)"
    using sim[unfolded pre_art_body.simulation_cond_def] by auto
  hence h:"art_node_impl.location (get_node Ai (art_impl.initial_nodes Ai)) = lts_impl.initial Pi"
    using get_node(3)[OF ini_ex] by(auto simp:map_of_helper art_of_def Let_def)
  show "State (valuation ?x') (art_node_impl.location (get_node Ai (state.location ?x'))) = x"
    by(auto simp:h ass)
  have ini_ex3:"node_exists Ai (art_impl.initial_nodes Ai)"
    using ini[unfolded pre_art_body.initial_cond_def]
    by(auto simp:art_nodes_def art_of_def Let_def)
  have "node_invariant (art_of Pi Ai) (art.initial_nodes (art_of Pi Ai)) = form_True"
    using ini[unfolded pre_art_body.initial_cond_def] by auto
  hence "art_node_impl.invariant (get_node Ai (art_impl.initial_nodes Ai)) = form_True"
    by (auto simp:art_of_def Let_def map_of_helper get_node(3)[OF ini_ex3])
  thus "satisfies_invariant Ai ?x'" by(auto simp:ass ini_ex3)
qed

lemma lts_termination_of_art:
  fixes Pi::"('f, 'v, 't, 'l, 'tr) lts_impl"
  assumes wf:"pre_art_body.well_formed (\<Lambda> :: ('f,'t,'d) logic) (lts_of Pi) (art_of Pi Ai)"
   and   lts:"lts (lts_of Pi)"
   and termn:"lts_termination (lts_of (lts_impl_of_art Pi Ai))"
  shows "lts_termination (lts_of Pi)"
by (rule stuttering_simulation_SN_on[OF path_simulation_simp[OF wf lts] _ termn]
   ;insert state_for_state_2[OF wf lts]; auto)
end
*)

lemmas [code] =
  pre_art_checker.check_art_invariants_impl_def
  pre_art_checker.check_art_invariants_def
  pre_art_checker.check_children_edges_cond_def
  pre_art_checker.check_cover_edges_cond_def
  pre_art_checker.check_simulation_cond_def
  pre_art_checker.check_initial_cond_def
  pre_art_checker.make_hinter_def
  pre_art_checker.check_art_def
  pre_art_checker.art_def
  pre_art_checker.check_unique_names_def

end
