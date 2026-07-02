(*
Author:  Akihisa Yamada and René Thiemann
*)
theory CPF_Input_Parser
  imports
    Ceta_Problem_Spec
    XML.Xmlt
    LTS.LTS_Parser
begin
hide_const (open) UnivPoly.deg
hide_const (open) Congruence.partition


definition plain_var :: "string xmlt" where "plain_var = xml_text (STR ''var'')"
definition var :: "('a, string) term xmlt"
where "var = xml_change plain_var (xml_return \<circ> Var)"

type_synonym index = string
type_synonym 'a termIndexMap = "(index,('a,string)term)mapping" 
type_synonym 'a ruleIndexMap = "(index,('a,string)rule)mapping" 

context fixes xml2name :: "'a :: showl xmlt"
  and termMap :: "'a termIndexMap" 
  and ruleMap :: "'a ruleIndexMap" 
begin

partial_function (sum_bot)
  "term" :: "('a, string) term xmlt"
where
 [code]: "term x = (
    XMLdo (STR ''funapp'') {
      name \<leftarrow> xml2name;
      args \<leftarrow>* term;
      xml_return (Fun name args)
    } XMLor var
    XMLor xml_change (xml_text (STR ''termIndex'')) (\<lambda> idx. case Mapping.lookup termMap idx of
    None \<Rightarrow> xml_error (STR ''term index '' + String.implode idx + STR '' is unknown in term-index map'') 
  | Some term \<Rightarrow> xml_return term)      
  ) x"

definition conditions :: "ltag \<Rightarrow> ('a, string) rule list xmlt" where
  "conditions tag = XMLdo tag {
    ret \<leftarrow>* XMLdo (STR ''condition'') {
      l \<leftarrow> term;
      r \<leftarrow> term;
      xml_return (l,r)
    };
    xml_return ret
  }"

definition crule :: "ltag \<Rightarrow> ('a, string) crule xmlt" where
  "crule tag = XMLdo tag {
    l \<leftarrow> term;
    r \<leftarrow> term;
    conds \<leftarrow>[[]] conditions (STR ''conditions'');
    xml_return ((l,r),conds)
  }"

definition full_rule where "full_rule =  
  xml_change (crule (STR ''rule'')) (\<lambda>(lr,conds).
    if conds = [] then xml_return lr else xml_error (STR ''conditional rule is not allowed here'')
  )"

definition rule where "rule =
  xml_change (xml_text (STR ''ruleIndex'')) (\<lambda> idx. case Mapping.lookup ruleMap idx of
    None \<Rightarrow> xml_error (STR ''rule index '' + String.implode idx + STR '' is unknown in rule map'') 
  | Some rule \<Rightarrow> xml_return rule) XMLor full_rule"

definition rules where "rules = XMLdo (STR ''rules'') {
  ret \<leftarrow>* rule;
  xml_return ret
}"

primrec strategy_to_fp :: "('f,string)fp_strategy \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)forb_pattern list" where
  "strategy_to_fp (Forbidden_Patterns p) r = p"
| "strategy_to_fp Outermost r = o_to_fp_impl (map fst r)"
| "strategy_to_fp (Context_Sensitive \<mu>) r = mu_to_fp_impl \<mu>"

definition ctrs :: "('a,string) crules xmlt" where
  "ctrs = XMLdo (STR ''ctrs'') {
      _ \<leftarrow> XMLdo (STR ''conditionType'') {
         _ \<leftarrow> XMLdo (STR ''oriented'') {
           xml_return ()
         };
         xml_return ()
      };
      a \<leftarrow> XMLdo (STR ''rules'') { ret \<leftarrow>* crule (STR ''rule''); xml_return ret };
      xml_return a
    }"

definition ctrs_input :: "('a,string)input xmlt" 
where
  "ctrs_input = XMLdo (STR ''ctrsInput'') {
    a \<leftarrow> ctrs;
    xml_return (CTRS_input a)
}"

definition infeasibility_input :: "('a,string)input xmlt" 
where
  "infeasibility_input = XMLdo (STR ''infeasibilityInput'') {
    c \<leftarrow> ctrs;
    r \<leftarrow> XMLdo (STR ''infeasibilityQuery'') { ret \<leftarrow>* rule; xml_return ret };
    xml_return (Infeasibility_input c r)
}"

definition equations_input :: "('a,string)input xmlt" 
where
  "equations_input = XMLdo (STR ''equations'') {ret \<leftarrow> rules; xml_return (EQ_input ret)}"

definition precedence_weight :: "(nat \<Rightarrow> 'a prec_weight_repr) xmlt" where
  "precedence_weight = XMLdo (STR ''precedenceWeight'') {
    ret \<leftarrow>* XMLdo (STR ''precedenceWeightEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_nat (STR ''precedence'');
      w \<leftarrow> xml_nat (STR ''weight'');
      e \<leftarrow>? XMLdo (STR ''subtermCoefficientEntries'') {
        ret \<leftarrow>* xml_nat (STR ''entry'');
        xml_return ret
      };
      xml_return ((f,a), (p,w,e))
    };
    xml_return (Pair ret)
  }"

definition "kbo_input = XMLdo (STR ''knuthBendixOrder'') {
    w0 \<leftarrow> xml_nat (STR ''w0'');
    prw \<leftarrow> precedence_weight;
    xml_return (KBO_Input (prw w0))
  }"

definition equations_and_ro_input :: "('a,string)input xmlt" 
where
  "equations_and_ro_input = XMLdo (STR ''equationsAndRedorderInput'') {
    es0 \<leftarrow> XMLdo (STR ''equations'') {ret \<leftarrow> rules; xml_return ret};
    ro \<leftarrow> kbo_input;
    xml_return (EQ_RO_input es0 ro)
  }"

definition equational_reasoning_input :: "('a,string)input xmlt"
where
  "equational_reasoning_input = XMLdo (STR ''equationalReasoningInput'') {
    eqs \<leftarrow> XMLdo (STR ''equations'') {ret \<leftarrow> rules; xml_return ret};
    goal \<leftarrow> XMLdo (STR ''equation'') {
      a \<leftarrow> term;
      b \<leftarrow> term;
      xml_return (a,b)
    };
    xml_return (EQ_reasoning_input eqs goal)
  }"

definition complexity_class :: "complexity_class xmlt"
where
  "complexity_class = xml_change (xml_nat (STR ''polynomial'')) (xml_return \<circ> Comp_Poly)"

definition symbols :: "ltag \<Rightarrow> ('a \<times> nat) list xmlt"
where
  "symbols tagname =
    XMLdo tagname {ret \<leftarrow>* XMLdo (STR ''symbol'') {a \<leftarrow> xml2name; b \<leftarrow> xml_nat (STR ''arity''); xml_return (a,b)}; xml_return ret}"

definition symbols_wo_arity :: "ltag \<Rightarrow> 'a list xmlt"
where
  "symbols_wo_arity tagname =
    XMLdo tagname {ret \<leftarrow>* xml2name; xml_return ret}"

definition "CPFsignature = symbols (STR ''signature'')"

definition complexity_measure :: "('a,string)complexityMeasure xmlt"
  where "complexity_measure =
   XMLdo (STR ''derivationalComplexity'') {a \<leftarrow>? CPFsignature; xml_return (Derivational a)}
   XMLor XMLdo (STR ''runtimeComplexity'') {a \<leftarrow>? CPFsignature; b \<leftarrow>? CPFsignature; 
     case (a,b) of (Some c, Some d) \<Rightarrow> xml_return (Runtime (Some (c,d)))
        | (None, None) \<Rightarrow> xml_return (Runtime None)
        | _ \<Rightarrow> xml_error (STR ''runtimeComplexity must provide 0 or 2 signatures'')}"

definition position :: "nat xmlt" where
  "position = xml_do (STR ''position'') (xml_take_nat (\<lambda>n. xml_return (n - 1)))"

primrec list2position :: "nat list \<Rightarrow> pos" where
  "list2position [] = []"
| "list2position (n # ns) = n # list2position ns"

definition pos :: "pos xmlt" where
  "pos = XMLdo (STR ''positionInTerm'') {
    lst \<leftarrow>* position;
    xml_return (list2position lst)
  }"

definition
  replacement_map :: "'a muL xmlt"
where
  "replacement_map = XMLdo (STR ''contextSensitive'') {
    ret \<leftarrow>* XMLdo (STR ''replacementMapEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      is \<leftarrow>* position;
      xml_return ((f,a),is)
    };
    xml_return ret
  }"

definition forbidden_pattern :: "(('a, string) ctxt \<times> ('a, string) term \<times> location) xmlt"
where
"forbidden_pattern = XMLdo (STR ''forbiddenPattern'') {
  t \<leftarrow> term;
  p \<leftarrow> pos;
  l \<leftarrow>
    xml_leaf (STR ''here'') Forbidden_Patterns.H
    XMLor xml_leaf (STR ''above'') Forbidden_Patterns.A
    XMLor xml_leaf (STR ''below'') Forbidden_Patterns.B
    XMLor xml_leaf (STR ''below'') Forbidden_Patterns.R;
  if p \<in> poss t then xml_return (ctxt_of_pos_term p t, t |_ p, l)
  else xml_error (STR ''position does not exist in term'')
}"

definition
  forbidden_patterns :: "((('a, string) ctxt \<times> ('a, string) term \<times> Forbidden_Patterns.location) list) xmlt"
where
  "forbidden_patterns = XMLdo (STR ''forbiddenPatterns'') {
    ret \<leftarrow>* forbidden_pattern;
    xml_return ret
  }"

definition nfs_def :: "bool option \<Rightarrow> bool" where 
  "nfs_def nfs_opt = (case nfs_opt of None \<Rightarrow> default_nfs_flag | Some nfs \<Rightarrow> nfs)" 

definition innermostLhss :: "('a, string) term list xmlt"
where
  "innermostLhss = XMLdo (STR ''innermostLhss'') {ret \<leftarrow>* term; xml_return ret}"

definition innermostLhssStrategy :: "('a, string) strategy xmlt"
where
  "innermostLhssStrategy = XMLdo (STR ''innermostLhss'') {nfs \<leftarrow>? xml_bool (STR ''nfs''); 
      ret \<leftarrow>* term; xml_return (Innermost_Q (nfs_def nfs) ret)}"

definition innermost :: "('a, string) strategy xmlt"
where
  "innermost = XMLdo (STR ''innermost'') {nfs \<leftarrow>? xml_bool (STR ''nfs''); xml_return (Innermost (nfs_def nfs))}"

definition strategy :: "('a,string)strategy xmlt" where
  "strategy = XMLdo (STR ''strategy'') {
    ret \<leftarrow> innermost XMLor innermostLhssStrategy;
    xml_return ret
  }"

definition inn_fp_strategy :: "('a,string)inn_fp_strategy xmlt" where
  "inn_fp_strategy = XMLdo (STR ''strategy'') {
    ret \<leftarrow> xml_change (innermost XMLor innermostLhssStrategy) (\<lambda> s. xml_return (Inl s))
      XMLor xml_leaf (STR ''outermost'') (Inr Outermost)
      XMLor xml_change (replacement_map) (\<lambda> p. xml_return (Inr (Context_Sensitive p)))
      XMLor xml_change (forbidden_patterns) (\<lambda> p. xml_return (Inr (Forbidden_Patterns p)));
    xml_return ret
  }"

definition
  trs_input :: "('a,string)input xmlt"
where
  "trs_input = XMLdo (STR ''trsInput'') {
    r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    str \<leftarrow>[Inl No_Strategy] inn_fp_strategy;
    rel \<leftarrow>[[]] XMLdo (STR ''relativeRules'') { ret \<leftarrow> rules; xml_return ret };
    case str
    of Inl istrat \<Rightarrow> xml_return (Inn_TRS_input istrat r rel)
    |  Inr fpstrat \<Rightarrow>
      if rel = [] then xml_return (FP_TRS_input fpstrat r)
      else xml_error (STR ''the combination of relative rules with strategies is only supported for innermost'')
  }"

definition
  dp_input :: "('a,string)input xmlt"
where
  "dp_input = XMLdo (STR ''dpInput'') {
    r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    p \<leftarrow> XMLdo (STR ''dps'') { ret \<leftarrow> rules; xml_return ret };
    str \<leftarrow>[No_Strategy] strategy;
    m \<leftarrow> xml_bool (STR ''minimal'');
    xml_return (DP_input m p str r)
  }"

definition
  trs_with_signature_input :: "('a,string)input xmlt"
where
  "trs_with_signature_input = XMLdo (STR ''trsWithSignature'') {
    sig \<leftarrow> CPFsignature;
    r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    xml_return (Single_TRS_input sig r)
  }"

definition
  two_trs_with_signature_input :: "('a,string)input xmlt"
where
  "two_trs_with_signature_input = XMLdo (STR ''twoTrsWithSignature'') {
    sig \<leftarrow> CPFsignature;
    r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    s \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    xml_return (Two_TRS_input sig r s)
  }"


definition
  ac_rewrite_system :: "('a,string)input xmlt"
where
  "ac_rewrite_system = XMLdo (STR ''acRewriteSystem'') {
    r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
    asym \<leftarrow> symbols_wo_arity (STR ''Asymbols'');
    csym \<leftarrow> symbols_wo_arity (STR ''Csymbols'');
    xml_return (AC_input r asym csym)
  }"

definition state :: "string xmlt" where
  "state = xml_text (STR ''state'')"

definition final_states :: "string list xmlt" where
  "final_states = XMLdo (STR ''finalStates'') {ret \<leftarrow>* state; xml_return ret}"

definition ta_normal_lhs where
  "ta_normal_lhs = XMLdo (STR ''lhs'') {
    XMLdo {
      a \<leftarrow> state;
      xml_return (Inr a)
    } XMLor XMLdo {
      a \<leftarrow> xml2name;
      b \<leftarrow>* state;
      xml_return (Inl (a,b))
    }
  }"

definition transition where
  "transition xml2lhs = XMLdo (STR ''transition'') {
    lhs \<leftarrow> xml2lhs;
    q \<leftarrow> XMLdo (STR ''rhs'') { q \<leftarrow> state; xml_return q};
    xml_return (case lhs of
      Inl (f, qs) \<Rightarrow> Inl (TA_rule f qs q)
    | Inr q' \<Rightarrow> Inr (q', q))}"

definition "transitions xml2lhs = XMLdo (STR ''transitions'') {
  rls \<leftarrow>* transition xml2lhs;
  let (rules, eps) = partition (\<lambda>rl. case rl of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False) rls;
  let ruls = map (\<lambda>rl. case rl of Inl r \<Rightarrow> r) rules;
  let ep   = map (\<lambda>rl. case rl of Inr e \<Rightarrow> e) eps;
  xml_return (ruls, ep)
}"

definition "tree_automaton xml2lhs = XMLdo (STR ''treeAutomaton'') {
  f \<leftarrow> final_states;
  t_eps \<leftarrow> transitions xml2lhs;
  xml_return (Tree_Automaton f (fst t_eps) (snd t_eps))}"

definition tree_automaton_and_trs :: "('a,string)input xmlt" where
  "tree_automaton_and_trs = XMLdo (STR ''treeAutomatonAndTrs'') {
     ta \<leftarrow> tree_automaton ta_normal_lhs;
     r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
     xml_return (TA_input ta r) 
   }" 

definition unknown_input' :: "string xmlt"
  where "unknown_input' = xml_text (STR ''unknownInput'')"

definition unknown_input :: "('a,string)input xmlt"
  where "unknown_input = xml_change unknown_input' (\<lambda> s. xml_return (Unknown_input s))"

definition
  input :: "('a,string)input xmlt"
where
  "input = XMLdo (STR ''input'') {
    i \<leftarrow> trs_input XMLor 
     trs_with_signature_input XMLor
     two_trs_with_signature_input XMLor
     ctrs_input XMLor
     equational_reasoning_input XMLor
     equations_and_ro_input XMLor
     infeasibility_input XMLor
     equations_input XMLor
     ac_rewrite_system XMLor
     dp_input XMLor
     xml_change lts_input_parser (\<lambda> lts. xml_return (LTS_input lts)) XMLor
     xml_change lts_safety_input_parser (\<lambda> (lts,err). xml_return (LTS_safety_input lts err)) XMLor
     tree_automaton_and_trs XMLor
     unknown_input;
    xml_return i}"

definition answer :: "('a,string) answer xmlt" where
  "answer = XMLdo (STR ''answer'') {
      a \<leftarrow> (XMLdo (STR ''yes'') {
         xml_return (Decision True)
      }) XMLor (XMLdo (STR ''no'') {
         xml_return (Decision False)
      }) XMLor (XMLdo (STR ''upperBound'') {
         n \<leftarrow> xml_nat (STR ''polynomial'');
         xml_return (Upperbound_Poly n)
      }) XMLor (XMLdo (STR ''completedTrs'') {
         r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
         xml_return (Completed_System r)
      }) XMLor (XMLdo (STR ''orderCompletedSystem'') {
         e \<leftarrow> XMLdo (STR ''equations'') { ret \<leftarrow> rules; xml_return ret };
         r \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules; xml_return ret };
         xml_return (Order_Completed_System e r)
      })
      ;
      xml_return a
    }"

definition property :: "('a,string) property xmlt" where
  "property = XMLdo (STR ''property'') {
      p \<leftarrow> (XMLdo (STR ''termination'') {xml_return Termination})
        XMLor (XMLdo (STR ''confluence'') {xml_return Confluence})
        XMLor (XMLdo (STR ''commutation'') {xml_return Commutation})
        XMLor (XMLdo (STR ''completion'') {xml_return Completion})
        XMLor (XMLdo (STR ''complexity'') { cm \<leftarrow> complexity_measure; xml_return (Complexity cm)})
        XMLor (XMLdo (STR ''safety'') {xml_return Safety})
        XMLor (XMLdo (STR ''entailment'') {xml_return Entailment})
        XMLor (XMLdo (STR ''infeasibility'') {xml_return Infeasibility})
        XMLor (XMLdo (STR ''closedUnderRewriting'') {xml_return Closed_Under_Rewriting})
        XMLor (XMLdo (STR ''unknownProperty'') {xml_return Unknown_Property})
      ;
      xml_return p
    }" 

definition ruleTable :: "'a ruleIndexMap xmlt" where "ruleTable = XMLdo (STR ''ruleTable'') {
             entries \<leftarrow>* XMLdo (STR ''indexToRule'') {
                   idx \<leftarrow> xml_text (STR ''index'');
                   rule \<leftarrow> full_rule;
                   xml_return (idx,rule)
               };
             if (distinct (map fst entries)) then
               xml_return (Mapping.of_alist entries)
             else xml_error (STR ''rule table contains duplicate index'')
         }" 

definition "indexToTerm =  XMLdo (STR ''indexToTerm'') {
                   idx \<leftarrow> xml_text (STR ''index'');
                   t \<leftarrow> term;
                   case Mapping.lookup termMap idx of 
                     None \<Rightarrow> xml_return (idx,t)
                   | Some _ \<Rightarrow> xml_error (STR ''term index table contains duplicate index'') 
               }"
end

definition termIndexTable :: "'a :: showl xmlt \<Rightarrow> 'a termIndexMap xmlt" where 
  "termIndexTable xml2name = xml_do (STR ''termIndexTable'')
    (xml_foldl (indexToTerm xml2name) (\<lambda> termMap (idx,t). Mapping.update idx t termMap) Mapping.empty)" 


definition lookupTables :: "'a :: showl xmlt \<Rightarrow> ('a termIndexMap \<times> 'a ruleIndexMap) xmlt" where "lookupTables xml2name = XMLdo (STR ''lookupTables'') {
      termIndexMap \<leftarrow>[Mapping.empty] (termIndexTable xml2name);
      ruleMap \<leftarrow>[Mapping.empty] (ruleTable xml2name termIndexMap);
      xml_return (termIndexMap,ruleMap)
   }"



(*
(* ... to xml *)
primrec xml_lab :: "('f :: showl, ('l :: showl)list)lab \<Rightarrow> xml" where
  "xml_lab (UnLab x) = XML ''name'' [] [XML_text (String.explode (showl x))]"
| "xml_lab (lab.Sharp x) = XML ''sharp'' [] [xml_lab x]"
| "xml_lab (FunLab x l) = XML ''labeledSymbol'' [] [xml_lab x, XML ''symbolLabel'' [] (map xml_lab l)]"
| "xml_lab (Lab x l) = XML ''labeledSymbol'' [] [xml_lab x, XML ''numberLabel'' [] (map (\<lambda> n. XML ''number'' [] [XML_text (String.explode (showl n))]) l)]"

definition xml_signature :: "(('f :: showl,('l :: showl)list)lab \<times> nat)list \<Rightarrow> xml" where
  "\<And>fs. xml_signature fs = XML ''signature'' [] (map (\<lambda> (f,n). XML ''symbol'' [] [xml_lab f, XML ''arity'' [] [XML_text (shows n Nil)]]) fs)"

primrec xml_complexity_measure :: "(('f :: showl,('l :: showl)list)lab,'v)complexity_measure \<Rightarrow> xml" where
  "xml_complexity_measure (Derivational_Complexity F) = XML ''derivationalComplexity'' [] [xml_signature F]"
 | "xml_complexity_measure (Runtime_Complexity C D) = XML ''runtimeComplexity'' [] [xml_signature C, xml_signature D]"

primrec xml_complexity_class :: "complexity_class \<Rightarrow> xml" where
  "xml_complexity_class (Comp_Poly n) = XML ''polynomial'' [] [XML_text (shows n Nil)]"

definition xml_single_pos :: "nat \<Rightarrow> xml" where
  "xml_single_pos i = XML ''position'' [] [XML_text (show (Suc i))]"

definition xml_pos :: "pos \<Rightarrow> xml" where
  "xml_pos p = XML ''positionInTerm'' [] (map xml_single_pos p)"

primrec xml_term :: "(('f :: showl,('l :: showl)list)lab, 'v :: showl)term \<Rightarrow> xml" where
  "xml_term (Var x) = XML ''var'' [] [XML_text (String.explode (showl x))]"
| "xml_term (Fun f ts) = XML ''funapp'' []
    (xml_lab f #
      (map (\<lambda> t. XML ''arg'' [] [xml_term t]) ts))"

definition xml_condition :: "(('f :: showl,('l :: showl)list)lab,'c :: showl) rule \<Rightarrow> xml" where
  "xml_condition = (\<lambda>(l, r). XML ''condition'' [] [
    XML ''lhs'' [] [xml_term l] ,
    XML ''rhs'' [] [xml_term r] ])"

definition xml_crule :: "(('f :: showl,('l :: showl)list)lab,'c :: showl) crule \<Rightarrow> xml" where
  "xml_crule = (\<lambda>((l,r), conds). XML ''rule'' [] (
    XML ''lhs'' [] [xml_term l] #
    XML ''rhs'' [] [xml_term r] #
    (if conds = [] then [] else [XML ''conditions'' [] (map xml_condition conds)])))"

definition xml_rule :: "(('f :: showl,('l :: showl)list)lab,'c :: showl) rule \<Rightarrow> xml" where
  "xml_rule = (\<lambda> (l, r). XML ''rule'' [] [
    XML ''lhs'' [] [xml_term l] ,
    XML ''rhs'' [] [xml_term r] ])"

definition xml_rules :: "string \<Rightarrow> (('f :: showl,('l :: showl)list)lab,'c :: showl) rules \<Rightarrow> xml" where
  "xml_rules tag rls = XML tag Nil [XML ''rules'' [] (map xml_rule rls)]"

definition xml_forbidden_pattern :: "(('f :: showl,('l :: showl) list)lab,'v :: showl) forb_pattern \<Rightarrow> xml" where
  "xml_forbidden_pattern = (\<lambda> (C,t,l). XML ''forbiddenPattern'' [] [
    xml_term C\<langle>t\<rangle>,
    xml_pos (hole_pos C),
    (case l of Forbidden_Patterns.H \<Rightarrow> XML ''here'' [] []
             | Forbidden_Patterns.A \<Rightarrow> XML ''above'' [] []
             | Forbidden_Patterns.B \<Rightarrow> XML ''below'' [] []
             | Forbidden_Patterns.R \<Rightarrow> XML ''right'' [] [] )
   ])"

definition xml_repl_map :: "(('f :: showl,('l :: showl) list)lab \<times> nat) \<times> (nat list) \<Rightarrow> xml" where
  "xml_repl_map = (\<lambda> ((f,a),l). XML ''replacementMapEntry'' [] (
    xml_lab f #
    XML ''arity'' [] [XML_text (show a)] #
    map xml_single_pos l
    ))"

definition xml_strategy :: "(('f :: showl,('l :: showl) list)lab,'v :: showl)inn_fp_strategy \<Rightarrow> xml list"
  where "xml_strategy x = (case x of
    Inl No_Strategy \<Rightarrow> []
  | Inl Innermost  \<Rightarrow> [XML ''strategy'' [] [XML ''innermost'' [] []]]
  | Inr Outermost \<Rightarrow> [XML ''strategy'' [] [XML ''outermost'' [] []]]
  | Inr (Forbidden_Patterns p) \<Rightarrow> [XML ''strategy'' [] [XML ''forbiddenPatterns'' [] (map xml_forbidden_pattern p)]]
  | Inr (Context_Sensitive \<mu>) \<Rightarrow> [XML ''strategy'' [] [XML ''contextSensitive'' [] (map xml_repl_map \<mu>)]]
  | Inl (Innermost_Q Q) \<Rightarrow> [XML ''strategy'' [] [XML ''innermostLhss'' [] (map xml_term Q)]])"

fun xml_trs_input :: "(('f :: showl,('l :: showl) list)lab,'v :: showl)inn_fp_strategy \<Rightarrow> (('f,'l list)lab,'v)rules
  \<Rightarrow> (('f,'l list)lab,'v)rules \<Rightarrow> xml"
  where "xml_trs_input strat R [] =  XML ''trsInput'' [] ([xml_rules ''trs'' R] @ xml_strategy strat)"
  |     "xml_trs_input strat R S = XML ''trsInput'' [] (xml_rules ''trs'' R # xml_strategy strat @ [xml_rules ''relativeRules'' S])"

definition xml_state :: "string \<Rightarrow> xml" where
  "xml_state s = XML ''state'' [] [XML_text s]"

fun xml_eps_transition :: "string \<times> string \<Rightarrow> xml" where
  "xml_eps_transition (s,t) = XML ''transition'' [] [
    XML ''lhs'' [] [xml_state s],
    XML ''rhs'' [] [xml_state t]]"

fun xml_transition :: "(string,('f :: showl,('l :: showl) list)lab)ta_rule \<Rightarrow> xml" where
  "xml_transition (TA_rule f qs q) = XML ''transition'' [] [
    XML ''lhs'' [] (xml_lab f # map xml_state qs),
    XML ''rhs'' [] [xml_state q]]"

fun xml_ta :: "(string,('f :: showl,('l :: showl) list)lab)tree_automaton \<Rightarrow> xml" where
  "xml_ta (Tree_Automaton fin tran eps) =  XML ''treeAutomaton'' [] [
    XML ''finalStates'' [] (map xml_state fin),
    XML ''transitions'' [] (map xml_transition tran @ map xml_eps_transition eps)]"

definition xml_ta_input :: "(string,('f :: showl,('l :: showl) list)lab)tree_automaton \<Rightarrow> (('f,'l list)lab,'v :: showl)rules
  \<Rightarrow> xml"
  where "xml_ta_input ta R =  XML ''treeAutomatonProblem'' [] ([xml_ta ta, xml_rules ''trs'' R])"

definition xml_ctrs_input :: "(('f :: showl,('l :: showl) list)lab,'v :: showl)crules \<Rightarrow> xml"
  where "xml_ctrs_input ctrs =  XML ''ctrsInput'' [] [XML ''rules'' [] (map xml_crule ctrs)]"

definition xml_ac_input :: "(('f :: showl,('l :: showl)list)lab,'v::showl)rules
  \<Rightarrow> ('f,'l list)lab list \<Rightarrow> ('f,'l list)lab list \<Rightarrow> xml" where
  "xml_ac_input r a c = XML ''acRewriteSystem'' [] [
     xml_rules ''trs'' r,
     XML ''Asymbols'' [] (map xml_lab a),
     XML ''Csymbols'' [] (map xml_lab c)
   ]"

definition xml_location_id :: "string \<Rightarrow> xml" where
  "xml_location_id x = XML ''locationId'' [] [XML_text x]"

definition xml_transition_id :: "string \<Rightarrow> xml" where
  "xml_transition_id x = XML ''transitionId'' [] [XML_text x]"

fun xml_trans_var where
  "xml_trans_var (Pre x) = XML ''variableId'' [] [XML_text (show x)]"
| "xml_trans_var (Post x) = XML ''post'' [] [XML ''variableId'' [] [XML_text (show x)]]"
| "xml_trans_var _ = Code.abort (STR ''problem in xml_trans_var'') (\<lambda> _. XML [] [] [])"

fun xml_expr :: "(IA.sig,_,_)exp \<Rightarrow> xml" where
  "xml_expr (Var (x,ty)) = xml_trans_var x"
| "xml_expr (Fun (IA.SumF n) ls) = XML ''sum'' [] (map xml_expr ls)"
| "xml_expr (Fun (IA.ConstF i) []) = XML ''constant'' [] [XML_text (show i)]"
| "xml_expr (Fun (IA.ProdF n) ls) = XML ''product'' [] (map xml_expr ls)"
| "xml_expr _ = Code.abort (STR ''problem in xml_expr for LIA'') (\<lambda> _. XML [] [] [])"

fun xml_atom :: "(IA.sig,_,_)exp \<Rightarrow> xml" where
  "xml_atom (Fun IA.LessF [l,r]) = XML ''less'' [] [xml_expr l, xml_expr r]"
| "xml_atom (Fun IA.LeF [l,r]) = XML ''leq'' [] [xml_expr l, xml_expr r]"
| "xml_atom (Fun IA.EqF [l,r]) = XML ''eq'' [] [xml_expr l, xml_expr r]"
| "xml_atom _ = Code.abort (STR ''problem in xml_atom for IA'') (\<lambda> _. XML [] [] [])"

fun xml_formula :: "_ \<Rightarrow> xml" where
  "xml_formula (Conjunction \<phi>s) = XML ''conjunction'' [] (map xml_formula \<phi>s)"
| "xml_formula (Disjunction \<phi>s) = XML ''disjunction'' [] (map xml_formula \<phi>s)"
| "xml_formula (Atom \<phi>) = xml_atom \<phi>"
| "xml_formula (NegAtom \<phi>) = Code.abort (STR ''negated atom not supported in xml_formula'') (\<lambda> _. XML [] [] [])"

fun xml_transition_rule :: "string \<times> (_,_,_,_) transition_rule \<Rightarrow> xml" where
  "xml_transition_rule (i, Transition l r \<phi>) = XML ''transition'' [] [
      xml_transition_id i,
      XML ''source'' [] [xml_location_id l],
      XML ''target'' [] [xml_location_id r],
      XML ''formula'' [] [xml_formula \<phi>]
   ]"

fun xml_lts :: "(_,_,_,_,_) lts_impl \<Rightarrow> xml" where
  "xml_lts (Lts_Impl I tau lc) = XML ''lts'' [] (
      XML ''initial'' [] (map xml_location_id I) #
      map xml_transition_rule tau
   )"

definition xml_lts_safety :: "(_,_,_,_,_) lts_impl \<Rightarrow> string list \<Rightarrow> xml" where
  "xml_lts_safety ltsi err = XML ''ltsSafetyInput'' [] (
      xml_lts ltsi  #
      map (\<lambda> e. XML ''error'' [] [xml_location_id e]) err
   )"

definition xml_precweight where
"xml_precweight pw =
  (let ((f,a), (p,w,e)) = pw in
  XML ''precedenceWeightEntry'' [] ([
    xml_lab f,
    XML ''arity'' [] [XML_text (show a)],
    XML ''precedence'' [] [XML_text (show p)],
    XML ''weight'' [] [XML_text (show w)]
  ] @ (
    case e of None \<Rightarrow> [] | Some scfs \<Rightarrow> [
    XML ''subtermCoefficientEntries'' [] (map (\<lambda>i. XML_text (show i)) scfs)
  ])))"

primrec xml_redord :: "_ reduction_order_input \<Rightarrow> xml" where
  "xml_redord (KBO_Input precw_w0) = XML ''reductionOrder'' [] [XML ''knuthBendixOrder'' [] [
  XML ''w0'' [] [XML_text (show (snd precw_w0))],
  XML ''precedenceWeight'' [] (map xml_precweight (fst precw_w0))
  ]]"
*)
end
