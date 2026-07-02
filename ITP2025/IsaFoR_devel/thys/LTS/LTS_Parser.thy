theory LTS_Parser
imports 
  XML.Xmlt
  IA_Instance
begin

hide_const (open) name

(* move? *)

context
  fixes atom_parser :: "('f,'a,'t) exp formula xmlt"
begin

partial_function (sum_bot) formula_parser :: "('f,'a,'t) exp formula xmlt" where
  [code]: "formula_parser x = (
  XMLdo (STR ''disjunction'') {
    fs \<leftarrow>* formula_parser; xml_return (Disjunction fs)
  } XMLor XMLdo (STR ''conjunction'') {
    fs \<leftarrow>* formula_parser; xml_return (Conjunction fs)
  } XMLor atom_parser) x"

end

context
  fixes location_parser :: "'l xmlt"
    and trans_parser :: "'tr xmlt"
    and tatom_parser :: "('f,'v trans_var,'t) exp formula xmlt"
begin

definition transition_parser :: "('tr \<times> ('f,'v,'t,'l) transition_rule) xmlt" where
  "transition_parser \<equiv> XMLdo (STR ''transition'') {
    tr \<leftarrow> trans_parser;
    l \<leftarrow> xml_do (STR ''source'') (xml_take location_parser xml_return);
    r \<leftarrow> xml_do (STR ''target'') (xml_take location_parser xml_return);
    \<phi> \<leftarrow> xml_do (STR ''formula'') (xml_take (formula_parser tatom_parser) xml_return);
    xml_return (tr, Transition l r \<phi>)
  }"


definition lts_parser :: "ltag \<Rightarrow> ('f,'v,'t,'l,'tr) lts_impl xmlt" where
  "lts_parser tag \<equiv> XMLdo tag {
     i \<leftarrow> xml_do (STR ''initial'') (xml_take_many 1 \<infinity> location_parser xml_return);
     t \<leftarrow>* transition_parser;
    xml_return (Lts_Impl i t [])
   }"

definition "safety_input_parser \<equiv>
  XMLdo (STR ''ltsSafetyInput'') {
    lts \<leftarrow> lts_parser (STR ''lts'');
    err \<leftarrow> xml_do (STR ''error'') (xml_take_many 1 \<infinity> location_parser xml_return);
    xml_return (lts,err)
  }"

end

partial_function (sum_bot) hints_parser :: "'h :: default xmlt" where
 [code]: "hints_parser xml =
  XMLdo (STR ''auto'') {
    xml_return default
  } xml" 

context
  fixes art_node_id_parser :: "ltag \<Rightarrow> 'n xmlt"
    and location_parser :: "'l xmlt"
    and trans_parser :: "'tr xmlt"
    and atom_parser :: "('f,'v,'t) exp formula xmlt"
begin

definition formula_pos_parser :: "nat xmlt" where [code]:
 "formula_pos_parser =
  XMLdo (STR ''conclusion'') {xml_return 0}
  XMLor XMLdo (STR ''assertion'') {xml_return 2}
  XMLor XMLdo (STR ''transition'') {xml_return 3}
  XMLor XMLdo (STR ''targetAssertion'') {xml_return 4}"

definition art_node_parser :: "(('f, 'v, 't, 'l, 'n, 'tr, 'h :: default) art_node_impl \<times> 'n list) xmlt" where
 "art_node_parser \<equiv> XMLdo (STR ''node'') {
    init \<leftarrow>[False] (xml_do (STR ''initial'') (xml_return True));
    nodeId \<leftarrow> art_node_id_parser (STR ''nodeId'');
    invariant \<leftarrow> xml_do (STR ''invariant'') (xml_take (formula_parser atom_parser) xml_return);
    location \<leftarrow> xml_do (STR ''location'') (xml_take location_parser xml_return);
    edges \<leftarrow> XMLdo (STR ''children'') {
        chs \<leftarrow>*
          XMLdo (STR ''child'') {
            tr \<leftarrow> trans_parser;
            n \<leftarrow> art_node_id_parser (STR ''nodeId'');
            h \<leftarrow>[default] (xml_do (STR ''hints'') (xml_take hints_parser xml_return));
            xml_return (tr, n, h)
          };
        xml_return (Children_Edge chs)
      } XMLor XMLdo (STR ''coverEdge'') {
          n \<leftarrow> art_node_id_parser (STR ''nodeId'');
          h \<leftarrow>[default] xml_do (STR ''hints'') (xml_take hints_parser xml_return);
          xml_return (Cover_Edge n h)
       };
    xml_return (Art_Node nodeId invariant location edges, if init then [nodeId] else [])
  }"

definition art_parser :: "(('f, 'v, 't, 'l, 'n, 'tr, 'h :: default) art_impl) xmlt" where
 "art_parser \<equiv> XMLdo (STR ''impact'') {
    init \<leftarrow>[[]] xml_change (art_node_id_parser (STR ''initial'')) (\<lambda>x. xml_return [x]);
    pairs \<leftarrow> xml_do (STR ''nodes'') (xml_take_many 0 \<infinity> art_node_parser xml_return);
    let nodes = map fst pairs;
    let inits = init @ concat (map snd pairs);
    xml_return \<lparr> art_impl.initial_nodes = inits, nodes = nodes \<rparr>
  }"

end

context
  fixes location_parser :: "'l xmlt"
    and trans_parser :: "'tr xmlt"
    and atom_parser :: "('f,'v,'t) exp formula xmlt"
begin

type_synonym art_node_id = string

abbreviation art where "art \<equiv> art_parser xml_text location_parser trans_parser atom_parser"

definition "invariant_proof_parser I \<equiv>
  xml_change art (\<lambda> prf. xml_return (Impact I prf))"

definition invariant_parser :: "('l \<times> ('f,'v,'t) exp formula) xmlt" where
 "invariant_parser \<equiv> XMLdo (STR ''invariant'') {
    l \<leftarrow> xml_do (STR ''location'') (xml_take location_parser xml_return);
    \<phi> \<leftarrow> xml_do (STR ''formula'') (xml_take (formula_parser atom_parser) xml_return);
    xml_return (l,\<phi>)
  }"

definition invariants_parser :: "('l \<times> ('f,'v,'t) exp formula)list xmlt" where
 "invariants_parser \<equiv> xml_do (STR ''invariants'') (xml_take_many 0 \<infinity> invariant_parser xml_return)"

definition safety_proof_parser :: "('f,'v,'t,'l,string,'tr,'h :: default) safety_proof xmlt" where
 "safety_proof_parser \<equiv> XMLdo (STR ''safetyViaInvariants'') {
    I \<leftarrow> invariants_parser;
    p \<leftarrow> invariant_proof_parser I;
    xml_return (safety_proof.Invariant_Assertion p safety_proof.Trivial)
  }"

end


fun cut_points_to_transitions :: "_ \<Rightarrow> _ \<Rightarrow> ('f,'v,'t,'l sharp,'tr sharp) transitions_impl" where
  "cut_points_to_transitions ts [] = ts"
| "cut_points_to_transitions ts ((l,tr,\<phi>)#cps) =
   cut_points_to_transitions ((Flat tr, Transition (Flat l) (Sharp l) \<phi>)#ts) cps"

context
  fixes location_id_parser :: "ltag \<Rightarrow> 'l xmlt"
    and trans_id_parser :: "ltag \<Rightarrow> 'tr xmlt"
    and exp_parser :: "('f,'v,'t) exp xmlt"
    and atom_parser :: "('f,'v,'t) exp formula xmlt"
    and tatom_parser :: "('f,'v trans_var,'t) exp formula xmlt"
    and variable_parser :: "'v xmlt"
    and trans_var_parser :: "'v trans_var xmlt"
    and hint_parser :: "'h :: default xmlt"
    and type_parser :: "'t xmlt"
    and dom_type :: "'t"
begin

definition "location_parser \<equiv> location_id_parser (STR ''locationId'')"

definition sharp_location_parser :: "'l sharp xmlt" where
 "sharp_location_parser \<equiv>
    (xml_change (location_id_parser (STR ''locationDuplicate'')) (xml_return \<circ> Sharp))
    XMLor (xml_change (location_id_parser (STR ''locationId'')) (xml_return \<circ> Flat))"

abbreviation "tformula \<equiv> formula_parser tatom_parser"

context
  fixes trans_parser :: "'trr xmlt"
begin

abbreviation "lts \<equiv> lts_parser sharp_location_parser trans_parser tatom_parser"

abbreviation "transition \<equiv> transition_parser sharp_location_parser trans_parser tatom_parser"

abbreviation "invariant_proof \<equiv> invariant_proof_parser sharp_location_parser trans_parser atom_parser"

abbreviation "invariants \<equiv> invariants_parser sharp_location_parser atom_parser"

partial_function (sum_bot) cooperation_proof_parser where [code]: "cooperation_proof_parser xs = (
  xml_do (STR ''trivial'') (xml_return cooperation_proof.Trivial)
  XMLor XMLdo (STR ''newInvariants'') {
    i \<leftarrow> invariants;
    p \<leftarrow> invariant_proof i;
    cp \<leftarrow> cooperation_proof_parser;
    xml_return (Invariants_Update p cp)
  } XMLor XMLdo (STR ''transitionRemoval'') {
    rs \<leftarrow> XMLdo (STR ''rankingFunctions'') {
      pairs \<leftarrow>* XMLdo (STR ''rankingFunction'') {
        l \<leftarrow> xml_do (STR ''location'') (xml_take sharp_location_parser xml_return);
        es \<leftarrow> xml_do (STR ''expression'') (xml_take_many 1 \<infinity> exp_parser xml_return);
        xml_return (l,es)
      };
      xml_return pairs};
    bounds \<leftarrow> xml_do (STR ''bound'') (xml_take_many 0 \<infinity> exp_parser xml_return);
    removed \<leftarrow> xml_do (STR ''remove'') (xml_take_many 0 \<infinity> trans_parser xml_return);
    hinter \<leftarrow>[\<lambda>x. default] XMLdo (STR ''hints'') {
      pairs \<leftarrow>* XMLdo (STR ''hint'') {
        tr \<leftarrow> trans_parser;
        hint \<leftarrow>[default] hints_parser;
        xml_return (tr, hint)
      };
      xml_return (map_of_default default pairs)};
    inner \<leftarrow> cooperation_proof_parser;
    let rf = map_of_default [] rs;
    xml_return (Transition_Removal (Transition_removal_info rf removed dom_type bounds hinter) inner)
  } XMLor XMLdo (STR ''locationAddition'') {
    tr \<leftarrow> transition;
    prof \<leftarrow> cooperation_proof_parser;
    let (tr_id,tau) = tr;
    xml_return (Location_Addition (Location_Addition_Info (source tau) (target tau) tr_id tau) prof)
  } XMLor XMLdo (STR ''freshVariableAddition'') {
    x1 \<leftarrow> variable_parser;
    x2 \<leftarrow> type_parser;
    x3 \<leftarrow> XMLdo (STR ''additionalFormulas'') {
      pairs \<leftarrow>* XMLdo (STR ''additionalFormula'') {
         tr \<leftarrow> trans_parser;
         \<phi> \<leftarrow> tformula;
         xml_return (tr,\<phi>)
      };
      xml_return pairs
    };
    prof \<leftarrow> cooperation_proof_parser;
    xml_return (Fresh_Variable_Addition (Fresh_Variable_Addition_Info x1 x2 x3) prof)
  } XMLor XMLdo (STR ''cutTransitionSplit'') {
    ps \<leftarrow>* (XMLdo (STR ''cutTransitionsWithProof'') {
      cuts \<leftarrow> xml_do (STR ''cutTransitions'') (xml_take_many 0 \<infinity> trans_parser xml_return);
      prof \<leftarrow> cooperation_proof_parser;
      xml_return (cuts,prof)});
    xml_return (Cut_Transition_Split ps)
  } XMLor XMLdo (STR ''sccDecomposition'') {
    sccs \<leftarrow>* XMLdo (STR ''sccWithProof'') {
      scc :: 'l sharp list \<leftarrow> xml_do (STR ''scc'') (xml_take_many 1 \<infinity> sharp_location_parser xml_return);
      prof \<leftarrow> cooperation_proof_parser;
      xml_return (scc,prof)};
    xml_return (Scc_Decomp sccs)
  }) xs" 

end

definition "trans_id \<equiv> trans_id_parser (STR ''transitionId'')"


definition "sharp_trans_id \<equiv>
  xml_change (trans_id_parser (STR ''transitionDuplicate'')) (xml_return \<circ> Sharp)
  XMLor xml_change (trans_id_parser (STR ''transitionId'')) (xml_return \<circ> Flat)"

definition "cutPoints_parser \<equiv> XMLdo (STR ''cutPoints'') {
  tuples \<leftarrow>* XMLdo (STR ''cutPoint'') {
    l \<leftarrow> location_id_parser (STR ''locationId'');
    tr \<leftarrow> trans_id_parser (STR ''skipId'');
    \<phi> \<leftarrow> XMLdo (STR ''skipFormula'') {
      ret \<leftarrow> tformula;
      xml_return ret
    };
    xml_return (l,tr,\<phi>)
  };
  xml_return (cut_points_to_transitions [] tuples)
}"

partial_function (sum_bot) termination_proof_parser where [code]: "termination_proof_parser xml = (
  XMLdo (STR ''trivial'') {
    xml_return termination_proof.Trivial
  } XMLor XMLdo (STR ''newInvariants'') {
    i \<leftarrow> invariants_parser location_parser atom_parser;
    p \<leftarrow> invariant_proof_parser location_parser trans_id atom_parser i;
    cp \<leftarrow> termination_proof_parser;
    xml_return (Invariants_Update_LTS p cp)
  } XMLor XMLdo (STR ''switchToCooperationTermination'') {
    cp \<leftarrow> cutPoints_parser;
    p \<leftarrow> cooperation_proof_parser sharp_trans_id;
    xml_return (termination_proof.Via_Cooperation [(cp,p)])
  }
) xml" 
end


type_synonym location_id = string
type_synonym transition_id = string
type_synonym variable_id = string


definition variable_parser :: "variable_id xmlt" where
  "variable_parser = xml_text (STR ''variableId'')"

definition trans_var_parser :: "variable_id trans_var xmlt" where
  "trans_var_parser =
    XMLdo (STR ''post'') {v \<leftarrow> variable_parser; xml_return (Post v)}
    XMLor XMLdo (STR ''aux'') {v \<leftarrow> variable_parser; xml_return (Intermediate v)}
    XMLor xml_change variable_parser (xml_return \<circ> Pre)"

definition "constant_parser \<equiv> xml_int (STR ''constant'')"

partial_function (sum_bot) exp_parser' :: "'a xmlt \<Rightarrow> 'a IA.exp xmlt" where
  [code]: "exp_parser' v xml = (
  XMLdo (STR ''product'') {
    exps \<leftarrow>* exp_parser' v;
    xml_return (Fun (IA.ProdF (length exps)) exps)
  } XMLor XMLdo (STR ''sum'') {
    exps \<leftarrow>* exp_parser' v;
    xml_return (Fun (IA.SumF (length exps)) exps)
  } XMLor xml_change (xml_int (STR ''constant'')) (\<lambda>i. xml_return (IA.const i))
  XMLor xml_change v (\<lambda> x. xml_return (IA.var x))
  ) xml"

definition bexp_parser' :: "'a xmlt \<Rightarrow> 'a IA.formula xmlt" where
 "bexp_parser' v \<equiv>
  (let bexp_parser'' = 
  XMLdo (STR ''leq'') {
    l \<leftarrow> exp_parser' v;
    r \<leftarrow> exp_parser' v;
    xml_return (Fun IA.LeF [l, r])
  } XMLor XMLdo (STR ''less'') {
    l \<leftarrow> exp_parser' v;
    r \<leftarrow> exp_parser' v;
    xml_return (Fun IA.LessF [l,r])
  } XMLor XMLdo (STR ''eq'') {
    l \<leftarrow> exp_parser' v;
    r \<leftarrow> exp_parser' v;
    xml_return (Fun IA.EqF [l,r])
  } XMLor XMLdo (STR ''geq'') {
    l \<leftarrow> exp_parser' v;
    r \<leftarrow> exp_parser' v;
    xml_return (Fun IA.LeF [r,l])
  } XMLor XMLdo (STR ''greater'') {
    l \<leftarrow> exp_parser' v;
    r \<leftarrow> exp_parser' v;
    xml_return (Fun IA.LessF [r,l])
  }
  in
  XMLdo STR ''not'' {a \<leftarrow> bexp_parser''; xml_return (NegAtom a)}
  XMLor xml_change bexp_parser'' (xml_return \<circ> Atom))"

definition "exp_parser \<equiv> exp_parser' variable_parser" 
definition "atom_parser \<equiv> xml_change (bexp_parser' variable_parser) xml_return"
definition "tatom_parser \<equiv> xml_change (bexp_parser' trans_var_parser) xml_return"
definition "atom_parser' = xml_change (bexp_parser' variable_parser) xml_return"
definition "tatom_parser' = xml_change (bexp_parser' trans_var_parser) xml_return"

definition valuation_parser :: "(string \<times> string IA.exp) list xmlt"
  where
    "valuation_parser = XMLdo (STR ''substitution'') {
      list \<leftarrow>* XMLdo (STR ''substEntry'') {
        var \<leftarrow> variable_parser;
        expr \<leftarrow> exp_parser;
        xml_return (var,expr)
      };
      xml_return list
    }"

definition state_parser
  where "state_parser \<equiv> XMLdo (STR ''state'') {
       loc \<leftarrow> location_parser xml_text;
       s \<leftarrow> valuation_parser;
       xml_return (s, loc)
     }"

definition type_parser :: "IA.ty xmlt" where
  "type_parser \<equiv>
    XMLdo (STR ''int'') {xml_return IA.IntT} XMLor XMLdo (STR ''bool'') {xml_return IA.BoolT}"


definition "lts_input_parser \<equiv>
  lts_parser
    (location_parser xml_text)
    (trans_id xml_text) tatom_parser'  (STR ''lts'')"

definition "lts_safety_input_parser \<equiv>
  safety_input_parser (location_parser xml_text) (trans_id xml_text) tatom_parser'"

definition "lts_termination_proof_parser \<equiv>
  termination_proof_parser
    xml_text
    xml_text
    exp_parser atom_parser tatom_parser variable_parser type_parser IA.IntT"

definition "lts_safety_proof_parser \<equiv>
  safety_proof_parser (location_parser xml_text) (trans_id xml_text) atom_parser"

definition transition_step_parser where "transition_step_parser \<equiv>
  XMLdo (STR ''transitionStep'') {
        src \<leftarrow> state_parser;
        tid \<leftarrow> trans_id xml_text;
        tgt \<leftarrow> state_parser;
        xml_return (src, tid, tgt)
      }"

definition transition_seq_parser
  where
    "transition_seq_parser name = XMLdo name {
      list \<leftarrow>* transition_step_parser;
      xml_return list
    }"


definition nontermination_proof where "nontermination_proof \<equiv>
  XMLdo (STR ''equivalentState'') {
        i \<leftarrow> location_parser xml_text;
        stem \<leftarrow> transition_seq_parser (STR ''stem'');
        loop \<leftarrow> transition_seq_parser (STR ''loop'');
        xml_return (i, stem, loop)
      }"


context
  fixes location_parser :: "'l xmlt"
    and trans_parser :: "'tr xmlt"
    and trans_var_parser :: "'v trans_var xmlt"
    and tatom_parser :: "('f,'v trans_var,'t) Sorted_Algebra.exp Formula.formula xmlt"
begin

definition "nontermination_input_parser \<equiv>
  XMLdo (STR ''nonterminationInput'') {
    lts \<leftarrow> lts_parser location_parser trans_parser tatom_parser (STR ''lts'');
    xml_return lts
  }"
end
end
