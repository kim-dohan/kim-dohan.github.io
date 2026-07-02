\<^marker>\<open>creator "Max W. Haslbeck"\<close>
theory SEG_XML_Parser
imports
  LTS.LTS_Parser
  LLVM_Termination_Prover
  LLVM_Parser
begin

definition name_parser where
  "name_parser = xml_do STR ''unname'' (xml_take_nat (xml_return \<circ> UnName))
                 XMLor
                 xml_do STR ''name'' (xml_take_text (xml_return \<circ> Name \<circ> String.implode))"

definition pos_parser where
  "pos_parser = XMLdo {
       fn \<leftarrow> xml_do STR ''function'' (xml_take name_parser xml_return);
       ln \<leftarrow> xml_do STR ''block'' (xml_take name_parser xml_return);
       n \<leftarrow> xml_nat STR ''line'';
       xml_return (fn, ln, n)
    }"

definition "map_parser key_parser value_parser =
  XMLdo {
   ms \<leftarrow>* XMLdo STR ''entry'' {
      x \<leftarrow> xml_do STR ''key'' key_parser;
      y \<leftarrow> xml_do STR ''value'' value_parser;
      xml_return (x,y)};
   xml_return ms
}"

definition char_list_term_to_String_term where
  "char_list_term_to_String_term = map_vars_term (\<lambda>(n, t). (String.implode n, t))"


definition char_list_formula_to_String_formula where
  "char_list_formula_to_String_formula = map_formula char_list_term_to_String_term"

definition as_parser where
  "as_parser \<equiv> XMLdo STR ''as'' {
    pos \<leftarrow> xml_do (STR ''pos'') pos_parser;
    s \<leftarrow> xml_do (STR ''stack'') (map_parser (xml_take name_parser xml_return) (xml_take_text xml_return));
    f \<leftarrow> xml_do (STR ''kb'')  (xml_take (formula_parser atom_parser) xml_return);
    xml_return (pos, s, f)
  }"

definition node_parser where
  "node_parser \<equiv> XMLdo STR ''node'' {
    i \<leftarrow> xml_text (STR ''nodeId'');
    as \<leftarrow> as_parser;
    xml_return (i, as)
  }"

definition nodes_parser where
  "nodes_parser \<equiv> XMLdo (STR ''nodes'') {
    ns \<leftarrow>* node_parser;
    xml_return ns
  }"

definition exp_parser_string where
  "exp_parser_string = (\<lambda>x. (exp_parser x) \<bind> Right \<circ> char_list_term_to_String_term)"

definition edge_rule_parser where
  "edge_rule_parser =
    XMLdo STR ''eval''
      {n \<leftarrow> xml_text STR ''target'';
       v \<leftarrow> xml_do STR ''variable'' (xml_take_text xml_return);
       xml_return (Eval n v)}
    XMLor
    XMLdo STR ''gen''
      {n \<leftarrow> xml_text STR ''target'';
       ps \<leftarrow> xml_do STR ''renaming'' (map_parser (xml_take_text xml_return) (xml_take_text xml_return));
       xml_return (Gen n ps)}
    XMLor
    XMLdo STR ''refine''
      {n1 \<leftarrow> xml_text STR ''target'';
       n2 \<leftarrow> xml_text STR ''target'';
       f \<leftarrow> xml_do STR ''formula'' (xml_take (formula_parser atom_parser) xml_return);
       xml_return (Refine n1 n2 f)}
    XMLor
    XMLdo STR ''br''
      {n \<leftarrow> xml_text STR ''target'';
       ps \<leftarrow> xml_do STR ''phi'' (map_parser (xml_take_text xml_return) (xml_take exp_parser xml_return));
       xml_return (Br n ps)}
    XMLor
    XMLdo STR ''condbr''
      {n \<leftarrow> xml_text STR ''target'';
       ps \<leftarrow> xml_do STR ''phi'' (map_parser (xml_take_text xml_return) (xml_take exp_parser xml_return));
       b \<leftarrow> xml_or (xml_do STR ''true'' (xml_return True)) (xml_do STR ''false'' (xml_return False));
       xml_return (CondBr n ps b)}
    XMLor
    XMLdo STR ''icmp''
      {n \<leftarrow> xml_text STR ''target'';
       v \<leftarrow> xml_do STR ''variable'' (xml_take_text (xml_return));
       b \<leftarrow> xml_or (xml_do STR ''true'' (xml_return True)) (xml_do STR ''false'' (xml_return False));
       xml_return (Icmp n v b)}
    XMLor
    xml_do STR ''return'' (xml_return Return)
"

definition edge_parser where
  "edge_parser \<equiv> XMLdo STR ''edge'' {
    i \<leftarrow> xml_text (STR ''source'');
    r \<leftarrow> xml_do (STR ''rule'') (xml_take edge_rule_parser xml_return);
    xml_return (i, r)
  }"

definition edges_parser where
  "edges_parser \<equiv> XMLdo (STR ''edges'') {
    ns \<leftarrow>* edge_parser;
    xml_return ns
  }"

definition seg_parser where
  "seg_parser \<equiv> XMLdo STR ''seg'' {
    i \<leftarrow> xml_text STR ''initialnode'';
    ns \<leftarrow> nodes_parser;
    es \<leftarrow> edges_parser;
    xml_return (Seg_Impl i es ns)
  }"

definition llvm_input_parser where
  "llvm_input_parser \<equiv> XMLdo {
    fn \<leftarrow> xml_do STR ''function'' (xml_take name_parser xml_return);
    n \<leftarrow> xml_do STR ''llvmprog'' (xml_take_text (xml_return \<circ> parse_llvm o String.implode));
    xml_return (fn, n)
  }"

definition seg_lts_parser where
  "seg_lts_parser \<equiv> XMLdo STR ''input'' {
    ns \<leftarrow> seg_parser;
    es \<leftarrow> lts_input_parser;
    xml_return (ns, es)
  }"

definition llvm_termination_proof_parser where
  "llvm_termination_proof_parser \<equiv> XMLdo {
    seg \<leftarrow> seg_parser;
    (lts, renamings, proof) \<leftarrow> XMLdo STR ''ltsandproof'' {
          lts \<leftarrow> lts_input_parser;
          renamings \<leftarrow> xml_do STR ''renamings''
                       (map_parser (xml_take (xml_text STR ''location'') xml_return)
                       (map_parser (xml_take variable_parser xml_return) (xml_take variable_parser xml_return)));
          proof \<leftarrow> xml_do STR ''ltsTerminationProof'' (xml_take lts_termination_proof_parser xml_return);
          xml_return (lts, renamings, proof)
      };
    xml_return (Llvm_termination_proof seg renamings lts proof)
  }"

definition llvm_represents_seg_parser where
  "llvm_represents_seg_parser \<equiv> XMLdo {
    seg \<leftarrow> seg_parser;
    xml_return seg
  }"

definition llvm_represents_lts_parser where
  "llvm_represents_lts_parser \<equiv> XMLdo {
    seg \<leftarrow> seg_parser;
    (lts, renamings) \<leftarrow> XMLdo STR ''ltsandproof'' {
          lts \<leftarrow> lts_input_parser;
          renamings \<leftarrow> xml_do STR ''renamings''
                       (map_parser (xml_take (xml_text STR ''location'') xml_return)
                       (map_parser (xml_take variable_parser xml_return) (xml_take variable_parser xml_return)));
          xml_return (lts, renamings)
      };
    xml_return (seg, renamings, lts)
  }"

definition parse_xml_string_literal where
  "parse_xml_string_literal f s = update_error (parse_xml_string f (String.explode s)) (showsl_lit \<circ> String.implode)"

end