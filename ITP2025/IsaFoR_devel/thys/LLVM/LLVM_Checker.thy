theory LLVM_Checker
  imports
    SEG_XML_Parser
    LLVM_Termination_Prover
    Auxx.Xmlt2
begin

definition llvm_termination_parser where
  "llvm_termination_parser =
     XMLdo STR ''certificationProblem'' {
     (fn, p) \<leftarrow> xml_do STR ''input'' (xml_take (xml_do STR ''llvm'' llvm_input_parser) xml_return);
      version \<leftarrow>? xml_text (STR ''cpfVersion'');
      proof \<leftarrow> xml_do STR ''proof'' (xml_take (xml_do STR ''llvmTerminationProof''  llvm_termination_proof_parser) xml_return);
      orig \<leftarrow>? xml_any;
     xml_return (fn, p, proof)
}"

definition llvm_seg_represents_cpf_parser where
  "llvm_seg_represents_cpf_parser =
     XMLdo STR ''certificationProblem'' {
     (fn, p) \<leftarrow> xml_do STR ''input'' (xml_take (xml_do STR ''llvm'' llvm_input_parser) xml_return);
      version \<leftarrow>? xml_text (STR ''cpfVersion'');
      seg \<leftarrow> xml_do STR ''proof'' (xml_take (xml_do STR ''llvmTerminationProof''  llvm_represents_seg_parser) xml_return);
      orig \<leftarrow>? xml_any;
     xml_return (fn, p, seg)
}"

definition llvm_lts_represents_cpf_parser where
  "llvm_lts_represents_cpf_parser =
     XMLdo STR ''certificationProblem'' {
     (fn, p) \<leftarrow> xml_do STR ''input'' (xml_take (xml_do STR ''llvm'' llvm_input_parser) xml_return);
      version \<leftarrow>? xml_text (STR ''cpfVersion'');
      (seg, renaming, lts) \<leftarrow> xml_do STR ''proof'' (xml_take (xml_do STR ''llvmTerminationProof''  llvm_represents_lts_parser) xml_return);
      orig \<leftarrow>? xml_any;
     xml_return (fn, p, seg, renaming, lts)
}"

definition "parse_llvm_cert_problem = parse_xmlfile llvm_termination_parser"

fun llvm_termination_checker where
  "llvm_termination_checker s = (case parse_xmlfile llvm_termination_parser (String.explode s)
    of Left s \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> showsl s) STR ''''
  | Right (fn, p, llvm_proof) \<Rightarrow>
     case llvm_check_termination p fn llvm_proof
        of Inl l \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> l) STR ''''
      | Inr r \<Rightarrow> STR ''CERTIFIED'')"

fun llvm_seg_represents_checker where
  "llvm_seg_represents_checker s = (case parse_xmlfile llvm_seg_represents_cpf_parser (String.explode s)
    of Left s \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> showsl s) STR ''''
  | Right (fn, p, seg) \<Rightarrow>
     case llvm_check_represents_seg p fn seg
        of Inl l \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> l) STR ''''
      | Inr r \<Rightarrow> STR ''CERTIFIED'')"

fun llvm_lts_represents_checker where
  "llvm_lts_represents_checker s = (case parse_xmlfile llvm_lts_represents_cpf_parser (String.explode s)
    of Left s \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> showsl s) STR ''''
  | Right (fn, p, seg, renaming, l) \<Rightarrow>
     case llvm_check_represents_lts p fn seg l renaming
        of Inl l \<Rightarrow> (showsl ''FAILED\<newline>Error message:\<newline>'' \<circ> l) STR ''''
      | Inr r \<Rightarrow> STR ''CERTIFIED'')"


end
