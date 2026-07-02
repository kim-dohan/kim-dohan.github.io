(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2016)
License: LGPL (see file COPYING.LESSER)
*)
theory CPF_Parser
  imports
    CPF_Proof_Parser
begin

definition certification_problem_parser :: "((lsymbol,string)input option \<times> 
  (lsymbol,string)property option \<times> (lsymbol,string) answer option \<times> (string,label_type,string)proof) xmlt"
where
  "certification_problem_parser = XMLdo (STR ''certificationProblem'') {
    version \<leftarrow> xml_text (STR ''cpfVersion'');
    (termIndexMap,ruleMap) \<leftarrow> lookupTables symbol_parser;
    inp \<leftarrow>? input_parser termIndexMap ruleMap;
    prop \<leftarrow>? property_parser;
    ans \<leftarrow>? answer_parser termIndexMap ruleMap;
    proof \<leftarrow> proof_parser termIndexMap ruleMap;
    meta_info \<leftarrow>? xml_any; 
    xml_return (inp, prop, ans, proof)
  }"

definition "parse_from_string xml_parser s = update_error (parse_xml_string (
    debug (showsl (STR ''0'')) (STR ''parsing xml'') xml_parser) s)
    String.implode"    

definition "parse_cert_problem = parse_from_string certification_problem_parser"

definition "parse_input inp = update_error (parse_from_string (input_parser Mapping.empty Mapping.empty) inp)
  (\<lambda> e. STR ''parse-input error: CeTA expects a CPF-'input' element\<newline>\<newline>'' + e)"

definition "parse_answer inp = 
  update_error (parse_from_string (answer_parser Mapping.empty Mapping.empty) inp)
  (\<lambda> e. STR ''parse-answer error: CeTA accepts YES, NO, WORST_CASE(?,O(n^k)) for some number k, or a CPF-'answer' element\<newline>\<newline>'' + e)"

definition "parse_property inp = 
  update_error (parse_from_string property_parser inp)
  (\<lambda> e. STR ''parse-property error: CeTA accepts SN, DC, RC, CR, INF, COM or a CPF-'property' element\<newline>\<newline>'' + e)"

definition parse_merge where "parse_merge e p op_maj op_min = (case op_maj of None \<Rightarrow> 
        (case op_min of None \<Rightarrow> error (STR ''no '' + e + STR '' has been provided'') | Some v \<Rightarrow> return v)
     | Some str \<Rightarrow> p str)" 

definition parse_combined_cert_problem where
  "parse_combined_cert_problem inp1 prop1 answ1 prfs = do {
      (inp2,prop2,answ2,prf) \<leftarrow> parse_cert_problem prfs;
      inp \<leftarrow> parse_merge (STR ''input'') parse_input inp1 inp2;
      prop \<leftarrow> parse_merge (STR ''property'') parse_property prop1 prop2;
      answ \<leftarrow> parse_merge (STR ''answer'') parse_answer answ1 answ2;
      return (inp, prop, answ, prf)
      }" 

end
