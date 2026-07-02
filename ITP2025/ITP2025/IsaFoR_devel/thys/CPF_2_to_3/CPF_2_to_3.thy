theory CPF_2_to_3
  imports
    Auxx.Xmlt2
    "HOL-Library.RBT_Mapping" 
    "HOL-Library.Code_Target_Numeral"
    Deriving.Compare_Order_Instances
begin

type_synonym ruleIndexInfo = "nat \<times> (string \<times> xml)list \<times> (xml, string)mapping \<times> (string,xml)mapping" 
type_synonym termIndexInfo = "nat \<times> (string \<times> xml)list \<times> (xml list, string)mapping" 

fun remove_arg :: "xml \<Rightarrow> xml" where
  "remove_arg (XML_text s) = (XML_text s)" 
| "remove_arg (XML tag as xs) = (let xs' = map remove_arg xs in
     if tag = ''arg'' then hd xs' else XML tag as xs')" 

abbreviation eq_string :: "string \<Rightarrow> String.literal \<Rightarrow> bool" (infix "=s" 50) where
  "(s =s l) \<equiv> (String.implode s = l)" 

abbreviation in_list :: "string \<Rightarrow> String.literal list \<Rightarrow> bool" (infix "\<in>s" 50) where
  "(s \<in>s l) \<equiv> (String.implode s \<in> set l)" 

definition "Xml x = XML (String.explode x)" 

fun term_indices_main :: "termIndexInfo \<Rightarrow> xml \<Rightarrow> xml \<times> termIndexInfo"
  and term_indices_main_list where
  "term_indices_main info (XML_text s) = (XML_text s,info)" 
| "term_indices_main info (XML tag atts xs) = (
      case term_indices_main_list info xs of 
       (xs', info') \<Rightarrow> let x = XML tag atts xs' in if tag =s STR ''funapp'' then
       case info' of (next,list,m) \<Rightarrow>
       case Mapping.lookup m xs' of 
         Some idx \<Rightarrow> (Xml (STR ''termIndex'') [] [XML_text (show idx)], info)
       | None \<Rightarrow> let s = show next in (Xml (STR ''termIndex'') [] [XML_text s], (Suc next, (s,x) # list, Mapping.update xs' s m)) 
    else (x, info'))" 
| "term_indices_main_list info [] = ([], info)" 
| "term_indices_main_list info (x # xs) = (case term_indices_main info x 
     of (x',info') \<Rightarrow> case term_indices_main_list info' xs 
     of (xs', info'') \<Rightarrow> (x' # xs', info''))" 

fun rule_indices_main :: "nat \<Rightarrow> ruleIndexInfo \<Rightarrow> xml \<Rightarrow> xml \<times> ruleIndexInfo"
  and rule_indices_main_list where
  "rule_indices_main i info (XML_text s) = (XML_text s,info)" 
| "rule_indices_main i info (XML tag atts xs) = (if tag =s STR ''rule'' \<and> i = 0 then
       (let x = XML tag atts xs in 
       case info of (next,list,(m,m')) \<Rightarrow>
       case Mapping.lookup m x of 
         Some idx \<Rightarrow> (Xml (STR ''ruleIndex'') [] [XML_text (show idx)], info)
       | None \<Rightarrow> let s = show next in (Xml (STR ''ruleIndex'') [] [XML_text s], (Suc next, (s,x) # list, Mapping.update x s m, Mapping.update s x m'))) 
     \<comment> \<open>do not replace rules in conditional setting ''probs'', prohibit 2 layers, i.e., rules/rule\<close>
    else let j = (if tag \<in>s [STR ''probs'', STR ''ctrsInput'',
           STR ''infeasibilityInput'', STR ''conditionalRewriteStep'',
           STR ''inlineConditions'', STR ''infeasibleRules'', STR ''unfeasibilityProof'',
            STR ''rightInlineConditions'', STR ''leftInlineConditions'', STR ''inlinedRules'', STR ''ifritRules''] 
          then 2 else i - 1) in
     \<comment> \<open>recurse\<close>
    case rule_indices_main_list j info xs of (xs', info') \<Rightarrow> (XML tag atts xs', info'))" 
| "rule_indices_main_list i info [] = ([], info)" 
| "rule_indices_main_list i info (x # xs) = (case rule_indices_main i info x 
     of (x',info') \<Rightarrow> case rule_indices_main_list i info' xs 
     of (xs', info'') \<Rightarrow> (x' # xs', info''))" 

definition rule_indices :: "xml \<Rightarrow> xml \<times> xml \<times> (string, xml) mapping" where 
  "rule_indices x = (case rule_indices_main 0 (1,[],Mapping.empty, Mapping.empty) x 
       of (x',(_,table,m,m')) \<Rightarrow> let
       tab = Xml (STR ''ruleTable'') [] (map (\<lambda> (i,r). 
            Xml (STR ''indexToRule'') [] [Xml (STR ''index'') [] [XML_text i], r]) (rev table))
      in (x',tab,m'))" 

definition term_indices :: "xml \<Rightarrow> xml \<times> xml" where 
  "term_indices x = (case term_indices_main (1,[],Mapping.empty) x 
       of (x',(_,table,m)) \<Rightarrow> let
       tab = Xml (STR ''termIndexTable'') [] (map (\<lambda> (i,r). 
            Xml (STR ''indexToTerm'') [] [Xml (STR ''index'') [] [XML_text i], r]) (rev table))
      in (x',tab))" 

definition xml_err where "xml_err s1 s2 = Code.abort (STR ''error at '' + String.implode s1 + STR '': '' + s2) (\<lambda> _. XML_text ''error'')" 

fun dps where "dps (XML DPs _ [XML rules _ p]) = p" 
fun trs where "trs (XML TRS _ [XML rules _ r]) = r"
  | "trs x = Code.abort (STR ''trs structure fail: '' + String.implode (shows_XML_indent [] 1 x [])) (\<lambda> _. [])" 

definition trs2' where "trs2' r s = (let S = trs s; sS = set S in filter (\<lambda> rule. rule \<notin> sS) r @ S)" 
definition trs2 where "trs2 r s = trs2' (trs r) s" 

definition xml_dps where "xml_dps p = Xml (STR ''dps'') [] [Xml (STR ''rules'') [] p]" 
definition xml_trs where "xml_trs p = Xml (STR ''trs'') [] [Xml (STR ''rules'') [] p]" 

fun deleted_dps where "deleted_dps c (XML DPs _ [XML rules _ p]) = XML DPs [] [XML rules [] (let remain = set p in filter (\<lambda>r. r \<notin> remain) c)]" 
fun deleted_trs where "deleted_trs c (XML TRS _ [XML rules _ r]) = XML TRS [] [XML rules [] (let remain = set r in filter (\<lambda>r. r \<notin> remain) c)]" 
fun deleted_trs2 where "deleted_trs2 c (XML TRS _ [XML rules _ r]) (XML TRS' _ [XML rules' _ r']) = 
  XML TRS [] [XML rules [] (let remain = set (r @ r') in filter (\<lambda>r. r \<notin> remain) c)]" 
fun remain_dps where "remain_dps c (XML DPs _ [XML rules _ pdel]) = (let del = set pdel in filter (\<lambda>r. r \<notin> del) c)"
fun remain_trs where "remain_trs c (XML TRS _ [XML rules _ del]) = (let del = set del in filter (\<lambda>r. r \<notin> del) c)"
fun replace_dps where "replace_dps xs x ys = (let xs' = filter (\<lambda> y. y \<noteq> x) xs
      in xs' @ filter (\<lambda> y. y \<notin> set xs') ys)" 
fun union_trs where "union_trs (XML TRS _ [XML rules _ r1]) (XML _ _ [XML _ _ r2]) = XML TRS [] [XML rules [] (r1 @ r2)]" 

fun trsInput where "trsInput (XML trsIn _ xs) = (let y = last xs in if Xml.tag y =s STR ''relativeRules'' then trs2 (hd xs) y else trs (hd xs))" 
fun reltrsInput where "reltrsInput (XML trsIn _ xs) = (let y = last xs in if Xml.tag y =s STR ''relativeRules'' then (trs (hd xs), trs y) else (trs (hd xs),[]))" 
fun comInput where "comInput (XML trsIn _ [_,r,s]) = (trs2 r s)" 

definition "sTrsTerminationProof = STR ''trsTerminationProof''"
definition "sRelativeTerminationProof = STR ''relativeTerminationProof''"
definition "sDpProof = STR ''dpProof''" 
definition "sDpNonterminationProof = STR ''dpNonterminationProof''" 
definition "sTrsNonterminationProof = STR ''trsNonterminationProof''" 
definition "sRelativeNonterminationProof = STR ''relativeNonterminationProof''"
definition "sCrProof = STR ''crProof''"
definition "sCrDisproof = STR ''crDisproof''"
definition "sComProof = STR ''comProof''"
definition "sComDisproof = STR ''comDisproof''" 
definition "sQuasiReductiveProof = STR ''quasiReductiveProof''" 
definition "sConditionalCrProof = STR ''conditionalCrProof''" 
definition "sCompletionProof = STR ''completionProof''"
definition "sEquationalProof = STR ''equationalProof''"
definition "sEquationalDisproof = STR ''equationalDisproof''"


context
  fixes ruleMap :: "(string, xml)mapping" 
begin

fun isEqualityRule :: "xml \<Rightarrow> bool" where
  "isEqualityRule (XML _ _ [XML_text ind]) = (case Mapping.lookup ruleMap ind of Some (XML _ _ [l,r]) \<Rightarrow> l = r)" 

function flip_deleted_dps :: "xml list \<Rightarrow> xml list \<Rightarrow> xml \<Rightarrow> xml" and flip_deleted_trs :: "xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_dps p r (XML dpprf _ children) = (if dpprf =s sDpProof then
       case children of [XML tag _ xs] \<Rightarrow> XML dpprf [] [
       if tag \<in>s [STR ''pIsEmpty'', STR ''sizeChangeProc''] then XML tag [] xs
       else if tag =s STR ''depGraphProc'' then XML tag [] (map (\<lambda> comp. case comp of XML c _ tuple \<Rightarrow> case rev tuple of l # ls \<Rightarrow> 
         XML c [] (rev ((if Xml.tag l =s sDpProof then flip_deleted_dps (dps (hd tuple)) r l else l) # ls))) xs)
       else if tag =s STR ''monoRedPairProc'' 
        then (case xs of 
            [x1,p',r',prf] \<Rightarrow> XML tag [] [x1,deleted_dps p p',deleted_trs r r', flip_deleted_dps (dps p') (trs r') prf])
       else if tag =s STR ''monoRedPairUrProc'' 
        then (case xs of 
           [x1,p',r',ur,prf] \<Rightarrow> XML tag [] [x1,deleted_dps p p',deleted_trs (trs ur) r', ur, flip_deleted_dps (dps p') (trs r') prf])
       else if tag \<in>s [STR ''redPairProc'', STR ''redPairUrProc''] 
        then (case xs of 
            [x1,p',prf] \<Rightarrow> XML tag [] [x1,deleted_dps p p', flip_deleted_dps (dps p') r prf]
          | [x1,p',x2,prf] \<Rightarrow> XML tag [] [x1,deleted_dps p p',x2, flip_deleted_dps (dps p') r prf])
       else if tag =s  STR ''subtermProc'' then (case rev xs of (prf # p' # ys) 
          \<Rightarrow> if Xml.tag (hd xs) =s STR ''argumentFilter'' then 
              XML tag [] (rev (flip_deleted_dps (dps p') r prf # deleted_dps p p' # ys))
             else XML tag [] (rev (flip_deleted_dps (remain_dps p p') r prf # p' # ys)))
       else if tag =s STR ''innermostMonoRedPairProc'' then (case xs of [x1,XML del _ [p',r'],prf] 
          \<Rightarrow> XML tag [] [x1,p',r', flip_deleted_dps (remain_dps p p') (remain_trs r r') prf])
       else if tag \<in>s [STR ''flatContextClosureProc'', STR ''uncurryProc''] then (case xs of 
         [x1,x2,p',r',prf] \<Rightarrow> XML tag [] [x1,x2,p',r',flip_deleted_dps (dps p') (trs r') prf]
       | [x2,p',r',prf] \<Rightarrow> XML tag [] [x2,p',r',flip_deleted_dps (dps p') (trs r') prf])
       else if tag \<in>s [STR ''semlabProc'', STR ''argumentFilterProc''] then (case xs of 
         [x1,p',r',x2,prf] \<Rightarrow> XML tag [] [x1,p',r',x2,flip_deleted_dps (dps p') (trs r') prf]
       | [x1,p',r',prf] \<Rightarrow> XML tag [] [x1,p',r',flip_deleted_dps (dps p') (trs r') prf])
       else if tag =s STR ''generalRedPairProc'' then (case xs of 
         [x1,p',p'',x2,prf] \<Rightarrow> XML tag [] [x1,p',p'',x2,flip_deleted_dps (let del1 = set (dps p'); del2 = set (dps p'') in filter (\<lambda> r. \<not> (r \<in> del1 \<and> r \<in> del2)) p) r prf]
       | [x1,p',p'',x2,prf,prf'] \<Rightarrow> XML tag [] [x1,p',p'',x2,flip_deleted_dps (remain_dps p p') r prf, flip_deleted_dps (remain_dps p p'') r prf'])
       else if tag =s  STR ''splitProc'' then (case xs of 
         [p',r',prf,prf'] \<Rightarrow> XML tag [] [p',r',flip_deleted_dps p r prf, flip_deleted_dps (remain_dps p p') (remain_trs r r') prf'])
       else if tag =s STR ''narrowingProc'' then (case xs of
         [rule,x1,p',prf] \<Rightarrow> XML tag [] [rule,x1,p',flip_deleted_dps (replace_dps p rule (dps p')) r prf])
       else if tag \<in>s [STR ''instantiationProc'', STR ''forwardInstantiationProc''] then (case xs of
          [rule,p',prf] \<Rightarrow> XML tag [] [rule,p',flip_deleted_dps (replace_dps p rule (dps p')) r prf]
        | [rule,p',x1,prf] \<Rightarrow> XML tag [] [rule,p',x1,flip_deleted_dps (replace_dps p rule (dps p')) r prf])
       else if tag =s STR ''complexConstantRemovalProc'' then (case xs of
         [x1,rm,prf] \<Rightarrow> XML tag [] [x1,rm, flip_deleted_dps (map (\<lambda> rme. case rme of (XML _ _ [_,r]) \<Rightarrow> r) (Xml.children rm)) r prf])
       else if tag =s STR ''rewritingProc'' then (case xs of
         [rule,x1,rule',x2,prf] \<Rightarrow> XML tag [] [rule,x1,rule',x2, flip_deleted_dps (replace_dps p rule [rule']) r prf])
       else if tag \<in>s [STR ''usableRulesProc'', STR ''innermostLhssRemovalProc'', STR ''switchInnermostProc''] then (case xs of 
         [x1,prf] \<Rightarrow> XML tag [] [x1,flip_deleted_dps p r prf])
       else if tag =s STR ''switchToTRS'' then case xs of [prf] \<Rightarrow> XML tag [] [flip_deleted_trs (p @ r) prf]
       else xml_err tag (STR ''flip_dps unknown tag'')]
      else xml_err dpprf (STR '' is not dpProof''))" 
| "flip_deleted_dps p r (XML_text _) = xml_err ''text'' (STR ''flip_dps: hit text'')" 
| "flip_deleted_trs r (XML trsprf _ children) = (if trsprf \<in>s [sTrsTerminationProof, sRelativeTerminationProof] then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''rIsEmpty'', STR ''rightGroundTermination'', STR ''bounds''] then XML tag [] xs
       else if tag =s STR ''ruleRemoval''
        then (case xs of 
            [x1,r',prf] \<Rightarrow> XML tag [] [x1,deleted_trs r r', flip_deleted_trs (trs r') prf]
           | [x1,r',s',prf] \<Rightarrow> XML tag [] [x1,deleted_trs2 r r' s', flip_deleted_trs (trs2 r' s') prf])
       else if tag =s STR ''dpTrans'' then case xs of [p,x1,prf] \<Rightarrow> XML tag [] [p,x1,flip_deleted_dps (dps p) r prf]
       else if tag =s STR ''semlab'' then (case xs of 
         [x1,r',s',prf] \<Rightarrow> XML tag [] [x1,union_trs r' s',flip_deleted_trs (trs2 r' s') prf]
       | [x1,r',prf] \<Rightarrow> XML tag [] [x1,r',flip_deleted_trs (trs r') prf])
       else if tag =s STR ''split'' then (case xs of 
         [r',prf,prf'] \<Rightarrow> XML tag [] [r',flip_deleted_trs r prf, flip_deleted_trs (remain_trs r r') prf'])
       else if tag =s STR ''uncurry'' then (case xs of
         [x1,r',s',prf] \<Rightarrow> XML tag [] [x1,union_trs r' s',flip_deleted_trs (trs2 r' s') prf]
       | [x1,r',prf] \<Rightarrow> XML tag [] [x1,r',flip_deleted_trs (trs r') prf])
       else if tag =s STR ''stringReversal'' then (case xs of
         [r',s',prf] \<Rightarrow> XML tag [] [union_trs r' s',flip_deleted_trs (trs2 r' s') prf]
       | [r',prf] \<Rightarrow> XML tag [] [r',flip_deleted_trs (trs r') prf])
       else if tag =s STR ''removeNonApplicableRules'' then (case xs of
         [r',prf] \<Rightarrow> XML tag [] [r',flip_deleted_trs (remain_trs r r') prf])
       else if tag =s STR ''flatContextClosure'' then (case xs of
         [x1,r',s',prf] \<Rightarrow> XML tag [] [x1,union_trs r' s',flip_deleted_trs (trs2 r' s') prf]
       | [x1,r',prf] \<Rightarrow> XML tag [] [x1,r',flip_deleted_trs (trs r') prf])
       else if tag =s STR ''constantToUnary'' then (case xs of
         [x1,x2,r',s',prf] \<Rightarrow> XML tag [] [x1,x2,union_trs r' s',flip_deleted_trs (trs2 r' s') prf]
       | [x1,x2,r',prf] \<Rightarrow> XML tag [] [x1,x2,r',flip_deleted_trs (trs r') prf])
       else if tag =s STR ''equalityRemoval'' then (case xs of 
         [prf] \<Rightarrow> XML tag [] [flip_deleted_trs (filter (\<lambda> rule. \<not> isEqualityRule rule) r) prf])
       else if tag =s STR ''switchInnermost'' then (case xs of
         [x1,prf] \<Rightarrow> XML tag [] [x1,flip_deleted_trs r prf])
       else if tag =s STR ''sIsEmpty'' then (case xs of
         [prf] \<Rightarrow> XML tag [] [flip_deleted_trs r prf])
       else xml_err tag (STR ''flip_trs unknown or unsupported tag'')]
      else xml_err trsprf (STR '' is not trs or relative termination proof''))" 
| "flip_deleted_trs r (XML_text _) = xml_err ''text'' (STR ''flip_trs: hit text'')"
  by pat_completeness auto

termination by (relation "measure (\<lambda> x. case x of Inl (_,_,y) \<Rightarrow> size y | Inr (_,y) \<Rightarrow> size y)")
    (auto simp: termination_simp)

fun flip_deleted_cr :: "xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_cr r (XML trsprf _ children) = (if trsprf \<in>s [sCrProof,sCrDisproof,sComProof,sComDisproof] then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''orthogonal'', 
         STR ''stronglyClosed'', 
         STR ''pcpClosed'', 
         STR ''ruleLabeling'',
         STR ''developmentClosed'', 
         STR ''modularityDisjoint'',
         STR ''nonJoinableFork'',
         STR ''pcpRuleLabeling'', 
         STR ''parallelClosed''] then XML tag [] xs
       else if tag \<in>s [STR ''wcrAndSN'', STR ''nonWcrAndSN'']
        then (case xs of [x1,prf] \<Rightarrow> XML tag [] [x1,flip_deleted_trs r prf])
       else if tag =s STR ''compositionalPcpRuleLabeling'' then case rev xs of
           prf # r' # r2 # ys \<Rightarrow> XML tag [] (rev (flip_deleted_cr 
             (if Xml.tag r2 =s STR ''trs'' then trs2 r' r2 else trs r') prf # r' # r2 # ys))
       else if tag \<in>s [STR ''swapTRSs'', STR ''switchToCrProof''] then (case xs of 
         [prf] \<Rightarrow> XML tag [] [flip_deleted_cr r prf])
       else if tag =s STR ''compositionalPcp'' then (case xs of 
         [c,x1,prf] \<Rightarrow> XML tag [] [c,x1,flip_deleted_cr (trs c) prf])
       else if tag =s STR ''compositionalPcps'' then (case xs of 
         [c,p,x1,x2,prf,prf'] \<Rightarrow> XML tag [] [c,p,x1,x2,flip_deleted_trs (trs2' r p) prf, flip_deleted_cr (trs c) prf']
       | [c,d,p,x1,x2,x3,x4,prf,prf'] \<Rightarrow> XML tag [] [c,d,p,x1,x2,x3,x4,flip_deleted_trs (trs2' r p) prf, flip_deleted_cr (trs2 c d) prf'])
       else if tag =s STR ''criticalPairClosingSystem'' then (case xs of 
         [r',prf,x1] \<Rightarrow> XML tag [] [r', flip_deleted_trs (trs r') prf, x1])
       else if tag =s STR ''decreasingDiagrams'' then (case xs of 
         [prf,x1] \<Rightarrow> XML tag [] [flip_deleted_trs r prf, x1]
         | [x1] \<Rightarrow> XML tag [] [x1])
       else if tag =s STR ''redundantRules'' then (case rev xs of 
         prf # ys \<Rightarrow> XML tag [] (rev (flip_deleted_cr (trs (hd xs)) prf # ys)))
       else if tag =s STR ''persistentDecomposition'' then (case xs of 
         x1 # ys \<Rightarrow> XML tag [] (x1 # map (\<lambda> y. case y of XML com _ [r',prf] \<Rightarrow> XML com [] [r', flip_deleted_cr (trs r') prf]) ys))
       else xml_err tag (STR ''flip_cr unknown or unsupported tag'')]
      else xml_err trsprf (STR '' is not cr or com proof''))" 
| "flip_deleted_cr r (XML_text _) = xml_err ''text'' (STR ''flip_cr: hit text'')"

fun flip_deleted_cond :: "xml \<Rightarrow> xml" where
  "flip_deleted_cond (XML cprf _ children) = (if cprf =s sQuasiReductiveProof then
       case children of [XML unrav _ [info,prf]] \<Rightarrow> XML cprf [] [
           XML unrav [] [info,flip_deleted_trs (List.maps (\<lambda> entry. case entry of XML _ _ (_ # rs) \<Rightarrow> rs) (Xml.children info)) prf]
        ] else xml_err cprf (STR '' in not conditional termination proof''))" 

fun flip_deleted_ccr :: "xml \<Rightarrow> xml" where
  "flip_deleted_ccr (XML trsprf _ children) = (if trsprf =s sConditionalCrProof then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''almostOrthogonal'', STR ''almostOrthogonalModuloInfeasibility''] then XML tag [] xs
       else if tag =s STR ''inlineConditions''
        then (case xs of [x1,x2,prf] \<Rightarrow> XML tag [] [x1,x2,flip_deleted_ccr prf])
       else if tag =s STR ''al94'' then case xs of
           (prf # ys) \<Rightarrow> XML tag [] (flip_deleted_cond prf # ys)
       else if tag =s STR ''unconditional'' then case xs of
           [prf] \<Rightarrow> XML tag [] [flip_deleted_cr (Code.abort (STR ''trs below unconditional'') (\<lambda> _. [])) prf]
       else if tag =s STR ''unraveling'' then (case xs of 
         [info,prf] \<Rightarrow> XML tag [] [info,flip_deleted_cr (List.maps (\<lambda> entry. case entry of XML _ _ (_ # rs) \<Rightarrow> rs) (Xml.children info)) prf])
       else if tag =s STR ''infeasibleRuleRemoval'' then (case xs of 
         [r',prf] \<Rightarrow> XML tag [] [r',flip_deleted_ccr prf])
       else xml_err tag (STR ''flip_cr unknown or unsupported tag'')]
      else xml_err trsprf (STR '' is not conditional cr proof''))" 
| "flip_deleted_ccr (XML_text _) = xml_err ''text'' (STR ''flip_conditional_cr: hit text'')"

fun flip_deleted_compl :: "xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_compl r (XML cprf _ children) = (if cprf =s sCompletionProof then
       case children of [x1,prf,x2] \<Rightarrow> XML cprf [] [x1,flip_deleted_trs r prf, x2]
      else xml_err cprf (STR '' is not completion proof''))" 
| "flip_deleted_compl r (XML_text _) = xml_err ''text'' (STR ''flip_completion: hit text'')"

fun flip_deleted_eq :: "xml \<Rightarrow> xml" where
  "flip_deleted_eq (XML trsprf _ children) = (if trsprf \<in>s [sEquationalProof, sEquationalDisproof] then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''equationalProofTree'', STR ''convertibleInstance'', STR ''conversion'', STR ''subsumptionProof''] then XML tag [] xs
       else if tag =s STR ''completionAndNormalization''
        then (case xs of [r,prf] \<Rightarrow> XML tag [] [r,flip_deleted_compl (trs r) prf])
       else xml_err tag (STR ''flip_eq unknown or unsupported tag'')]
      else xml_err trsprf (STR '' is not equational (dis) proof''))" 
| "flip_deleted_eq (XML_text _) = xml_err ''text'' (STR ''flip_conditional_eq: hit text'')"

function flip_deleted_dps_nt :: "xml list \<Rightarrow> xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_dps_nt p r (XML dpprf _ children) = (if dpprf =s sDpNonterminationProof then
       case children of [XML tag _ xs] \<Rightarrow> XML dpprf [] [
       if tag \<in>s [STR ''loop'', STR ''nonLoop''] then XML tag [] xs
       else if tag =s STR ''dpRuleRemoval'' then (case xs of 
         x1 # xs1 \<Rightarrow> case (if Xml.tag x1 =s STR ''dps'' then (x1,xs1) else (xml_dps p, x1 # xs1)) of
         (p', x2 # xs2) \<Rightarrow> case (if Xml.tag x2 =s STR ''trs'' then (x2,xs2) else (xml_trs r, x2 # xs2)) of
         (r', [prf]) \<Rightarrow> XML tag [] [deleted_dps p p',deleted_trs r r',flip_deleted_dps_nt (dps p') (trs r') prf])
       else if tag \<in>s [STR ''innermostLhssRemovalProc'', STR ''innermostLhssIncreaseProc'', STR ''switchFullStrategyProc'']  
        then (case xs of 
            [x1,prf] \<Rightarrow> XML tag [] [x1,flip_deleted_dps_nt p r prf])
       else if tag =s STR ''narrowingProc'' then (case xs of
         [rule,x1,p',prf] \<Rightarrow> XML tag [] [rule,x1,p',flip_deleted_dps_nt (replace_dps p rule (dps p')) r prf])
       else if tag =s STR ''instantiationProc'' then (case xs of
          [p',prf] \<Rightarrow> XML tag [] [p',flip_deleted_dps_nt (dps p') r prf])
       else if tag =s STR ''rewritingProc'' then (case xs of
         [rule,x1,rule',x2,prf] \<Rightarrow> XML tag [] [rule,x1,rule',x2, flip_deleted_dps_nt (replace_dps p rule [rule']) r prf])
       else xml_err tag (STR ''flip_dps_nt unknown tag'')]
      else xml_err dpprf (STR '' is not dpNonterminationProof''))" 
| "flip_deleted_dps_nt p r (XML_text _) = xml_err ''text'' (STR ''flip_dps_nt: hit text'')" 
  by pat_completeness auto

termination by (relation "measure (\<lambda> (_,_,x). size x)", auto split: if_splits)

fun flip_deleted_trs_nt :: "xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_trs_nt r (XML trsprf _ children) = (if trsprf =s sTrsNonterminationProof then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''rightGroundNontermination'', STR ''variableConditionViolated'', STR ''loop'',
          STR ''nonLoop'', STR ''nonterminatingSRS'', STR ''notWNTreeAutomaton''] 
          then XML tag [] xs
       else if tag =s STR ''ruleRemoval'' then (case xs of 
         [r', prf] \<Rightarrow> XML tag [] [deleted_trs r r',flip_deleted_trs_nt (trs r') prf])
       else if tag  \<in>s [ STR ''innermostLhssIncrease'', STR ''switchFullStrategy''] then (case xs of 
         [x1, prf] \<Rightarrow> XML tag [] [x1,flip_deleted_trs_nt r prf])
       else if tag =s STR ''constantToUnary'' then (case xs of 
         [x1,x2,r', prf] \<Rightarrow> XML tag [] [x1,x2,r',flip_deleted_trs_nt (trs r') prf])
       else if tag =s STR ''stringReversal'' then (case xs of 
         [r', prf] \<Rightarrow> XML tag [] [r',flip_deleted_trs_nt (trs r') prf])
       else if tag =s STR ''dpTrans'' then (case xs of 
         [p', x1, prf] \<Rightarrow> XML tag [] [p',x1, flip_deleted_dps_nt (dps p') r prf])
       else if tag =s STR ''uncurry'' then (case xs of
         [x1,r',prf] \<Rightarrow> XML tag [] [x1,r',flip_deleted_trs_nt (trs r') prf])
       else xml_err tag (STR ''flip_dps_nt unknown tag'')]
      else xml_err trsprf (STR '' is not trsNonterminationProof''))" 
| "flip_deleted_trs_nt r (XML_text _) = xml_err ''text'' (STR ''flip_trs_nt: hit text'')" 

fun flip_deleted_reltrs_nt :: "xml list \<Rightarrow> xml list \<Rightarrow> xml \<Rightarrow> xml" where
  "flip_deleted_reltrs_nt r s (XML trsprf _ children) = (if trsprf =s sRelativeNonterminationProof then
       case children of [XML tag _ xs] \<Rightarrow> XML trsprf [] [
       if tag \<in>s [STR ''variableConditionViolated'', STR ''loop''] 
          then XML tag [] xs
       else if tag =s STR ''ruleRemoval'' then (case xs of 
         [r', s', prf] \<Rightarrow> XML tag [] [deleted_trs r r', deleted_trs s s', flip_deleted_reltrs_nt (trs r') (trs s') prf])
       else if tag =s STR ''stringReversal'' then (case xs of 
         [r', s', prf] \<Rightarrow> XML tag [] [r',s', flip_deleted_reltrs_nt (trs r') (trs s') prf])
       else if tag =s STR ''trsNonterminationProof'' then 
           flip_deleted_trs_nt r (hd children)
       else xml_err tag (STR ''flip_dps_nt unknown tag'')]
      else xml_err trsprf (STR '' is not relativeNonterminationProof''))" 
| "flip_deleted_reltrs_nt r s (XML_text _) = xml_err ''text'' (STR ''flip_reltrs_nt: hit text'')" 


fun flip_deletion :: "xml \<Rightarrow> xml" where
 "flip_deletion (XML cp as [XML input _ [inp], vers, XML proof _ [prf], orig]) = (XML cp as 
     [XML input [] [inp], vers,
     XML proof [] [
        if Xml.tag prf =s sDpProof then case inp of XML dpInput _ (r # p # _) \<Rightarrow> flip_deleted_dps (dps p) (trs r) prf
        else if Xml.tag prf \<in>s [sTrsTerminationProof, sRelativeTerminationProof] then flip_deleted_trs (trsInput inp) prf
        else if Xml.tag prf \<in>s [sCrProof, sCrDisproof] then flip_deleted_cr (trsInput inp) prf
        else if Xml.tag prf \<in>s [sComProof, sComDisproof] then flip_deleted_cr (comInput inp) prf
        else if Xml.tag prf =s sQuasiReductiveProof then flip_deleted_cond prf
        else if Xml.tag prf =s sConditionalCrProof then flip_deleted_ccr prf
        else if Xml.tag prf =s sCompletionProof then case inp of XML cInp _ [e,r] \<Rightarrow> flip_deleted_compl (trs r) prf
        else if Xml.tag prf \<in>s [sEquationalProof,sEquationalDisproof] then flip_deleted_eq prf
        else if Xml.tag prf =s sDpNonterminationProof then case inp of XML dpInput _ (r # p # _) \<Rightarrow> flip_deleted_dps_nt (dps p) (trs r) prf
        else if Xml.tag prf =s sTrsNonterminationProof then flip_deleted_trs_nt (trsInput inp) prf
        else if Xml.tag prf =s sRelativeNonterminationProof then case reltrsInput inp of (r,s) \<Rightarrow> flip_deleted_reltrs_nt r s prf
        else prf
      ], orig])" 
end

definition "xml_to_final_string x = String.implode (filter ((\<noteq>) (CHR ''\<newline>'')) (shows_XML_indent [] 0 x []))" 

definition term_index_optional :: "bool \<Rightarrow> xml \<Rightarrow> xml \<times> xml list" where 
  "term_index_optional use x = (if use then case term_indices x of (x',tiTable) \<Rightarrow> (x',[tiTable])
     else (x,[]))" 

fun signature :: "xml set \<Rightarrow> xml list \<Rightarrow> xml list" where
  "signature s (XML tag as xs # ys) = (if tag =s STR ''funapp'' 
    then case xs of f # xs' \<Rightarrow> let rest = xs' @ ys in if f \<in> s then signature s rest else 
       Xml (STR ''symbol'') [] [f, Xml (STR ''arity'') [] [XML_text (show (length xs'))]] # signature (insert f s) rest
    else signature s (xs @ ys))" 
| "signature s (_ # ys) = signature s ys" 
| "signature s [] = []" 

definition signature_optional :: "xml \<Rightarrow> xml list" where
  "signature_optional x = (case x of XML cp as (XML input _ [inp] # _) \<Rightarrow>
     if Xml.tag inp =s STR ''trsInput'' then let rls = trsInput inp in [Xml (STR ''signature'') [] (signature {} rls)] 
     else []
   | XML cp as foo \<Rightarrow> Code.abort (STR ''sigopt: '' + String.implode cp) (\<lambda> _. []))" 

definition cpf_2_to_3_phase_1 :: "bool \<Rightarrow> String.literal \<Rightarrow> String.literal" where
  "cpf_2_to_3_phase_1 ti s = (case doc_of_string (String.explode s) of 
      Inl err \<Rightarrow> Code.abort (String.implode err) (\<lambda> _. s)  
    | Inr (XMLDOC _ x) \<Rightarrow> let x1 = remove_arg x in 
       case term_index_optional ti x1 of
       (x', tiTableOpt) \<Rightarrow> case rule_indices x' of
       (y, riTable, m) \<Rightarrow> case flip_deletion m y 
       of XML tag atts xs \<Rightarrow> xml_to_final_string (XML tag atts (Xml (STR ''lookupTables'') [] (tiTableOpt @ [riTable] @ signature_optional x1) # xs)))" 

derive compare_order xml

(* use maps as sets *)
definition Setm :: "('a,unit)mapping \<Rightarrow> 'a set" where
  [simp]: "Setm = Mapping.keys" 

declare [[code drop:  
  Set.insert
  Set.member
  Set.union
  Set.filter
  Set.empty 
  Set.image
  Set.is_empty
  List.set
  Set.minus_set_inst.minus_set
  ]]

code_datatype Setm
lemma empty[code]: "{} = Setm Mapping.empty" by auto
lemma insert[code]: "insert x (Setm m) = Setm (Mapping.update x () m)" by auto
lemma member[code]: "x \<in> Setm m \<longleftrightarrow> (case Mapping.lookup m x of None \<Rightarrow> False | Some _ \<Rightarrow> True)" 
  by (auto split: option.splits) (transfer, auto)+
lemma set[code]: "set xs = Setm (Mapping.tabulate xs (\<lambda> _. ()))" 
  by auto

export_code cpf_2_to_3_phase_1 in Haskell module_name CPF_2_to_3 

end
