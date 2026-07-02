(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2015)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Unraveling_Impl
imports
  Unraveling
  Conditional_Rewriting_Impl
  Framework.QDP_Framework_Impl
  Show.Shows_Literal
begin

definition create_ctxts :: "('f, 'v) rules \<Rightarrow> (nat \<Rightarrow> ('f, 'v) ctxt) option"
where
  "create_ctxts R =
    (case R of
      [] \<Rightarrow> None
    | Cons l RR \<Rightarrow> do {
      cs \<leftarrow> Option_Monad.mapM (\<lambda>(l, r).
        (case l of
          Fun U (t # ts) \<Rightarrow> Some (More U [] \<box> ts)
        | _ \<Rightarrow> None)) RR;
      let n = length cs;
      Some (\<lambda>i. if i < length cs then cs ! i else \<box>) })"

definition
  create_U ::
    "(('f, 'v) crule \<times> ('f, 'v) rules) list \<Rightarrow> (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt) option"
where
  "create_U c_rs = do {
    cr_ctxts \<leftarrow> Option_Monad.mapM (\<lambda> (cr, rs). do {
      guard (length rs = Suc (length (snd cr)));
      ctxt \<leftarrow> create_ctxts rs;
      Some (cr, ctxt)
    }) c_rs;
    let m = map_of cr_ctxts;
    Some (\<lambda> cr. case m cr of None \<Rightarrow> (\<lambda> _. \<box>) | Some ctxt \<Rightarrow> ctxt)
  }"

declare unraveling.lhs_n.simps[code] unraveling.rhs_n.simps[code]

definition
  rules_impl :: "(('f, 'v) crule \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt) \<Rightarrow> ('f, 'v) crule \<Rightarrow> ('f, 'v) rules"
where
  "rules_impl U cr = map (\<lambda>i.
    (unraveling.lhs_n U cr i, unraveling.rhs_n U cr i)) [0 ..< Suc (length (snd cr))]"

lemma rules_impl[simp]: "set (rules_impl U cr) = unraveling.rules U cr"
proof -
  interpret unraveling "{}" U .
  obtain n where n: "Suc (length (snd cr)) = n" by auto
  have "{0..<Suc (length (snd cr))} = {i. i < Suc (length (snd cr))}" (is "?l = _")
    unfolding n by auto
  also have "... = {i. i \<le> length (snd cr)}" (is "_ = ?r") by auto
  finally have id: "?l = ?r" .
  show ?thesis unfolding rules_def rules_impl_def 
    by (simp del: upt_Suc add: id)
qed

definition check_unraveling :: "(('f :: showl,'v :: showl)crule \<times> ('f,'v)rules)list \<Rightarrow> ('f,'v)crules \<Rightarrow> ('f,'v)rules result"
  where "check_unraveling c_rs ctrs \<equiv> do {
      check_subseteq ctrs (map fst c_rs) <+? 
        (\<lambda> cr. showsl_lit (STR ''did not find rule '') \<circ> showsl_crule cr \<circ> showsl_nl);
      U \<leftarrow> case create_U c_rs of None \<Rightarrow> error (showsl_lit (STR ''unable to extract unraveling contexts'')) | Some U \<Rightarrow> return U;
      check_allm (\<lambda> (c,rs). check (rules_impl U c = rs) (showsl_lit (STR ''problem with rules of '') \<circ> showsl_crule c \<circ> showsl_nl)) c_rs;
      return (concat (map snd c_rs))
   } <+? (\<lambda> e. showsl_lit (STR ''problem in unraveling\<newline>'') \<circ> e)"

lemma check_unraveling:
  assumes ok: "check_unraveling c_rs ctrs = return r"
    and SN: "SN (rstep (set r))"
  shows "quasi_reductive (set ctrs)"
proof - 
  note ok = ok[unfolded check_unraveling_def, simplified]
  from ok obtain U where U: "create_U c_rs = Some U" by (cases "create_U c_rs", auto)
  note ok = ok[unfolded U, simplified]
  from ok have r: "r = concat (map snd c_rs)" by simp
  interpret unraveling "set ctrs" U .
  show ?thesis
  proof (rule SN_quasi_reductive, rule SN_subset[OF SN rstep_mono])
    show "UR \<subseteq> set r" 
    proof(rule subsetI)
      fix lr
      assume lr: "lr \<in> UR"
      from this[unfolded UR_def] obtain cr where cr: "cr \<in> set ctrs"
      and lr: "lr \<in> rules cr" by auto
      from ok cr obtain rs where mem: "(cr,rs) \<in> set c_rs" by auto
      from ok mem have "rules_impl U cr = rs" by auto
      from arg_cong[OF this, of set] have "rules cr = set rs" by simp
      with lr have lr: "lr \<in> set rs" by auto
      with mem show "lr \<in> set r" unfolding r by force
    qed
  qed
qed     
 

definition check_Z_vars :: "('f :: showl,'v :: showl) crules \<Rightarrow>  (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> showsl check"
where
  "check_Z_vars crs Z = do {
    check_allm 
     (\<lambda>cr .
      check_allm
       (\<lambda>i. do {
        check_subseteq (list_inter (X_impl cr i) (Y_impl cr i)) (Z cr i) 
         <+? (\<lambda>x. showsl_lit (STR ''Variable '') \<circ> showsl x \<circ> showsl_lit (STR '' does not occur in variable list of '')
            \<circ> showsl (Suc i) \<circ> showsl_lit (STR ''. U-symbol\<newline>''));
        check (distinct (Z cr i)) 
           (showsl_lit (STR '' variables in additional arguments of U-symbols are not distinct.\<newline>''))
        } <+? (\<lambda>e. showsl_lit (STR ''conditions for variable-lists in U-symbols for '') \<circ> showsl_crule cr 
              \<circ> showsl_lit (STR '' are violated.\<newline>'') \<circ> e)
       ) [0..<length (snd cr)]
     ) crs 
  } <+? (\<lambda>e. showsl_lit (STR ''The CTRS does not fulfill the condition on Z variables.\<newline>'') \<circ> e)"

lemma check_Z_vars[simp]: 
  "isOK (check_Z_vars c_rs Z) = unraveling.Z_vars (set c_rs) Z"
by (simp add: check_Z_vars_def unraveling.Z_vars_def Y_impl atLeast0LessThan) (blast)

definition create_zs :: "('f, 'v) rules \<Rightarrow>  (nat \<Rightarrow> 'v list) option"
where
  "create_zs R =
    (case R of
      [] \<Rightarrow> None
    | Cons l RR \<Rightarrow> do {
      cs \<leftarrow> Option_Monad.mapM (\<lambda>(l, r).
        (case l of
          Fun U (t # ts) \<Rightarrow> Some (map the_Var ts)
        | _ \<Rightarrow> None)) RR;
      Some (\<lambda>i. if i < length cs then (cs ! i) else [])})"

definition create_Z :: "(('f, 'v) crule \<times> ('f, 'v) rules) list \<Rightarrow> (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list) option"
where "create_Z c_rs = do {
    cr_zs \<leftarrow> Option_Monad.mapM (\<lambda> (cr, rs). do {
      zs \<leftarrow> create_zs rs;
      Some (cr, zs)
    }) c_rs;
    let mc = map_of cr_zs;
    Some (\<lambda> cr. case mc cr of None \<Rightarrow> (\<lambda> _. []) | Some zs \<Rightarrow> zs)
  }"

definition create_Umap_cr :: "('f, 'v) crule \<Rightarrow> ('f, 'v) rules \<Rightarrow> (('f \<times> (('f, 'v) crule \<times> nat)) list) option"
where "create_Umap_cr cr R = (case R of 
       [] \<Rightarrow> None
     | Cons l RR \<Rightarrow> Option_Monad.mapM (\<lambda>((l, r), i).
        (case l of Fun U (t # ts) \<Rightarrow> Some (U,(cr,i)) | _ \<Rightarrow> None)) (zip RR [0..<length RR])) "

definition create_Umap :: "(('f, 'v) crule \<times> ('f, 'v) rules) list \<Rightarrow> ('f \<Rightarrow> (('f, 'v) crule \<times> nat) option)"
where "create_Umap c_rs = ( case Option_Monad.mapM (\<lambda> (cr, rs). create_Umap_cr cr rs) c_rs of 
 None \<Rightarrow> (\<lambda> _ .None) | Some u \<Rightarrow> map_of (concat u))"

abbreviation si :: "('f,'v) crule \<Rightarrow> nat =>  ('f,'v) term" where "si \<rho> i \<equiv> fst ((snd \<rho>)!i)"
abbreviation ti :: "('f,'v) crule \<Rightarrow> nat =>  ('f,'v) term" where "ti \<rho> i \<equiv> snd ((snd \<rho>)!i)"

definition check_prefix_equivalent :: "('f::showl, 'v::showl) crule \<Rightarrow> ('f, 'v) crule \<Rightarrow> nat \<Rightarrow> showsl check" where 
  "check_prefix_equivalent \<rho> \<rho>' n = do {
     check (n < length (snd \<rho>)) 
      (showsl_lit (STR ''There are fewer than '') \<circ> showsl n \<circ> showsl_lit (STR '' conditions in '') \<circ> showsl_crule \<rho>);
     check (n < length (snd \<rho>')) 
      (showsl_lit (STR ''There are fewer than '') \<circ> showsl n \<circ> showsl_lit (STR '' conditions in '') \<circ> showsl_crule \<rho>');
     check (fst (fst \<rho>) = fst (fst \<rho>')) (showsl_lit (STR ''Left-hand sides are different.''));
     check_allm
        (\<lambda>i. check (ti \<rho> i = ti \<rho>' i) (showsl_lit (STR ''Rhs of conditions are different\<newline>''))) 
          [0..<n];
     check_allm
        (\<lambda>i. check (si \<rho> i = si \<rho>' i) (showsl_lit (STR ''Lhs of conditions are different\<newline>''))) 
          [0..<Suc n]
   }  <+? (\<lambda>e. showsl_lit (STR ''Rules'') \<circ> showsl_crule \<rho> \<circ> showsl_lit (STR '' and '') 
      \<circ> showsl_crule \<rho>' \<circ> showsl_lit (STR '' are not '') \<circ> showsl n \<circ> showsl_lit (STR '' equivalent.\<newline>'') \<circ> e)"

lemma prefix_equivalent:
 "isOK(check_prefix_equivalent \<rho> \<rho>' n) = prefix_equivalent \<rho> \<rho>' n"
 unfolding prefix_equivalent_def check_prefix_equivalent_def  isOK_update_error
   isOK_bind isOK_check isOK_forallM set_upt by fastforce


definition check_f :: 
 "('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'f \<Rightarrow> ('f::showl, 'v::showl) crule list \<Rightarrow> (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt)  \<Rightarrow> showsl check"
 where "check_f cr' j f crs U =  
    check_allm 
     (\<lambda>cr.
      check_allm
       (\<lambda>i. 
        case U (cr:: ('f, 'v) crule) (i::nat) of More g b c aft \<Rightarrow> (
          if f = g then ( do{
           check (i = j) (showsl_lit (STR ''Same symbol occurs at different levels\<newline>''));
           check_allm  (\<lambda>k. check (U cr k = U cr' k) (showsl_lit (STR ''Contexts are different\<newline>''))) [0..< Suc j];
           check_prefix_equivalent cr cr' j}  
              <+? (\<lambda>e. showsl_lit (STR ''Rules'') \<circ> showsl_crule cr \<circ> showsl_lit (STR '' and '') 
                 \<circ> showsl_crule cr' \<circ> showsl_lit (STR '' share a symbol.\<newline>'') \<circ> e))
          else succeed)
         | _ \<Rightarrow> succeed
       ) [0..<length (snd cr)]
     ) crs"

lemma check_f: 
 "isOK(check_f \<rho> j f crs (U:: (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> ('f::showl, 'v::showl) ctxt))) = 
   (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> (set crs) \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> 
     f \<noteq> g \<or> (j = n' \<and> (\<forall>i \<le>j. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho>' \<rho> j))"
proof-
   let ?check = "\<lambda> e1 e2 e3 cr' j cr i . case U cr i of More g b c aft \<Rightarrow> (
          if f = g then ( do{
           check (i = j) e1;
           check_allm  (\<lambda>k. check (U cr k = U cr' k) e2) [0..<Suc j];
           check_prefix_equivalent cr cr' j}  <+? e3)
          else succeed)
         | _ \<Rightarrow> succeed"
 { fix cr ::"('f,'v) crule" fix cr' i j e1 e2 e3
   let ?check = "?check e1 e2 e3 cr' j cr i"
   have aux:"\<And>P j. (\<forall>x\<in>set [0..<Suc j]. P x) = (\<forall>x \<le> j. P x)" by auto
   have "isOK (?check) = (\<forall> g b c a. ( U cr i = More g b c a) \<longrightarrow> f \<noteq> g \<or> (j = i \<and> (\<forall>i \<le>j. U cr i = U cr' i) \<and> prefix_equivalent cr cr' j))"
   proof(cases "U cr i", simp)
    case (More g b c a) 
     then show ?thesis unfolding More actxt.split isOK_error is_OK_if_return(2) 
      unfolding isOK_update_error isOK_bind isOK_check isOK_forallM prefix_equivalent aux by auto
   qed
 } note aux = this 
 have aux':"\<And>P j. (\<forall>x\<in>set [0..<j]. P x) = (\<forall>x < j. P x)" by auto
 {fix e1 e2 e3 cr cr' j
  have "isOK(check_allm  (\<lambda>i. ?check e1 e2 e3 cr' j cr i ) [0..<length (snd cr)]) =
  (\<forall> n' g b c a.  (n' < length (snd cr) \<and> U cr n' = More g b c a) \<longrightarrow> 
     f \<noteq> g \<or> (j = n' \<and> (\<forall>i \<le>j. U cr i = U cr' i) \<and> prefix_equivalent cr cr' j))" 
  unfolding isOK_update_error isOK_forallM aux aux' by blast
 } note * = this
 show ?thesis unfolding check_f_def isOK_update_error unfolding isOK_forallM * by metis
qed


definition check_U_cond :: 
 "(('f::showl, 'v::showl) crule \<Rightarrow> nat \<Rightarrow> ('f, 'v) ctxt) \<Rightarrow> ('f, 'v) crule list \<Rightarrow>  'f list \<Rightarrow> (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list) \<Rightarrow> showsl check"
 where "check_U_cond U crs F Z =  do {
    check_allm 
     (\<lambda>cr .
      check_allm
       (\<lambda>i. (case U cr i of 
             More f [] \<box> aft \<Rightarrow> do { 
             \<comment> \<open>check (Umap f  = Some (cr,i)) (shows '' The internally generated  symbol map does not match. '');\<close>
             check_disjoint [f] F <+? (\<lambda>x. showsl_lit (STR ''The function symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' is not fresh.\<newline>''));
             check (aft = map Var (Z cr i)) (showsl_lit (STR '' U does not map to Z vars ''));
             check_f cr i f crs U
             }  <+? (\<lambda>e. showsl_lit (STR ''Conditions for '') \<circ> showsl_crule cr \<circ> showsl_lit (STR '' at  '') 
               \<circ> showsl i \<circ> showsl_lit (STR '' are violated.\<newline>'') \<circ> e)
          | _ \<Rightarrow> error (showsl_lit (STR '' Unexpected empty context.''))
)) [0..<length (snd cr)]
     ) crs 
  } <+? (\<lambda>e. showsl_lit (STR ''The CTRS does not fulfill the condition on the U symbols.\<newline>'') \<circ> e)"

lemma pe:"prefix_equivalent cr cr' n = prefix_equivalent cr' cr n"
 unfolding prefix_equivalent_def by fastforce

lemma check_U_cond[simp]:
 "isOK(check_U_cond U crs F Z) = U_cond U (set crs) (set F) Z" (is "?check = ?sem")
proof -
 let ?U = "\<lambda> \<rho> n. (\<exists> f. (U \<rho> n = (More f Nil Hole (map Var (Z \<rho> n)))  \<and> f \<notin> (set F) \<and>
    (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> (set crs) \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> 
      f \<noteq> g \<or> (n = n' \<and> (\<forall>i \<le>n. U \<rho> i = U \<rho>' i) \<and> prefix_equivalent \<rho> \<rho>' n))))"
 let ?C = "\<lambda> cr i. case U cr i of 
             More f [] \<box> aft \<Rightarrow> do { 
             check_disjoint [f] F <+? (\<lambda>x. showsl_lit (STR ''The function symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' is not fresh.\<newline>''));
             check (aft = map Var (Z cr i)) (showsl_lit (STR '' U does not map to Z vars ''));
             check_f cr i f crs U
             }  <+? (\<lambda>e. showsl_lit (STR ''Conditions for '') \<circ> showsl_crule cr \<circ> showsl_lit (STR '' at  '') 
               \<circ> showsl i \<circ> showsl_lit (STR '' are violated.\<newline>'') \<circ> e) 
          | _ \<Rightarrow> error (showsl_lit (STR '' Unexpected empty context.''))" 
  show ?thesis
  proof
    assume ?check
    show ?sem
    proof (rule U_condI)
      fix cr i
      assume cr: "cr \<in> set crs" and i: "i < length (snd cr)"
      with \<open>?check\<close> have ok: "isOK(?C cr i)" unfolding check_U_cond_def by auto
      then have "\<exists>f b c a. U cr i = More f b c a" using isOK_error by (cases "U cr i", auto) 
      then obtain f b c a where 0:"U cr i = More f b c a" by blast
      from ok[unfolded 0] isOK_error have b:"b=[]" by (cases b, auto) 
      from ok[unfolded 0 b, simplified] isOK_error actxt.exhaust have c:"c=\<box>" by (cases c, auto)
      note ok = ok[unfolded 0[unfolded b c], simplified]
      note 2 = conjunct1[OF conjunct2[OF ok]]
      from ok have a:"a = map Var (Z cr i)" by auto
      from conjunct2[OF conjunct2[OF ok], unfolded check_f] conjunct1[OF ok]
       0[unfolded a b c] 2 pe 
      show "?U cr i" by blast
    qed
  next
    assume ?sem
    show ?check unfolding check_U_cond_def isOK_forallM isOK_update_error set_upt
    proof (intro ballI)
      fix cr i
      assume cr: "cr \<in> set crs" and "i \<in> {0..<length (snd cr)}"
      then have i: "i < length (snd cr)" by auto
      let ?A = "\<lambda>f. U cr i = More f [] \<box> (map Var (Z cr i))"
      let ?C' = "\<lambda>f. f \<notin> set F"
      let ?D = "\<lambda>f. (\<forall> \<rho>' n' g b c a.  (\<rho>' \<in> (set crs) \<and> n' < length (snd \<rho>') \<and> U \<rho>' n' = More g b c a) \<longrightarrow> 
      f \<noteq> g \<or> (i = n' \<and> (\<forall>j \<le>i. U cr j = U \<rho>' j) \<and> prefix_equivalent cr \<rho>'  i))"
      from U_condD[OF \<open>?sem\<close> cr i] obtain f where "?A f \<and> ?C' f \<and> ?D f" by blast
      then have A:"?A f" and C:"?C' f" and D:"?D f" by (fast+)
      from D pe have 4:"isOK (check_f cr i f crs U)" unfolding check_f by blast
      from C 4 show "isOK (?C cr i)" unfolding A actxt.case list.case by force
    qed      
  qed
qed

definition check_source_preserving :: 
 "('f::showl, 'v::showl) crules \<Rightarrow> (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list)  \<Rightarrow> showsl check"
 where "check_source_preserving crs (Zv :: (('f, 'v) crule \<Rightarrow> nat \<Rightarrow> 'v list)) =  
    check_allm 
     (\<lambda>cr.
      check_allm
       (\<lambda>i. 
         check_subseteq (vars_term_list (fst (fst cr))) (Zv cr i)  <+? 
          (\<lambda> x. showsl_lit (STR ''Some variable in lhs does not occur in Z_'') \<circ> showsl i \<circ> showsl_lit (STR ''. \<newline>'') ) 
         <+? (\<lambda>e. showsl_lit (STR ''The unraveling is not source preserving for rule '') \<circ> showsl_crule cr \<circ> showsl_nl \<circ> e)
       ) [0..<length (snd cr)]
     ) crs"

lemma source_preserving [simp]:
   "isOK (check_source_preserving crs Z) = source_preserving (set crs) Z"
  unfolding source_preserving_def check_source_preserving_def by force

definition check_sp_unraveling :: "(('f :: showl,'v :: showl)crule \<times> ('f,'v)rules)list \<Rightarrow> ('f,'v)crules \<Rightarrow> ('f,'v)rules result"
where
  "check_sp_unraveling c_rs ctrs = do {
    check_same_set ctrs (map fst c_rs) <+? (\<lambda> cr. showsl_lit (STR ''did not find rule '') \<circ> showsl_crule cr \<circ> showsl_nl);
    U \<leftarrow> case create_U c_rs of None \<Rightarrow> error (showsl_lit (STR ''unable to extract unraveling contexts'')) | Some U \<Rightarrow> return U;
    Z \<leftarrow> case create_Z c_rs of None \<Rightarrow> error (showsl_lit (STR ''unable to extract Z variables'')) | Some Z \<Rightarrow> return Z;
    Umap \<leftarrow> return (create_Umap c_rs);
    check_U_cond U ctrs (funs_ctrs_list ctrs) Z;
    check_Z_vars ctrs Z;
    check_dctrs ctrs;
    check_type3 ctrs;
    check_allm (\<lambda> (c,rs). check (rules_impl U c = rs) (showsl_lit (STR ''problem with rules of '') \<circ> showsl_crule c \<circ> showsl_nl)) c_rs;
    check_left_linear_trs (concat (map snd c_rs)) <+? (\<lambda> e. showsl_lit (STR ''the unraveled TRS is not left-linear\<newline>'') \<circ> e);
    check_wf_ctrs ctrs <+? (\<lambda> e. showsl_lit (STR ''the CTRS is not well-formed\<newline>'') \<circ> e);
    check_source_preserving ctrs Z <+? (\<lambda> e. showsl_lit (STR ''unraveling is not source preserving\<newline>'') \<circ> e);
    return (concat (map snd c_rs))
  } <+? (\<lambda>e. showsl_lit (STR ''preconditions on the unraveling are not satisfied\<newline>'') \<circ> e)"


lemma check_sp_unraveling_CR:
  assumes ok: "check_sp_unraveling c_rs ctrs = return  (ur :: ('f :: showl, string) rules)"
    and inf: "infinite (UNIV :: 'f set)"
    and CR: "CR (rstep (set (ur :: ('f, string) rules)))"
  shows "CR (cstep (set ctrs))"
proof -
  note ok = ok[unfolded check_sp_unraveling_def, simplified]
  from ok obtain U where U: "create_U c_rs = Some U" by (cases "create_U c_rs", auto)
  from ok obtain Z where Z: "create_Z c_rs = Some Z" by (cases "create_Z c_rs", auto)
  note ok = ok[unfolded U Z, simplified]
  from ok have ur: "ur = concat (map snd c_rs)" by simp
  from ok source_preserving have z:"source_preserving (set ctrs) Z" by auto
  from ok check_left_linear_trs have ll:"left_linear_trs (set ur)" by auto 
  from ok  have wf:"wf_ctrs (set ctrs)" by auto
  from ok have U_cond: "U_cond U (set ctrs) (funs_ctrs (set ctrs)) Z" by auto
  interpret unraveling "set ctrs" U .
  have ur1:"UR \<subseteq> set ur" 
  proof(rule subsetI)
    fix lr
    assume lr: "lr \<in> UR"
    from this[unfolded UR_def] obtain cr where cr: "cr \<in> set ctrs"
    and lr: "lr \<in> rules cr" by auto
    from ok cr obtain rs where mem: "(cr,rs) \<in> set c_rs" by auto
    from ok mem have "rules_impl U cr = rs" by auto
    from arg_cong[OF this, of set] have "rules cr = set rs" by simp
    with lr have lr: "lr \<in> set rs" by auto
    with mem show "lr \<in> set ur" unfolding ur by force
  qed
  have ur2:"UR \<supseteq> set ur" 
  proof(rule subsetI)
    fix lr
    assume lr: "lr \<in> set ur"
    from this[unfolded ur set_concat set_map] have "\<exists>(cr,rs) \<in> set c_rs. lr \<in> set rs" by fastforce
    then obtain cr rs where mem:"(cr,rs) \<in> set c_rs" "lr \<in> set rs" by blast
    with ok have a:"\<forall>x\<in>set c_rs. case x of (c, rs) \<Rightarrow> rules_impl U c = rs" by meson
    from imageI[OF mem(1), of fst] conjunct1[OF ok] have mem':"cr \<in> set ctrs" by simp
    from a[rule_format, OF mem(1), unfolded split] mem(2) have "lr \<in> rules cr" by force
    with mem' show "lr \<in> UR" unfolding UR_def by blast
  qed
  with ur1 have ur:"UR = set ur" by auto
  show ?thesis
  proof (rule CR_imp_CR)
    show "infinite (UNIV :: string set)" by (rule infinite_UNIV_listI)
    show "infinite (UNIV :: 'f set)" by (rule inf)
  qed (insert ur z ll CR wf ok, auto)
qed

text \<open>The split-if transformation (Claessen and Smallbone, 2018) for infeasibility of CTRSs via normal unraveling.\<close>

type_synonym ('f, 'v) U_list = "((('f,'v) crule \<times> ('f \<times> ('f,'v)term list)) list)"

(* (T, F, U) where T = F is the goal and U is given as a list *)
type_synonym ('f, 'v) split_if = "('f, 'v) term \<times> ('f, 'v) term \<times> ('f, 'v) U_list"

definition
  create_U_s ::
    "('f, 'v) U_list \<Rightarrow> ('f, 'v) crule \<Rightarrow>  ('f \<times> ('f,'v) term list) option"
  where
  "create_U_s ls rule =
    (case List.find (\<lambda> x. fst x = rule) ls of Some (_, r) \<Rightarrow> Some r | None \<Rightarrow> None)"

definition rules_impl_s :: "(('f, 'v) crule \<Rightarrow>  ('f \<times> ('f,'v) term list) option) \<Rightarrow> ('f,'v)crule \<Rightarrow> ('f,'v) rules"
  where "rules_impl_s U crule = (case U crule of 
     None \<Rightarrow> [fst crule]
   | Some (f, ctxt) \<Rightarrow> let conds = snd crule; lr = fst crule in
       if conds = [] then [ lr ] else [ (fst lr, Fun f (map fst conds @ ctxt)),
         (Fun f (map snd conds @ ctxt), snd lr)])"

lemma rules_impl_s:
  "set (rules_impl_s U crule) = normal_unraveling.rules U crule"
  unfolding rules_impl_s_def normal_unraveling.rules_def
  by (auto split: option.splits simp: Let_def)

definition UR_impl_s :: "(('f, 'v) crule \<Rightarrow>  ('f \<times> ('f,'v) term list) option) \<Rightarrow> ('f,'v)crules \<Rightarrow> ('f, 'v) rules"
  where "UR_impl_s U R = concat (map (rules_impl_s U) R)"

lemma UR_impl:
  "set (UR_impl_s U R) = (normal_unraveling.UR (set R) U)"
  unfolding UR_impl_s_def normal_unraveling.UR_def using rules_impl_s by fastforce

definition split_if :: "('f :: showl,'v :: showl) split_if \<Rightarrow> ('f,'v)crules \<Rightarrow> 
  (('f, 'v) term \<times> ('f, 'v) term) list \<Rightarrow> ('f,'v) rules"
  where "split_if p R cs = (case p of (T, F, U) \<Rightarrow> UR_impl_s (create_U_s U) R)"

lemma split_if:
  "set (split_if (T, F, U) R cs) = normal_unraveling.UR (set R) (create_U_s U)"
  unfolding split_if_def using UR_impl by force

lemma split_if_correct:
  assumes
    "(T, F) \<in> set cs"
    "ground T" "ground F"
    "(T, F) \<notin> (rstep (set (split_if (T, F, U) R cs)))\<^sup>*" 
  shows "\<not> conds_sat (set R) cs \<sigma>"
  using assms split_if infeasibility_via_normal_unravel by metis

hide_const (open) rules_impl create_U rules_impl_s create_U_s create_zs create_Z U_cond check_U_cond check_Z_vars 
 check_f si ti

end
