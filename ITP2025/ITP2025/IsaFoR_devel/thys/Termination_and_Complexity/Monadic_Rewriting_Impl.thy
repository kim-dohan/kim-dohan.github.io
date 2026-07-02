(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Monadic_Rewriting_Impl
imports
  Monadic_Rewriting
  First_Order_Rewriting.Trs_Impl
  Auxx.Map_Choice
  Framework.QDP_Framework_Impl
begin

definition extract_renamings :: "('f \<times> 'f)list \<Rightarrow> ('f \<Rightarrow> 'f) \<times> ('f \<Rightarrow> 'f)" where
  "extract_renamings old_new = 
  (fun_of_map_fun (map_of old_new) id, fun_of_map_fun (map_of (map prod.swap old_new)) id)"

definition extract_components :: "('f \<times> nat) list \<Rightarrow> ('f \<times> 'f)list \<Rightarrow> ('f \<Rightarrow> 'f) \<times> ('f \<Rightarrow> 'f) \<times> 'f list" where
  "extract_components MU old_new \<equiv> let 
    (d,d') = extract_renamings old_new; 
    C = map fst (filter (\<lambda> (f,a). a = 0) MU);
    NU = map d C
    in
     (d,d',NU)"

definition check_components :: "(('f :: showl) \<times> nat) list \<Rightarrow> ('f \<Rightarrow> 'f) \<times> ('f \<Rightarrow> 'f) \<times> 'f list \<Rightarrow> showsl check" where
  "check_components MU ddNU \<equiv> case ddNU of (d,d',NU) \<Rightarrow> do {
     check_allm (\<lambda> f. do {
       check ((f,1) \<notin> set MU) 
         (showsl_lit (STR ''new unary symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' clashes with old symbol''));
       check (d (d' f) = f) (showsl_lit (STR ''problem with bijection for renaming of '') \<circ> showsl f);
       check ((d' f,0) \<in> set MU) (showsl_lit (STR ''problem with inverse renaming of '') \<circ> showsl f)
     }) NU;
     check_allm (\<lambda> (f,n). do {
       check (n \<le> 1) 
         (showsl_lit (STR ''arity > 1 for symbol '') \<circ> showsl f);
       check (n = 0 \<longrightarrow> d f \<in> set NU \<and> d' (d f) = f) (showsl_lit (STR ''problem with bijection for renaming of constant '') \<circ> showsl f)
     }) MU
   }
   "

lemma check_components[simp]: "isOK(check_components MU (d,d',NU)) = max_unary (set NU) d d' (set MU)"
  unfolding max_unary_def check_components_def split by auto

definition choose_var :: "'v \<Rightarrow> ('f,'v)term \<Rightarrow> 'v"
  where "choose_var x l \<equiv> hd (vars_term_list l @ [x])"

definition check_to_srs_complete :: "'v \<Rightarrow> ('f \<times> 'f)list \<Rightarrow> ('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check" where
  "check_to_srs_complete v old_new R S \<equiv> do {
    let MU = funas_trs_list R;
    let (d,d',NU) = extract_components MU old_new;
    check_components MU (d,d',NU);
    check_varcond_subset S;
    check_allm (\<lambda> slr. let y = choose_var v (fst slr); str = pre_max_unary.str d y; to_slr = (\<lambda> (l,r). (str l, str r))
       in check (\<exists> lr \<in> set R. to_slr lr = slr) (showsl_lit (STR ''could not find original rule for '') \<circ> showsl_rule slr))
       S
  }"

lemma check_to_srs_complete: assumes ok: "isOK(check_to_srs_complete v old_new R S)"
  and "\<not> SN (rstep (set S))"
  shows "\<not> SN (rstep (set R))"
proof
  assume SN: "SN(rstep (set R))"
  let ?MU = "funas_trs_list R"
  obtain d d' NU where extr: "extract_components ?MU old_new = (d, d', NU)" 
    by (cases "extract_components ?MU old_new", auto)
  let ?NU = "set NU"
  note ok = ok[unfolded check_to_srs_complete_def Let_def extr split, simplified]
  define MU where "MU = funas_trs (set R)"
  from ok have "max_unary ?NU d d' MU" unfolding MU_def by auto  
  interpret max_unary ?NU d d' MU by fact
  interpret max_unary_reverse ?NU d d' MU "set R" "set S"
    by (unfold_locales, insert ok, (force simp: MU_def)+)
  have "SN(rstep (set S))"
    by (rule SN_R_imp_SN_S[OF SN])
  with assms show False by auto
qed

definition check_to_srs_sound :: "'v \<Rightarrow> ('f \<times> 'f)list \<Rightarrow> ('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check" where
  "check_to_srs_sound v old_new R S Rw Sw \<equiv> do {
    let MU = funas_trs_list (R @ Rw);
    let (d,d',NU) = extract_components MU old_new;
    check_components MU (d,d',NU);
    check_varcond_subset R;
    check_varcond_subset Rw;
    let check = (\<lambda> R S. 
      check_allm (\<lambda> (l,r). let y = choose_var v l; str = pre_max_unary.str d y; slr = (str l, str r)
         in check (vars_term l \<subseteq> {y} \<and> slr \<in> set S) (showsl_lit (STR ''problem with new rule '') \<circ> showsl_rule slr))
         R);
    check R S;
    check Rw Sw
  }"

lemma check_to_srs_sound: assumes ok: "isOK(check_to_srs_sound v old_new R S Rw Sw)"
  and SN: "SN_rel (rstep (set S)) (rstep (set Sw))"
  shows "SN_rel (rstep (set R)) (rstep (set Rw))"
proof -
  let ?MU = "funas_trs_list (R @ Rw)"
  obtain d d' NU where extr: "extract_components ?MU old_new = (d, d', NU)" 
    by (cases "extract_components ?MU old_new", auto)
  let ?NU = "set NU"
  note ok = ok[unfolded check_to_srs_sound_def Let_def extr split, simplified]
  define MU where "MU = funas_trs (set R \<union> set Rw)"
  from ok have "max_unary ?NU d d' MU" unfolding MU_def by auto  
  interpret max_unary ?NU d d' MU by fact
  show ?thesis
    by (rule  SN_rel_S_Sw_imp_SN_rel_R_Rw[OF _ _ _ _ _ _ SN],
    insert ok, (force simp: MU_def)+)
qed

datatype ('f,'v)const_string_sound_proof = Const_string_sound_proof 'v "('f \<times> 'f)list" "('f,'v)rules"

(* TODO: support relative setting by splitting S into strict and non-strict part automatically *)

primrec const_to_string_sound_tt :: "('f,'v)const_string_sound_proof \<Rightarrow> ('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow> 'tp proc" where
  "const_to_string_sound_tt (Const_string_sound_proof v old_new S) I tp = do {
    check_to_srs_sound v old_new (tp_ops.R I tp) S (tp_ops.Rw I tp) []; 
    return (tp_ops.mk I False [] S [])
  }"

context tp_spec
begin
lemma const_to_string_sound_tt:
  "sound_tt_impl (const_to_string_sound_tt prf I)"
proof (standard, cases "prf")
  fix tp tp' v old_new S
  assume ok: "const_to_string_sound_tt prf I tp = return tp'"
    and fin: "SN_qrel (qreltrs tp')"
    and p: "prf = Const_string_sound_proof v old_new S"
  let ?Q = "set (Q tp)"
  let ?R = "set (R tp)"
  let ?Rw = "set (Rw tp)"  
  from ok[unfolded p, simplified]
  have tp': "tp' = mk False [] S []" 
    and ok: "isOK (check_to_srs_sound v old_new (R tp) S (Rw tp) [])"
    by auto
  from fin tp' have "SN_rel (rstep (set S)) (rstep (set []))" by auto
  from check_to_srs_sound[OF ok this] have "SN_rel (rstep ?R) (rstep ?Rw)" .
  then have SN: "SN_qrel (NFS tp, {}, ?R, ?Rw)" by auto
  have "SN_qrel (NFS tp, ?Q, ?R, ?Rw)"
    by (rule SN_qrel_mono[OF _ _ _ SN], auto)
  then show "SN_qrel (qreltrs tp)"
    unfolding qreltrs_sound .
qed
end


datatype ('f,'v)const_string_complete_proof = Const_string_complete_proof 'v "('f \<times> 'f)list" "('f,'v)rules"

primrec const_to_string_complete_tt where
  "const_to_string_complete_tt I tp (Const_string_complete_proof v old_new S) = do {
    check (tp_ops.Q_empty I tp) (showsl_lit (STR ''Q is not empty''));
    check_to_srs_complete v old_new (tp_ops.rules I tp) S;
    return (tp_ops.mk I False [] S [])
  }"

lemma const_to_string_complete_tt:
  assumes I: "tp_spec I" 
  and ok: "const_to_string_complete_tt I tp prf = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" (is "\<not> SN ?tp'")
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" (is "\<not> SN ?tp")
proof (cases "prf")
  case (Const_string_complete_proof v old_new S)
  interpret tp_spec I by fact
  note ok = ok[unfolded Const_string_complete_proof, simplified]
  let ?R = "set (rules tp)"
  let ?tp' = "mk False [] S []"
  from ok have Q: "set (Q tp) = {}" by simp
  from ok have tp': "tp' = ?tp'" by simp
  from ok have "isOK (check_to_srs_complete v old_new (rules tp) S)" by auto
  from check_to_srs_complete[OF this] Q nSN show ?thesis unfolding tp' by auto
qed
  
end
