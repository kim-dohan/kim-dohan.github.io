(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Semantic_Labeling_Carrier
imports 
  Auxx.Pointwise_Extension
  Semantic_Labeling_Impl
  Labelings_Impl
  Show.Shows_Literal
begin

subsection \<open>carrier {0..n}\<close>

datatype arithFun =
  Arg nat
| Const nat
| Sum "arithFun list"
| Max "arithFun list"
| Min "arithFun list"
| Prod "arithFun list"
| IfEqual arithFun arithFun arithFun arithFun

text \<open>An alternative induction scheme for arithFuns.\<close>
lemma
  fixes P :: "arithFun \<Rightarrow> bool"
  assumes "\<And>n. P(Arg n)" and "\<And>n. P(Const n)"
    and "\<And>fs. (\<And>f. f \<in> set fs \<Longrightarrow> P f) \<Longrightarrow> P(Sum fs)"
    and "\<And>fs. (\<And>f. f \<in> set fs \<Longrightarrow> P f) \<Longrightarrow> P(Max fs)"
    and "\<And>fs. (\<And>f. f \<in> set fs \<Longrightarrow> P f) \<Longrightarrow> P(Min fs)"
    and "\<And>fs. (\<And>f. f \<in> set fs \<Longrightarrow> P f) \<Longrightarrow> P(Prod fs)"
    and "\<And> f1 f2 ft fe. P f1 \<Longrightarrow> P f2 \<Longrightarrow> P ft \<Longrightarrow> P fe \<Longrightarrow> P(IfEqual f1 f2 ft fe)"
  shows arithFun_induct[case_names Arg Const Sum Max Min Prod IfEqual,induct type: arithFun]: "P f"
  by (rule arithFun.induct, insert assms, auto)

instantiation arithFun :: showl
begin
fun showsl_arithFun :: "arithFun \<Rightarrow> showsl" where
  "showsl_arithFun (Arg i) = showsl_lit (STR ''x_'') \<circ> showsl (Suc i)" |
  "showsl_arithFun (Const n) = showsl n" |
  "showsl_arithFun (Sum fs) = showsl_list_gen id (STR '''') (STR '''') (STR '' + '') (STR '''') (map showsl_arithFun fs)" |
  "showsl_arithFun (Prod fs) = showsl_list_gen id (STR '''') (STR '''') (STR '' * '') (STR '''') (map showsl_arithFun fs)" |
  "showsl_arithFun (Min fs) = showsl_list_gen id (STR '''') (STR ''min('') (STR '','') (STR '')'') (map showsl_arithFun fs)" |
  "showsl_arithFun (Max fs) = showsl_list_gen id (STR '''') (STR ''max('') (STR '','') (STR '')'') (map showsl_arithFun fs)" |
  "showsl_arithFun (IfEqual f1 f2 ft fe) =
    showsl_lit (STR ''if '') \<circ> showsl_arithFun f1 \<circ> showsl_lit (STR '' = '') \<circ> showsl_arithFun f2 \<circ>
    showsl_lit (STR '' then '') \<circ> showsl_arithFun ft \<circ>
    showsl_lit (STR '' else '') \<circ> showsl_arithFun fe \<circ> showsl_lit (STR '' fi'')"
definition "showsl_list (xs :: arithFun list) = default_showsl_list showsl xs"
instance ..
end

fun take_default where
  "take_default def [] _ = def"
| "take_default _ (x # xs) 0 = x"
| "take_default def (_ # xs) (Suc i) = take_default def xs i"

fun eval_arithFun_unbound :: "nat \<Rightarrow> nat list \<Rightarrow> arithFun \<Rightarrow> nat" and 
  eval_arithFun :: "nat \<Rightarrow> nat list \<Rightarrow> arithFun \<Rightarrow> nat"
  where
  "eval_arithFun_unbound c nats (Arg i) = take_default 0 nats i"
| "eval_arithFun_unbound c nats (Const n) = n"
| "eval_arithFun_unbound c nats (Sum []) = 0"
| "eval_arithFun_unbound c nats (Sum (f # fs)) = (eval_arithFun c nats f + eval_arithFun c nats (Sum fs))"
| "eval_arithFun_unbound c nats (Prod []) = 1"
| "eval_arithFun_unbound c nats (Prod (f # fs)) = (eval_arithFun c nats f * eval_arithFun c nats (Prod fs))"
| "eval_arithFun_unbound c nats (Max [f]) = eval_arithFun c nats f"
| "eval_arithFun_unbound c nats (Max (f # fs)) = (max (eval_arithFun c nats f) (eval_arithFun c nats (Max fs)))"
| "eval_arithFun_unbound c nats (Min [f]) = eval_arithFun c nats f"
| "eval_arithFun_unbound c nats (Min (f # fs)) = (min (eval_arithFun c nats f) (eval_arithFun c nats (Min fs)))"
| "eval_arithFun_unbound c nats (IfEqual f1 f2 ft fe) = (if (eval_arithFun c nats f1 = eval_arithFun c nats f2)
    then eval_arithFun c nats ft else eval_arithFun c nats fe)"
| "eval_arithFun c nats f = (eval_arithFun_unbound c nats f) mod c"

declare eval_arithFun_unbound.simps[simp del]


datatype ('f) sl_inter = SL_Inter nat "(('f \<times> nat) \<times> arithFun) list"

instantiation sl_inter :: (showl) showl
begin

fun showsl_sl_inter :: "'a sl_inter \<Rightarrow> showsl"
where
  "showsl_sl_inter(SL_Inter n fnas) =
    showsl_lit (STR ''carrier {0,...,'') \<circ> showsl n \<circ> showsl_lit (STR ''}\<newline>'') \<circ> 
     foldr (\<lambda>((f, n), a).
       showsl_lit (STR ''['') \<circ> showsl f \<circ> showsl_lit (STR ''/'') \<circ> showsl n 
       \<circ> showsl_lit (STR ''] = '') \<circ> showsl a \<circ> showsl_nl) fnas"
definition "showsl_list (xs :: _ sl_inter list) = default_showsl_list showsl xs"
instance ..
end

primrec get_largest_element where "get_largest_element (SL_Inter n _) = n"

primrec sl_inter_to_inter :: "'f sl_inter \<Rightarrow> ('f, nat) inter" where
  "sl_inter_to_inter (SL_Inter c ls) fl cs =
    (case map_of ls (fl, length cs) of 
      None \<Rightarrow> 0
    | Some f \<Rightarrow> eval_arithFun (Suc c) cs f)"

lemma wf_sl_inter: 
  "wf_inter (sl_inter_to_inter sli) {x | x.  x < Suc (get_largest_element sli)}"
proof (cases sli)
  case (SL_Inter c ls)
  then show ?thesis unfolding wf_inter_def
  proof (intro allI, intro impI)
    fix f cs
    show "sl_inter_to_inter sli f cs \<in> {x | x. x < Suc (get_largest_element sli)}" using SL_Inter
      by (cases "map_of ls (f, length cs)", auto)
  qed
qed

lemma sl_helper:  "set [0..<Suc n] = {x | x. x < Suc n}" by auto

text \<open>lets consider different finite carriers / variants\<close>
type_synonym label_type = "nat list"

subsection \<open>arithmetic modulo, for models\<close>

definition
  sli_to_slm :: "('f, label_type) lab sl_inter \<Rightarrow> (('f, label_type) lab, nat, label_type + ('f, label_type) lab list, 'v) slm_ops"
where
  "sli_to_slm sli \<equiv>
    let c = get_largest_element sli in \<lparr>
      slm_L = \<lambda> _. Inl,
      slm_I = sl_inter_to_inter sli,
      slm_C = [0..< Suc c],
      slm_c = c,
      slm_L'' = \<lambda> _. Inl
    \<rparr>"

interpretation sl_fin_model: sl_finite_model_impl label label_decomp "\<lambda> _ _. return (sli_to_slm sli)"
proof (unfold_locales, rule label_decomp_label)
  fix F G ops
  assume "Inr (sli_to_slm sli) = Inr ops"
  then have ops: "ops = sli_to_slm sli" by simp
  show "slm_c ops \<in> set (slm_C ops) \<and> wf_inter (slm_I ops) (set (slm_C ops))"
    unfolding ops sli_to_slm_def Let_def slm_ops.simps sl_helper
    using wf_sl_inter by auto
qed


subsection \<open>root-labeling\<close>

definition rl_slm :: "(('f,'l)lab \<times> nat) option \<Rightarrow> (('f,'l)lab \<times> nat) list \<Rightarrow> (('f,'l)lab \<times> nat) list \<Rightarrow> showsl + (('f,'l)lab,('f,'l)lab,'l + ('f,'l)lab list,'v)slm_ops"
  where "rl_slm delt_opt pre_fs G \<equiv>  do {
     let fs = (if delt_opt = None then pre_fs else filter (\<lambda> f. f \<noteq> the delt_opt) pre_fs);
     check (fs \<noteq> [])
       (showsl_lit (STR ''root-labeling requires at least one function symbol in the signature\<newline>''));
     let f = fst (hd fs);
     return \<lparr>
       slm_L = (\<lambda> _. Inr),
       slm_I = (\<lambda> g cs. if (g,length cs) \<in> set fs then g else f),
       slm_C = map fst fs,
       slm_c = f,
       slm_L'' = (if delt_opt = None then (\<lambda> _. Inr) else (\<lambda> _ gs. Inr (replicate (length gs) (fst (the (delt_opt))))))
     \<rparr>
   }
   "

interpretation rl_fin_model: sl_finite_model_impl label label_decomp "rl_slm delt_opt"
proof(unfold_locales, rule label_decomp_label)
  fix F H ops
  assume F: "rl_slm delt_opt F H = Inr ops"
  obtain G where G: "G = (if delt_opt = None then F else filter (\<lambda> f. f \<noteq> the delt_opt) F)" by auto
  note F = F[unfolded rl_slm_def Let_def G[symmetric]]
  from F obtain f fs where f: "G = f # fs" 
    by (cases G, auto simp: check_def)
  from F[unfolded f] have c: "slm_c ops = fst f" and I: "slm_I ops = (\<lambda> g cs. if (g,length cs) \<in> set (f # fs) then g else fst f)" and C: "slm_C ops = fst f # map fst fs" 
    unfolding list.sel
    by (auto simp: check_def)  
  show "slm_c ops \<in> set (slm_C ops) \<and> wf_inter (slm_I ops) (set (slm_C ops))"
    unfolding c C I wf_inter_def by force
qed

subsection \<open>arithmetic modulo, for quasi-models\<close>

fun enum_vectors_nat :: "'c list \<Rightarrow> nat \<Rightarrow> 'c list list"
where "enum_vectors_nat C 0 = [[]]"
    | "enum_vectors_nat C (Suc n) = (let rec = enum_vectors_nat C n in concat (map (\<lambda> vec. map (\<lambda> c. c # vec) C) rec))" 


lemma enum_vectors_nat[simp]: 
  shows "set (enum_vectors_nat C n) = { xs. set xs \<subseteq> set C \<and> length xs = n}"
proof (induct n)
  case 0 
  show ?case by auto
next
  case (Suc n)
  have "set (enum_vectors_nat C (Suc n)) = 
    (\<Union>a\<in>{xs. set xs \<subseteq> set C \<and> length xs = n}. (\<lambda>c. c # a) ` set C)"
    unfolding enum_vectors_nat.simps Let_def
    by (simp add: Suc)
  also have "\<dots> = {xs. set xs \<subseteq> set C \<and> length xs = Suc n}" (is "?l = ?r")
  proof (intro set_eqI iffI)
    fix xs
    assume "xs \<in> ?l"
    then show "xs \<in> ?r" by auto
  next
    fix xs
    assume "xs \<in> ?r"
    then show "xs \<in> ?l" by (cases xs, auto)
  qed
  finally show ?case .
qed

declare enum_vectors_nat.simps[simp del]

definition qmodel_LS_gen: "qmodel_LS_gen sig LS = (\<lambda> f n. if (f,n) \<in> set sig then map Inl (enum_vectors_nat LS n) else [Inl []])"

definition qmodel_LS :: "('f \<times> nat) list \<Rightarrow> 'l list \<Rightarrow> ('f,'l list + 'b)labels" 
  where [code del]: "qmodel_LS sig LS \<equiv> \<lambda> f n x. x \<in> (if (f,n) \<in> set sig then {Inl xs | xs. set xs \<subseteq> set LS \<and> length xs = n} else {Inl []})"

lemma qmodel_LS_gen': "\<And> f n. set (qmodel_LS_gen sig LS f n) = Collect (qmodel_LS sig LS f n)"
  unfolding qmodel_LS_gen qmodel_LS_def set_map enum_vectors_nat image_Collect by auto

lemma [code]: "qmodel_LS sig LS = (\<lambda> f n x. x \<in> set (qmodel_LS_gen sig LS f n))"
  unfolding qmodel_LS_gen' by simp

definition qmodel_L :: "(('f,'l)lab \<times> nat) list \<Rightarrow> (('f,'l)lab,'c,'c list + 'a)label" 
  where "qmodel_L sig \<equiv> \<lambda> f cs. if (f,length cs) \<in> set sig then Inl cs else Inl []"
definition qmodel_cge where "qmodel_cge \<equiv> greater_eq :: nat \<Rightarrow> nat \<Rightarrow> bool"
definition qmodel_lge where "qmodel_lge f n \<equiv> \<lambda> l r. case (l,r) of 
  (Inl cs1, Inl cs2) \<Rightarrow> snd (pointwise_ext (\<lambda> x y :: nat. (y < x, y \<le> x)) cs1 cs2)
  | _ \<Rightarrow> False"


definition qmodel_check_interpretation :: "arithFun \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> showsl check" where 
  "qmodel_check_interpretation f n c \<equiv>
      let C = [0 ..< Suc c];
          css = enum_vectors_nat C n
       in check_allm 
             (\<lambda> cs. check_allm 
                   (\<lambda> i. check_allm 
                         (\<lambda> l. check (eval_arithFun (Suc c) cs f \<le> eval_arithFun (Suc c) (cs [i := l]) f) 
                              (showsl_lit (STR ''not monotone in '') \<circ> showsl (Suc i) \<circ> showsl_lit (STR ''. argument'')))
                         [cs ! i ..< Suc c])
                   [0 ..< n])
          css"

fun qmodel_check_valid :: "('f :: showl)sl_inter \<Rightarrow> showsl check" 
  where "qmodel_check_valid (SL_Inter c ls) = check_allm (\<lambda> ((f,n),g). qmodel_check_interpretation g n c <+? 
            (\<lambda> e. showsl_lit (STR ''problem in weak-monotonicity of interpretation of '') \<circ> showsl f \<circ> showsl_nl \<circ> e )) ls"

lemma qmodel_check_valid: assumes valid: "isOK(qmodel_check_valid sli)"
  shows "cge_wm (sl_inter_to_inter sli) {x | x. x < Suc (get_largest_element sli)} qmodel_cge"
proof (cases sli)
  case (SL_Inter n fas)
  then show ?thesis
  proof (simp, unfold cge_wm qmodel_cge_def, intro allI impI, clarify)
    fix f bef c d aft
    assume mem: "set ([c,d] @ bef @ aft) \<subseteq> {u. u < Suc n}" and dc: "d \<le> c"
    let ?n = "Suc (length bef + length aft)"
    let ?i = "length bef"
    show "sl_inter_to_inter (SL_Inter n fas) f (bef @ d # aft) \<le> sl_inter_to_inter (SL_Inter n fas) f (bef @ c # aft)"
    proof (cases "map_of fas (f, ?n)")
      case None
      then show ?thesis by simp 
    next
      case (Some g)        
      let ?cs = "bef @ d # aft"
      let ?ccs = "bef @ c # aft"
      have elem: "((f, ?n), g) \<in> set fas" by (rule map_of_SomeD[OF Some])
      from elem valid[unfolded SL_Inter]
      have ok: "isOK(qmodel_check_interpretation g ?n n)" by auto
      from mem have mem: "bef @ d # aft \<in> set (enum_vectors_nat [0 ..< Suc n] ?n)" and c: "c < Suc n" by auto
      have i: "?i \<in> set [0 ..< ?n]" by auto
      from dc c have c: "c \<in> set [?cs ! ?i ..< Suc n]" by auto
      from ok[unfolded qmodel_check_interpretation_def Let_def,
        unfolded isOK_update_error isOK_forallM,
        THEN bspec[OF _ mem], THEN bspec[OF _ i], THEN bspec[OF _ c]]
      have "eval_arithFun (Suc n) ?cs g \<le> eval_arithFun (Suc n) ?ccs g" by auto
      then show ?thesis by (simp add: Some)
    qed
  qed
qed

lemma qmodel_lge_wm: "lge_wm I (qmodel_L sig) C qmodel_cge qmodel_lge"
  unfolding lge_wm qmodel_cge_def qmodel_lge_def qmodel_L_def pointwise_ext_iff
proof (simp, intro allI impI, clarify)
  fix f bef and c d :: nat and  aft i
  assume dc: "d \<le> c"
  show "(bef @ d # aft) ! i \<le> (bef @ c # aft) ! i"
  proof (cases "i = length bef")
    case True then show ?thesis by (simp add: dc)
  next
    case False note oFalse = this
    then show ?thesis
    proof (cases "i < length bef")
      case True
      then show ?thesis by (simp add: nth_append)
    next
      case False
      with oFalse have "i - length bef > 0" by auto
      then obtain j where "i - length bef = Suc j"
        by (cases "i - length bef") auto
      then show ?thesis by (simp add: nth_append)
    qed
  qed
qed

definition
  check_decr_present_aux_1 :: "('f, 'v \<times> nat)rules \<Rightarrow> 'v \<Rightarrow> 'f \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> ('f,'v \<times> nat) rule check"
where
  "check_decr_present_aux_1 R v f1 f2 n \<equiv> 
    let
      vs = map (\<lambda> n. Var (v,n)) [0 ..< n];
      rule = (Fun f1 vs, Fun f2 vs)
    in check (List.find (instance_rule rule) R \<noteq> None) rule"
        
lemma check_decr_present_aux_1:
  fixes R :: "('f,'v \<times> nat)rules"
  assumes check: "isOK(check_decr_present_aux_1 R v f1 f2 n)"
  shows "{(Fun f1 ts,Fun f2 ts) | ts. length ts = n} \<subseteq> subst.closure (set R)"
proof -
  {
    fix ts :: "('f,'v \<times> nat) term list"
    assume len: "length ts = n"
    let ?n = "[0 ..< n]"
    let ?vs = "map (\<lambda> n. Var (v,n)) ?n"
    let ?rule = "(Fun f1 ?vs, Fun f2 ?vs)"
    have "List.find (instance_rule ?rule) R \<noteq> None" (is "?f \<noteq> None")
      using check[unfolded check_decr_present_aux_1_def Let_def] by auto
    then obtain rule where "?f = Some rule" by (cases ?f, auto)
    from this[unfolded find_Some_iff] have rule: "rule \<in> set R"
      and inst: "instance_rule ?rule rule" by auto
    from inst[unfolded instance_rule_def] obtain \<sigma> where
      id: "?rule = (fst rule \<cdot> \<sigma>, snd rule \<cdot> \<sigma>)" by auto
    obtain \<delta> :: "('f, 'v \<times> nat) subst" where delta: "\<delta> = (\<lambda>(_,i). ts ! i)" by auto
    obtain \<gamma> where gamma: "\<gamma> = \<sigma> \<circ>\<^sub>s \<delta>" by auto
    have ts_delta: "map (\<lambda> t. t \<cdot> \<delta>) ?vs = ts" unfolding delta
      by (rule nth_equalityI, auto simp add: len)
    then have "(Fun f1 ts, Fun f2 ts) = (Fun f1 ?vs \<cdot> \<delta>, Fun f2 ?vs \<cdot> \<delta>)" by auto
    with id have id: "(Fun f1 ts, Fun f2 ts) = (fst rule \<cdot> \<gamma>, snd rule \<cdot> \<gamma>)"
      by (auto simp: gamma)
    have "(Fun f1 ts, Fun f2 ts) \<in> subst.closure (set R)"
      unfolding id by (auto simp: rule)
  }
  then show ?thesis by auto
qed

definition
  check_decr_present_aux_2 ::
    "('f, 'v) rules \<Rightarrow> 'v \<Rightarrow> ('f \<times> 'f \<times> nat) list \<Rightarrow> ('f, 'v \<times> nat) rule check"
where
  "check_decr_present_aux_2 R v req = ( 
    let
      (add_nats :: ('f, 'v) term \<Rightarrow> ('f,'v \<times> nat) term) = map_vars_term (\<lambda> v. (v, 0));
      R' = map (\<lambda>(l, r). (add_nats l, add_nats r)) R
    in check_allm (\<lambda>(f1 :: 'f, f2, n). check_decr_present_aux_1 R' v f1 f2 n) req)"

lemma check_decr_present_aux_2: 
  fixes R :: "('f,'v)rules"
  assumes check: "isOK(check_decr_present_aux_2 R v req)"
  shows "{(Fun f1 ts, Fun f2 ts) | f1 f2 n ts. (f1,f2,n) \<in> set req \<and> length ts = n} \<subseteq> subst.closure (set R)"
proof -
  {
    fix f1 f2 :: 'f and n :: nat and ts :: "('f,'v)term list"
    let ?add_nats = "map_vars_term (\<lambda> v. (v, 0)) :: ('f,'v)term \<Rightarrow> ('f,'v \<times> nat)term"
    let ?rem_nats = "map_vars_term (\<lambda> (v,n). v) :: ('f,'v \<times> nat)term \<Rightarrow> ('f,'v)term"
    let ?R = "map (\<lambda> (l,r). (?add_nats l, ?add_nats r)) R"
    let ?ts = "map ?add_nats ts"
    assume "(f1,f2,n) \<in> set req" and len: "length ts = n"
    from this check[unfolded check_decr_present_aux_2_def Let_def] 
    have "isOK(check_decr_present_aux_1 ?R v f1 f2 n)" by auto
    from check_decr_present_aux_1[OF this] len
    have "(Fun f1 ?ts, Fun f2 ?ts) \<in> subst.closure (set ?R)" by auto
    then have "(?rem_nats (Fun f1 ?ts), ?rem_nats (Fun f2 ?ts)) \<in> (\<lambda> (l,r). (?rem_nats l, ?rem_nats r)) ` subst.closure (set ?R)" (is "_ \<in> ?RR") by force
    then have mem: "(Fun f1 ts, Fun f2 ts) \<in> ?RR"
      unfolding term.map(2) [of "\<lambda>x. x", symmetric] map_vars_term_compose
      by (simp add: o_def map_vars_term_id [simplified id_def])
    then obtain l r where mem: "(l,r) \<in> subst.closure (set ?R)"
      and "Fun f1 ts = ?rem_nats l" and "Fun f2 ts = ?rem_nats r"  by force
    then obtain l r \<sigma> where mem: "(l,r) \<in> set R"
      and l: "Fun f1 ts = ?rem_nats (?add_nats l \<cdot> \<sigma>)" and r: "Fun f2 ts = ?rem_nats (?add_nats r \<cdot> \<sigma>)" by (force elim: subst.closure.cases)
    obtain \<delta> where delta: "\<delta> = (\<lambda>v. ?rem_nats (Var (v,0) \<cdot> \<sigma>))" by auto
    {
      fix t
      have "?rem_nats (?add_nats t \<cdot> \<sigma>) = t \<cdot> \<delta>"
      proof (induct t)
        case (Var x)
        show ?case unfolding delta by (auto)
      next
        case (Fun f ts)
        then show ?case by auto
      qed
    }
    with l r have "Fun f1 ts = l \<cdot> \<delta>" and "Fun f2 ts = r \<cdot> \<delta>" by auto
    with mem have "(Fun f1 ts, Fun f2 ts) \<in> subst.closure (set R)"
      by (auto) (metis subst.closureI2)
  }
  then show ?thesis by auto
qed

definition check_decr_present :: "('f \<times> nat)list \<Rightarrow> ('f \<Rightarrow> nat list \<Rightarrow> 'f) \<Rightarrow> 'v \<Rightarrow> nat \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v \<times> nat) rule check"
where "check_decr_present sig l v c R \<equiv>
   let C = [0 ..< Suc c];
       ls = \<lambda> (f,n). concat (map (\<lambda> cs. 
                concat (map (\<lambda> i. let ci = cs ! i in if ci < c then [(l f (cs[ i:= Suc ci]),l f cs,n)] else []) [0 ..< n])
                            ) (enum_vectors_nat C n))
       in check_decr_present_aux_2 R v (concat (map ls sig))"

(* soundness of check_decr_present is proven is three steps,
   first, that one increase one component of a vector by 1,
   second, that one can increase one component of a vector arbitrarily,
   third, that one can increase all components of the vector arbitrarily (pointwise_ext is covered)
*)

lemma check_decr_present_1: 
  assumes check: "isOK(check_decr_present sig l v c R)"
  and f: "(f,n) \<in> set sig"
  and i: "i < n"
  and d: "d < c"
  and cs: "set cs \<subseteq> {0 ..< Suc c}"
  and ts: "length ts = n"
  and lcs: "length cs = n"
  shows "(Fun (l f (cs[i := Suc d])) ts, Fun (l f (cs[i := d])) ts) \<in> subst.closure (set R)"
proof -
  let ?C = "[0 ..< Suc c]"
  let ?ls = "\<lambda> (f,n). concat (map (\<lambda> cs. 
                concat (map (\<lambda> i. let ci = cs ! i in if ci < c then [(l f (cs[ i:= Suc ci]),l f cs,n)] else []) [0 ..< n])
                            ) (enum_vectors_nat ?C n))"
  let ?ll = "l f (cs[i := Suc d])"
  let ?lr = "l f (cs[i := d])"
  let ?req = "set (concat (map ?ls sig))"
  have "set (cs[i := d]) \<subseteq> {0 ..< Suc c}" using cs 
  proof (induct cs arbitrary: i)
    case (Cons e cs)
    from d have "d < Suc c" by simp
    with Cons show ?case by (cases i, auto)
  qed simp
  moreover have "\<exists>a\<in>{0..<n}.
       (?ll, ?lr, n) \<in> set (let ci = cs[i := d] ! a
              in if ci < c
                 then [(l f (cs[i := d, a := Suc ci]), l f (cs[i := d]), n)]
                 else [])"
    by (rule bexI[of _ i], auto simp: Let_def i lcs d)
  moreover have "length (cs[i := d]) = n" using lcs by simp
  ultimately have "(?ll,?lr,n) \<in> ?req"
    by (simp del: upt_Suc, intro bexI[OF _ f], simp del: upt_Suc, intro exI[of _ "cs[i := d]"], auto)
  then show ?thesis using check_decr_present_aux_2[OF check[unfolded check_decr_present_def Let_def]] ts
    unfolding Let_def by blast
qed

lemma check_decr_present_2:   
  assumes check: "isOK(check_decr_present sig Lab v c R)"
  and f: "(f,n) \<in> set sig"
  and i: "i < n"
  and d: "d < e"
  and e: "e \<le> c"
  and cs: "set cs \<subseteq> {0 ..< Suc c}"
  and ts: "length ts = n"
  and lcs: "length cs = n"
  shows "(Fun (Lab f (cs[i := e])) ts, Fun (Lab f (cs[i := d])) ts) \<in> (subst.closure (set R) \<inter> (decr_of_ord (lge_to_lgr_rel qmodel_lge (qmodel_LS sig [0..<Suc c])) label (qmodel_LS sig [0..<Suc c])))^+" (is "_ \<in> (_ \<inter> ?Ord)^+")
proof -
  from d obtain diff where "e - d = Suc diff" by (cases "e - d", auto)
  with d e have e: "e = Suc (d + diff)" and diff: "Suc (d + diff) \<le> c" by auto
  have ord: "\<And> d e :: nat. \<lbrakk>d \<le> c; d > e\<rbrakk>  \<Longrightarrow> (Fun (Lab f (cs[i := d])) ts, Fun (Lab f (cs[i := e])) ts) \<in> ?Ord"
  proof -
    fix d e :: nat
    assume ed: "e < d" and dc: "d \<le> c"
    then have ec: "e < Suc c" and dc: "d < Suc c" by auto
    have csd: "set (cs[i := d]) \<subseteq> {0 ..< Suc c}"
      by (rule set_update_subsetI[OF cs], simp add: dc)
    have cse: "set (cs[i := e]) \<subseteq> {0 ..< Suc c}"
      by (rule set_update_subsetI[OF cs], simp add: ec)    
    have csde: "cs[i := d] \<noteq> cs[i := e]" (is "?d \<noteq> ?e")
    proof
      assume "?d = ?e"
      then have "?d ! i = ?e ! i" by simp
      then show False using i[unfolded lcs[symmetric]] ed by auto
    qed
    show "(Fun (Lab f (cs[i := d])) ts, Fun (Lab f (cs[i := e])) ts) \<in> ?Ord"
      unfolding decr_of_ord_def lge_to_lgr_rel_def lge_to_lgr_def Let_def qmodel_lge_def qmodel_LS_def
    proof (intro CollectI, rule exI[of _ f], rule exI[of _ "Inl (cs[i := d])"], rule exI[of _ "Inl (cs[i := e])"], rule exI[of _ ts],
      simp add: f ts lcs pointwise_ext_iff csd cse csde del: upt_Suc)
      show "\<forall> j < n. ?e ! j \<le> ?d ! j"
      proof (intro allI impI)
        fix j
        assume "j < n"
        with ed show "?e ! j \<le> ?d ! j"
          unfolding lcs[symmetric] by (cases "j = i", auto)
      qed
    qed
  qed
  from diff have "(Fun (Lab f (cs[i := Suc (d + diff)])) ts, Fun (Lab f (cs[i := d])) ts) \<in> (subst.closure (set R) \<inter> ?Ord)^+"
  proof (induct diff)
    case 0
    then have dc1: "d < c" and dc2: "Suc d \<le> c" by auto
    from check_decr_present_1[OF check f i dc1 cs ts lcs]
    have one: "(Fun (Lab f (cs[i := Suc d])) ts, Fun (Lab f (cs[i := d])) ts) \<in> subst.closure (set R)" (is "?pair \<in> ?subst_closure") .
    have "?pair \<in> ?Ord" by (rule ord[OF dc2], simp)
    with one show ?case by force
  next
    case (Suc diff)
    then have rec: "(Fun (Lab f (cs[i := Suc (d + diff)])) ts, Fun (Lab f (cs[i := d])) ts) \<in> (subst.closure (set R) \<inter> ?Ord)^+" (is "(?m,?r) \<in> _") by auto
    from Suc(2) have dc1: "Suc (d + diff) < c" and dc2: "Suc (Suc (d + diff)) \<le> c" by auto
    from check_decr_present_1[OF check f i dc1 cs ts lcs] 
    have cs: "(Fun (Lab f (cs[i := Suc (Suc (d + diff))])) ts, ?m) \<in> subst.closure (set R)" (is "(?l,_) \<in> ?subst_closure") .
    obtain rel where rel: "?subst_closure \<inter> ?Ord = rel" by auto
    have "(?l,?m) \<in> ?Ord" by (rule ord[OF dc2], simp)
    with cs have "(?l,?m) \<in> ?subst_closure \<inter> ?Ord" by auto
    with rec show ?case unfolding rel by auto 
  qed
  with e show ?thesis by simp
qed
  
lemma check_decr_present: assumes check: "isOK(check_decr_present sig Lab v c R)"
  and f: "(f,n) \<in> set sig"
  and cs: "set cs \<subseteq> {0 ..< Suc c}"
  and ds: "set ds \<subseteq> {0 ..< Suc c}"
  and ts: "length ts = n"
  and lcs: "length cs = n"
  and gt: "fst (pointwise_ext (\<lambda> x y :: nat. (y < x, y \<le> x)) cs ds)"
  shows "(Fun (Lab f cs) ts, Fun (Lab f ds) ts) \<in> (subst.closure (set R) \<inter> (decr_of_ord (lge_to_lgr_rel qmodel_lge (qmodel_LS sig [0..<Suc c])) label (qmodel_LS sig [0..<Suc c])))^+" (is "_ \<in> (_ \<inter> ?Ord)^+")
proof -
  note check = check_decr_present_2[OF check f _ _ _ _ ts]
  let ?subst_closure = "subst.closure (set R)"
  let ?R = "?subst_closure \<inter> ?Ord"
  let ?C = "{0 ..< Suc c}"
  from gt[unfolded pointwise_ext_iff] lcs obtain i where
    lds: "length ds = n" and ids: "i < length ds" and ics: "i < length cs" and gt: "ds ! i < cs ! i"
    and ge: "\<And> i. i < length ds \<Longrightarrow> ds ! i \<le> cs ! i"  and i: "i < n" by auto
  let ?csds = "\<lambda> i. take i ds @ drop i cs"
  let ?l = "Fun (Lab f cs) ts"
  let ?r = "\<lambda> j. Fun (Lab f (?csds j)) ts"
  from lcs lds have lcsds: "\<And> j. length (?csds j) = n" by auto
  {
    fix j
    assume "j \<le> length ds"
    then have "(?l, ?r j) \<in> ?R^* \<and> set (?csds j) \<subseteq> ?C \<and> (j > i \<longrightarrow> (?l, ?r j) \<in> ?R^+)"
    proof (induct j)
      case 0
      show ?case by (simp add: cs)
    next
      case (Suc j)
      with lds
      have ind1: "(?l, ?r j) \<in> ?R^*" and ind2: "set (?csds j) \<subseteq> ?C" and ind3: "j > i \<longrightarrow> (?l, ?r j) \<in> ?R^+" and j: "j < n" by auto
      from j lcs have idd: "(?csds j)[ j := ds ! j] = ?csds (Suc j)" unfolding lds[symmetric] by (rule take_drop_update_first)
      from j lcs have idc: "(?csds j)[ j := cs ! j] = ?csds j" unfolding lds[symmetric] by (rule take_drop_update_second)
      from j cs lcs have csj: "cs ! j \<le> c" unfolding set_conv_nth by auto
      {
        assume "cs ! j > ds ! j"
        from check[OF j this csj ind2 lcsds] 
        have "(Fun (Lab f ((?csds j)[ j := cs ! j])) ts, Fun (Lab f ((?csds j)[ j := ds ! j])) ts) \<in> ?R^+" .
        then have "(?r j, ?r (Suc j)) \<in> ?R^+" by (simp only: idd idc)
      } note strict = this
      {
        assume "\<not> (cs ! j > ds ! j)"
        with j ge lds have "cs ! j = ds ! j" by force
        then have "(?csds j)[j := ds ! j] = (?csds j)[j := cs ! j]" by simp
        then have "?csds (Suc j) = ?csds j" unfolding idd idc .
        then have "(?r j, ?r (Suc j)) \<in> ?R^*" by simp
      } note non_strict = this
      from strict non_strict have non_strict: "(?r j, ?r (Suc j)) \<in> ?R^*" by (cases "cs ! j > ds ! j", auto)      
      with ind1 have "(?l, ?r (Suc j)) \<in> ?R^*" by auto
      moreover have "set (?csds (Suc j)) \<subseteq> ?C"
      proof 
        fix x
        assume "x \<in> set (?csds (Suc j))"
        then have "x \<in> set (take (Suc j) ds) \<or> x \<in> set (drop (Suc j) cs)" by auto
        then show "x \<in> ?C"
        proof
          assume "x \<in> set (drop (Suc j) cs)"
          with set_drop_subset[of "Suc j" cs] cs 
          show "x \<in> ?C" by auto
        next
          assume "x \<in> set (take (Suc j) ds)"
          with set_take_subset[of "Suc j" ds] ds
          show "x \<in> ?C" by auto
        qed
      qed
      moreover have "Suc j > i \<longrightarrow> (?l, ?r (Suc j)) \<in> ?R^+"
      proof
        assume sj: "Suc j > i"
        show "(?l, ?r (Suc j)) \<in> ?R^+"
        proof (cases "i = j")
          case False
          with sj have "j > i" by auto
          with ind3 non_strict show ?thesis by auto
        next
          case True
          from strict[OF gt[unfolded True]] ind1 show ?thesis by auto
        qed
      qed
      ultimately show ?case by blast
    qed
  }
  from this[of "length ds"] ids have "(?l, ?r (length ds)) \<in> ?R^+" by simp
  with lcs lds show ?thesis by auto
qed
      

definition "qmodel_check_decr sig v c \<equiv> \<lambda> lR. check_decr_present sig Lab v c lR 
    <+? (\<lambda> r. let display = map_vars_term (\<lambda> (_,n). (shows ''x'' \<circ> shows n) []) in 
            showsl_lit (STR ''decreasing rule '') \<circ> showsl_rule (display (fst r), display (snd r)) \<circ> showsl_lit (STR '' missing''))" 

lemma qmodel_check_decr: 
  assumes ok: "isOK(qmodel_check_decr sig v n lR)"
  shows "decr_of_ord (lge_to_lgr_rel qmodel_lge (qmodel_LS sig [0 ..< Suc n])) label (qmodel_LS sig [0 ..< Suc n])
   \<subseteq> (subst.closure (set lR) \<inter> decr_of_ord (lge_to_lgr_rel qmodel_lge (qmodel_LS sig [0 ..< Suc n])) label (qmodel_LS sig [0 ..< Suc n]))^+" (is "?Decr \<subseteq> _")
proof -
  let ?g = "\<lambda> x y :: nat. (y < x, y \<le> x)"
  let ?C = "{0 ..< Suc n}"    
  have C: "?C = insert n {0 ..< n}" by auto
  let ?labs = "\<lambda> f ts. if (f, length ts) \<in> set sig then {Inl xs |xs. set xs \<subseteq> set [0..<Suc n] \<and> length xs = length ts} else {Inl []}"
  {
    fix l r :: "(('a,nat list)lab,'b)term"
    assume mem: "(l,r) \<in> ?Decr"
    then obtain f ts lab1 lab2 where l: "l = Fun (label f (length ts) lab1) ts" and r: "r = Fun (label f (length ts) lab2) ts" 
      and neq: "lab1 \<noteq> lab2" and lab1: "lab1 \<in> ?labs f ts" and lab2: "lab2 \<in> ?labs f ts" and ll: "(lab1,lab2) \<in> {(l,l') | l l'. case (l, l') of
      (Inl cs1, Inl cs2) \<Rightarrow>
      snd (pointwise_ext ?g cs1 cs2)
      | (Inl cs1, Inr ba) \<Rightarrow> False | (Inr bb, b) \<Rightarrow> False}" (is "_ \<in> ?ll")
      unfolding qmodel_LS_def lge_to_lgr_rel_def lge_to_lgr_def qmodel_lge_def decr_of_ord_def Let_def by auto
    note mem = mem[unfolded l r] 
    let ?labs = "?labs f ts"
    from lab1 obtain cs1 where cs1: "lab1 = Inl cs1" by (cases lab1, simp, cases "(f,length ts) \<in> set sig", auto) 
    from lab2 obtain cs2 where cs2: "lab2 = Inl cs2" by (cases lab2, simp, cases "(f,length ts) \<in> set sig", auto)
    have sig: "(f,length ts) \<in> set sig"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      with lab1 lab2 neq show False unfolding cs1 cs2 by auto
    qed
    note mem = mem[unfolded cs1 cs2] 
    from ll neq
    have snd: "snd (pointwise_ext ?g cs1 cs2)" and neq: "cs1 \<noteq> cs2" unfolding cs1 cs2 by auto
    let ?pair = "(Fun (Lab f cs1) ts, Fun (Lab f cs2) ts)"
    from pointwise_ext_snd_neq_imp_fst[OF _ snd neq]
    have fst: "fst (pointwise_ext ?g cs1 cs2)" by auto
    from lab1[unfolded cs1] have cs1C: "set cs1 \<subseteq> ?C" and lcs1: "length cs1 = length ts" by (auto simp: sig)
    from lab2[unfolded cs2] have cs2C: "set cs2 \<subseteq> ?C" and lcs2: "length cs2 = length ts" by (auto simp: sig)
    from ok[unfolded qmodel_check_decr_def] 
    have "isOK(check_decr_present sig Lab v n lR)" by simp
    from check_decr_present[OF this sig cs1C cs2C refl lcs1 fst]
    have "(l,r) \<in> (subst.closure (set lR) \<inter> ?Decr)^+" unfolding l r cs1 cs2 by simp
  }
  then show ?thesis ..
qed

lemma qmodel_wf_label: "wf_label (qmodel_L F) (qmodel_LS F [0..<Suc (get_largest_element sli)])
     {x |x. x < Suc (get_largest_element sli)}"
  unfolding qmodel_L_def qmodel_LS_def sl_helper wf_label_def by auto

lemma qmodel_SN: "SN (lge_to_lgr_rel qmodel_lge U f n)" (is "SN ?r")
proof 
  fix S
  assume "\<forall> i. (S i, S (Suc i)) \<in> ?r"
  then have steps: "\<And> i. (S i, S (Suc i)) \<in> ?r" ..
  {
    fix i
    from steps[of i] obtain xs where Si: "S i = Inl xs" 
      unfolding lge_to_lgr_rel_def qmodel_lge_def lge_to_lgr_def Let_def 
      by (cases "S i", auto)
    then have "\<exists> xs. S i = Inl xs" ..
  }
  then have "\<forall> i. \<exists> xs. S i = Inl xs" ..
  from choice[OF this] obtain z where "\<And> i. S i = Inl (z i)" by auto
  with steps have steps: "\<And> i. (Inl (z i), Inl (z (Suc i))) \<in> ?r" by auto
  let ?g = "\<lambda> x y :: nat. (y < x, y \<le> x)"
  {
    fix i
    from steps[of i]
    have "snd (pointwise_ext ?g (z i) (z (Suc i)))" and "z i \<noteq> z (Suc i)"
      unfolding lge_to_lgr_rel_def qmodel_lge_def lge_to_lgr_def Let_def 
      by auto
    from pointwise_ext_snd_neq_imp_fst[OF _ this]
    have "fst (pointwise_ext ?g (z i) (z (Suc i)))" by auto
  } note steps = this
  have "SN {(ys, xs). fst (pointwise_ext ?g ys xs)}"
    by (rule pointwise_ext_SN_2[of ?g], auto simp: SN_iff_wf converse_def wf_less)
  with steps show False by auto
qed

definition pointwise_lgen :: "label_type \<Rightarrow> label_type list"
  where "pointwise_lgen ns \<equiv> concat_lists (map (\<lambda> n. [0 ..< Suc n]) ns)" 

lemma pointwise_lgen: "set (pointwise_lgen ns) = {ms. snd (pointwise_ext (\<lambda> n m. (n > m, n \<ge> m)) ns ms)}"
  unfolding pointwise_lgen_def set_concat_lists pointwise_ext_iff by auto

definition qmodel_lgen :: "label_type + 'a \<Rightarrow> (label_type + 'a) list"
  where "qmodel_lgen l \<equiv> case l of Inl ns \<Rightarrow> map Inl (pointwise_lgen ns) | _ \<Rightarrow> []"

lemma qmodel_lgen: "set (qmodel_lgen l) = {l'. qmodel_lge f n l l'}"
proof (cases l)
  case (Inr x)
  then show ?thesis unfolding qmodel_lge_def qmodel_lgen_def by auto
next
  case (Inl x)
  have "set (qmodel_lgen l) =  Inl ` {ms. snd (pointwise_ext (\<lambda>n m. (m < n, m \<le> n)) x ms)}" 
    unfolding qmodel_lgen_def Inl set_map pointwise_lgen sum.simps ..
  also have "... = {l'. case l' of Inl cs2 \<Rightarrow> snd (pointwise_ext (\<lambda>x y. (y < x, y \<le> x)) x cs2)
     | Inr ba \<Rightarrow> False}" (is "?l = ?r")
  proof -
    { 
      fix x
      assume "x \<in> ?l" then have "x \<in> ?r" by auto
    }
    moreover
    {
      fix x
      assume r: "x \<in> ?r"
      then obtain l' where x: "x = Inl l'" by (cases x, auto)
      from r have "x \<in> ?l" unfolding x by auto
    }
    ultimately show ?thesis by blast
  qed
  finally
  show ?thesis unfolding Inl qmodel_lge_def  sum.simps  split
    by blast
qed

definition
  qmodel_LS' :: "(('f, label_type) lab, label_type + ('f, label_type) lab list) labels"
where
   "qmodel_LS' \<equiv> \<lambda> _ _ x. case x of Inl _ \<Rightarrow> True | Inr _ \<Rightarrow> False"
    
definition qsli_to_sl_unsafe :: "'v \<Rightarrow> (('f :: showl,label_type)lab \<times> nat)list \<Rightarrow> (('f,label_type)lab \<times> nat)list \<Rightarrow> ('f,label_type)lab sl_inter \<Rightarrow> (('f,label_type)lab,nat,label_type + ('f,label_type)lab list,'v)sl_ops"
  where "qsli_to_sl_unsafe v F G sli \<equiv> 
  let c = get_largest_element sli; 
      C = [0..< Suc c] in
      \<lparr>
  sl_L = qmodel_L F,
  sl_LS = qmodel_LS F C,
  sl_I = sl_inter_to_inter sli,
  sl_C = C,
  sl_c = c,
  sl_check_decr = qmodel_check_decr F v c,
  sl_L'' = qmodel_L G,
  sl_LS'' = qmodel_LS',
  sl_lgen = qmodel_lgen,
  sl_LS_gen = qmodel_LS_gen F C
  \<rparr>"

definition qsli_to_sl :: "'v \<Rightarrow> (('f :: showl,label_type)lab \<times> nat)list \<Rightarrow> (('f,label_type)lab \<times> nat)list \<Rightarrow> ('f,label_type)lab sl_inter 
  \<Rightarrow> showsl + (('f,label_type)lab,nat,label_type + ('f,label_type)lab list,'v)sl_ops"
  where "qsli_to_sl v F G sli \<equiv> do {
     qmodel_check_valid sli;
     return (qsli_to_sl_unsafe v F G sli)
  }"


interpretation arith_finite_qmodel: sl_finite_impl label label_decomp qmodel_cge qmodel_lge "\<lambda> F G. qsli_to_sl v F G sli"
  unfolding sl_finite_impl_def
proof (intro allI impI conjI)
  fix F G ops f n and l l' :: "nat list + ('a,nat list)lab list"
  assume ok: "qsli_to_sl v F G sli = Inr ops" and lge: "qmodel_lge f n l l'"
  then have ops: "ops = qsli_to_sl_unsafe v F G sli" 
    by (cases "qmodel_check_valid sli", auto simp: qsli_to_sl_def)
  show "l' \<in> set (sl_lgen ops l)" 
    using lge
    unfolding ops qsli_to_sl_unsafe_def Let_def sl_ops.simps 
    unfolding qmodel_lgen[of l, of f n] by auto
next
  fix F G ops D 
  assume ok: "isOK (sl_check_decr ops D)" and "qsli_to_sl v F G sli = Inr ops"
  then have ops: "ops = qsli_to_sl_unsafe v F G sli" 
    by (cases "qmodel_check_valid sli", auto simp: qsli_to_sl_def)
  show " decr_of_ord (lge_to_lgr_rel qmodel_lge (sl_LS ops)) label (sl_LS ops)
          \<subseteq> (subst.closure (set D) \<inter>
             decr_of_ord (lge_to_lgr_rel qmodel_lge (sl_LS ops)) label
              (sl_LS ops))\<^sup>+"
    unfolding ops qsli_to_sl_unsafe_def Let_def sl_ops.simps
    by (rule qmodel_check_decr, insert ok, auto simp: ops qsli_to_sl_unsafe_def Let_def)
next
  fix F G ops
  assume ok: "qsli_to_sl v F G sli = Inr ops"
  then have ops: "ops = qsli_to_sl_unsafe v F G sli \<and> isOK(qmodel_check_valid sli)" 
    by (cases "qmodel_check_valid sli", auto simp: qsli_to_sl_def)
  note ok = ops[THEN conjunct2] 
  note ops = ops[THEN conjunct1]
  show "sl_interpr_root_same (set (sl_C ops)) (sl_c ops) (sl_I ops) qmodel_cge
        qmodel_lge (sl_L ops) label label_decomp (sl_LS ops) (sl_L'' ops) (sl_LS'' ops)"
    unfolding ops qsli_to_sl_unsafe_def Let_def sl_ops.simps sl_helper
  proof(unfold_locales, simp, rule wf_sl_inter, rule qmodel_wf_label, rule qmodel_check_valid[OF ok],
    rule qmodel_lge_wm, rule qmodel_SN, rule label_decomp_label)
    fix f n x y z
    assume one: "qmodel_lge f n x y" and two: "qmodel_lge f n y z"
    from one obtain xx where x: "x = Inl xx" by (unfold qmodel_lge_def, cases x,simp, cases y, auto)
    from one obtain yy where y: "y = Inl yy" by (unfold qmodel_lge_def, cases x,simp, cases y, auto)
    from two obtain zz where z: "z = Inl zz" by (unfold qmodel_lge_def, cases y,simp, cases z, auto)
    from one two 
    show "qmodel_lge f n x z"
      unfolding qmodel_lge_def x y z
      using pointwise_snd_trans[of _ xx yy zz] by force
  next
    show "wf_label (qmodel_L G) qmodel_LS' { x | x. x < Suc (get_largest_element sli)}"
      unfolding wf_label_def qmodel_L_def qmodel_LS'_def by auto
  next
    fix f n x 
    assume "qmodel_LS' f n x"
    then show "qmodel_lge f n x x" unfolding qmodel_lge_def qmodel_LS'_def 
      by (cases x, auto intro: pointwise_ext_refl)
  next
    show "lge_wm (sl_inter_to_inter sli) (qmodel_L G)
      {x | x. x < Suc (get_largest_element sli)} qmodel_cge qmodel_lge"
      by (rule qmodel_lge_wm)
  qed (insert qmodel_SN, auto)
qed

interpretation arith_finite_LS_qmodel: sl_finite_LS_impl label label_decomp qmodel_cge qmodel_lge "\<lambda> F G. qsli_to_sl v F G sli"
proof(unfold_locales)
  fix F G ops f n
  assume "qsli_to_sl v F G sli = Inr ops"
  then have ops: "ops = qsli_to_sl_unsafe v F G sli" 
    by (cases "qmodel_check_valid sli", auto simp: qsli_to_sl_def)
  then show "set (sl_LS_gen ops f n) = Collect (sl_LS ops f n)" unfolding ops
    by (simp add: qsli_to_sl_unsafe_def Let_def qmodel_LS_gen')
qed

datatype ('f,'v)sl_variant = Rootlab "('f \<times> nat) option" | Finitelab "'f sl_inter" | QuasiFinitelab "'f sl_inter" 'v


fun semlab_fin_tt :: "('tp,('f :: showl,label_type)lab,'v :: showl)tp_ops 
  \<Rightarrow> (('f,label_type)lab,'v)sl_variant \<Rightarrow> (('f,label_type)lab,'v) term list \<Rightarrow> (('f,label_type)lab,'v)rules \<Rightarrow> 'tp proc"
where "semlab_fin_tt J (Rootlab _) = 
           sem_lab_fin_tt (model_splitter label_decomp) label label_decomp model_cge J (slm_gen_to_sl_gen (rl_slm None))"
    | "semlab_fin_tt J (Finitelab sli) = 
           sem_lab_fin_tt (model_splitter label_decomp) label label_decomp model_cge J (slm_gen_to_sl_gen (\<lambda>_ _. return (sli_to_slm sli)))"
    | "semlab_fin_tt J (QuasiFinitelab sli v) = 
           sem_lab_fin_tt (quasi_splitter label_decomp) label label_decomp qmodel_cge J (\<lambda> F G . qsli_to_sl v F G sli)"

lemma semlab_fin_tt: assumes I: "tp_spec I"
  shows "tp_spec.sound_tt_impl I (semlab_fin_tt I sli lQ lAll)"
proof -
  interpret tp_spec I by fact
  show ?thesis
    using sl_fin_model.sem_lab_fin_tt[OF I]
      rl_fin_model.sem_lab_fin_tt[OF I]
      arith_finite_qmodel.sem_lab_fin_tt[OF I]    
    unfolding sound_tt_impl_def
    by (cases sli, auto)
qed


fun semlab_fin_proc :: "('dp,('f :: showl,label_type)lab,'v :: showl)dpp_ops \<Rightarrow> (('f,label_type)lab,'v) sl_variant \<Rightarrow> 
  (('f,label_type)lab,'v)rules \<Rightarrow> 
  (('f,label_type)lab,'v)term list \<Rightarrow> 
  (('f,label_type)lab,'v)rules \<Rightarrow> 'dp proc"
where "semlab_fin_proc J (Rootlab None) = 
           sem_lab_fin_proc label label_decomp J (slm_gen_to_sl_gen (rl_slm None))"
    | "semlab_fin_proc J (Rootlab (Some d)) = 
           sem_lab_fin_root_proc label label_decomp J (slm_gen_to_sl_gen (rl_slm (Some d)))"
    | "semlab_fin_proc J (Finitelab sli) = 
           sem_lab_fin_proc label label_decomp J (slm_gen_to_sl_gen (\<lambda>_ _. return (sli_to_slm sli)))"
    | "semlab_fin_proc J (QuasiFinitelab sli v) = 
           sem_lab_fin_quasi_root_proc label label_decomp qmodel_cge qmodel_lge J (\<lambda> F G. qsli_to_sl v F G sli)"

lemma semlab_fin_proc: assumes I: "dpp_spec I"
  shows "dpp_spec.sound_proc_impl I (semlab_fin_proc I sli lPAll lQ lRAll)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof (cases sli)
    case (Rootlab d_opt)
    show ?thesis
    proof (cases d_opt)
      case None
      show ?thesis unfolding Rootlab None semlab_fin_proc.simps
      proof (rule rl_fin_model.sem_lab_fin_model_proc[OF I])
        fix F G ops f
        assume "rl_slm None F G = Inr ops"
        then show "inj (slm_L ops f)" unfolding inj_on_def rl_slm_def Let_def
          by (cases F, auto simp: check_def)
      qed
    next
      case (Some d)
      show ?thesis unfolding Rootlab Some semlab_fin_proc.simps
      proof (rule rl_fin_model.sem_lab_fin_model_root_proc[OF I])
        fix F G ops f
        assume "rl_slm (Some d) F G = Inr ops"
        then show "inj (slm_L ops f)" unfolding inj_on_def rl_slm_def Let_def
          by (cases "[f \<leftarrow> F. f \<noteq> d]", auto simp: check_def)
      qed
    qed
  next
    case (Finitelab sl)
    show ?thesis
      unfolding Finitelab semlab_fin_proc.simps
    proof (rule sl_fin_model.sem_lab_fin_model_proc[OF I])
      fix F G ops f
      assume "Inr (sli_to_slm sl) = Inr ops"
      then show "inj (slm_L ops f)" unfolding inj_on_def sli_to_slm_def Let_def
        by auto
    qed
  next
    case (QuasiFinitelab sli v)
    show ?thesis
      unfolding QuasiFinitelab semlab_fin_proc.simps
      by (rule arith_finite_LS_qmodel.sem_lab_fin_quasi_root_proc[OF I])
  qed
qed

end
