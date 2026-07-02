(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Flat_Context_Closure_Impl
imports
  Flat_Context_Closure
  Framework.QDP_Framework_Impl
  Auxx.Map_Choice
begin

definition fresh_vars_list :: "nat \<Rightarrow> string list \<Rightarrow> string list" where
  "fresh_vars_list n tabus \<equiv> fresh_strings_list ''x'' 0 tabus n"

lemma fresh_vars_list_sound[simp]:
  "fresh_vars_list n tabus = fresh_vars n (set tabus)"
  unfolding fresh_vars_list_def fresh_vars_def by auto

lemma flat_ctxt_i_fresh_vars_list_conv[simp]:
  "flat_ctxt_i (map Var (fresh_vars_list n tabus)) =
    flat_ctxt_i (map Var (fresh_vars n (set tabus)))"
  by (intro ext) (simp add: flat_ctxt_i_def)

lemma fresh_vars_list_fresh: "set (fresh_vars_list n vs) \<inter> set vs = {}"
  using fresh_name_gen_for_strings_list[of "''x''" 0]
  unfolding fresh_vars_list_def fresh_name_gen_list_def by auto

lemma fresh_vars_list_length: "length (fresh_vars_list n vs) = n"
  using fresh_name_gen_for_strings_list[of "''x''" 0]
  unfolding fresh_name_gen_list_def fresh_vars_list_def by simp

lemma fresh_vars_list_distinct: "distinct (fresh_vars_list n vs)"
  using Var_inj[of "fresh_strings_list ''x'' 0 vs n"]
  fresh_name_gen_for_strings_list[of "''x''" 0]
  distinct_map[of "Var" "fresh_strings_list ''x'' 0 vs n",symmetric]
  unfolding fresh_name_gen_list_def fresh_vars_list_def by auto

definition
  flat_ctxts_list :: "string list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, string) ctxt list"
where
  "flat_ctxts_list tabus fs \<equiv> concat (map (\<lambda>(f, n). (
    let xs = map Var (fresh_vars_list n tabus) in
    map (flat_ctxt_i xs f) [(0::nat)..<n]
  )) fs)"

lemma flat_ctxts_list_sound[simp]:
  assumes "distinct fs"
  shows "set (flat_ctxts_list tabus fs) = flat_ctxts (set tabus) (set fs)"
  using assms by (induct fs) (auto simp: flat_ctxts_list_def flat_ctxts_def)

definition
  flat_ctxt_closure_list :: "('f \<times> nat) list \<Rightarrow> ('f, string) rules \<Rightarrow> ('f, string) rules"
where
  "flat_ctxt_closure_list fs trs \<equiv> (
    let fcs       = flat_ctxts_list (vars_trs_list trs) fs in
    let (ras, rs) = partition (\<lambda>(l, r). root l \<noteq> root r) trs in
    concat (map (\<lambda>(l, r). map (\<lambda>C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)) fcs) ras) @ rs)"

lemma flat_ctxt_closure_list_sound_1[simp]: 
  assumes "distinct fs"
  shows "set (
    concat (map (\<lambda>(l, r).
      map (\<lambda>C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)) (flat_ctxts_list (vars_trs_list trs) fs)
    ) (fst (partition (\<lambda>(l, r). root l \<noteq> root r) trs)))
  ) = (\<Union>(l, r)\<in>(set trs)a.
    {(C\<langle>l\<rangle>, C\<langle>r\<rangle>) | C. C \<in> flat_ctxts (vars_trs (set trs)) (set fs)}
  )"
proof -
  let ?C = "\<lambda>(l,r)C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)"
  let ?ra = "fst(partition (\<lambda>(l, r). root l \<noteq> root r) trs)"
  let ?fcs = "flat_ctxts_list (vars_trs_list trs) fs"
  have "set (concat (map (\<lambda>(l, r). map (?C(l, r)) ?fcs) ?ra)) =
    (\<Union>x\<in>set(map (\<lambda>(l, r). map (?C(l, r)) ?fcs) ?ra). set x)" by simp
  also have "\<dots> = (\<Union>x\<in>(\<lambda>(l, r). map (?C(l, r)) ?fcs) ` set ?ra. set x)" by simp
  also have "\<dots> = (\<Union>(l, r)\<in>set ?ra. set((\<lambda>(l, r). map (?C(l, r)) ?fcs) (l, r)))" by best
  also have "\<dots> = (\<Union>(l, r)\<in>set ?ra. set(map (\<lambda>C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)) ?fcs))" by simp
  also have "\<dots> = (\<Union>(l, r)\<in>set ?ra. {(C\<langle>l\<rangle>, C\<langle>r\<rangle>) | C. C \<in> set (?fcs)})" by auto
  also have "\<dots> = (\<Union>(l, r)\<in>(set trs)a. {(C\<langle>l\<rangle>, C\<langle>r\<rangle>) | C. C \<in> set (?fcs)})"
    using root_altering_list[of "trs"] by simp
  finally show ?thesis
  using flat_ctxts_list_sound[of "fs" "vars_trs_list trs",OF \<open>distinct fs\<close>] by auto
qed

lemma flat_ctxt_closure_list_sound[simp]:
  assumes "distinct fs"
  shows "set (flat_ctxt_closure_list fs trs) = FC (set fs) (set trs)"
proof -
  let ?fcs = "flat_ctxts_list (vars_trs_list trs) fs"
  let ?ras = "fst(partition (\<lambda>(l, r). root l \<noteq> root r) trs)"
  let ?rs  = "snd(partition (\<lambda>(l, r). root l \<noteq> root r) trs)"
  have a: "set (
    let fcs       = ?fcs in
    let (ras, rs) = partition (\<lambda>(l, r). root l \<noteq> root r) trs in
    concat (map (\<lambda>(l, r). map (\<lambda>C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)) fcs) ras) @ rs) =
    set (concat (map (\<lambda>(l, r). map (\<lambda>C. (C\<langle>l\<rangle>, C\<langle>r\<rangle>)) ?fcs) ?ras)) \<union> set ?rs"
    by simp
  show ?thesis
    unfolding flat_ctxt_closure_list_def flat_ctxt_closure_def
    unfolding a
    unfolding flat_ctxt_closure_list_sound_1[OF \<open>distinct fs\<close>]
    unfolding root_altering_list_aux by simp
qed

(* Closure under Flat Contexts *)
definition
  check_rule_preserving ::
    "('f:: showl, 'v:: showl) ctxt list
     \<Rightarrow> ('f, 'v) rule list
     \<Rightarrow> ('f, 'v) rule
     \<Rightarrow> showsl check"
where
  "check_rule_preserving fcs rs' rule \<equiv> (
     check ((Bex (set rs') (instance_rule rule)) \<or> (\<forall>C\<in>set fcs. Bex (set rs') (instance_rule (C\<langle>fst rule\<rangle>, C\<langle>snd rule\<rangle>))))
       (showsl_lit (STR ''the rule '') \<circ> showsl_rule rule \<circ>
         showsl_lit (STR '' is neither contained in the resulting set of rules nor closed under all flat contexts\<newline>''))
   )"

definition
  check_rule_reflecting ::
    "('f:: showl, 'v:: showl) ctxt list
     \<Rightarrow> ('f, 'v) rule list
     \<Rightarrow> ('f, 'v) rule
     \<Rightarrow> showsl check"
where
  "check_rule_reflecting fcs rs rule \<equiv> (
     check (\<exists>(l, r)\<in>set rs. \<exists>C\<in>set (\<box> # fcs). fst rule = C\<langle>l\<rangle> \<and> snd rule = C\<langle>r\<rangle>)
       (showsl_lit (STR ''the rule '') \<circ> showsl_rule rule \<circ>
         showsl_lit (STR '' is neither contained in the original set of rules nor obtained by applying a flat context\<newline>''))
   )"

lemma check_rule_preserving_sound:
  "isOK (check_rule_preserving fcs rs' (l, r)) \<Longrightarrow>
   (Bex (set rs') (instance_rule (l, r))) \<or> (\<forall>C\<in>set fcs. Bex (set rs') (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
  unfolding check_rule_preserving_def by force

lemma check_rule_reflecting_sound:
  assumes "isOK (check_rule_reflecting fcs rs (l, r))"
  shows "\<exists>(u, v) \<in> set rs.\<exists>C\<in>set(\<box>#fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
proof -
  from assms have "\<exists>(u, v)\<in>set rs. \<exists>C\<in>set (\<box> # fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
    unfolding check_rule_reflecting_def by simp
  then show ?thesis .
qed

lemma check_rules_preserving_sound:
  assumes "isOK (check_allm (check_rule_preserving fcs lR) R)"
  shows "\<forall>(l, r)\<in>set R. 
    (Bex (set lR) (instance_rule (l, r))) \<or> (\<forall>C\<in>set fcs. Bex (set lR) (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
proof -
  from assms have "\<forall>rule\<in>set R. isOK (check_rule_preserving fcs lR rule)" by simp
  then show ?thesis using check_rule_preserving_sound by best
qed

lemma check_rules_reflecting_sound:
  assumes "isOK (check_allm (check_rule_reflecting fcs R) lR)"
  shows "\<forall>(l, r)\<in>set lR. \<exists>(u, v)\<in>set R. \<exists>C\<in>set (\<box>#fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
proof -
  from assms have "\<forall>rule\<in>set lR. isOK(check_rule_reflecting fcs R rule)" by simp
  then show ?thesis using check_rule_reflecting_sound[of fcs R] by fast
qed

definition
  check_flat_ctxt :: "('v:: showl) list \<Rightarrow> ('f:: showl, 'v) ctxt \<Rightarrow> showsl check"
where
  "check_flat_ctxt vs C \<equiv>
     (case C of
       More f ss1 \<box> ss2 \<Rightarrow> do {
         let ss = ss1 @ ss2;
         check (distinct ss) (showsl C \<circ> showsl_lit (STR '' contains duplicate variables\<newline>''));
         check (\<forall>s\<in>set ss. is_Var s) (showsl C
           \<circ> showsl_lit (STR '' is not flat, i.e., has depth greater than one\<newline>''));
         check (\<forall>t\<in>set (ss1 @ ss2). \<not> (the_Var t) \<in> set vs) (showsl C \<circ>
           showsl_lit (STR '' has to contain only fresh variables\<newline>''))
       }
     | _ \<Rightarrow> error (showsl C \<circ> showsl_lit (STR '' is not a flat context\<newline>'')))"

fun
  is_flat_ctxt_list :: "'v list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> bool"
where
  "is_flat_ctxt_list vs fas (More f ss1 \<box> ss2) = (let ss = ss1 @ ss2 in (
     (f, Suc (length ss)) \<in> set fas
       \<and> (\<forall>s\<in>set ss. is_Var s) \<and> distinct ss \<and> list_inter (map the_Var ss) vs = []
   ))"
| "is_flat_ctxt_list vs fas _ = False"

lemma is_flat_ctxt_list_cases[consumes 1,case_names True]:
  assumes "is_flat_ctxt_list vs fas C" and "\<And>f ss1 ss2. C = More f ss1 \<box> ss2 \<Longrightarrow> P" shows "P"
  using assms by (cases rule: is_flat_ctxt_list.cases[of "(vs,fas,C)"]) (auto simp: Let_def)

lemma is_flat_ctxt_list_sound:
  "is_flat_ctxt_list vs fas C = is_flat_ctxt (set vs) (set fas) C"
proof
  assume fc: "is_flat_ctxt_list vs fas C" then show "is_flat_ctxt (set vs) (set fas) C"
  proof (cases rule: is_flat_ctxt_list_cases)
    case (True f ss1 ss2)
    from fc have "(f,Suc(length(ss1@ss2))) \<in> set fas"
      and "\<forall>s\<in>set (ss1 @ ss2). is_Var s" and "distinct (ss1 @ ss2)"
      and "set (map the_Var (ss1 @ ss2)) \<inter> set vs = {}"
      unfolding True set_list_inter[symmetric] by (auto simp: Let_def)
    moreover have "set (map the_Var (ss1 @ ss2)) = vars_ctxt C" unfolding True
      using terms_to_vars[OF \<open>\<forall>s\<in>set (ss1 @ ss2). is_Var s\<close>] by (simp add: Let_def)
    ultimately show ?thesis unfolding True by simp
  qed
next
  assume fc: "is_flat_ctxt (set vs) (set fas) C" then show "is_flat_ctxt_list vs fas C"
  proof (cases rule: is_flat_ctxt_cases)
    case (True f ss1 ss2)
    from fc have "(f, Suc (length (ss1 @ ss2))) \<in> set fas"
      and "\<forall>s\<in>set (ss1 @ ss2). is_Var s" and "distinct (ss1 @ ss2)"
      and "list_inter (map the_Var (ss1 @ ss2)) vs = []"
      unfolding True
      using terms_to_vars[of "ss1 @ ss2"] set_list_inter[of "map the_Var (ss1@ss2)" "vs"] 
      by (auto simp del: set_list_inter simp: Let_def)
    then show ?thesis unfolding True by simp
  qed
qed

definition
  check_flat_ctxt_complete :: "('f:: showl, 'v:: showl) ctxt list \<Rightarrow> ('f \<times> nat) \<Rightarrow> showsl check"
where
  "check_flat_ctxt_complete fcs fa \<equiv>
     check (\<forall>i\<in>set [0..<snd fa]. \<exists>C\<in>set fcs. hole_at (snd fa) i (fst fa) C)
       (showsl_lit (STR ''the list of flat contexts is incomplete\<newline>''))"

definition
  check_is_flat_ctxt ::
    "('v:: showl) list \<Rightarrow> ('f:: showl \<times> nat) list \<Rightarrow> ('f, 'v) ctxt \<Rightarrow> showsl check"
where
  "check_is_flat_ctxt vs fas C \<equiv> (
     check (is_flat_ctxt_list vs fas C) (showsl C \<circ> showsl_lit (STR '' is not a flat context\<newline>'')))"

lemma check_is_flat_ctxt_sound:
  assumes "isOK (check_allm (check_is_flat_ctxt vs fas) fcs)"
  shows "\<forall>C\<in>set fcs. is_flat_ctxt (set vs) (set fas) C"
proof -
  from assms have "\<forall>C\<in>set fcs. is_flat_ctxt_list vs fas C"
    by (auto simp add: check_is_flat_ctxt_def)
  then show ?thesis unfolding is_flat_ctxt_list_sound .
qed

lemma check_flat_ctxt_complete_sound:
  assumes "isOK (check_allm (check_flat_ctxt_complete fcs) F)"
  shows "\<forall>(f, n) \<in> set F. \<forall>i<n. \<exists>ss1 ss2.
    More f ss1 \<box> ss2 \<in> set fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
proof (intro ballI2 allI impI)
  fix f n i assume "(f, n) \<in> set F" and "i < n"
  with assms have "\<exists>C\<in>set fcs. hole_at n i f C"
    using check_flat_ctxt_complete_def[of fcs "(f, n)"] by auto
  then obtain C where "C \<in> set fcs" and C: "hole_at n i f C" by auto
  from C show "\<exists>ss1 ss2. More f ss1 \<box> ss2 \<in> set fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
  proof (cases rule: hole_at.cases[of "(n, i, f, C)"])
    case (1 n' i' f' g ss1 ss2) with \<open>C \<in> set fcs\<close> and C show ?thesis by auto
  next
    case ("2_1" n' i' f') with C show ?thesis by simp
  next
    case ("2_2" n' i' f' g ss1 h ts1 D ts2 ss2) with C show ?thesis by simp
  qed
qed

definition
  partition_rules ::
    "('f, 'v) ctxt list \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "partition_rules Cs R \<equiv>
    partition (\<lambda> lr. (\<exists> (u, v) \<in> set R. \<exists> C \<in> set (\<box> # Cs). lr = (C\<langle>u\<rangle>, C\<langle>v\<rangle>)))"

(* silently drops strategy *)
definition fcc_tt ::
  "('tp, 'f:: showl, 'v:: showl) tp_ops \<Rightarrow>
   ('f, 'v) ctxt list \<Rightarrow> ('f, 'v) rules \<Rightarrow> 'tp \<Rightarrow> 'tp result"
where
  "fcc_tt I fcs cRb tp \<equiv>
    let
      R   = tp_ops.R I tp;
      Rw   = tp_ops.Rw I tp;
      nfs  = tp_ops.nfs I tp;
      Rb  = R @ Rw;
      (cR,cRw) = partition_rules fcs R cRb;
      Q   = tp_ops.Q I tp;
      vs  = vars_trs_list Rb;
      fas = funas_trs_list Rb
    in
    check_return (do {
      check (fcs \<noteq> [])
        (showsl_lit (STR ''at least one flat context is required for flat context closure\<newline>''));
      check_allm (check_flat_ctxt vs) fcs;
      check_allm (check_is_flat_ctxt vs fas) fcs;
      check_allm (check_flat_ctxt_complete fcs) fas;
      check_allm (check_rule_preserving fcs cR) R;
      check_allm (check_rule_preserving fcs cRb) Rw
    }) (tp_ops.mk I nfs [] cR cRw)"


context tp_spec begin

lemma check_fcc_tt[simp]:
  assumes ok: "fcc_tt I fcs Rb' tp = return tp'"
  shows "Flat_Context_Closure.fcc_tt (set fcs) (qreltrs tp) (qreltrs tp')"
proof -
  let ?R  = "set (R tp)"
  let ?Rw = "set (Rw tp)"
  let ?Rb = "?R \<union> ?Rw"
  let ?Q = "set (Q tp)"
  let ?Rb' = "set Rb'"
  let ?nfs = "NFS tp"
  obtain R' Rw' where part: "partition_rules fcs (R tp) Rb' = (R',Rw')" by force
  let ?R' = "set R'"
  let ?Rw' = "set Rw'"
  note cond = assms[unfolded fcc_tt_def Let_def part split, simplified]
  from part have Rb': "?Rb' = ?R' \<union> ?Rw'" unfolding partition_rules_def by auto
  from cond have "tp' = mk ?nfs [] R' Rw'" by (simp add: fcc_tt_def Let_def)
  then have tp': "qreltrs tp' = (?nfs,{}, ?R', ?Rw')"
    by (simp add: set_empty[symmetric] tp_spec_sound mk_simps)
  have tp: "qreltrs tp = (?nfs,?Q, ?R, ?Rw)" by (simp add: tp_spec_sound)
  have "Flat_Context_Closure.fcc_tt_cond (set fcs) ?R ?R' ?Rw ?Rw'"
  proof -
    let ?F  = "funas_trs ?Rb"
    let ?fs = "funas_trs_list (R tp @ Rw tp)"
    have "fcs \<noteq> []" using cond by simp
    moreover have "\<forall>C\<in>set fcs. is_flat_ctxt (vars_trs ?Rb) ?F C"
    proof -
      from cond
        have "isOK (check_allm (check_is_flat_ctxt
          (vars_trs_list (R tp @ Rw tp)) ?fs) fcs)" by simp
      from check_is_flat_ctxt_sound[OF this] show ?thesis by simp
    qed

    moreover have "\<forall>(g, n)\<in>?F. \<forall>i<n. \<exists>ss1 ss2.
      More g ss1 \<box> ss2 \<in> set fcs \<and> length ss1 = i \<and> length ss2 = n - i - 1"
    proof -
      from cond have "isOK (check_allm (check_flat_ctxt_complete fcs) ?fs)" by simp
      from check_flat_ctxt_complete_sound[OF this] show ?thesis by simp
    qed

    moreover have "\<forall>(l, r)\<in>?R. Bex ?R' (instance_rule (l, r)) \<or> (\<forall>C\<in>set fcs. Bex ?R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    proof -
      from cond have "isOK (check_allm (check_rule_preserving fcs R') (R tp))"
        by simp
      from check_rules_preserving_sound[OF this] show ?thesis by simp
    qed

    moreover have "\<forall>(l, r)\<in>?Rw. Bex ?Rb' (instance_rule (l, r)) \<or> (\<forall>C\<in>set fcs. Bex ?Rb' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    proof -
      from cond have "isOK (check_allm (check_rule_preserving fcs Rb') (Rw tp))"
        by simp
      from check_rules_preserving_sound[OF this] show ?thesis by simp
    qed

    ultimately show ?thesis unfolding fcc_tt_cond_def Let_def Rb' by blast
  qed
  then show ?thesis unfolding tp tp' by simp
qed

lemma fcc_tt:
  "sound_tt_impl (fcc_tt I fcs Rb')"
  unfolding sound_tt_impl_def
proof (intro allI impI)
  fix tp tp'
  assume ok: "fcc_tt I fcs Rb' tp = return tp'"
    and SN: "SN_qrel (qreltrs tp')"
  from SN fcc_tt_sound[OF check_fcc_tt[OF ok, unfolded tp_spec_sound]]
  show "SN_qrel (qreltrs tp)" by simp
qed

end

definition
  block_trs_list :: "'f \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "block_trs_list f trs = map (block_rule f) trs"

lemmas block_defs = block_trs_list_def block_rule_def

definition
  check_superset_of_blocked ::
    "'f:: showl \<Rightarrow> ('f, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "check_superset_of_blocked f P' P \<equiv> (
     check_all (\<lambda>rule. (block_rule f rule) \<in> set P') P
       <+? (\<lambda>rule. showsl_lit (STR ''the rule '') \<circ> showsl_rule (block_rule f rule)
         \<circ> showsl_lit (STR '' is missing\<newline>''))
       <+? (\<lambda>e. showsl_trs P  \<circ> showsl_lit (STR ''is not a subset of'') \<circ>
         showsl_trs P' \<circ> e \<circ> showsl_nl))"

lemma check_superset_of_blocked_sound:
  assumes "isOK (check_superset_of_blocked f P' P)"
  shows "set (block_trs_list f P) \<subseteq> set P'"
proof (rule subrelI)
  from assms[unfolded check_superset_of_blocked_def]
  have a: "\<forall>r\<in>set P. block_rule f r \<in> set P'" by simp
  fix s t assume "(s, t) \<in> set (block_trs_list f P)"
  then have "(s, t) \<in> block_rule f ` set P" unfolding block_defs by simp
  then obtain r where st: "block_rule f r = (s, t)" and "r \<in> set P" by auto
  with a have "block_rule f r \<in> set P'" by blast
  then show "(s, t) \<in> set P'" unfolding st .
qed

definition
  check_no_defined_root_defined :: "(('f:: showl) \<times> nat) list \<Rightarrow> ('f, 'v:: showl) term \<Rightarrow> showsl check"
where
  "check_no_defined_root_defined F t = check (\<not> (the (root t)) \<in> set F) (
     showsl_lit (STR ''the root of '') \<circ> showsl t \<circ> showsl_lit (STR '' is defined''))"

lemma check_no_defined_root_defined[simp]:
  "isOK (check_no_defined_root_defined (defined_list R) t) =
    (\<not> defined (set R) (the (root t)))"
  unfolding check_no_defined_root_defined_def using set_defined_list by force

definition
  unblock_trs_list :: "'f \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "unblock_trs_list f trs \<equiv> map (unblock_rule f) trs"

lemma block_trs_list_sound[simp]: "set (block_trs_list f R) = block_rule f ` set R"
  unfolding block_trs_list_def by (induct R) simp_all

lemma unblock_block_trs_list_ident[simp]:
  "unblock_trs_list f (block_trs_list f trs) = trs"
  unfolding unblock_trs_list_def block_trs_list_def
  by (induct trs) (simp_all add: unblock_rule_def block_rule_def)

lemma block_trs_list_unblock_trs_list[simp]:
  assumes "set (block_trs_list f P) \<subseteq> set P'"
  shows "set P \<subseteq> set (unblock_trs_list f P')"
proof (rule subrelI)
  fix s t assume "(s, t) \<in> set P"
  then have "block_rule f (s, t) \<in> block_rule f ` set P" by simp
  with assms have "block_rule f (s, t) \<in> set P'" unfolding block_defs by auto
  then have "unblock_rule f (block_rule f (s, t)) \<in> unblock_rule f ` set P'" by simp
  then show "(s, t) \<in> set (unblock_trs_list f P')"
    unfolding block_rule_def unblock_rule_def unblock_trs_list_def by simp
qed

definition partition_pairs :: "'f \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<times> ('f,'v)rules"
 where "partition_pairs f P \<equiv> partition (\<lambda> r. unblock_rule f r \<in> set P)"

definition
  fcc_proc_cond ::
    "('dpp, 'f:: showl, 'v:: showl) dpp_ops \<Rightarrow>
    'f \<Rightarrow> ('f, 'v) ctxt list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    'dpp proc"
where
  "fcc_proc_cond I f fcs P' Pw' R' Rw' dpp \<equiv> 
    let P  = dpp_ops.P I dpp;
        Pw = dpp_ops.Pw I dpp;
        R = dpp_ops.R I dpp;
        Rw = dpp_ops.Rw I dpp;
        nfs = dpp_ops.nfs I dpp;
        m = dpp_ops.minimal I dpp;
        new_dpp = dpp_ops.mk I nfs m P' Pw' [] R' Rw'
 in

    check_return (do {

    let Pb = list_union P Pw;
    let Rb = list_union R Rw;
    let Rb' = list_union R' Rw';
    let fa   = (f, 1);
    let Cf   = More f [] \<box> [];
    let fcs' = Cf # fcs;
    let vs   = vars_trs_list Rb;
    let fs   = list_union (funas_trs_list Rb) (funas_args_trs_list Pb);
    let fas  = fa # fs;
    let ds   = defined_list Rb;

    check (\<not> fa \<in> set ds) (showsl f \<circ> showsl_lit (STR ''is not fresh\<newline>''));
    check_wf_trs Rb;
    check_allm (\<lambda>r.
      check_no_var (fst r) >>
      check_no_var (snd r) >>
      check_no_defined_root_defined ds (snd r)) Pb;
    check_allm (check_flat_ctxt vs) fcs';
    check_allm (check_is_flat_ctxt vs fas) fcs';
    check_allm (check_flat_ctxt_complete fcs') fas;
    check_allm (check_rule_preserving fcs' R') R;
    check_allm (check_rule_preserving fcs' Rb') Rw;
    check_allm (check_rule_reflecting fcs' Rb) Rb';
    check_superset_of_blocked f P' P;
    check_superset_of_blocked f Pw' Pw
  } <+?
  (\<lambda> e. showsl_lit (STR ''problem when checking flat context closure conditions to switch from\<newline>'') \<circ> 
  showsl_dpp I dpp \<circ> showsl_lit (STR ''\<newline>to the DP problem\<newline>'')  
  \<circ> showsl_dpp I new_dpp \<circ> showsl_nl \<circ> e)) 
     new_dpp"

definition
  fcc_proc ::
    "('dpp, 'f:: showl, 'v:: showl) dpp_ops \<Rightarrow>
    'f \<Rightarrow> ('f, 'v) ctxt list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow>
    'dpp proc"
where
  "fcc_proc I f fcs Pb' Rw' dpp \<equiv> 
    let P  = dpp_ops.P I dpp;
        Q  = dpp_ops.Q I dpp;
        R = dpp_ops.R I dpp;
        (P',Pw') = partition_pairs f P Pb'
     in do {
         check (Q = []) (showsl_lit (STR ''Q is not empty''));
         check (R = []) (showsl_lit (STR ''strict rules not allowed''));
         check_left_linear_trs (dpp_ops.Rw I dpp);
         fcc_proc_cond I f fcs P' Pw' [] Rw' dpp
      }"

(* Pb' and Rb' are the resulting pairs and rules of applying fcc,
   Ps and Rs are the strict rules for the split *)
definition
  fcc_split_proc ::
    "('dpp, 'f::{showl,compare_order}, 'v::{showl,compare_order}) dpp_ops \<Rightarrow>
    'f \<Rightarrow> ('f, 'v) ctxt list \<Rightarrow>
    ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
    'dpp \<Rightarrow> ('dpp \<times> 'dpp) result"
where
  "fcc_split_proc I f fcs Pb' Rb' Ps Rs dpp \<equiv> 
    let P  = dpp_ops.P I dpp;
        Pw = dpp_ops.Pw I dpp;
        R = dpp_ops.R I dpp;
        Rw = dpp_ops.Rw I dpp;
        Q = dpp_ops.Q I dpp;
        nfs = dpp_ops.nfs I dpp;
        m = dpp_ops.minimal I dpp;
        Pb = list_union P Pw;
        Rb = Rw;
        Pns = ceta_list_diff Pb Ps;
        Rns = ceta_list_diff Rb Rs;
        (P',Pw') = partition_pairs f Ps Pb';
        (R',Rw') = partition_rules (More f [] \<box> [] # fcs) Rs Rb';
        two = dpp_ops.mk I nfs m (ceta_list_diff P Ps) (ceta_list_diff Pw Ps) [] [] Rns;
        dpp_mid = dpp_ops.mk I nfs m Ps Pns [] Rs Rns
     in do {
         check_subseteq Ps Pb <+? (\<lambda> r. showsl_lit (STR ''pair '') \<circ> showsl_rule r \<circ> showsl_lit (STR '' should be deleted but is not present''));
         check_subseteq Rs Rb <+? (\<lambda> r. showsl_lit (STR ''rule '') \<circ> showsl_rule r \<circ> showsl_lit (STR '' should be deleted but is not present''));
         check (Q = []) (showsl_lit (STR ''Q is not empty\<newline>''));
         check (R = []) (showsl_lit (STR ''strict rules not allowed\<newline>''));
         check_left_linear_trs Rw;
         fcc_proc_cond I f fcs P' Pw' R' Rw' dpp_mid
      } \<bind> (\<lambda> one. return (one,two))"

context dpp_spec
begin

lemma fcc_proc_cond:
  assumes "fcc_proc_cond I f fcs P' Pw' R' Rw' d = return d'"
  shows "Flat_Context_Closure.fcc_proc f fcs (dpp d) (dpp d') \<and> dpp d' = (NFS d,M d,set P', set Pw', {}, set R', set Rw')"
proof -
  let ?P   = "set (P d)"
  let ?P'  = "set P'"
  let ?Pw  = "set (Pw d)"
  let ?Pw' = "set Pw'"
  let ?R   = "set (R d)"
  let ?Rw   = "set (Rw d)"
  let ?R' = "set R'"
  let ?Rw' = "set Rw'"
  let ?Q = "set (Q d)"
  note cond = assms[unfolded fcc_proc_cond_def Let_def split]
  let ?R'  = "set R'"
  let ?Rb = "?R \<union> ?Rw"
  let ?Rb' = "?R' \<union> ?Rw'"
  let ?nfs = "NFS d"
  let ?m = "M d"
  from cond have "d' = dpp_ops.mk I ?nfs ?m P' Pw' [] R' Rw'" by simp
  then have d': "dpp_ops.dpp I d' = (?nfs, ?m, ?P', ?Pw', {}, ?R', ?Rw')"
    by (simp add: dpp_spec_sound set_empty[symmetric] mk_simps)
  from cond have d: "dpp_ops.dpp I d = (?nfs,?m,?P, ?Pw, ?Q, ?R, ?Rw)" by (simp add: dpp_spec_sound)
  have "fcc_cond f fcs ?P ?Pw ?R ?Rw ?P' ?Pw' ?R' ?Rw'"
  proof -
    let ?Cf = "More f [] \<box> []"
    let ?F' = "funas_trs ?Rb \<union> funas_args_trs (?P \<union> ?Pw)"
    let ?fs = "list_union
      (funas_trs_list (list_union (dpp_ops.R I d) (dpp_ops.Rw I d)))
      (funas_args_trs_list (list_union (dpp_ops.P I d) (dpp_ops.Pw I d)))"
    let ?F  = "{(f, 1)} \<union> ?F'"
    have "wf_trs ?Rb"
      and "\<not> defined ?Rb (f, 1)"
      using cond by simp_all
    moreover have "\<forall>C\<in>set (?Cf # fcs). is_flat_ctxt (vars_trs ?Rb) ?F C"
    proof -
      from cond
        have "isOK (check_allm (check_is_flat_ctxt
          (vars_trs_list (list_union (dpp_ops.R I d) (dpp_ops.Rw I d))) ((f, 1) # ?fs)) (?Cf # fcs))" by simp
      from check_is_flat_ctxt_sound[OF this] show ?thesis by simp
    qed
    moreover have "\<forall>(g, n)\<in>?F'. \<forall>i<n. \<exists>ss1 ss2.
      More g ss1 \<box> ss2 \<in> set (?Cf # fcs) \<and> length ss1 = i \<and> length ss2 = n - i - 1"
    proof -
      from cond have "isOK (check_allm (check_flat_ctxt_complete (?Cf # fcs))
        ((f, 1) # ?fs))" by simp
      from check_flat_ctxt_complete_sound[OF this] show ?thesis by simp
    qed
    moreover have "\<forall>(l, r)\<in>?R. Bex ?R' (instance_rule (l, r)) \<or> (\<forall>C\<in>set (?Cf # fcs). Bex ?R' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    proof -
      from cond have "isOK (check_allm (check_rule_preserving (?Cf # fcs) R') (dpp_ops.R I d))"
        by simp
      from check_rules_preserving_sound[OF this] show ?thesis by simp
    qed
    moreover have "\<forall>(l, r)\<in>?Rw. Bex ?Rb' (instance_rule (l, r)) \<or> (\<forall>C\<in>set (?Cf # fcs). Bex ?Rb' (instance_rule (C\<langle>l\<rangle>, C\<langle>r\<rangle>)))"
    proof -
      from cond have "isOK (check_allm (check_rule_preserving (?Cf # fcs) (list_union R' Rw')) (dpp_ops.Rw I d))"
        by simp
      from check_rules_preserving_sound[OF this] show ?thesis by simp
    qed
    moreover have "\<forall>(l, r)\<in>?Rb'. \<exists>(u, v)\<in>?Rb. \<exists>C\<in>set (\<box> # ?Cf # fcs). l = C\<langle>u\<rangle> \<and> r = C\<langle>v\<rangle>"
    proof -
      from cond have "isOK (check_allm (check_rule_reflecting (?Cf # fcs) (list_union (R d) (Rw d))) (list_union R' Rw'))"
        by simp
      from check_rules_reflecting_sound[OF this] show ?thesis 
        by auto
    qed
    moreover have "block_rule f ` ?P \<subseteq> ?P'"
    proof -
      from cond have "isOK (check_superset_of_blocked f P' (dpp_ops.P I d))" by simp
      from check_superset_of_blocked_sound[OF this] show ?thesis by simp
    qed
    moreover have "block_rule f ` ?Pw \<subseteq> ?Pw'"
    proof -
      from cond have "isOK (check_superset_of_blocked f Pw' (dpp_ops.Pw I d))" by simp
      from check_superset_of_blocked_sound[OF this] show ?thesis by simp
    qed
    moreover have "\<forall>(s, t)\<in>set (dpp_ops.P I d) \<union> set (dpp_ops.Pw I d). is_Fun s \<and> is_Fun t"
    proof -
      from cond have "isOK (check_allm (\<lambda>r. check_no_var (fst r) >> check_no_var (snd r))
        (list_union (dpp_ops.P I d) (dpp_ops.Pw I d)))" by simp
      then show ?thesis by force
    qed
    moreover have "\<forall>(s, t)\<in>set (dpp_ops.P I d) \<union> set (dpp_ops.Pw I d).
        \<not> defined ?Rb (the (root t))"
    proof -
      from cond have "isOK (check_allm (\<lambda>r. check_no_defined_root_defined
        (defined_list (list_union (dpp_ops.R I d) (dpp_ops.Rw I d))) (snd r)) (list_union (dpp_ops.P I d) (dpp_ops.Pw I d)))"
        by simp
      then show ?thesis by force
    qed
    ultimately show ?thesis unfolding fcc_cond_def Let_def by simp
  qed
  then show ?thesis unfolding d d' by simp
qed


lemma fcc_proc:
  "sound_proc_impl (fcc_proc I f fcs Pb' Rw')"
proof
  fix d d'
  let ?P  = "set (dpp_ops.P I d)"
  let ?Pw = "set (dpp_ops.Pw I d)"
  let ?R  = "set (dpp_ops.Rw I d)"
  let ?nfs = "NFS d"
  let ?m = "M d"
  obtain P' Pw' where partP: "partition_pairs f (dpp_ops.P I d) Pb' = (P',Pw')" by force
  assume ok: "fcc_proc I f fcs Pb' Rw' d = return d'"
    and fin: "finite_dpp (dpp_ops.dpp I d')"
  note ok = ok[unfolded fcc_proc_def Let_def partP split]
  from ok have d': "fcc_proc_cond I f fcs P' Pw' [] Rw' d = Inr d'" by auto
  from ok have ll: "left_linear_trs ?R" by auto
  from ok have R: "set (R d) = {}" by auto
  from ok have Q: "set (Q d) = {}" by auto
  from fcc_proc_cond[OF d'] have proc: "Flat_Context_Closure.fcc_proc f fcs (dpp d) (dpp d')" and d': "dpp d' = (?nfs,?m,set P', set Pw', {}, {}, set Rw')" by auto
  from Q R have d: "dpp d = (?nfs,?m,set (P d), set (Pw d), {}, {}, set (Rw d))" by simp
  from fcc_proc_sound[OF proc[unfolded d' d] ll fin[unfolded d']]
  show "finite_dpp (dpp_ops.dpp I d)" unfolding d .
qed
end

lemma fcc_split_proc: assumes I: "dpp_spec I"
  and res: "fcc_split_proc I f fcs Pb' Rb' Ps Rs d = Inr (d1,d2)"
  and fin1: "finite_dpp (dpp_ops.dpp I d1)"
  and fin2: "finite_dpp (dpp_ops.dpp I d2)"
  shows "finite_dpp (dpp_ops.dpp I d)"
proof -
  interpret dpp_spec I by fact
  let ?P  = "set (P d)"
  let ?Pw = "set (Pw d)"
  let ?R  = "set (R d)"
  let ?Rw  = "set (Rw d)"
  let ?Q  = "set (Q d)"
  let ?Pb = "list_union (P d) (Pw d)"
  let ?Rb = "Rw d"
  let ?Pns = "ceta_list_diff ?Pb Ps"
  let ?Rns = "ceta_list_diff ?Rb Rs"
  let ?nfs = "NFS d"
  let ?m = "M d"
  obtain P' Pw' where p3: "partition_pairs f Ps Pb' = (P',Pw')" by force
  obtain R' Rw' where p4: "partition_rules (More f [] \<box> [] # fcs) Rs Rb' = (R',Rw')" by force
  note part = p3 p4
  note res = res[unfolded fcc_split_proc_def Let_def part split, simplified] 
  from res have ll: "left_linear_trs ?Rw" by auto
  from res have R: "?R = {}" by auto
  from res have Q: "?Q = {}" by auto
  from R Q have d: "dpp d = (?nfs,?m,?P,?Pw,{},{},?Rw)" by simp
  let ?call = "fcc_proc_cond I f fcs P' Pw' R' Rw' (mk ?nfs ?m Ps ?Pns [] Rs ?Rns)"
  from res have cond: "?call = Inr d1" by (cases ?call, auto)
  note res = res[unfolded cond, simplified]
  from res
  have d2: "d2 = mk ?nfs ?m (ceta_list_diff (P d) Ps) (ceta_list_diff (Pw d) Ps) [] [] ?Rns" by auto
  from res have subset: "set Ps \<subseteq> set ?Pb" "set Rs \<subseteq> set ?Rb" by auto
  let ?dpp1 = "(?nfs,?m,set Ps, set ?Pns, {}, set Rs, set ?Rns)"
  let ?dpp2 = "(?nfs,?m,set Ps \<inter> (?P \<union> ?Pw), ?P \<union> ?Pw - set Ps, {}, ?Rw \<inter> set Rs, ?Rw - set Rs)"
  have id: "?dpp1 = ?dpp2" using subset part R Q by auto
  from fcc_proc_cond[OF cond] 
  have proc: "Flat_Context_Closure.fcc_proc f fcs ?dpp1 (?nfs,?m,set P',set Pw',{},set R',set Rw')" and d1: "dpp d1 = (?nfs,?m,set P', set Pw', {}, set R', set Rw')" by auto
  note proc = fcc_split_proc_sound[OF proc[unfolded id] ll]
  from d2 have d2: "dpp d2 = (?nfs,?m,?P - set Ps, ?Pw - set Ps, {},{},?Rw - set Rs)"
    by auto
  note proc = proc[OF fin1[unfolded d1] fin2[unfolded d2]]
  show ?thesis unfolding d by (rule proc)
qed

end
