(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Semantic_Labeling_Impl
imports 
  Semantic_Labeling
  Framework.QDP_Framework_Impl
  TRS.Q_Restricted_Rewriting_Impl
begin

type_synonym ('f,'v)sl_check1 =
  "('f,'v)term list \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check"

type_synonym ('f,'v)sl_check2 =
  "('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check"

type_synonym ('f,'v)sl_check2s =
  "('f,'v)trs \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check"

type_synonym ('f,'v)sl_check0 =
  "('f,'v)rules \<Rightarrow> showsl check"

type_synonym ('f,'v)splitter = "('f,'v)rules \<Rightarrow> 
  ('f,'v)trs \<Rightarrow> (('f,'v)rules \<times>  ('f,'v)rules \<times>  ('f,'v)rules)"

definition quasi_splitter :: "('f,'f,'l)ldecompose \<Rightarrow> ('f,'v)splitter"
  where "quasi_splitter LD lAll uRw \<equiv> let 
  unlab = (\<lambda>lf. fst (LD lf));
  la = map (\<lambda>r. (r,map_funs_rule unlab r)) lAll;
  (D,nD) = partition (\<lambda>(r,ur). fst ur = snd ur \<and> fst r \<noteq> snd r) la;
  (Rw,R) = partition (\<lambda>(r,ur). ur \<in> uRw) nD
  in (map fst R,map fst Rw,map fst D)"

definition model_splitter :: "('f,'f,'l)ldecompose \<Rightarrow> ('f,'v)splitter"
  where "model_splitter LD lAll uRw \<equiv> let 
  unlab = (\<lambda>lf. fst (LD lf));
  la = map (\<lambda>r. (r,map_funs_rule unlab r)) lAll;
  (Rw,R) = partition (\<lambda>(r,ur). ur \<in> uRw) la
  in (map fst R,map fst Rw,[])"

definition check_sl_Q :: "('f \<Rightarrow> ('f \<times> 'l)) \<Rightarrow> ('f::showl, 'v::showl) sl_check1"
where
  "check_sl_Q LD lQ Q =
    (let u = (\<lambda>l. fst (LD l)) in 
    check_allm (\<lambda> lq. check (
      let mlq = map_funs_term u lq in
      (\<exists> q \<in> set Q. matches mlq q \<and> matches q mlq))
      (showsl_lit (STR ''unlabeling '') \<circ> showsl lq \<circ> showsl_lit (STR '' yields a term not in Q''))) lQ)"
(* 
  remark: just demanding matches mlq q does not suffice to achieve check_sl_Q lemma!
   consider Q = {f(x,x)} lQ = {f_1(a_1,a_2)}.
   Then mlq = f(a,a) which is an instance of f(x,x), so the check would be satisfied,
   but f_1(a_1,a_2) is a normal form w.r.t. lab_lhss_all Q, but not w.r.t. lQ
*)

lemma check_sl_Q:
  assumes check: "isOK(check_sl_Q LD lQ Q)"
  shows "NF_terms (set lQ) \<supseteq> NF_terms (lab_lhss_all LD (set Q))"
proof(rule NF_vars_subset, rule)
  fix q'
  assume q': "q' \<in> set lQ"
  let ?f = "(\<lambda>l. fst (LD l))"
  let ?m = "map_funs_term ?f"
  from check[unfolded check_sl_Q_def Let_def, simplified] q'
  obtain q \<sigma> \<mu> where q: "q \<in> set Q" and match: "q \<cdot> \<sigma> = ?m q'" 
    and match2: "q = ?m q' \<cdot> \<mu>" unfolding matches_iff by blast+
  let ?sm = "\<mu> \<circ>\<^sub>s \<sigma>"
  have "?m q' \<cdot> Var = q \<cdot> \<sigma>" unfolding match by simp
  also have "\<dots> = ?m q' \<cdot> ?sm" unfolding match2 by simp
  finally have "?m q' \<cdot> ?sm = ?m q' \<cdot> Var" by simp
  from term_subst_eq_rev[OF this] have sigma_mu: "\<And> x. x \<in> vars_term q' \<Longrightarrow> ?sm x = Var x" by auto
  show "\<exists>q \<in> lab_lhss_all LD (set Q). matches q' q" unfolding matches_iff
  proof (rule bexI[of _ "q' \<cdot> \<mu>"], rule exI[of _ \<sigma>])
    from term_subst_eq[of q' ?sm Var, OF sigma_mu]
    show "q' \<cdot> \<mu> \<cdot> \<sigma> = q'" by simp
  next
    show "q' \<cdot> \<mu> \<in> lab_lhss_all LD (set Q)"
    proof
      have "?m (q' \<cdot> \<mu>) = ?m q' \<cdot> map_funs_subst ?f \<mu>" by simp
      also have "\<dots> = ?m q' \<cdot> \<mu>"
      proof (rule term_subst_eq)
        fix x
        assume "x \<in> vars_term (?m q')"
        then have x: "x \<in> vars_term q'" by simp
        from sigma_mu[OF this] have "\<mu> x \<cdot> \<sigma> = Var x" unfolding subst_compose_def .
        then obtain y where "\<mu> x = Var y" by (cases "\<mu> x", auto)
        then show "map_funs_subst ?f \<mu> x = \<mu> x" by simp
      qed
      also have "\<dots> = q" unfolding match2 ..
      finally 
      show "?m (q' \<cdot> \<mu>) \<in> set Q" using q by simp 
    qed
  qed
qed

definition
  sem_lab_rel_tt ::
    "('f,'v)splitter \<Rightarrow> 
     ('f,'f,'l)ldecompose \<Rightarrow>
     ('tp, 'f::showl, 'v::showl) tp_ops \<Rightarrow>
     showsl check \<Rightarrow> (('f,'v)rules \<Rightarrow> showsl check) \<Rightarrow> 
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)term list \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     'tp proc"
where
  "sem_lab_rel_tt splitter LD I valid check_decr check_model_lab lQ lAll tp \<equiv> 
    let R = tp_ops.R I tp;
        Rw = tp_ops.Rw I tp;
        nfs = tp_ops.nfs I tp;
        (lR,lRw,D) = splitter lAll (set Rw) in
    check_return ( 
      do {
        valid; 
        let Q = tp_ops.Q I tp;
        do {
          (if nfs \<and> \<not> tp_ops.Q_empty I tp then check_wf_trs D else succeed);
          check_decr D;
          check_sl_Q LD lQ Q;
          check_model_lab (set lR) R;
          check_model_lab (set lRw) Rw
        } <+? (\<lambda>s. showsl_lit (STR ''problem with labeled TRS:\<newline>'') \<circ> s)
      })
   (tp_ops.mk I nfs lQ lR (lRw @ D))"

definition
  sem_lab_proc ::
    "('f,'f,'l)ldecompose \<Rightarrow>
     ('dpp, 'f::showl, 'v::showl) dpp_ops \<Rightarrow>
     showsl check \<Rightarrow> 
     ('f,'v)sl_check1 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)sl_check2 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     ('f,'v)term list \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_proc LD I valid check_Q' check_lab check_lab' check_model_lab lPAll lQ lRAll dpp \<equiv> 
    let R = dpp_ops.R I dpp;
        Rw = dpp_ops.Rw I dpp;
        Pw = dpp_ops.Pw I dpp;
        P = dpp_ops.P I dpp;
        nfs = dpp_ops.nfs I dpp;
        m = dpp_ops.minimal I dpp;
        (lP,lPw,_) = model_splitter LD lPAll (set Pw);
        (lR,lRw,_) = model_splitter LD lRAll (set Rw) in
    check_return ( 
      do {
        valid; 
        let Q = dpp_ops.Q I dpp;
        do {
          check (nfs \<longrightarrow> \<not> dpp_ops.Q_empty I dpp \<longrightarrow> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''well formedness required''));
          check_Q' lQ Q;
          check_sl_Q LD lQ Q;
          check_lab (set lP) P;
          check_lab (set lPw) Pw;
          check_model_lab (set lR) R;
          check_model_lab (set lRw) Rw;
          check_lab' lR R;
          check_lab' lRw Rw
        } <+? (\<lambda>s. showsl_lit (STR ''problem during labeling:\<newline>'') \<circ> s)
      })
   (dpp_ops.mk I nfs m lP lPw lQ lR lRw)"

definition
  sem_lab_root_proc ::
    "('f,'f,'l)ldecompose \<Rightarrow>
     ('dpp, 'f::showl, 'v::showl) dpp_ops \<Rightarrow>
     showsl check \<Rightarrow> 
     ('f,'v)sl_check1 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)sl_check2 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     ('f,'v)term list \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_root_proc LD I valid check_Q' check_lab check_lab' check_model_lab lPAll lQ lRAll dpp \<equiv> 
    let R = dpp_ops.R I dpp;
        Rw = dpp_ops.Rw I dpp;
        Pw = dpp_ops.Pw I dpp;
        P = dpp_ops.P I dpp;
        nfs = dpp_ops.nfs I dpp;
        m = dpp_ops.minimal I dpp;
        (lP,lPw,_) = model_splitter LD lPAll (set Pw);
        (lR,lRw,_) = model_splitter LD lRAll (set Rw) in
    check_return ( 
      do {
        valid; 
        check_allm (\<lambda>(l, r). do {
          check_no_var l;
          check_no_var r;
          check_no_defined_root (dpp_spec.is_defined I dpp) r
        }) (dpp_ops.pairs I dpp);
        check_allm (\<lambda>(l, r). check_no_var l) (dpp_ops.rules I dpp);
        let Q = dpp_ops.Q I dpp;
        do {
          check (nfs \<longrightarrow> \<not> dpp_ops.Q_empty I dpp \<longrightarrow> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''well formedness required''));
          check_Q' lQ Q;
          check_sl_Q LD lQ Q;
          check_lab (set lP) P;
          check_lab (set lPw) Pw;
          check_model_lab (set lR) R;
          check_model_lab (set lRw) Rw;
          check_lab' lR R;
          check_lab' lRw Rw
        } <+? (\<lambda>s. showsl_lit (STR ''problem during labeling:\<newline>'') \<circ> s)
      })
   (dpp_ops.mk I nfs m lP lPw lQ lR lRw)"

definition
  sem_lab_quasi_root_proc ::
    "('f,'f,'l)ldecompose \<Rightarrow>
     ('dpp, 'f::showl, 'v::showl) dpp_ops \<Rightarrow>
     showsl check \<Rightarrow> 
     ('f,'v)sl_check0 \<Rightarrow>
     ('f,'v)sl_check0 \<Rightarrow>
     ('f,'v)sl_check1 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)sl_check2 \<Rightarrow>
     ('f,'v)sl_check2s \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     ('f,'v)term list \<Rightarrow>
     ('f,'v)rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_quasi_root_proc LD I valid check_decr check_decr' check_lhss_more 
     check_lab_all check_lab_all_trs 
     check_model_lab lPAll lQ lRAll dpp \<equiv> 
    let R = dpp_ops.R I dpp;
        Rw = dpp_ops.Rw I dpp;
        Pw = dpp_ops.Pw I dpp;
        P = dpp_ops.P I dpp;
        nfs = dpp_ops.nfs I dpp;
        m = dpp_ops.minimal I dpp;
        (lP,lPw,_) = model_splitter LD lPAll (set Pw);
        (lR,lRw,D) = quasi_splitter LD lRAll (set Rw);
        qempty = dpp_ops.Q_empty I dpp in
    check_return (
      do {
        valid; 
        check (nfs \<longrightarrow> \<not> qempty \<longrightarrow> dpp_ops.wwf_rules I dpp) (showsl_lit (STR ''well formedness required''));
        check_allm (\<lambda>(l, r). do {
          check_no_var l;
          check_no_var r;
          check_no_defined_root (dpp_spec.is_defined I dpp) r
        }) (dpp_ops.pairs I dpp);
        check_allm (\<lambda>(l, r). check_no_var l) (dpp_ops.rules I dpp);
        let Q = dpp_ops.Q I dpp;
        (if nfs \<and> \<not> qempty then check_wf_trs D else succeed);
        check_decr D;
        check_decr' D;
        check_allm (\<lambda> q. check (linear_term q) (showsl_lit (STR ''Q must not contain non-linear terms''))) Q;
        do {
          check_lhss_more lQ Q;
          check_sl_Q LD lQ Q;
          check_lab_all (set lP) P;
          check_lab_all (set lPw) Pw;
          check_model_lab (set lR) R;
          check_model_lab (set lRw) Rw;
          check_lab_all_trs lR R;
          check_lab_all_trs lRw Rw
        } <+? (\<lambda>s. showsl_lit (STR ''problem during labeling:\<newline>'') \<circ> s)
      })
   (dpp_ops.mk I nfs m lP lPw lQ lR (lRw @ D))"

abbreviation (input) model_lge where "model_lge \<equiv> \<lambda> _ _ . (=)"
abbreviation (input) model_cge where "model_cge \<equiv> (=)"

lemma decr_empty: "decr_of_ord (lge_to_lgr_rel model_lge x) y z = {}"
  unfolding decr_of_ord_def lge_to_lgr_rel_def lge_to_lgr_def Let_def by auto

locale sl_interpr_impl = 
  fixes check_Q' :: "('f :: showl, 'v ::showl)sl_check1"
   and  check_lab :: "('f,'v)sl_check2s"
   and  check_lab_root :: "('f,'v)sl_check2s"
   and  check_lab_root_all :: "('f,'v)sl_check2s"
   and  check_lab' :: "('f,'v)sl_check2"
   and  check_model_lab :: "('f,'v)sl_check2s"
   and  check_lab_all_trs :: "('f,'v)sl_check2"
   and  check_lab_lhss_more :: "('f, 'v)sl_check1"
   and  check_decr :: "('f,'v)rules \<Rightarrow> showsl check"
   and  check_decr' :: "('f,'v)rules \<Rightarrow> showsl check"
   and  check_valid :: "showsl check"
   and  C :: "'c set"
   and  c :: "'c"
   and  I :: "('f,'c)inter"
   and  cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
   and  lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
   and  L :: "('f,'c,'l)label"
   and  LS :: "('f,'l)labels" 
   and  LC :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'f"
   and  LD :: "'f \<Rightarrow> ('f \<times> 'l)"
   and  L' :: "('f,'c,'l)label"
   and  LS' :: "('f,'l)labels" 
 assumes check_Q': "isOK(check_Q' lQ Q) \<Longrightarrow> NF_terms (lab_lhss I L LC C (set Q)) \<supseteq> NF_terms (set lQ)"
   and   check_lab: "isOK(check_lab lR R) \<Longrightarrow> lab_trs I L LC C (set R) \<subseteq> lR"
   and   check_lab_root: "isOK(check_lab_root lP P) \<Longrightarrow> lab_root_trs I L L' LC C (set P) \<subseteq> lP"
   and   check_lab_root_all: "isOK(check_lab_root_all lP P) \<Longrightarrow> lab_root_all_trs I L L' LC lge C (set P) \<subseteq> lP"
   and   check_lab': "\<And> lR. isOK(check_lab' lR R) \<Longrightarrow> set lR \<subseteq> lab_trs I L LC C (set R)"
   and   check_model_lab: "isOK(check_model_lab lR R) \<Longrightarrow> lab_trs I L LC C (set R) \<subseteq> lR \<and> qmodel I L LC C cge (set R)"
   and   check_lab_all_trs: "\<And> lR. isOK(check_lab_all_trs lR R) \<Longrightarrow> set lR \<subseteq> sl_interpr.Lab_all_trs LC LD LS (set R)"
   and   check_lab_lhss_more: "isOK(check_lab_lhss_more lQ Q) \<Longrightarrow> NF_terms (sl_interpr.Lab_lhss_more LC LD LS (set Q)) \<supseteq> NF_terms (set lQ)"
   and   check_decr:  "isOK(check_decr D) \<Longrightarrow> decr_of_ord (lge_to_lgr_rel lge LS) LC LS \<subseteq> (subst.closure (set D) \<inter> decr_of_ord (lge_to_lgr_rel lge LS) LC LS)^+"
   and   check_decr':  "isOK(check_decr' D) \<Longrightarrow> set D \<subseteq> decr_of_ord (lge_to_lgr_rel lge LS) LC LS"
   and   check_valid: "isOK(check_valid) \<Longrightarrow> sl_interpr_root_same C c I cge lge L LC LD LS L' LS'"
begin

lemma sem_lab_rel_tt: assumes J: "tp_spec J"
  shows "tp_spec.sound_tt_impl J (sem_lab_rel_tt splitter LD J check_valid check_decr check_model_lab lQ lAll)"
proof -
  interpret tp_spec J by fact
  show ?thesis
  proof
    fix trs trs'
    assume ok: "sem_lab_rel_tt splitter LD J check_valid check_decr check_model_lab lQ lAll trs = return trs'"
    and SN: "SN_qrel (tp_ops.qreltrs J trs')"
    let ?Q = "tp_ops.Q J trs"
    let ?R = "tp_ops.R J trs"
    let ?Rw = "tp_ops.Rw J trs"
    let ?sRw = "set ?Rw"
    let ?nfs = "NFS trs"
    obtain lR lRw D where splitter: "splitter lAll ?sRw = (lR,lRw,D)"
      by (cases "splitter lAll ?sRw", auto)
    let ?lR = "set lR"
    let ?lRw = "set lRw"
    note ok = ok[unfolded sem_lab_rel_tt_def Let_def splitter, simplified]
    from ok have valid: "isOK (check_valid)" 
      and decr: "isOK(check_decr D)"
      and Q: "isOK (check_sl_Q LD lQ ?Q)"
      and R: "isOK(check_model_lab ?lR ?R)"
      and Rw: "isOK(check_model_lab ?lRw ?Rw)"
      and wf: "?nfs \<Longrightarrow> set ?Q \<noteq> {} \<Longrightarrow> wf_trs (set D)" 
      and trs': "trs' = tp_ops.mk J ?nfs lQ lR (lRw @ D)" by auto
    from check_valid[OF valid]
    interpret sl_interpr_root_same C c I cge lge L LC LD LS L' LS' .    
    from check_model_lab[OF R] have 
      R1: "lab_trs I L LC C (set ?R) \<subseteq> ?lR"
      and R2: "qmodel I L LC C cge (set ?R)" by auto
    from check_model_lab[OF Rw] have 
      Rw1: "lab_trs I L LC C ?sRw \<union> set D \<subseteq> ?lR \<union> (?lRw \<union> set D)"
      and Rw2: "qmodel I L LC C cge ?sRw" by auto
    show "SN_qrel (tp_ops.qreltrs J trs)"
      unfolding qreltrs_sound
    proof (rule quasi_rel_SN_lab_imp_rel_SN[OF check_decr[OF decr] wf check_sl_Q[OF Q]
        SN_qrel_mono[OF subset_refl R1 Rw1] 
        R2 Rw2])
      show "SN_qrel (?nfs,set lQ, set lR, set lRw \<union> set D)"
        using SN[unfolded trs' mk_sound] by auto
    qed
  qed
qed

lemma sem_lab_proc: assumes J: "dpp_spec J"
  and L: "\<And> f. inj (L f)"
  and lge: "lge = model_lge"
  and cge: "cge = model_cge"
  shows "dpp_spec.sound_proc_impl J (sem_lab_proc LD J check_valid check_Q' check_lab check_lab' check_model_lab lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis
  proof
    fix dp dp'
    assume ok: "sem_lab_proc LD J check_valid check_Q' check_lab check_lab' check_model_lab lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    let ?Q = "dpp_ops.Q J dp"
    let ?R = "dpp_ops.R J dp"
    let ?Rw = "dpp_ops.Rw J dp"
    let ?sRw = "set ?Rw"
    let ?P = "dpp_ops.P J dp"
    let ?Pw = "dpp_ops.Pw J dp"
    let ?sPw = "set ?Pw"
    let ?nfs = "NFS dp"
    let ?m = "M dp"
    let ?splitter = "model_splitter LD"
    obtain lR lRw D where splitterR: "?splitter lRAll ?sRw = (lR,lRw,D)"
      by (cases "?splitter lRAll ?sRw", auto)
    obtain lP lPw D where splitterP: "?splitter lPAll ?sPw = (lP,lPw,D)"
      by (cases "?splitter lPAll ?sPw", auto)
    let ?lR = "set lR"
    let ?lRw = "set lRw"
    let ?lP = "set lP"
    let ?lPw = "set lPw"
    note ok = ok[unfolded sem_lab_proc_def Let_def splitterR splitterP, simplified]
    from ok have valid: "isOK (check_valid)" 
      and Q: "isOK (check_sl_Q LD lQ ?Q)"
      and Q': "isOK (check_Q' lQ ?Q)"
      and R: "isOK(check_model_lab ?lR ?R)"
      and Rw: "isOK(check_model_lab ?lRw ?Rw)"
      and R': "isOK(check_lab' lR ?R)"
      and Rw': "isOK(check_lab' lRw ?Rw)"
      and P: "isOK(check_lab ?lP ?P)"
      and Pw: "isOK(check_lab ?lPw ?Pw)"
      and wwf: "?nfs \<Longrightarrow> set ?Q \<noteq> {} \<Longrightarrow> wwf_qtrs (set ?Q) (set ?R \<union> set ?Rw)"
      and dp': "dp' = dpp_ops.mk J ?nfs ?m lP lPw lQ lR lRw" by auto
    from check_valid[OF valid]
    interpret sl_interpr_root_same C c I cge model_lge L LC LD LS L' LS' unfolding lge .
    from check_model_lab[OF R] have 
      R1: "lab_trs I L LC C (set ?R) \<subseteq> set lR"
      and R2: "qmodel I L LC C cge (set ?R)" by auto
    from check_model_lab[OF Rw] have 
      Rw1: "lab_trs I L LC C ?sRw \<subseteq> set lR \<union> set lRw"
      and Rw2: "qmodel I L LC C cge ?sRw" by auto
    show "finite_dpp (dpp_ops.dpp J dp)"
      unfolding dpp_sound      
    proof (rule sl_model_finite[OF L wwf R2 Rw2 cge decr_empty check_Q'[OF Q'] check_sl_Q[OF Q] 
        finite_dpp_mono[OF fin[unfolded dp' mk_sound] check_lab[OF P] _ refl R1]])
      show "Lab_trs (set ?P) \<union> Lab_trs (set ?Pw) \<subseteq> set lP \<union> set lPw"
        using check_lab[OF P] check_lab[OF Pw] by auto
      show "Lab_trs (set ?R) \<union> Lab_trs (set ?Rw) = set lR \<union> set lRw" (is "?left = ?right")
      proof
        show "?left \<subseteq> ?right" using R1 Rw1 by auto
        show "?right \<subseteq> ?left" using check_lab'[OF R'] check_lab'[OF Rw'] by auto
      qed
    qed
  qed
qed

lemma sem_lab_root_proc: assumes J: "dpp_spec J"
  and L: "\<And> f. inj (L f)"
  and lge: "lge = model_lge"
  and cge: "cge = model_cge"
  shows "dpp_spec.sound_proc_impl J (sem_lab_root_proc LD J check_valid check_Q' check_lab_root check_lab' check_model_lab lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis
  proof
    fix dp dp'
    assume ok: "sem_lab_root_proc LD J check_valid check_Q' check_lab_root check_lab' check_model_lab lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    let ?Q = "dpp_ops.Q J dp"
    let ?R = "dpp_ops.R J dp"
    let ?Rw = "dpp_ops.Rw J dp"
    let ?sRw = "set ?Rw"
    let ?P = "dpp_ops.P J dp"
    let ?Pw = "dpp_ops.Pw J dp"
    let ?sPw = "set ?Pw"
    let ?nfs = "NFS dp"
    let ?m = "M dp"
    let ?splitter = "model_splitter LD"
    obtain lR lRw D where splitterR: "?splitter lRAll ?sRw = (lR,lRw,D)"
      by (cases "?splitter lRAll ?sRw", auto)
    obtain lP lPw D where splitterP: "?splitter lPAll ?sPw = (lP,lPw,D)"
      by (cases "?splitter lPAll ?sPw", auto)
    let ?lR = "set lR"
    let ?lRw = "set lRw"
    let ?lP = "set lP"
    let ?lPw = "set lPw"
    note ok = ok[unfolded sem_lab_root_proc_def Let_def splitterR splitterP, simplified]
    from ok
    have nvar: "\<forall>(l, r)\<in> set ?P \<union> set ?Pw.
      is_Fun l \<and> is_Fun r" and ndef: "\<forall>(l,r) \<in> set ?P \<union> set ?Pw. \<not> defined (set ?R \<union> set ?Rw) (the (root r))"
      and nvarR: "\<forall> (l,r) \<in> set ?R \<union> set ?Rw. is_Fun l"
      by (auto simp: split_def Let_def)
    from ok have valid: "isOK (check_valid)" 
      and Q: "isOK (check_sl_Q LD lQ ?Q)"
      and Q': "isOK (check_Q' lQ ?Q)"
      and R: "isOK(check_model_lab ?lR ?R)"
      and Rw: "isOK(check_model_lab ?lRw ?Rw)"
      and R': "isOK(check_lab' lR ?R)"
      and Rw': "isOK(check_lab' lRw ?Rw)"
      and P: "isOK(check_lab_root ?lP ?P)"
      and Pw: "isOK(check_lab_root ?lPw ?Pw)"
      and wwf: "?nfs \<Longrightarrow> set ?Q \<noteq> {} \<Longrightarrow> wwf_qtrs (set ?Q) (set ?R \<union> set ?Rw)"
      and dp': "dp' = dpp_ops.mk J ?nfs ?m lP lPw lQ lR lRw" by auto
    from check_valid[OF valid]
    interpret sl_interpr_root_same C c I cge model_lge L LC LD LS L' LS' unfolding lge .
    from check_model_lab[OF R] have 
      R1: "lab_trs I L LC C (set ?R) \<subseteq> set lR"
      and R2: "qmodel I L LC C cge (set ?R)" by auto
    from check_model_lab[OF Rw] have 
      Rw1: "lab_trs I L LC C (set ?Rw) \<subseteq> set lR \<union> set lRw"
      and Rw2: "qmodel I L LC C cge (set ?Rw)" by auto
    show "finite_dpp (dpp_ops.dpp J dp)"
      unfolding dpp_sound      
    proof (rule sl_model_root_finite[OF L wwf R2 Rw2 cge decr_empty decr_empty check_Q'[OF Q'] check_sl_Q[OF Q] nvar]) 
      show "finite_dpp (?nfs,?m,Lab_root_trs (set ?P), Lab_root_trs (set ?Pw), set lQ, Lab_trs (set ?R), Lab_trs (set ?Rw))" 
      proof (rule finite_dpp_mono[OF fin[unfolded dp' mk_sound] check_lab_root[OF P] _ refl R1])
        show "Lab_root_trs (set ?P) \<union> Lab_root_trs ?sPw \<subseteq> set lP \<union> set lPw"
          using check_lab_root[OF P] check_lab_root[OF Pw] by auto
        show "Lab_trs (set ?R) \<union> Lab_trs ?sRw = set lR \<union> set lRw" (is "?left = ?right")
        proof
          show "?left \<subseteq> ?right" using R1 Rw1 by auto
          show "?right \<subseteq> ?left" using check_lab'[OF R'] check_lab'[OF Rw'] by auto
        qed
      qed
    next
      show "\<forall> (s,t) \<in> set ?P \<union> set ?Pw. \<not> defined (applicable_rules (set ?Q) (set ?R \<union> set ?Rw)) (the (root t))"
        using ndef_applicable_rules ndef by blast
    qed (insert nvarR, auto)
  qed
qed

lemma sem_lab_quasi_root_proc: assumes J: "dpp_spec J"
  shows "dpp_spec.sound_proc_impl J (sem_lab_quasi_root_proc LD J check_valid check_decr check_decr' check_lab_lhss_more 
    check_lab_root_all check_lab_all_trs check_model_lab lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis
  proof
    fix dp dp'
    assume ok: "sem_lab_quasi_root_proc LD J check_valid check_decr check_decr' check_lab_lhss_more check_lab_root_all check_lab_all_trs check_model_lab lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    let ?Q = "dpp_ops.Q J dp"
    let ?R = "dpp_ops.R J dp"
    let ?Rw = "dpp_ops.Rw J dp"
    let ?sRw = "set ?Rw"
    let ?P = "dpp_ops.P J dp"
    let ?Pw = "dpp_ops.Pw J dp"
    let ?sPw = "set ?Pw"
    let ?nfs = "NFS dp"
    let ?m = "M dp"
    let ?msplitter = "model_splitter LD"
    let ?qsplitter = "quasi_splitter LD"
    obtain lR lRw D where splitterR: "?qsplitter lRAll ?sRw = (lR,lRw,D)"
      by (cases "?qsplitter lRAll ?sRw", auto)
    obtain lP lPw D' where splitterP: "?msplitter lPAll ?sPw = (lP,lPw,D')"
      by (cases "?msplitter lPAll ?sPw", auto)
    let ?lR = "set lR"
    let ?lRw = "set lRw"
    let ?lP = "set lP"
    let ?lPw = "set lPw"
    note ok = ok[unfolded sem_lab_quasi_root_proc_def Let_def splitterR splitterP, simplified]
    from ok
    have nvar: "\<forall>(l, r)\<in> set ?P \<union> set ?Pw.
      is_Fun l \<and> is_Fun r" and ndef: "\<forall>(l,r) \<in> set ?P \<union> set ?Pw. \<not> defined (set ?R \<union> set ?Rw) (the (root r))"
      and nvarR: "\<forall> (l,r) \<in> set ?R \<union> set ?Rw. is_Fun l"
      by (auto simp: split_def Let_def)
    from ok have valid: "isOK (check_valid)" 
      and Q: "isOK (check_sl_Q LD lQ ?Q)"
      and Q': "isOK (check_lab_lhss_more lQ ?Q)"
      and lQ: "\<And> q. q \<in> set ?Q \<Longrightarrow> linear_term q"
      and D: "isOK(check_decr D)"
      and D': "isOK(check_decr' D)"
      and R: "isOK(check_model_lab ?lR ?R)"
      and Rw: "isOK(check_model_lab ?lRw ?Rw)"
      and R': "isOK(check_lab_all_trs lR ?R)"
      and Rw': "isOK(check_lab_all_trs lRw ?Rw)"
      and P: "isOK(check_lab_root_all ?lP ?P)"
      and Pw: "isOK(check_lab_root_all ?lPw ?Pw)"
      and wf: "?nfs \<Longrightarrow> set ?Q \<noteq> {} \<Longrightarrow> wf_trs (set D)" 
      and wwf: "?nfs \<Longrightarrow>  set ?Q \<noteq> {} \<Longrightarrow> wwf_qtrs (set ?Q) (set ?R \<union> set ?Rw)"
      and dp': "dp' = dpp_ops.mk J ?nfs ?m lP lPw lQ lR (lRw @ D)" by auto
    from check_valid[OF valid]
    interpret sl_interpr_root_same C c I cge lge L LC LD LS L' LS' .
    from check_model_lab[OF R] have 
      R1: "lab_trs I L LC C (set ?R) \<subseteq> set lR"
      and R2: "qmodel I L LC C cge (set ?R)" by auto
    from check_model_lab[OF Rw] have 
      Rw1: "lab_trs I L LC C (set ?Rw) \<subseteq> set lR \<union> set lRw"
      and Rw2: "qmodel I L LC C cge (set ?Rw)" by auto
    show "finite_dpp (dpp_ops.dpp J dp)"
      unfolding dpp_sound      
    proof (rule sl_qmodel_root_finite[OF R2 Rw2 check_decr[OF D] wf wwf check_decr'[OF D'] check_lab_lhss_more[OF Q']
          check_sl_Q[OF Q] lQ R1 Rw1 _ nvar])
      show "set lR \<union> set lRw \<subseteq> Lab_all_trs (set ?R \<union> set ?Rw)"
        using check_lab_all_trs[OF R'] check_lab_all_trs[OF Rw'] unfolding Lab_all_trs_def by auto
      show "\<forall> (s,t) \<in> set ?P \<union> set ?Pw. \<not> defined (applicable_rules (set ?Q) (set ?R \<union> set ?Rw)) (the (root t))"
        using ndef_applicable_rules ndef by blast
      show "finite_dpp (?nfs,?m,Lab_root_all_trs (set ?P), Lab_root_all_trs (set ?Pw), set lQ, set lR, set lRw \<union> set D)"
      proof (rule finite_dpp_mono[OF fin[unfolded dp' mk_sound] check_lab_root_all[OF P] _ refl subset_refl])
        show "Lab_root_all_trs (set ?P) \<union> Lab_root_all_trs (set ?Pw) \<subseteq> set lP \<union> set lPw"
          using check_lab_root_all[OF P]  check_lab_root_all[OF Pw]  by auto
      qed simp
    qed (insert nvarR, auto)
  qed
qed

lemma check_decr_rstep: assumes check: "isOK(check_decr lR)" shows "decr_of_ord (lge_to_lgr_rel lge LS) LC LS \<subseteq> (rstep (set lR))^+"
proof -
  show ?thesis unfolding rstep_eq_closure 
    by (rule subset_trans[OF check_decr[OF check]], rule trancl_mono_set,
    rule subset_trans[OF _ ctxt.subset_closure], auto)
qed
end

subsection \<open>checking the various model / ... conditions\<close>

fun
  check_sl_rule_ass ::
    "bool \<Rightarrow> ('f::showl,'c::showl)inter \<Rightarrow> ('f,'c,'l)label
     \<Rightarrow> ('f,'l,'lf :: showl)lcompose 
     \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> ('lf,'v)trs
     \<Rightarrow> ('v::showl,'c)assign \<Rightarrow> ('f,'v)rule \<Rightarrow> showsl check"
where
  "check_sl_rule_ass mc I L LC cge lR \<alpha> (l, r) = do {
     let cl_ll = eval_lab I L LC \<alpha> l;
     let cr_lr = eval_lab I L LC \<alpha> r;
     check (mc \<longrightarrow> (cge (fst cl_ll) (fst cr_lr)))
       (showsl_lit (STR ''rule '') \<circ> showsl_rule (l, r) \<circ> showsl_lit (STR '' violates the model condition, [lhs] = '')
         \<circ> showsl (fst cl_ll) \<circ> showsl_lit (STR '', [rhs] = '') \<circ> showsl (fst cr_lr));
     check ((snd cl_ll, snd cr_lr) \<in> lR)
       (showsl_lit (STR ''labeled rule '') \<circ> showsl_rule (snd cl_ll, snd cr_lr) \<circ> showsl_lit (STR '' missing''))
   }"

fun
  lab_rule_ass ::
    "('f,'c)inter \<Rightarrow> ('f,'c,'l)label
     \<Rightarrow> ('f,'l,'lf)lcompose 
     \<Rightarrow> ('v,'c)assign \<Rightarrow> ('f,'v)rule \<Rightarrow> ('lf,'v)rule"
where
  "lab_rule_ass I L LC \<alpha> rule = 
     (lab I L LC \<alpha> (fst rule), lab I L LC \<alpha> (snd rule))"

fun
  check_sl_rule_all_ass ::
    "('f::showl,'c::showl)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'c,'l)label
     \<Rightarrow> ('f,'l,'lf :: showl)lcompose 
     \<Rightarrow> ('l \<Rightarrow> 'l list)
     \<Rightarrow> ('lf,'v)trs
     \<Rightarrow> ('v::showl,'c)assign \<Rightarrow> ('f,'v)rule \<Rightarrow> showsl check"
where
  "check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> (l, Fun f ts) = do {
     let ll = lab_root I L L' LC \<alpha> l;
         clts = map (eval_lab I L LC \<alpha>) ts;
         lts = map snd clts;
         l'   = L' f (map fst clts);
         n = length ts;
         small = gen_smaller l' in
     check_allm (\<lambda> l'. check ((ll, Fun (LC f n l') lts) \<in> lR) 
       (showsl_lit (STR ''labeled rule '') \<circ> showsl_rule (ll, Fun (LC f n l') lts) \<circ> showsl_lit (STR '' missing''))) small
   }" |
  "check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> (l, Var x) = do {
     let ll = lab_root I L L' LC \<alpha> l;
     let lr = lab_root I L L' LC \<alpha> (Var x) in
   check ((ll, lr) \<in> lR) 
       (showsl_lit (STR ''labeled rule '') \<circ> showsl_rule (ll, lr) \<circ> showsl_lit (STR '' missing''))
   }"

fun
  check_sl_rule_root ::
    "('f::showl,'c::showl)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf :: showl)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('lf,'v)trs \<Rightarrow> ('f,'v::showl)rule \<Rightarrow> showsl check"
where
  "check_sl_rule_root I L L' LC C lR lr = check_allm (\<lambda>\<alpha>. 
  let la = lab_root I L L' LC \<alpha>;
      l =  la (fst lr);
      r =  la (snd lr)
    in check ((l,r) \<in> lR) (showsl_lit (STR ''labeled rule '') \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '' is missing'')))
     (map fun_of (enum_vectors C (vars_rule_impl lr)))"

fun
  check_sl_rule ::
    "('f::showl,'c::showl)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf :: showl)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool)
     \<Rightarrow> bool
     \<Rightarrow> ('lf :: showl,'v)trs \<Rightarrow> ('f,'v::showl)rule \<Rightarrow> showsl check"
where
  "check_sl_rule I L LC C cge mc lR lr = check_allm (\<lambda>\<alpha>. check_sl_rule_ass mc I L LC cge lR \<alpha> lr) 
     (map fun_of (enum_vectors C (vars_rule_impl lr)))"

fun
  check_sl_rule_all ::
    "('f::showl,'c::showl)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf :: showl)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('l \<Rightarrow> 'l list)
     \<Rightarrow> ('lf :: showl,'v)trs \<Rightarrow> ('f,'v::showl)rule \<Rightarrow> showsl check"
where
  "check_sl_rule_all I L L' LC C gen_smaller lR lr = check_allm (\<lambda>\<alpha>. check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> lr) 
     (map fun_of (enum_vectors C (vars_rule_impl lr)))"

lemma check_sl_rule_sound[simp]:
  fixes lR :: "('f::showl,'v::showl)trs" and I :: "('f,'c::showl)inter" 
  assumes "isOK (check_sl_rule I L LC C cge mc lR (l,r))"
  shows "(mc \<longrightarrow> qmodel_rule I L LC (set C) cge l r) \<and> lab_rule I L LC (set C) (l,r) \<subseteq> lR"
proof (cases C)
  case Nil
  then show ?thesis unfolding lab_rule_def wf_assign_def by auto
next
  case (Cons c D)
  let ?C = "Cons c D"
  let ?V = "vars_rule_impl (l,r) :: 'v list"
  from assms Cons have check: "\<forall> \<alpha> \<in> set (map fun_of (enum_vectors ?C ?V)). isOK(check_sl_rule_ass mc I L LC cge lR \<alpha> (l,r))"
    by auto
  have "\<forall> \<alpha>. wf_assign (set ?C) \<alpha> \<longrightarrow> isOK(check_sl_rule_ass mc I L LC cge lR \<alpha> (l,r))"
  proof (intro allI, intro impI)
    fix \<alpha> :: "'v \<Rightarrow> 'c"
    assume wf_ass: "wf_assign (set ?C) \<alpha>"
    from enum_vectors_complete obtain vec where vec: "vec \<in> set (enum_vectors ?C ?V) \<and> (\<forall> x \<in> set ?V. \<forall> c \<in> set ?C. \<alpha> x = c \<longrightarrow> fun_of vec x = c)"
      by best
    let ?\<beta> = "fun_of vec"
    from wf_ass vec have "\<forall> x \<in> set ?V. \<alpha> x = ?\<beta> x" unfolding wf_assign_def by auto
    then have l: "(\<forall> x \<in> vars_term l. ?\<beta> x = \<alpha> x)" and r: "(\<forall> x \<in> vars_term r. ?\<beta> x = \<alpha> x) " 
      unfolding set_vars_rule_impl vars_rule_def by auto
    have equal: "eval_lab I L LC \<alpha> l = eval_lab I L LC ?\<beta> l \<and> eval_lab I L LC \<alpha> r = eval_lab I L LC ?\<beta> r" 
      unfolding eval_lab_independent[OF l] eval_lab_independent[OF r] by auto
    from vec check have "isOK(check_sl_rule_ass mc I L LC cge lR ?\<beta> (l,r))" by auto
    with equal show "isOK(check_sl_rule_ass mc I L LC cge lR \<alpha> (l,r))" by auto
  qed
  then show ?thesis using Cons unfolding lab_rule_def by (auto simp: Let_def)
qed

declare check_sl_rule.simps[simp del]

lemma check_sl_rule_root:
  fixes lR :: "('f::showl,'v::showl)trs" and I :: "('f,'c::showl)inter" 
  assumes "isOK (check_sl_rule_root I L L' LC C lR (l,r))"
  shows "lab_root_rule I L L' LC (set C) (l,r) \<subseteq> lR"
proof (cases C)
  case Nil
  then show ?thesis unfolding lab_root_rule_def wf_assign_def by auto
next
  case (Cons c D)
  let ?C = "Cons c D"
  let ?V = "vars_rule_impl (l,r) :: 'v list"
  let ?L = "lab_root I L L' LC"
  from assms Cons have check: "\<forall> \<alpha> \<in> set (map fun_of (enum_vectors ?C ?V)). (?L \<alpha> l, ?L \<alpha> r) \<in> lR"
    by (auto simp: Let_def)
  show ?thesis unfolding lab_root_rule_def fst_conv snd_conv 
  proof (clarify)
    fix x y :: "('f,'v)term" and \<alpha> :: "('v,'c)assign"
    assume wf_ass: "wf_assign (set C) \<alpha>"
    from enum_vectors_complete obtain vec where vec: "vec \<in> set (enum_vectors ?C ?V) \<and> (\<forall> x \<in> set ?V. \<forall> c \<in> set ?C. \<alpha> x = c \<longrightarrow> fun_of vec x = c)"
      by best
    let ?\<beta> = "fun_of vec"
    from wf_ass vec have "\<forall> x \<in> set ?V. \<alpha> x = ?\<beta> x" unfolding wf_assign_def Cons by auto
    then have l: "(\<forall> x \<in> vars_term l. ?\<beta> x = \<alpha> x)" and r: "(\<forall> x \<in> vars_term r. ?\<beta> x = \<alpha> x) " 
      unfolding set_vars_rule_impl vars_rule_def by auto
    have equal: "?L \<alpha> l = ?L ?\<beta> l \<and> ?L \<alpha> r = ?L ?\<beta> r" 
      unfolding lab_root_independent[OF l] lab_root_independent[OF r] by auto
    from vec check equal
    show "(?L \<alpha> l, ?L \<alpha> r) \<in> lR" by auto
  qed
qed

declare check_sl_rule_root.simps[simp del]

fun
  lab_rule_list ::
    "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('f,'v)rule \<Rightarrow> ('lf,'v)rules"
where
  "lab_rule_list I L LC C lr = map (\<lambda>\<alpha>. lab_rule_ass I L LC \<alpha> lr) 
     (map fun_of (enum_vectors C (vars_rule_impl lr)))"

lemma lab_rule_list:
  fixes L :: "('f,'c,'l)label" and  I :: "('f,'c)inter" 
  and rule :: "('f,'v)rule"
  assumes C: "C \<noteq> []"
  shows "set (lab_rule_list I L LC C rule) = lab_rule I L LC (set C) rule" (is "?list = ?set")
proof -
  obtain l r where rule: "rule = (l,r)" by force
  let ?V = "vars_rule_impl rule"
  let ?lab = "lab I L LC"
  let ?lab_rule = "\<lambda> \<alpha>. (?lab \<alpha> (fst rule), ?lab \<alpha> (snd rule))"
  {
    fix \<alpha> :: "'v \<Rightarrow> 'c"
    assume wf_ass: "wf_assign (set C) \<alpha>"
    from enum_vectors_complete[OF C] obtain vec where vec: "vec \<in> set (enum_vectors C ?V) \<and> (\<forall> x \<in> set ?V. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c)"
      by best
    let ?\<beta> = "fun_of vec"
    from wf_ass vec have "\<forall> x \<in> set ?V. \<alpha> x = ?\<beta> x" unfolding wf_assign_def by auto
    then have l: "(\<forall> x \<in> vars_term l. ?\<beta> x = \<alpha> x)" and r: "(\<forall> x \<in> vars_term r. ?\<beta> x = \<alpha> x)" 
      unfolding rule set_vars_rule_impl vars_rule_def by auto
    have equal: "?lab \<alpha> l = ?lab ?\<beta> l" "?lab \<alpha> r = ?lab ?\<beta> r" 
      unfolding eval_lab_independent[OF l] eval_lab_independent[OF r] by auto
    then have "?lab_rule \<alpha> \<in> ?list" unfolding rule fst_conv snd_conv equal
      using vec unfolding lab_rule_list.simps rule by auto
  }
  then have one: "?set \<subseteq> ?list" unfolding lab_rule_def by auto
  {
    fix vec
    assume vec: "vec \<in> set (enum_vectors C ?V)"
    let ?\<beta> = "fun_of vec"
    let ?\<alpha> = "\<lambda> x. if (x \<in> set ?V) then ?\<beta> x else hd C"
    have "wf_assign (set C) ?\<alpha>"
      unfolding wf_assign_def
    proof (clarify)
      fix x
      show "?\<alpha> x \<in> set C"
      proof (cases "x \<in> set ?V")
        case False
        then show ?thesis using C by auto
      next
        case True
        with enum_vectors_sound[OF True vec]
        show ?thesis by auto
      qed
    qed
    then have mem: "(?lab ?\<alpha> l, ?lab ?\<alpha> r) \<in> ?set"
      unfolding rule lab_rule_def by auto
    have "\<forall> x \<in> set ?V. ?\<alpha> x = ?\<beta> x" by auto
    then have l: "(\<forall> x \<in> vars_term l. ?\<beta> x = ?\<alpha> x)" and r: "(\<forall> x \<in> vars_term r. ?\<beta> x = ?\<alpha> x)" 
      unfolding rule set_vars_rule_impl vars_rule_def by auto
    have equal: "?lab ?\<alpha> l = ?lab ?\<beta> l" "?lab ?\<alpha> r = ?lab ?\<beta> r" 
      unfolding eval_lab_independent[OF l] eval_lab_independent[OF r] by auto
    from mem[unfolded equal]
    have "(?lab ?\<beta> (fst rule), ?lab ?\<beta> (snd rule)) \<in> ?set" unfolding rule by auto
  }
  then have "?list \<subseteq> ?set" by auto
  with one show ?thesis by auto
qed
   
declare lab_rule_list.simps[simp del]

definition  lab_trs_list ::
    "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('f,'v)rules \<Rightarrow> ('lf,'v)rules"
where
  "lab_trs_list I L LC C R = concat (map (lab_rule_list I L LC C) R)"

lemma lab_trs_list:
  fixes L :: "('f,'c,'l)label" and  I :: "('f,'c)inter" 
  and R :: "('f,'v)rules"
  assumes C: "C \<noteq> []"
  shows "set (lab_trs_list I L LC C R) = lab_trs I L LC (set C) (set R)"
  unfolding lab_trs_list_def using lab_rule_list[OF C, of I L LC]
  by auto

fun
  lab_lhs_list ::
    "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('f,'v)term \<Rightarrow> ('lf,'v)term list"
where
  "lab_lhs_list I L LC C t = map (\<lambda>\<alpha>. lab I L LC \<alpha> t) 
     (map fun_of (enum_vectors C (vars_term_impl t)))"

lemma lab_lhs_list:
  fixes L :: "('f,'c,'l)label" and  I :: "('f,'c)inter" 
  and t :: "('f,'v)term"
  assumes C: "C \<noteq> []"
  shows "set (lab_lhs_list I L LC C t) = lab_lhs I L LC (set C) t" (is "?list = ?set")
proof -
  let ?V = "vars_term_impl t"
  let ?lab = "lab I L LC"
  let ?lab_lhs = "\<lambda> \<alpha>. ?lab \<alpha> t"
  {
    fix \<alpha> :: "'v \<Rightarrow> 'c"
    assume wf_ass: "wf_assign (set C) \<alpha>"
    from enum_vectors_complete[OF C] obtain vec where vec: "vec \<in> set (enum_vectors C ?V) \<and> (\<forall> x \<in> set ?V. \<forall> c \<in> set C. \<alpha> x = c \<longrightarrow> fun_of vec x = c)"
      by best
    let ?\<beta> = "fun_of vec"
    from wf_ass vec have "\<forall> x \<in> set ?V. \<alpha> x = ?\<beta> x" unfolding wf_assign_def by auto
    then have t: "(\<forall> x \<in> vars_term t. ?\<beta> x = \<alpha> x)" by auto 
    have equal: "?lab \<alpha> t = ?lab ?\<beta> t" 
      unfolding eval_lab_independent[OF t] by auto
    then have "?lab_lhs \<alpha> \<in> ?list" unfolding equal
      using vec by auto
  }
  then have one: "?set \<subseteq> ?list" unfolding lab_lhs_def by auto
  {
    fix vec
    assume vec: "vec \<in> set (enum_vectors C ?V)"
    let ?\<beta> = "fun_of vec"
    let ?\<alpha> = "\<lambda> x. if (x \<in> set ?V) then ?\<beta> x else hd C"
    have "wf_assign (set C) ?\<alpha>"
      unfolding wf_assign_def
    proof (clarify)
      fix x
      show "?\<alpha> x \<in> set C"
      proof (cases "x \<in> set ?V")
        case False
        then show ?thesis using C by auto
      next
        case True
        with enum_vectors_sound[OF True vec]
        show ?thesis by auto
      qed
    qed
    then have mem: "?lab_lhs ?\<alpha> \<in> ?set"
      unfolding lab_lhs_def by auto
    have "\<forall> x \<in> set ?V. ?\<alpha> x = ?\<beta> x" by auto
    then have t: "(\<forall> x \<in> vars_term t. ?\<beta> x = ?\<alpha> x)"
      by auto
    have equal: "?lab_lhs ?\<alpha> = ?lab_lhs ?\<beta>"
      unfolding eval_lab_independent[OF t] by auto
    from mem[unfolded equal]
    have "?lab_lhs ?\<beta> \<in> ?set" by auto
  }
  then have "?list \<subseteq> ?set" by auto
  with one show ?thesis by auto
qed
   
declare lab_lhs_list.simps[simp del]

definition lab_lhss_list ::
    "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'lf)lcompose 
     \<Rightarrow> 'c list 
     \<Rightarrow> ('f,'v)term list \<Rightarrow> ('lf,'v)term list"
where
  "lab_lhss_list I L LC C Q = concat (map (lab_lhs_list I L LC C) Q)"

lemma lab_lhss_list:
  fixes L :: "('f,'c,'l)label" and  I :: "('f,'c)inter" 
  and Q :: "('f,'v)term list"
  assumes C: "C \<noteq> []"
  shows "set (lab_lhss_list I L LC C Q) = lab_lhss I L LC (set C) (set Q)"
  unfolding lab_lhss_list_def using lab_lhs_list[OF C, of I L LC]
  by auto

definition check_sl_Q' :: "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'f)lcompose 
     \<Rightarrow> 'c list \<Rightarrow> ('f :: showl,'v :: showl)term list \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check"
  where "check_sl_Q' I L LC C lQ Q \<equiv> do {
  check (C \<noteq> []) (showsl_lit (STR ''carrier must be non-empty''));
  check_NF_vars_subset (lab_lhss_list I L LC C Q) lQ
    <+? (\<lambda> l. showsl_lit (STR ''labeled term '') \<circ> showsl l \<circ> showsl_lit (STR '' is missing''))
  }"

lemma check_sl_Q': assumes ok: "isOK(check_sl_Q' I L LC C lQ Q)"
  shows "NF_terms (lab_lhss I L LC (set C) (set Q)) \<supseteq> NF_terms (set lQ)"
proof -
  note ok = ok[unfolded check_sl_Q'_def]
  from ok have "C \<noteq> []" by auto
  from ok lab_lhss_list[OF this, of I L LC Q]
  show ?thesis 
    by (intro NF_vars_subset, auto)
qed

definition check_sl_lab' :: "('f,'c)inter \<Rightarrow> ('f,'c,'l)label 
     \<Rightarrow> ('f,'l,'f)lcompose 
     \<Rightarrow> 'c list \<Rightarrow> ('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> showsl check"
  where "check_sl_lab' I L LC C lR R \<equiv> do {
  check (C \<noteq> []) (showsl_lit (STR ''carrier must be non-empty''));
  check_subseteq lR (lab_trs_list I L LC C R)
    <+? (\<lambda> lr. showsl_lit (STR ''labeled rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is not allowed''))
  }"

lemma check_sl_lab': assumes ok: "isOK(check_sl_lab' I L LC C lR R)"
  shows "set lR \<subseteq> lab_trs I L LC (set C) (set R)"
proof -
  note ok = ok[unfolded check_sl_lab'_def]
  from ok have "C \<noteq> []" by auto
  from ok lab_trs_list[OF this, of I L LC R]
  show ?thesis by auto
qed

lemma check_sl_rule_all_sound:
  fixes lR :: "('f::showl,'v::showl)trs" and I :: "('f,'c::showl)inter" 
  assumes ok: "isOK (check_sl_rule_all I L L' LC C gen_smaller lR (l,r))"
  and gen: "\<And> f n l l'. lge f n l l' \<Longrightarrow> l' \<in> set (gen_smaller l)"
  shows "lab_root_all_rule I L L' LC lge (set C) (l,r) \<subseteq> lR"
proof (cases C)
  case Nil
  then show ?thesis unfolding lab_root_all_rule_def wf_assign_def by auto
next
  case (Cons c D)
  let ?C = "Cons c D"
  let ?V = "vars_rule_impl (l,r) :: 'v list"
  from assms Cons have check: "\<forall> \<alpha> \<in> set (map fun_of (enum_vectors ?C ?V)). isOK(check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> (l,r))"
    by auto
  have check: "\<forall> \<alpha>. wf_assign (set ?C) \<alpha> \<longrightarrow> isOK(check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> (l,r))"
  proof (intro allI, intro impI)
    fix \<alpha> :: "'v \<Rightarrow> 'c"
    assume wf_ass: "wf_assign (set ?C) \<alpha>"
    from enum_vectors_complete obtain vec where vec: "vec \<in> set (enum_vectors ?C ?V) \<and> (\<forall> x \<in> set ?V. \<forall> c \<in> set ?C. \<alpha> x = c \<longrightarrow> fun_of vec x = c)"
      by best
    let ?\<beta> = "fun_of vec"
    from wf_ass vec have "\<forall> x \<in> set ?V. \<alpha> x = ?\<beta> x" unfolding wf_assign_def by auto
    then have l: "(\<forall> x \<in> vars_term l. ?\<beta> x = \<alpha> x)" and r: "(\<forall> x \<in> vars_term r. ?\<beta> x = \<alpha> x) " 
      unfolding set_vars_rule_impl vars_rule_def by auto
    have equal: "lab_root I L L' LC \<alpha> l = lab_root I L L' LC ?\<beta> l \<and> lab_root I L L' LC \<alpha> r = lab_root I L L' LC ?\<beta> r" 
      unfolding lab_root_independent[OF l] lab_root_independent[OF r] by auto
    from vec check have check: "isOK(check_sl_rule_all_ass I L L' LC gen_smaller lR ?\<beta> (l,r))" by auto
    show "isOK(check_sl_rule_all_ass I L L' LC gen_smaller lR \<alpha> (l,r))" 
    proof (cases r)
      case (Var x)
      with equal check show ?thesis by simp
    next
      case (Fun f ts)
      with r have "\<And> t. t \<in> set ts \<Longrightarrow> \<forall> x \<in> vars_term t. ?\<beta> x = \<alpha> x" by auto
      from eval_lab_independent[OF this, of _ I L LC] 
      have map: "map (eval_lab I L LC \<alpha>) ts = map (eval_lab I L LC ?\<beta>) ts" by auto
      from equal[THEN conjunct1] check
      show ?thesis unfolding Fun
        by (simp add: Let_def map)
    qed
  qed
  note check = check[unfolded Cons[symmetric], THEN spec, THEN mp]
  { 
    fix \<alpha> lr
    assume wf: "wf_assign (set C) \<alpha>" and lr: "lr \<in> lab_root_all I L L' LC lge \<alpha> r"
    note ok = check[OF wf]
    have "(lab_root I L L' LC \<alpha> l, lr) \<in> lR" 
    proof (cases r)
      case (Var x)
      with ok lr show ?thesis by (simp add: Let_def)
    next
      case (Fun f ts)
      let ?n = "length ts"
      from lr[unfolded Fun]
      obtain l' where lr: "lr = Fun (LC f ?n l') (map (lab I L LC \<alpha>) ts)" and lge: "lge f ?n (L' f (map (eval I L LC \<alpha>) ts)) l'" 
        by (auto simp: o_def)
      from gen[OF lge] have l': "l' \<in> set (gen_smaller (L' f (map (eval I L LC \<alpha>) ts)))" by simp
      from ok[unfolded Fun] l' show ?thesis
        unfolding lr by (auto simp: Let_def o_def)
    qed
  }
  then show ?thesis unfolding lab_root_all_rule_def by auto 
qed

declare check_sl_rule_all.simps[simp del]

type_synonym ('f,'c,'l,'v)sl_check4 =
  "('f,'c)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> 'c list \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'f) \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules
   \<Rightarrow> showsl check"

type_synonym ('f,'c,'l,'v)sl_check4_set =
  "('f,'c)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> 'c list \<Rightarrow> ('c \<Rightarrow> 'c \<Rightarrow> bool) \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'f) \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)rules
   \<Rightarrow> showsl check"

definition
  check_sl_model_lab_trs_set  :: "('f::showl,'c::showl,'l,'v::showl)sl_check4_set" 
where
  "check_sl_model_lab_trs_set I L C cge labl lR R \<equiv> check_allm (check_sl_rule I L labl C cge True lR) R"

definition
  check_sl_model_lab_trs :: "('f::showl,'c::showl,'l,'v::showl)sl_check4_set" 
where
  "check_sl_model_lab_trs I L C cge labl lR R \<equiv> check_sl_model_lab_trs_set I L C cge labl lR R"

definition 
  check_sl_lab_trs_set :: "('f::showl,'c::showl,'l,'v::showl)sl_check4_set" 
where
  "check_sl_lab_trs_set I L C cge labl lP P \<equiv> check_allm (check_sl_rule I L labl C cge False lP) P"

definition 
  check_sl_lab_trs :: "('f::showl,'c::showl,'l,'v::showl)sl_check4_set" 
where
  "check_sl_lab_trs I L C cge labl lP P \<equiv> check_sl_lab_trs_set I L C cge labl lP P"

definition 
  check_sl_lab_root_trs 
where
  "check_sl_lab_root_trs I L L' C labl lP P \<equiv> check_allm (check_sl_rule_root I L L' labl C lP) P"

lemma check_sl_lab_trs_set_sound:
  assumes "isOK(check_sl_lab_trs_set I L C cge labl lP P)"
  shows "lab_trs I L labl (set C) (set P) \<subseteq> lP"
proof -
  from assms have check: "\<forall> (l,r) \<in> set P. isOK(check_sl_rule I L labl C cge False lP (l,r))"
    unfolding check_sl_lab_trs_set_def by auto
  have "\<forall> (l,r) \<in> set P. lab_rule I L labl (set C) (l,r) \<subseteq> lP" 
  proof (clarify)
    fix l r ll lr
    assume lr: "(l,r) \<in> set P" and llr: "(ll,lr) \<in> lab_rule I L labl (set C) (l,r)"
    from lr check have "isOK(check_sl_rule I L labl C cge False lP (l,r))" by auto 
    then have "lab_rule I L labl (set C) (l,r) \<subseteq> lP" by auto
    with lr llr show "(ll,lr) \<in> lP" by auto
  qed
  then show ?thesis by auto
qed

lemma check_sl_lab_trs_sound:
  "isOK(check_sl_lab_trs I L C cge labl lP P) \<Longrightarrow> lab_trs I L labl (set C) (set P) \<subseteq> lP"
  using check_sl_lab_trs_set_sound unfolding check_sl_lab_trs_def .


lemma check_sl_model_lab_trs_set_sound: 
  fixes label :: "('f :: showl \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'f)"
    and R :: "('f, 'v :: showl)rules"
  assumes "isOK(check_sl_model_lab_trs_set I L C cge label lR R)"
  shows "lab_trs I L label (set C) (set R) \<subseteq> lR \<and> qmodel I L label (set C) cge (set R)"
proof -
  from assms have check: "\<forall> (l,r) \<in> set R. isOK(check_sl_rule I L label C cge True lR (l,r))"
    unfolding check_sl_model_lab_trs_set_def by auto
  have "\<forall> (l,r) \<in> set R. qmodel_rule I L label (set C) cge l r \<and> lab_rule I L label (set C) (l,r) \<subseteq> lR" 
  proof (clarify)
    fix l r
    assume lr: "(l,r) \<in> set R" 
    from lr check have "isOK(check_sl_rule I L label C cge True lR (l,r))" by auto 
    then show "qmodel_rule I L label (set C) cge l r \<and> lab_rule I L label (set C) (l,r) \<subseteq> lR" by auto
  qed
  then show ?thesis unfolding qmodel_def by auto
qed

lemma check_sl_model_lab_trs_sound: 
  "isOK(check_sl_model_lab_trs I L C cge labl lR R) \<Longrightarrow> lab_trs I L labl (set C) (set R) \<subseteq> lR \<and> qmodel I L labl (set C) cge (set R)"
  using check_sl_model_lab_trs_set_sound unfolding check_sl_model_lab_trs_def .
  

lemma check_sl_lab_root_trs_sound: fixes lP :: "('f :: showl, 'v :: showl)trs" and P :: "('f,'v)rules"
  and I :: "('f,'c::showl)inter" 
  assumes "isOK(check_sl_lab_root_trs I L L' C labl lP P)"
  shows "lab_root_trs I L L' labl (set C) (set P) \<subseteq> lP"
proof -
  from assms have check: "\<forall> (l,r) \<in> set P. isOK(check_sl_rule_root I L L' labl C lP (l,r))"
    unfolding check_sl_lab_root_trs_def by auto
  have "\<forall> (l,r) \<in> set P. lab_root_rule I L L' labl (set C) (l,r) \<subseteq> lP" 
  proof (clarify)
    fix l r ll lr :: "('f,'v)term"
    assume lr: "(l,r) \<in> set P" and llr: "(ll,lr) \<in> lab_root_rule I L L' labl (set C) (l,r)"
    from lr check have check: "isOK(check_sl_rule_root I L L' labl C lP (l,r))" by auto 
    from check_sl_rule_root[OF check]
    have"lab_root_rule I L L' labl (set C) (l,r) \<subseteq> lP" .
    with lr llr show "(ll,lr) \<in> lP" by auto
  qed
  then show ?thesis by auto
qed

definition 
  check_sl_lab_all_trs 
where
  "check_sl_lab_all_trs I L L' C gen labl lP P \<equiv> check_allm (check_sl_rule_all I L L' labl C gen lP) P"


lemma check_sl_lab_all_trs_sound: 
  fixes label :: "('f :: showl \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'f)"
    and P :: "('f, 'v :: showl)rules"
  assumes ok: "isOK(check_sl_lab_all_trs I L L' C gen label lP P)"
  and gen: "\<And> f n l l'. lge f n l l' \<Longrightarrow> l' \<in> set (gen l)"
  shows "lab_root_all_trs I L L' label lge (set C) (set P) \<subseteq> lP"
proof -
  from ok have check: "\<forall> (l,r) \<in> set P. isOK(check_sl_rule_all I L L' label C gen lP (l,r))"
    unfolding check_sl_lab_all_trs_def by auto
  have "\<forall> (l,r) \<in> set P. lab_root_all_rule I L L' label lge (set C) (l,r) \<subseteq> lP" 
  proof (clarify)
    fix l r ll lr
    assume lr: "(l,r) \<in> set P" and llr: "(ll,lr) \<in> lab_root_all_rule I L L' label lge (set C) (l,r)"
    from lr check have "isOK(check_sl_rule_all I L L' label C gen lP (l,r))" by auto 
    from check_sl_rule_all_sound[OF this gen]
    have "lab_root_all_rule I L L' label lge (set C) (l,r) \<subseteq> lP" by simp
    with lr llr show "(ll,lr) \<in> lP" by auto
  qed
  then show ?thesis by auto
qed

lemma (in sl_interpr) Lab_lhss_more_instance_term: 
  "Lab_lhss_more Q = { l. \<exists> q. q \<in> Q \<and> instance_term l (map_funs_term_wa (\<lambda> (f,n). {g. (g,n) \<in> F_all \<and> UNLAB g = f}) q)}" (is "?L = ?R")
proof -
  {
    fix l
    assume "l \<in> ?L"
    from this[unfolded Lab_lhss_more_def]
    have wf: "funas_term l \<subseteq> F_all" and q: "map_funs_term UNLAB l \<in> Q" by auto
    from wf have "instance_term l (map_funs_term_wa (\<lambda> (f,n). {g. (g,n) \<in> F_all \<and> UNLAB g = f}) (map_funs_term UNLAB l))" 
    proof (induct l)
      case (Var x)
      then show ?case by auto
    next
      case (Fun f ls)
      show ?case
      proof (unfold map_funs_term_wa.simps term.simps instance_term.simps split, intro conjI allI impI, rule, intro conjI)
        fix i
        assume i: "i < length ls"
        then have i': "i < length (map (map_funs_term UNLAB) ls)" by auto
        then have lsi: "ls ! i \<in> set ls" by auto
        from Fun(1)[OF lsi]
        show "instance_term (ls ! i) (map (map_funs_term_wa (\<lambda> (f,n). {g. (g,n)  \<in> F_all \<and> UNLAB g = f})) (map (map_funs_term UNLAB) ls) ! i)" unfolding nth_map[OF i'] nth_map[OF i] using Fun(2)[unfolded funas_term.simps set_map set_conv_nth] i
        by force
      qed (insert Fun(2), auto)
    qed
    with q have "l \<in> ?R" by auto
  }
  then have "?L \<subseteq> ?R" by auto
  moreover
  {
    fix l
    assume "l \<in> ?R"
    then obtain q where q: "q \<in> Q" and inst: "instance_term l (map_funs_term_wa (\<lambda>(f,n). {g. (g,n) \<in> F_all \<and> UNLAB g = f}) q)" by auto
    have "l \<in> ?L" unfolding Lab_lhss_more_def
    proof 
      have "funas_term l \<subseteq> F_all \<and> map_funs_term UNLAB l = q" using inst
      proof (induct l arbitrary: q)
        case (Var x)
        then show ?case by (cases q, auto)
      next
        case (Fun f ss q)
        then obtain g qs where q: "q = Fun g qs" by (cases q, auto)
        note Fun = Fun[unfolded q]
        {
          fix i
          assume i: "i < length ss"
          then have s: "ss ! i \<in> set ss" by auto
          from Fun(2) i
          have inst: "instance_term (ss ! i) (map (map_funs_term_wa (\<lambda>(f,n). {g. (g,n) \<in> F_all \<and> UNLAB g = f})) qs ! i)"
            by auto
          from i Fun(2) have i: "i < length qs" by auto
          from Fun(1)[OF s inst[unfolded nth_map[OF i]]]
          have "funas_term (ss ! i) \<subseteq> F_all \<and> map_funs_term UNLAB (ss ! i) = qs ! i" .
        } note ind = this
        from Fun(2) have len: "length ss = length qs" by auto
        have "map (map_funs_term UNLAB) ss = qs" 
          unfolding map_nth_eq_conv[OF len]
          by (intro allI impI, insert ind len, auto)
        then have "map_funs_term UNLAB (Fun f ss) = q" unfolding q using Fun(2) by auto
        moreover 
        have "funas_term (Fun f ss) \<subseteq> F_all"
        proof -
          {
            fix s 
            assume "s \<in> set ss"
            from this[unfolded set_conv_nth] ind
            have "funas_term s \<subseteq> F_all" by force
          }
          with Fun(2) show ?thesis by force
        qed
        ultimately show ?case by simp
      qed
      with q 
      show "funas_term l \<subseteq> F_all \<and> map_funs_term UNLAB l \<in> Q" by simp
    qed
  }
  ultimately show ?thesis by auto
qed

definition Lab_lhss_more_impl where 
  "Lab_lhss_more_impl LC LS_gen Q \<equiv> let F_all' = (\<lambda> (f,n). map (LC f n) (LS_gen f n)) in concat (map (\<lambda> q. flatten_term_enum (map_funs_term_wa F_all' q)) Q)"

definition check_sl_lab_lhss_more :: "('f,'l,'f)lcompose \<Rightarrow> 
  ('f \<Rightarrow> nat \<Rightarrow> 'l list) \<Rightarrow> ('f :: showl,'v :: showl)sl_check1"
  where "check_sl_lab_lhss_more LC LS_gen lQ Q \<equiv> check_NF_vars_subset (Lab_lhss_more_impl LC LS_gen Q) lQ <+? (\<lambda> t. showsl t \<circ> showsl_lit (STR '' is missing in labeled Q''))"

locale sl_interpr_root_same_show = sl_interpr_root C c I cge lge L LC LD LS L' LS'
  for  C :: "'c set"
  and  c :: "'c"
  and  I :: "('f :: showl,'c)inter"
  and  cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and  lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and  L :: "('f,'c,'l)label"
  and  LC :: "('f,'l,'f)lcompose"
  and  LD :: "('f,'f,'l)ldecompose"
  and  LS :: "('f,'l)labels" 
  and  L' :: "('f,'c,'l)label"
  and  LS' :: "('f,'l)labels"   
begin

lemma Lab_lhss_more_impl: assumes LS_gen: "\<And> f n. set (LS_gen f n) = Collect (LS f n)"
  shows "set (Lab_lhss_more_impl LC LS_gen Q) = Lab_lhss_more (set Q)"
proof -
  {
    fix f :: 'f and n :: nat
    have "LC f n ` set (LS_gen f n) = {g. (g,n) \<in> F_all \<and> UNLAB g = f}" unfolding LS_gen
      by (auto simp: LD_LC)
  } note id = this
  show ?thesis 
  unfolding Lab_lhss_more_instance_term 
    Lab_lhss_more_impl_def Let_def
  by (auto simp: flatten_term_enum map_funs_term_map_funs_term_wa map_funs_term_wa_compose id)
qed

lemma check_sl_lab_lhss_more: assumes LS_gen: "\<And> f n. set (LS_gen f n) = Collect (LS f n)"
  and check: "isOK(check_sl_lab_lhss_more LC LS_gen lQ Q)"
  shows "NF_terms (Lab_lhss_more (set Q)) \<supseteq> NF_terms (set lQ)"
proof (rule NF_vars_subset)
  show "NF_vars_subset (Lab_lhss_more (set Q)) (set lQ)"
    using check
    unfolding check_sl_lab_lhss_more_def 
    using Lab_lhss_more_impl[OF LS_gen, of Q] by auto
qed
end



definition check_wf_sym_F_all :: "('f,'l,'lf)lcompose \<Rightarrow> ('lf :: showl,'f,'l)ldecompose \<Rightarrow> ('f,'l)labels \<Rightarrow> ('lf \<times> nat) \<Rightarrow> showsl check"
  where "check_wf_sym_F_all LC LD LS \<equiv> \<lambda> (lf,n). (do {
            let (f,l) = LD lf;
            check (LS f n l \<and> lf = LC f n l) (showsl_lit (STR ''labeled symbol '') \<circ> showsl lf \<circ> showsl_lit (STR '' not allowed''))
          })"

definition
  check_wf_terms_F_all ::
    "('f, 'l, 'lf) lcompose \<Rightarrow> ('lf, 'f, 'l) ldecompose \<Rightarrow> ('f, 'l) labels \<Rightarrow> ('lf :: showl, 'v) term \<Rightarrow>
      showsl check"
where
  "check_wf_terms_F_all LC LD LS lt = do {
    let lfs = funas_term_impl lt;
    check_allm (check_wf_sym_F_all LC LD LS) lfs
  }"
  
lemma (in sl_interpr_root_same_show) check_wf_terms_F_all:
  "isOK (check_wf_terms_F_all LC LD LS lt) \<longleftrightarrow> funas_term lt \<subseteq> F_all"
proof -
  let ?ft = "funas_term"
  {
    fix lf n
    have "(\<exists> l f m. (lf,n) = (LC f m l,m) \<and> LS f m l) = isOK(check_wf_sym_F_all LC LD LS (lf,n))" (is "?l = ?r")
    proof -
      obtain f m where LD: "LD lf = (f,m)" by force
      show ?thesis
      proof
        assume ?r
        from this[unfolded check_wf_sym_F_all_def split Let_def LD]
        show ?l by auto
      next
        assume ?l
        then obtain l f where id: "lf = LC f n l" and l: "LS f n l" by auto
        from arg_cong[OF id, of LD, unfolded LD_LC] l id
        show ?r unfolding check_wf_sym_F_all_def by auto
      qed
    qed
  } note main = this
  have "(?ft lt \<subseteq> F_all) = (\<forall> lfn \<in> ?ft lt. lfn \<in> F_all)" by auto
  also have "... = isOK(check_wf_terms_F_all LC LD LS lt)"
    unfolding check_wf_terms_F_all_def Let_def using main
    by force
  finally show ?thesis by simp
qed

definition check_Lab_all_trs :: "('f,'l,'f)lcompose \<Rightarrow> ('f,'f,'l)ldecompose \<Rightarrow> ('f,'l)labels \<Rightarrow> ('f :: showl,'v :: showl)sl_check2"
where "check_Lab_all_trs LC LD LS lR R \<equiv> do {
  check_allm (\<lambda> (l,r). 
    do {
      check_wf_terms_F_all LC LD LS r;
      check (map_funs_rule (\<lambda>lf. fst (LD lf)) (l,r) \<in> set R)  (showsl_lit (STR ''unlabeling of the rule does not yield original rule''))
    } <+? (\<lambda>s. showsl_lit (STR ''problem with labeled rule'') \<circ> showsl_rule (l,r) \<circ> showsl_nl \<circ> s)
  ) lR
  }"

lemma (in sl_interpr_root_same_show) check_Lab_all_trs: "isOK(check_Lab_all_trs LC LD LS lR R) = (set lR \<subseteq> Lab_all_trs (set R))"
  unfolding check_Lab_all_trs_def Lab_all_trs_def check_wf_terms_F_all[symmetric] by auto

fun check_sl_decr'_rule :: "('f,'l,'lf)lcompose \<Rightarrow> ('lf,'f,'l)ldecompose \<Rightarrow> ('f,'l)labels \<Rightarrow> 
  ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l => bool) \<Rightarrow> ('lf,'v)rule \<Rightarrow> bool"
  where "check_sl_decr'_rule LC LD LS lge (Fun lf ts, Fun lg us) =
    ( let (f,l1) = LD lf;
          (g,l2) = LD lg;
          n = length ts
        in (f = g \<and> ts = us \<and> lf = LC f n l1 \<and> lg = LC f n l2 \<and> LS f n l1 \<and> LS f n l2 \<and> lge_to_lgr lge LS f n l1 l2))"
  | "check_sl_decr'_rule _ _ _ _ _ = False"

lemma (in sl_interpr) check_sl_decr'_rule: 
  "check_sl_decr'_rule LC LD LS lge lr = (lr \<in> Decr)" 
proof -
  obtain l r where lr: "lr = (l,r)" by force
  show ?thesis
  proof (cases "is_Var l \<or> is_Var r")
    case True
    then show ?thesis
    proof
      assume "is_Var l"
      then obtain x where x: "l = Var x" by auto
      show ?thesis unfolding decr_of_ord_def lr x by auto
    next
      assume "is_Var r"
      then obtain x where x: "r = Var x" by auto
      show ?thesis unfolding decr_of_ord_def lr x by auto
    qed
  next
    case False
    from False obtain lf ts where l: "l = Fun lf ts" by (cases l, auto)
    from False obtain lg us where r: "r = Fun lg us" by (cases r, auto)
    obtain f l1 where lf: "LD lf = (f,l1)" by force    
    obtain g l2 where lg: "LD lg = (g,l2)" by force
    let ?n = "length ts"
    show ?thesis 
      unfolding lr decr_of_ord_def l r
        check_sl_decr'_rule.simps lge_to_lgr_rel_def Let_def lf lg split 
      using lf lg LD_LC by auto
  qed
qed

definition check_sl_decr' :: "('f,'l,'lf)lcompose \<Rightarrow> ('lf,'f,'l)ldecompose \<Rightarrow> ('f,'l)labels \<Rightarrow> 
  ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l => bool) \<Rightarrow> ('lf :: showl,'v :: showl)rules \<Rightarrow> showsl check"
  where "check_sl_decr' LC LD LS lge D \<equiv> check_allm (\<lambda> lr. 
    check (check_sl_decr'_rule LC LD LS lge lr) (showsl_rule lr \<circ> showsl_lit (STR '' is not a decreasing rule''))) D"
  
lemma (in sl_interpr_root_same_show) check_sl_decr': "isOK(check_sl_decr' LC LD LS lge D) = 
   (set D \<subseteq> Decr)"
  unfolding check_sl_decr'_def using check_sl_decr'_rule by auto

record ('f,'c,'l,'v)sl_ops = 
  sl_L :: "('f,'c,'l)label"
  sl_LS :: "('f,'l)labels" 
  sl_I :: "('f,'c)inter"
  sl_C :: "'c list"
  sl_c :: "'c"
  sl_check_decr :: "('f,'v)rules \<Rightarrow> showsl check"
  sl_L'' :: "('f,'c,'l)label"
  sl_LS'' :: "('f,'l)labels" 
  sl_lgen :: "'l \<Rightarrow> 'l list"
  sl_LS_gen :: "'f \<Rightarrow> nat \<Rightarrow> 'l list"

(* TODO: think about, whether it is a good idea to add the 
   signature of Q or not (for root-labeling)
   in the following processors
   (since it will produce more rules, it is possible not a good idea)
   (but then default symbol is attached in Q which is also not nice)
*)
definition
  sem_lab_fin_tt ::
    "('f, 'v) splitter \<Rightarrow> ('f, 'l, 'f) lcompose \<Rightarrow> ('f, 'f, 'l) ldecompose \<Rightarrow> 
     ('c \<Rightarrow> 'c :: showl \<Rightarrow> bool) \<Rightarrow>
     ('tp, 'f :: showl, 'v :: showl) tp_ops \<Rightarrow>
     (('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f, 'c, 'l, 'v) sl_ops) \<Rightarrow>
     ('f, 'v) term list \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     'tp proc"
where
  "sem_lab_fin_tt splitter LC LD cge I gen lQ lAll tp = do {
    ops \<leftarrow> gen (funas_trs_impl (tp_ops.rules I tp)) []; 
    let check_ml = check_sl_model_lab_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_C ops) cge LC;
    let check_d = sl_ops.sl_check_decr ops;
    sem_lab_rel_tt splitter LD I succeed check_d check_ml lQ lAll tp
  }"


definition
  sem_lab_fin_proc ::
    "('f, 'l, 'f) lcompose \<Rightarrow> ('f, 'f, 'l) ldecompose \<Rightarrow> 
     ('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow>
     (('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f, 'c :: showl, 'l, 'v) sl_ops) \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     ('f, 'v) term list \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_fin_proc LC LD I gen lPAll lQ lRAll dp = do {
    ops \<leftarrow> gen (list_union (funas_trs_impl (dpp_ops.rules I dp)) (funas_args_trs_impl (dpp_ops.pairs I dp))) [];
    let check_q' = check_sl_Q' (sl_ops.sl_I ops) (sl_ops.sl_L ops) LC (sl_ops.sl_C ops);
    let check_ml = check_sl_model_lab_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_C ops) (=) LC;
    let check_l = check_sl_lab_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_C ops) (=) LC;
    let check_l' = check_sl_lab' (sl_ops.sl_I ops) (sl_ops.sl_L ops) LC (sl_ops.sl_C ops);
    sem_lab_proc LD I succeed check_q' check_l check_l' check_ml lPAll lQ lRAll dp
  }"

definition
  sem_lab_fin_root_proc ::
    "('f, 'l, 'f) lcompose \<Rightarrow> ('f, 'f, 'l) ldecompose \<Rightarrow> 
     ('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow>
     (('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f, 'c :: showl, 'l, 'v) sl_ops) \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     ('f, 'v) term list \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_fin_root_proc LC LD I gen lPAll lQ lRAll dp = do {
    let pairs = dpp_ops.pairs I dp;
    ops \<leftarrow> gen (list_union (funas_trs_impl (dpp_ops.rules I dp)) (funas_args_trs_impl pairs)) (roots_trs_impl pairs);
    let check_q' = check_sl_Q' (sl_ops.sl_I ops) (sl_ops.sl_L ops) LC (sl_ops.sl_C ops);
    let check_ml = check_sl_model_lab_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_C ops) (=) LC;
    let check_l = check_sl_lab_root_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_L'' ops) (sl_ops.sl_C ops) LC;
    let check_l' = check_sl_lab' (sl_ops.sl_I ops) (sl_ops.sl_L ops) LC (sl_ops.sl_C ops);
    sem_lab_root_proc LD I succeed check_q' check_l check_l' check_ml lPAll lQ lRAll dp
  }"

definition
  sem_lab_fin_quasi_root_proc ::
    "('f, 'l, 'f) lcompose \<Rightarrow> ('f, 'f, 'l) ldecompose \<Rightarrow> 
     ('c \<Rightarrow> 'c :: showl \<Rightarrow> bool) \<Rightarrow>
     ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow>
     ('dpp, 'f :: showl, 'v :: showl) dpp_ops \<Rightarrow>
     (('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f, 'c, 'l, 'v) sl_ops) \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     ('f, 'v) term list \<Rightarrow>
     ('f, 'v) rules \<Rightarrow> 
     'dpp proc"
where
  "sem_lab_fin_quasi_root_proc LC LD cge lge I gen lPAll lQ lRAll dp = do {
    let pairs = dpp_ops.pairs I dp;
    ops \<leftarrow> gen (list_union (funas_trs_impl (dpp_ops.rules I dp)) (funas_args_trs_impl pairs)) (roots_trs_impl pairs);
    let check_d = sl_ops.sl_check_decr ops;
    let check_d' = check_sl_decr' LC LD (sl_ops.sl_LS ops) lge;
    let check_q' = check_sl_lab_lhss_more LC (sl_ops.sl_LS_gen ops);
    let check_ml = check_sl_model_lab_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_C ops) cge LC;
    let check_l = check_sl_lab_all_trs (sl_ops.sl_I ops) (sl_ops.sl_L ops) (sl_ops.sl_L'' ops) (sl_ops.sl_C ops) (sl_ops.sl_lgen ops) LC;
    let check_l' = check_Lab_all_trs LC LD (sl_ops.sl_LS ops);
    sem_lab_quasi_root_proc LD I succeed check_d check_d' check_q' check_l check_l' check_ml lPAll lQ lRAll dp
  }"

locale sl_finite_impl =
 fixes LC :: "('f :: showl,'l,'f)lcompose"
   and LD :: "('f,'f,'l)ldecompose"
   and cge :: "'c :: showl \<Rightarrow> 'c \<Rightarrow> bool"
   and lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
   and sl_gen :: "('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f,'c,'l,'v :: showl)sl_ops"
 assumes sl_gen_inter: "sl_gen F G = Inr ops \<Longrightarrow>
  sl_interpr_root_same (set (sl_ops.sl_C ops)) (sl_ops.sl_c ops) (sl_ops.sl_I ops) cge lge (sl_ops.sl_L ops) LC LD (sl_ops.sl_LS ops) (sl_ops.sl_L'' ops) (sl_ops.sl_LS'' ops)"
  and sl_gen_decr: "sl_gen F G = Inr ops \<Longrightarrow>
   isOK(sl_ops.sl_check_decr ops D) \<Longrightarrow> decr_of_ord (lge_to_lgr_rel lge (sl_ops.sl_LS ops)) LC (sl_ops.sl_LS ops) \<subseteq> (subst.closure (set D) \<inter> decr_of_ord (lge_to_lgr_rel lge (sl_ops.sl_LS ops)) LC (sl_ops.sl_LS ops))^+"
  and sl_gen_lgen: "\<And> f n l l'. sl_gen F G = Inr ops \<Longrightarrow> lge f n l l' \<Longrightarrow> l' \<in> set (sl_ops.sl_lgen ops l)"
begin

lemma sem_lab_fin_tt: assumes J: "tp_spec J"
  shows "tp_spec.sound_tt_impl J (sem_lab_fin_tt splitter LC LD cge J sl_gen lQ lAll)"
proof -
  interpret tp_spec J by fact
  show ?thesis unfolding sound_tt_impl_def
  proof (clarify)
    fix tp tp'
    assume ok: "sem_lab_fin_tt splitter LC LD cge J sl_gen lQ lAll tp = return tp'"
    and SN: "SN_qrel (tp_ops.qreltrs J tp')"
    note ok = ok[unfolded sem_lab_fin_tt_def]
    let ?F = "funas_trs_impl (tp_ops.rules J tp)"
    from ok obtain ops where gen: "sl_gen ?F [] = Inr ops" 
      by (cases "sl_gen ?F []", auto)
    let ?C = "sl_C ops"
    let ?I = "sl_I ops"
    let ?c = "sl_c ops"
    let ?L = "sl_L ops"
    let ?LS = "sl_LS ops"
    let ?L' = "sl_L'' ops"
    let ?LS' = "sl_LS'' ops"
    let ?cml = "check_sl_model_lab_trs ?I ?L ?C cge LC"
    let ?cd = "sl_check_decr ops"
    from sl_gen_inter[OF gen]
    interpret sl_interpr_root_same "set ?C" ?c ?I cge lge ?L LC LD ?LS ?L' ?LS' .
    interpret sl_interpr_impl "\<lambda> _ _. error id" "\<lambda> _ _. error id" "\<lambda> _ _. error id" "\<lambda> _ _.error id" "\<lambda> _ _.error id" ?cml "\<lambda> _ _. error id" "\<lambda> _ _. error id" ?cd "\<lambda> _. error id" succeed "set ?C" ?c ?I cge lge ?L ?LS LC LD ?L' ?LS'
      by (unfold_locales, simp, simp, simp, simp, simp, rule
      check_sl_model_lab_trs_sound, insert sl_gen_decr[OF gen], auto)
    from ok[unfolded gen]
    have "sem_lab_rel_tt splitter LD J succeed ?cd
      ?cml lQ lAll tp = Inr tp'" by auto
    with sem_lab_rel_tt[OF J] SN
    show "SN_qrel (tp_ops.qreltrs J tp)"
      unfolding sound_tt_impl_def by blast
  qed
qed

lemma sem_lab_fin_proc: assumes J: "dpp_spec J"
  and cge: "cge = (=)"
  and lge: "lge = (\<lambda> _ _. (=))"
  and inj: "\<And> F G f ops. sl_gen F G = Inr ops \<Longrightarrow> inj (sl_L ops f)"
  shows "dpp_spec.sound_proc_impl J (sem_lab_fin_proc LC LD J sl_gen lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis unfolding sound_proc_impl_def
  proof (clarify)
    fix dp dp'
    assume ok: "sem_lab_fin_proc LC LD J sl_gen lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    note ok = ok[unfolded sem_lab_fin_proc_def]
    let ?F = "list_union (funas_trs_impl (dpp_ops.rules J dp)) (funas_args_trs_impl (dpp_ops.pairs J dp))"
    let ?G = "[]"
    from ok obtain ops where gen: "sl_gen ?F ?G = Inr ops" 
      by (cases "sl_gen ?F ?G", auto)
    let ?C = "sl_C ops"
    let ?I = "sl_I ops"
    let ?c = "sl_c ops"
    let ?L = "sl_L ops"
    let ?LS = "sl_LS ops"
    let ?L' = "sl_L'' ops"
    let ?LS' = "sl_LS'' ops"
    let ?cml = "check_sl_model_lab_trs ?I ?L ?C (=) LC"
    let ?cl = "check_sl_lab_trs ?I ?L ?C (=) LC"
    let ?cl' = "check_sl_lab' ?I ?L LC ?C"
    let ?q' = "check_sl_Q' ?I ?L LC ?C"
    from sl_gen_inter[OF gen, unfolded cge lge]
    interpret sl_interpr_root_same "set ?C" ?c ?I model_cge model_lge ?L LC LD ?LS ?L' ?LS' .
    interpret sl_interpr_impl ?q' ?cl "\<lambda> _ _. error id" "\<lambda> _ _. error id" ?cl' ?cml "\<lambda> _ _. error id" "\<lambda> _ _. error id" "\<lambda> _. error id" "\<lambda> _. error id" succeed "set ?C" ?c ?I model_cge model_lge ?L ?LS LC LD ?L' ?LS'
      by (unfold_locales,  
        rule check_sl_Q', simp,
        rule check_sl_lab_trs_sound, simp,
        simp, simp,
        rule check_sl_lab', simp,
        rule check_sl_model_lab_trs_sound, auto)
    from ok[unfolded gen]
    have "sem_lab_proc LD J succeed
      ?q' ?cl ?cl' ?cml lPAll lQ lRAll dp = Inr dp'" by auto
    with sem_lab_proc[OF J inj[OF gen]] fin
    show "finite_dpp (dpp_ops.dpp J dp)"
      unfolding sound_proc_impl_def by blast
  qed
qed

lemma sem_lab_fin_root_proc: assumes J: "dpp_spec J"
  and cge: "cge = (=)"
  and lge: "lge = (\<lambda> _ _. (=))"
  and inj: "\<And> F G f ops. sl_gen F G = Inr ops \<Longrightarrow> inj (sl_L ops f)"
  shows "dpp_spec.sound_proc_impl J (sem_lab_fin_root_proc LC LD J sl_gen lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis unfolding sound_proc_impl_def
  proof (clarify)
    fix dp dp'
    assume ok: "sem_lab_fin_root_proc LC LD J sl_gen lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    note ok = ok[unfolded sem_lab_fin_root_proc_def Let_def]
    let ?F = "list_union (funas_trs_impl (dpp_ops.rules J dp)) (funas_args_trs_impl (dpp_ops.pairs J dp))"
    let ?G = "roots_trs_impl (dpp_ops.pairs J dp)"
    from ok obtain ops where gen: "sl_gen ?F ?G = Inr ops" 
      by (cases "sl_gen ?F ?G", auto)
    let ?C = "sl_C ops"
    let ?I = "sl_I ops"
    let ?c = "sl_c ops"
    let ?L = "sl_L ops"
    let ?LS = "sl_LS ops"
    let ?L' = "sl_L'' ops"
    let ?LS' = "sl_LS'' ops"
    let ?cml = "check_sl_model_lab_trs ?I ?L ?C (=) LC"
    let ?cl = "check_sl_lab_trs ?I ?L ?C (=) LC"
    let ?clr = "check_sl_lab_root_trs ?I ?L ?L' ?C LC"
    let ?cl' = "check_sl_lab' ?I ?L LC ?C"
    let ?q' = "check_sl_Q' ?I ?L LC ?C"
    from sl_gen_inter[OF gen, unfolded cge lge]
    interpret sl_interpr_root_same "set ?C" ?c ?I model_cge model_lge ?L LC LD ?LS ?L' ?LS' .
    interpret sl_interpr_impl ?q' ?cl ?clr "\<lambda> _ _. error id" ?cl' ?cml "\<lambda> _ _. error id" "\<lambda> _ _. error id" 
      "\<lambda> _. error id" "\<lambda> _. error id" succeed "set ?C" ?c ?I model_cge model_lge ?L ?LS LC LD ?L' ?LS'
      by (unfold_locales, 
        rule check_sl_Q', simp,
        rule check_sl_lab_trs_sound, simp,
        rule check_sl_lab_root_trs_sound, simp,
        simp,
        rule check_sl_lab', simp,
        rule check_sl_model_lab_trs_sound, auto)
    from ok[unfolded gen]
    have "sem_lab_root_proc LD J succeed
      ?q' ?clr ?cl' ?cml lPAll lQ lRAll dp = Inr dp'" by auto
    with sem_lab_root_proc[OF J inj[OF gen]] fin
    show "finite_dpp (dpp_ops.dpp J dp)"
      unfolding sound_proc_impl_def by blast
  qed
qed
end

locale sl_finite_LS_impl = sl_finite_impl +
 assumes sl_LS_gen: "\<And> f n. sl_gen F G = Inr ops \<Longrightarrow> set (sl_ops.sl_LS_gen ops f n) = Collect (sl_ops.sl_LS ops f n)"
begin

lemma sem_lab_fin_quasi_root_proc: assumes J: "dpp_spec J"
  shows "dpp_spec.sound_proc_impl J (sem_lab_fin_quasi_root_proc LC LD cge lge J sl_gen lPAll lQ lRAll)"
proof -
  interpret dpp_spec J by fact
  show ?thesis unfolding sound_proc_impl_def
  proof (clarify)
    fix dp dp'
    assume ok: "sem_lab_fin_quasi_root_proc LC LD cge lge J sl_gen lPAll lQ lRAll dp = return dp'"
    and fin: "finite_dpp (dpp_ops.dpp J dp')"
    note ok = ok[unfolded sem_lab_fin_quasi_root_proc_def Let_def]
    let ?F = "list_union (funas_trs_impl (dpp_ops.rules J dp)) (funas_args_trs_impl (dpp_ops.pairs J dp))"
    let ?G = "roots_trs_impl (dpp_ops.pairs J dp)"
    from ok obtain ops where gen: "sl_gen ?F ?G = Inr ops" 
      by (cases "sl_gen ?F ?G", auto)
    let ?C = "sl_C ops"
    let ?I = "sl_I ops"
    let ?c = "sl_c ops"
    let ?L = "sl_L ops"
    let ?LS = "sl_LS ops"
    let ?L' = "sl_L'' ops"
    let ?LS' = "sl_LS'' ops"
    let ?LS_gen = "sl_LS_gen ops"
    let ?lgen = "sl_lgen ops"
    let ?cml = "check_sl_model_lab_trs ?I ?L ?C cge LC"
    let ?cl = "check_sl_lab_trs ?I ?L ?C cge LC"
    let ?cd = "sl_check_decr ops"
    let ?cd' = "check_sl_decr' LC LD ?LS lge"
    let ?clr = "check_sl_lab_all_trs ?I ?L ?L' ?C ?lgen LC"
    let ?cla = "check_Lab_all_trs LC LD ?LS"
    let ?cllm = "check_sl_lab_lhss_more LC ?LS_gen"
    from sl_gen_inter[OF gen]
    interpret sl_interpr_root_same "set ?C" ?c ?I cge lge ?L LC LD ?LS ?L' ?LS' .
    interpret sl_interpr_root_same_show "set ?C" ?c ?I cge lge ?L LC LD ?LS ?L' ?LS' ..
    interpret sl_interpr_impl "\<lambda> _ _.error id" ?cl "\<lambda> _ _. error id" ?clr "\<lambda> _ _. error id" ?cml ?cla ?cllm
      ?cd ?cd' succeed "set ?C" ?c ?I cge lge ?L ?LS LC LD ?L' ?LS'
      by (unfold_locales, 
        simp,
        rule check_sl_lab_trs_sound, simp,
        simp,
        rule check_sl_lab_all_trs_sound[OF _ sl_gen_lgen[OF gen]], simp, simp,
        simp,
        rule check_sl_model_lab_trs_sound, simp,
        unfold check_Lab_all_trs, simp,
        rule check_sl_lab_lhss_more[OF sl_LS_gen[OF gen]], simp,
        rule sl_gen_decr[OF gen], simp,
        unfold check_sl_decr', simp)
    from ok[unfolded gen]
    have "sem_lab_quasi_root_proc LD J succeed ?cd ?cd'
      ?cllm ?clr ?cla ?cml lPAll lQ lRAll dp = Inr dp'" by auto
    with sem_lab_quasi_root_proc[OF J]
    show "finite_dpp (dpp_ops.dpp J dp)"
      using fin
      unfolding sound_proc_impl_def 
      by blast
  qed
qed
end

(* for models, a simplified version can be taken *)
record ('f,'c,'l,'v)slm_ops = 
  slm_L :: "('f,'c,'l)label"
  slm_I :: "('f,'c)inter"
  slm_C :: "'c list"
  slm_c :: "'c"
  slm_L'' :: "('f,'c,'l)label"

definition slm_to_sl :: "('f,'c,'l,'v)slm_ops \<Rightarrow> ('f,'c,'l,'v)sl_ops"
  where "slm_to_sl ops \<equiv> \<lparr>
    sl_L = slm_ops.slm_L ops,
    sl_LS = \<lambda> _ _ _. True,
    sl_I = slm_ops.slm_I ops,
    sl_C = slm_ops.slm_C ops,
    sl_c = slm_ops.slm_c ops,
    sl_check_decr = (\<lambda> _.succeed),
    sl_L'' = slm_ops.slm_L'' ops,
    sl_LS'' = \<lambda> _ _ _. True,
    sl_lgen = \<lambda> l. [l],
    sl_LS_gen = \<lambda> _ _. []
  \<rparr>"

definition slm_gen_to_sl_gen :: "(('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f,'c,'l,'v)slm_ops) \<Rightarrow>
  ('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f,'c,'l,'v)sl_ops"
where "slm_gen_to_sl_gen gen \<equiv> \<lambda> F G. do { ops \<leftarrow> gen F G; return (slm_to_sl ops)}"


locale sl_finite_model_impl =
 fixes LC :: "('f :: showl,'l,'f)lcompose"
   and LD :: "('f,'f,'l)ldecompose"
   and slm_gen :: "('f \<times> nat) list \<Rightarrow> ('f \<times> nat) list \<Rightarrow> showsl + ('f,'c :: showl,'l,'v :: showl)slm_ops"
 assumes LD_LC: "LD (LC f n l) = (f,l)"
  and slm_gen: "slm_gen F G = Inr ops \<Longrightarrow>
  slm_ops.slm_c ops \<in> set (slm_ops.slm_C ops) \<and> wf_inter (slm_ops.slm_I ops) (set (slm_ops.slm_C ops))"
begin

lemma sl_finite_impl: "sl_finite_impl LC LD model_cge model_lge (slm_gen_to_sl_gen slm_gen)"
  unfolding sl_finite_impl_def decr_empty
proof (intro allI impI conjI)
  fix F G ops
  assume ops: "slm_gen_to_sl_gen slm_gen F G = Inr ops"
  then obtain opss where opss: "slm_gen F G = Inr opss"
    unfolding slm_gen_to_sl_gen_def by (cases "slm_gen F G", auto)
  from opss ops have ops: "ops = slm_to_sl opss" 
    unfolding slm_gen_to_sl_gen_def by auto
  show "sl_interpr_root_same (set (sl_C ops)) (sl_c ops) (sl_I ops) model_cge model_lge (sl_L ops) LC LD (sl_LS ops) (sl_L'' ops) (sl_LS'' ops)" unfolding ops slm_to_sl_def sl_ops.simps
    by (unfold_locales, insert slm_gen[OF opss],
      auto simp: wf_label_def cge_wm lge_wm lge_to_lgr_def lge_to_lgr_rel_def LD_LC)
next
  fix F G ops f n and l l' :: 'l
  assume ops: "slm_gen_to_sl_gen slm_gen F G = Inr ops" and id: "l = l'"
  then obtain opss where opss: "slm_gen F G = Inr opss"
    unfolding slm_gen_to_sl_gen_def by (cases "slm_gen F G", auto)
  from opss ops have ops: "ops = slm_to_sl opss" 
    unfolding slm_gen_to_sl_gen_def by auto
  show "l' \<in> set (sl_lgen ops l)" unfolding ops id slm_to_sl_def by auto
qed auto
end

sublocale sl_finite_model_impl \<subseteq> sl_finite_impl LC LD model_cge model_lge "slm_gen_to_sl_gen slm_gen"
  by (rule sl_finite_impl)

context sl_finite_model_impl
begin
lemma sem_lab_fin_model_proc: assumes J: "dpp_spec J"
  and inj: "\<And> F G ops f. slm_gen F G = Inr ops \<Longrightarrow> inj (slm_L ops f)"
  shows "dpp_spec.sound_proc_impl J (sem_lab_fin_proc LC LD J (slm_gen_to_sl_gen slm_gen) lPAll lQ lRAll)"
proof (rule sem_lab_fin_proc[OF J refl refl])
  fix F G f ops
  assume "slm_gen_to_sl_gen slm_gen F G = Inr ops"
  then show "inj (sl_L ops f)"
    unfolding slm_gen_to_sl_gen_def inj_on_def
    by (cases "slm_gen F G", insert inj[unfolded inj_on_def], auto simp: slm_to_sl_def)
qed

lemma sem_lab_fin_model_root_proc: assumes J: "dpp_spec J"
  and inj: "\<And> F G ops f. slm_gen F G = Inr ops \<Longrightarrow> inj (slm_L ops f)"
  shows "dpp_spec.sound_proc_impl J (sem_lab_fin_root_proc LC LD J (slm_gen_to_sl_gen slm_gen) lPAll lQ lRAll)"
proof (rule sem_lab_fin_root_proc[OF J refl refl])
  fix F G f ops
  assume "slm_gen_to_sl_gen slm_gen F G = Inr ops"
  then show "inj (sl_L ops f)"
    unfolding slm_gen_to_sl_gen_def inj_on_def
    by (cases "slm_gen F G", insert inj[unfolded inj_on_def], auto simp: slm_to_sl_def)
qed
end

end
