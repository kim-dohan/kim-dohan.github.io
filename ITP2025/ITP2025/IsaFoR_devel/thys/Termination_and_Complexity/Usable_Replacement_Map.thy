(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2014, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Replacement_Map
imports 
  Ord.Term_Order
  TRS.Q_Relative_Rewriting
  Icap
  TRS.QDP_Framework
  Auxx.Name
  Complexity_Framework
  Innermost_Usable_Rules
begin      

subsection \<open>usable replacement maps and compatibility, taken from Diss Avanzini\<close>
context 
  fixes \<mu> :: "'f af"
begin
(* deviation: Avanzini uses positions and subterms instead *)
definition af_nf_compatible_terms :: "('f,'v)trs \<Rightarrow> ('f,'v)terms" where
  "af_nf_compatible_terms rel \<equiv> { t . \<forall> C s. t = C\<langle>s\<rangle> \<longrightarrow> af_regarded_pos \<mu> t (hole_pos C) \<or> s \<in> NF rel}"

lemma af_nf_compatible_terms_full_af: assumes full: "\<mu> = full_af"
  shows "s \<in> af_nf_compatible_terms rel"
  unfolding af_nf_compatible_terms_def
  by (auto simp: af_regarded_full full)

lemma af_nf_compatible_terms_mono: assumes rel: "rel' \<subseteq> rel"
  shows "af_nf_compatible_terms rel \<subseteq> af_nf_compatible_terms rel'" 
  unfolding af_nf_compatible_terms_def using NF_anti_mono[OF rel] by blast

definition usable_replacement_map :: "('f,'v)terms \<Rightarrow> bool \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)terms \<Rightarrow> ('f,'v)trs \<Rightarrow> bool" where
  "usable_replacement_map T nfs P Q R \<equiv> 
  (qrstep nfs Q P) ^* `` T \<subseteq> af_nf_compatible_terms (qrstep nfs Q R)"

lemma usable_replacement_map_mono: assumes T: "T' \<subseteq> T" and P: "P' \<subseteq> P" and R: "R' \<subseteq> R"
  shows "usable_replacement_map T nfs P Q R \<Longrightarrow> usable_replacement_map T' nfs P' Q R'"
  unfolding usable_replacement_map_def
  using rtrancl_mono[OF qrstep_mono[OF P subset_refl, of nfs Q]] T
    af_nf_compatible_terms_mono[OF qrstep_mono[OF R subset_refl, of nfs Q]] by blast

lemma avanzini_14_9_1:
  assumes us: "usable_replacement_map T nfs (S \<union> W) Q R" and "R \<subseteq> S \<union> W"
  and R: "R \<subseteq> ord" and mono: "af_monotone \<pi> ord" and af: "af_subset \<mu> \<pi>" and subst: "subst.closed ord"
  and s: "s \<in> (qrstep nfs Q (S \<union> W))^* `` T" and step: "(s,t) \<in> qrstep nfs Q R" 
  shows "(s,t) \<in> ord"
proof -
  from us[unfolded usable_replacement_map_def] s have 
  s_af: "s \<in> af_nf_compatible_terms (qrstep nfs Q R)" by auto
  from qrstepE[OF step] obtain l r C \<sigma> where 
    nf: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and
    lr: "(l, r) \<in> R" and
    s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and
    t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and
    nfs: "NF_subst nfs (l, r) \<sigma> Q" .
  then have "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R" (is "(?l,?r) \<in> _") by auto
  with s_af[unfolded af_nf_compatible_terms_def, simplified, rule_format, OF s]
  have rp: "af_regarded_pos \<mu> C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos C)" by auto
  from lr R have "(l,r) \<in> ord" by auto
  from subst.closedD[OF subst this] have lr: "(?l,?r) \<in> ord" by auto
  have "(C\<langle>?l\<rangle>, C\<langle>?r\<rangle>) \<in> ord"
    by (rule af_monotone_af_regarded_posD[OF af_subset_af_monotone[OF af mono] rp lr])
  with s t show ?thesis by auto
qed
end

lemma usable_replacement_map_full_af[simp]: "usable_replacement_map full_af T nfs R Q R'"
  unfolding usable_replacement_map_def using af_nf_compatible_terms_full_af[OF refl] by auto


(* deviation: currently we do not support separate af for weak order! 
  reason: the reduction pair requirement already demands full monotonicity *)
context compat_redpair_order
begin

context 
  fixes \<mu>
  assumes \<mu>: "af_monotone \<mu> S"
begin
definition NS_\<mu> :: "'f af" where "NS_\<mu> = full_af"
lemma NS_\<mu>: "af_monotone NS_\<mu> NS" 
  by (rule ctxt_closed_imp_af_monotone[OF ctxt_NS])

lemma usable_replacement_map_NS: "usable_replacement_map NS_\<mu> T nfs P Q R"
  unfolding usable_replacement_map_def
  using af_nf_compatible_terms_full_af[OF NS_\<mu>_def] by blast


lemma avanzini_14_9_2: assumes compatR: "Rs \<subseteq> S" "Rw \<subseteq> NS" and
  usable: "usable_replacement_map \<mu>' T nfs (Rs \<union> Rw) Q Rs"
  and af: "af_subset \<mu>' \<mu>"
  and step: "(s,t) \<in> relto (qrstep nfs Q Rs) (qrstep nfs Q Rw)"
  and s: "s \<in> (qrstep nfs Q (Rs \<union> Rw))^* `` T" (is "s \<in> ?T")
  shows "(s,t) \<in> S"
proof -
  have subset: "Rs \<subseteq> Rs \<union> Rw" "Rw \<subseteq> Rs \<union> Rw" by auto
  note strict = avanzini_14_9_1[OF usable subset(1) compatR(1) \<mu> af subst_S]
  note weak = avanzini_14_9_1[OF usable_replacement_map_NS subset(2) compatR(2) NS_\<mu> af_subset_refl subst_NS, of _ nfs Q T]
  let ?Rs = "qrstep nfs Q Rs" let ?Rw = "qrstep nfs Q Rw" let ?P = "qrstep nfs Q (Rs \<union> Rw)"
  from step obtain u v where su: "(s,u) \<in> ?Rw^*" and uv: "(u,v) \<in> ?Rs" and vt: "(v,t) \<in> ?Rw^*" by auto
  have [simp]: "\<And> s. (s,s) \<in> NS" using refl_NS[unfolded refl_on_def] by auto
  {
    fix s t R
    assume s: "s \<in> ?T" and R: "(s,t) \<in> qrstep nfs Q R"
      "R \<subseteq> Rs \<union> Rw"
    from qrstep_mono[OF R(2)] R(1) have "(s,t) \<in> ?P" by blast
    with s have "t \<in> ?T"
      by (metis r_into_rtrancl rtrancl_Image_step) 
  } note T = this
  {
    fix s u
    assume s: "s \<in> ?T" and su: "(s,u) \<in> ?Rw^*"
    from su have "(s,u) \<in> NS \<and> u \<in> ?T"
    proof (induct)
      case (step t u)
      from weak[OF _ step(2)] step(3) have "(t,u) \<in> NS" by auto
      from trans_NS_point[OF _ this] step(3) have su: "(s,u) \<in> NS" by auto
      from T[OF _ step(2)] step(3) have "u \<in> ?T" by auto
      with su show ?case by auto
    qed (insert s, auto)
    then have "(s,u) \<in> NS" "u \<in> ?T" by auto
  } note steps = this
  from steps[OF s su] have su: "(s,u) \<in> NS" and u: "u \<in> ?T" .
  from T[OF u uv] have v: "v \<in> ?T" by auto
  from strict[OF u uv] have uv: "(u,v) \<in> S" .
  from steps[OF v vt] have vt: "(v,t) \<in> NS" by auto
  from compat_NS_S_point[OF su uv] have sv: "(s,v) \<in> S" .
  from compat_S_NS_point[OF sv vt] show "(s,t) \<in> S" .
qed

theorem avanzini_14_10: assumes compatR: "Rs \<subseteq> S" "Rw \<subseteq> NS" and
  usable: "usable_replacement_map \<mu>' (terms_of cm) nfs (Rs \<union> Rw) Q Rs" and
  af: "af_subset \<mu>' \<mu>" and
  bound: "deriv_bound_measure_class S cm cc"
shows "deriv_bound_measure_class (relto (qrstep nfs Q Rs) (qrstep nfs Q Rw)) cm cc"
  (is "deriv_bound_measure_class ?P cm cc")
proof -
  let ?T = "(qrstep nfs Q (Rs \<union> Rw))^* `` terms_of cm"
  note d = deriv_bound_measure_class_def deriv_bound_rel_class_def deriv_bound_rel_def
  from bound[unfolded d] obtain f where f: "f \<in> O_of cc" 
    and bound: "\<And> n t. t \<in> terms_of_nat cm n \<Longrightarrow> deriv_bound S t (f n)"
    by auto
  show ?thesis unfolding d
  proof (intro exI conjI allI impI, rule f)
    fix n t
    assume t: "t \<in> terms_of_nat cm n"
    from bound[OF t] have bound: "deriv_bound S t (f n)" by auto
    from t have t: "t \<in> ?T" by (auto simp: terms_of)
    note d = deriv_bound_def
    note main = avanzini_14_9_2[OF compatR usable af]
    show "deriv_bound ?P t (f n)" 
    proof (rule ccontr)
      assume "\<not> ?thesis"
      from this[unfolded d]
      obtain s where ts: "(t,s) \<in> ?P ^^ (Suc (f n))" by auto
      define m where "m = Suc (f n)"
      from ts have "(t,s) \<in> S ^^ (Suc (f n)) \<and> s \<in> ?T" unfolding m_def[symmetric]
      proof (induct m arbitrary: s)
        case (Suc m s)
        from Suc(2)[simplified] obtain u where tus: "(t,u) \<in> ?P^^m" and uss: "(u,s) \<in> ?P" by auto
        from Suc(1)[OF tus] have tu: "(t,u) \<in> S^^m" and u: "u \<in> ?T" by auto
        from main[OF uss u] have us: "(u,s) \<in> S" .
        from tu us have ts: "(t,s) \<in> S^^(Suc m)" by auto
        from uss have "(u,s) \<in> (qrstep nfs Q (Rs \<union> Rw))^*" unfolding qrstep_union by regexp
        with u have "s \<in> ?T" by (metis rtrancl_Image_step) 
        with ts show ?case by auto
      qed (insert t, auto)
      with bound show False unfolding d by blast
    qed
  qed
qed
end
end

lemma (in compat_redpair_order) urm_mono_redpair_sound:
  assumes weakR: "(R \<union> Rw) - Rs \<subseteq> NS"
  and nonStrict: "P \<union> Pw \<subseteq> NS \<union> S"
  and strictP: "Ps \<subseteq> S"
  and strictR: "Rs \<subseteq> S"
  and inn: "NF_terms Q \<subseteq> NF_trs (R \<union> Rw)"
  and urm: "\<And> s t \<sigma>. (s,t) \<in> P \<union> Pw \<Longrightarrow> s \<cdot> \<sigma> \<in> NF_terms Q \<Longrightarrow> usable_replacement_map \<mu>' {t \<cdot> \<sigma>} nfs (R \<union> Rw) Q (Rs \<inter> (R \<union> Rw))" 
  and af: "af_subset \<mu>' \<mu>" 
  and mono: "af_monotone \<mu> S"
  and chain: "min_ichain (nfs,m,P,Pw,Q,R,Rw) s t \<sigma>"
  shows  "\<exists> j. min_ichain (nfs,m,P - Ps, Pw - Ps, Q, R - Rs, Rw - Rs) (shift s j) (shift t j) (shift \<sigma> j)"
proof (rule min_ichain_split[OF chain], rule)
  let ?R = "R \<union> Rw"
  let ?P = "P \<union> Pw"
  assume chain: "min_ichain (nfs,m,Ps \<inter> ?P, ?P - Ps, Q, Rs \<inter> ?R, ?R - Rs) s t \<sigma>"
  have id: "Ps \<inter> ?P \<union> (?P - Ps) = ?P" by auto
  have idR: "Rs \<inter> ?R \<union> (?R - Rs) = ?R" by auto
  have idS: "S \<union> NS = NS \<union> S" by auto
  note chain = chain[unfolded min_ichain.simps ichain.simps minimal_cond_def id idR]
  from chain have P: "\<And> i. (s i, t i) \<in> ?P" by auto
  from chain have steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q ?R)^*" by auto
  from chain have Q: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q" by auto
  {
    fix i u v
    assume tu: "(t i \<cdot> \<sigma> i, u) \<in> (qrstep nfs Q ?R)^*" 
      and uv: "(u,v) \<in> qrstep nfs Q (Rs \<inter> ?R)"
    then have "u \<in> (qrstep nfs Q ?R)\<^sup>* `` {t i \<cdot> \<sigma> i}" by auto
    from avanzini_14_9_1[OF urm[OF P Q] _ _ mono af subst_S this uv] strictR have "(u,v) \<in> S" by auto
    then have "(u,v) \<in> S" by auto
  } note S = this
  {
    fix u v
    assume uv: "(u,v) \<in> qrstep nfs Q (?R - Rs)"
    then have "(u,v) \<in> rstep (?R - Rs)" by auto
    with rstep_subset[OF ctxt_NS subst_NS weakR] have "(u,v) \<in> NS" by auto
    then have "(u,v) \<in> NS" by auto
  } note NS = this
  {
    fix i u v
    assume tu: "(t i \<cdot> \<sigma> i, u) \<in> (qrstep nfs Q ?R)^*" 
      and uv: "(u,v) \<in> qrstep nfs Q ?R"
    have "(u,v) \<in> NS \<union> S"
    proof (cases "(u,v) \<in> qrstep nfs Q (Rs \<inter> ?R)")
      case True
      show ?thesis using S[OF tu True] by auto
    next
      case False
      with uv have uv: "(u,v) \<in> qrstep nfs Q (?R - Rs)" 
        unfolding arg_cong[OF idR[symmetric], of "qrstep nfs Q"] 
        unfolding qrstep_union by auto
      then show ?thesis using NS[OF uv] by auto
    qed
  } note both = this
  {
    fix i u v 
    assume tu: "(t i \<cdot> \<sigma> i, u) \<in> (qrstep nfs Q ?R)^*"
    and uv: "(u,v) \<in> (qrstep nfs Q ?R)^*"
    from uv have "(u, v) \<in> (NS \<union> S)^*"
    proof (induct rule: rtrancl_induct)
      case (step v w)
      from tu step(1) have "(t i \<cdot> \<sigma> i, v) \<in> (qrstep nfs Q ?R)\<^sup>*" by auto
      from rtrancl_into_rtrancl[OF step(3) both[OF this step(2)]] show ?case .
    qed simp
  } note both_steps_gen = this
  {
    fix i u 
    assume tu: "(t i \<cdot> \<sigma> i, u) \<in> (qrstep nfs Q ?R)^*"
    have "(t i \<cdot> \<sigma> i, u) \<in> (NS \<union> S)^*"
      by (rule both_steps_gen[OF _ tu], auto)
  } note both_steps = this
  {
    fix i
    from P nonStrict have "(s i, t i) \<in> NS \<union> S" by auto
    with subst.closedD subst_NS subst_S have "(s i \<cdot> \<sigma> i, t i \<cdot> \<sigma> i) \<in> NS \<union> S" by auto
  } note both_P = this
  let ?NSS = "NS \<union> S"
  let ?S = "?NSS^* O S O ?NSS^*"
  let ?NS = "?NSS^*"
  let ?t = "\<lambda> i. t i \<cdot> \<sigma> i"
  let ?s = "\<lambda> i. s i \<cdot> \<sigma> i"
  have "\<forall> i. (?s i, ?s (Suc i)) \<in> ?NS \<union> ?S"
  proof 
    fix i
    from both_P[of i] both_steps[OF steps[of i]]
    have "(?s i, ?s (Suc i)) \<in> ?NSS O ?NS" by auto
    then show "(?s i, ?s (Suc i)) \<in> ?NS \<union> ?S" by regexp
  qed
  note main = non_strict_ending[OF this]
  have "?NS O ?S \<subseteq> ?S" by regexp
  note main = main[OF this]
  have "SN ?S" 
    by (rule compatible_SN'[OF compat_NS_S SN]) 
  then have "\<And> T. SN_on ?S T" unfolding SN_defs by blast
  note main = main[OF this]
  from main obtain n where n: "\<And> m. m \<ge> n \<Longrightarrow> (?s m, ?s (Suc m)) \<notin> ?S" by blast
  let ?Q = "qrstep nfs Q ?R"
  let ?QQ = "?Q^* O qrstep nfs Q (Rs \<inter> ?R) O ?Q^*"
  from chain 
  have "(INFM i. (s i, t i) \<in> Ps \<inter> ?P) \<or>
    (INFM i. (?t i, ?s (Suc i)) \<in> ?QQ)" by blast
  from this[unfolded INFM_disj_distrib[symmetric], unfolded INFM_nat]
  obtain m where m: "n < m" and alt:"(s m, t m) \<in> Ps \<inter> ?P \<or> 
        (?t m, ?s (Suc m)) \<in> ?QQ" by blast
  from n[of m] m have noS: "(?s m, ?s (Suc m)) \<notin> ?S" by auto
  from alt have "(?s m, ?s (Suc m)) \<in> ?S"
  proof
    assume "(s m, t m) \<in> Ps \<inter> ?P"
    with strictP have "(s m, t m) \<in> S" by auto
    from subst.closedD[OF subst_S this] have "(?s m, ?t m) \<in> S" by auto
    with both_steps[OF steps[of m]] have "(?s m, ?s (Suc m)) \<in> S O ?NS" by auto
    then show ?thesis by regexp
  next
    assume "(?t m, ?s (Suc m)) \<in> ?QQ"
    then obtain u v where tu: "(?t m, u) \<in> ?Q^*" and uv: "(u,v) \<in> qrstep nfs Q (Rs \<inter> ?R)"
      and vs: "(v,?s (Suc m)) \<in> ?Q^*" by auto
    from S[OF tu uv] have uvS: "(u,v) \<in> S" .
    from uv have "(u,v) \<in> qrstep nfs Q ?R" by auto
    with tu have tv: "(?t m, v) \<in> ?Q^*" by auto
    from both_steps[OF tu] have tuNS: "(?t m, u) \<in> ?NSS^*" by auto
    from both_steps_gen[OF tv vs] have vsNS: "(v, ?s (Suc m)) \<in> ?NSS^*" by auto
    from converse_rtrancl_into_rtrancl[OF both_P[of m] tuNS] have su: "(?s m, u) \<in> ?NSS^*" .
    from su uvS vsNS show ?thesis by blast
  qed
  with noS show False ..
qed

subsection \<open>computing innermost usable replacement maps from Moser/Hirokawa\<close>

context
  fixes ecap :: "('f,string)cap_fun"
  and R :: "('f,string)trs"
  and Q :: "('f,string)terms"
begin
fun get_args where
  "get_args True t = set (args t)"
| "get_args False t = {t}"
 
definition innermost_repl_map :: "('f,string)trs \<Rightarrow> (('f \<times> nat) \<times> nat) set" where
  "innermost_repl_map P \<equiv> { ((f,length rs),i) | l C f rs i b. 
    ((l,C\<langle>Fun f rs\<rangle>),b) \<in> R \<times> {True} \<union> P \<times> {False} \<and>
    i < length rs \<and>
    Inl () \<in> vars_term (ecap R Q (mv_xvar ` (get_args b l)) (mv_xvar (rs ! i)))}"

definition \<mu>_i_P :: "('f,string)trs \<Rightarrow> 'f af" where
  "\<mu>_i_P P f = { i. (f,i) \<in> innermost_repl_map P}"

definition \<mu>_i :: "'f af" where
  "\<mu>_i = \<mu>_i_P {}"

context
  fixes U :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)trs"
  and init :: "(('f,string)term list \<times> ('f,string)term \<times> ('f,string)rule)set"
begin

inductive approx_cond :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)rule \<Rightarrow> bool" and
  \<mu>_cond :: "'f \<times> nat \<Rightarrow> nat \<Rightarrow> bool"
where 
  approx_cond_init: "(ss,t,lr) \<in> init \<Longrightarrow> approx_cond ss t lr"
| approx_cond_rec: "approx_cond ss (Fun f ts) (l,r)
  \<Longrightarrow> (l',r') \<in> R 
  \<Longrightarrow> rule_match R Q ecap (mv_xvar ` set ss) f (map mv_xvar ts) l'
  \<Longrightarrow> (l,r) \<in> U (args l') r'
  \<Longrightarrow> approx_cond (args l') r' (l,r)"
| approx_cond_sub: "approx_cond ss (Fun f ts) (l,r) 
    \<Longrightarrow> i < length ts 
    \<Longrightarrow> (l,r) \<in> U ss (ts ! i) 
    \<Longrightarrow> approx_cond ss (ts ! i) (l,r)"
| \<mu>_cond: "approx_cond ss (Fun f ts) (l,r) 
    \<Longrightarrow> i < length ts 
    \<Longrightarrow> (l,r) \<in> U ss (ts ! i) 
    \<Longrightarrow> \<mu>_cond (f,length ts) i"

definition "\<mu>_approx f \<equiv> Collect (\<mu>_cond f)"
end

context 
  assumes inn: "NF_terms Q \<subseteq> NF_trs R"
  and ecap: "is_ecap ecap"
  and wf: "wwf_qtrs Q R" 
begin

lemma hirokawa_moser_4_7_1_main:   
  assumes redex: "(redex,r') \<in> rqrstep nfs Q R"
  and lr: "((l,r),b) \<in> R \<times> {True} \<union> P \<times> {False}"
  and args: "get_args b l \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and nfs: "NF_subst True (l,r) \<sigma> Q"
  shows "r \<cdot> \<sigma> \<unrhd> C \<langle> redex \<rangle> \<Longrightarrow> af_regarded_pos (\<mu>_i_P P) (C \<langle> redex \<rangle>) (hole_pos C)"
proof (induct C)
  case (More f bef C aft)
  let ?\<mu>_i = "\<mu>_i_P P"
  from supteq_trans[OF More(2)] have "r \<cdot> \<sigma> \<unrhd> C\<langle>redex\<rangle>" by auto
  from More(1)[OF this] have IH: "af_regarded_pos ?\<mu>_i C\<langle>redex\<rangle> (hole_pos C)" .
  from More(2) obtain D where id: "r \<cdot> \<sigma> = D \<langle> (More f bef C aft) \<langle> redex \<rangle> \<rangle>" 
    by (metis supteq_ctxtE)
  let ?hp = "hole_pos D" 
  let ?i = "length bef"
  let ?n = "Suc (?i + length aft)"
  from redex have "(redex,r') \<in> rstep R" unfolding rqrstep_def by auto
  then have redex_NF: "redex \<notin> NF_trs R" by auto
  {
    fix x
    assume "\<sigma> x \<in> NF_terms Q"
    with inn have "\<sigma> x \<in> NF_trs R" by auto
    from NF_subterm[OF this, of redex] redex_NF have "\<not> \<sigma> x \<unrhd> redex" by auto
  } note vars = this
  let ?mv = "mv_xvar"
  from id have "?hp \<in> poss (r \<cdot> \<sigma>)" by auto
  from poss_subst_choice[OF this]
  have "?i \<in> ?\<mu>_i (f,?n)" 
  proof
    assume in_r: "?hp \<in> poss r \<and> is_Fun (r |_ ?hp)"
    then have [simp]: "r \<cdot> \<sigma> |_ ?hp = r |_ ?hp \<cdot> \<sigma>" by auto
    from arg_cong[OF id, of "\<lambda> t. t |_ ?hp"]
    have id: "r |_ ?hp \<cdot> \<sigma> = Fun f (bef @ C\<langle>redex\<rangle> # aft)" by simp
    with in_r obtain rs where rhp: "r |_ ?hp = Fun f rs" by (cases "r |_ ?hp", auto)
    define E where "E = ctxt_of_pos_term ?hp r"
    from in_r have "r = E \<langle> r |_ ?hp \<rangle>" unfolding E_def
      by (metis ctxt_supt_id)
    with rhp have r: "r = E \<langle> Fun f rs \<rangle>" by auto
    note lr = lr[unfolded r]
    show ?thesis unfolding \<mu>_i_P_def
    proof
      let ?m = "length rs"
      note id = id[unfolded rhp]
      from arg_cong[OF id, of num_args] 
      have sym: "((f,?n),?i) = ((f,?m),?i)" and im: "?i < ?m" by auto
      show "((f,?n),?i) \<in> innermost_repl_map P" unfolding innermost_repl_map_def
      proof (rule, intro exI conjI, rule sym, rule lr, rule im)
        define ri where "ri = rs ! ?i"
        from arg_cong[OF id, of "\<lambda> t. args t ! ?i"] sym
        have ri_red: "ri \<cdot> \<sigma> = C\<langle>redex\<rangle>" unfolding ri_def by auto
        from r have "r \<unrhd> Fun f rs" by auto
        moreover have "Fun f rs \<unrhd> ri" using sym ri_def by auto
        ultimately have "r \<unrhd> ri" by (rule supteq_trans)
        then have "vars_term ri \<subseteq> vars_term r" by (rule supteq_imp_vars_term_subset)
        with nfs[unfolded NF_subst_def vars_rule_def] 
        have "\<sigma> ` vars_term ri \<subseteq> NF_terms Q" by auto
        with ri_red
        show "Inl () \<in> vars_term (ecap R Q (?mv ` get_args b l) (?mv (rs ! ?i)))"
          unfolding ri_def[symmetric]
        proof (induct ri arbitrary: C)
          case (Var x C)
          then have "\<sigma> x \<unrhd> redex" and "\<sigma> x \<in> NF_terms Q" by auto
          with vars[of x] show ?case by auto
        next
          case (Fun f rs C)
          show ?case
          proof (cases C)
            case Hole
            have id: "get_args b l \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> = ?mv ` get_args b l \<cdot>\<^sub>s\<^sub>e\<^sub>t mv_subst \<sigma>"
              using mv_xvar[of _ \<sigma>] by auto
            from Hole Fun have "Fun f rs \<cdot> \<sigma> = redex" by simp            
            with redex have "(Fun f rs \<cdot> \<sigma>, r') \<in> (qrstep nfs Q R)\<^sup>* O rqrstep nfs Q R" by auto
            also have "Fun f rs \<cdot> \<sigma> = Fun f (map ?mv rs) \<cdot> mv_subst \<sigma>" 
              unfolding mv_xvar[of _ \<sigma>] by simp
            finally have "cap R Q (?mv ` get_args b l) ((Fun f (map ?mv rs))) = Var (Inl ())" 
              using args[unfolded id]
              by force
            from cap_Fun_fresh[OF ecap this]
            show ?thesis by auto
          next
            case (More g bef D aft)
            let ?i = "length bef"
            note id = Fun(2)[unfolded More]
            from arg_cong[OF id, of num_args] have len: "length rs = Suc (?i + length aft)" by simp
            with arg_cong[OF id, of "\<lambda> t. args t ! ?i"] have id: "rs ! ?i \<cdot> \<sigma> = D\<langle>redex\<rangle>" by auto
            from len have mem: "rs ! ?i \<in> set rs" by auto
            from Fun(1)[OF mem id] Fun(3) mem 
            have IH: "Inl () \<in> vars_term (ecap R Q (?mv ` get_args b l) (?mv (rs ! ?i)))" by auto
            with ecap_Fun[OF ecap, of R Q "?mv ` get_args b l" f "map ?mv rs"]
            show ?thesis using mem by auto
          qed
        qed
      qed
    qed
  next
    assume "\<exists> x q1 q2. q1 \<in> poss r \<and> q2 \<in> poss (\<sigma> x) \<and>
     r |_ q1 = Var x \<and> x \<in> vars_term r \<and> ?hp = q1 @ q2 \<and> r \<cdot> \<sigma> |_ ?hp = \<sigma> x |_ q2"
    then obtain x q2 where x: "x \<in> vars_term r" and idd: "r \<cdot> \<sigma> |_ ?hp = \<sigma> x |_ q2"
      and q2: "q2 \<in> poss (\<sigma> x)" by auto
    from idd[unfolded id] have "(More f bef C aft)\<langle>redex\<rangle> = \<sigma> x |_ q2" by simp
    with q2 have "\<sigma> x \<unrhd> redex" 
      by (metis ctxt_imp_supteq subt_at_imp_supteq subterm.le_imp_less_or_eq subterm.order.strict_trans2 supt_imp_supteq)
    with vars[of x] have "\<sigma> x \<notin> NF_terms Q" by auto
    with nfs x have False unfolding NF_subst_def vars_rule_def by auto
    then show ?thesis by auto
  qed
  then show ?case using IH by simp
qed simp

lemma hirokawa_moser_4_7_1_and_DPs: 
  assumes wfP: "wf_trs P" 
  and P: "P \<subseteq> P'"
  and s_af: "s \<in> af_nf_compatible_terms (\<mu>_i_P P') (qrstep nfs Q R)"
  and step: "(s,t) \<in> qrstep nfs Q R \<union> NF_terms Q \<times> UNIV \<inter> rrstep P"
  shows "t \<in> af_nf_compatible_terms (\<mu>_i_P P') (qrstep nfs Q R)"
proof -
  note d = af_nf_compatible_terms_def
  let ?NF = "NF (qrstep nfs Q R)"
  let ?\<mu>_i = "\<mu>_i_P P'"
  note wwf = wf wf_trs_imp_wwf_qtrs[OF wfP, of Q]
  show ?thesis unfolding d
  proof (rule, intro allI impI)
    fix D u
    assume tD: "t = D\<langle>u\<rangle>"
    let ?prop = "\<lambda> C \<sigma> l r b. s = C\<langle>l \<cdot> \<sigma>\<rangle> \<and> t = C\<langle>r \<cdot> \<sigma>\<rangle> \<and> get_args b l \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q 
      \<and> ((l,r),b) \<in> R \<times> {True} \<union> P \<times> {False} \<and> NF_subst True (l, r) \<sigma> Q
      \<and> ((l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R \<or> C = Hole)"
    from step have "\<exists> C \<sigma> l r b. ?prop C \<sigma> l r b"
    proof
      assume step: "(s,t) \<in> qrstep nfs Q R"      
      from qrstepE[OF step[unfolded wwf_qtrs_imp_nfs_switch[OF wwf(1), of nfs True]]]
      obtain C \<sigma> l r where 
        NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" and
        lr: "(l, r) \<in> R" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" 
        and nfs: "NF_subst True (l, r) \<sigma> Q" .
      from nfs have nfs_F: "NF_subst nfs (l,r) \<sigma> Q" unfolding NF_subst_def by auto
      from NF lr nfs_F have rstep: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R" by auto
      from NF[folded NF_terms_args_conv]
      have "set (args l) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q" by (cases l, auto)
      then have "?prop C \<sigma> l r True"
        by (intro conjI s t, insert lr nfs rstep, auto)
      then show ?thesis by metis
    next
      assume "(s,t) \<in> NF_terms Q \<times> UNIV \<inter> rrstep P"
      from this[unfolded rrstep_def']
      obtain \<sigma> l r where 
        NF: "l \<cdot> \<sigma> \<in> NF_terms Q" and
        lr: "(l, r) \<in> P" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" by auto
      have "NF_subst True (l,r) \<sigma> Q" using NF unfolding NF_subst_def
      proof (intro impI subsetI)
        fix t
        assume "t \<in> \<sigma> ` vars_rule (l,r)"
        with wf wfP lr have "t \<in> \<sigma> ` vars_term l" unfolding wf_trs_def vars_rule_def by force
        with supteq_subst[OF supteq_Var, of _ l \<sigma>]
        have "l \<cdot> \<sigma> \<unrhd> t" by auto
        with NF_subterm[OF NF] show "t \<in> NF_terms Q" by auto
      qed
      then have "?prop Hole \<sigma> l r False"
        by (insert s t lr NF, auto)
      then show ?thesis by metis
    qed
    then obtain C \<sigma> l r b where "?prop C \<sigma> l r b" by metis
    then have s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" 
      and *: "((l, r), b) \<in> R \<times> {True} \<union> P' \<times> {False}" "get_args b l \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
      and nfs: "NF_subst True (l, r) \<sigma> Q" and rstep: "C = Hole \<or> (l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R" 
      using P by auto
    note main = hirokawa_moser_4_7_1_main[OF _ * nfs]
    let ?l = "l \<cdot> \<sigma>" let ?r = "r \<cdot> \<sigma>"
    show "af_regarded_pos ?\<mu>_i t (hole_pos D) \<or> u \<in> ?NF"
    proof (cases "u \<in> ?NF")
      case False note u = this
      from s_af[unfolded d] have s_af: "\<And> D u. s = D\<langle>u\<rangle> \<Longrightarrow> af_regarded_pos ?\<mu>_i s (hole_pos D) \<or> u \<in> ?NF" by auto
      from s_af[OF s] rstep have reg1: "af_regarded_pos ?\<mu>_i s (hole_pos C)" by auto
      from s_af[of _ u] False have reg2: "\<And> D. s = D\<langle>u\<rangle> \<Longrightarrow> af_regarded_pos ?\<mu>_i s (hole_pos D)" by auto
      from reg1 reg2 have "af_regarded_pos ?\<mu>_i t (hole_pos D)" using tD unfolding t s
      proof (induct C arbitrary: D)
        case (More f bef C aft D) note C = this
        let ?i = "length bef"
        let ?n = "Suc (length bef + length aft)"
        from C(2) have i: "?i \<in> ?\<mu>_i (f,?n)" and reg: "af_regarded_pos ?\<mu>_i (C \<langle>?l\<rangle>) (hole_pos C)" by auto
        show ?case
        proof (cases D)
          case (More g bbef DD aaft) note D = this
          let ?i' = "length bbef"
          show ?thesis
          proof (cases "?i' = ?i")
            case True
            with C(4)[unfolded D] have id: "C\<langle>r \<cdot> \<sigma>\<rangle> = DD\<langle>u\<rangle>" by auto
            have "af_regarded_pos ?\<mu>_i C\<langle>r \<cdot> \<sigma>\<rangle> (hole_pos DD)"
            proof (rule C(1)[OF reg _ id])
              fix DD
              assume "C\<langle>l \<cdot> \<sigma>\<rangle> = DD\<langle>u\<rangle>"
              with C(3)[of "More f bef DD aft"] reg
              show "af_regarded_pos ?\<mu>_i C\<langle>l \<cdot> \<sigma>\<rangle> (hole_pos DD)" by auto
            qed
            then show ?thesis using True i unfolding D by simp
          next
            case False note neq = this
            from C(4)[unfolded D]
            have id: "bef @ C\<langle>r \<cdot> \<sigma>\<rangle> # aft = bbef @ DD\<langle>u\<rangle> # aaft" by simp
            from arg_cong[OF id, of length] have i': "?i' < ?n" by simp
            from arg_cong[OF id, of "\<lambda> ts. ts ! ?i'"]
            have idd: "DD\<langle>u\<rangle> = (bef @ C\<langle>?r\<rangle> # aft) ! ?i'" by simp
            show ?thesis
            proof (cases "?i < ?i'")
              case False
              with neq have i': "?i' < ?i" by auto
              then have bef: "bef ! ?i' = DD\<langle>u\<rangle>" unfolding idd by (auto simp: nth_append)
              from id_take_nth_drop[OF i', unfolded bef] i' obtain b1 b2 where
                bef: "bef = b1 @ DD\<langle>u\<rangle> # b2" and len: "length b1 = ?i'" by auto
              from C(3)[unfolded bef, of "More f b1 DD (b2 @ C\<langle>l \<cdot> \<sigma>\<rangle> # aft)"]
              have "length b1 \<in> ?\<mu>_i (f, Suc (Suc (length b1 + (length b2 + length aft))))"
                and "af_regarded_pos ?\<mu>_i DD\<langle>u\<rangle> (hole_pos DD)" by auto
              then show ?thesis unfolding bef D using len
                by (simp add: nth_append)
            next
              case True
              define i'' where "i'' = ?i' - Suc ?i"
              from True i''_def i' have i': "?i' = Suc ?i + i''" and i'': "i'' < length aft" by auto
              have aft: "aft ! i'' = DD\<langle>u\<rangle>" unfolding idd i' by (auto simp: nth_append)
              from id_take_nth_drop[OF i'', unfolded aft] i'' obtain a1 a2 where
                aft: "aft = a1 @ DD\<langle>u\<rangle> # a2" and len: "length a1 = i''" by auto
              from C(3)[unfolded aft, of "More f (bef @ C\<langle>l \<cdot> \<sigma>\<rangle> # a1) DD a2"]
              have " Suc (?i + length a1) \<in> ?\<mu>_i (f, Suc (Suc (?i + (length a1 + length a2))))"
              and "af_regarded_pos ?\<mu>_i ((bef @ C\<langle>l \<cdot> \<sigma>\<rangle> # a1 @ DD\<langle>u\<rangle> # a2) ! Suc (?i + length a1)) (hole_pos DD)" 
                by auto
              then show ?thesis unfolding aft D using len
                by (simp add: nth_append i')
            qed
          qed
        qed simp
      next
        case (Hole D)
        let ?hp = "hole_pos D"
        from Hole have idd: "r \<cdot> \<sigma> = D\<langle>u\<rangle>" by simp
        from False obtain v where "(u,v) \<in> qrstep nfs Q R" unfolding NF_def by auto
        {
          from qrstepE[OF this]
            obtain E \<sigma>' l' r' where 
            NF: "\<forall>u\<lhd>l' \<cdot> \<sigma>'. u \<in> NF_terms Q" and
            lr: "(l', r') \<in> R" and u: "u = E\<langle>l' \<cdot> \<sigma>'\<rangle>" and v: "v = E\<langle>r' \<cdot> \<sigma>'\<rangle>" 
            and nfs: "NF_subst nfs (l', r') \<sigma>' Q" .
          then have "(l' \<cdot> \<sigma>', r' \<cdot> \<sigma>') \<in> rqrstep nfs Q R" by auto
          with u have "\<exists> E red r'. u = E\<langle>red\<rangle> \<and> (red,r') \<in> rqrstep nfs Q R" by auto          
        }
        then obtain E red r' where u: "u = E\<langle>red\<rangle>" and red: "(red,r') \<in> rqrstep nfs Q R" by auto
        define rr where "rr = r \<cdot> \<sigma>"
        from main[OF red, of "D \<circ>\<^sub>c E"] idd[unfolded u]
        have "af_regarded_pos ?\<mu>_i (r \<cdot> \<sigma>) (hole_pos (D \<circ>\<^sub>c E))" by auto
        then show ?case unfolding intp_actxt.simps rr_def[symmetric]
          by (simp add: af_regarded_pos_append)
      qed
      then show ?thesis by simp
    qed simp
  qed
qed

lemma hirokawa_moser_4_7_1: 
  assumes s_af: "s \<in> af_nf_compatible_terms (\<mu>_i_P P) (qrstep nfs Q R)"
  and step: "(s,t) \<in> qrstep nfs Q R"
  shows "t \<in> af_nf_compatible_terms (\<mu>_i_P P) (qrstep nfs Q R)"
  by (rule hirokawa_moser_4_7_1_and_DPs[OF _ _ s_af, of "{}"], insert step, auto simp: wf_trs_def)

lemma hirokawa_moser_4_7_1_star: 
  assumes s_af: "s \<in> af_nf_compatible_terms (\<mu>_i_P P) (qrstep nfs Q R)"
  shows "(s,t) \<in> (qrstep nfs Q R)^* \<Longrightarrow> t \<in> af_nf_compatible_terms (\<mu>_i_P P) (qrstep nfs Q R)"
  by (induct rule: rtrancl_induct, rule s_af, rule hirokawa_moser_4_7_1)

lemma runtime_complexity_af_nf_compatible: 
  fixes T :: "('f,string)terms" and C D :: "('f \<times> nat)list"
  defines "T \<equiv> terms_of (Runtime_Complexity C D)"
  assumes C: "\<And> c. c \<in> set C \<Longrightarrow> \<not> defined R c"
  and s: "s \<in> T"
  shows "s \<in> af_nf_compatible_terms \<mu> (qrstep nfs Q R)"
proof -
  from s[unfolded T_def] obtain f cs where
  s: "s = Fun f cs" and f: "(f,length cs) \<in> set D" and 
  cs: "\<And> c. c \<in> set cs \<Longrightarrow> funas_term c \<subseteq> set C" by (force simp: funas_args_term_def)
  show ?thesis unfolding s af_nf_compatible_terms_def
  proof (rule, intro allI impI)
    fix D u
    assume id: "Fun f cs = D\<langle>u\<rangle>"
    show "af_regarded_pos \<mu> (Fun f cs) (hole_pos D) \<or> u \<in> NF (qrstep nfs Q R)"
    proof (cases D)
      case (More g bef E aft)
      with id have "E\<langle>u\<rangle> \<in> set cs" by auto
      from cs[OF this] have u: "funas_term u \<subseteq> set C" by auto
      {
        fix v
        assume "(u,v) \<in> qrstep nfs Q R"
        from qrstepE[OF this]
          obtain F l r \<sigma> where uu: "u = F\<langle>l\<cdot>\<sigma>\<rangle>" and lr: "(l,r) \<in> R" and NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" .
        from wwf_qtrs_imp_left_fun[OF wf lr] obtain f ls where l: "l = Fun f ls" by blast
        let ?n = "length ls"
        from u[unfolded uu l] have "(f,?n) \<in> set C" by auto
        from C[OF this] lr[unfolded l] have False unfolding defined_def by auto
      }
      then have "u \<in> NF (qrstep nfs Q R)" by auto
      then show ?thesis by auto
    qed simp
  qed
qed
  

theorem hirokawa_moser_4_8_1:
  fixes T :: "('f,string)terms" and C D :: "('f \<times> nat)list"
  defines "T \<equiv> terms_of (Runtime_Complexity C D)"
  assumes C: "\<And> c. c \<in> set C \<Longrightarrow> \<not> defined R c"
  shows "usable_replacement_map \<mu>_i T nfs R Q R"
proof (unfold usable_replacement_map_def, rule)
  fix t
  assume "t \<in> (qrstep nfs Q R)\<^sup>* `` T"
  then obtain s where steps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*" and s: "s \<in> T" by blast
  show "t \<in> af_nf_compatible_terms \<mu>_i (qrstep nfs Q R)" unfolding \<mu>_i_def
    by (rule hirokawa_moser_4_7_1_star[OF runtime_complexity_af_nf_compatible[OF C] steps],
    insert s T_def, auto)
qed

lemma NF_imp_af_nf_compatible: 
  assumes NF: "s \<in> NF_terms Q"
  shows "s \<in> af_nf_compatible_terms \<mu> (qrstep nfs Q R)"
  unfolding af_nf_compatible_terms_def
proof (rule, intro allI impI disjI2)
  fix C t
  assume "s = C\<langle>t\<rangle>"
  then have "s \<unrhd> t" by auto 
  from NF_subterm[OF NF this] inn have "t \<in> NF_trs R" by auto
  then show "t \<in> NF (qrstep nfs Q R)" by blast
qed
  

theorem urm_for_DP:
  assumes P: "(s,t) \<in> P"
  and NF: "s \<cdot> \<sigma> \<in> NF_terms Q" 
  and wfP: "wf_trs P"
  shows "usable_replacement_map (\<mu>_i_P P) {t \<cdot> \<sigma>} nfs R Q R"
proof (unfold usable_replacement_map_def, rule)
  fix u
  assume "u \<in> (qrstep nfs Q R)\<^sup>* `` {t \<cdot> \<sigma>}"
  then have steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*" by auto
  from P NF have P: "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NF_terms Q \<times> UNIV \<inter> rrstep P" unfolding rrstep_def' by auto
  show "u \<in> af_nf_compatible_terms (\<mu>_i_P P) (qrstep nfs Q R)"
    by (rule hirokawa_moser_4_7_1_star[OF hirokawa_moser_4_7_1_and_DPs[OF wfP subset_refl 
      NF_imp_af_nf_compatible[OF NF]] steps], insert P, auto)
qed

text \<open>The following approximation of usable replacement maps is a refinement
  of the one that is used within AProVE (as it is described in the JAR11 induction paper
  of Carsten, Juergen, et al.).
  The refinement integrated so far is using icap instead of just symbol comparisons\<close>

context
  fixes U :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)trs"
  and init :: "(('f,string)term list \<times> ('f,string)term \<times> ('f,string)rule)set"
  assumes U: "usable_rules_approx Q R True U"
begin
lemma approx_cond_main: 
  assumes \<sigma>: "\<sigma> ` vars_term t \<subseteq> NF_terms Q" "set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and steps: "(t \<cdot> \<sigma>, C\<langle>l \<cdot> \<delta>\<rangle>) \<in> (qrstep nfs Q R)^*"
  and step: "(C\<langle>l \<cdot> \<delta>\<rangle>, C\<langle>r \<cdot> \<delta>\<rangle>) \<in> qrstep_r_p_s nfs Q R (l,r) (hole_pos C) \<delta>"
  and cond: "approx_cond U init ss t (l,r)"
  shows "af_regarded_pos (\<mu>_approx U init) (C\<langle>l \<cdot> \<delta>\<rangle>) (hole_pos C)"
proof -
  let ?approx_cond = "approx_cond U init"
  let ?\<mu> = "\<mu>_approx U init"
  note switch = wwf_qtrs_imp_nfs_switch[OF wf, of nfs True]
  note step = step[unfolded wwf_qtrs_imp_nfs_switch_r_p_s[OF wf, of nfs True]]
  note U = usable_rules_approxD[OF U] 
  let ?R = "qrstep True Q R"
  let ?N = "nrqrstep True Q R"
  from rtrancl_imp_UN_relpow[OF steps[unfolded switch]] obtain n where 
    steps: "(t \<cdot> \<sigma>, C\<langle>l \<cdot> \<delta>\<rangle>) \<in> ?R^^n" by auto
  show ?thesis using \<sigma> steps step cond
  proof (induct n arbitrary: ss t \<sigma> l r C \<delta> rule: less_induct)
    case (less n ss t \<sigma> l r C \<delta>)
    from inn have inn2: "NF_terms Q \<subseteq> NF ?R" by force
    {
      fix t u n
      assume tu: "(t,u) \<in> ?R^^n" and t: "t \<in> NF ?R"
      have "n = 0"
      proof (cases n)
        case (Suc m)
        from tu[unfolded Suc] obtain v where tv: "(t,v) \<in> ?R" by blast
        with t show ?thesis by auto
      qed simp
    } note NF_steps_0 = this
    from less.prems
    show ?case 
    proof (induct t arbitrary: ss \<sigma> l r C \<delta>)
      case (Var x) (* variable case is trivial *)
      with inn2 have NF: "\<sigma> x \<in> NF ?R" by auto
      with Var(3) NF_steps_0[OF Var(3)] have C: "C \<langle> l \<cdot> \<delta> \<rangle> = \<sigma> x" by simp
      from Var(4)[unfolded C] have "(\<sigma> x, C \<langle> r \<cdot> \<delta> \<rangle>) \<in> ?R^^1" using qrstep_qrstep_r_p_s_conv[of _ _ True Q R]
        unfolding switch by auto
      from NF_steps_0[OF this NF] show ?case by simp
    next
      case (Fun f ts ss \<sigma> l r C \<delta>)
      let ?n = "length ts"
      show ?case
      proof (cases "(Fun f ts \<cdot> \<sigma>, C\<langle>l \<cdot> \<delta>\<rangle>) \<in> ?N^^n")
        case True (* only non-root steps *)
        show ?thesis
        proof (cases C) (* w.l.o.g. C \<noteq> Hole *)
          case (More g bef D aft)
          let ?i = "length bef"
          let ?m = "Suc (?i + length aft)"
          from nrqrsteps_preserve_root[OF relpow_imp_rtrancl[OF True], unfolded More]
          have gf: "g = f" and mn: "?m = ?n" by auto        
          then have i: "?i < ?n" by auto
          from nrqrsteps_imp_arg_qrsteps_count[OF True, of ?i] obtain m where m: "m \<le> n"
            and steps: "(ts ! ?i \<cdot> \<sigma>, D\<langle>l \<cdot> \<delta>\<rangle>) \<in> ?R^^m" using i unfolding More by auto
          from i have ti: "ts ! ?i \<in> set ts" by auto
          from ti Fun(2) have \<sigma>: "\<sigma> ` vars_term (ts ! ?i) \<subseteq> NF_terms Q" by auto
          from Fun(5) have step: "(D\<langle>l \<cdot> \<delta>\<rangle>, D\<langle>r \<cdot> \<delta>\<rangle>) \<in> qrstep_r_p_s True Q R (l, r) (hole_pos D) \<delta>"
            unfolding qrstep_r_p_s_def by auto
          have U: "(l, r) \<in> U ss (ts ! ?i)"
            by (rule U[OF \<sigma> Fun(3) relpow_imp_rtrancl[OF steps] step])
          from approx_cond_sub[OF Fun(6) i U] \<mu>_cond[OF Fun(6) i U] 
          have cond: "?approx_cond ss (ts ! ?i) (l,r)" and \<mu>: "?i \<in> ?\<mu> (f,?n)" unfolding \<mu>_approx_def by auto
          from steps m Fun(1)[OF ti \<sigma> Fun(3) _ step cond] less(1)[OF _ \<sigma> Fun(3) _ step cond] 
          have "af_regarded_pos ?\<mu> D\<langle>l \<cdot> \<delta>\<rangle> (hole_pos D)" by (cases "m < n", auto)
          with \<mu>
          show ?thesis unfolding More mn[symmetric] gf by simp
        qed simp
      next
        case False (* at least one root step *)
        note qr = qrstep_iff_rqrstep_or_nrqrstep
        from relpow_union_cases[OF Fun(4)[unfolded qr]] False
        obtain u v m k where tu: "(Fun f ts \<cdot> \<sigma>, u) \<in> ?N^^m"
          and uv: "(u,v) \<in> rqrstep True Q R" and vl: "(v,C\<langle>l \<cdot> \<delta>\<rangle>) \<in> ?R^^k" and n: "n = Suc (m + k)" 
          unfolding qr[symmetric] by blast
        note tu = relpow_imp_rtrancl[OF tu]
        from n have k: "k < n" by auto      
        from uv obtain l' r' \<sigma>' where u: "u = l' \<cdot> \<sigma>'" and v: "v = r' \<cdot> \<sigma>'" and lr': "(l',r') \<in> R" 
          and \<sigma>': "NF_subst True (l',r') \<sigma>' Q" 
          and NF1: "\<forall>u\<lhd>l' \<cdot> \<sigma>'. u \<in> NF_terms Q" by auto
        from only_applicable_rules[OF NF1] lr' wf
        have "vars_term r' \<subseteq> vars_term l'" and l': "is_Fun l'" unfolding wwf_qtrs_def by force+
        with \<sigma>' have \<sigma>': "\<sigma>' ` vars_term r' \<subseteq> NF_terms Q" unfolding NF_subst_def vars_rule_def by auto
        from NF1 have NF: "set (args l') \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma>' \<subseteq> NF_terms Q" unfolding NF_terms_args_conv[symmetric]
          using l' by (cases l', auto)
        have rm: "rule_match R Q ecap (mv_xvar ` set ss) f (map mv_xvar ts) l'"
          by (rule rule_matchI[OF ecap Fun(3) NF1 tu[unfolded u]]) 
        have "?approx_cond (args l') r' (l, r)"
          by (rule approx_cond_rec[OF Fun(6) lr' rm U[OF \<sigma>' NF relpow_imp_rtrancl[OF vl[unfolded v]] Fun(5)]])
        from less(1)[OF k \<sigma>' NF vl[unfolded v] Fun(5) this] 
        show ?thesis .
      qed
    qed
  qed
qed

context
  fixes S :: "('f,string)trs"
  assumes S: "S \<subseteq> R"
begin
lemma approx_cond: 
  assumes \<sigma>: "\<sigma> ` vars_term t \<subseteq> NF_terms Q" "set ss \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q"
  and steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)^*"
  and init: "{ss} \<times> {t} \<times> S \<subseteq> init"
  shows "u \<in> af_nf_compatible_terms (\<mu>_approx U init) (qrstep nfs Q S)"
  unfolding af_nf_compatible_terms_def
proof (rule, intro allI impI)
  fix C s
  let ?\<mu> = "\<mu>_approx U init"
  assume u: "u = C \<langle> s \<rangle>"
  show "af_regarded_pos ?\<mu> u (hole_pos C) \<or> s \<in> NF (qrstep nfs Q S)"
  proof (cases "s \<in> NF (qrstep nfs Q S)")
    case False
    then obtain v where sv: "(s,v) \<in> qrstep nfs Q S" by blast
    from this[unfolded qrstep_qrstep_r_p_s_conv] obtain lr p \<delta>
      where step: "(s,v) \<in> qrstep_r_p_s nfs Q S lr p \<delta>" by blast
    obtain l r where lr: "lr = (l,r)" by force
    from step[unfolded lr] S have lrS: "(l,r) \<in> S" and step: "(s,v) \<in> qrstep_r_p_s nfs Q R (l,r) p \<delta>"
      unfolding qrstep_r_p_s_def by auto
    from qrstep_r_p_s_conv[OF step[unfolded lr]] obtain D where s: "s = D \<langle> l \<cdot> \<delta> \<rangle>" and v: "v = D \<langle> r \<cdot> \<delta> \<rangle>" 
      and p: "p = hole_pos D" by auto
    let ?C = "C \<circ>\<^sub>c D"
    from step[unfolded s v p lr] have step: "(?C \<langle> l \<cdot> \<delta> \<rangle>, ?C \<langle> r \<cdot> \<delta> \<rangle>) \<in> qrstep_r_p_s nfs Q R (l,r) (hole_pos ?C) \<delta>"
      unfolding qrstep_r_p_s_def by (simp, induct C, auto)
    from u s have u: "u = ?C \<langle> l \<cdot> \<delta> \<rangle>" by simp
    from init lrS have "(ss,t,(l,r)) \<in> init" by auto
    from approx_cond_main[OF \<sigma> steps[unfolded u] step approx_cond_init[OF this]]
    have "af_regarded_pos ?\<mu> (?C\<langle>l \<cdot> \<delta>\<rangle>) (hole_pos ?C)" .
    then have "af_regarded_pos ?\<mu> (?C\<langle>l \<cdot> \<delta>\<rangle>) (hole_pos C)"
      by (induct C, auto)
    then show ?thesis unfolding u ..
  qed simp
qed

theorem aprove_urm_complexity:
  fixes T :: "('f,string)terms" and C D :: "('f \<times> nat)list" and name :: string
  defines "T \<equiv> terms_of (Runtime_Complexity C D)"
    and "gen_xs \<equiv> \<lambda> n. (map Var (x\<^sub>1_to_x\<^sub>n n)) :: ('f,string)term list"
  assumes C: "\<And> c. c \<in> set C \<Longrightarrow> \<not> defined R c"
  and approx: "\<And> f n. (f,n) \<in> set D 
    \<Longrightarrow> {gen_xs n} \<times> {(Fun f (gen_xs n))} \<times> S \<subseteq> init"
  shows "usable_replacement_map (\<mu>_approx U init) T nfs R Q S"
proof (unfold usable_replacement_map_def, rule)
  let ?\<mu> = "\<mu>_approx U init"
  fix t
  assume "t \<in> (qrstep nfs Q R)\<^sup>* `` T"
  then obtain s where steps: "(s,t) \<in> (qrstep nfs Q R)\<^sup>*" and s: "s \<in> T" by blast
  from s[unfolded T_def, simplified] obtain f ss where s: "s = Fun f ss" 
    and funas: "\<And> si. si \<in> set ss \<Longrightarrow> funas_term si \<subseteq> set C" and D: "(f,length ss) \<in> set D" 
    by (cases s, auto simp: funas_args_term_def)
  let ?n = "length ss"
  define xs where "xs = x\<^sub>1_to_x\<^sub>n ?n"
  have xs: "length xs = ?n" unfolding xs_def by simp
  define \<sigma> where "\<sigma> = inv_x\<^sub>1_to_x\<^sub>n ss"
  from inv_x\<^sub>1_to_x\<^sub>n[of ss, folded \<sigma>_def xs_def] 
  have ss: "ss = map \<sigma> xs" by simp
  then have s: "s = Fun f (map Var xs) \<cdot> \<sigma>" unfolding s by (simp add: o_def)
  show "t \<in> af_nf_compatible_terms ?\<mu> (qrstep nfs Q S)" 
  proof (cases "set ss \<subseteq> NF_terms Q")
    case True
    show ?thesis
    proof (rule approx_cond[OF _ _ steps[unfolded s] approx[OF D, unfolded gen_xs_def, folded xs_def]], rule)
      from True show "set (map Var xs) \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q" using ss by auto
      fix u
      assume "u \<in> \<sigma> ` vars_term (Fun f (map Var xs))"
      then obtain i where u: "u = \<sigma> (xs ! i)" and i: "i < length xs" 
        by (auto simp: set_conv_nth)
      have u: "u = ss ! i" unfolding ss u using i xs by auto
      with i xs have "u \<in> set ss" by auto
      with True
      show "u \<in> NF_terms Q" by auto
    qed
  next
    case False
    from \<open>s \<in> T\<close> T_def have s: "s \<in> terms_of (Runtime_Complexity C D)" by auto
    from runtime_complexity_af_nf_compatible[OF C this]
    have s: "\<And> \<mu>. s \<in> af_nf_compatible_terms \<mu> (qrstep nfs Q R)" by simp
    have "s = t" 
    proof (cases rule: converse_rtranclE[OF steps])
      fix u
      assume "(s,u) \<in> qrstep nfs Q R"
      then obtain C l r \<sigma> where "(l,r) \<in> R" and NF: "\<And> u. u\<lhd>l \<cdot> \<sigma> \<Longrightarrow> u \<in> NF_terms Q" and su: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "u = C\<langle>r \<cdot> \<sigma>\<rangle>" and step: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> qrstep nfs Q R"
        by blast
      have False
      proof (cases C)
        case (More f bef D aft)
        from s[of "\<lambda> _. {}", unfolded af_nf_compatible_terms_def, simplified, rule_format, OF su(1)[unfolded More]] step
        show False by auto
      next
        case Hole
        with su(1) \<open>s = Fun f ss\<close> have l: "l \<cdot> \<sigma> = Fun f ss" by auto 
        from False obtain si where si: "si \<in> set ss" and "si \<notin> NF_terms Q" by auto
        with NF[unfolded l, of si]
        show False by auto
      qed
      then show "s = t" by simp
    qed
    with s have t: "t \<in> af_nf_compatible_terms ?\<mu> (qrstep nfs Q R)" by auto
    show ?thesis 
      by (rule set_mp[OF af_nf_compatible_terms_mono[OF qrstep_mono[OF S]] t]) auto
  qed
qed

theorem aprove_urm_for_DP:
  assumes P: "(s,t) \<in> P"
  and NF: "s \<cdot> \<sigma> \<in> NF_terms Q" 
  and approx: "{[s]} \<times> {t} \<times> S \<subseteq> init"
  and wfP: "wf_trs P"
  shows "usable_replacement_map (\<mu>_approx U init) {t \<cdot> \<sigma>} nfs R Q S"
  unfolding usable_replacement_map_def
proof
  let ?\<mu> = "\<mu>_approx U init"
  fix u
  assume "u \<in> (qrstep nfs Q R)\<^sup>* `` {t \<cdot> \<sigma>}"
  then have steps: "(t \<cdot> \<sigma>, u) \<in> (qrstep nfs Q R)\<^sup>*" by simp
  show "u \<in> af_nf_compatible_terms ?\<mu> (qrstep nfs Q S)"
  proof (rule approx_cond[OF _ _ steps approx], rule)
    show "set [s] \<cdot>\<^sub>s\<^sub>e\<^sub>t \<sigma> \<subseteq> NF_terms Q" using NF by simp
    fix v
    assume "v \<in> \<sigma> ` vars_term t"
    then obtain x where v: "v = \<sigma> x" and x: "x \<in> vars_term t" by auto
    with wfP P have x: "x \<in> vars_term s" unfolding wf_trs_def by auto
    then have "s \<unrhd> Var x" by auto
    from NF_subterm[OF NF supteq_subst[OF this, of \<sigma>]]
    show "v \<in> NF_terms Q" unfolding v by simp
  qed
qed
end
end
end
end

lemma avanzini_14_34: assumes us: "usable_replacement_map \<mu> (terms_of cm) nfs (RS \<union> R) Q RS'"
  and DP: "is_DP_complexity Cp FS F RS R cm"
  and RS': "RS' \<subseteq> RS"
  and \<mu>_com: "\<And> f. f \<in> Cp \<Longrightarrow> \<mu>_com f \<supseteq> \<mu> f"
  shows "usable_replacement_map \<mu>_com (terms_of cm) nfs (RS \<union> R) Q RS'"
  unfolding usable_replacement_map_def
proof
  fix t
  assume tt: "t \<in> (qrstep nfs Q (RS \<union> R))\<^sup>* `` terms_of cm"
  with avanzini_14_20(2)[OF DP] have t: "t \<in> Tsharp_terms Cp FS F" by auto
  from tt us[unfolded usable_replacement_map_def] 
  have tt: "t \<in> af_nf_compatible_terms \<mu> (qrstep nfs Q RS')" by auto
  note d = af_nf_compatible_terms_def
  show "t \<in> af_nf_compatible_terms \<mu>_com (qrstep nfs Q RS')" unfolding d
  proof (rule, intro allI impI)
    fix C s
    assume ts: "t = C\<langle>s\<rangle>"
    with tt[unfolded d] have af: "af_regarded_pos \<mu> t (hole_pos C) \<or> s \<in> NF (qrstep nfs Q RS')" by auto
    show "af_regarded_pos \<mu>_com t (hole_pos C) \<or> s \<in> NF (qrstep nfs Q RS')"
    proof (cases "s \<in> NF (qrstep nfs Q RS')")
      case False      
      with af have af: "af_regarded_pos \<mu> t (hole_pos C)" by auto
      from False obtain u where "(s,u) \<in> qrstep nfs Q RS'" unfolding NF_def by auto
      {
        from qrstepE[OF this] obtain l r C \<sigma> where lr: "(l,r) \<in> RS'" and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" .
        from lr RS' have lr: "(l,r) \<in> RS" by auto
        from DP have "wf_trs RS" and RS: "lhss RS \<subseteq> Fsharp_terms FS F" by (cases, auto)+
        from wf_trs_imp_lhs_Fun[OF this(1) lr] obtain f ls where l: "l = Fun f ls" by auto
        from RS lr have "l \<in> Fsharp_terms FS F" by auto
        from this[unfolded l] have "(f,length ls) \<in> FS" by (cases, auto)
        with s l have "funas_term s \<inter> FS \<noteq> {}" by simp
      } note s_FS = this
      from DP have FS_F: "FS \<inter> F = {}" by (cases, auto)
      with s_FS have sF: "\<not> funas_term s \<subseteq> F" by auto
      from t ts af have "af_regarded_pos \<mu>_com t (hole_pos C)"
      proof (induct t arbitrary: C)
        case (compound f ts C)
        show ?case
        proof (cases C)
          case (More g bef D aft) note C = this
          let ?i = "length bef"
          let ?n = "length ts"
          from compound(1) have "(f,?n) \<in> Cp" by simp
          note \<mu>_com = \<mu>_com[OF this]
          from compound(5)[unfolded C]
          have i[simp]: "?i < ?n"
            and mu: "?i \<in> \<mu> (f, ?n)"
            and af: "af_regarded_pos \<mu> (ts ! ?i) (hole_pos D)" by auto
          from mu \<mu>_com have [simp]: "?i \<in> \<mu>_com (f,?n)" by auto
          have [simp]: "af_regarded_pos \<mu>_com (ts ! ?i) (hole_pos D)"
            by (rule compound(3)[OF _ _ af], insert i compound(4) C, auto)
          show ?thesis unfolding C by simp
        qed simp
      next
        case (base t C)
        with sF have False by auto
        then show ?case by simp
      next
        case (sharp t C)
        show ?case
        proof (cases C)
          case (More g bef D aft)
          from sharp(1)[unfolded sharp(2) More]
          have "funas_term s \<subseteq> F" by (cases, force)
          with sF have False by simp
          then show ?thesis by simp
        qed simp
      qed
      then show ?thesis ..
    qed simp
  qed
qed

end
