(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Usable_Replacement_Map_Impl
  imports 
    Icap_Impl
    Ord.Term_Order_Impl
    Framework.QDP_Framework_Impl
    Auxx.Map_Choice
    Auxx.Inductive_Set_Impl
    Usable_Replacement_Map
    Complexity_Framework_Impl
    Innermost_Usable_Rules_Impl
begin

definition "full_empty fs = (let fs' = filter (\<lambda> (f,n). n \<noteq> 0) fs in (fs', \<lambda> f. if f \<in> set fs' then full_af f else {}, STR ''full AF''))"

fun get_args_impl where
  "get_args_impl True t = args t"
| "get_args_impl False t = [t]"

lemma get_args_impl[simp]: "set (get_args_impl b t) = get_args b t"
  by (cases b, auto)

locale usable_replacement_map =
  fixes R :: "('f :: {showl, compare_order},string)rules"
  and Q :: "('f,string)term list"
  and ecap :: "('f,string)term list \<Rightarrow> ('f, string) term \<Rightarrow> ('f, unit + string) term"
begin

definition innermost_repl_map_impl where 
  "innermost_repl_map_impl P \<equiv> remdups [(f,i) . ((l,r),b) <- [(lr,True) . lr <- R] @ [(st,False) . st <- P], u <- supteq_list r, is_Fun u, rs <- [args u], f <- [the (root u)],
  n <- [snd f], i <- [0..< n], Inl () \<in> vars_term (ecap (get_args_impl b l) (rs ! i)) ]"

definition \<mu>_i_P_impl :: "('f,string)rules \<Rightarrow> (('f \<times> nat)list \<times> 'f af \<times> String.literal)" where 
  "\<mu>_i_P_impl P \<equiv> let fis = innermost_repl_map_impl P;
    fs = remdups (map fst fis);
    \<mu> = (\<lambda> f. set (map snd (filter (\<lambda> (g,i). g = f) fis)))
    in (fs,precompute_fun \<mu> fs, STR ''innermost URM'')"

definition \<mu>_i_impl :: "(('f \<times> nat)list \<times> 'f af \<times> String.literal)" where 
  "\<mu>_i_impl = \<mu>_i_P_impl []"

definition "default_fs \<equiv> funas_trs_list R"

lemma full_empty: assumes fe: "full_empty fs = (fs',\<mu>,info)"
  and defa: "set default_fs \<subseteq> set fs"
  and sig: "set (get_signature_of_cm cm) \<subseteq> set fs"
  and wf: "wf_trs (set R)"
  shows "\<And> f. f \<notin> set fs' \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set R)"
proof -
  let ?fs = "filter (\<lambda> (f,n). n \<noteq> 0) fs"
  from fe[unfolded full_empty_def, simplified]
  have \<mu>: "\<mu> = (\<lambda>f. if f \<in> set ?fs then full_af f else {})" and fs: "fs' = ?fs" by auto
  show "\<And> f. f \<notin> set fs' \<Longrightarrow> \<mu> f = {}" unfolding fs \<mu> by auto
  let ?T = "terms_of cm"
  let ?R = "qrstep nfs (set Q) (set R)"
  from defa[unfolded default_fs_def] have R: "funas_trs (set R) \<subseteq> set fs" by auto
  show "usable_replacement_map \<mu> ?T nfs (set R) (set Q) (set R)"
    unfolding usable_replacement_map_def
  proof
    fix t
    assume "t \<in> ?R^* `` ?T"
    then obtain u where steps: "(u,t) \<in> ?R^*" and u: "u \<in> ?T" by auto
    then obtain n where "u \<in> terms_of_nat cm n" by (auto simp: terms_of)
    from set_mp[OF get_signature_of_cm this] 
    have "funas_term u \<subseteq> set (get_signature_of_cm cm)" by auto
    with sig have "funas_term u \<subseteq> set fs" by auto
    from rsteps_preserve_funas_terms[OF R this set_mp[OF rtrancl_mono steps] wf]
    have t: "funas_term t \<subseteq> set fs" by auto
    {
      fix C s
      assume id: "t = C\<langle>s\<rangle>"
      with t have "funas_ctxt C \<subseteq> set fs" by auto
      then have "af_regarded_pos \<mu> t (hole_pos C)" unfolding id
      proof (induct C)
        case (More f bef C aft)
        let ?i = "length bef"
        let ?n = "Suc (?i + length aft)"
        from More
        have IH: "af_regarded_pos \<mu> C\<langle>s\<rangle> (hole_pos C)" and 
          f: "(f,?n) \<in> set fs" by auto
        from f have "?i \<in> \<mu> (f,?n)" unfolding \<mu> full_af_def by auto
        with IH show ?case by auto
      qed simp
    }
    then show  "t \<in> af_nf_compatible_terms \<mu> ?R" unfolding af_nf_compatible_terms_def by auto
  qed
qed

fun get_fs_\<mu> :: "bool \<Rightarrow> ('f,string)complexity_measure \<Rightarrow> (('f \<times> nat)list \<times> 'f af \<times> String.literal)" where
  "get_fs_\<mu> inn (Derivational_Complexity F) = (full_empty (remdups (F @ default_fs)))"
| "get_fs_\<mu> inn (Runtime_Complexity C D) = 
    (if inn \<and> set C \<inter> set (defined_list R) \<subseteq> {} then \<mu>_i_impl 
      else full_empty (remdups (C @ D @ default_fs))
    )"

definition get_fs_\<mu>_DP :: "bool \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)complexity_measure \<Rightarrow> (('f \<times> nat)list \<times> 'f af \<times> String.literal)" where
  "get_fs_\<mu>_DP inn S cm = (
   let (fs,\<mu>,info) = get_fs_\<mu> inn cm   
   in (case check_DP_complexity R cm of 
     Inr (RS, R', Cp, FS, F) \<Rightarrow> if set S \<subseteq> set RS then (list_inter fs Cp, \<lambda> f. if f \<in> set Cp then \<mu> f else {}, info + STR '' with DPs'') else (fs,\<mu>,info)
     | _ \<Rightarrow> (fs,\<mu>,info)))"

context
  assumes ecap: "ecap = icap_impl' (\<lambda> t. t \<in> NF_terms (set Q)) R"
begin

lemma innermost_repl_map_impl[simp]: "set (innermost_repl_map_impl P) = innermost_repl_map icap' (set R) (set Q) (set P)"
  (is "?l = ?r")
proof -
  note d = innermost_repl_map_impl_def
  define RR where "RR = set R \<times> {True} \<union> set P \<times> {False}"
  define RR' where "RR' = (map (\<lambda>lr. (lr, True)) R @ map (\<lambda>st. (st, False)) P)"  
  have [simp]: "set RR' = RR" unfolding RR_def RR'_def by auto
  have "?r = { ((f,length rs),i) | l C f rs i b. ((l,C\<langle>Fun f rs\<rangle>),b) \<in> RR \<and>
    i < length rs \<and> Inl () \<in> vars_term (ecap (get_args_impl b l) (rs ! i))}" (is "_ = ?m")    
    unfolding innermost_repl_map_def RR_def
    unfolding icap' icap_mv_def[symmetric] icap_impl'_sound[symmetric] 
      ecap[symmetric] get_args_impl[symmetric]
    by (rule refl)
  also have "?m = ?l" 
  proof -
    {
      fix f n i
      assume "((f,n),i) \<in> ?m"
      then obtain l C rs b where lr: "((l,C\<langle>Fun f rs\<rangle>),b) \<in> RR"
       and *: "i < length rs \<and> Inl () \<in> vars_term (ecap (get_args_impl b l) (rs ! i))" 
       and n: "n = length rs" by auto
      have "((f,n),i) \<in> ?l" unfolding d n RR'_def[symmetric]
        by (clarsimp, rule bexI[OF _ lr], rule exI, rule exI, rule exI, rule conjI[OF refl],
          rule bexI[of _ "Fun f rs"], insert *, auto)
    }
    then have one: "?m \<subseteq> ?l" by force
    {
      fix fn i
      assume "(fn,i) \<in> ?l"
      from this[unfolded d, folded RR'_def]
      obtain l r u b where 
        lr: "((l,r),b) \<in> RR"
        and supt: "r \<unrhd> u" and u: "is_Fun u"
        and f: "fn = the (root u)"
        and i: "i < snd (the (root u))"
        and cap: "Inl () \<in> vars_term (ecap (get_args_impl b l) (args u ! i))" by auto
      from supt obtain C where r: "r = C \<langle> u \<rangle>" by auto
      from u obtain f rs where u: "u = Fun f rs" by auto
      have "(fn,i) \<in> ?m" using lr i cap unfolding u r f by auto
    } 
    then have "?l \<subseteq> ?m" by auto
    with one show ?thesis by blast
  qed
  finally show ?thesis by simp
qed

lemma \<mu>_i_P_impl: assumes impl: "\<mu>_i_P_impl P = (fs,\<mu>,info)"
  shows "\<mu> = \<mu>_i_P icap' (set R) (set Q) (set P) \<and> (\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {})"
proof -
  note d = \<mu>_i_P_impl_def Let_def
  show ?thesis
  proof (intro conjI allI impI)
    fix f
    assume "f \<notin> set fs"
    then show "\<mu> f = {}"
    using impl by (auto simp: d)
  next
    show "\<mu> = \<mu>_i_P icap' (set R) (set Q) (set P)" using impl unfolding d
      by (intro ext, auto simp: \<mu>_i_P_def)
  qed
qed  

lemma \<mu>_i_impl: assumes impl: "\<mu>_i_impl = (fs,\<mu>,info)"
  shows "\<mu> = \<mu>_i icap' (set R) (set Q) \<and> (\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {})"
  unfolding \<mu>_i_def using \<mu>_i_P_impl[OF impl[unfolded \<mu>_i_impl_def]] by auto  

lemma get_fs_\<mu>: assumes split: "get_fs_\<mu> inn cm = (fs,\<mu>,info)"
  and wf: "wf_trs (set R)"
  and inn: "inn = (NF_terms (set Q) \<subseteq> NF_trs (set R))"
  shows "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set R)"
proof -
  have "(\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {}) \<and> usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set R)"
  proof (cases cm)
    case (Derivational_Complexity F) note cm = this
    from split[unfolded cm] 
    have "full_empty (remdups (F @ default_fs)) = (fs, \<mu>, info)" by simp
    from full_empty[OF this _ _ wf, of cm]
    show ?thesis unfolding cm by auto
  next
    case (Runtime_Complexity C D) note cm = this
    let ?cond = "inn \<and> set C \<inter> {fn. defined (set R) fn} = {}"
    show ?thesis
    proof (cases ?cond)
      case False
      with split[unfolded cm]
      obtain info where "full_empty (remdups (C @ D @ default_fs)) = (fs, \<mu>, info)" by auto
      from full_empty[OF this _ _ wf, of cm]
      show ?thesis unfolding cm by auto
    next
      case True
      with split[unfolded cm]
      have "\<mu>_i_impl = (fs,\<mu>,info)" by auto
      from \<mu>_i_impl[OF this] have \<mu>: "\<mu> = \<mu>_i icap' (set R) (set Q)" and 
        fs: "(\<forall>f. f \<notin> set fs \<longrightarrow> \<mu> f = {})" by auto
      show ?thesis
        by (rule conjI[OF fs], unfold \<mu> cm, rule hirokawa_moser_4_8_1[OF _ icap],
        insert True[unfolded inn] wf_trs_imp_wwf_qtrs[OF wf], auto)
    qed
  qed
  then show "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set R)"
    by blast+
qed

lemma get_fs_\<mu>_DP: assumes get: "get_fs_\<mu>_DP inn S cm = (fs,\<mu>,info)"
  and wf: "wf_trs (set R)"
  and S: "set S \<subseteq> set R"
  and inn: "inn = (NF_terms (set Q) \<subseteq> NF_trs (set R))"
  shows "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set S)"
proof -
  note d = get_fs_\<mu>_DP_def
  obtain fs' \<mu>' info where get': "get_fs_\<mu> inn cm = (fs',\<mu>',info)" by (cases "get_fs_\<mu> inn cm")
  from get_fs_\<mu>[OF this wf inn] have f: "\<And> f. f \<notin> set fs' \<Longrightarrow> \<mu>' f = {}" 
    and urm: "usable_replacement_map \<mu>' (terms_of cm) nfs (set R) (set Q) (set R)" by auto
  from usable_replacement_map_mono[OF _ _ S urm]
  have urm: "usable_replacement_map \<mu>' (terms_of cm) nfs (set R) (set Q) (set S)" by auto
  have "(\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {}) \<and> usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set S)"
  proof (cases "(fs,\<mu>,info) = (fs',\<mu>',info)")
    case True
    with f urm show ?thesis by auto
  next
    case False
    note get = get[unfolded d get' Let_def split]
    from get False obtain res where check: "check_DP_complexity R cm = Inr res" by (cases "check_DP_complexity R cm", auto)
    obtain RS R' Cp FS F where res: "res = (RS, R', Cp, FS, F)" by (cases res, auto)
    from get[unfolded check res, simplified] False have S: "set S \<subseteq> set RS"
    and fs: "fs = list_inter fs' Cp" and \<mu>: "\<mu> = (\<lambda>f. if f \<in> set Cp then \<mu>' f else {})" 
      by (auto split: if_splits)
    from check_DP_complexity[OF check[unfolded res] wf]
    have R: "set R = set RS \<union> set R'" and dp: "is_DP_complexity (set Cp) (set FS) (set F) (set RS) (set R') cm"
      by auto
    have urm: "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set S)"
      by (rule avanzini_14_34[OF urm[unfolded R] dp S, folded R], auto simp: \<mu>)
    show ?thesis
      by (rule conjI[OF _ urm], auto simp: fs \<mu> f)
  qed
  then show "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" and "usable_replacement_map \<mu> (terms_of cm) nfs (set R) (set Q) (set S)" 
    by auto
qed

end
end

declare usable_replacement_map.get_fs_\<mu>.simps[code]
declare usable_replacement_map.get_fs_\<mu>_DP_def[code]
declare usable_replacement_map.\<mu>_i_impl_def[code]
declare usable_replacement_map.\<mu>_i_P_impl_def[code]
declare usable_replacement_map.default_fs_def[code]
declare usable_replacement_map.innermost_repl_map_impl_def[code]


section \<open>Computation of AProVE's urms\<close>

locale urm_computation = 
  fixes ecap :: "('f :: compare_order,string)cap_fun"
  and R :: "('f,string)trs"
  and Q :: "('f,string)terms"
  and U :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)trs"
  and init :: "(('f,string)term list \<times> ('f,string)term \<times> ('f,string)rule)set"
begin
abbreviation "approx_cond' \<equiv> approx_cond ecap R Q U init"
abbreviation "\<mu>_cond' \<equiv> \<mu>_cond ecap R Q U init"
abbreviation "\<mu>_approx' \<equiv> \<mu>_approx ecap R Q U init"
abbreviation "rule_match' \<equiv> rule_match R Q ecap"
lemmas approx_cond_rec = approx_cond_rec[of ecap R Q U init]
lemmas approx_cond_sub = approx_cond_sub[of ecap R Q U init]
lemmas approx_cond_init = approx_cond_init[of _ _ _ init ecap R Q U]
lemmas \<mu>_cond = \<mu>_cond[of ecap R Q U init]

definition "all_terms = {(ss,t) | ss t lr. (ss,t,lr) \<in> init} \<union> {(args l, r) | l r. (l,r) \<in> R}"
definition "all_subterms = {(ss,t) | ss s t. (ss,s) \<in> all_terms \<and> s \<unrhd> t}"
definition "everything \<equiv> Inl ` {(ss,t,lr) | ss t lr. (ss,t) \<in> all_subterms \<and> (\<exists> ss t. (ss,t,lr) \<in> init)}
  \<union> Inr ` { ((f,length ts),i) | f ts i . i < length ts \<and> Fun f ts \<in> snd ` all_subterms}"

abbreviation "gen_a ss f ts l r \<equiv> Inl ` {(ss, ts ! i, (l,r)) | i. i < length ts \<and> (l,r) \<in> U ss (ts ! i)}"
abbreviation "gen_b ss f ts l r \<equiv> Inl ` {(args l', r', (l,r)) | l' r'. (l',r') \<in> R \<and> rule_match' (mv_xvar ` (set ss)) f (map mv_xvar ts) l' \<and> (l,r) \<in> U (args l') r'}"
abbreviation "gen_c ss f ts l r \<equiv> Inr ` {((f,length ts),i) | i. i < length ts \<and> (l,r) \<in> U ss (ts ! i)}"

fun generate where 
  "generate (Inl (ss, Fun f ts,(l,r))) = gen_a ss f ts l r \<union> gen_b ss f ts l r \<union> gen_c ss f ts l r"
| "generate _ = {}"

interpretation gen_set: generic_inductive_set everything "(=)" generate .

definition "check_approx = gen_set.the_set"

lemma check_approx_sound: assumes "check_approx t_lr s"
  and "t_lr \<in> Inl ` init"
  shows "(\<forall> ss' t' lr'. s = Inl (ss', t',lr') \<longrightarrow> approx_cond' ss' t' lr') \<and>
  (\<forall> f i. s = Inr (f,i) \<longrightarrow> \<mu>_cond' f i)"
proof -
  from assms(2) have "t_lr \<in> Inl ` {(ss,t,lr). approx_cond' ss t lr} \<union> Inr ` {(f,i). \<mu>_cond' f i}" (is "_ \<in> ?sound")
    by (cases t_lr, auto intro: approx_cond_init)
  from assms(1) this show ?thesis unfolding check_approx_def 
  proof (induct t_lr s rule: gen_set.the_set_induct)
    case (rec t1_lr1 copy t2_lr2 t3_lr3)
    note IH = rec(5)[unfolded rec(2)]
    note prems = rec(3,6)[unfolded rec(2)]
    show ?case 
    proof (rule IH)
      from prems(1) obtain t_lr1 where "t1_lr1 = Inl t_lr1" by (cases t1_lr1, auto)
      then obtain ss1 t1 l1 r1 where "t1_lr1 = Inl (ss1,t1,(l1,r1))" by (cases t_lr1, auto)
      note prems = prems[unfolded this]
      from prems(1) obtain f ts where t1: "t1 = Fun f ts" by (cases t1, auto)
      with prems(2) have cond: "approx_cond' ss1 (Fun f ts) (l1,r1)" by auto
      note prems = prems(1)[unfolded t1]
      show "t2_lr2 \<in> ?sound"
      proof (cases t2_lr2)
        case (Inr g_i)
        with prems obtain i where g_i: "g_i = ((f,length ts),i)"
          and i: "i < length ts" and U: "(l1, r1) \<in> U ss1 (ts ! i)" by auto
        have "\<mu>_cond' (f,length ts) i"
          by (rule \<mu>_cond[OF cond i U])
        with Inr g_i show ?thesis by auto
      next
        case (Inl t_lr2)
        with prems obtain ss2 t2 where 2: "t2_lr2 = Inl (ss2,t2,(l1,r1))" by (cases t_lr2, auto)
        have "approx_cond' ss2 t2 (l1,r1)"
        proof (cases "ss2 = ss1 \<and> (\<exists> i. t2 = ts ! i \<and> i < length ts \<and> (l1, r1) \<in> U ss1 (ts ! i))")
          case True
          then obtain i where ss2: "ss2 = ss1" and t2: "t2 = ts ! i" and i: "i < length ts" and U: "(l1,r1) \<in> U ss1 (ts ! i)" by auto
          show "approx_cond' ss2 t2 (l1,r1)" unfolding t2 ss2
            by (rule approx_cond_sub[OF cond i U])
        next
          case False
          with prems[unfolded 2]
          obtain l' r'
            where ss2: "ss2 = args l'" and t2: "t2 = r'" and lr: "(l', r') \<in> R" 
            and match: "rule_match' (mv_xvar ` (set ss1)) f (map mv_xvar ts) l'" and U: "(l1, r1) \<in> U (args l') r'" 
            by auto
          show "approx_cond' ss2 t2 (l1,r1)" unfolding t2 ss2
            by (rule approx_cond_rec[OF cond lr match U])
        qed
        then show ?thesis unfolding 2 by simp
      qed
    qed
  qed auto
qed

lemmas every_defs = everything_def all_subterms_def all_terms_def

lemma the_set_refl: "a \<in> everything \<Longrightarrow> gen_set.the_set a a"
  by (rule gen_set.non_rec, auto)

lemma check_approx_complete: 
  "approx_cond' ss t lr \<Longrightarrow> Inl (ss,t,lr) \<in> everything \<and> (\<exists> t_lr \<in> Inl ` init. check_approx t_lr (Inl (ss,t,lr)))"
  "\<mu>_cond' f i \<Longrightarrow> \<exists> t_lr \<in> Inl ` init. check_approx t_lr (Inr (f,i))"
  unfolding check_approx_def
proof (induct ss t lr and f i rule: approx_cond_\<mu>_cond.inducts)
  case (approx_cond_init ss t lr)
  note IH = this
  from IH have 1: "(ss,t) \<in> all_subterms" unfolding every_defs by blast
  from IH have 2: "\<exists> ss t. (ss,t,lr) \<in> init" unfolding o_def by force
  from 1 2 have every: "Inl (ss,t,lr) \<in> everything" unfolding everything_def by blast
  show ?case
    by (rule conjI[OF every], rule bexI, rule the_set_refl[OF every],
      insert IH, auto)
next
  case (\<mu>_cond ss f ts l r i)
  note IH = this
  let ?t = "Fun f ts"
  let ?lr = "(l,r)"
  let ?f = "(f,length ts)"
  from IH(2) obtain t_lr where tlr: "t_lr \<in> Inl ` init"
    and the_set: "gen_set.the_set t_lr (Inl (ss, ?t, ?lr))" 
    and every: "Inl (ss, ?t, ?lr) \<in> everything" by auto
  have gen: "Inr (?f, i) \<in> generate (Inl (ss, ?t, ?lr))"
    using IH(3-4) by auto
  from every IH(3)  have f: "Inr (?f, i) \<in> everything" unfolding everything_def by force
  show ?case
    by (rule bexI[OF _ tlr], rule gen_set.rec_rec[OF the_set gen the_set_refl[OF f]])
next
  case (approx_cond_sub ss f ts l r i)
  note IH = this
  let ?t = "Fun f ts"
  let ?lr = "(l,r)"
  let ?f = "(f,length ts)"
  from IH(2) obtain t_lr where tlr: "t_lr \<in> Inl ` init"
    and the_set: "gen_set.the_set t_lr (Inl (ss, ?t, ?lr))" 
    and every: "Inl (ss, ?t, ?lr) \<in> everything" by auto
  have gen: "Inl (ss, ts ! i, ?lr) \<in> generate (Inl (ss, ?t, ?lr))"
    using IH(3-4) by auto
  from every have sub: "(ss,?t) \<in> all_subterms" and lr: "\<exists> s t. (s,t,?lr) \<in> init" 
    unfolding everything_def by auto
  from sub[unfolded all_subterms_def] obtain s where s: "(ss,s) \<in> all_terms" and sub: "s \<unrhd> ?t" by auto
  from IH(3) have "?t \<unrhd> ts ! i" by auto
  with sub have "s \<unrhd> ts ! i" by (rule supteq_trans)
  with s have "(ss,ts ! i) \<in> all_subterms" unfolding all_subterms_def by auto
  with lr have every: "Inl (ss,ts ! i, ?lr) \<in> everything" unfolding everything_def by auto
  show ?case
    by (rule conjI[OF every], rule bexI[OF gen_set.rec_rec[OF _ gen] tlr], rule the_set,
    rule the_set_refl[OF every])
next
  case (approx_cond_rec ss f ts l r l' r')
  note IH = this
  let ?t = "Fun f ts"
  let ?lr = "(l,r)"
  let ?f = "(f,length ts)"
  from IH(2) obtain t_lr where tlr: "t_lr \<in> Inl ` init"
    and the_set: "gen_set.the_set t_lr (Inl (ss, ?t, ?lr))" 
    and every: "Inl (ss, ?t, ?lr) \<in> everything" by auto
  have gen: "Inl (args l', r', ?lr) \<in> generate (Inl (ss, ?t, ?lr))"
    using IH(3-5) by auto
  from every have lr: "\<exists> s t. (s,t,?lr) \<in> init" unfolding everything_def by auto
  from IH(3) have "(args l', r') \<in> all_subterms" unfolding every_defs by auto
  with lr have every: "Inl (args l', r', ?lr) \<in> everything" unfolding everything_def by auto
  show ?case
    by (rule conjI[OF every], rule bexI[OF gen_set.rec_rec[OF _ gen] tlr], rule the_set,
      rule the_set_refl[OF every])
qed

lemma \<mu>_approx: "\<mu>_approx' f = {i . \<exists> t_lr \<in> init. check_approx (Inl t_lr) (Inr (f,i))}" (is "?l = ?r")
proof -
  {
    fix i
    assume "i \<in> ?r"
    then obtain t_lr where "check_approx (Inl t_lr) (Inr (f,i))" "t_lr \<in> init" by auto
    from check_approx_sound[OF this(1)] this(2) have "\<mu>_cond' f i" by auto
    then have "i \<in> ?l" unfolding \<mu>_approx_def by blast
  }
  moreover
  {
    fix i
    assume "i \<in> ?l"
    from this[unfolded \<mu>_approx_def] have "\<mu>_cond' f i" by blast
    from check_approx_complete(2)[OF this]
    have "i \<in> ?r" by auto
  }
  ultimately show ?thesis by auto
qed

context 
  fixes RR :: "('f,string)rules"
  and initt :: "(('f,string)term list \<times> ('f,string)term \<times> ('f,string)rule)list"
  and U_impl :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)rules"
  and NFQ :: "('f,string)term \<Rightarrow> bool"
  and e_cap :: "('f,string)term list \<Rightarrow> ('f,string)term \<Rightarrow> ('f, unit + string)term"
begin

definition "all_terms_impl = remdups (map (\<lambda> (ss,t,lr). (ss,t)) initt @ map (\<lambda> (l,r). (args l,r)) RR)"
definition "all_subterms_impl = remdups [ (ss,t). (ss,s) <- all_terms_impl, t <- supteq_list s]"
definition "everything_impl \<equiv> map Inl ([(ss,t,lr) . (ss,t) <- all_subterms_impl, lr <- remdups (map (snd o snd) initt)]) 
   @ remdups (map Inr [((f,length ts),i). t <- remdups (map snd all_subterms_impl), is_Fun t, (f,ts) <- (case t of Fun f ts \<Rightarrow> [(f,ts)]),
    i <- [0..<length ts]])" 

abbreviation "gen_ac_impl UU ss f ts l r \<equiv> [u . i <- [0 ..< length ts], (l,r) \<in> set (UU ss (ts ! i)), u <- [Inl (ss, ts ! i, (l,r)), Inr ((f,length ts), i)]]"
abbreviation "gen_b_impl UU ss f ts l r \<equiv> [Inl (args l', r', (l,r)) . (l',r') <- RR, mss <- [map mv_xvar ss], rule_match_impl NFQ (e_cap mss) mss f (map mv_xvar ts) l', (l,r) \<in> set (UU (args l') r')]"

fun generate_impl where 
  "generate_impl UU (Inl (ss, Fun f ts,(l,r))) = 
    gen_ac_impl UU ss f ts l r @ gen_b_impl UU ss f ts l r"
| "generate_impl UU _ = []"

definition \<mu>_approx_impl where 
  "\<mu>_approx_impl \<equiv> let 
    UU' = precompute_fun (\<lambda> (ss,t). U_impl ss t) all_subterms_impl;
    UU = \<lambda> s t. UU' (s,t);
    fis = remdups [fi. 
      entry <- inductive_set_impl everything_impl (=) (generate_impl UU) (map Inl initt),
      fi <- (case entry of Inl _ \<Rightarrow> [] | Inr fi \<Rightarrow> [fi])];
    fs = remdups (map fst fis);
    \<mu> = (\<lambda> f. set (map snd (filter (\<lambda> (g,i). g = f) fis)))
    in (fs, precompute_fun \<mu> fs, STR ''innermost URM wrt. specific rules'')"

lemmas \<mu>_approx_impl_code = 
  \<mu>_approx_impl_def 
  generate_impl.simps
  all_subterms_impl_def
  all_terms_impl_def
  everything_impl_def

context
  assumes RR: "set RR = R"
  and initt: "set initt = init"
  and U_impl: "\<And> ss t. set (U_impl ss t) = U ss t"
  and NFQ: "NFQ = (\<lambda> t. t \<in> NF_terms Q)"
  and e_cap: "\<And> ss t. e_cap (map mv_xvar ss) (mv_xvar t) = ecap R Q (mv_xvar ` set ss) (mv_xvar t)"
begin

lemma rule_match_impl_e_cap[simp]: 
  "rule_match_impl NFQ (e_cap (map mv_xvar ss)) (map mv_xvar ss) f (map mv_xvar ts) = rule_match R Q ecap (mv_xvar ` set ss) f (map mv_xvar ts)"
proof -
  let ?ss = "map mv_xvar ss"
  let ?ts = "map mv_xvar ts"
  have "rule_match_impl NFQ (e_cap ?ss) ?ss f ?ts = 
    rule_match_impl NFQ (ecap R Q (set ?ss)) ?ss f ?ts"
    by (rule rule_match_impl_cong, insert e_cap[of ss], auto)
  also have "\<dots> = rule_match R Q ecap (mv_xvar ` set ss) f ?ts"
    unfolding rule_match_impl[of Q _ R ?ss, folded NFQ] by simp
  finally show ?thesis .
qed

lemma all_terms_impl[simp]: "set all_terms_impl = all_terms" 
  unfolding all_terms_def all_terms_impl_def by (force simp: RR initt)

lemma all_subterms_impl[simp]: "set all_subterms_impl = all_subterms" 
  unfolding all_subterms_def all_subterms_impl_def by auto

lemma everything_impl[simp]: "set everything_impl = everything"
proof -
  have cong: "\<And> a b c d. a = b \<Longrightarrow> c = d \<Longrightarrow> Inl ` a \<union> Inr ` c = Inl ` b \<union> Inr ` d" by auto
  show ?thesis
    unfolding everything_impl_def everything_def set_map set_append set_remdups set_concat all_subterms_impl
    by (rule cong, (force simp: initt)+)
qed

lemma generate_impl[simp]: "set (generate_impl U_impl t) = generate t"
proof (induct t rule: generate.induct)
  case (1 ss f ts l r)
  have "set (generate_impl U_impl (Inl (ss, Fun f ts, l, r))) = 
    set (gen_ac_impl U_impl ss f ts l r) \<union> set (gen_b_impl U_impl ss f ts l r)" (is "_ = ?ac \<union> ?b") by auto
  also have "?b = gen_b ss f ts l r" by (auto simp: RR U_impl)
  also have "?ac = gen_a ss f ts l r \<union> gen_c ss f ts l r"
    by (force simp: U_impl RR) 
  finally
  show ?case by auto
qed auto

lemma \<mu>_approx_impl: assumes "\<mu>_approx_impl = (fs,\<mu>,info)"
  shows "\<mu> = \<mu>_approx' \<and> (\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {})"
proof -
  define fis where "fis = remdups
        (concat (map (\<lambda>entry. map (\<lambda>fi. fi) (case entry of Inl x \<Rightarrow> [] | Inr fi \<Rightarrow> [fi]))
                  (inductive_set_impl everything_impl (=) (generate_impl U_impl)
                    (map Inl initt))))"
  note \<mu> = assms[unfolded \<mu>_approx_impl_def precompute_fun Let_def split, folded fis_def]
  {
    fix i f
    assume f: "f \<notin> set fs" and i: "i \<in> \<mu> f"
    from i have "(f,i) \<in> set fis" using \<mu> by auto
    with \<mu> have "f \<in> set fs" by auto
    with f have False by auto
  } 
  moreover
  {
    fix f
    from \<mu> have \<mu>: "\<mu> f = {i . (f, i) \<in> set fis}" by auto
    have "\<mu> f = \<mu>_approx' f" 
      unfolding \<mu> fis_def \<mu>_approx[unfolded check_approx_def]
      unfolding set_remdups set_concat set_map
      unfolding inductive_set_impl[OF everything_impl refl generate_impl]
      unfolding set_map initt
      by (cases f, auto)
  }
  then have "\<mu> = \<mu>_approx'" by auto
  ultimately
  show ?thesis by auto
qed
end
end
end

declare urm_computation.\<mu>_approx_impl_code[code]
 
definition get_innermost_strict_repl_map_dpp where
  "get_innermost_strict_repl_map_dpp I d S \<equiv> let
     r = dpp_ops.rules I d;
     p = dpp_ops.pairs I d;
     isNF = dpp_ops.is_QNF I d;
     U = inn_usable_rules_wf_dpp I d True;
     ic = icap_impl_dpp I d
     in urm_computation.\<mu>_approx_impl r 
       [([s],t,lr) . (s,t) <- p, lr <- S] 
       (\<lambda> ss t. U (ss,t))
       isNF ic
   "

lemma get_innermost_strict_repl_map_dpp: assumes I: "dpp_spec I"
  and inn: "NF_terms (set (dpp_ops.Q I d)) \<subseteq> NF_trs (set (dpp_ops.rules I d))"
  and wfP: "wf_trs (set (dpp_ops.pairs I d))"
  and wf: "wwf_qtrs (set (dpp_ops.Q I d)) (set (dpp_ops.rules I d))"
  and S: "set S \<subseteq> (set (dpp_ops.rules I d))"
  and res: "get_innermost_strict_repl_map_dpp I d S = (fs, \<mu>, info)"
  shows "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "(s,t) \<in> set (dpp_ops.pairs I d) \<Longrightarrow> s \<cdot> \<sigma> \<in> NF_terms (set (dpp_ops.Q I d)) \<Longrightarrow> usable_replacement_map \<mu> {t \<cdot> \<sigma>} (dpp_ops.nfs I d) (set (dpp_ops.rules I d)) (set (dpp_ops.Q I d)) (set S)"
proof -
  interpret dpp_spec I by fact
  let ?R = "set (rules d)"
  let ?P = "set (pairs d)"
  let ?nfs = "NFS d"
  let ?Q = "set (Q d)"
  let ?S = "set S"
  note res = res[unfolded get_innermost_strict_repl_map_dpp_def Let_def]
  let ?init = "concat (map (\<lambda>(s, t). map (\<lambda>lr. ([s], t, lr)) S) (pairs d))"
  let ?Init = "{([s],t,lr) | s t lr. (s,t) \<in> ?P \<and> lr \<in> ?S}"
  let ?U = "(\<lambda>ss t. set (inn_usable_rules_wf_dpp I d True (ss, t)))"
  have init: "set ?init = ?Init" by auto
  from res have res: "urm_computation.\<mu>_approx_impl (rules d) ?init
    (\<lambda>ss t. inn_usable_rules_wf_dpp I d True (ss, t)) (\<lambda> t. t \<in> NF_terms ?Q) (icap_impl_dpp I d) =
    (fs, \<mu>, info)" by simp
  from inn_usable_rules_wf_dpp_approx[OF I inn wf, of True]
  have U: "usable_rules_approx ?Q ?R True ?U" by auto
  from urm_computation.\<mu>_approx_impl[OF refl init refl refl _ res, of icap',
    unfolded icap_impl_dpp_icap[OF I]] icap'[of ?R ?Q]
  have \<mu>: "\<mu> = \<mu>_approx icap' ?R ?Q ?U ?Init" and fs: "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" by auto
  show "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" by fact
  assume P: "(s,t) \<in> set (dpp_ops.pairs I d)" and NF: "s \<cdot> \<sigma> \<in> NF_terms (set (dpp_ops.Q I d))"
  from P have mem: "{[s]} \<times> {t} \<times> ?S \<subseteq> ?Init" by auto
  note urm = aprove_urm_for_DP[OF inn icap wf U S P NF mem wfP, of ?nfs]
  from aprove_urm_for_DP[OF inn icap wf U S P NF mem wfP, of ?nfs, folded \<mu>]
  show "usable_replacement_map \<mu> {t \<cdot> \<sigma>} ?nfs ?R ?Q ?S" .
qed

fun get_innermost_strict_repl_map_rc where
  "get_innermost_strict_repl_map_rc I d S (Derivational_Complexity F) = (full_empty (remdups (F @ 
  usable_replacement_map.default_fs (tp_ops.rules I d))))"
| "get_innermost_strict_repl_map_rc I d S (Runtime_Complexity C D) = (
   let r = tp_ops.rules I d in
   if tp_ops.NFQ_subset_NF_rules I d \<and> set C \<inter> set (defined_list r) \<subseteq> {}
   then (let
     isNF = tp_ops.is_QNF I d;
     U = inn_usable_rules_wf_tp I d True;
     ic = icap_impl_tp I d
     in 
       urm_computation.\<mu>_approx_impl r 
       [(xs,Fun f xs,lr) . (f,n) <- D, xs <- [map Var (x\<^sub>1_to_x\<^sub>n n)], lr <- S] 
       (\<lambda> ss t. U (ss,t))
       isNF ic) 
   else 
     full_empty (remdups (C @ D @
       usable_replacement_map.default_fs r)))
   "

lemma get_innermost_strict_repl_map_rc: assumes I: "tp_spec I"
  and wf: "wf_trs (set (tp_ops.rules I d))"
  and S: "set S \<subseteq> (set (tp_ops.rules I d))"
  and res: "get_innermost_strict_repl_map_rc I d S T = (fs, \<mu>, info)"
  shows "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of T) (tp_ops.nfs I d) 
    (set (tp_ops.rules I d)) (set (tp_ops.Q I d)) (set S)" (is ?goal)
proof -
  interpret tp_spec I by fact
  interpret usable_replacement_map "rules d" "Q d" undefined .  
  let ?R = "set (rules d)"
  let ?nfs = "NFS d"
  let ?Q = "set (Q d)"
  let ?S = "set S"
  {
    assume "usable_replacement_map \<mu> (terms_of T) ?nfs ?R ?Q ?R"
    from usable_replacement_map_mono[OF subset_refl subset_refl S this]
    have "usable_replacement_map \<mu> (terms_of T) ?nfs ?R ?Q ?S" .
  } note switch = this
  have "?goal \<and> (\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {})"
  proof (cases T)
    case (Derivational_Complexity F)
    note dc = this
    from res[unfolded dc] have "full_empty (remdups (F @ usable_replacement_map.default_fs (rules d))) = (fs, \<mu>, info)"
      by auto 
    from full_empty[OF this _ _ wf, of T, unfolded dc]
    show ?thesis 
      by (intro conjI switch, auto simp: dc)
  next
    case (Runtime_Complexity C D)
    note rc = this
    note res = res[unfolded rc get_innermost_strict_repl_map_rc.simps Let_def]
    let ?test = "NFQ_subset_NF_rules d \<and> set C \<inter> set (defined_list (rules d)) \<subseteq> {}"
    show ?thesis
    proof (cases ?test)
      case False
      with res have "full_empty (remdups (C @ D @ usable_replacement_map.default_fs (rules d))) = (fs, \<mu>, info)"
       by (auto split: if_splits)
      note fe = full_empty[OF this _ _ wf, of T, unfolded rc]
      show ?thesis 
        by (intro conjI switch, insert fe, auto simp: rc)
    next
      case True
      then have "?test = True" by simp
      note res = res[unfolded this if_True]
      from True have inn: "NF_terms ?Q \<subseteq> NF_trs ?R" by auto
      let ?init = "(concat (map (\<lambda>(f, n). concat (map (\<lambda>xs. map (\<lambda>lr. (xs, Fun f xs, lr)) S) [map Var (x\<^sub>1_to_x\<^sub>n n)])) D))"  
      let ?Init = "{(map Var (x\<^sub>1_to_x\<^sub>n n), Fun f (map Var (x\<^sub>1_to_x\<^sub>n n)),lr) | f n lr. (f,n) \<in> set D \<and> lr \<in> ?S}"
      let ?U = "(\<lambda>ss t. set (inn_usable_rules_wf_tp I d True (ss, t)))"
      have init: "set ?init = ?Init" by auto
      from res have res: "urm_computation.\<mu>_approx_impl (rules d) ?init
        (\<lambda>ss t. inn_usable_rules_wf_tp I d True (ss, t)) (\<lambda> t. t \<in> NF_terms ?Q) (icap_impl_tp I d) =
        (fs, \<mu>, info)" by simp
      from inn_usable_rules_wf_tp_approx[OF I inn wf_trs_imp_wwf_qtrs[OF wf], of True]
      have U: "usable_rules_approx ?Q ?R True ?U" by auto
      from urm_computation.\<mu>_approx_impl[OF refl init refl refl _ res, of icap',
        unfolded icap_impl_tp_icap[OF I]] icap'[of ?R ?Q]
      have \<mu>: "\<mu> = \<mu>_approx icap' ?R ?Q ?U ?Init" and fs: "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" by auto
      show ?thesis
      proof 
        show "usable_replacement_map \<mu> (terms_of T) (NFS d) (set (rules d)) (set (Q d)) (set S)"
          unfolding rc \<mu>
          by (rule aprove_urm_complexity[OF inn icap wf_trs_imp_wwf_qtrs[OF wf] U S],
            insert True, auto)
      qed (insert fs, auto)
    qed
  qed
  then show "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" ?goal by auto
qed

definition get_innermost_strict_repl_map_rc_DP where
  "get_innermost_strict_repl_map_rc_DP I d S T = (
   let (fs,\<mu>,info) = get_innermost_strict_repl_map_rc I d S T   
   in (case check_DP_complexity (tp_ops.rules I d) T of 
     Inr (RS, R', Cp, FS, F) \<Rightarrow> if set S \<subseteq> set RS then (list_inter fs Cp, \<lambda> f. if f \<in> set Cp then \<mu> f else {}, info + STR '' with DPs'') else (fs,\<mu>,info)
     | _ \<Rightarrow> (fs,\<mu>,info)))"

lemma get_innermost_strict_repl_map_rc_DP: assumes I: "tp_spec I"
  and wf: "wf_trs (set (tp_ops.rules I d))"
  and S: "set S \<subseteq> (set (tp_ops.rules I d))"
  and res: "get_innermost_strict_repl_map_rc_DP I d S T = (fs, \<mu>, info)"
  shows "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}"
  and "usable_replacement_map \<mu> (terms_of T) (tp_ops.nfs I d) 
    (set (tp_ops.rules I d)) (set (tp_ops.Q I d)) (set S)" (is ?goal)
proof -
  interpret tp_spec I by fact
  let ?R = "set (rules d)"
  let ?inn = "get_innermost_strict_repl_map_rc I d S T"
  obtain fs' \<mu>' info' where inn: "?inn = (fs',\<mu>',info')" by (cases ?inn)
  note res = res[unfolded get_innermost_strict_repl_map_rc_DP_def Let_def inn split]
  note inn2 = get_innermost_strict_repl_map_rc[OF I wf S inn]
  let ?check = "check_DP_complexity (rules d) T"
  have "?goal \<and> (\<forall> f. f \<notin> set fs \<longrightarrow> \<mu> f = {})"
  proof (cases "(fs,\<mu>,info) = (fs',\<mu>',info')")
    case True
    with inn2 show ?thesis by auto
  next
    case False
    then obtain tuple where check: "?check = Inr tuple" using res by (cases ?check, auto)
    obtain RS R' Cp FS F where tuple: "tuple = (RS, R', Cp, FS, F)" by (cases tuple)
    from res[unfolded check tuple, simplified] False have S: "set S \<subseteq> set RS"
    and fs: "fs = list_inter fs' Cp" and \<mu>: "\<mu> = (\<lambda>f. if f \<in> set Cp then \<mu>' f else {})" 
      by (auto split: if_splits)
    from check_DP_complexity[OF check[unfolded tuple] wf]
    have R: "?R = set RS \<union> set R'" and dp: "is_DP_complexity (set Cp) (set FS) (set F) (set RS) (set R') T"
      by auto
    have urm: "usable_replacement_map \<mu> (terms_of T) (NFS d) ?R (set (Q d)) (set S)"    
      by (rule avanzini_14_34[OF inn2(2)[unfolded R] dp S, folded R], auto simp: \<mu>)
    show ?thesis
      by (rule conjI[OF urm], auto simp: fs \<mu> inn2(1))
  qed
  then show "\<And> f. f \<notin> set fs \<Longrightarrow> \<mu> f = {}" ?goal by auto
qed


section \<open>Processors\<close>

definition showsl_position_set :: "'f \<times> nat \<Rightarrow> nat set \<Rightarrow> showsl" where
  "showsl_position_set f s = showsl_list [Suc i . i <- [0 ..< snd f], i \<in> s]"

definition
  rule_shift_complexity_urm_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> ('f,string)rules \<Rightarrow>
    ('f,string)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> 'tp proc"
where
  "rule_shift_complexity_urm_tt I rp Rdelete cm cc tp \<equiv> let 
      Rb = tp_ops.rules I tp;
      R = tp_ops.R I tp;
      Rw = tp_ops.Rw I tp;
      R2 = ceta_list_diff R Rdelete ;
      Q = tp_ops.Q I tp
  in
 check_return (do {
     check_subseteq Rdelete Rb 
        <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> 
          showsl_lit (STR '' should be deleted, but does not occur in problem''));
     check_wf_trs Rb;
     let (fs,\<mu>,info) = get_innermost_strict_repl_map_rc_DP I tp Rdelete cm;
     rel_impl_redpair rp;
     (check_allm (\<lambda> f. check (\<mu> f \<subseteq> rel_impl.mono_af rp f) 
       (showsl_lit (STR ''error in monotonicity: strict order for '') o showsl f
       o showsl_lit (STR '' ensures monotonicity in positions '') o showsl_position_set f (rel_impl.mono_af rp f)
       o showsl_lit (STR ''\<newline>but usable replacement map is '')
       o showsl_position_set f (\<mu> f))) fs) <+? 
     (\<lambda> s. s o showsl_lit (STR ''\<newline>the computed usable replacement map ('') o showsl info o showsl_lit (STR '') is\<newline>'') o
       showsl_sep (\<lambda> f. showsl_lit (STR ''mu('') o showsl f o showsl_lit (STR '') = '') o showsl_position_set f (\<mu> f)) showsl_nl fs
       o showsl_lit (STR ''\<newline>and mu(f) = {} for all other symbols f''));
     rel_impl_s rp Rdelete
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting strict TRS\<newline>'') o s);
     rel_impl_ns rp (Rw @ R2)
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting non-strict TRS\<newline>'') o s);
     rel_impl.cpx rp cm cc
       <+? (\<lambda>s. showsl_lit (STR ''problem when ensuring complexity of order\<newline>'') o s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not derive the intended complexity '') o showsl cc o showsl_lit (STR '' from the following\<newline>'') o
     (rel_impl.desc rp) o showsl_nl o s))
     (tp_ops.mk I (tp_ops.nfs I tp) (tp_ops.Q I tp) R2 (list_union Rw Rdelete))"

lemma rule_shift_complexity_urm_tt:
  assumes I: "tp_spec I"
  and rp: "rel_impl rp"
  and res: "rule_shift_complexity_urm_tt I rp Rdelete cm cc tp = return tp'"
  and cpx: "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp')) cm cc"
  shows "deriv_bound_measure_class (rel_qrstep (tp_ops.qreltrs I tp)) cm cc"
proof -
  interpret tp_spec I by fact
  note res = res[unfolded rule_shift_complexity_urm_tt_def Let_def, simplified]
  let ?R = "set (R tp)"
  let ?Rw = "set (Rw tp)"
  let ?D = "ceta_list_diff (R tp) Rdelete"
  let ?RwD = "Rw tp @ ?D"
  let ?nfs = "NFS tp"
  let ?Q = "qrstep ?nfs (set (Q tp))"
  let ?us = "get_innermost_strict_repl_map_rc_DP I tp Rdelete cm"
  let ?pi = "rel_impl.mono_af rp"
  obtain fs \<mu> info where us: "?us = (fs,\<mu>,info)" by (cases ?us)
  note res = res[unfolded us, simplified]
  from res have valid: "isOK (rel_impl_redpair rp)"
    and S: "isOK(rel_impl_s rp Rdelete)" 
    and NS: "isOK(rel_impl_ns rp ?RwD)"
    and af: "\<And> f. f \<in> set fs \<Longrightarrow> \<mu> f \<subseteq> ?pi f"
    and wf: "wf_trs (set (rules tp))"
    and subset: "set Rdelete \<union> (?Rw \<union> set ?D) \<subseteq> ?R \<union> ?Rw" "set Rdelete \<subseteq> ?R \<union> ?Rw" "set Rdelete \<subseteq> set (rules tp)"
    by (auto simp: rel_impl_list)
  have rules: "set (rules tp) = ?R \<union> ?Rw" by auto
  note urm = get_innermost_strict_repl_map_rc_DP[OF I wf subset(3) us, unfolded rules]
  have af: "af_subset \<mu> ?pi" unfolding af_subset_def
  proof 
    fix f
    show "\<mu> f \<subseteq> ?pi f"
      by (cases "f \<in> set fs", rule af, insert urm(1), auto)
  qed
  let ?cpx = "rel_impl.cpx rp cm cc"
  from res have tp': "tp' = mk ?nfs (Q tp) ?D (list_union (Rw tp) Rdelete)" by simp
  from cpx[unfolded tp', simplified] 
  have bound: "deriv_bound_measure_class (relto (?Q (?R - set Rdelete)) (?Q (?Rw \<union> set Rdelete))) cm cc" .
  from res have cpx: "isOK ?cpx" by auto
  from rel_impl_redpair[OF rp valid S NS, of cm cc] cpx
  obtain S NS where "compat_redpair_order S NS" 
  and S: "set Rdelete \<subseteq> S" and NS: "set ?RwD \<subseteq> NS"
  and af_mono: "af_monotone (rel_impl.mono_af rp) S" 
  and bnd: "deriv_bound_measure_class S cm cc" 
    by blast
  from NS have NS: "?Rw \<union> set ?D \<subseteq> NS" by auto
  interpret compat_redpair_order S NS by fact
  have bound1: "deriv_bound_measure_class (relto (?Q (set Rdelete)) (?Q (?Rw \<union> set ?D))) cm cc"
    by (rule avanzini_14_10[OF af_mono S NS usable_replacement_map_mono[OF _ subset(1) _ urm(2)] af bnd], auto)
  have bound: "deriv_bound_measure_class (relto (?Q (set Rdelete \<union> set ?D)) (?Q ?Rw)) cm cc"
    unfolding qrstep_union
    by (rule deriv_bound_relto_measure_class_union, insert bound bound1, auto simp: qrstep_union)
  have bound: "deriv_bound_measure_class (relto (?Q ?R) (?Q ?Rw)) cm cc" 
    by (rule deriv_bound_measure_class_mono[OF relto_mono[OF qrstep_mono[OF _ subset_refl] subset_refl] subset_refl subset_refl bound], auto)
  then show ?thesis by simp
qed

end
