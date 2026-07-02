(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Size_Change_Termination_Processors
imports
  Size_Change_Termination
  Generic_Usable_Rules
  Subterm_Criterion
  Dependency_Graph
begin

(* get_arg delivers the whole term (for 0), or otherwise the i-th argument, where 
   arguments are here indexed starting by 1 *)
fun get_arg :: "('f, 'v) term \<Rightarrow> nat \<Rightarrow> ('f, 'v) term" where
  "get_arg t 0 = t"
| "get_arg t (Suc n) = args t ! n"

lemma (in redtriple) sct_semantics: "sct_semantics S (NS \<union> NST)"
  by (rule sct_semantics.intro, rule SN, rule both.compat)

lemma generic_sct_redtriple:
   fixes P :: "('f,'v)trs" and R :: "('f,'v)rules" and Gs :: "('a :: compare_order, nat) scg list"
   and info :: "('f,'v)rule \<Rightarrow> 'a"
  defines sts: "sts \<equiv> {(s,get_arg t j) | s t j . \<exists> st ns. Scg (info (s,t)) (info (s,t)) st ns \<in> set Gs \<and> j \<in> snd ` set st \<union> snd ` set ns}"
  assumes tuple: "\<forall> (s,t) \<in> P. is_Fun s \<and> is_Fun t \<and> \<not> defined (set R) (the (root t))"
  and var_R: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> is_Fun l"
  and checker: "usable_rules_checker checker"
  and U: "set U \<subseteq> NS"
  and redtriple: "af_redtriple S NS NST \<pi>"
  and ce: "ce \<Longrightarrow> ce_compatible NS" 
  and Ucheck: "checker nfs m ce (wwf_qtrs Q (set R)) \<pi> Q R U_opt sts = Some U"
  and graphs: "\<forall> (s,t) \<in> P. \<exists> stri non_stri. (
         Scg (info (s,t)) (info (s,t)) ( stri) ( non_stri) \<in> set Gs \<and>
         (\<forall> (i,j) \<in> set stri. i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> S) \<and> 
         (\<forall> (i,j) \<in> set non_stri. i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> NST))"
  and edg: "\<And> st uv. (st,uv) \<in> DG nfs m P Q (set R) \<Longrightarrow> edg (info st) (info uv)"  
  and check: "check_SCT (\<lambda> i_st i_uv. edg i_st i_uv) Gs" (is "check_SCT ?conn Gs")
  and P: "P = Ps \<union> Pw" and R: "set R = set Rs \<union> set Rw"
  shows "finite_dpp (nfs,m,Ps,Pw,Q,set Rs,set Rw)"
proof -
  interpret af_redtriple S NS NST \<pi>  by fact
  let ?rd = "\<lambda> x. x"
  show ?thesis
  proof (rule finite_dpp_mono)
    show "finite_dpp (nfs,m,P,{},Q,set R,{})" unfolding finite_dpp_def
    proof (clarify)
      fix s t \<sigma>
      assume chain: "min_ichain (nfs,m,P, {}, Q, set R, {}) s t \<sigma>"
      have redp: "af_redpair S NS \<pi>" ..
      let ?R = "qrstep nfs Q (set R)"
      let ?Rs = "?R^*"
      note checker[unfolded usable_rules_checker_def, rule_format, OF Ucheck redp U ce]
      then obtain I where I: "\<And> s t u \<sigma> \<tau>. (s,t) \<in> sts \<Longrightarrow> s \<cdot> \<sigma> \<in> NF_terms Q \<Longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<Longrightarrow> (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> ?Rs \<Longrightarrow> (m \<Longrightarrow> SN_on ?R {t \<cdot> \<sigma>}) \<Longrightarrow> (t \<cdot> I \<sigma>, u \<cdot> I \<tau>) \<in> NS^*" by blast
      let ?entry = "\<lambda> k. (info (s k,t k))"
      let ?Is = "\<lambda> i. I (\<sigma> i)"
      let ?pairs = "\<lambda> k. (?entry k, (\<lambda> j. get_arg (s k) j \<cdot> ?Is k))"
      let ?R = "{(?pairs k, ?pairs (Suc k)) | k. True}"
      let ?S = "(NS \<union> NST \<union> S)\<^sup>* O S O (NS \<union> NST \<union> S)\<^sup>*"
      let ?NS = "(NS \<union> NST \<union> S)\<^sup>*"
      {
        fix k
        let ?sk = "\<lambda> i. get_arg (s k) i \<cdot> \<sigma> k"
        let ?tk = "\<lambda> i. get_arg (t k) i \<cdot> \<sigma> k"
        let ?sk1 = "\<lambda> i. args (s (Suc k)) ! i \<cdot> \<sigma> (Suc k)"
        let ?Isk = "\<lambda> i. get_arg (s k) i \<cdot> ?Is k"
        let ?Itk = "\<lambda> i. get_arg (t k) i \<cdot> ?Is k"
        let ?Isk1 = "\<lambda> i. get_arg (s (Suc k)) i \<cdot> ?Is (Suc k)"
        from chain have inP': "(s (Suc k), t (Suc k)) \<in> P" by (auto simp: ichain.simps)
        from chain have inP: "(s k, t k) \<in> P" by (auto simp: ichain.simps)
        with tuple have validDP: "is_Fun (t k) \<and> \<not> defined (set R) (the (root (t k)))" by auto
        from chain inP tuple have validDP1: "is_Fun (s (Suc k))" by (auto simp: ichain.simps)
        from chain have steps: "(t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?Rs" by (auto simp: ichain.simps)
        from chain have NF: "(s k \<cdot> \<sigma> k) \<in> NF_terms Q" by (auto simp: ichain.simps)
        from chain have NFs: "(s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> NF_terms Q" by (auto simp: ichain.simps)
        from chain have nfs: "NF_subst nfs (s k, t k) (\<sigma> k) Q" by (auto simp: ichain.simps)
        from chain have nfs': "NF_subst nfs (s (Suc k), t (Suc k)) (\<sigma> (Suc k)) Q" by (auto simp: ichain.simps)
        from chain have tSN: "m \<Longrightarrow> SN_on (qrstep nfs Q (set R)) {t k \<cdot> \<sigma> k}" by (simp add: minimal_cond_def)
        have argSteps: "\<And> j. j \<le> length (args (t k)) \<Longrightarrow> (s k, get_arg (t k) j) \<in> sts \<Longrightarrow> (?Itk j, ?Isk1 j) \<in> NS^*"
        proof -
          fix j1
          assume j1: "j1 \<le> length (args (t k))" and mem: "(s k, get_arg (t k) j1) \<in> sts"
          note I = I[OF mem NF]
          show "(?Itk j1, ?Isk1 j1) \<in> NS^*"
          proof (cases j1)
            case 0
            show ?thesis
              by (rule I, unfold 0, insert steps tSN nfs, auto)
          next
            case (Suc j)
            with j1 have j: "j < length (args (t k))" by auto
            note I = I[unfolded Suc get_arg.simps]
            let ?tj = "args (t k) ! j"
            let ?sj = "args (s (Suc k)) ! j"
            from validDP obtain f ts where tk: "t k = Fun f ts \<and> \<not> defined (set R) (f,length ts)" by (cases "t k", auto)
            from validDP1 obtain g ss where sk1: "s (Suc k) = Fun g ss" by (cases "s (Suc k)", auto) 
            let ?tss = "(map (\<lambda> t. t \<cdot> \<sigma> k) ts)"
            from tk have f: "\<not> defined (set R) (f, length ?tss)" by simp
            let ?sss = "(map (\<lambda> s. s \<cdot> \<sigma> (Suc k)) ss)"
            from tSN have SN: "m \<Longrightarrow> SN_on (qrstep nfs Q (set R)) {Fun f ?tss}" using tk by auto
            from tk j have "?tj \<in> set ts" by auto
            then have "vars_term ?tj \<subseteq> vars_term (t k)" using tk by auto
            with nfs have nfs: "NF_subst nfs (s k, ?tj) (\<sigma> k) Q" unfolding NF_subst_def vars_rule_def by auto
            note I = I[OF this]
            from tk j have mem: "?tj \<cdot> \<sigma> k \<in> set ?tss" by auto
            from steps have "(Fun f ts \<cdot> \<sigma> k, Fun g ss \<cdot> \<sigma> (Suc k)) \<in> ?Rs" using tk sk1 by auto
            then have steps2: "(Fun f ?tss, Fun g ?sss) \<in> ?Rs" by auto
            have "\<exists> us. length us = length ?tss \<and> Fun g ?sss = Fun f us \<and> (\<forall> i < length ?tss. (?tss ! i, us ! i) \<in> ?Rs)" 
              by (rule nondef_root_imp_arg_qrsteps[OF steps2], insert var_R f, force+)
            from this obtain us where nearly: "length us = length ?tss \<and> Fun g ?sss = Fun f us \<and> (\<forall> i < length ?tss. (?tss ! i, us ! i) \<in> ?Rs)" ..
            from nearly j tk sk1 have "(?tj \<cdot> \<sigma> k, ?sj \<cdot> \<sigma> (Suc k)) \<in> ?Rs" (is ?part1) by auto
            have SN2: "m \<Longrightarrow> SN_on (qrstep nfs Q (set R)) {?tj \<cdot> \<sigma> k}"
              by (rule SN_imp_SN_arg_gen[OF ctxt_closed_qrstep SN mem])
            note I = I[OF \<open>?part1\<close> SN2]
            then show ?thesis unfolding Suc by simp
          qed
        qed
        from steps have rsteps: "(t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> (rstep (set R))^*"
          using rtrancl_mono[OF qrstep_subset_rstep] by auto
        have "((s k, t k), (s (Suc k), t (Suc k))) \<in> DG nfs m P Q (set R)"
          by (rule DG_I[OF inP inP' steps NF NFs nfs nfs' tSN])
        from edg[OF this]
        have conn: "?conn (?entry k) (?entry (Suc k))" by auto
        from inP obtain stri non_stri where graph: "Scg (?entry k) (?entry k) (?rd stri) (?rd non_stri) \<in> set Gs \<and> 
          (\<forall> (i,j) \<in> set stri. i \<le> length (args (s k)) \<and> j \<le> length (args (t k)) \<and> (get_arg (s k) i, get_arg (t k) j) \<in> S) \<and> 
          (\<forall> (i,j) \<in> set non_stri. i \<le> length (args (s k)) \<and> j \<le> length (args (t k)) \<and> (get_arg (s k) i, get_arg (t k) j) \<in> NST)" using graphs by force
        let ?g = "Scg (?entry k) (?entry k) (?rd stri) (?rd non_stri)"
        from graph have gGs: "?g \<in> set Gs" ..
        let ?check = "\<lambda> g. ((?entry k, ?Isk), (?entry (Suc k)), ?Isk1)
          \<in> sct_semantics.steps S (NS \<union> NST) ?conn g"
        have "?check ?g"
        proof (simp add: sct_semantics.steps.simps sct_semantics conn[simplified], intro conjI)
          {
            fix i j
            assume ij: "(i,j) \<in> set non_stri"
            with graph have i: "i \<le> length (args (s k))" and j: "j \<le> length (args (t k))"
              and NS: "(get_arg (s k) i, get_arg (t k) j) \<in> NST" by auto
            have "(s k, get_arg (t k) j) \<in> sts" unfolding sts using graph[THEN conjunct1] ij by force
            from argSteps[OF j this]
            have astepsNS: "(?Itk j, ?Isk1 j) \<in> NS^*"  .
            from NS subst_NST have non_strict: "(?Isk i, ?Itk j) \<in> NST" unfolding subst.closed_def using subst.closure.intros by blast
            have NS: "(?Isk i, ?Isk1 j) \<in> NST O NS^*" using astepsNS non_strict by blast
            have "(?Isk i, ?Isk1 j) \<in> ?NS" by (rule set_mp[OF _ NS], regexp)
          }
          then show "\<forall>ij\<in>set non_stri. (\<lambda>(i, j). (?Isk i, ?Isk1 j) \<in> ?NS) ij" by blast
        next
          {
            fix i j
            assume ij: "(i,j) \<in> set stri"
            with graph have i: "i \<le> length (args (s k))" and j: "j \<le> length (args (t k))"
              and S: "(get_arg (s k) i, get_arg (t k) j) \<in> S" by auto 
            have "(s k, get_arg (t k) j) \<in> sts" unfolding sts using graph[THEN conjunct1] ij by force
            from argSteps[OF j this]
            have astepsNS: "(?Itk j, ?Isk1 j) \<in> NS^*"  .
            from S subst_S have strict: "(?Isk i, ?Itk j) \<in> S" unfolding subst.closed_def using subst.closure.intros by blast
            have S: "(?Isk i, ?Isk1 j) \<in> S O NS^*" using strict astepsNS by blast
            have "(?Isk i, ?Isk1 j) \<in> ?S" by (rule set_mp[OF _ S], regexp)
          }
          then show "\<forall>ij\<in>set stri.(\<lambda>(i, j). (?Isk i, ?Isk1 j) \<in> ?S) ij" by auto
        qed
        with gGs have "\<exists> g \<in> set Gs. ?check g" by auto
      }
      then have main: "?R \<subseteq> (\<Union>G \<in> set Gs. sct_semantics.steps S (NS \<union> NST) ?conn G)" by auto
      have "SN ?R"
        by (rule sct_semantics.SCT_correctness2[where S = S and NS = "NS \<union> NST"], rule sct_semantics, rule main, rule check)
      obtain f where "f = ?pairs" by auto
      then have id: "?R = {(f k, f (Suc k)) | k. True}" by auto
      have "\<not> SN ?R" unfolding SN_defs by (simp only: id, blast) 
      with \<open>SN ?R\<close> show False by auto
    qed
  qed (auto simp: R P)
qed

lemma sct_with_subterm:
  assumes chain: "min_ichain (nfs,m,P, {}, Q, R, {}) s t \<sigma>"
    and tuple: "\<forall>(s, t)\<in>P. is_Fun s \<and> is_Fun t \<and> \<not> defined R (the (root t))"
    and graphs: "\<forall>(s, t)\<in>P. \<exists>stri nstri. (
      Scg (info (s, t)) (info (s, t)) (remdups_sort stri) (remdups_sort nstri) \<in> set Gs
      \<and> (\<forall>(i, j)\<in>set stri.
        i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> supt)
      \<and> (\<forall>(i, j)\<in>set nstri.
        i \<le> length (args s) \<and> j \<le> length (args t) \<and> (get_arg s i, get_arg t j) \<in> supteq))"
    and no_left_vars: "\<forall>(l, r)\<in>R. is_Fun l"
    and m_or_inn: "m \<or> NF_terms Q \<subseteq> NF_trs R"
    and edg: "\<And> st uv. (st,uv) \<in> DG nfs m P Q R \<Longrightarrow> edg (info st) (info uv)"  
    and check: "check_SCT (\<lambda> i_st i_uv. edg i_st i_uv) Gs" (is "check_SCT ?conn Gs")
   shows False
proof -
  let ?entry = "\<lambda>k. info (s (Suc k), t (Suc k))"
  let ?s = "\<lambda>i. s (Suc i)"
  let ?t = "\<lambda>i. t (Suc i)"
  let ?\<sigma> = "\<lambda>i. \<sigma> (Suc i)"
  let ?qrstep = "qrstep nfs Q R"
  let ?supt = "restrict_SN (({\<rhd>} \<union> ?qrstep)^+) ?qrstep"
  let ?supteq = "restrict_SN (?qrstep^* ) ?qrstep"
  let ?pairs = "\<lambda>k. (?entry k, (\<lambda>j. get_arg (?s k) j \<cdot> ?\<sigma> k))"
  let ?Rs = "?qrstep^*"
  let ?R = "{(?pairs k, ?pairs(Suc k)) | k. True}"
  let ?S = "(?supteq \<union> ?supt)^* O ?supt O (?supteq \<union> ?supt)^*"
  let ?NS = "(?supteq \<union> ?supt)^*"
  have sct_semantics: "sct_semantics ?supt ?supteq"
  proof
    show "SN ?supt"
    proof -
      have "\<forall>t. SN_on ?supt {t}"
      proof (rule ccontr)
        assume "\<not>(\<forall>t. SN_on ?supt {t})"
        then obtain t where "\<not> SN_on ?supt {t}" by auto
        then obtain S where "S 0 = t" and "\<forall>i. (S i, S (Suc i)) \<in> ?supt"
          unfolding SN_defs by auto
        then have "\<forall>i. SN_on ?qrstep {S i}" unfolding restrict_SN_def by simp
        then have "SN_on ?qrstep {S 0}" by simp
        then have "SN_on ({\<rhd>} \<union> ?qrstep) {t}" unfolding \<open>S 0 = t\<close>
          by (rule SN_on_qrstep_imp_SN_on_supt_union_qrstep)
        then have "SN_on (({\<rhd>} \<union> ?qrstep)^+) {t}" by (rule SN_on_trancl)
        moreover have "?supt \<subseteq> ({\<rhd>} \<union> ?qrstep)^+" by (rule restrict_SN_subset)
        ultimately have "SN_on ?supt {t}" by (rule SN_on_subset1)
        with \<open>\<not> SN_on ?supt {t}\<close> show False by simp
      qed
      then show ?thesis unfolding SN_defs by simp
    qed
  next
    show "?supteq O ?supt \<subseteq> ?supt"
    proof (rule subrelI)
      fix s t assume "(s, t) \<in> ?supteq O ?supt"
      then obtain u where fst: "(s, u) \<in> ?supteq" and snd: "(u, t) \<in> ?supt" by auto
      have "(s, u) \<in> ?Rs" and "SN_on ?qrstep {s}" using fst unfolding restrict_SN_def by auto
      moreover have "(u, t) \<in> ({\<rhd>} \<union> ?qrstep)^+" and "SN_on ?qrstep {u}" using snd
        unfolding restrict_SN_def by auto
      ultimately show "(s, t) \<in> ?supt"
      proof (induct)
        case base then show ?case unfolding restrict_SN_def by simp
      next
        case (step v w)
        from \<open>(v, w) \<in> ?qrstep\<close> have "(v, w) \<in> ?qrstep^+" by simp
        with trancl_union_right[where r="?qrstep" and s="{\<rhd>}"]
          have "(v, w) \<in> ({\<rhd>} \<union> ?qrstep)^+" by blast
        with \<open>(w, t) \<in> ({\<rhd>} \<union> ?qrstep)^+\<close> have "(v, t) \<in> ({\<rhd>} \<union> ?qrstep)^+" by simp
        moreover have "SN_on ?qrstep {v}"
          by (rule steps_preserve_SN_on[OF \<open>(s, v) \<in> ?Rs\<close> \<open>SN_on ?qrstep {s}\<close>])
        ultimately show ?case using step by simp
      qed
    qed
  qed
  from chain
    have inR: "\<forall>k. (t k \<cdot> \<sigma> k, s (Suc k) \<cdot> \<sigma> (Suc k)) \<in> ?qrstep^*" by (auto simp: ichain.simps)
  {
    fix k
    {
      assume "NF_terms Q \<subseteq> NF_trs R"
      with chain have NF: "?s k \<cdot> ?\<sigma> k \<in> NF_trs R" by (auto simp: ichain.simps)
    } note NF = this
    from m_or_inn have min_s: "SN_on ?qrstep {?s k \<cdot> ?\<sigma> k}"
    proof
      assume NFQ: "NF_terms Q \<subseteq> NF_trs R"
      show ?thesis
        by (rule NF_imp_SN_on[OF set_mp[OF NF_anti_mono NF[OF NFQ]]], auto)
    next
      assume m
      with chain have min_t: "SN_on ?qrstep {t k \<cdot> \<sigma> k}" by (auto simp: minimal_cond_def)
      from inR have step: "(t k \<cdot> \<sigma> k, ?s k \<cdot> ?\<sigma> k) \<in> ?qrstep^*" by auto 
      from steps_preserve_SN_on[OF step min_t] show "SN_on ?qrstep {?s k \<cdot> ?\<sigma> k}" .
    qed
    note min_s NF
  } note min_s = this
  {
    fix k
    let ?sk = "\<lambda>i. get_arg (?s k) i \<cdot> ?\<sigma> k"
    let ?tk = "\<lambda>i. get_arg (?t k) i \<cdot> ?\<sigma> k"
    let ?sk1 = "\<lambda>i. get_arg (?s (Suc k)) i \<cdot> ?\<sigma> (Suc k)"
    from chain have inP: "(?s k, ?t k) \<in> P" by (auto simp: ichain.simps)
    from chain have inP': "(?s (Suc k), ?t (Suc k)) \<in> P" by (auto simp: ichain.simps)
    from chain have inR: "(?t k \<cdot> ?\<sigma> k, ?s (Suc k) \<cdot> ?\<sigma> (Suc k)) \<in> ?qrstep^*"
      by (auto simp: ichain.simps)
    have tk_supt: "\<forall>i\<le>length (args (?t k)). i > 0 \<longrightarrow> ?t k \<cdot> ?\<sigma> k \<rhd> ?tk i"
    proof (intro impI allI)
      fix i assume i: "i \<le> length (args (?t k))"
        and i2: "i > 0"
      then show "?t k \<cdot> ?\<sigma> k \<rhd> ?tk i"
      proof (cases "?t k")
        case (Var x) with tuple and inP show ?thesis by auto
      next
        case (Fun f ss)
        from i2 obtain j where j2: "i = Suc j" by (cases i, auto)
        with i have j: "j < length (args (?t k))" by auto 
        from j have "?t k \<rhd> args (?t k) ! j" unfolding Fun
          using supt.arg[of "args (Fun f ss) ! j" "ss" f] by auto
        then show ?thesis using j2 supt_subst[to_set] by auto
      qed
    qed
    have sk_supt: "\<forall>i\<le>length (args (?s k)). i > 0 \<longrightarrow> ?s k \<cdot> ?\<sigma> k \<rhd> ?sk i"
    proof (intro impI allI)
      fix i assume i: "i \<le> length (args (?s k))"
        and i2: "i > 0" then show "?s k \<cdot> ?\<sigma> k \<rhd> ?sk i"
      proof (cases "?s k")
        case (Var x) with tuple and inP show ?thesis by auto
      next
        case (Fun f ss)
        from i2 obtain j where j2: "i = Suc j" by (cases i, auto)
        with i have j: "j < length (args (?s k))" by auto 
        from j have "?s k \<rhd> args (?s k) ! j" unfolding Fun
          using supt.arg[of "args (Fun f ss) ! j" "ss" f] by auto
        then show ?thesis using j2 supt_subst[to_set] by auto
      qed
    qed
    have SN_sk: "SN_on ?qrstep {?s k \<cdot> ?\<sigma> k}" using min_s by simp
    have SN_ski: "\<forall>i\<le>length (args (?s k)). SN_on ?qrstep {?sk i}"
    proof
      fix i
      show "i \<le> length(args(?s k)) \<longrightarrow> SN_on ?qrstep {?sk i}"
        using subterm_preserves_SN_gen[OF ctxt_closed_qrstep SN_sk] sk_supt SN_sk
        by (cases i) auto
    qed
    note chain = chain[unfolded min_ichain.simps ichain.simps minimal_cond_def]
    from inP tuple
      have validDP: "is_Fun (?t k) \<and> \<not> defined R (the (root (?t k)))"
      by auto
    from chain inP tuple have validDP1: "is_Fun (?s (Suc k))" by auto
    from chain have steps: "(?t k \<cdot> ?\<sigma> k, ?s(Suc k) \<cdot> ?\<sigma>(Suc k)) \<in> ?Rs" by auto
    {
      fix j1
      assume j1: "j1 \<le> length (args (?t k))"
      and sntk: "SN_on ?qrstep {?tk j1 }" 
      have "(?tk j1, ?sk1 j1) \<in> ?NS"
      proof (cases j1)
        case 0
        with steps show ?thesis unfolding restrict_SN_def using sntk by auto
      next
        case (Suc j)
        let ?tj = "args (?t k) ! j"
        let ?sj = "args (?s (Suc k)) ! j"
        from j1 Suc have j: "j < length (args (?t k))" by simp
        from validDP obtain f ts
          where tk: "?t k = Fun f ts \<and> \<not> defined R (f, length ts)" by (cases "?t k") auto
        from validDP1 obtain g ss
          where sk1: "?s (Suc k) = Fun g ss" by (cases "?s (Suc k)") auto
        let ?tss = "map (\<lambda>t. t \<cdot> ?\<sigma> k) ts"
        let ?sss = "map (\<lambda>s. s \<cdot> ?\<sigma> (Suc k)) ss"
        from tk have f: "\<not> defined R (f, length ?tss)" by simp
        from steps have "(Fun f ts \<cdot> ?\<sigma> k, Fun g ss \<cdot> ?\<sigma> (Suc k)) \<in> ?Rs" using tk sk1 by auto
        then have steps2: "(Fun f ?tss, Fun g ?sss) \<in> ?Rs" by auto
        from this no_left_vars f
          have "\<exists>us. length us = length ?tss
            \<and> Fun g ?sss = Fun f us
            \<and> (\<forall>i<length ?tss. (?tss ! i, us ! i) \<in> ?Rs)"
          by (rule nondef_root_imp_arg_qrsteps)
        from this obtain us
          where nearly: "length us = length ?tss
            \<and> Fun g ?sss = Fun f us
            \<and> (\<forall>i<length ?tss. (?tss ! i, us ! i) \<in> ?Rs)" ..
        from sntk have SN_tkj: "SN_on ?qrstep {?tj \<cdot> ?\<sigma> k}" using j1 Suc by auto
        from nearly j tk sk1 have "(?tj \<cdot> ?\<sigma> k, ?sj \<cdot> ?\<sigma> (Suc k)) \<in> ?Rs" by auto
        with SN_tkj have "(?tj \<cdot> ?\<sigma> k, ?sj \<cdot> ?\<sigma> (Suc k)) \<in> restrict_SN ?Rs ?qrstep"
          unfolding restrict_SN_def by simp
        then show ?thesis using Suc unfolding restrict_SN_def by auto
      qed
    } note stepsNS = this 
    have DG: "((?s k, ?t k), (?s (Suc k), ?t (Suc k))) \<in> DG nfs m P Q R"
      by (rule DG_I[OF inP inP' steps], insert chain, auto)
    from edg[OF this]
      have conn: "?conn (?entry k) (?entry (Suc k))" by auto
    let ?rd = remdups_sort
    from inP obtain stri nstri
      where graph: "Scg (?entry k) (?entry k) (?rd stri) (?rd nstri) \<in> set Gs
        \<and> (\<forall>(i, j)\<in>set stri.
          i \<le> length (args (?s k)) \<and> j \<le> length (args (?t k))
          \<and> get_arg (?s k) i \<rhd> get_arg (?t k) j)
        \<and> (\<forall>(i, j)\<in>set nstri.
          i \<le> length (args (?s k)) \<and> j \<le> length (args (?t k))
          \<and> get_arg (?s k) i \<unrhd> get_arg (?t k) j)" using graphs by force
    let ?g = "Scg (?entry k) (?entry k) (?rd stri) (?rd nstri)"
    from graph have gGs: "?g \<in> set Gs" ..
    let ?check = "\<lambda>g. ((?entry k, ?sk), (?entry (Suc k), ?sk1))
           \<in> sct_semantics.steps ?supt ?supteq ?conn g"
    {
      fix i j
      assume i: "i \<le> length(args(?s k))" and j: "j \<le> length(args(?t k))"
          and NS: "get_arg(?s k) i \<unrhd> get_arg (?t k) j"
      from m_or_inn have "SN_on ?qrstep {?tk j}"
      proof
        assume "NF_terms Q \<subseteq> NF_trs R"
        from min_s(2)[OF this] have NF: "?s k \<cdot> ?\<sigma> k \<in> NF_trs R" .
        from tuple inP have "is_Fun (?s k)" by auto
        with i have "?s k \<unrhd> get_arg(?s k) i" by (cases i, auto)
        with NS have "?s k \<unrhd> get_arg (?t k) j"
          by (metis subterm.dual_order.trans)
        then have subt: "?s k \<cdot> ?\<sigma> k \<unrhd> get_arg (?t k) j \<cdot> ?\<sigma> k" by auto
        show ?thesis
          by (rule NF_imp_SN_on[OF set_mp[OF NF_anti_mono NF_subterm[OF NF subt]]], auto)
      next
        assume m
        with chain have SN: "SN_on ?qrstep {?t k \<cdot> ?\<sigma> k}" by auto
        have subt: "?t k \<cdot> ?\<sigma> k \<unrhd> get_arg (?t k) j \<cdot> ?\<sigma> k " using j validDP by (cases j, cases "?t k", auto)
        show ?thesis by (rule ctxt_closed_SN_on_subt [OF ctxt_closed_qrstep SN subt])
      qed
    } note SN = this
    have "?check ?g"
    proof (simp add: sct_semantics.steps.simps sct_semantics conn[simplified], rule conjI)
      {
        fix i j
        assume ij: "(i, j) \<in> set nstri"
        with graph have i: "i \<le> length(args(?s k))" and j: "j \<le> length(args(?t k))"
          and NS: "get_arg(?s k) i \<unrhd> get_arg (?t k) j" by auto
        have astepsNS: "(?tk j, ?sk1 j) \<in> ?NS"
          by (rule stepsNS[OF j SN[OF i j NS]])
        from SN_ski and i have snski: "SN_on ?qrstep {?sk i}" by simp
        from NS subst_closed_supteq have "?sk i \<unrhd> ?tk j"
          unfolding subst.closed_def using subst.closure.intros by blast
        then have non_strict: "(?sk i, ?tk j) \<in> ?NS" using snski
          unfolding restrict_SN_def supteq_supt_conv by force
        from rtrancl_trans[OF non_strict astepsNS] have "(?sk i, ?sk1 j) \<in> ?NS" by auto
      }
      then show "\<forall>ij\<in>set nstri.(\<lambda>(i, j). (?sk i, ?sk1 j) \<in> ?NS) ij" by auto
    next
      {
        fix i j
        assume "(i, j) \<in> set stri"
        with graph have i: "i \<le> length (args(?s k))" and j: "j \<le> length(args(?t k))"
          and S: "get_arg(?s k) i \<rhd> get_arg(?t k) j" by auto
        have astepsNS: "(?tk j, ?sk1 j) \<in> ?NS" 
          by (rule stepsNS[OF j SN[OF i j]], insert S, auto)
        from SN_ski and i have snski: "SN_on ?qrstep {?sk i}" by simp
        from S subst_closed_supt have "?sk i \<rhd> ?tk j"
          unfolding subst.closed_def using subst.closure.intros by blast
        then have strict: "(?sk i, ?tk j) \<in> ?supt" using snski
          unfolding restrict_SN_def by force
        have "(?sk i, ?sk1 j) \<in> ?S" using strict astepsNS by auto
      }
      then show "\<forall>ij\<in>set stri.(\<lambda>(i, j). (?sk i, ?sk1 j) \<in> ?S) ij" by auto
    qed
    with gGs have "\<exists>g\<in>set Gs. ?check g" by blast
  }
  then have main: "?R \<subseteq> (\<Union>G\<in>set Gs. sct_semantics.steps ?supt ?supteq ?conn G)" by auto
  have "SN ?R"
    by (rule sct_semantics.SCT_correctness2[where S = ?supt and NS = ?supteq],rule sct_semantics,rule main,rule check)
  obtain f where "f = ?pairs" by auto
  then have id: "?R = {(f k, f (Suc k)) | k. True}" by auto
  have "\<not> SN ?R" unfolding SN_defs by (simp only: id, blast)
  with \<open>SN ?R\<close> show False by auto
qed

end
