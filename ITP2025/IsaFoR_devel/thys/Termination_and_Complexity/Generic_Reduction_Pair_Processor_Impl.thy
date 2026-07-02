(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generic_Reduction_Pair_Processor_Impl
  imports
    Generic_Usable_Rules_Impl
    Innermost_Usable_Rules_Impl
    Reduction_Pair_Proc_Impl
    Generic_Reduction_Pair_Processor
begin

definition
  generic_ur_af_redtriple_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> 
     ('f,string)rules option \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "generic_ur_af_redtriple_proc I rp U_opt Premove dpp = check_return (do {
     rel_impl_redtriple rp;
     let (ps, pns) = dpp_ops.split_pairs I dpp Premove;
     let P = dpp_ops.pairs I dpp;
     U \<leftarrow> smart_usable_rules_checker_impl I dpp (isOK(rel_impl.ce_compat rp)) (rel_impl.af rp) U_opt P;
     rel_impl_ns rp U
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting (usable) rules\<newline>'') \<circ> s);
     rel_impl_nst rp pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the generic reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs I dpp Premove)"

lemma generic_ur_af_redtriple_proc:
  assumes I: "dpp_spec I"
  and rp: "rel_impl rp"
  shows "dpp_spec.sound_proc_impl I (generic_ur_af_redtriple_proc I rp U_opt ps)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume fin: "finite_dpp (dpp d')"
      and ok: "generic_ur_af_redtriple_proc I rp U_opt ps d = return d'"
    let ?S = "set ps"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Pb = "set (pairs d)"
    let ?PP = "?P \<union> ?Pw"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "set (rules d)"
    let ?RR = "set (R d @ Rw d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?wwf = "wwf_qtrs ?Q ?Rb"
    have RR_conv: "?RR = ?Rb" unfolding dpp_spec_sound by auto
    have PP_conv: "?PP = ?Pb" unfolding dpp_spec_sound by auto
    show "finite_dpp (dpp d)"
    proof (cases "split_pairs d ps")
      case (Pair Ps Pr)    
      from split_pairs_sound[OF this] have Ps: "set Ps = (?P \<union> ?Pw) \<inter> ?S" 
        and Pr: "set Pr = (?P \<union> ?Pw) - ?S" by auto
      let ?pi = "rel_impl.af rp"
      let ?ce = "rel_impl.ce_compat rp" 
      let ?urcheck = "smart_usable_rules_checker_impl I d (isOK ?ce) ?pi U_opt (pairs d)" 
      note ok = ok[unfolded generic_ur_af_redtriple_proc_def Let_def Pair, simplified]
      from ok have valid: "isOK(rel_impl_redtriple rp)" 
        and compat: "isOK(?urcheck)" by auto 
      from compat obtain U where urc: "?urcheck = return U" by (cases ?urcheck, auto) 
      note ok = ok[unfolded urc]
      from ok have
            NS: "isOK (rel_impl_ns rp U)"
        and NST: "isOK (rel_impl_nst rp Pr)"
        and S: "isOK(rel_impl_s rp Ps)" 
        and d': "d' = delete_pairs d ps" by (auto simp: rel_impl_list)
      from rel_impl_redtriple[OF rp valid S NS NST]
      obtain S NS NST where "af_redtriple_order S NS NST ?pi" 
        and ce: "isOK ?ce \<Longrightarrow> ce_compatible NS" 
        and orient: "set Ps \<subseteq> S" "set U \<subseteq> NS" "set Pr \<subseteq> NST" by auto
      from orient have S: "(?P \<union> ?Pw) \<inter> ?S \<subseteq> S" and NS: "?P \<union> ?Pw - ?S \<subseteq> NST" and R: "set U \<subseteq> NS" by (auto simp: Pr Ps)
      then have NS: "?P \<union> ?Pw \<subseteq> NST \<union> S" by auto
      from smart_usable_rules_checker_impl[OF I urc] have ur: "smart_usable_rules_checker ?nfs ?m (isOK ?ce) ?wwf ?pi ?Q (rules d) U_opt ?PP = Some U" by auto
      interpret af_redtriple_order S NS NST ?pi by fact
      have rt: "af_redtriple S NS NST ?pi" ..
      note proc = generic_redtriple_proc[OF smart_usable_rules_checker R NS rt ce, OF _ ur]
      have *: "\<And>P Q. (P \<Longrightarrow> Q) \<Longrightarrow> \<not> Q \<Longrightarrow> \<not> P" by blast
      show ?thesis
        unfolding finite_dpp_def
      proof(rule, elim exE) 
        fix s t \<sigma>
        assume min: "min_ichain (dpp d) s t \<sigma>"
        have "\<exists> i. min_ichain (?nfs,?m,?P - ?S,?Pw - ?S,?Q,?R,?Rw) (shift s i) (shift t i) (shift \<sigma> i)"
          by (rule min_ichain_split[OF min[unfolded dpp_sound], of ?S "{}", unfolded Int_empty_left Diff_empty],
            rule * [OF _ proc[of s t \<sigma>, unfolded dpp_spec_sound]], rule min_ichain_mono[of ?nfs ?m "?S \<inter> ?PP" "?PP - ?S" ?Q "{}" "?R \<union> ?Rw"], insert S, auto 
            )
        with fin[unfolded d' delete_P_Pw_sound finite_dpp_def] show False by blast
      qed
    qed
  qed
qed

definition root_aft_to_entry where
  "root_aft_to_entry s t \<pi> \<equiv> let rt = the (root t); \<pi>t = \<pi> rt; ts = args t
        in map (\<lambda> i. (s, ts ! i)) (filter (\<lambda> i. i \<in> \<pi>t) [0 ..< snd rt])"

definition
  generic_ur_af_root_redtriple_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> 
     ('f,string)rules option \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "generic_ur_af_root_redtriple_proc I rp U_opt Premove dpp = check_return (do {
     rel_impl_root_redtriple rp;
     let (ps, pns) = dpp_ops.split_pairs I dpp Premove;
     let P = dpp_ops.pairs I dpp;
     let pi = rel_impl.af rp;
     let pi' = rel_impl.top_af rp;
     let is_def = dpp_spec.is_defined I dpp;
     check_allm (\<lambda>(l, r). do {
        check_no_var l;
        check_no_var r;
        check_no_defined_root is_def r
      }) P;
     check_allm (\<lambda>(l, r). do {
        check_no_var l
      }) (dpp_ops.rules I dpp);
     U \<leftarrow> smart_usable_rules_checker_impl I dpp (isOK (rel_impl.ce_compat rp)) pi U_opt (concat (map (\<lambda> (s,t). root_aft_to_entry s t pi') P));
     rel_impl_ns rp U
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting (usable) rules\<newline>'') \<circ> s);
     rel_impl_nst rp pns
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s);
     rel_impl_s rp ps
       <+? (\<lambda>s. showsl_lit (STR ''problem when orienting DPs\<newline>'') \<circ> s)
   } <+? (\<lambda>s. showsl_lit (STR ''could not apply the generic root reduction pair processor with the following\<newline>'') \<circ>
     (rel_impl.desc rp) \<circ> showsl_nl \<circ> s))
   (dpp_spec.delete_pairs I dpp Premove)"

lemma generic_ur_af_root_redtriple_proc:
  assumes I: "dpp_spec I"
  and rp: "rel_impl rp"
  shows "dpp_spec.sound_proc_impl I (generic_ur_af_root_redtriple_proc I rp U_opt ps)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume fin: "finite_dpp (dpp d')"
      and ok: "generic_ur_af_root_redtriple_proc I rp U_opt ps d = return d'"
    let ?S = "set ps"
    let ?P = "set (P d)"
    let ?Pw = "set (Pw d)"
    let ?Pb = "set (pairs d)"
    let ?PP = "?P \<union> ?Pw"
    let ?Q = "set (Q d)"
    let ?R = "set (R d)"
    let ?Rw = "set (Rw d)"
    let ?Rb = "set (rules d)"
    let ?RR = "set (R d @ Rw d)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?wwf = "wwf_qtrs ?Q ?Rb"
    have RR_conv: "?RR = ?Rb" unfolding dpp_spec_sound by auto
    have PP_conv: "?PP = ?Pb" unfolding dpp_spec_sound by auto
    show "finite_dpp (dpp d)"
    proof (cases "split_pairs d ps")
      case (Pair Ps Pr)    
      from split_pairs_sound[OF this] have Ps: "set Ps = (?P \<union> ?Pw) \<inter> ?S" 
        and Pr: "set Pr = (?P \<union> ?Pw) - ?S" by auto
      let ?pi = "rel_impl.af rp"
      let ?pi' = "rel_impl.top_af rp"
      let ?P' = "concat (map (\<lambda> (s,t). root_aft_to_entry s t ?pi') (pairs d))"
      let ?R = "rules d"
      let ?ce = "isOK (rel_impl.ce_compat rp)" 
      let ?urcheck = "smart_usable_rules_checker_impl I d ?ce ?pi U_opt ?P'" 
      note ok = ok[unfolded generic_ur_af_root_redtriple_proc_def Let_def Pair, simplified]
      from ok have valid: "isOK(rel_impl_root_redtriple rp)" 
        and compat: "isOK(?urcheck)" by auto 
      from compat obtain U where urc: "?urcheck = return U" by (cases ?urcheck, auto) 
      note ok = ok[unfolded urc]
      from ok have
            NS: "isOK (rel_impl_ns rp U)"
        and NST: "isOK (rel_impl_nst rp  Pr)"
        and S: "isOK(rel_impl_s rp Ps)" 
        and d': "d' = delete_pairs d ps" 
        and Pcond: "\<And> s t. (s,t) \<in> ?P \<union> ?Pw \<Longrightarrow> is_Fun s \<and> is_Fun t" 
        and Rcond: "\<And> l r. (l,r) \<in> ?Rb \<Longrightarrow> is_Fun l"
        and ndef: "\<forall> (s,t) \<in> ?P \<union> ?Pw. \<not> defined (set ?R) (the (root t))" by auto
      from rel_impl_root_redtriple[OF rp valid S NS NST]
      obtain S NS NST where rt: "af_root_redtriple_order S NS NST ?pi ?pi'" 
        and orient: "set Ps \<subseteq> S" "set Pr \<subseteq> NST" 
        and R: "set U \<subseteq> NS"
        and ce: "?ce \<Longrightarrow> ce_compatible NS" by blast
      from orient have NST: "?P \<union> ?Pw - ?S \<subseteq> NST" by (auto simp: Pr)
      from orient have S: "(?P \<union> ?Pw) \<inter> ?S \<subseteq> S" by (auto simp: Pr Ps)
      from NST S have NS: "?P \<union> ?Pw \<subseteq> NST \<union> S" by auto
      from smart_usable_rules_checker_impl[OF I urc] have ur: "smart_usable_rules_checker ?nfs ?m ?ce ?wwf ?pi ?Q (rules d) U_opt (set ?P') = Some U" by auto
      note proc = root_redtriple_sound[OF smart_usable_rules_checker _ R NS Pcond Rcond ndef rt ce, of ?nfs ?m ?ce ?Q U_opt] 
      let ?PP = "?P \<union> ?Pw"
      have no_chain: "\<And> s t \<sigma>. \<not> min_ichain (?nfs,?m,S \<inter> ?PP, ?PP - S, ?Q, {}, set ?R) s t \<sigma>"
      proof (rule proc, unfold ur[symmetric], rule arg_cong[where f = "smart_usable_rules_checker ?nfs ?m ?ce ?wwf ?pi ?Q (rules d) U_opt"])
        show "{u. \<exists> s f ts i. u = (s, ts ! i) \<and> (s,Fun f ts) \<in> ?P \<union> ?Pw \<and> i < length ts \<and> i \<in> ?pi' (f,length ts)} = set ?P'"
          (is "?one = ?two")
        proof -
          {
            fix s f ts i
            assume "(s,Fun f ts) \<in> ?P \<union> ?Pw \<and> i < length ts \<and> i \<in> ?pi' (f,length ts)"
            then have "(s, ts ! i) \<in> ?two" unfolding root_aft_to_entry_def Let_def unfolding pairs_sound[symmetric] by force
          }
          then have one: "?one \<subseteq> ?two" by blast
          {
            fix s ti
            assume "(s,ti) \<in> ?two"
            then obtain s' t' where st': "(s',t') \<in> set (pairs d)" 
              and mem: "(s,ti) \<in> set (root_aft_to_entry s' t' ?pi')" by auto
            from Pcond[of s' t'] st' obtain f ts where t': "t' = Fun f ts" by (cases t', auto)
            from mem[unfolded t' root_aft_to_entry_def Let_def, simplified]
            obtain i where ti: "ti = ts ! i" and i: "i < length ts" and pi: "i \<in> ?pi' (f,length ts)" and s: "s = s'"
              by auto
            have "(s,ti) \<in> ?one" unfolding ti s
              by (rule, intro exI conjI, rule refl, insert st' pi i t', auto)
          }
          then have two: "?two \<subseteq> ?one" ..
          from one two show ?thesis by blast
        qed
      qed
      have *: "\<And>P Q. (P \<Longrightarrow> Q) \<Longrightarrow> \<not> Q \<Longrightarrow> \<not> P" by blast
      show ?thesis
        unfolding finite_dpp_def
      proof(rule, elim exE) 
        fix s t \<sigma>
        assume min: "min_ichain (dpp d) s t \<sigma>"
        have "\<exists> i. min_ichain (?nfs,?m,?P - ?S,?Pw - ?S,?Q,set (R d),set (Rw d)) (shift s i) (shift t i) (shift \<sigma> i)" 
          by (rule min_ichain_split[OF min[unfolded dpp_sound], of ?S "{}", unfolded Int_empty_left Diff_empty],
          rule * [OF _ no_chain[of s t \<sigma>]], rule min_ichain_mono[of ?nfs ?m "?S \<inter> ?PP" "?PP - ?S" ?Q "{}" "set ?R"], 
            insert S, auto)              
        with fin[unfolded d' delete_P_Pw_sound finite_dpp_def] show False by blast
      qed
    qed
  qed
qed

definition
  generic_mono_ur_redpair_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f::{showl, compare_order}, string) rel_impl \<Rightarrow> 
     ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> ('f,string)rules \<Rightarrow> 'dpp proc"
where
  "generic_mono_ur_redpair_proc I rp Premove Rremove ur dpp = 
     (if dpp_ops.NFQ_subset_NF_rules I dpp then  
       mono_inn_usable_rules_ce_proc I rp Premove Rremove ur dpp
   else (do {
     check (dpp_ops.minimal I dpp) (showsl_lit (STR ''minimality or innermost required for mon. red. pair proc. with usable rules''));
     mono_ur_redpair_proc I rp Premove Rremove ur dpp
   }))"


lemma generic_mono_ur_redpair_proc:
  assumes I: "dpp_spec I" 
  and rp: "rel_impl rp"
  shows "dpp_spec.sound_proc_impl I (generic_mono_ur_redpair_proc I rp ps rs ur)"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume fin: "finite_dpp (dpp d')"
      and ok: "generic_mono_ur_redpair_proc I rp ps rs ur d = return d'"
    note ok = ok[unfolded generic_mono_ur_redpair_proc_def]
    show "finite_dpp (dpp d)"
    proof (cases "NFQ_subset_NF_rules d")
      case False
      with ok have "mono_ur_redpair_proc I rp ps rs ur d = return d'" 
        by auto
      with mono_ur_redpair_proc[OF rp, of ps rs ur] fin show ?thesis 
        unfolding sound_proc_impl_def by auto
    next
      case True
      with ok have "mono_inn_usable_rules_ce_proc I rp ps rs ur d = return d'" by auto
      with mono_inn_usable_rules_ce_proc[OF I rp, of ps rs ur] fin show ?thesis
        unfolding sound_proc_impl_def by auto
    qed
  qed
qed

end
