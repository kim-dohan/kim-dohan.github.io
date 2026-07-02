(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory SCNP
imports
  Term_Order
  Knuth_Bendix_Order.Lexicographic_Extension
begin

fun proja :: "('f,'v)term \<Rightarrow> nat \<Rightarrow> ('f,'v)term"
  where "proja (Fun f ts) i = (if i < length ts then ts ! i else Fun f ts)"

definition lterms :: "(('f \<times> nat) \<Rightarrow> (nat \<times> nat)list) \<Rightarrow> ('f,'v)term \<Rightarrow> (('f,'v)term \<times> nat)list"
  where "lterms \<pi> \<equiv> \<lambda> t. case t of Fun f ts \<Rightarrow> map (\<lambda>(i,n). (proja (Fun f ts) i, n)) (\<pi> (f,length ts))"

locale scnp = redpair_order S NS + compat_pair S NS + list_order_extension s_ext ns_ext
  for S NS :: "('f,'v)trs" and 
      s_ext ns_ext :: "(('f,'v)term \<times> nat) list_ext" +
  fixes \<pi> :: "('f \<times> nat) \<Rightarrow> (nat \<times> nat)list"
begin

abbreviation gt :: "nat rel" where "gt \<equiv> {(a,b). a > b}"
abbreviation ge :: "nat rel" where "ge \<equiv> {(a,b). a \<ge> b}"

definition label_s :: "(('f, 'v) term \<times> nat) rel"
  where "label_s \<equiv> lex_two S NS gt"

definition label_ns :: "(('f, 'v) term \<times> nat) rel"
  where "label_ns \<equiv> lex_two S NS ge"

lemma trans_S_O: "S O S \<subseteq> S" using trans_S_point by auto
lemma trans_NS_O: "NS O NS \<subseteq> NS" using trans_NS_point by auto

lemmas trans_compat = compat_NS_S compat_S_NS trans_S_O trans_NS_O

lemma label_s_ns_order_pair: "SN_order_pair label_s label_ns"
proof(unfold_locales)
  {
    fix s t u
    assume st: "(s,t) \<in> label_s" and tu: "(t,u) \<in> label_s" 
    from st[unfolded label_s_def] have st: "(s,t) \<in> lex_two S NS gt" .
    from tu[unfolded label_s_def] have tu: "(t,u) \<in> lex_two S NS gt" by blast
    have "(s,u) \<in> lex_two S NS gt"
      by (rule lex_two_compat[of NS S gt gt, OF trans_compat _ st tu], auto)
    then have "(s,u) \<in> label_s" unfolding label_s_def by blast
  }
  then show "trans label_s" unfolding trans_def by blast
next
  {
    fix s t u
    assume st: "(s,t) \<in> label_ns" and tu: "(t,u) \<in> label_ns" 
    from st[unfolded label_ns_def] have st: "(s,t) \<in> lex_two S NS ge" .
    from tu[unfolded label_ns_def] have tu: "(t,u) \<in> lex_two S NS ge" .
    have "(s,u) \<in> lex_two S NS ge" 
      by (rule lex_two_compat[of NS S ge ge, OF trans_compat _ st tu], auto)
    then have "(s,u) \<in> label_ns" unfolding label_ns_def by blast
  }
  then show "trans label_ns" unfolding trans_def by blast
next
  {
    fix s t u
    assume st: "(s,t) \<in> label_ns" and tu: "(t,u) \<in> label_s" 
    from st[unfolded label_ns_def] have st: "(s,t) \<in> lex_two S NS ge" .
    from tu[unfolded label_s_def] have tu: "(t,u) \<in> lex_two S NS gt" .
    have "(s,u) \<in> lex_two S NS gt" 
      by (rule lex_two_compat[of NS S ge gt, OF trans_compat _ st tu], auto)
    then have "(s,u) \<in> label_s" unfolding label_s_def by blast
  }
  then show "label_ns O label_s \<subseteq> label_s" by blast
next
  {
    fix s t u
    assume st: "(s,t) \<in> label_s" and tu: "(t,u) \<in> label_ns" 
    from st[unfolded label_s_def] have st: "(s,t) \<in> lex_two S NS gt" .
    from tu[unfolded label_ns_def] have tu: "(t,u) \<in> lex_two S NS ge" .
    have "(s,u) \<in> lex_two S NS gt" 
      by (rule lex_two_compat'[of NS S gt ge, OF trans_compat _ st tu], auto)
    then have "(s,u) \<in> label_s" unfolding label_s_def by blast
  }
  then show "label_s O label_ns \<subseteq> label_s" by blast
next
  show "SN label_s" unfolding label_s_def
    by (rule lex_two[OF compat_NS_S], insert SN SN_nat_gt, auto)
next
  show "refl label_ns" unfolding refl_on_def label_ns_def using refl_NS 
    unfolding refl_on_def by auto
qed

definition NST_label_mul :: "('f,'v)trs" where
  "NST_label_mul \<equiv> {(Fun f ts, Fun g ss) | f g ts ss. (lterms \<pi> (Fun f ts), lterms \<pi> (Fun g ss)) \<in> ns_ext label_s label_ns}"

definition S_label_mul :: "('f,'v)trs" where
  "S_label_mul \<equiv> {(Fun f ts, Fun g ss) | f g ts ss. (lterms \<pi> (Fun f ts), lterms \<pi> (Fun g ss)) \<in> s_ext label_s label_ns}"

lemma scnp_mul: "root_redtriple_order S_label_mul NS NST_label_mul \<and> S_label_mul O NST_label_mul \<subseteq> S_label_mul" 
  (is "root_redtriple_order ?S _ ?NST \<and> _ ")
proof -
  note S = S_label_mul_def
  note NST = NST_label_mul_def
  let ?ml = "\<lambda> f ts. lterms \<pi> (Fun f ts)"
  let ?S' = "s_ext label_s label_ns"
  let ?NS' = "ns_ext label_s label_ns"
  from subst_S[unfolded subst.closed_def] 
  have subS: "\<And> \<sigma> s t. (s,t) \<in> S \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> S" by auto
  from subst_NS[unfolded subst.closed_def] 
  have subNS: "\<And> \<sigma> s t. (s,t) \<in> NS \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> NS" by auto
  let ?\<sigma> = "(\<lambda> (\<sigma> :: ('f,'v)subst) s. s \<cdot> \<sigma>)"
  let ?\<sigma>n = "(\<lambda> \<sigma> (t,n). (?\<sigma> \<sigma> t, n)) :: ('f,'v)subst \<Rightarrow> ('f,'v)term \<times> nat \<Rightarrow> ('f,'v)term \<times> nat"
  {
    fix f ss \<sigma>
    have "?ml f (map (?\<sigma> \<sigma>) ss) = map (?\<sigma>n \<sigma>) (?ml f ss)"
      unfolding lterms_def term.simps map_map o_def length_map 
      unfolding map_eq_conv
      by (clarify, rule conjI[OF _ refl], auto)     
  } note idsub = this
  interpret list: SN_order_pair ?S' ?NS'
    by (rule extension[OF label_s_ns_order_pair])
  show ?thesis
  proof (intro conjI, unfold_locales)
    show "ctxt.closed NS" by (rule ctxt_NS)
    show "subst.closed NS" by (rule subst_NS)
    show "refl NS" by (rule refl_NS)
    show "trans NS" by (rule trans_NS)
    show "SN S_label_mul" unfolding S
      by (rule SN_subset[OF SN_inv_image[OF list.SN]], auto)
    show "trans S_label_mul" unfolding S using list.trans_S unfolding trans_def
      by blast
    show "trans NST_label_mul" unfolding NST using list.trans_NS unfolding trans_def by blast
    show "?NST O ?S \<subseteq> ?S" unfolding S NST using list.compat_NS_S by blast
    show "?S O ?NST \<subseteq> ?S" unfolding S NST using list.compat_S_NS by blast
  next
    show "top_mono NS NST_label_mul" unfolding top_mono_def
    proof (intro allI impI)
      fix s t f bef aft u
      assume st: "(s,t) \<in> NS" 
      let ?ts = "bef @ t # aft"
      let ?t = "Fun f ?ts"
      let ?ss = "bef @ s # aft"
      let ?s = "Fun f ?ss"
      obtain n where n: "n = Suc (length bef + length aft)" by auto
      let ?pt = "proja (Fun f (bef @ t # aft))"
      let ?ps = "proja (Fun f (bef @ s # aft))"
      let ?ts' = "map (\<lambda> (i,y). (?pt i, y)) (\<pi> (f,n))"   
      let ?ss' = "map (\<lambda> (i,y). (?ps i, y)) (\<pi> (f,n))"   
      have "(?ss', ?ts') \<in> ?NS'" 
      proof (rule all_ns_imp_ns, simp)
        fix i
        assume i': "i < length ?ts'"
        then have i: "i < length (\<pi> (f,n))" by auto
        then obtain j m where pi: "\<pi> (f,n) ! i = (j,m)" by force
        show "(?ss' ! i, ?ts' ! i) \<in> label_ns" unfolding nth_map[OF i] pi prod.simps 
        proof (cases "j = length bef")
          case True
          then show "((?ps j, m), (?pt j, m)) \<in> label_ns" using st unfolding label_ns_def by auto
        next
          case False 
          then have id: "?ss ! j = ?ts ! j" unfolding nth_append by auto
          show "((?ps j, m), (?pt j, m)) \<in> label_ns"
          proof (cases "j < Suc (length bef + length aft)")
            case True
            then show ?thesis using id refl_NS unfolding label_ns_def refl_on_def by auto
          next
            case False
            then show ?thesis
              using ctxt_closed_one[OF ctxt_NS st, of f bef aft]
              unfolding label_ns_def by auto
          qed
        qed
      qed
      then have S': "(?ml f ?ss, ?ml f ?ts) \<in> ?NS'" unfolding n lterms_def term.simps by auto
      then show "(Fun f ?ss, Fun f ?ts) \<in> ?NST" unfolding NST by auto
    qed
  next
    show "subst.closed ?S" unfolding subst.closed_def  
    proof 
      fix ss ts
      assume "(ss,ts) \<in> subst.closure ?S"
      then show "(ss,ts) \<in> ?S"
      proof (induct)
        fix s t and \<sigma> :: "('f,'v)subst"
        assume mem: "(s,t) \<in> ?S" 
        from mem obtain f ss  where s: "s = Fun f ss" unfolding S by auto
        from mem obtain g ts  where t: "t = Fun g ts" unfolding S by auto
        from mem[unfolded s t S] have S': "(?ml f ss,?ml g ts) \<in> ?S'" by simp
        show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?S" unfolding s t S
          by (rule, intro exI conjI, unfold eval_term.simps, rule refl,
            unfold idsub, rule s_map[OF _ _ S'],
            unfold label_s_def label_ns_def, insert subS subNS, auto)
      qed
    qed
  next
    show "subst.closed ?NST" unfolding subst.closed_def  
    proof 
      fix ss ts
      assume "(ss,ts) \<in> subst.closure ?NST"
      then show "(ss,ts) \<in> ?NST"
      proof (induct)
        fix s t and \<sigma> :: "('f,'v)subst"
        assume mem: "(s,t) \<in> ?NST" 
        from mem obtain f ss  where s: "s = Fun f ss" unfolding NST by auto
        from mem obtain g ts  where t: "t = Fun g ts" unfolding NST by auto
        from mem[unfolded s t NST] have S': "(?ml f ss,?ml g ts) \<in> ?NS'" by simp
        show "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> ?NST" unfolding s t NST
          by (rule, intro exI conjI, unfold eval_term.simps, rule refl,
            unfold idsub, rule ns_map[OF _ _ S'],
            unfold label_s_def label_ns_def, insert subS subNS, auto)
      qed
    qed
  qed
qed
end

definition scnp_af_to_af :: "(('f \<times> nat) \<Rightarrow> (nat \<times> nat)list) \<Rightarrow> 'f af \<Rightarrow> 'f af" where
  "scnp_af_to_af \<pi> \<pi>' \<equiv> \<lambda>(f, n).
    let is = map fst (\<pi> (f, n)) in 
    if (\<exists>i\<in>set is. i \<ge> n)
      then \<pi>' (f, n) \<union> set is
      else set is"

locale af_scnp = scnp S NS s_ext ns_ext \<pi> + af_redpair S NS \<pi>'
  for S NS :: "('f, 'v) trs" and \<pi> and s_ext ns_ext and \<pi>' 
begin
lemma af_scnp_mul: "af_root_redtriple_order S_label_mul NS NST_label_mul \<pi>' (scnp_af_to_af \<pi> \<pi>')" 
  (is "af_root_redtriple_order ?S _ ?NST _ ?pi")
proof -
  from scnp_mul interpret root_redtriple_order S_label_mul NS NST_label_mul by blast
  show ?thesis 
  proof (unfold_locales, rule af_compat)
    show "af_compatible ?pi ?NST"
      unfolding af_compatible_def 
    proof (intro allI)
      fix f bef s t aft
      show "length bef \<in> ?pi (f, Suc (length bef + length aft)) \<or>
        (Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ?NST" (is "?i \<in> (scnp_af_to_af \<pi> \<pi>') (f, ?n) \<or> (?s,?t) \<in> ?NST")
      proof -
        {
          assume not: "?i \<notin> ?pi (f, ?n)"
          let ?ss = "bef @ s # aft"
          let ?ts = "bef @ t # aft"
          note not = not[unfolded scnp_af_to_af_def Let_def, unfolded Product_Type.split]
          have "(?s,?t) \<in> ?NST" unfolding NST_label_mul_def
          proof (rule, intro exI conjI, rule refl, rule all_ns_imp_ns)
            show "length (lterms \<pi> ?s) = length (lterms \<pi> ?t)" unfolding lterms_def by auto
          next
            fix i
            assume i: "i < length (lterms \<pi> ?t)"
            then have i: "i < length (\<pi> (f,?n))" unfolding lterms_def by auto
            obtain a b where pi: "\<pi> (f, ?n) ! i = (a,b)" by force
            have id: "(lterms \<pi> ?s ! i, lterms \<pi> ?t ! i) = ((proja ?s a,b), (proja ?t a, b))" (is "_ = ((?ps,b),(?pt,b))")
              unfolding lterms_def term.simps using i pi by auto
            from pi i have mem: "(a,b) \<in> set (\<pi> (f,?n))" unfolding set_conv_nth by force
            then have mem': "a \<in> set (map fst (\<pi> (f,?n)))" by force
            let ?cond = "Bex (set (map fst (\<pi> (f, ?n))))  ((\<le>) ?n)" 
            have "(?ps, ?pt) \<in> NS" 
            proof (cases "a < ?n")
              case True
              have "a \<noteq> ?i"
              proof (cases ?cond)
                case True
                then have c: "?cond = True" by simp
                from not[unfolded c] mem' show ?thesis by force
              next
                case False
                then have c: "?cond = False" by simp
                from not[unfolded c] mem' show ?thesis by force
              qed
              with True have "?ps = ?pt" by (simp add: nth_append)
              then show ?thesis using refl_NS unfolding refl_on_def by auto
            next
              case False
              then have a: "a \<ge> ?n" by simp
              with mem' have c: "?cond = True" by auto
              from a have id: "?ps = ?s" "?pt = ?t" by auto
              from not[unfolded c] have not: "?i \<notin> \<pi>' (f, ?n)" by auto
              show ?thesis unfolding id
              proof (rule af_steps_imp_orient[where p = "\<lambda> i. i \<in> \<pi>' (f, ?n)", OF trans_NS refl_NS ctxt_NS, rule_format])
                fix i
                assume "i < length ?ss" and "i \<in> \<pi>' (f, ?n)"
                with not have "i \<noteq> ?i" by auto
                then have "?ss ! i = ?ts ! i" unfolding nth_append by auto
                then show "(?ss ! i, ?ts ! i) \<in> NS" using refl_NS[unfolded refl_on_def] by auto
              qed (insert af_compat[unfolded af_compatible_def], auto)
            qed
            then show "(lterms \<pi> ?s ! i, lterms \<pi> ?t ! i) \<in> label_ns" unfolding id label_ns_def by auto
          qed
        }
        then show ?thesis by blast
      qed
    qed
  qed
qed
end
end
