(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Uncurry_Impl
imports
  Uncurry
  Sem_Lab.Labelings_Impl
  Framework.QDP_Framework_Impl
  TRS.Tcap_Impl
  Show.Shows_Literal
begin

definition
  eta_closed_rules ::
    "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "eta_closed_rules a sm R R' \<equiv> check_allm (\<lambda>(l, r). 
    case aarity_term a sm l of 
      Some (Suc aa) \<Rightarrow> check (\<exists>(lll, rrr)\<in>set R'.
        case (lll,rrr) of
          (Fun f [ll, Var x], Fun g [rr, Var y]) \<Rightarrow>
             f = a \<and> g = a \<and> x = y \<and> x \<notin> set (vars_rule_impl (ll, rr)) \<and>
             instance_rule (l, r) (ll, rr)
        | _ \<Rightarrow> False)
    (showsl_lit (STR ''eta expansion of '') \<circ> showsl_rule (l, r) \<circ> showsl_lit (STR '' missing'')) 
    | _ \<Rightarrow> succeed) R"


lemma eta_closed_rules:
  "isOK (eta_closed_rules a sm R R') = eta_closed a sm (set R) (set R')"
proof -
  let ?Q = "\<lambda>l r. (\<lambda> (lll,rrr). case (lll,rrr) of (Fun f [ll, Var x],Fun g [rr, Var y]) \<Rightarrow> f = a \<and> g = a \<and> x = y \<and> x \<notin> set (vars_rule_impl (ll,rr)) \<and> instance_rule (l,r) (ll,rr) | _ \<Rightarrow> False)"
  show ?thesis
  proof
    assume ok: "isOK (eta_closed_rules a sm R R')"
    show "eta_closed a sm (set R) (set R')"
      unfolding eta_closed_def
    proof (intro allI impI)
      fix l r aa
      assume lr: "(l,r) \<in> set R" and "aarity_term a sm l = Some aa" and "0 < aa"
      then obtain aa where aa: "aarity_term a sm l = Some (Suc aa)" by (cases aa, auto)
      let ?P = "?Q l r"
      from ok[unfolded eta_closed_rules_def, simplified, THEN bspec[OF _ lr], simplified, unfolded aa, simplified]
      obtain lll rrr where lllrrr: "(lll,rrr) \<in> set R'" and P: "?P (lll,rrr)" by auto
      from P obtain f ls where lll: "lll = Fun f ls" by (cases lll, auto)
      from P[unfolded lll] obtain ll ls where lll: "lll = Fun f (ll # ls)" unfolding lll by (cases ls, auto)
      from P[unfolded lll] obtain lt ls where lll: "lll = Fun f (ll # lt # ls)" unfolding lll by (cases ls, auto)
      from P[unfolded lll] obtain x where lll: "lll = Fun f (ll # Var x # ls)" unfolding lll by (cases lt, auto)  
      from P[unfolded lll] have lll: "lll = Fun f [ll, Var x]" unfolding lll by (cases ls, auto)  
      note P = P[unfolded lll]
      from P obtain g ls where rrr: "rrr = Fun g ls" by (cases rrr, auto)
      from P[unfolded rrr] obtain rr ls where rrr: "rrr = Fun g (rr # ls)" unfolding rrr by (cases ls, auto)
      from P[unfolded rrr] obtain lt ls where rrr: "rrr = Fun g (rr # lt # ls)" unfolding rrr by (cases ls, auto)
      from P[unfolded rrr] obtain y where rrr: "rrr = Fun g (rr # Var y # ls)" unfolding rrr by (cases lt, auto)  
      from P[unfolded rrr] have rrr: "rrr = Fun g [rr, Var y]" unfolding rrr by (cases ls, auto)
      from P[unfolded rrr] lll rrr have lll: "lll = Fun a [ll, Var x]" and rrr: "rrr = Fun a [rr, Var x]" and x: "x \<notin> set (vars_rule_impl (ll,rr))" and inst: "instance_rule (l,r) (ll,rr)" by auto
      show "\<exists> ll rr y. instance_rule (l,r) (ll,rr) \<and> y \<notin> vars_rule (ll,rr) \<and> (Fun a [ll,Var y], Fun a [rr, Var y]) \<in> set R'"
        by (rule exI[of _ ll], rule exI[of _ rr], rule exI[of _ x], intro conjI, rule inst, rule x[unfolded set_vars_rule_impl],
          rule lllrrr[unfolded lll rrr])
    qed
  next
    assume eta: "eta_closed a sm (set R) (set R')"
    show "isOK (eta_closed_rules a sm R R')"
      unfolding eta_closed_rules_def isOK_check_allm
    proof (intro ballI)
      fix lr
      assume mem: "lr \<in> set R"
      obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
      let ?P = "?Q l r"
      let ?R = " (\<lambda>(l, r). 
        case aarity_term a sm l of 
          Some (Suc aa) \<Rightarrow> check (\<exists>rule\<in>set R'. ?Q l r rule)
        (showsl_lit (STR ''eta expansion of '') \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '' missing''))
        | _ \<Rightarrow> succeed)"
      show "isOK (?R lr)"
      proof (cases "aarity_term a sm l")
        case None
        then show ?thesis unfolding lr by auto
      next
        case (Some aa)
        show ?thesis
        proof (cases aa)
          case 0
          then show ?thesis using Some unfolding lr by auto
        next
          case (Suc aa)
          from eta[unfolded eta_closed_def, THEN spec, of l, THEN spec, of r, THEN spec, THEN mp[OF _ mem[unfolded lr]], THEN mp[OF _ Some],
          THEN mp, unfolded Suc]
          obtain ll rr y where inst: "instance_rule (l,r) (ll,rr)" and y:"y \<notin> vars_rule (ll,rr)" 
            and mem: "(Fun a [ll, Var y], Fun a [rr, Var y]) \<in> set R'" (is "?lr \<in> set R'")
            by auto
          have "(?Q l r) ?lr"
            unfolding set_vars_rule_impl
            by (simp add: y inst mem)
          with mem have "\<exists>rule\<in>set R'. ?Q l r rule" by blast
          then show ?thesis using Some Suc unfolding lr by auto
        qed
      qed
    qed
  qed
qed

definition
  eta_closed_top_rules ::
    "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "eta_closed_top_rules a n sm R P \<equiv> check_allm (\<lambda>(l, r). 
    case l of 
      Fun ff ls \<Rightarrow> check (aarity sm ff (length ls) = 0 \<or> (\<exists>(lll, rrr)\<in>set P.
        case (lll, rrr) of
          (Fun f (ll # yy), Fun g (rr # zz)) \<Rightarrow>
            f = a \<and> g = a \<and> zz = yy \<and> length yy = n - 1 \<and> distinct yy \<and>
            (\<forall>y\<in>set yy. is_Var y) \<and>
            list_inter (map the_Var yy) (vars_rule_impl (ll,rr)) = [] \<and>
            instance_rule (l, r) (ll, rr)
        | _ \<Rightarrow> False))
        (showsl_lit (STR ''eta expansion of '') \<circ> showsl_rule (l, r) \<circ> showsl_lit (STR '' missing'')) 
    | _ \<Rightarrow> succeed) R"


lemma eta_closed_top_rules:
  "isOK (eta_closed_top_rules a n sm R P) = eta_closed_top a n sm (set R) (set P)"
proof -
  let ?Q = "\<lambda>l r. (\<lambda>(lll, rrr). case (lll, rrr) of
    (Fun f (ll # yy), Fun g (rr # zz)) \<Rightarrow>
      f = a \<and> g = a \<and> zz = yy \<and> length yy = n - 1 \<and> distinct yy \<and>
      (\<forall>y\<in>set yy. is_Var y) \<and> list_inter (map the_Var yy) (vars_rule_impl (ll,rr)) = [] \<and>
      instance_rule (l,r) (ll,rr)
  | _ \<Rightarrow> False)"
  let ?R = "\<lambda>l r.  isOK (case l of 
    Fun ff ls \<Rightarrow> check (aarity sm ff (length ls) = 0 \<or> (\<exists>p\<in>set P. ?Q l r p))
      (showsl_lit (STR ''eta expansion of '') \<circ> showsl_rule (l, r) \<circ> showsl_lit (STR '' missing'')) 
  | _ \<Rightarrow> succeed)"
  let ?Var = "Var :: 'b \<Rightarrow> ('a, 'b) term"
  show ?thesis
  proof 
    assume ok: "isOK (eta_closed_top_rules a n sm R P)" 
    show "eta_closed_top a n sm (set R) (set P)"
      unfolding eta_closed_top_def
    proof (intro allI impI)
      fix ff l r
      assume lr: "(Fun ff l,r) \<in> set R" and aa: "aarity sm ff (length l) \<noteq> 0"
      let ?l = "Fun ff l"
      let ?P = "?Q ?l r"
      from ok[unfolded eta_closed_top_rules_def, simplified, THEN bspec[OF _ lr], unfolded set_list_inter] aa
      obtain lll rrr where lllrrr: "(lll,rrr) \<in> set P" and P: "?P (lll,rrr)" by auto
      from P obtain f ls where lll: "lll = Fun f ls" by (cases lll, auto)
      from P[unfolded lll] obtain ll yy where lll: "lll = Fun f (ll # yy)" unfolding lll by (cases ls, auto)
      note P = P[unfolded lll]
      from P obtain g rs where rrr: "rrr = Fun g rs" by (cases rrr, auto)
      from P[unfolded rrr] obtain rr rs where rrr: "rrr = Fun g (rr # rs)" unfolding rrr by (cases rs, auto)
      from P[unfolded rrr] lll rrr have lll: "lll = Fun a (ll # yy)"
        and rrr: "rrr = Fun a (rr # yy)" 
        and len: "length yy = n - 1" and yy1: "distinct yy" 
        and yy2: "\<forall>y\<in>set yy. is_Var y"
        and yy3: "list_inter (map the_Var yy) (vars_rule_impl (ll, rr)) = []"
        and inst: "instance_rule (?l, r) (ll, rr)" by auto
      have id: "map ?Var (map the_Var yy) = yy" by (rule Var_the_Var_id[OF yy2])
      have "distinct (map ?Var (map the_Var yy))" unfolding id  by (rule yy1)
      from this[unfolded distinct_map[of ?Var]] have yy1: "distinct (map the_Var yy)" ..
      from arg_cong[OF yy3, of set] have yy3: "set (map the_Var yy) \<inter> vars_rule (ll,rr) = {}" unfolding set_list_inter set_vars_rule_impl by simp
      show "\<exists> ll rr ys. length ys = n - 1 \<and> distinct ys \<and> set ys \<inter> vars_rule (ll,rr) = {} \<and> instance_rule (?l,r) (ll,rr) \<and> (Fun a (ll # map Var ys), Fun a (rr # map Var ys)) \<in> set P"
        by (rule exI[of _ ll], rule exI[of _ rr], rule exI[of _ "map the_Var yy"], simp only: inst yy3 yy1 id, simp add: len lllrrr[unfolded lll rrr]) 
    qed
  next
    assume eta: "eta_closed_top a n sm (set R) (set P)"
    {
      fix l r
      assume mem: "(l,r) \<in> set R"
      have "?R l r"
      proof (cases l)	
        case (Var x) 
        then show ?thesis by auto
      next
        case (Fun ff ls)
        show ?thesis 
        proof (cases "aarity sm ff (length ls)")
          case 0
          show ?thesis unfolding Fun by (simp add: 0)
        next
          case (Suc m)
          from eta[unfolded eta_closed_top_def, THEN spec, THEN spec, THEN spec, THEN mp[OF _ mem[unfolded Fun]], THEN mp, unfolded Suc]
          obtain ll rr ys where len: "length ys = n - 1" and dist: "distinct ys" and ys: "set ys \<inter> vars_rule (ll,rr) = {}" and 
            inst: "instance_rule (l,r) (ll,rr)" 
            and mem: "(Fun a (ll # map ?Var ys), Fun a (rr # map ?Var ys)) \<in> set P" (is "?lr \<in> set P")
            unfolding Fun
            by auto
          from ys have "set ys \<inter> set (vars_rule_impl (ll,rr)) = {}" unfolding set_vars_rule_impl .
          then have ys: "list_inter ys (vars_rule_impl (ll,rr)) = []" unfolding set_list_inter[symmetric] 
            by (cases "list_inter ys (vars_rule_impl (ll,rr))", auto)
          from dist have dist: "distinct (map Var ys)"
            unfolding distinct_map inj_on_def by auto
          have "(?Q l r) ?lr" 
            by (simp add: ys inst mem len o_def dist)
          with mem have "\<exists>p\<in>set P. ?Q l r p" by blast
          then show ?thesis unfolding Fun by (simp add: Suc)
        qed
      qed
    } note main = this
    show "isOK (eta_closed_top_rules a n sm R P)"
      unfolding eta_closed_top_rules_def isOK_check_allm
      by (intro ballI, insert main, auto)
  qed
qed

definition
  only_eta_rules :: "('f:: showl, 'v:: showl) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> showsl check"
where
  "only_eta_rules E R_eta \<equiv> check_allm (\<lambda>(l, r). 
    check ((case (l, r) of
      (Fun f ls, Fun g rs) \<Rightarrow>
        f = g \<and> length ls = 2 \<and> length rs = 2 \<and> ls ! 1 = rs ! 1 \<and>
        (\<exists>(l', r')\<in>set R_eta. instance_rule (hd ls, hd rs) (l',r'))
    | _ \<Rightarrow> False))
    (showsl_lit (STR ''rule '') \<circ> showsl_rule (l, r) \<circ>
      showsl_lit (STR '' is not an (eta-expanded) original rule''))) E"

lemma only_eta_rules:
  assumes inf: "infinite (UNIV::('v:: showl) set)"
  shows "isOK (only_eta_rules (E::('f:: showl, 'v:: showl) rules) R_eta) =
    only_eta (set E) (set R_eta)"
proof -
  let ?P = "\<lambda>l r. ((case (l, r) of
    (Fun f ls, Fun g rs) \<Rightarrow>
      f = g \<and> length ls = 2 \<and> length rs = 2 \<and> ls ! 1 = rs ! 1 \<and>
      (\<exists>(l', r')\<in>set R_eta. instance_rule (hd ls, hd rs) (l',r'))
  | _ \<Rightarrow> False))"
  show ?thesis
  proof
    assume ok: "isOK (only_eta_rules E R_eta)"
    show "only_eta (set E) (set R_eta)"
      unfolding only_eta_def
    proof(intro allI impI)
      fix l r::"('f, 'v) term"
      assume lr: "(l, r) \<in> set E"      
      with ok[unfolded only_eta_rules_def] have P: "?P l r" by auto
      from P obtain f ls where l: "l = Fun f ls" by (cases l, auto)
      from P obtain g rs where r: "r = Fun g rs" unfolding l by (cases r, auto)
      from P l r obtain l' r' where l: "l = Fun f ls" and r: "r = Fun f rs"
        and ls: "length ls = 2" and rs: "length rs = 2" and ls1: "ls ! 1 = rs ! 1"
        and l'r': "(l',r') \<in> set R_eta"
        and inst: "instance_rule (hd ls, hd rs) (l',r')"
        by auto
      obtain l1 l2 where ls: "ls = [l1,l2]" by (rule obtain_length2[OF ls])
      obtain r1 r2 where rs: "rs = [r1,r2]" by (rule obtain_length2[OF rs])
      from ls rs l r ls1 have l: "l = Fun f [l1,l2]" and r: "r = Fun f [r1,l2]" by auto      
      from inst[unfolded ls rs, simplified] obtain \<sigma> where l1: "l1 = l' \<cdot> \<sigma>" and r1: "r1 = r' \<cdot> \<sigma>" unfolding instance_rule_def by auto
      from infinite_imp_elem[OF Diff_infinite_finite[OF finite_set[of "vars_rule_impl (l',r')"] inf]]
      obtain x where xl': "x \<notin> vars_term l'" and xr': "x \<notin> vars_term r'" unfolding set_vars_rule_impl vars_rule_def by auto
      let ?sig = "subst_extend \<sigma> (zip [x] [l2])"
      note subst_extend_id = subst_extend_id[of "UNIV - {x}" "[x]" _ \<sigma> "[l2]", simplified]
      from xl' subst_extend_id[of l'] have l': "l' \<cdot> ?sig = l' \<cdot> \<sigma>" by auto
      from xr' subst_extend_id[of r'] have r': "r' \<cdot> ?sig = r' \<cdot> \<sigma>" by auto
      show "\<exists> a t l' r'. (l',r') \<in> set R_eta \<and> instance_rule (l,r) (Fun a [l',t], Fun a [r',t])"
        by (rule exI[of _ f], rule exI[of _ "Var x"], intro exI, intro conjI, rule l'r', unfold instance_rule_def l r l1 r1, rule exI[of _ ?sig], simp
           add: l'[symmetric] r'[symmetric])
    qed
  next
    assume eta: "only_eta (set E) (set R_eta)"
    show "isOK(only_eta_rules E R_eta)"
      unfolding only_eta_rules_def isOK_check_allm
    proof
      fix lr
      assume mem: "lr \<in> set E"
      obtain l r where lr: "lr = (l,r)" by (cases lr, auto)
      let ?Q = "\<lambda> (l,r). check (?P l r)
                   (showsl_lit (STR ''rule '') \<circ> showsl_rule (l,r) \<circ> showsl_lit (STR '' is not an (eta-expanded) original rule''))"
      have "?P l r"
      proof -
        from eta[unfolded only_eta_def, THEN spec, THEN spec, THEN mp[OF _ mem[unfolded lr]]]
        obtain a t l' r' where l'r': "(l',r') \<in> set R_eta" and inst: "instance_rule (l,r) (Fun a [l',t], Fun a [r', t])" 
          by auto
        then obtain \<sigma> where l: "l =  Fun a [l',t] \<cdot> \<sigma>" and r: "r = Fun a [r', t] \<cdot> \<sigma>"
          unfolding instance_rule_def by auto
        show "?P l r"
          by (unfold l r, simp, rule bexI[OF _ l'r'], unfold instance_rule_def, rule exI[of _ \<sigma>], simp)
      qed
      then show "isOK(?Q lr)" unfolding lr by auto
    qed
  qed
qed


definition
  uncurry_rules :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules"
where
  "uncurry_rules a sm \<equiv> map (\<lambda>(l, r). (uncurry_term a sm l, uncurry_term a sm r))"

lemma uncurry_rules: "set (uncurry_rules a sm R) = uncurry_trs a sm (set R)"
  unfolding uncurry_rules_def uncurry_trs_def by auto

type_synonym 'f sig_map_list = "(('f \<times> nat) \<times> 'f list) list"

definition
  sig_list_to_sig_map :: "'f \<Rightarrow> 'f sig_map_list \<Rightarrow> ('f sig_map_list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f)  \<Rightarrow> 'f sig_map"
where
  "sig_list_to_sig_map a sml fmap \<equiv>
    let
      fm = fmap sml
    in (\<lambda>f n. case map_of sml (f, n) of None \<Rightarrow> [fm f n] | Some xs \<Rightarrow> if xs = [] then [fm f n] else xs)"


definition uncurry_of_sig_list :: "'f \<Rightarrow> 'f sig_map_list \<Rightarrow> 'f sig_map \<Rightarrow> ('f,string)rules"
  where "uncurry_of_sig_list a sml sm \<equiv> concat (map (\<lambda> ((f,n),_). (
                  let g = get_symbol sm f n in
                    map (\<lambda> i. (Fun a [generate_f_xs (g i) (n+i), Var (generate_var (n+i))], generate_f_xs (g (Suc i)) (n + Suc i))) [0 ..< aarity sm f n]
           )) sml)"

lemma uncurry_of_sig_list: "set (uncurry_of_sig_list a sml (sig_list_to_sig_map a sml fmap)) = uncurry_of_sig a (sig_list_to_sig_map a sml fmap)" (is "?l = ?r")
proof -
  let ?sm = "sig_list_to_sig_map a sml fmap"
  {
    fix l r
    assume "(l,r) \<in> ?l"
    then obtain f n list where mem: "((f,n),list) \<in> set sml" 
      and mem2: "(l,r) \<in>  set (map (\<lambda>i. (Fun a
                                   [generate_f_xs (get_symbol ?sm f n i) (n + i),
                                    Var (generate_var (n + i))],
                                  generate_f_xs  (get_symbol ?sm f n (Suc i)) (n + Suc i)))
                         [0..<aarity ?sm f n])"
      unfolding uncurry_of_sig_list_def Let_def by auto
    from mem2
    obtain i where i: "i < aarity ?sm f n" and l: "l = Fun a [generate_f_xs (get_symbol ?sm f n i) (n + i),Var (generate_var (n + i))]"
      and r: "r = generate_f_xs  (get_symbol ?sm f n (Suc i)) (n + Suc i)" by auto
    have "(l,r) \<in> ?r" unfolding l r uncurry_of_sig_def using i by auto
  } note l_imp_r = this
  {
    fix l r
    assume "(l,r) \<in> ?r"
    then obtain f n i where i: "i < aarity ?sm f n" and l: "l = Fun a [generate_f_xs (get_symbol ?sm f n i) (n + i),Var (generate_var (n + i))]"
      and r: "r = generate_f_xs  (get_symbol ?sm f n (Suc i)) (n + Suc i)" unfolding uncurry_of_sig_def by auto
    from i[unfolded aarity_def sig_list_to_sig_map_def] obtain list where map_of: "map_of sml (f, n) = Some list" 
      by (cases "map_of sml (f, n)", auto simp: Let_def)
    from map_of_SomeD[OF map_of] have mem: "((f,n),list) \<in> set sml" by auto
    have "(l,r) \<in> ?l" unfolding uncurry_of_sig_list_def
      by (simp, rule bexI[OF _ mem], simp add: Let_def, unfold l r, insert i, auto)
  }
  with l_imp_r show ?thesis by auto
qed  

declare hvf_term.simps[simp del]

abbreviation "uncurry_below_rules sm \<equiv> map_funs_rules_wa (get_default_sym sm)"

definition uncurry_top_rules :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules"
  where "uncurry_top_rules a n sm \<equiv> map (\<lambda> (l,r). (uncurry_top a n sm l, uncurry_top a n sm r))"

lemma uncurry_top_rules: "set (uncurry_top_rules a n sm R) = uncurry_top_trs a n sm (set R)"
  unfolding uncurry_top_rules_def uncurry_top_trs_def by auto

definition uncurry_of_top_sig_list :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map_list \<Rightarrow> 'f sig_map \<Rightarrow> ('f,string)rules"
  where "uncurry_of_top_sig_list a m sml sm \<equiv> concat (map (\<lambda> ((f,n),_). (
                  let g = get_symbol sm f n in
                    map (\<lambda> i. (Fun a (generate_f_xs (g i) (n+i)  # map (\<lambda>i. Var (generate_var i)) [n + i..<n + i + (m - 1)]), generate_f_xs (g (Suc i)) (n + i + (m - 1)))) [0 ..< aarity sm f n]
           )) sml)"

lemma uncurry_of_top_sig_list: "set (uncurry_of_top_sig_list a m sml (sig_list_to_sig_map a sml fmap)) = uncurry_of_top_sig a m (sig_list_to_sig_map a sml fmap)" (is "?l = ?r")
proof -
  let ?sm = "sig_list_to_sig_map a sml fmap"
  let ?g = "get_symbol ?sm"
  {
    fix l r
    assume "(l,r) \<in> ?l"
    then obtain f n list where mem: "((f,n),list) \<in> set sml" 
      and mem2: "(l,r) \<in>  set (map (\<lambda>i. (Fun a
                              (generate_f_xs (?g f n i) (n+i)  # map (\<lambda>i. Var (generate_var i)) [n + i..<n + i + (m - 1)]), 
                              generate_f_xs (?g f n (Suc i)) (n + i + (m - 1)))) [0 ..< aarity ?sm f n])"
      unfolding uncurry_of_top_sig_list_def Let_def by auto
    from mem2
    obtain i where i: "i < aarity ?sm f n" and l: "l = Fun a (generate_f_xs (?g f n i) (n + i) # map (\<lambda> i. Var (generate_var i)) [n+ i..< n + i + (m - 1)])" 
      and r: "r = generate_f_xs  (?g f n (Suc i)) (n + i + (m - 1))" by auto
    have "(l,r) \<in> ?r" unfolding l r uncurry_of_top_sig_def using i by auto
  } note l_imp_r = this
  {
    fix l r
    assume "(l,r) \<in> ?r"
    then obtain f n i where i: "i < aarity ?sm f n" and l: "l = Fun a (generate_f_xs (?g f n i) (n + i) # map (\<lambda> i. Var (generate_var i)) [n+i..< n + i + (m - 1)])" 
      and r: "r = generate_f_xs  (?g f n (Suc i)) (n + i + (m - 1))" unfolding uncurry_of_top_sig_def by auto 
    from i[unfolded aarity_def sig_list_to_sig_map_def] obtain list where map_of: "map_of sml (f, n) = Some list" 
      by (cases "map_of sml (f, n)", auto simp: Let_def)
    from map_of_SomeD[OF map_of] have mem: "((f,n),list) \<in> set sml" by auto
    have "(l,r) \<in> ?l" unfolding uncurry_of_top_sig_list_def
      by (simp, rule bexI[OF _ mem], simp add: Let_def, unfold l r, insert i, auto)
  }
  with l_imp_r show ?thesis by auto
qed  

subsection \<open>tts and procs\<close>
      
(* uncurry info consists of
   1. uncurry symbol
   2. symbol mapping
   3. uncurrying rules
   4. additional rules in eta expansion
*)
type_synonym ('f,'v) uncurry_info = "'f \<times> 'f sig_map_list \<times> ('f,'v)rules \<times> ('f,'v)rules"
    
(* uncurry_eta_split splits the additional eta rules into two parts *)
definition
  uncurry_eta_split :: "('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) rules \<times> ('f, 'v) rules"
where
  "uncurry_eta_split Eboth Rtest \<equiv> let 
    test = (\<lambda>(l, r). num_args l > 0 \<and> num_args r > 0 \<and>
      (\<exists>rule\<in>set Rtest. (hd (args l), hd (args r)) =\<^sub>v rule))
  in partition test Eboth"

(* the usage of R' is not required for this processor, however, it is used
   to detect early, whether the user has computed the correct uncurried rules *)
definition
  uncurry_tt ::
    "('tp, 'f, string) tp_ops \<Rightarrow>
    ('f, string) uncurry_info \<Rightarrow> ('f:: showl, string) rules \<Rightarrow> 'tp proc"
where
  "uncurry_tt I info R' tp \<equiv> case info of (a,sml,U,Eb) \<Rightarrow> let      
      R = tp_ops.R I tp;
      Rw = tp_ops.Rw I tp;
      (E,Ew) = uncurry_eta_split Eb R;
      R_eta = E @ R;
      Rw_eta = Ew @ Rw;
      Rb_eta = R_eta @ Rw_eta;
      fmap = (\<lambda> _ f _. f);
      sm = sig_list_to_sig_map a sml fmap;
      uR = uncurry_rules a sm R_eta;
      uRw = uncurry_rules a sm Rw_eta
      in       
       check_return (do {
           let S = uncurry_of_sig_list a sml sm;
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) R_eta;
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) Rw_eta;
           eta_closed_rules a sm R_eta R_eta;
           eta_closed_rules a sm Rb_eta Rb_eta;
           check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhs must not be a variable in rule '') \<circ> showsl_rule (l,r))) Rw_eta;
           check_subseteq uR R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq uRw R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_CS_subseteq S U
              <+? (\<lambda> lr. showsl_lit (STR ''uncurry rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq U R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurry rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in new TRS''))
   }) (tp_ops.mk I (tp_ops.nfs I tp) [] uR (uRw @ U))"

lemma uncurry_tt:
  assumes I: "tp_spec I"
  shows "tp_spec.sound_tt_impl I (uncurry_tt I info R')"
proof (cases info)
  case (fields a sml U Eb)
  interpret tp_spec I by (rule I)
  show ?thesis unfolding fields
  proof
    fix tp tp'
    assume ok: "uncurry_tt I (a,sml,U,Eb) R' tp = return tp'" 
      and SN: "SN_qrel (tp_ops.qreltrs I tp')"
    obtain R where R: "tp_ops.R I tp = R" by auto
    obtain Rw where Rw: "tp_ops.Rw I tp = Rw" by auto
    obtain E Ew where "uncurry_eta_split Eb R = (E,Ew)" by (cases "uncurry_eta_split Eb R", auto)
    note ok =  ok[unfolded uncurry_tt_def split Let_def R this]
    obtain Q where Q: "set (tp_ops.Q I tp) = Q" by auto
    let ?sm = "sig_list_to_sig_map a sml (\<lambda> _ f _. f)"
    let ?R_eta = "E @ R"
    let ?Rw_eta = "Ew @ Rw"
    let ?u = "uncurry_rules a ?sm"
    let ?U = "uncurry_trs a ?sm (set ?R_eta)"
    let ?Uw = "uncurry_trs a ?sm (set ?Rw_eta)"
    let ?S = "uncurry_of_sig a ?sm"
    let ?nfs = "NFS tp"
    obtain R_eta where R_eta: "?R_eta = R_eta" by simp
    obtain Rw_eta where Rw_eta: "?Rw_eta = Rw_eta" by simp
    from ok
    have hvf1: "\<And> l r. (l,r) \<in> set ?R_eta \<Longrightarrow> hvf_term a l" 
      and hvf2: "\<And> l r. (l,r) \<in> set ?Rw_eta \<Longrightarrow> hvf_term a l" 
      and eta1: "eta_closed a ?sm (set ?R_eta) (set ?R_eta)"
      and eta2: "eta_closed a ?sm (set (?R_eta @ ?Rw_eta)) (set (?R_eta @ ?Rw_eta))"
      and var: "\<And> l r. (l,r) \<in> set ?Rw_eta \<Longrightarrow> is_Fun l"
      and S: "subst.closure ?S \<subseteq> subst.closure (set U)"
      and tp': "tp' = tp_ops.mk I ?nfs [] (?u ?R_eta) (?u ?Rw_eta @ U)"
      unfolding R Rw
      by (auto simp: Rw_eta R_eta eta_closed_rules Let_def  uncurry_rules uncurry_of_sig_list)
    from R_eta have R_eta: "set R \<subseteq> set ?R_eta" by auto 
    {
      fix x r
      have "(Var x,r) \<notin> set ?Rw_eta"
        using var[of "Var x" r] by auto
    } note var = this
    from ctxt.closure_mono[OF S, unfolded rstep_eq_closure[symmetric]] 
    have S: "rstep ?S \<subseteq> rstep (set U)" .
    from SN[unfolded tp' mk_sound uncurry_rules set_append]
    have SN: "SN_qrel (?nfs,{}, ?U, ?Uw \<union> set U)" by auto
    have SN: "SN_qrel (?nfs,{},?U,?Uw \<union> ?S)"
      by (rule SN_qrel_mono_plain[OF subset_refl _ SN], insert S, auto simp: rstep_union)
    show "SN_qrel (tp_ops.qreltrs I tp)"
      unfolding qreltrs_sound R Rw Q
      by (rule uncurrying_sound[OF hvf1 hvf2 _ eta1 _ _ var SN], insert eta2)
         ( auto simp: Un_assoc) 
  qed
qed

definition
  uncurry_nonterm_tt_check ::
    "('tp, 'f, string) tp_ops \<Rightarrow> ('f, string) uncurry_info
    \<Rightarrow> ('f sig_map_list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'f sig_map_list \<Rightarrow> showsl check)
    \<Rightarrow> ('f:: showl, string)rules \<Rightarrow> 'tp proc"
where
  "uncurry_nonterm_tt_check I info fmap check_inj R' dpp \<equiv> case info of (a,sml,U,E) \<Rightarrow> (let 
      R = tp_ops.rules I dpp;
      nfs = tp_ops.nfs I dpp;
      sm = sig_list_to_sig_map a sml fmap;
      R_eta = E @ R;
      uR = uncurry_rules a sm R_eta
    in 
        check_return (do {
           check (tp_ops.Q I dpp = []) (showsl_lit (STR ''strategy not supported for uncurrying''));
           let S = uncurry_of_sig_list a sml sm;
           only_eta_rules E R_eta;
           check_inj a 2 sml;
           check_CS_subseteq U S
              <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is not an uncurry rule''));
           check_subseteq R' (U @ uR)
              <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is neither uncurried rules nor uncurry rule''))
   }) (tp_ops.mk I nfs [] R' []))"

lemma uncurry_nonterm_tt_check:
  assumes I: "tp_spec I" 
    and check_inj: "isOK(check_inj a 2 sml)
    \<Longrightarrow> inj_sig_map a 2 (sig_list_to_sig_map a sml fmap)"
  and ok: "uncurry_nonterm_tt_check I (a, sml, U, E) fmap check_inj R' tp = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" 
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" 
proof -
  let ?map = "sig_list_to_sig_map a sml fmap"
  interpret tp_spec I by fact
  note [simp] = uncurry_rules uncurry_of_sig_list
  note ok = ok[unfolded uncurry_nonterm_tt_check_def split Let_def]
  from ok have Q: "set (Q tp) = {}"
    and eta: "isOK (only_eta_rules E (E @ rules tp))"
    and inj: "isOK (check_inj a 2 sml)"
    and U: "subst.closure (set U) \<subseteq> subst.closure (uncurry_of_sig a ?map)"
    and R': "set R' \<subseteq> set U \<union> uncurry_trs a ?map (set E \<union> set (rules tp))"
    and tp': "tp' = tp_ops.mk I (NFS tp) [] R' []" by auto
  from nSN tp' have nSN: "\<not> SN (rstep (set R'))" by auto
  have "infinite (UNIV :: string set)" by (rule infinite_UNIV_listI)
  from eta[unfolded only_eta_rules[OF this]] have eta: "only_eta (set E) (set E \<union> set (rules tp))" by simp
  note proc = uncurrying_for_nonterm[OF check_inj[OF inj] eta]
  have id: "?thesis = (\<not> SN (rstep (set (rules tp))))"
    by (simp add: Q)
  note un = rrstep_union[folded CS_rrstep_conv]
  show ?thesis unfolding id
  proof (rule proc[OF contrapos_nn[OF nSN]], rule SN_subset)
    show "rstep (set R') \<subseteq> rstep (uncurry_trs a ?map (set E \<union> set (rules tp)) \<union>
      uncurry_of_sig a ?map)"
    by (rule order_trans[OF rstep_mono[OF R']], unfold rstep_eq_closure, 
      rule ctxt.closure_mono, unfold un, insert U, auto)
  qed
qed

(* the usage of R' and P' is not required for this processor, however, it is used
   to detect early, whether the user has computed the correct uncurried pairs *)
definition
  uncurry_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f, string) uncurry_info
    \<Rightarrow> ('f sig_map_list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'f sig_map_list \<Rightarrow> showsl check)
    \<Rightarrow> ('f, string) rules \<Rightarrow> ('f:: showl, string)rules \<Rightarrow> 'dpp proc"
where
  "uncurry_proc I info fmap check_inj P' R' dpp \<equiv> case info of (a,sml,U,Eb) \<Rightarrow> (let 
      P = dpp_ops.P I dpp;
      Pw = dpp_ops.Pw I dpp;
      R = dpp_ops.R I dpp;
      Rw = dpp_ops.Rw I dpp;
      nfs = dpp_ops.nfs I dpp;
      m = dpp_ops.minimal I dpp;
      (E,Ew) = uncurry_eta_split Eb R;
      sm = sig_list_to_sig_map a sml fmap;
      uP = uncurry_rules a sm P;
      uPw = uncurry_rules a sm Pw;
      R_eta = E @ R;
      Rw_eta = Ew @ Rw;
      uR = uncurry_rules a sm R_eta;
      uRw = uncurry_rules a sm Rw_eta
    in 
        check_return (do {
           let S = uncurry_of_sig_list a sml sm;
           check (dpp_ops.Q I dpp = []) (showsl_lit (STR ''strategy not supported for uncurrying''));
           only_eta_rules E R_eta;
           only_eta_rules Ew Rw_eta;
           check_inj a 2 sml;
           check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhs as variable is not allowed''))) (R @ Rw);
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) P;
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) Pw;
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) R_eta;
           check_allm (\<lambda> (l,r). check (hvf_term a l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''))) Rw_eta;
           eta_closed_rules a sm R_eta R_eta;
           eta_closed_rules a sm Rw_eta Rw_eta;
           check_subseteq uP P'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq uPw P'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq uR R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq uRw R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_CS_subseteq S U
              <+? (\<lambda> lr. showsl_lit (STR ''uncurry rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_CS_subseteq U S
              <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is not an uncurry rule''));
           check_subseteq U R'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurry rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in new TRS''))
   }) (dpp_ops.mk I nfs m uP uPw [] uR (uRw @ U)))"


lemma uncurry_proc:
  assumes "dpp_spec I"
    and check_inj: "isOK (check_inj a 2 sml)
    \<Longrightarrow> inj_sig_map a 2 (sig_list_to_sig_map a sml fmap)"
  shows "dpp_spec.sound_proc_impl I (uncurry_proc I (a, sml, U, Eb) fmap check_inj P' R')"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume ok: "uncurry_proc I (a, sml, U, Eb) fmap check_inj P' R' d = return d'"
      and fin: "finite_dpp (dpp_ops.dpp I d')"
    obtain r where r: "dpp_ops.R I d = r" by auto
    obtain rw where rw: "dpp_ops.Rw I d = rw" by auto
    obtain p where p: "dpp_ops.P I d = p" by auto
    obtain pw where pw: "dpp_ops.Pw I d = pw" by auto
    obtain E Ew where Eb: "uncurry_eta_split Eb r = (E, Ew)"
      by (cases "uncurry_eta_split Eb r", auto)
    let ?sm = "sig_list_to_sig_map a sml fmap"
    let ?R = "set r"
    let ?Rw = "set rw"
    let ?R_eta = "E @ r"
    let ?Rw_eta = "Ew @ rw"
    obtain r_eta where r_eta: "?R_eta = r_eta" by simp
    obtain rw_eta where rw_eta: "?Rw_eta = rw_eta" by simp
    let ?UP = "uncurry_trs a ?sm (set p)"
    let ?UPw = "uncurry_trs a ?sm (set pw)"
    let ?UR = "uncurry_trs a ?sm (set ?R_eta)"
    let ?URw = "uncurry_trs a ?sm (set ?Rw_eta)"
    let ?nfs = "NFS d"
    let ?m = "M d"
    let ?S = "uncurry_of_sig a ?sm"
    let ?u = "uncurry_rules a ?sm"
    note ok = ok[unfolded uncurry_proc_def split Let_def r Eb]
    from ok
    have  hvf1: "\<And> l r. (l,r) \<in> set ?R_eta \<Longrightarrow> hvf_term a l" 
      and hvf2: "\<And> l r. (l,r) \<in> set ?Rw_eta \<Longrightarrow> hvf_term a l" 
      and hvfP: "\<And> l r. (l,r) \<in> set p \<union> set pw \<Longrightarrow> hvf_term a l" 
      and eta1: "eta_closed a ?sm (set ?R_eta) (set ?R_eta)"
      and eta2: "eta_closed a ?sm (set ?Rw_eta) (set ?Rw_eta)"
      and only1: "isOK(only_eta_rules E ?R_eta)"
      and only2: "isOK(only_eta_rules Ew ?Rw_eta)"
      and S: "subst.closure ?S \<subseteq> subst.closure (set U)"
      and U: "subst.closure (set U) \<subseteq> subst.closure ?S"
      and inj: "isOK(check_inj a 2 sml)"
      and Q: "dpp_ops.Q I d = []"
      and d': "d' = dpp_ops.mk I ?nfs ?m (?u p) (?u pw) [] (?u ?R_eta) (?u ?Rw_eta @ U)"
      unfolding p pw r rw
      by (auto simp: r_eta rw_eta eta_closed_rules uncurry_rules uncurry_of_sig_list)
    from ok have nvar: "\<And> x. x \<in> ?R \<union> ?Rw \<Longrightarrow> isOK (case x of (l, r) \<Rightarrow> check (is_Fun l) 
      (showsl_lit (STR ''lhs as variable is not allowed'')))"
      unfolding r rw by auto
    {
      fix l r
      assume "(l,r) \<in> ?R \<union> ?Rw"
      from nvar[OF this]
      have "is_Fun l" by auto
    } note nvar = this
    have inf: "infinite (UNIV :: string set)" by (rule infinite_UNIV_listI)
    have only1: "only_eta (set E) (set ?R_eta)" 
      using only1[unfolded only_eta_rules[OF inf]] by simp      
    have only2: "only_eta (set Ew) (set ?Rw_eta)" 
      using only2[unfolded only_eta_rules[OF inf]] by simp
    from only1 only2 have only: "only_eta (set E \<union> set Ew) (set ?R_eta \<union> set ?Rw_eta)"
      unfolding only_eta_def by blast
    from eta1 eta2 have eta2: "eta_closed a ?sm (set ?R_eta \<union> set ?Rw_eta) (set ?R_eta \<union> set ?Rw_eta)" unfolding eta_closed_def by blast
    from hvf1 hvf2 hvfP have hvf: "\<And> l r. (l,r) \<in> set ?R_eta \<union> set ?Rw_eta \<union> set p \<union> set pw \<Longrightarrow> hvf_term a l" by blast
    from ctxt.closure_mono[OF S, unfolded rstep_eq_closure[symmetric]] 
      ctxt.closure_mono[OF U, unfolded rstep_eq_closure[symmetric]] 
    have S: "rstep ?S = rstep (set U)" by auto
    note fin = fin[unfolded d' mk_sound list.set]
    show "finite_dpp (dpp_ops.dpp I d)" unfolding dpp_sound rw Q pw list.set p r
      by (rule uncurrying_sound_dp[OF hvf eta1 eta2 _ _ only _ check_inj[OF inj] finite_dpp_mono_plain[OF fin]], auto simp: uncurry_rules S nvar rstep_union)
  qed
qed

definition
  uncurry_top_proc ::
    "('dpp, 'f, string) dpp_ops \<Rightarrow> ('f, string) uncurry_info \<Rightarrow> nat
     \<Rightarrow> ('f sig_map_list \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f) \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'f sig_map_list \<Rightarrow> showsl check)
     \<Rightarrow> ('f, string) rules \<Rightarrow> ('f:: showl, string) rules \<Rightarrow> 'dpp proc"
where
  "uncurry_top_proc I info n fmap check_inj P' R' dpp \<equiv> case info of (a,sml,U,Eb) \<Rightarrow> let
      P = dpp_ops.P I dpp;
      Pw = dpp_ops.Pw I dpp;
      R = dpp_ops.R I dpp;
      Rw = dpp_ops.Rw I dpp;
      nfs = dpp_ops.nfs I dpp;
      m = dpp_ops.minimal I dpp;
      (E,Ew) = uncurry_eta_split Eb R;
      sm = sig_list_to_sig_map a sml fmap;
      P_eta = E @ P;
      Pw_eta = Ew @ Pw;
      uP = uncurry_top_rules a n sm P_eta;
      uPw = uncurry_top_rules a n sm Pw_eta;
      uR = uncurry_below_rules sm R;
      uRw = uncurry_below_rules sm Rw
    in (check_return (do {
           check (dpp_ops.Q I dpp = []) (showsl_lit (STR ''strategy currently unsupported''));
           check (n \<noteq> 0) (showsl_lit (STR ''the arity of the uncurried symbol must be at least 1''));
           check_inj a n sml;           
           let Pb = dpp_ops.pairs I dpp;
           let is_def = dpp_spec.is_defined I dpp;
           let rm = dpp_ops.rules_map I dpp;
           check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''lhs as variable is not allowed''))) (R @ Rw);
           check_allm (\<lambda> (l,r). do {
                 check (hvf_top a n l) (showsl_lit (STR ''head variable in lhs '') \<circ> showsl l \<circ> showsl_lit (STR '' not allowed''));
                 check_no_var r
           }) (Pw_eta @ P_eta);
           check_allm (\<lambda> (l,r). 
                 check (\<not> is_def (the (root r))) (showsl_lit (STR ''root of '') \<circ> showsl r \<circ> showsl_lit (STR '' must not be defined''))) Pb;
           check (\<not> (is_def (a,n))) (showsl_lit (STR ''application symbol '') \<circ> showsl a \<circ> showsl_lit (STR '' must not be defined in R''));
           (if (\<exists>(l, r)\<in>set Pb. the (root r) = (a, n) \<and>
                 tcapRM2 rm (hd (args r)) = GCHole) then
               do {
                  check_CS_subseteq (uncurry_of_top_sig_list a n sml sm) U
                       <+? (\<lambda> lr. showsl_lit (STR ''uncurrying pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in\<newline>'') \<circ> showsl_rules U);
                  eta_closed_top_rules a n sm R P_eta;
                  eta_closed_top_rules a n sm Rw Pw_eta
               } else succeed);
           check_subseteq uP P'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq uPw P'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurried pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing''));
           check_subseteq U P'
              <+? (\<lambda> lr. showsl_lit (STR ''uncurrying pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in new pairs''));
           check_subseteq uR R'
              <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in new rules''));
           check_subseteq uRw R'
              <+? (\<lambda> lr. showsl_lit (STR ''rule '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in new rules''))
   }) (dpp_ops.mk I nfs m uP (uPw @ U) [] uR uRw))"


lemma uncurry_top_proc:
  assumes "dpp_spec I"
    and check_inj: "n \<noteq> 0 \<Longrightarrow> isOK(check_inj a n sml)
    \<Longrightarrow> inj_sig_map a n (sig_list_to_sig_map a sml fmap)"
  shows "dpp_spec.sound_proc_impl I (uncurry_top_proc I (a,sml,U,Eb) n fmap check_inj P' R')"
proof -
  interpret dpp_spec I by fact
  show ?thesis
  proof
    fix d d'
    assume ok: "uncurry_top_proc I (a,sml,U,Eb) n fmap check_inj P' R' d = return d'"
      and fin: "finite_dpp (dpp_ops.dpp I d')"
    obtain P where P: "dpp_ops.P I d = P" by auto
    obtain Pw where Pw: "dpp_ops.Pw I d = Pw" by auto
    obtain Pb where Pb: "dpp_ops.pairs I d = Pb" by auto
    obtain R where R: "dpp_ops.R I d = R" by auto
    obtain Rw where Rw: "dpp_ops.Rw I d = Rw" by auto
    obtain Rb where Rb: "dpp_ops.rules I d = Rb" by auto
    obtain Q where Q: "dpp_ops.Q I d = Q" by auto
    obtain E Ew where Eb: "uncurry_eta_split Eb R = (E, Ew)" by force
    note ok = ok[unfolded uncurry_top_proc_def Let_def
      is_defined_sound Eb P Pw R Rw Pb Rb split Q, simplified]
    let ?sm = "sig_list_to_sig_map a sml fmap"
    obtain sm where sm: "sm = ?sm" by auto
    let ?R = "set R"
    let ?Rw = "set Rw"
    let ?P_eta = "E @ P"
    obtain P_eta where P_eta: "?P_eta = P_eta" by simp
    let ?Pw_eta = "Ew @ Pw"
    obtain Pw_eta where Pw_eta: "?Pw_eta = Pw_eta" by simp
    note ok
    let ?UP = "uncurry_top_trs a n sm (set ?P_eta)"
    let ?UPw = "uncurry_top_trs a n sm (set ?Pw_eta)"
    let ?UR = "uncurry_below_trs sm (set R)"
    let ?URw = "uncurry_below_trs sm (set Rw)"
    let ?U = "uncurry_of_top_sig a n sm"
    let ?u = "uncurry_top_rules a n sm"
    let ?uu = "uncurry_below_rules sm"
    let ?nfs = "NFS d"
    let ?m = "M d"
    obtain PPw_eta where PPw_eta: "PPw_eta = set Ew \<union> (set Pw \<union> (set E \<union> set P))" by auto
    note ok = ok[unfolded sm[symmetric] PPw_eta[symmetric]]
    from ok have nvar: "\<And> x. x \<in> ?R \<union> ?Rw \<Longrightarrow> isOK (case x of (l, r) \<Rightarrow> check (is_Fun l) 
      (showsl_lit (STR ''lhs as variable is not allowed'')))"
      unfolding R Rw by auto
    {
      fix l r
      assume "(l,r) \<in> ?R \<union> ?Rw"
      from nvar[OF this]
      have "is_Fun l" by auto
    } note nvar = this
    then have var: "\<And> lr. lr \<in> set Rb \<Longrightarrow> is_Fun (fst lr)" 
      unfolding Rb[symmetric] R[symmetric] Rw[symmetric] by force
    have tcap: "tcapRM2 (dpp_ops.rules_map I d) = tcap (set Rb)"
      by (intro ext, rule tcapRM2_sound[OF var, of Rb "dpp_ops.rules_map I d", unfolded Rb], 
        insert rules_map_sound[of d], unfold Rb, auto)
    note ok = ok[unfolded tcap]
    from ok
    have hvf: "\<And>l r. (l, r) \<in> PPw_eta \<Longrightarrow> hvf_top a n l \<and> is_Fun r"
      and ndef: "\<And>l r. (l, r) \<in> set Pb \<Longrightarrow> \<not> defined (set Rb) (the (root r))"        
      and eta: "isOK (if \<exists>(l, r)\<in>set Pb. the (root r) = (a, n) \<and> tcap (set Rb) (hd (args r)) = GCHole then
               do {
                  check_CS_subseteq (uncurry_of_top_sig_list a n sml sm) U
                       <+? (\<lambda> lr. showsl_lit (STR ''uncurrying pair '') \<circ> showsl_rule lr \<circ> showsl_lit (STR '' is missing in\<newline>'') \<circ> showsl_rules U);
                  eta_closed_top_rules a n sm R P_eta;
                  eta_closed_top_rules a n sm Rw Pw_eta
               } else succeed)" 
      and a: "\<not> defined (set Rb) (a,n)"
      and inj: "isOK(check_inj a n sml)"
      and Qe: "Q = []"
      and n: "n \<noteq> 0"
      and d': "d' = dpp_ops.mk I ?nfs ?m (?u P_eta) (?u Pw_eta @ U) [] (?uu R) (?uu Rw)"
        unfolding P_eta Pw_eta by auto
    from fin[unfolded d' mk_sound map_funs_rules_wa] 
    have fin: "finite_dpp (?nfs,?m,?UP,?UPw \<union> set U,{},?UR,?URw)"
      by (auto simp: uncurry_top_rules P_eta Pw_eta)
    note inj = check_inj[OF n inj]
    from n obtain m where n: "n = Suc m" by (cases n, auto)
    let ?d = "\<exists> (l,r) \<in> set Pb. the (root r) = (a, n) \<and> tcap (set Rb) (hd (args r)) = GCHole"
    have eta: "\<forall> (l,r) \<in> set Pb. the (root r) = (a, n) \<and> tcap (set Rb) (hd (args r)) = GCHole \<longrightarrow> eta_closed_top a n ?sm (set R) (set P_eta) \<and> eta_closed_top a n ?sm (set Rw) (set Pw_eta) \<and> subst.closure ?U \<subseteq> subst.closure (set U)"
    proof (cases ?d)
      case False
      then show ?thesis by blast
    next
      case True
      then have "?d = True" by simp
      note eta = eta[unfolded this, simplified, unfolded sm uncurry_of_top_sig_list] 
      from eta[unfolded eta_closed_top_rules] show ?thesis by (auto simp: sm)
    qed
    from ndef have ndef: "\<And> s f ts. (s, Fun f ts) \<in> set Pb \<Longrightarrow> \<not> defined (set Rb) (f, length ts)" by force
    have PPw: "PPw_eta = set P_eta \<union> set Pw_eta" unfolding PPw_eta P_eta[symmetric] Pw_eta[symmetric] by auto
    have Rb: "set Rb = set R \<union> set Rw" unfolding Rb[symmetric] rules_sound R Rw by auto
    have Pb: "set Pb = set P \<union> set Pw" unfolding Pb[symmetric] pairs_sound P Pw by auto
    note hvf = hvf[unfolded PPw n]
    note a = a[unfolded Rb n]
    note ndef = ndef[unfolded Pb Rb n]      
    note eta = eta[unfolded Pb Rb n sm CS_rrstep_conv]
    note inj = inj[unfolded n sm]
    note fin = fin[unfolded sm P_eta Pw_eta n]
    have fin: "finite_dpp (?nfs,?m,set P, set Pw, {}, set R, set Rw)" 
      by (rule uncurrying_top_sound_dp[OF hvf _ _ eta a ndef _ inj fin], insert nvar P_eta Pw_eta, auto)
    then show "finite_dpp (dpp d)"
      unfolding dpp_sound P Pw Q R Rw Qe by simp
  qed
qed

subsection \<open>generating injective symbol mappings from lists\<close>
context
begin
qualified definition fmap :: "('f,'l)lab \<Rightarrow> nat \<Rightarrow> ('f,'l)lab sig_map_list \<Rightarrow> ('f,'l)lab \<Rightarrow> nat \<Rightarrow> ('f,'l)lab"
where "fmap a nn sml \<equiv> let m = Suc (max_list (map label_depth (a # concat (map snd sml))))
                   in (\<lambda> f n. if (f,n) = (a,nn) then a else gen_label f m)"

definition
  check_partition :: "'a list list \<Rightarrow> 'a check"
where
  "check_partition xss = check_pairwise check_disjoint xss"

lemma isOK_check_partition [simp]:
  "isOK (check_partition xs) \<longleftrightarrow> is_partition (map set xs)"
  unfolding is_partition_def check_partition_def by auto

definition
  check_inj :: "('f :: showl, 'l :: showl) lab \<Rightarrow> nat \<Rightarrow> ('f, 'l) lab sig_map_list \<Rightarrow> showsl check"
where
  "check_inj a nn sml =
    (let
      symbols =
        map (\<lambda>((f, n), fs). map (\<lambda>(g, i). (g, n + i * (nn - 1))) (zip fs [0 ..< length fs])) sml;
      fsymbols = concat symbols
    in do {
      check_partition symbols 
        <+? (\<lambda> f. (showsl_lit (STR ''symbol '') \<circ> showsl f \<circ> showsl_lit (STR '' occurs twice)'')));
      check ((a, nn) \<notin> set fsymbols)
        (showsl_lit (STR ''application symbol'') \<circ> showsl a \<circ> showsl_lit (STR '' must not occur as new symbol''));
      check ((a, nn) \<notin> set (map fst sml))
        (showsl_lit (STR ''application symbol'') \<circ> showsl a \<circ> showsl_lit (STR '' must not be uncurried''));
      (if nn \<le> 1 then
        check_allm (check_pairwise (\<lambda> gn1 gn2.
          check (gn1 \<noteq> gn2) (showsl_lit (STR ''symbol '') \<circ> showsl gn1 \<circ> showsl_lit (STR '' occurs twice'')))) symbols
      else succeed)
    })"

lemma check_inj:
  assumes ok: "isOK (check_inj a nn sml)"
  shows "inj_sig_map a nn (sig_list_to_sig_map a sml (fmap a nn))"
proof -
  note ok = ok[unfolded check_inj_def Let_def, simplified]
  {
    fix v
    assume "map_of sml (a, nn) = Some v"
    from map_of_SomeD[OF this] have "(a,nn) \<in> set (map fst sml)" by force
    with ok have False by auto
  } note Some = this
  have a: "sig_list_to_sig_map a sml (fmap a nn) a nn = [a]"
    unfolding sig_list_to_sig_map_def Let_def
    by (cases "map_of sml (a, nn)", simp add: fmap_def, insert Some, auto)
  show ?thesis 
    unfolding inj_sig_map_def get_symbol_def aarity_def
  proof (rule conjI[OF _ a])
    let ?s = "sig_list_to_sig_map a sml (fmap a nn)"
    let ?g = "\<lambda>(f,n,i). (?s f n ! i, n + i * (nn - 1))"
    let ?U = "{(f,n,i). i \<le> length (?s f n) - 1}"
    let ?L = "a # concat (map snd sml)"
    let ?M = "set ?L"
    let ?m = "Suc (max_list (map label_depth ?L))"
    let ?S = "{(fs ! i,n + i * (nn - 1)) | f n i fs. ((f,n),fs) \<in> set sml \<and> i < length fs}"
    {
      fix f n i
      have "?s f n \<noteq> []"  unfolding sig_list_to_sig_map_def
        by (cases "map_of sml (f, n)", auto simp: Let_def)
      then have "(i \<le> length (?s f n) - 1) = (i < length (?s f n))"
        by (cases "?s f n", auto)
    } note len = this
    show "inj_on ?g ?U"
      unfolding inj_on_def
    proof (intro ballI, unfold len, clarify)
      fix f g n m i j
      assume i: "i < length (?s f n)"
      and    j: "j < length (?s g m)"
      and    idg: "?s f n ! i = ?s g m ! j"
      and    ids: "n + i * (nn - 1) = m + j * (nn - 1)" 
      from idg have lid: "label_depth (?s f n ! i) = label_depth (?s g m ! j)" by auto
      {
        fix f
        assume "f \<in> ?M"
        then have "label_depth f \<in> set (map label_depth ?L)" by auto 
        from max_list[OF this] have "label_depth f < ?m" by simp
      } note small = this
      {
        fix f
        have "label_depth (gen_label f ?m) \<ge> ?m" unfolding label_depth_gen_label by auto
      } note large = this
      {
        fix f n i
        assume napp: "(f,n) \<noteq> (a,nn)" and fmap: "?s f n = [fmap a nn sml f n]" and i: "i < length (?s f n)"
        then have "?s f n ! i = gen_label f ?m \<and> i = 0" and "label_depth (?s f n ! i) \<ge> ?m" using large unfolding fmap_def Let_def by auto
      } note generated = this
      {
        fix f n i
        assume app: "(f,n) = (a,nn)" and i: "i < length (?s f n)"
        then have "?s f n ! i = a \<and> i = 0" and "label_depth (?s f n ! i) < ?m" using a small[of a] by auto
      } note app = this
      {
        fix f n i
        assume napp: "(f,n) \<noteq> (a,nn)" and fmap: "?s f n \<noteq> [fmap a nn sml f n]" and i: "i < length (?s f n)"
        note fmap =  fmap[unfolded sig_list_to_sig_map_def Let_def]
        from fmap obtain fs where Some: "map_of sml (f, n) = Some fs"
          by (cases "map_of sml (f, n)", auto)
        note mem = map_of_SomeD[OF Some]
        from fmap Some have fs: "fs \<noteq> []" by (cases fs, auto)
        from Some fs have sfn: "?s f n = fs" unfolding sig_list_to_sig_map_def Let_def by auto
        from i have mem2: "?s f n ! i \<in> set fs" unfolding sfn by auto
        from mem mem2 i have inS: "(?s f n ! i,n+i * (nn - 1)) \<in> ?S" unfolding sfn by auto
        have ld: "label_depth (?s f n ! i) < ?m"
          by (rule small, insert mem mem2, force)
        from fmap mem2 Some mem i sfn
          have "\<exists> fs. ?s f n = fs \<and> i < length fs \<and> ((f,n),fs) \<in> set sml \<and> map_of sml (f, n) = Some fs" by force
        note inS and ld and this
      } note sml = this        
      have a2: "(a,nn) \<notin> ?S"
      proof
        assume "(a,nn) \<in> ?S"
        then obtain f n i fs mm where a: "a = fs ! i" and nn: "nn = n + i * (mm - 1)" and mm: "mm = nn" and mem: "((f,n),fs) \<in> set sml" and i: "i < length fs" by auto        
        have id: "(fs ! i, nn) = (fs ! i, n + ([0..<length fs] ! i) * (mm - 1))" using i unfolding nn by auto 
        from ok[THEN conjunct2, THEN conjunct1, THEN bspec[OF _ mem], simplified] show False unfolding set_zip a
          by (simp add: id, insert mm, insert i, best)
      qed
      show "f = g \<and> (n,i) = (m,j)"
      proof (cases "label_depth (?s f n ! i) < ?m")
        case False
        from app(2)[OF _ i] False have nappf: "(f,n) \<noteq> (a,nn)" by blast
        from sml(2)[OF nappf _ i] False have genf: "?s f n = [fmap a nn sml f n]" by blast
        from generated(1)[OF nappf genf i] have sfn: "?s f n ! i = gen_label f ?m" and i: "i = 0" by auto
        note False = False[unfolded lid]
        from app(2)[OF _ j] False have nappg: "(g,m) \<noteq> (a,nn)" by blast
        from sml(2)[OF nappg _ j] False have geng: "?s g m = [fmap a nn sml g m]" by blast
        from generated(1)[OF nappg geng j] have sgm: "?s g m ! j = gen_label g ?m" and j: "j = 0" by auto
        from idg[unfolded sfn sgm] gen_label_inj_f[unfolded inj_on_def] have "f = g" by auto
        then show ?thesis using ids i j by auto
      next
        case True
        from generated(2)[OF _ _ i] True have sfn: "(f,n) = (a,nn) \<or> ((f,n) \<noteq> (a,nn) \<and> ?s f n \<noteq> [fmap a nn sml f n])" by force
        from generated(2)[OF _ _ j] True[unfolded lid] have sgm: "(g,m) = (a,nn) \<or> ((g,m) \<noteq> (a,nn) \<and> ?s g m \<noteq> [fmap a nn sml g m])" by force
        from sfn
        show ?thesis
        proof
          assume fn: "(f,n) = (a,nn)"
          from app(1)[OF this i] a2 fn have nmem: "(?s f n ! i,n + i * (nn - 1)) \<notin> ?S" and i: "i = 0" by auto
          from sgm show ?thesis
          proof
            assume "(g,m) = (a,nn)"
            with fn app(1)[OF this j] i ids show ?thesis by auto
          next
            assume "((g,m) \<noteq> (a,nn) \<and> ?s g m \<noteq> [fmap a nn sml g m])"
            from sml(1)[OF _ _ j] this nmem[unfolded idg ids] show ?thesis 
              by auto
          qed
        next
          assume "(f,n) \<noteq> (a,nn) \<and> ?s f n \<noteq> [fmap a nn sml f n]"
          then have nappf: "(f,n) \<noteq> (a,nn)" and smlf: "?s f n \<noteq> [fmap a nn sml f n]" by auto
          from sml(1)[OF nappf smlf i] have finS: "(?s f n ! i, n+ i * (nn - 1)) \<in> ?S" .
          from sgm show ?thesis
          proof
            assume "(g,m) = (a,nn)"
            with finS[unfolded idg ids] app(1)[OF this j] a2 show ?thesis by auto
          next
            assume "((g,m) \<noteq> (a,nn) \<and> ?s g m \<noteq> [fmap a nn sml g m])"
            then have nappg: "(g,m) \<noteq> (a,nn)" and smlg: "?s g m \<noteq> [fmap a nn sml g m]" by auto
            from sml(1)[OF nappg smlg j] have ginS: "(?s g m ! j, m + j * (nn - 1 )) \<in> ?S" .
            from sml(3)[OF nappf smlf i]
            obtain fs where sfn: "?s f n = fs" and i: "i < length fs" and fnfs: "((f,n),fs) \<in> set sml" by auto
            from fnfs obtain I where fnfsI: "sml ! I = ((f,n),fs)" and I: "I < length sml" unfolding set_conv_nth by auto
            show ?thesis
            proof (cases "(f,n) = (g,m)")
              case True note oTrue = this
              show ?thesis
              proof (cases "nn \<le> Suc 0")
                case False
                with True ids show ?thesis by auto
              next
                case True
                then have nn1: "(nn \<le> Suc 0) = True" and nn2: "nn - Suc 0 = 0" by auto
                from ok[unfolded nn1 nn2, THEN conjunct2, THEN conjunct2, THEN conjunct2, simplified, THEN bspec[OF _ fnfs], simplified]
                have dist: "\<And> j. j < length fs \<Longrightarrow> \<forall> i < j. fs ! i \<noteq> fs ! j"
                  by simp
                from sfn sgm oTrue idg i j have idfs: "fs ! i = fs ! j" and j: "j < length fs" by auto
                have "i = j"
                proof (cases "i < j")
                  case True
                  from dist[OF j] idfs True show ?thesis by simp
                next
                  case False note oFalse = this
                  show ?thesis
                  proof (cases "j < i")
                    case True
                    from dist[OF i] idfs True show ?thesis by auto
                  next
                    case False
                    with oFalse show ?thesis by simp 
                  qed
                qed
                with oTrue show ?thesis by simp
              qed                
            next
              case False
              from sml(3)[OF nappg smlg j]
              obtain gs where sgm: "?s g m = gs" and j: "j < length gs" and gmgs: "((g,m),gs) \<in> set sml" by auto
              from gmgs obtain J where gmgsJ: "sml ! J = ((g,m),gs)" and J: "J < length sml" unfolding set_conv_nth by auto
              show ?thesis
              proof (cases "I = J")
                case False
                obtain nnn where nnn: "nnn = nn - Suc 0" by simp
                let ?f = "\<lambda>x. set ((\<lambda>((f, n), fs). map (\<lambda>(g, i). (g, n + i * nnn)) (zip fs [0..<length fs])) x)"
                let ?innA = "\<lambda> n fs. set (map (\<lambda>(g, i). (g, n + i * nnn)) (zip fs [0..<length fs]))"
                let ?innB = "\<lambda> n fs. {(fs ! i,n+ i * nnn) | i. i < length fs}"
                let ?g = "\<lambda>((f,n),fs). ?innB n fs"
                have inn: "?innA = ?innB"
                proof (rule ext, rule ext)
                  fix n fs
                  show "?innA n fs = ?innB n fs"
                  proof (simp add: set_zip, rule, (auto)[1])
                    from nth_upt[of 0 _ "length fs"]
                    have upt: "\<And> i. i < length fs \<Longrightarrow> [0..<length fs] ! i = i" by auto
                    show "{(fs ! i, n + i * nnn) | i. i < length fs} \<subseteq> (\<lambda>(g, i). (g, n + i * nnn)) ` {(fs ! i, [0..<length fs] ! i) |i. i < length fs}"
                      by (rule, clarify, simp, insert upt, force)
                  qed
                qed 
                have fg: "?f = ?g" unfolding inn[symmetric]  by (intro ext, clarify)
                from fnfs fnfsI I i have mem1: "(?s f n ! i, n + i * nnn) \<in> map ?g sml ! I" unfolding sfn nnn by auto
                from gmgs gmgsJ J j have mem2: "(?s g m ! j, m + j * nnn) \<in> map ?g sml ! J" unfolding sgm nnn by auto
                from ok[THEN conjunct1, unfolded o_def is_partition_alt is_partition_alt_def, THEN spec[of _ I], THEN spec[of _ J], unfolded nnn[symmetric] fg] I J False
                have disjoint: "map ?g sml ! I \<inter> map ?g sml ! J = {}" by auto
                from disjoint mem1 mem2 have False using idg ids nnn by auto
                then show ?thesis ..
              next
                case True
                with False fnfsI gmgsJ show ?thesis by simp 
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

datatype ('f,'l,'v)uncurry_nt_proof = Uncurry_nt_proof "(('f,'l)lab, 'v) uncurry_info" "(('f,'l)lab,'v)rules"

fun
  uncurry_nonterm_tt
where
  "uncurry_nonterm_tt I (Uncurry_nt_proof (a,sml,U,E) R') tp = uncurry_nonterm_tt_check I (a,sml,U,E) (fmap a 2) check_inj R' tp" 

lemma uncurry_nonterm_tt:
  assumes I: "tp_spec I" 
  and ok: "uncurry_nonterm_tt I i tp = return tp'"
  and nSN: "\<not> SN (qrstep (tp_ops.nfs I tp') (set (tp_ops.Q I tp')) (set (tp_ops.rules I tp')))" 
  shows "\<not> SN (qrstep (tp_ops.nfs I tp) (set (tp_ops.Q I tp)) (set (tp_ops.rules I tp)))" 
proof (cases i)
  case (Uncurry_nt_proof info R')
  obtain a sml U E where info: "info = (a,sml,U,E)" by (cases info, auto)
  from ok Uncurry_nt_proof info have ok: "uncurry_nonterm_tt_check I (a, sml, U, E) (fmap a 2) check_inj R' tp = return tp'" by simp
  show ?thesis
    by (rule uncurry_nonterm_tt_check[OF I check_inj ok nSN])
qed

fun uncurry_proc_both where 
  "uncurry_proc_both I None (a,sml,U,Eb) = uncurry_proc I (a,sml,U,Eb) (fmap a 2) check_inj"
| "uncurry_proc_both I (Some n) (a,sml,U,Eb) = uncurry_top_proc I (a,sml,U,Eb) n (fmap a n) check_inj"


lemma uncurry_proc_both:
  assumes I: "dpp_spec I"
  shows "dpp_spec.sound_proc_impl I (uncurry_proc_both I mode info P' R')"
proof -
  obtain a sml U Eb where info: "info = (a,sml,U,Eb)" by (cases info, blast)
  show ?thesis 
  proof (cases mode)
    case None
    show ?thesis unfolding info None uncurry_proc_both.simps
      by (rule uncurry_proc[OF I check_inj])
  next
    case (Some n)
    show ?thesis unfolding info Some uncurry_proc_both.simps
      by (rule uncurry_top_proc[OF I check_inj])
  qed
qed

end
end
