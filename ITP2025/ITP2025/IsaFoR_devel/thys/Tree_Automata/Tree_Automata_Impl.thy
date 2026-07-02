(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Tree_Automata_Impl
imports
  Tree_Automata_Det_Impl
  First_Order_Rewriting.Trs_Impl
begin

(* Add the notation which has been removed in Tree_Automata_Wit_Impl... *)
notation TA_rule ("_ _ \<rightarrow> _" [51, 51, 51] 52)
(* ... and remove the clashing notation *)
no_notation fun_rel_syn (infixr "\<rightarrow>" 60)

context
  notes [[typedef_overloaded]]
begin
datatype ('q, dead 'f) ta_rule_impl = TA_rule_impl 'f "'q list" 'q "'q rs" 
end

fun ta_rule_conv :: "('q, 'f) ta_rule_impl \<Rightarrow> ('q, 'f) ta_rule" where
  "ta_rule_conv (TA_rule_impl f qs q qs') = (TA_rule f qs q)"

fun conv_ta_rule :: "('q \<Rightarrow> 'q rs) \<Rightarrow> ('q, 'f) ta_rule \<Rightarrow> ('q, 'f) ta_rule_impl" where
  "conv_ta_rule eps (TA_rule f qs q) = (TA_rule_impl f qs q (eps q))"

context
  notes [[typedef_overloaded]]
begin
datatype ('q, 'f) ta_impl = TA_Impl
  (ta_final_impl: "'q rs")
  (ta_rules_impl: "('f \<times> nat, ('q,'f) ta_rule_impl list) rm")
  (ta_r_lhs_states_impl: "'q list")
  (ta_rhs_states_set: "'q rs")
  (ta_eps_impl: "('q \<times> 'q) list")
  (ta_epss_impl: "'q \<Rightarrow> 'q rs")
  (ta_epsrs_impl: "'q \<Rightarrow> 'q rs")
end

definition ta_of :: "('q :: linorder, 'f :: linorder) ta_impl \<Rightarrow> ('q, 'f) ta" where
  "ta_of TA = \<lparr>
    ta_final = set (rs.to_list (ta_final_impl TA)), 
    ta_rules = \<Union>{ta_rule_conv ` (set (rm_set_lookup (ta_rules_impl TA) fn)) | fn. True},
    ta_eps = set (ta_eps_impl TA) \<rparr>"

fun r_lhs_states_impl where "r_lhs_states_impl (TA_rule_impl f qs q qs') = qs"
fun r_rhs_impl where "r_rhs_impl (TA_rule_impl f qs q qs') = q"
fun rqss_impl where "rqss_impl (TA_rule_impl f qs q qs') = qs'"
fun r_sym_impl where "r_sym_impl (TA_rule_impl f qs q qs') = (f,length qs)"

fun ta_res_impl :: "('f \<times> nat,('q :: linorder,'f :: linorder)ta_rule_impl list)rm \<Rightarrow> ('q \<Rightarrow> 'q rs) \<Rightarrow> ('f,'q)term \<Rightarrow> 'q rs"
where "ta_res_impl TA eps (Var q) = eps q"
  | "ta_res_impl TA eps (Fun f ts) = (
        let rec = map (ta_res_impl TA eps) ts;
            n = length ts;
            rules = rm_set_lookup TA (f,n);
            arules = filter (\<lambda> rule. let qs = r_lhs_states_impl rule in Ball (set [0 ..< n]) (\<lambda> i. rs.memb (qs ! i) (rec ! i))) rules;
            qs = map (\<lambda> rule. rqss_impl rule) arules   
           in rs_Union qs)"



locale ta_inv = rm_set "ta_rules_impl TA" r_sym_impl "conv_ta_rule (ta_epss_impl TA) ` ta_rules (ta_of TA)" for
  TA :: "('q :: linorder,'f :: linorder)ta_impl" +
  fixes rel :: "'q rs \<Rightarrow> 'q rs \<Rightarrow> 'q option" and rell :: "'q rel" 
  assumes ta_rhs_states_set: "rs.\<alpha> (ta_rhs_states_set TA) = ta_rhs_states (ta_of TA)"
  and     ta_r_lhs_states_impl: "set (ta_r_lhs_states_impl TA) = ta_rhs_states (ta_of TA)"
  and     ta_epss: "\<And> q. rs.\<alpha> (ta_epss_impl TA q) = {q'. (q,q') \<in> (ta_eps (ta_of TA))^*}"
  and     ta_epsrs: "\<And> q. rs.\<alpha> (ta_epsrs_impl TA q) = {q'. (q',q) \<in> (ta_eps (ta_of TA))^*}"
  and     ta_eps: "ta_eps (ta_of TA) = set (ta_eps_impl TA)"
  and     ta_final: "rs.\<alpha> (ta_final_impl TA) = ta_final (ta_of TA)"
  and     rel: "\<And> ql qr. rel ql qr = None \<Longrightarrow> rs.\<alpha> ql \<subseteq> rell^-1 `` (rs.\<alpha> qr)"
  and     coherent: "state_coherent (ta_of TA) rell"
begin
abbreviation ta_rm_set_lookup where "ta_rm_set_lookup \<equiv> rm_set_lookup (ta_rules_impl TA)"
abbreviation TA' :: "('q,'f)ta" where "TA' \<equiv> ta_of TA"

lemma rm_set_lookup1: assumes "rule \<in> set (ta_rm_set_lookup (f,n))"
  shows "\<exists> qs q qs'. rule = (TA_rule_impl f qs q qs') \<and> 
    n = length qs \<and> rs.\<alpha> qs' = {q'. (q,q') \<in> (ta_eps TA')^*} \<and> (f qs \<rightarrow> q) \<in> ta_rules TA'"
proof -
  from assms have "r_sym_impl rule = (f,n)" and mem: "rule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'"
    using assms unfolding rm_set_lookup by auto
  then obtain qs q qs' where n: "n = length qs" and rule: "rule = TA_rule_impl f qs q qs'" by (cases rule, auto)
  from mem obtain rrule where id: "rule = conv_ta_rule (ta_epss_impl TA) rrule" and rrule: "rrule \<in> ta_rules TA'" by auto
  from id[unfolded rule] have idd: "rrule = (f qs \<rightarrow> q)" by (cases rrule, auto) 
  from id[unfolded rule idd] have "rs.\<alpha> qs' = rs.\<alpha> (ta_epss_impl TA q)" by auto
  from this[unfolded ta_epss] rrule
  show ?thesis unfolding idd rule n
    by auto
qed

lemma rm_set_lookup2: assumes "rule \<in> conv_ta_rule (ta_epss_impl TA) ` (ta_rules TA')"
  shows "rule \<in> set (ta_rm_set_lookup (r_sym_impl rule))"
  using assms unfolding rm_set_lookup
  by (cases rule, auto)

lemma rm_set_lookup3: assumes "rule \<in> conv_ta_rule (ta_epss_impl TA) ` (ta_rules TA')"
  shows "\<exists> rules. Some rules = rm.\<alpha> (ta_rules_impl TA) (r_sym_impl rule) \<and> rule \<in> set rules"
  using rm_set_lookup2[OF assms] by (auto simp: rm_set_lookup_def)


lemma ta_res_impl: 
  shows "rs.\<alpha> (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) t) = ta_res TA' t"
proof (induct t)
  case (Var x) then show ?case by (simp add: ta_epss)
next
  case (Fun f ts)
  show ?case
  proof (rule set_eqI)
    fix q
    show "(q \<in> rs.\<alpha> (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (Fun f ts))) = (q \<in> ta_res (ta_of TA) (Fun f ts))"
      (is "(q \<in> ?L) = (q \<in> ?S)")
    proof
      assume "q \<in> ?L"
      then obtain qs' rule where mem: "rule \<in> set (ta_rm_set_lookup (f,length ts))"
        and q: "rqss_impl rule = qs'"
        and q': "q \<in> rs.\<alpha> qs'"
        and args: "\<forall> i \<in> {0 ..< length ts}.
             rs.memb (r_lhs_states_impl rule ! i) (map (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)) ts ! i)"
        by (auto simp: Let_def rs.correct)
      from rm_set_lookup1[OF mem] 
      obtain qs qs'' q' where id: "rule = TA_rule_impl f qs q' qs''" and
        len: "length ts = length qs" and 
        qs'': "rs.\<alpha> qs'' = {q. (q',q) \<in> (ta_eps TA')^*}" and
        rule: "(f qs \<rightarrow> q') \<in> ta_rules TA'" by auto
      from q id have qs': "qs' = qs''" by auto
      from q'[unfolded qs' qs''] have qq': "(q',q) \<in> (ta_eps TA')^*" by simp
      show "q \<in> ?S"
      proof (unfold ta_res.simps, rule, rule exI[of _ q], rule exI[of _ q'], rule exI[of _ qs], intro conjI, simp, simp add: rule, rule qq', simp add: len, intro allI impI)
        fix i
        assume i: "i < length ts"
        then have mem: "ts ! i \<in> set ts" by auto
        from args[unfolded id, simplified] i len
        have "rs.memb (qs ! i) (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (ts ! i))" by auto
        with Fun[OF mem] i 
        show "qs ! i \<in> map (ta_res TA') ts ! i" by (simp add: rs.correct)
      qed
    next
      assume "q \<in> ?S"
      then obtain q' qs where rule: "(f qs \<rightarrow> q') \<in> ta_rules TA'"
        and len: "length qs = length ts"
        and args: "\<forall> i < length ts. qs ! i \<in> map (ta_res TA') ts ! i"
        and q: "(q',q) \<in> (ta_eps TA')^*"
        by auto
      let ?rule = "TA_rule_impl f qs q' (ta_epss_impl TA q')"
      have rrule: "?rule = conv_ta_rule (ta_epss_impl TA) (f qs \<rightarrow> q')" by auto
      have rrule: "?rule \<in> conv_ta_rule (ta_epss_impl TA) ` ta_rules TA'"
        unfolding rrule using rule by blast
      have rule: "?rule \<in> set (ta_rm_set_lookup (f,length qs))"
        using rm_set_lookup3[OF rrule]
        unfolding rm_set_lookup_def by auto
      {
                fix i
        assume i: "i < length ts"
        then have mem: "ts ! i \<in> set ts" by simp
        have "qs ! i \<in> rs.\<alpha> (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (ts ! i))"
          unfolding Fun[OF mem] using args i by auto
      } note args = this
      show "q \<in> ?L"
        by (simp add: Let_def rs.correct, intro exI conjI, rule rule[unfolded len], 
          insert args q, simp add: len, simp add: ta_epss)
    qed
  qed
qed
end



(* the following performs a brute force enumeration over
  all possible substitutions; this is a bottle-neck and an improved version is developed below:
  rule_state_compatible_eff_list *)
definition rule_state_compatible_list :: "('q :: linorder,'f :: linorder)ta_impl \<Rightarrow> ('q rs \<Rightarrow> 'q rs \<Rightarrow> 'q option)  \<Rightarrow> ('f,'v)rule \<times> 'v list \<Rightarrow> (('f,'q)rule \<times> 'q) check"
where "rule_state_compatible_list TA rel \<equiv> let rm = ta_rules_impl TA; eps = ta_epss_impl TA in (\<lambda> ((l,r),xs). 
          (check_allm (\<lambda> vec. let \<tau> = fun_of vec;
                               l\<tau> = map_vars_term \<tau> l;
                               r\<tau> = map_vars_term \<tau> r;
                               rhs = ta_res_impl rm eps r\<tau>;
                               lhs = ta_res_impl rm eps l\<tau>
                            in  (case rel lhs rhs of None \<Rightarrow> succeed | Some q \<Rightarrow> error ((l\<tau>,r\<tau>),q)))
                        (enum_vectors (ta_r_lhs_states_impl TA) xs)))"

context ta_inv
begin

lemma rule_state_compatible_list: assumes 
     wf: "vars_term r \<subseteq> vars_term l"
  and comp: "isOK(rule_state_compatible_list TA rel ((l,r),vars_term_list l))"
  shows "rule_state_compatible TA' rell (l,r)"
proof (cases "ta_rhs_states TA' = {}")
  case False
  show ?thesis
    unfolding rule_state_compatible_def 
  proof(clarify)
    fix \<tau> q
    assume q: "q \<in> ta_res TA' (map_vars_term \<tau> l)"
      and \<tau>: "\<tau> ` vars_term l \<subseteq> ta_rhs_states TA'"
    let ?Q = "ta_r_lhs_states_impl TA"
    from False have "?Q \<noteq> []" using ta_r_lhs_states_impl by auto
    from enum_vectors_complete[OF this, of "vars_term_list l"]
    obtain vec where vec: "vec \<in> set (enum_vectors ?Q (vars_term_list l))" 
      and \<tau>2: "\<And> x c. x \<in> set (vars_term_list l) \<Longrightarrow> c \<in> set ?Q \<Longrightarrow>  \<tau> x = c \<longrightarrow> fun_of vec x = c" by blast
    let ?\<tau> = "fun_of vec"
    {
      fix x
      assume x: "x \<in> vars_term l"
      with \<tau> have "\<tau> x \<in> ta_rhs_states TA'" by auto    
      from \<tau>2[unfolded set_vars_term_list ta_r_lhs_states_impl, OF x this] have "\<tau> x = ?\<tau> x"
        by simp
    } note \<tau>2 = this
    have l: "map_vars_term \<tau> l = map_vars_term ?\<tau> l"
      by (rule map_vars_term_vars_term[OF \<tau>2])
    have r: "map_vars_term \<tau> r = map_vars_term ?\<tau> r"
      by (rule map_vars_term_vars_term, insert \<tau>2 wf, auto)
    let ?R = "ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)"    
    let ?check = "rel (?R (map_vars_term (fun_of vec) l)) (?R (map_vars_term (fun_of vec) r))"
    from comp[unfolded rule_state_compatible_list_def Let_def, simplified, THEN bspec[OF _ vec]] 
    have "?check = None" by (cases ?check, auto)
    from rel[OF this, unfolded ta_res_impl] q
    show "q \<in> rell^-1 `` ta_res TA' (map_vars_term \<tau> r)" unfolding l r by auto
  qed
next
  case True
  show "rule_state_compatible TA' rell (l,r)"
    unfolding rule_state_compatible_def
  proof (clarify)
    fix \<tau> q
    assume q: "q \<in> ta_res TA' (map_vars_term \<tau> l)"
      and \<tau>: "\<tau> ` vars_term l \<subseteq> ta_rhs_states TA'"    
    show "q \<in> rell^-1 `` ta_res TA' (map_vars_term \<tau> r)"
    proof (cases l)
      case (Fun f ls)
      from q[unfolded Fun] True
      show ?thesis unfolding ta_rhs_states_def by auto
    next
      case (Var x)
      from \<tau>[unfolded Var ta_rhs_states_def]  True
      show ?thesis unfolding ta_rhs_states_def by simp
    qed
  qed    
qed
end

(* TODO: integrate (here and in ta_match) an optimization of concat / fun_merge that deals with 
   non-linear terms. Currently conflicts might occur (x / a and x / b) and duplicates may occur (x / a 
   and x / a). This is only important for efficiency, it will not effect power *)
fun ta_match_pre_impl :: "('f \<times> nat,('q :: linorder,'f :: linorder)ta_rule_impl list)rm \<Rightarrow> 'q rs \<Rightarrow> ('q \<Rightarrow> 'q rs) \<Rightarrow> ('f,'v)term \<Rightarrow> 'q set \<Rightarrow> ('v \<times> 'q)list set"
  where "ta_match_pre_impl TA Qsig eps (Var x) Q = { [(x,q')] | q' q. q \<in> Q \<and> q' \<in> rs.\<alpha> (eps q) \<and> q' \<in> rs.\<alpha> Qsig}"
   | "ta_match_pre_impl TA Qsig eps (Fun f ts) Q = { concat \<sigma>s | \<sigma>s qs' qs q' q. 
          (TA_rule_impl f qs q' qs') \<in> set (rm_set_lookup TA (f,length ts)) \<and> 
          q \<in> Q \<and>
          q' \<in> rs.\<alpha> (eps q) \<and> 
          length \<sigma>s = length ts \<and>
          (\<forall> i < length ts. \<sigma>s ! i \<in> ta_match_pre_impl TA Qsig eps (ts ! i) {qs ! i}) }"

context ta_inv
begin
lemma ta_match_pre_impl: "ta_match_pre_impl (ta_rules_impl TA) Qsig (ta_epsrs_impl TA) = ta_match TA' (rs.\<alpha> Qsig)"
proof (rule sym, intro ext)
  fix t Q
  show "ta_match TA' (rs.\<alpha> Qsig) t Q = ta_match_pre_impl (ta_rules_impl TA) Qsig (ta_epsrs_impl TA) t Q"
  proof (induct t arbitrary: Q)
    case (Var x Q)
    show ?case by (auto simp add: ta_epsrs rs.correct)
  next
    case (Fun f ts Q)
    let ?l = "\<lambda> \<sigma>s qs i. \<sigma>s ! i \<in> ta_match_pre_impl (ta_rules_impl TA) Qsig (ta_epsrs_impl TA) (ts ! i) {qs ! i}"
    let ?r = "\<lambda> \<sigma>s qs i. \<sigma>s ! i \<in> ta_match TA' (rs.\<alpha> Qsig) (ts ! i) {qs ! i}"
    {
      fix qs \<sigma>s
      {
        fix i
        assume i: "i < length ts"
        then have "ts ! i \<in> set ts" by auto
        from Fun[OF this, of "{qs ! i}"]
        have "?l \<sigma>s qs i = ?r \<sigma>s qs i" by auto
      } 
      then have "(\<forall> i < length ts. ?l \<sigma>s qs i) = (\<forall> i < length ts. ?r \<sigma>s qs i)" by auto
    } note rec = this   
    let ?P = "\<lambda> \<sigma>s qs. \<forall> i < length ts. ?l \<sigma>s qs i"
    show ?case (is "?L = ?R")
    proof -
      {
        fix \<sigma>
        assume "\<sigma> \<in> ?L"
        then obtain \<sigma>s qs q' q
          where \<sigma>: "\<sigma> = concat \<sigma>s" and rule: "f qs \<rightarrow> q' \<in> ta_rules TA'" and q: "q \<in> Q" "(q', q) \<in> (ta_eps TA')\<^sup>*" 
          and len: "length \<sigma>s = length ts" "length qs = length ts" and P: "?P \<sigma>s qs" using rec by auto
        have rule: "TA_rule_impl f qs q' (ta_epss_impl TA q') \<in> set (ta_rm_set_lookup (f, length ts))" 
          unfolding rm_set_lookup
          by (rule, rule conjI, rule, insert rule len, auto)
        have "\<sigma> \<in> ?R" unfolding ta_match_pre_impl.simps
          by (rule, intro exI conjI, rule \<sigma>, rule rule, rule q(1), insert q(2) len P, auto simp: rec ta_epsrs)
      }
      moreover
      {
        fix \<sigma>
        assume "\<sigma> \<in> ?R"
        then obtain \<sigma>s qs' qs q' q 
        where \<sigma>: "\<sigma> = concat \<sigma>s" and rule: "TA_rule_impl f qs q' qs' \<in> set (ta_rm_set_lookup (f, length ts))"
              and q: "q \<in> Q" "q' \<in> {q'. (q', q) \<in> (ta_eps TA')\<^sup>*}"
              and len: "length \<sigma>s = length ts" and P: "?P \<sigma>s qs" by (auto simp: ta_epsrs)
        from rm_set_lookup1[OF rule] have rule: "f qs \<rightarrow> q' \<in> ta_rules TA'" and len2: "length qs = length ts" by auto
        have "\<sigma> \<in> ?L" unfolding ta_match.simps
          by (rule, intro exI conjI, rule \<sigma>, rule rule, rule q(1), insert len len2 q(2) P, auto simp: rec)
      }
      ultimately
      show ?thesis by blast
    qed
  qed
qed
end

lemma ta_match_code_Var: "ta_match TA Qsig (Var x) Q = (\<lambda> q'. [(x,q')]) ` {q' \<in> ((ta_eps TA)^-1)^* `` Q. q' \<in> Qsig}"
  unfolding ta_match.simps
  by (auto simp: rtrancl_converse)


lemma ta_match_code_Fun: "ta_match TA Qsig (Fun f ts) Q = 
   (let n = length ts;
       rls = { rule \<in> ta_rules TA. r_sym rule = (f,n) \<and> (\<exists> q' \<in> (ta_eps TA)^* `` {r_rhs rule}. q' \<in> Q) }
   in  \<Union> ((\<lambda> rule. case rule of TA_rule g qs q' \<Rightarrow> 
         concat ` listset (map (\<lambda> (tsi,qsi). ta_match TA Qsig tsi {qsi}) (zip ts qs))
         ) ` rls))" (is "?L = ?R")
proof -
  let ?n = "length ts"
  let ?rls = "{ rule \<in> ta_rules TA. r_sym rule = (f,?n) \<and> (\<exists> q' \<in> (ta_eps TA)^* `` {r_rhs rule}. q' \<in> Q) }"
  {
    fix \<sigma>
    assume "\<sigma> \<in> ?L"
    from this
    obtain \<sigma>s qs q' q 
      where \<sigma>: "\<sigma> = concat \<sigma>s" and rule: "f qs \<rightarrow> q' \<in> ta_rules TA"
      and q: "q \<in> Q" "(q', q) \<in> (ta_eps TA)^*"
      and len: "length qs = ?n" "length \<sigma>s = ?n"
      and rec: "\<And> i. i < ?n \<Longrightarrow> \<sigma>s ! i \<in> ta_match TA Qsig (ts ! i) {qs ! i}" by auto
    have rule: "(f qs \<rightarrow> q') \<in> ?rls"
      by (rule, intro conjI, rule rule, simp add: len, rule, rule q, insert q, auto)
    have "\<sigma> \<in> ?R"
      unfolding Let_def \<sigma>
    proof (rule, rule imageI[OF rule], unfold ta_rule.simps, rule imageI)
      show "\<sigma>s \<in> listset (map (\<lambda>(tsi, qsi). ta_match TA Qsig tsi {qsi}) (zip ts qs))"
        unfolding listset using len rec by auto
    qed
  }
  moreover
  {
    fix \<sigma>
    assume "\<sigma> \<in> ?R"
    then obtain rule where rls: "rule \<in> ?rls" 
      and mem: "\<sigma> \<in> (case rule of g qs \<rightarrow> q' \<Rightarrow> concat ` listset (map (\<lambda>(tsi, qsi). ta_match TA Qsig tsi {qsi}) (zip ts qs)))" by auto
    from rls obtain qs q' where rule: "rule = (f qs \<rightarrow> q')" by (cases rule, auto)
    from rls rule obtain q where rule': "(f qs \<rightarrow> q') \<in> ta_rules TA" and len: "length qs = length ts"
      and eps: "(q',q) \<in> (ta_eps TA)\<^sup>*" and q: "q \<in> Q" by auto
    from mem[unfolded rule]
    obtain \<sigma>s where \<sigma>: "\<sigma> = concat \<sigma>s" and \<sigma>s: "\<sigma>s \<in> listset (map (\<lambda>(tsi, qsi). ta_match TA Qsig tsi {qsi}) (zip ts qs))" by auto
    have "\<sigma> \<in> ?L" unfolding ta_match.simps
      by (rule, intro exI conjI, rule \<sigma>, rule rule', rule q, insert eps len \<sigma>s[unfolded listset], auto)
  }
  ultimately show ?thesis by blast
qed

declare ta_match_code_Var[code] ta_match_code_Fun[code]

fun ta_match_impl :: "('f \<times> nat,('q :: linorder,'f :: linorder)ta_rule_impl list)rm \<Rightarrow> 'q rs \<Rightarrow> ('q \<Rightarrow> 'q rs) \<Rightarrow> ('f,'v)term \<Rightarrow> 'q list \<Rightarrow> ('v :: linorder \<times> 'q)list rs"
  where "ta_match_impl TA Qsig eps (Var x) Q = rs.from_list (map (\<lambda>q'. [(x,q')]) (rs.to_list (rs.inter (rs_Union (map eps Q)) Qsig)))" 
   | "ta_match_impl TA Qsig eps (Fun f ts) Q = (let 
          n = length ts;
          rules = rm_set_lookup TA (f, n);
          ep = rs_Union (map eps Q);
          f = (\<lambda> rule. rs.from_list (case rule of TA_rule_impl _ qs q' qs' \<Rightarrow>
                 (if rs.memb q' ep then 
                   (let rec = map (\<lambda> (tsi,qsi). rs.to_list (ta_match_impl TA Qsig eps tsi [qsi])) (zip ts qs)
                     in map concat (concat_lists rec))
                 else [])))
        in rs_Union (map f rules))" 

definition ta_match'_impl :: "('f \<times> nat,('q :: linorder,'f :: linorder)ta_rule_impl list)rm \<Rightarrow> 'q rs \<Rightarrow> ('q \<Rightarrow> 'q rs) \<Rightarrow> 'q list \<Rightarrow> ('f,'v)term \<Rightarrow> ('v :: linorder \<times> 'q)list rs" where
  "ta_match'_impl TA Qsig eps rhs t = ta_match_impl TA Qsig eps t rhs" 

context ta_inv
begin
lemma ta_match_impl_conv_pre: "rs.\<alpha> (ta_match_impl (ta_rules_impl TA) Qsig eps t Q) = ta_match_pre_impl (ta_rules_impl TA) Qsig eps t (set Q)"
proof (induct t arbitrary: Q)
  case (Var x)
  then show ?case by (auto simp: rs.correct)
next
  case (Fun f ts Q)
  let ?TA = "ta_rules_impl TA"
  show ?case (is "?I = ?P")
  proof -
    {
      fix \<sigma>
      assume "\<sigma> \<in> ?P"
      from this
      obtain \<sigma>s qs qs' q' q where \<sigma>: "\<sigma> = concat \<sigma>s"
        and rule: "TA_rule_impl f qs q' qs' \<in> set (ta_rm_set_lookup (f, length ts))"
        and q: "q \<in> set Q"
        and q'q: "q' \<in> rs.\<alpha> (eps q)"
        and len1: "length \<sigma>s = length ts"
        and rec: "\<And> i. i < length ts \<Longrightarrow> \<sigma>s ! i \<in> ta_match_pre_impl ?TA Qsig eps (ts ! i) {qs ! i}" by auto
      from rm_set_lookup1[OF rule] have len2: "length qs = length ts" by auto
      from q'q q have q'q: "rs.memb q' (rs_Union (map eps Q))" by (auto simp: rs.correct)
      have " \<exists>a\<in>set (ta_rm_set_lookup (f, length ts)).
       \<exists>uu q' qs.
          (\<exists> f. TA_rule_impl f qs q' uu = a) \<and>
          rs.memb q' (rs_Union (map eps Q)) \<and>
          concat \<sigma>s
          \<in> concat `
            {as. length as = min (length ts) (length qs) \<and>
                 (\<forall>i. i < length ts \<and> i < length qs \<longrightarrow>
                      as ! i \<in> rs.\<alpha> (ta_match_impl ?TA Qsig eps (ts ! i) [qs ! i]))} "
      proof (rule bexI[OF _ rule], intro exI conjI, rule refl, rule q'q, rule, rule refl, rule,
        unfold len1 len2, intro conjI allI impI allI, simp)
        fix i
        assume "i < length ts \<and> i < length ts" 
        then have i: "i < length ts" by auto
        then have "ts ! i \<in> set ts" by auto
        from Fun[OF this] rec[OF i] show "\<sigma>s ! i \<in> rs.\<alpha> (ta_match_impl ?TA Qsig eps (ts ! i) [qs ! i])" by auto
      qed
      then have "\<sigma> \<in> ?I" unfolding ta_match_impl.simps Let_def set_concat rs.correct \<sigma>
        by (simp add: rs.correct)
    }
    moreover
    {
      fix \<sigma>
      assume "\<sigma> \<in> ?I"
      from this
      obtain rule :: "('q,'f)ta_rule_impl" and g and \<sigma>s :: "'q \<Rightarrow> 'q" and qs' qs q' where
         rule: "TA_rule_impl g qs q' qs' \<in> set (ta_rm_set_lookup (f, length ts))"
        and q': "rs.memb q' (rs_Union (map eps Q))"
        and \<sigma>: "\<sigma> \<in> concat ` {\<sigma>s. length \<sigma>s = min (length ts) (length qs) \<and> (\<forall> i. i < length ts \<and> i < length qs \<longrightarrow> \<sigma>s ! i \<in> rs.\<alpha> (ta_match_impl ?TA Qsig eps (ts ! i) [qs ! i]))}" by (simp add: rs.correct) blast+
      from rm_set_lookup1[OF rule] have gf: "g = f" and len2: "length qs = length ts" by auto
      from \<sigma> obtain \<sigma>s where \<sigma>: "\<sigma> = concat \<sigma>s" and len1: "length \<sigma>s = length ts" and rec: "\<And> i. i < length ts \<Longrightarrow> \<sigma>s ! i \<in> rs.\<alpha> (ta_match_impl ?TA Qsig eps (ts ! i) [qs ! i])" unfolding len2 by auto
      from q' obtain q where q: "q \<in> set Q" and q': "q' \<in> rs.\<alpha> (eps q)" by (auto simp: rs.correct)
      have "\<sigma> \<in> ?P" unfolding ta_match_pre_impl.simps
      proof (rule, intro exI conjI, rule \<sigma>, rule rule[unfolded gf], rule q, rule q', rule len1, 
        intro allI impI)
        fix i
        assume i: "i < length ts" 
        then have "ts ! i \<in> set ts" by auto
        from Fun[OF this] rec[OF i] show "\<sigma>s ! i \<in> ta_match_pre_impl ?TA Qsig eps (ts ! i) {qs ! i}" by auto
      qed
    }
    ultimately show ?thesis by blast
  qed
qed        

lemma ta_match_impl: "rs.\<alpha> (ta_match_impl (ta_rules_impl TA) Qsig (ta_epsrs_impl TA) t Q) = ta_match TA' (rs.\<alpha> Qsig) t (set Q)"
  unfolding ta_match_impl_conv_pre 
  unfolding ta_match_pre_impl ..

lemma ta_match'_impl: "rs.\<alpha> (ta_match'_impl (ta_rules_impl TA) (ta_rhs_states_set TA) (ta_epsrs_impl TA) (rs.to_list (ta_rhs_states_set TA)) t) = ta_match' TA' (ta_rhs_states TA') t"
  unfolding ta_match'_impl_def
  unfolding ta_match_impl ta_match'_def
  by (auto simp: ta_rhs_states_set rs.correct)
end

declare ta_match_impl.simps[simp del]

fun rule_state_compatible_eff_list :: "('q :: linorder,'f :: linorder)ta_impl 
  \<Rightarrow> ('q rs \<Rightarrow> 'q rs \<Rightarrow> 'q option)
  \<Rightarrow> ('f,'v :: linorder)rule 
  \<Rightarrow> (('f,'q)rule \<times> 'q) check"
where "rule_state_compatible_eff_list TA rel =  
           (let rm = ta_rules_impl TA; 
                eps = ta_epss_impl TA;
                eps' = ta_epsrs_impl TA;
                ta_res' = ta_res_impl rm eps;
                rhs_rbt = ta_rhs_states_set TA;
                rhs = rs.to_list rhs_rbt
             in (\<lambda> (l,r). check_allm (\<lambda> \<sigma>. 
                       let \<sigma>' = fun_of \<sigma>;
                           l\<sigma> = map_vars_term \<sigma>' l;
                           r\<sigma> = map_vars_term \<sigma>' r;
                           qsl = ta_res' l\<sigma>;
                           qsr = ta_res' r\<sigma>
                         in (case rel qsl qsr of None \<Rightarrow> succeed | Some q' \<Rightarrow> error ((l\<sigma>,r\<sigma>),q'))
                   ) (rs.to_list (ta_match'_impl rm rhs_rbt eps' rhs l))))
                 " 

lemma (in ta_inv) rule_state_compatible_eff_list: assumes 
    ok: "isOK(rule_state_compatible_eff_list TA rel (l,r))"
  and vars: "vars_term r \<subseteq> vars_term l"
  shows "rule_state_compatible TA' rell (l,r)"
proof (rule rule_state_compatible_eff[OF vars refl])
  show "rule_state_compatible_eff TA' (ta_rhs_states TA') rell (l, r)" 
    unfolding rule_state_compatible_eff.simps
  proof (intro allI impI, clarify)
    fix \<sigma> q
    assume match: "\<sigma> \<in> ta_match' TA' (ta_rhs_states TA') l" and q: "q \<in> ta_res TA' (map_vars_term (fun_of \<sigma>) l)"
    let ?call = "ta_match'_impl (ta_rules_impl TA) (ta_rhs_states_set TA) (ta_epsrs_impl TA) (rs.to_list (ta_rhs_states_set TA)) l"
    from match[unfolded ta_match'_impl[symmetric]]
    have \<tau>1: "\<sigma> \<in> rs.\<alpha> ?call" by auto
    let ?e = "ta_epss_impl TA q"
    let ?rl = "\<lambda> x. ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (map_vars_term (fun_of x) l)"
    let ?rr = "\<lambda> x. ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (map_vars_term (fun_of x) r)"
    from ok[unfolded Fun rule_state_compatible_eff_list.simps Let_def] rule
    have " \<And>x. x\<in> rs.\<alpha> ?call \<Longrightarrow>
      isOK (case rel (?rl x) (?rr x) of
         None \<Rightarrow> Inr () | Some q' \<Rightarrow> Inl ((map_vars_term (fun_of x) l, map_vars_term (fun_of x) r), q'))" 
      unfolding Fun by (auto simp: rs.correct)
    from this[OF \<tau>1]
    have "rel (?rl \<sigma>) (?rr \<sigma>) = None"
      by (cases "rel (?rl \<sigma>) (?rr \<sigma>)", auto)
    from rel[OF this, unfolded  ta_res_impl] q
    show "q \<in> rell\<inverse> `` ta_res TA' (map_vars_term (fun_of \<sigma>) r)" by auto
  qed
qed

fun ta_res_impl_all :: "'q rs \<Rightarrow> ('f \<times> nat,('q :: linorder,'f :: linorder)ta_rule_impl list)rm \<Rightarrow> ('f,'v)term \<Rightarrow> 'q rs"
where "ta_res_impl_all Q TA (Var _) = Q"
  | "ta_res_impl_all Q TA (Fun f ts) = (
        let rec = map (ta_res_impl_all Q TA) ts;
            n = length ts;
            rules = rm_set_lookup TA (f,n);
            arules = filter (\<lambda> rule. let qs = r_lhs_states_impl rule in Ball (set [0 ..< n]) (\<lambda> i. rs.memb (qs ! i) (rec ! i))) rules;
            qs = map (\<lambda> rule. rqss_impl rule) arules   
           in rs_Union qs)"

context ta_inv
begin
lemma ta_res_impl_all: assumes "\<tau> ` vars_term t \<subseteq> ta_rhs_states TA'"
  shows "rs.\<alpha> (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA) (map_vars_term \<tau> t)) 
    \<subseteq> rs.\<alpha> (ta_res_impl_all (ta_rhs_states_set TA) (ta_rules_impl TA) t)"
  using assms
proof (induct t)
  case (Var q)
  with assms  have q: "\<tau> q \<in> ta_rhs_states TA'" by auto
  { 
    fix q'
    assume q': "(\<tau> q, q') \<in> (ta_eps TA')^*"
    from q q' 
    have "q' \<in> ta_rhs_states TA'" unfolding ta_rhs_states_def
      by (auto intro!: bexI)
  }
  then show ?case by (auto simp: ta_epss ta_rhs_states_set)
next
  case (Fun f ts)
  {
    fix rule :: "('q,'f)ta_rule_impl"
    assume 
      args: "\<forall> i \<in> {0..<length ts}. rs.memb (r_lhs_states_impl rule ! i) 
        (map (ta_res_impl (ta_rules_impl TA) (ta_epss_impl TA)) (map (map_vars_term \<tau>) ts) ! i)"
    have args: "\<forall> i \<in> {0..<length ts}. rs.memb (r_lhs_states_impl rule ! i)  
      (map (ta_res_impl_all (ta_rhs_states_set TA) (ta_rules_impl TA)) ts ! i)" (is "\<forall> i \<in> _. ?c i")
    proof -
      {
        fix i
        assume i: "i < length ts"
        from i have mem: "ts ! i \<in> set ts" by auto
        with Fun(2) have "\<tau> ` vars_term (ts ! i) \<subseteq> ta_rhs_states TA'" by auto
        from Fun(1)[OF mem this] args i
        have "?c i" by (auto simp: rs.correct)
      }
      then show ?thesis by auto
    qed
  }
  then show ?case by (auto simp: Let_def rs.correct)
qed
end

definition rule_state_compatible_heuristic :: "('q :: linorder,'f :: linorder)ta_impl \<Rightarrow> ('f,'v :: linorder)term \<Rightarrow> bool" where
"rule_state_compatible_heuristic TA l \<equiv> rs.isEmpty (ta_res_impl_all (ta_rhs_states_set TA) (ta_rules_impl TA) l)"

context ta_inv
begin

lemma rule_state_compatible_heuristic_subteq: assumes compat: "rule_state_compatible_heuristic TA u"
    and subt: "l \<unrhd> u"
  shows "rule_state_compatible TA' rell (l,r)"
proof -
  {
    fix \<tau>
    assume \<tau>: "\<tau> ` vars_term l \<subseteq> ta_rhs_states TA'"
    {
      fix x
      assume "x \<in> vars_term u"
      from subt supteq_Var[OF this] have "l \<unrhd> Var x" by (rule supteq_trans)
      from subteq_Var_imp_in_vars_term[OF this] have "x \<in> vars_term l" .
    }
    with \<tau> have \<tau>u: "\<tau> ` vars_term u \<subseteq> ta_rhs_states TA'" by auto
    from assms[unfolded rule_state_compatible_heuristic_def]
    have empty: "rs.\<alpha> (ta_res_impl_all (ta_rhs_states_set TA) (ta_rules_impl TA) u) = {}" by (simp add: rs.correct)
    from ta_res_impl_all[OF \<tau>u] empty
    have empty: "ta_res TA' (map_vars_term \<tau> u) = {}" 
      unfolding ta_res_impl by auto
    from subt obtain C where l: "l = C\<langle>u\<rangle>" ..
    have "ta_res TA' (map_vars_term \<tau> l) = {}"
      unfolding l
    proof (induct C)
      case (More f bef C aft)
      { 
        fix qs
        have "\<And> g. \<exists> i < Suc (length bef + length aft). qs ! i \<notin> (map g bef @ ta_res TA' (map_vars_term \<tau> C\<langle>u\<rangle>) # map g aft) ! i"
          by (rule exI[of _ "length bef"], simp add: nth_append, insert More, auto)
      }
      then show ?case by (auto simp: o_def)
    qed (insert empty, auto)
  }
  then show ?thesis
    unfolding rule_state_compatible_def by auto
qed
end


definition state_compatible_list :: "('q :: linorder,'f :: linorder)ta_impl 
  \<Rightarrow> ('q rs \<Rightarrow> 'q rs \<Rightarrow> 'q option)
  \<Rightarrow> (('f,'v)rule \<times> 'v list)list \<Rightarrow> (('f,'v)rule \<times> ('f,'q)rule \<times> 'q) check"
where "state_compatible_list TA rel R \<equiv> let check = rule_state_compatible_list TA rel in
     check_allm (\<lambda> lr. check lr <+? (\<lambda> lq. (fst lr,lq))) R"

lemma (in ta_inv) state_compatible_list: assumes wf_trs: "\<And> l r. (l,r) \<in> fst ` set R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and vars: "\<And> l r xs. ((l,r),xs) \<in> set R \<Longrightarrow> xs = vars_term_list l"
  and comp: "isOK(state_compatible_list TA rel R)"
  shows "state_compatible TA' rell (fst ` set R)" 
proof -
  {
    fix l r xs
    assume rule: "((l,r),xs) \<in> set R"
    from comp[unfolded state_compatible_list_def Let_def]
      rule have comp: "isOK(rule_state_compatible_list TA rel ((l,r),xs))"
      by auto
    from rule_state_compatible_list[OF wf_trs comp[unfolded vars[OF rule]]] rule
    have "rule_state_compatible TA' rell (l,r)" by force
  }
  then show ?thesis unfolding state_compatible_def 
    by force
qed

definition state_compatible_eff_list :: 
  "('q :: linorder,'f :: linorder)ta_impl 
  \<Rightarrow> ('q rs \<Rightarrow> 'q rs \<Rightarrow> 'q option)
  \<Rightarrow> ('f,'v :: linorder)rule list \<Rightarrow> (('f,'v)rule \<times> ('f,'q)rule \<times> 'q) check"
where "state_compatible_eff_list TA rel R \<equiv> let check = rule_state_compatible_eff_list TA rel in
     check_allm (\<lambda> lr. check lr <+? (\<lambda> lq. (lr,lq))) R"

lemma (in ta_inv) state_compatible_eff_list: assumes wf_trs: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l"
  and comp: "isOK(state_compatible_eff_list TA rel R)"
  shows "state_compatible TA' rell (set R)" 
proof -
  {
    fix l r 
    assume rule: "(l,r) \<in> set R"
    from comp[unfolded state_compatible_eff_list_def Let_def]
      rule have comp: "isOK(rule_state_compatible_eff_list TA rel (l,r))"
      by auto
    from rule_state_compatible_eff_list[OF comp wf_trs[OF rule]]
    have "rule_state_compatible TA' rell (l,r)" .
  }
  then show ?thesis unfolding state_compatible_def 
    by force
qed

definition ta_contains_aux_impl :: "('f \<times> nat) list \<Rightarrow> 'q list \<Rightarrow> ('q :: linorder,'f :: linorder)ta_impl \<Rightarrow> 'q set \<Rightarrow> ('f,'q)term check"
  where "ta_contains_aux_impl F qs TA Q \<equiv> 
       do { 
         let fin = ta_final_impl TA;
         let look = rm_set_lookup (ta_rules_impl TA);
         let eps = ta_epss_impl TA;
         check_allm (\<lambda> (f,n). let rules = look (f,n) 
              in (check_all (\<lambda> qs'. Bex (set rules) (\<lambda> rule. r_lhs_states_impl rule = qs' 
                \<and> (let qq = rqss_impl rule in rs.bex qq (\<lambda>q. q \<in> Q))))
          (concat_lists (replicate n qs))) <+? (\<lambda>qs'. Fun f (map Var qs'))) F            
          } "


definition ta_contains_impl :: "('f \<times> nat) list \<Rightarrow> ('f \<times> nat)list \<Rightarrow>
  ('q :: linorder,'f :: linorder)ta_impl \<Rightarrow> 'q list \<Rightarrow> ('f,'q)term check" where
  "ta_contains_impl F G TA qs \<equiv> do {
    ta_contains_aux_impl F qs TA (set qs);
    ta_contains_aux_impl G qs TA (rs.\<alpha> (ta_final_impl TA))}"

context ta_inv
begin
(* I believe that also the other direction is correct, but currently this
   is not needed *)
lemma ta_contains_aux_impl: 
  assumes contain: "isOK(ta_contains_aux_impl F qs TA Q)"
  shows "ta_contains_aux (set F) (set qs) TA' Q"
proof -
  note contain = contain[unfolded ta_contains_aux_impl_def Let_def set_concat_lists, simplified, simplified rs.correct, simplified]
  show ?thesis unfolding ta_contains_aux_def
  proof (intro allI impI)
    fix f qs'
    assume "(f,length qs') \<in> set F \<and> set qs' \<subseteq> set qs"
    then have f: "(f,length qs') \<in> set F" and i: "\<forall> i < length qs'. qs' ! i \<in> set qs" unfolding set_conv_nth[of qs'] by auto
    from contain[rule_format, OF f, simplified, rule_format, of qs', OF conjI[OF refl i]] 
     obtain rule q where q: "q \<in> Q" and rule: "rule \<in> set (ta_rm_set_lookup (f, length qs'))" 
      and q2: "q \<in> rs.\<alpha> (rqss_impl rule)" and qs': "r_lhs_states_impl rule = qs'" by (auto simp: rs.correct)
    from rm_set_lookup1[OF rule] 
    obtain qsr1 qr qsr2 where rule: "rule = TA_rule_impl f qsr1 qr qsr2"
      and len: "length qs' = length qsr1"
      and eps: "rs.\<alpha> qsr2 = {q'. (qr,q') \<in> (ta_eps TA')^*}"
      and rrule: "(f qsr1 \<rightarrow> qr) \<in> ta_rules TA'" by auto
    from rule qs' have qs': "qs' = qsr1" by auto
    show "\<exists> q q'. (f qs' \<rightarrow> q) \<in> ta_rules TA' \<and> q' \<in> Q \<and> (q,q') \<in> (ta_eps TA')^*"
      by (intro exI conjI, unfold qs', rule rrule, rule q, insert q2[unfolded rule] eps, auto)
  qed
qed

lemma ta_contains_impl: 
  assumes contain: "isOK(ta_contains_impl F G TA qs)"
  shows "ta_contains (set F) (set G) TA' (set qs)"
proof -
  from contain[unfolded ta_contains_impl_def, simplified]
  have 1: "isOK (ta_contains_aux_impl F qs TA (set qs))"
    and 2: "isOK (ta_contains_aux_impl G qs TA (rs.\<alpha> (ta_final_impl TA)))" by auto
  from ta_contains_aux_impl[OF 1] have 1: "ta_contains_aux (set F) (set qs) TA' (set qs)" .
  from ta_contains_aux_impl[OF 2] have 2: "ta_contains_aux (set G) (set qs) TA' (rs.\<alpha> (ta_final_impl TA))" .
  from 1 2 show ?thesis unfolding ta_contains_def
    by (auto simp: ta_final)
qed
end


datatype ('q,'f)tree_automaton = Tree_Automaton "'q list" (ta_rules_impl': "('q,'f)ta_rule list") "('q \<times> 'q)list"
datatype ('q) ta_relation = Decision_Proc_Old | Decision_Proc | Id_Relation | Some_Relation "('q \<times> 'q) list"

fun relation_of :: "'q ta_relation \<Rightarrow> 'q rel" where
  "relation_of (Some_Relation rel) = set rel"
| "relation_of Id_Relation = Id"
| "relation_of Decision_Proc = Id"
| "relation_of Decision_Proc_Old = Id"

fun rel_checker :: "'q ta_relation \<Rightarrow> ('q :: linorder) rs \<Rightarrow> 'q rs \<Rightarrow> 'q option" where 
  "rel_checker (Some_Relation rel) = (\<lambda> lhs rhs. let rlist = rs.to_list rhs in case (check_allm 
     (\<lambda> l. check (\<exists> r \<in> set rlist. (l,r) \<in> set rel) l) (rs.to_list lhs)) of Inl l \<Rightarrow> Some l | Inr _ \<Rightarrow> None)"
| "rel_checker Id_Relation = rs_subset"
| "rel_checker Decision_Proc = rs_subset"
| "rel_checker Decision_Proc_Old = rs_subset"

lemma rel_checker:
  assumes "rel_checker rel lhs rhs = None" 
  shows "rs.\<alpha> lhs \<subseteq> (relation_of rel)^-1 `` (rs.\<alpha> rhs)"
proof (cases rel)
  case (Some_Relation rell)
  {
    assume "forallM (\<lambda>l. check (\<exists>r\<in>rs.\<alpha> rhs. (l, r) \<in> set rell) l) (rs.to_list lhs) = Inr ()" (is "?l = _")
    then have "isOK(?l)" by (cases ?l, auto)
    from this[simplified] have ?thesis by (auto simp: rs.correct Some_Relation)
  }
  with assms show ?thesis unfolding Some_Relation  
    by (auto split: option.splits sum.splits simp: rs.correct)
qed (insert assms, auto)

fun ta_of_ta :: "('q,'f)tree_automaton \<Rightarrow> ('q,'f)ta"
  where "ta_of_ta (Tree_Automaton fin rules eps) = 
  \<lparr> ta_final = set fin,
    ta_rules = set rules,
    ta_eps   = set eps
  \<rparr>"


fun check_coherent_rule :: "('q :: {showl,linorder} \<Rightarrow> 'q list) \<Rightarrow> ('q \<times> 'q)rs \<Rightarrow> ('q,'f :: showl)ta_rule list \<Rightarrow> ('q,'f)ta_rule \<Rightarrow> showsl check" where
  "check_coherent_rule iter rel rules (TA_rule f qs q)  = 
      check_allm (\<lambda> i. 
        let qi = qs ! i in 
        check_allm (\<lambda> qi'. 
          let qs' = qs[ i := qi'] in
          check (filter (\<lambda> rule. case rule of 
            TA_rule g qs'' q' \<Rightarrow> f = g \<and> qs' = qs'' \<and> rs.memb (q,q') rel) rules \<noteq> [] ) 
            (showsl_lit (STR ''rule '') \<circ> showsl f \<circ> showsl_lit (STR ''('') \<circ> showsl_list qs \<circ> showsl_lit (STR '') -> '') \<circ> showsl q \<circ> 
             showsl_lit (STR '' with '') \<circ> showsl (Suc i) \<circ> showsl_lit (STR ''. argument decreased to '') \<circ> showsl qi' \<circ>
             showsl_lit (STR '' has no counterpart'')) 
        ) (iter qi)
      ) [0 ..< length qs]"

(* TODO: currently ep^+ is computed quite inefficiently! *)
fun check_coherent :: "('q :: {linorder,showl},'f :: showl)tree_automaton \<Rightarrow> 'q ta_relation \<Rightarrow> showsl check" where
  "check_coherent (Tree_Automaton fin rules eps) (Some_Relation rel) = do {
    let iter = (\<lambda> q. map snd (filter (\<lambda> (a,b). a = q) rel));
    let rs = rs.from_list rel;
    let ep = set eps;
    let rell = (set rel)^-1;
    check_subseteq (concat (map iter fin)) fin
      <+? (\<lambda> q. showsl q \<circ> showsl_lit (STR '' is in relation to a final state, but not a final state itself''));
    check_allm (check_coherent_rule iter rs rules) rules;
    check (rell O ep \<subseteq> (ep^+ O rell) \<union> rell) (showsl_lit (STR ''problem in coherence of epsilon rules''))
  }"
| "check_coherent _ _ = succeed"

lemma check_coherent[simp]: "isOK(check_coherent TA rel) = (state_coherent (ta_of_ta TA) (relation_of rel))" (is "?l = ?r")
proof (cases rel)
  case (Some_Relation rel) note rel = this
  obtain fin rules eps where ta: "TA = Tree_Automaton fin rules eps" by (cases TA, auto)
  let ?TA = "\<lparr> ta_final = set fin, ta_rules = set rules, ta_eps = set eps \<rparr>"
  let ?iter = "\<lambda> q. map snd (filter (\<lambda> (a,b). a = q) rel)"
  let ?rel = "rs.from_list rel"
  have TA: "ta_of_ta TA = ?TA" unfolding ta by simp
  have l: "?l = (set (concat (map ?iter fin)) \<subseteq> set fin \<and>
     (\<forall>x\<in>set rules. isOK (check_coherent_rule ?iter ?rel rules x)) \<and> (set rel)\<inverse> O set eps \<subseteq> (set eps)^+ O (set rel)\<inverse> \<union> (set rel)^-1)" (is "_ = (?l1 \<subseteq> _ \<and> ?l2 \<and> _ \<subseteq> ?l3)")
     unfolding ta rel by (simp add: Let_def)
  have r: "?r = (set rel `` set fin \<subseteq> set fin \<and>
     (\<forall>f qs q. (f qs \<rightarrow> q) \<in> set rules \<longrightarrow>
               (\<forall>i<length qs. \<forall>qi. (qs ! i, qi) \<in> set rel \<longrightarrow> (\<exists>q'. (f qs[i := qi] \<rightarrow> q') \<in> set rules \<and> (q, q') \<in> set rel)))
               \<and> (set rel)\<inverse> O set eps \<subseteq> (set eps)\<^sup>* O (set rel)\<inverse>)" 
    (is "_ = (?r1 \<subseteq> _ \<and> ?r2 \<and> _ \<subseteq> ?r3)")
    unfolding TA rel state_coherent_def by simp
  have id1: "?l1 = ?r1" by force
  have id2: "?l2 = ?r2" 
  proof
    assume ?l2
    show ?r2
    proof (intro allI impI)
      fix f qs q i qi
      assume rule: "(f qs \<rightarrow> q) \<in> set rules"
        and i: "i < length qs"
        and rel: "(qs ! i, qi) \<in> set rel"
      from i have i': "i \<in> {0 ..< length qs}" by simp
      let ?f = "(case_ta_rule (\<lambda>g qs'' q'. f = g \<and> qs[i := qi] = qs'' \<and> rs.memb (q, q') ?rel))"
      from \<open>?l2\<close>[rule_format, OF rule] have ok: "isOK (check_coherent_rule ?iter ?rel rules (f qs \<rightarrow> q))" .
      note ok = ok[simplified, rule_format, OF i' rel]
      from ok have "filter ?f rules \<noteq> []" by auto
      then obtain rule where f: "rule \<in> set rules \<and> ?f rule" by (cases "filter ?f rules", force+)
      then show "\<exists>q'. (f qs[i := qi] \<rightarrow> q') \<in> set rules \<and> (q, q') \<in> set rel" by (cases rule, auto simp: rs.correct)
    qed
  next
    assume ?r2
    show ?l2
    proof
      fix rule
      assume mem: "rule \<in> set rules"
      obtain f qs q where rule: "rule = (f qs \<rightarrow> q)" (is "_ = ?rule") by (cases rule, auto)
      let ?f = "\<lambda> i qi. case_ta_rule (\<lambda>g qs'' q'. f = g \<and> qs[i := qi] = qs'' \<and> (q, q') \<in> set rel)"
      have "isOK(check_coherent_rule ?iter ?rel rules ?rule) = (\<forall>i < length qs. 
        \<forall>qi. (qs ! i, qi) \<in> set rel \<longrightarrow>
            filter (?f i qi) rules \<noteq> [])" 
        by (auto simp: rs.correct)
      also have "..."
      proof (intro allI impI)
        fix i qi
        assume i: "i < length qs"
        assume rel: "(qs ! i, qi) \<in> set rel"
        from \<open>?r2\<close>[rule_format, OF mem[unfolded rule] i rel]
        obtain q' where "(f qs[i := qi] \<rightarrow> q') \<in> set rules" "(q, q') \<in> set rel" by auto
        then have "(f qs[i := qi] \<rightarrow> q') \<in> set (filter (?f i qi) rules)" by auto
        then show "filter (?f i qi) rules \<noteq> []" by force
      qed
      finally
      show "isOK(check_coherent_rule ?iter ?rel rules rule)" unfolding rule .
    qed
  qed
  have id3: "?l3 = ?r3" by regexp
  show ?thesis unfolding l r id1 id2 id3 ..
qed (insert state_coherent_Id, auto)

fun check_det :: "('q,'f)tree_automaton \<Rightarrow> showsl check" where
  "check_det (Tree_Automaton fin rules eps) = (do {
      check (eps = []) (showsl_lit (STR ''epsilon transitions not allowed''));
      check (distinct (map (\<lambda> rule. case rule of TA_rule f qs q \<Rightarrow> (f,qs)) (remdups rules))) (showsl_lit (STR ''some lhs occurs twice''))
    }) <+? (\<lambda> s. showsl_lit (STR ''problem when ensuring determinism of automata\<newline>'') \<circ> s)"

lemma check_det[simp]: "isOK(check_det TA) = ta_det (ta_of_ta TA)"
proof (cases TA)
  case (Tree_Automaton fin rules eps) note ta = this
  let ?ta = "\<lparr> ta_final = set fin, ta_rules = set rules, ta_eps = set eps \<rparr>"
  have ta': "ta_of_ta TA = ?ta" unfolding ta by auto
  let ?rules = "set (remdups rules)"
  have main: "(\<forall>f qs q. f qs \<rightarrow> q \<in> set rules \<longrightarrow> (\<forall>q'. f qs \<rightarrow> q' \<in> set rules \<longrightarrow> q = q'))
    = distinct (map (case_ta_rule (\<lambda>f qs q. (f, qs))) (remdups rules))" (is "?l = ?r")
  proof 
    assume ?r
    show ?l
    proof (intro allI impI)
      fix f qs q q'
      assume q: "(f qs \<rightarrow> q) \<in> set rules" and q': "(f qs \<rightarrow> q') \<in> set rules" 
      then have q: "(f qs \<rightarrow> q) \<in> ?rules" and q': "(f qs \<rightarrow> q') \<in> ?rules" by auto
      from \<open>?r\<close>[unfolded distinct_map inj_on_def, THEN conjunct2,  
        THEN bspec[OF _ q], THEN bspec[OF _ q']] 
      show "q = q'" by auto
    qed
  next
    assume ?l
    let ?f = "case_ta_rule (\<lambda>f qs q. (f, qs))"
    show ?r unfolding distinct_map
    proof (rule conjI, simp, simp, rule inj_onI)
      fix r1 r2
      assume mem1: "r1 \<in> set rules"
        and mem2: "r2 \<in> set rules"
        and id: "?f r1 = ?f r2"
      obtain f qs q where r1: "r1 = (f qs \<rightarrow> q)" by (cases r1, auto)
      obtain f' qs' q' where r2: "r2 = (f' qs' \<rightarrow> q')" by (cases r2, auto)
      from id[unfolded r1 r2] have r2: "r2 = (f qs \<rightarrow> q')" unfolding r2 by auto
      from \<open>?l\<close>[rule_format, OF mem1[unfolded r1] mem2[unfolded r2]]
      show "r1 = r2" unfolding r1 r2 by auto
    qed
  qed
  show ?thesis unfolding ta ta'
    by (simp add: ta_det_def main)
qed

fun generate_ta :: "('q :: linorder,'f :: linorder)tree_automaton \<Rightarrow> ('q,'f)ta_impl"
  where "generate_ta (Tree_Automaton fin rules eps) = (let ep = memo_rbt_rtrancl eps;
     epr = memo_rbt_rtrancl (map (\<lambda> (q,q'). (q',q)) eps);
     rqs_rs = rs_Union (map (\<lambda> rule. (ep (r_rhs rule))) rules);
     rrules = map (conv_ta_rule ep) rules
     in TA_Impl
       (rs.from_list fin)
       (elem_list_to_rm r_sym_impl rrules)
       (rs.to_list rqs_rs)
       rqs_rs
       eps
       ep
       epr )"

definition generate_ta_cond :: "('q :: {linorder, showl},'f :: {linorder,showl})tree_automaton \<Rightarrow> 'q ta_relation \<Rightarrow> showsl + ('q,'f)ta_impl"
  where "generate_ta_cond ta rel \<equiv> do {
      check_coherent ta rel <+? (\<lambda> s. showsl_lit (STR ''automaton is not coherent w.r.t. relation\<newline>'') \<circ> s);
      return (generate_ta ta)
    }" 

lemma generate_ta_eps: "ta_eps (ta_of (generate_ta (Tree_Automaton fin rules eps))) = set eps"
  by (simp add: Let_def ta_of_def)

lemma generate_ta_final: "ta_final (ta_of (generate_ta (Tree_Automaton fin rules eps))) = set fin"
  by (simp add: Let_def ta_of_def rs.correct)

lemma generate_ta_rules: "ta_rules (ta_of (generate_ta (Tree_Automaton fin rules eps))) = set rules"
  (is "ta_rules ?TA' = _")
proof -
  {
    fix eps
    let ?rules = "\<Union> { ta_rule_conv ` {d \<in> set (map (conv_ta_rule eps) rules). r_sym_impl d = fn} | fn. True}"
    {
      fix r
      assume "r \<in> ?rules"
      from this[simplified]
      obtain rl rs where r: "r = ta_rule_conv rl"
        and          rl: "rl = conv_ta_rule eps rs"
        and           rs: "rs \<in> set rules"
        by auto
      then have "r \<in> set rules" by (cases rs, auto)
    }
    moreover
    {
      fix r 
      assume "r \<in> set rules"
      then obtain f qs q where r: "r = (f qs \<rightarrow> q)"
        and rr: "(f qs \<rightarrow> q) \<in> set rules" by (cases r rule: ta_rule.exhaust) (auto)
      have "conv_ta_rule eps r = TA_rule_impl f qs q (eps q)" (is "_ = ?rl") unfolding r  by simp
      with rr have rl: "?rl \<in> set (map (conv_ta_rule eps) rules)" (is "_ \<in> ?L") by force
      have r: "r = ta_rule_conv ?rl" unfolding r by auto
      have "r \<in> ta_rule_conv ` ?L" unfolding r using rl by blast
      then have "r \<in> ?rules" by blast
    }
    ultimately have "?rules = set rules" by blast
  }
  then show ?thesis
    unfolding generate_ta.simps  Let_def
    unfolding ta_of_def ta.simps ta_impl.sel elem_list_to_rm.rm_set_lookup
    by auto
qed

declare generate_ta.simps[simp del]

lemma generate_ta: "ta_of (generate_ta TA) = ta_of_ta TA"
proof (cases TA)
  case (Tree_Automaton fin rules eps)
  show ?thesis unfolding Tree_Automaton ta_of_ta.simps
    by (rule ta.equality, auto simp: generate_ta_rules generate_ta_eps generate_ta_final)
qed
  
lemma generate_ta_cond: assumes cond: "generate_ta_cond TA rel = return ta"
  shows "ta_inv ta (rel_checker rel) (relation_of rel) \<and> ta = generate_ta TA"
proof (cases TA)
  case (Tree_Automaton fin rules epsilon)
  note cond = cond[unfolded generate_ta_cond_def Tree_Automaton] 
  from cond have ta: "ta = generate_ta (Tree_Automaton fin rules epsilon)" by auto
  obtain eps where eps: "eps = memo_rbt_rtrancl epsilon" by auto
  obtain epsr where epsr: "epsr = memo_rbt_rtrancl (map (\<lambda>(q,q'). (q',q)) epsilon)" by auto
  let ?rqs = "rs_Union (map (\<lambda> rule. (eps (r_rhs rule))) rules)"
  let ?rrules = "map (conv_ta_rule eps) rules"
  from ta eps epsr have A: "ta = TA_Impl
      (rs.from_list fin)
      (elem_list_to_rm r_sym_impl ?rrules)
      (rs.to_list ?rqs)
      ?rqs epsilon eps epsr" (is "_ = ?TA")
    by (auto simp: Let_def generate_ta.simps)
  let ?TA' = "ta_of ?TA"
  let ?rules = "\<Union> { ta_rule_conv ` {d \<in> set (map (conv_ta_rule eps) rules). r_sym_impl d = fn} | fn. True}"
  have ta_rules: "ta_rules ?TA' = set rules"
    using generate_ta_rules[of fin rules epsilon] 
    by (simp add: eps epsr Let_def generate_ta.simps)
  have qq1: "{(q, q'). (q, q') \<in> (set epsilon)^*} = (set epsilon)^*" by auto
  have qq2: "((\<lambda>(q,q'). (q',q)) ` set epsilon)^* = ((set epsilon)^*)^-1" unfolding rtrancl_converse[symmetric]
    by (rule arg_cong[where f = "\<lambda> x. x^*"], auto)
  have one: "ta_rhs_states ?TA' = rs.\<alpha> (ta_rhs_states_set ?TA)" 
    unfolding ta_rhs_states_def ta_rules 
    unfolding ta_of_def ta.simps ta_impl.simps rs_Union
    by (simp add: eps memo_rbt_rtrancl qq1, auto)
  have two: "set (ta_r_lhs_states_impl ?TA) = ta_rhs_states ?TA'" unfolding one 
    by (auto simp: rs.correct Let_def) 
  let ?ta_of = "\<lparr>ta_final = set fin, ta_rules = set rules, ta_eps = set epsilon\<rparr>"
  from cond have coh: "state_coherent ?ta_of (relation_of rel)" by auto 
  have id: "?ta_of = ta_of ?TA" using ta_rules unfolding ta_of_def 
    by (simp add: rs.correct)
  with coh have coh: "state_coherent (ta_of ?TA) (relation_of rel)" by simp
  have "ta_inv ta (rel_checker rel) (relation_of rel)" unfolding A
    by (unfold_locales, insert coh, unfold one two, unfold ta_impl.sel elem_list_to_rm.rm_set_lookup ta_rules, 
    insert choice, auto simp: ta_of_def eps epsr memo_rbt_rtrancl qq1 qq2 rel_checker rs.correct) 
  then show ?thesis unfolding Tree_Automaton ta by auto
qed

instantiation ta_rule :: (showl, showl) showl
begin
fun showsl_ta_rule :: "(_, _)ta_rule \<Rightarrow> showsl" where
  "showsl_ta_rule (TA_rule f qs q) = showsl f \<circ> showsl_list qs \<circ> showsl_lit (STR '' -> '') \<circ> showsl q"
definition "showsl_list (xs :: (_,_)ta_rule list) = default_showsl_list showsl xs"
instance ..
end
 
instantiation tree_automaton :: (showl, showl) showl
begin
fun showsl_tree_automaton :: "(_, _) tree_automaton \<Rightarrow> showsl" where
  "showsl_tree_automaton (Tree_Automaton fin rules eps) =
    showsl_lit (STR ''final: '') \<circ> showsl_list fin \<circ>
    showsl_lit (STR ''\<newline>rules: '') \<circ> showsl_lines (STR ''empty'') rules \<circ> 
    showsl_lit (STR ''\<newline>epsilon: '') \<circ> showsl_list eps \<circ> showsl_nl"
definition "showsl_list (xs :: (_,_) tree_automaton list) = default_showsl_list showsl xs"
instance ..
end

(* FIXME: move *)
lemma sorted_list_of_set_inj:
  assumes "finite A" "B \<subseteq> Pow A"
    shows "inj_on sorted_list_of_set B" (is "inj_on ?f B")
proof (intro inj_on_inverseI[where g = set])
  fix x y assume "x \<in> B" 
  with assms have "finite x" by (auto intro: finite_subset)
  from sorted_list_of_set(1)[OF this] show "set (?f x) = x" by blast
qed

(* Note that the decision procedure (ta_code.check_comcoh_wit) requires linorder on states.
 * Since the powerset construction uses sets, which cannot instantiate linorder, it's necessary
 * to map states to some other type. Using sorted and distinct lists seems to be the simplest
 * solution. *)
definition sorted_ps_ta where
"sorted_ps_ta TA \<equiv>
  let TA = fmap_states_ta sorted_list_of_set (ps_ta TA) in
  Tree_Automaton (sorted_list_of_set (ta_final TA)) (sorted_list_of_set (ta_rules TA)) []"

declare sorted_ps_ta_def[unfolded fmap_states_ta_def Let_def ta.simps, code]

lemma sorted_ps_ta:
  assumes "finite (ta_rules TA)" (is "finite ?rules")
  assumes "finite (ta_eps TA)" (is "finite ?eps")
  shows "ta_det (ta_of_ta (sorted_ps_ta TA))" (is "ta_det ?ta")
    and "ta_lang TA = ta_lang (ta_of_ta (sorted_ps_ta TA))" (is "?L = ?R")
proof -
  let ?fta = "fmap_states_ta sorted_list_of_set (ps_ta TA)"
  let ?pow = "Pow (r_rhs ` ?rules \<union> snd ` ?eps)"
  let ?pta = "ps_ta TA"
  from assms have finite_pow: "finite ?pow" by simp
  have finite_rules: "finite (ta_rules ?pta)" using ps_ta_finite[OF assms] .
  then have finite_srules: "finite (ta_rules ?fta)" by (auto simp: fmap_states_ta_def)
  have final_subset: "ta_final ?pta \<subseteq> ta_states ?pta" unfolding ta_states_def by auto
  from order_trans[OF this ps_ta_states] finite_pow have
    finite_final: "finite (ta_final ?pta)" by (auto intro: finite_subset)
  then have finite_sfinal: "finite (ta_final ?fta)" by (auto simp: fmap_states_ta_def)
  have eps: "ta_eps ?fta = {}" by (auto simp: fmap_states_ta_def)

  note sorted = sorted_list_of_set(1)[OF finite_sfinal] sorted_list_of_set(1)[OF finite_srules] eps[symmetric]

  let ?f = sorted_list_of_set
  from assms have inj: "inj_on ?f (ta_states ?pta)" by (auto intro!: sorted_list_of_set_inj[OF _ ps_ta_states])

  from fmap_ta[OF inj] have "ta_det ?fta" by simp
  then show "ta_det ?ta" by (auto simp: sorted_ps_ta_def Let_def sorted) (cases ?fta, simp)
  have lang: "?L = ta_lang ?fta" by (simp add: fmap_ta[OF inj] ps_ta_lang[symmetric]) 
  show "?L = ?R" unfolding lang by (auto simp: sorted_ps_ta_def Let_def sorted) (cases ?fta, simp)+
qed

fun ta_code_make_impl where
  "ta_code_make_impl (Tree_Automaton fin rs eps) = ta_code.make_ls fin rs eps"

definition tree_aut_trs_closed where
  "tree_aut_trs_closed ta rel R  \<equiv> do {
    check_varcond_subset R;
    (case rel of
      Decision_Proc \<Rightarrow> do {
        let tc = ta_code_make_impl ta;
        if ta_code.det tc then
          case ta_code.check_comcoh_wit_ls tc R of
            None \<Rightarrow> succeed
          | Some (wl, wr) \<Rightarrow>
              error (showsl_lit (STR ''TA is not closed under rewriting\<newline>'') \<circ>
                     showsl wl \<circ> showsl_lit (STR '' is accepted by TA and rewrites to\<newline>'') \<circ>
                     showsl wr \<circ> showsl_lit (STR '' which is not accepted by TA''))          
          else
            let tc = ta_code_make_impl (sorted_ps_ta (trim_ta (ta_of_ta ta))) in
            case ta_code.check_comcoh_wit_ls tc R of
              None \<Rightarrow> succeed
            | Some (wl, wr) \<Rightarrow>
                error (showsl_lit (STR ''TA is not closed under rewriting\<newline>'') \<circ>
                       showsl wl \<circ> showsl_lit (STR '' is accepted by TA and rewrites to\<newline>'') \<circ>
                       showsl wr \<circ> showsl_lit (STR '' which is not accepted by TA''))    
      }
    | Decision_Proc_Old \<Rightarrow> do {
        check_det ta <+? (\<lambda> s. showsl_lit (STR ''decision procedure requires det. TA as input\<newline>'') \<circ> s);
        check (closed_under_rewriting (ta_of_ta ta) (set R)) (showsl_lit (STR ''TA is not closed under rewriting''))
      }
    | _ \<Rightarrow> do {
        TA \<leftarrow>  generate_ta_cond ta rel;
        (if isOK (check_left_linear_trs R) then succeed
            else check_det ta)
        <+? (\<lambda> s. showsl_lit (STR ''could not ensure left-linearity or determinism\<newline>'') \<circ> s);
        state_compatible_eff_list TA (rel_checker rel) R
        <+? (\<lambda> (lr,lrq,q). showsl_lit (STR ''TA is not compatible with R\<newline>'')
             \<circ> showsl_lit (STR ''for rule '') \<circ> showsl_rule lr  
             \<circ> showsl_lit (STR ''\<newline>which is instantiated by states to '') \<circ> showsl_rule lrq 
             \<circ> showsl_lit (STR ''\<newline>the state '') \<circ> showsl q \<circ> showsl_lit (STR '' is only reachable from the lhs\<newline>''))
      }
    ) <+? (\<lambda> s. showsl_lit (STR ''problem when ensuring (state-)compatibility of TRS with TA\<newline>'') \<circ> showsl ta \<circ> showsl_nl \<circ> s)
  }"

lemma tree_aut_trs_closed:
  assumes ok: "isOK(tree_aut_trs_closed ta rel R)"
  shows "{t | s. s \<in> ta_lang (ta_of_ta ta) \<and> (s,t) \<in> (rstep (set R))^*} \<subseteq> ta_lang (ta_of_ta ta)" 
  (is "?RL \<subseteq> ?L")
proof (cases "rel")
  case Decision_Proc
    let ?ta = "ta_code_make_impl ta"
    have closed: "(rstep (set R) `` ?L) \<subseteq> ?L" proof (cases "ta_det (ta_code.\<alpha> ?ta)")
      case True
        moreover note ok = ok[unfolded tree_aut_trs_closed_def Decision_Proc ta_relation.case] 
        ultimately have
          wf: "\<forall>(l,r) \<in> set R. vars_term r \<subseteq> vars_term l" and
          det: "ta_det (ta_code.\<alpha> ?ta)" by (auto simp: ta_code.correct)
        from ok ta_code.correct_comcoh_wit(2)[OF det wf] True show ?thesis
          by (cases ta, auto split: option.splits simp: ta.make_def ta_code.correct) next
      case False
        let ?ta' = "ta_of_ta ta"
        let ?ta_det = "(sorted_ps_ta (trim_ta ?ta'))"
        have finite: "finite (ta_rules (trim_ta ?ta'))" "finite (ta_eps (trim_ta ?ta'))"
          using trim_ta_subset[of ?ta'] by (cases ta, (auto simp: ta_subset_def intro: finite_subset)[])+
        note ok = ok[unfolded tree_aut_trs_closed_def Decision_Proc ta_relation.case]
        with False have
          wf: "\<forall>(l,r) \<in> set R. vars_term r \<subseteq> vars_term l" and
          det: "ta_det (ta_of_ta ?ta_det)" by (simp_all add: sorted_ps_ta(1)[OF finite])
        from det have "ta_det (ta_code.\<alpha> (ta_code_make_impl ?ta_det))"
          by (cases "?ta_det", simp add: ta_code.correct ta.make_def)
        from ok ta_code.correct_comcoh_wit(2)[OF this wf] False have
          "(rstep (set R) `` (ta_lang (ta_of_ta ?ta_det))) \<subseteq> (ta_lang (ta_of_ta ?ta_det))"
        by (cases "?ta_det", simp split: option.splits add: ta.make_def ta_code.correct)
        then show ?thesis by (simp add: sorted_ps_ta(2)[OF finite, symmetric] trim_ta_lang)
    qed 
    show ?thesis proof standard
      fix t
      assume "t \<in> ?RL"
      then obtain s where s: "s \<in> ?L" and st: "(s,t) \<in> (rstep (set R))^*" by auto
      from st 
      show "t \<in> ?L"
        by (induct, insert s closed, auto)
    qed
  next

  case Decision_Proc_Old
    let ?ta = "ta_of_ta ta"
    from ok[unfolded tree_aut_trs_closed_def Decision_Proc_Old ta_relation.case] have
      wf: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" and
      det: "ta_det ?ta" and
      closed: "closed_under_rewriting ?ta (set R)" 
    by force+
    have fin: "finite (ta_states ?ta)" by (cases ta, auto simp: ta_states_def r_states_def)
    from closed closed_under_rewriting[OF det wf fin, of "set R"]
    have closed: "(rstep (set R) `` ?L) \<subseteq> ?L" by auto
    show ?thesis
    proof
      fix t
      assume "t \<in> ?RL"
      then obtain s where s: "s \<in> ?L" and st: "(s,t) \<in> (rstep (set R))^*" by auto
      from st 
      show "t \<in> ?L"
        by (induct, insert s closed, auto)
    qed
  next

  {
    fix r
    assume rel: "rel = Id_Relation \<or> rel = Some_Relation r"
    obtain fin rules eps where ta: "ta = Tree_Automaton fin rules eps" by (cases ta, auto)
    note ok = ok[unfolded tree_aut_trs_closed_def] rel
    from ok obtain TA where gc: "generate_ta_cond ta rel = return TA"
      by (cases rel) auto
    let ?ta = "generate_ta ta"  
    from generate_ta_cond[OF gc] have TA: "TA = ?ta" and inv: "ta_inv ?ta (rel_checker rel) (relation_of rel)" by auto
    note ok = ok[unfolded gc TA, simplified]
    from ok have compat: "isOK(state_compatible_eff_list ?ta (rel_checker rel) R)"
      by (cases rel) auto
    from ok rel have var_cond: "\<And> l r. (l,r) \<in> set R \<Longrightarrow> vars_term r \<subseteq> vars_term l" by (cases rel) auto
    let ?TA = "\<lparr>ta_final = set fin, ta_rules = set rules, ta_eps = set eps\<rparr>"
    let ?ll = "left_linear_trs (set R)"
    from ok assms(1) have "?ll \<or> ta_det (ta_of_ta ta)" by (auto split: if_splits)
    with ta have ll: "?ll \<or> ta_det ?TA" by auto
    interpret ta_inv "generate_ta ta" "rel_checker rel" "relation_of rel" by fact 
    have "?RL \<subseteq> ?L" unfolding ta ta_of_ta.simps
    proof (rule state_compatible[OF _ _ _ var_cond subset_refl])
      let ?TA = "\<lparr>ta_final = set fin, ta_rules = set rules, ta_eps = set eps\<rparr>"
      let ?T = "ta_of (generate_ta ta)"    
      have id: "?T = ?TA" unfolding ta generate_ta by simp 
      show "state_compatible ?TA (relation_of rel) (set R)" 
        by (rule state_compatible_eff_list[OF var_cond compat, unfolded id])
      show "state_coherent ?TA (relation_of rel)" using id coherent by auto
    qed (insert ll, auto simp: ta ta_of_def Let_def)
  } note rel_check = this

  { case Id_Relation with rel_check show ?thesis by blast}
  { case Some_Relation with rel_check show ?thesis by blast}
qed

definition non_join_with_ta
  where "non_join_with_ta ta1 rel1 R1 t1 ta2 rel2 R2 t2 \<equiv> let TA1 = ta_of_ta ta1; TA2 = ta_of_ta ta2 in (do {
    check (ta_member t1 TA1) (showsl t1 \<circ> showsl_lit (STR '' is not accepted by first automaton''));
    check (ta_member t2 TA2) (showsl t2 \<circ> showsl_lit (STR '' is not accepted by second automaton''));
    check (ta_empty (intersect_ta TA1 TA2)) (showsl_lit (STR ''intersection of automata is non-empty''));
    tree_aut_trs_closed ta1 rel1 R1
      <+? (\<lambda> s. showsl_lit (STR ''could not ensure closure under rewriting for first automaton\<newline>'') \<circ> s);
    tree_aut_trs_closed ta2 rel2 R2
      <+? (\<lambda> s. showsl_lit (STR ''could not ensure closure under rewriting for second automaton\<newline>'') \<circ> s)
   })"

lemma non_join_with_ta: assumes "isOK(non_join_with_ta ta1 rel1 R1 t1 ta2 rel2 R2 t2)"
  shows "\<not> (\<exists> u. (t1,u) \<in> (rstep (set R1))^* \<and> (t2,u) \<in> (rstep (set R2))^*)" (is "\<not> ?join")
proof
  assume ?join
  then obtain u where t1u: "(t1,u) \<in> (rstep (set R1))^*" and t2u: "(t2,u) \<in> (rstep (set R2))^*" by auto
  let ?TA1 = "ta_of_ta ta1"
  let ?TA2 = "ta_of_ta ta2"
  note ass = assms[unfolded non_join_with_ta_def Let_def, simplified]
  from ass have t1: "t1 \<in> ta_lang ?TA1"
    and t2: "t2 \<in> ta_lang ?TA2"
    and empty: "ta_empty (intersect_ta ?TA1 ?TA2)"
    and closed1: "isOK (tree_aut_trs_closed ta1 rel1 R1)"
    and closed2: "isOK (tree_aut_trs_closed ta2 rel2 R2)" by auto
  from tree_aut_trs_closed[OF closed1] t1 t1u have u1: "u \<in> ta_lang ?TA1" by auto
  from tree_aut_trs_closed[OF closed2] t2 t2u have u2: "u \<in> ta_lang ?TA2" by auto
  from u1 u2 empty ta_empty intersect_ta show False by blast
qed

definition certify_ta_closed  where
  "certify_ta_closed ta R dp = tree_aut_trs_closed ta (if dp then Decision_Proc else Id_Relation) R"

lemma certify_ta_closed:
  assumes ok: "isOK(certify_ta_closed ta R dp)"
  shows "(rstep (set R))^* `` ta_lang (ta_of_ta ta) \<subseteq> ta_lang (ta_of_ta ta)" 
using tree_aut_trs_closed[OF ok[unfolded certify_ta_closed_def]] by auto

end

