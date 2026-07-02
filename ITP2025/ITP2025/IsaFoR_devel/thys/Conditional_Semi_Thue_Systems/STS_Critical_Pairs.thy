(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Critical Pairs for Semi-Thue Systems\<close>

theory STS_Critical_Pairs
  imports
   String_Rewriting
begin

definition sts_critical_peaks :: "sts \<Rightarrow> (string \<times> string \<times> string) set"
where
  "sts_critical_peaks R = {(v @ y, x @ u', x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ u' @ y, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}" 

(* Definition 6(i) *)
definition sts_critical_pairs :: "sts \<Rightarrow> sts"
where
  "sts_critical_pairs R = {(v @ y, x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}" 

lemma sts_critical_pairs_mono:
  assumes "R\<^sub>1 \<subseteq> R\<^sub>2" shows "sts_critical_pairs R\<^sub>1 \<subseteq> sts_critical_pairs R\<^sub>2"
proof 
  fix a b
  assume asm:"(a, b) \<in> sts_critical_pairs R\<^sub>1"
  have sts_un:"sts_critical_pairs R\<^sub>1 = {(v @ y, x @ v') | x y u v u' v'. (u, v) \<in> R\<^sub>1 \<and> (u', v') \<in> R\<^sub>1 \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ v' @ y) | x y u v u' v'. (u, v) \<in>  R\<^sub>1 \<and> (u', v') \<in>  R\<^sub>1 \<and>
    u = x @ u' @ y}"  (is "_ = ?X \<union> ?Y") unfolding sts_critical_pairs_def by simp
  show "(a, b) \<in> sts_critical_pairs R\<^sub>2"
  proof(cases "(a, b) \<in> ?X")
    case True
    hence "(a, b) \<in> {(v @ y, x @ v') | x y u v u' v'. (u, v) \<in> R\<^sub>2 \<and> (u', v') \<in> R\<^sub>2 \<and>
    u @ y = x @ u' \<and> length x < length u}" unfolding sts_critical_pairs_def using assms asm by blast
    with UnI1[OF this] show ?thesis unfolding sts_critical_pairs_def by simp
  next
    case False
    then have "(a, b) \<in> ?Y" using sts_un asm by fastforce
    hence "(a, b) \<in> {(v, x @ v' @ y) | x y u v u' v'. (u, v) \<in>  R\<^sub>2 \<and> (u', v') \<in>  R\<^sub>2 \<and>
    u = x @ u' @ y}" unfolding sts_critical_pairs_def using assms asm by blast
    with UnI1[OF this] show ?thesis unfolding sts_critical_pairs_def by simp
  qed
qed

lemma sts_critical_peaks_condition1[intro]:
  assumes "(u, v) \<in> R" and "(u', v') \<in> R" and
    "u @ y = x @ u'" and "length x < length u"
  shows "(v @ y, x @ u', x @ v') \<in> sts_critical_peaks R"
proof -
  from assms have "(v @ y, x @ u', x @ v')\<in> {(v @ y, x @ u', x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u}" by blast
  with UnI1[OF this] show "(v @ y, x @ u', x @ v') \<in> sts_critical_peaks R" 
    unfolding sts_critical_peaks_def by simp
qed

lemma sts_critical_peaks_condition2[intro]:
  assumes "(u, v) \<in> R" and "(u', v') \<in> R" and "u = x @ u' @ y"
  shows "(v, x @ u' @ y, x @ v' @ y) \<in> sts_critical_peaks R"
proof -
  from assms have "(v, x @ u' @ y, x @ v' @ y) \<in>{(v, x @ u' @ y, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}" by blast
  with UnI1[OF this] show "(v, x @ u' @ y, x @ v' @ y) \<in> sts_critical_peaks R" 
    unfolding sts_critical_peaks_def by simp
qed

lemma sts_critical_peak_steps:
  fixes R :: "sts"
  assumes cp: "(l, m, r) \<in> sts_critical_peaks R"
  shows "(m, l) \<in> ststep R \<and> (m,r) \<in> ststep R"
proof -
  from cp have lmr:"(l, m, r) \<in> {(v @ y,  x @ u',  x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ u' @ y, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}" (is "_ \<in> ?X \<union>?Y") unfolding sts_critical_peaks_def by simp
  then show "(m, l) \<in> ststep R \<and> (m,r) \<in> ststep R"
  proof(cases "(l, m, r) \<in> ?X")
    case True
    then show ?thesis unfolding sts_critical_peaks_def using lmr
    proof (clarsimp)
      fix x y u v u' v'
      assume "l = v @ y" and "m = x @ u'" and "r = x @ v'"
      and uv:"(u, v) \<in> R"
      and u'v':"(u', v') \<in> R"
      and uu':"u @ y = x @ u'"
      and "length x < length u"
      show "(x @ u', v @ y) \<in> ststep R \<and> (x @ u', x @ v') \<in> ststep R"
      proof(rule conjI)
        show "(x @ u', v @ y) \<in> ststep R" using uu'[symmetric] uv by auto
        show "(x @ u', x @ v') \<in> ststep R" using u'v' by auto
      qed
    qed
  next
    case False
    then show ?thesis unfolding sts_critical_peaks_def using lmr by auto
  qed
qed

lemma sts_critical_peaks_disjoint:
  fixes R :: "sts"
  assumes lr1: "(l1, r1) \<in> R"
    and lr2: "(l2, r2) \<in> R"
    and s1: "s = bef @ w1 @ l1 @ w2 @ aft" 
    and s2: "s = bef @ w3 @ l2 @ w4 @ aft"
    and t: "t = bef @ w1 @ r1 @ w2 @ aft" 
    and u: "u = bef @ w3 @ r2 @ w4 @ aft"
    and len:"length (bef @ w3) \<ge> length (bef @ w1 @ l1) \<or>
      length (bef @ w1) \<ge> length (bef @ w3 @ l2)"
  shows "(t, u) \<in> join (ststep R)" 
proof -
  from len show ?thesis
  proof 
    assume asm:"length (bef @ w3) \<ge> length (bef @ w1 @ l1)"
    have "take (length (bef @ w1 @ l1)) (bef @ w3) = (bef @ w1 @ l1)" using asm
      by (metis append.assoc append_eq_append_conv_if s1 s2)
    then obtain w5 where w5:"bef @ w3 = bef @ w1 @ l1 @ w5"
      by (metis append.assoc append_take_drop_id)
    have s:"s = bef @ w1 @ l1 @ w5 @ l2 @ w4 @ aft" using s2 w5 by auto
    have t:"t = bef @ w1 @ r1 @ w5 @ l2 @ w4 @ aft" using t s s1 by auto
    have u:"u = bef @ w1 @ l1 @ w5 @ r2 @ w4 @ aft" using u w5 by auto
    define v where "v = bef @ w1 @ r1 @ w5 @ r2 @ w4 @ aft"
    have tv:"(t, v) \<in> ststep R" using t lr2 unfolding v_def 
      by (smt (verit) append.assoc assms(5) s1 same_append_eq ststepI)
    have uv:"(u, v) \<in> ststep R" using u lr1 unfolding v_def
      by (metis append.assoc ststepI)
    from tv uv show ?thesis by auto
  next
    assume asm:"length (bef @ w1) \<ge> length (bef @ w3 @ l2)"
    have "take (length (bef @ w3 @ l2)) (bef @ w1) = bef @ w3 @ l2" using asm
      by (metis append.assoc append_eq_append_conv_if s1 s2)
    then obtain w5 where w5:"bef @ w1 = bef @ w3 @ l2 @ w5"
      by (metis append.assoc append_take_drop_id)
    have s:"s = bef @ w3 @ l2 @ w5 @ l1 @ w2 @ aft" using s1 w5 by auto
    have t:"t = bef @ w3 @ l2 @ w5 @ r1 @ w2 @ aft" using t s s1 by auto
    have u:"u = bef @ w3 @ r2 @ w5 @ l1 @ w2 @ aft" using u w5 s s2 by auto
    define v where "v = bef @ w3 @ r2 @ w5 @ r1 @ w2 @ aft"
    have tv:"(t, v) \<in> ststep R" using t lr2 unfolding v_def 
      by (smt (verit) append.assoc assms(5) s1 same_append_eq ststepI)
    have uv:"(u, v) \<in> ststep R" using u lr1 unfolding v_def
      by (metis append.assoc ststepI)
    from tv uv show ?thesis by auto
  qed
qed

lemma sts_critical_peaks_left_overlap:
  fixes R :: "sts"
  assumes lr1: "(l1, r1) \<in> R"
    and lr2: "(l2, r2) \<in> R"
    and s1: "s = bef @ l1 @ w1 @ aft" 
    and s2: "s = bef @ l2 @ w2 @ aft"
    and t: "t = bef @ r1 @ w1 @ aft" 
    and u: "u = bef @ r2 @ w2 @ aft"
    and neq: "w1 \<noteq> w2"
  shows "(\<exists> C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, m, r) \<in> sts_critical_peaks R \<or> (r, m, l) \<in> sts_critical_peaks R))"
proof(cases "length l1 \<ge> length l2")
  case True note T1 = this
  hence "take (length l2) l1 = l2" using s1 s2 
    by (simp add: append_eq_append_conv_if)
  then obtain w3 where w3:"l1 = l2 @ w3"
    by (metis append_take_drop_id)
  hence s:"s = bef @ l2 @ w3 @ w1 @ aft" using s1 by simp
  have t:"t = bef @ r1 @ w1 @ aft" using t .
  have u:"u = bef @ r2 @ w3 @ w1 @ aft" using u s s2 by auto
  define D where "D = More bef \<circle> (w1 @ aft)"
  have cr:"(r1, l2 @ w3, r2 @ w3) \<in> sts_critical_peaks R"
  proof(cases "length l1 = length l2")
    case True
    then show ?thesis using neq s1 s2 by auto
  next
    case False
    hence "length l1 > length l2" using T1 False by simp
    then show ?thesis using lr1 lr2 w3 unfolding sts_critical_peaks_def by blast
  qed
  have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and>
        (l, m, r) \<in> sts_critical_peaks R"
    by (rule exI[of _ D], rule exI[of _ r1], rule exI[of _ "l2 @ w3"], rule exI[of _ "r2 @ w3"], 
        insert cr, simp add: D_def s1 t u w3) 
  then show ?thesis by auto
next
  case False
  hence len:"length l2 > length l1" by simp
  hence "take (length l1) l2 = l1" using s1 s2 
    by (simp add: append_eq_append_conv_if)
  then obtain w3 where w3:"l2 = l1 @ w3"
    by (metis append_take_drop_id)
  hence s:"s = bef @ l1 @ w3 @ w2 @ aft" using s2 by simp
  have t:"t = bef @ r1 @ w3 @ w2 @ aft" using t s s1 by auto
  have u:"u = bef @ r2 @ w2 @ aft" using u .
  define D where "D = More bef \<circle> (w2 @ aft)"
  have cr:"(r2, l1 @ w3, r1 @ w3) \<in> sts_critical_peaks R" 
    unfolding sts_critical_peaks_def using len lr1 lr2 w3 by blast
  have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> (r, m, l) \<in> sts_critical_peaks R"
    by (rule exI[of _ D], rule exI[of _ "r1 @ w3"], rule exI[of _ "l1 @ w3"],
        rule exI[of _ r2], insert cr, simp add: D_def s2 t u w3 len)
  then show ?thesis by auto
qed

lemma sts_critical_peaks_overlap:
  fixes R :: "sts"
  assumes lr1: "(l1, r1) \<in> R"
    and lr2:"(l2, r2) \<in> R"
    and s1:"s = bef @ w1 @ l1 @ w2 @ aft" 
    and s2:"s = bef @ w3 @ l2 @ w4 @ aft"
    and t:"t = bef @ w1 @ r1 @ w2 @ aft" 
    and u:"u = bef @ w3 @ r2 @ w4 @ aft"
    and neq:"(w1 = [] \<and> w3 \<noteq> []) \<or> (w1 \<noteq> [] \<and> w3 = [])"
    and w24e:"w2 = [] \<or> w4 = []"
  shows "(t, u) \<in> join (ststep R) \<or> (\<exists> C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, m, r) \<in> sts_critical_peaks R \<or> (r, m, l) \<in> sts_critical_peaks R))"
proof -
  from neq show ?thesis
  proof
    assume asm1:"w1 = [] \<and> w3 \<noteq> []"
    then show ?thesis
    proof(cases "length w3 \<ge> length l1")
      case True
      hence "take (length l1) w3 = l1" using s1 s2 asm1
        by (metis append_eq_append_conv_if self_append_conv2)
      then obtain w5 where w5:"w3 = l1 @ w5"
        by (metis append_take_drop_id)
      hence s:"s = bef @ l1 @ w5 @ l2 @ w4 @ aft" using s2 w5 by simp
      hence t:"t = bef @ r1 @ w5 @ l2 @ w4 @ aft" using t asm1 s1 by simp
      have u:"u = bef @ l1 @ w5 @ r2 @ w4 @ aft" using u w5 by simp
      define v where "v = bef @ r1 @ w5 @ r2 @ w4 @ aft"
      have tv:"(t, v) \<in> ststep R" unfolding v_def using lr2
        by (metis append.assoc ststepI t)
      have uv:"(u, v) \<in> ststep R" unfolding v_def using lr1 u by auto
      from tv uv have "(t, u) \<in> join (ststep R)" by auto
      then show ?thesis by auto
    next
      case False
      hence len:"length l1 > length w3" by auto
      from w24e show ?thesis
      proof
        assume asm2:"w2 = []"
        from asm1 asm2 have leq:"l1 = w3 @ l2 @ w4" using s1 s2 by simp
        have s1:"s = bef @ l1 @ aft" using asm1 asm2 s1 by simp
        have s2:"s = bef @ w3 @ l2 @ w4 @ aft" using s2 by simp
        have t:"t = bef @ r1 @ aft" using t asm1 asm2 by simp
        have u:"u = bef @ w3 @ r2 @ w4 @ aft" using u by simp
        have cr:"(r1, l1, w3 @ r2 @ w4 ) \<in> sts_critical_peaks R"
          unfolding sts_critical_peaks_def using  lr1 lr2 leq by blast
        define D where "D = More bef \<circle> aft"
        have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> (l, m, r) \<in> sts_critical_peaks R"
          by (rule exI[of _ D], rule exI[of _ "r1"], rule exI[of _ "l1"], rule exI[of _ "w3 @ r2 @ w4"],
              insert cr lr1 lr2, simp add:s1 s2 t u D_def leq)
        then show ?thesis by auto
      next
        assume asm2:"w4 = []"
        have s1:"s = bef @ l1 @ w2 @ aft" using asm1 asm2 s1 by auto
        have s2:"s = bef @ w3 @ l2 @ aft" using asm1 asm2 s2 by auto
        have t:"t = bef @ r1 @ w2 @ aft" using asm1 asm2 t by auto
        have u:"u = bef @ w3 @ r2 @ aft" using asm1 asm2 u by auto
        define w where "w = drop (length l1) (w3 @ l2)"
        have weq: "w3 @ l2 = l1 @ w" unfolding w_def using s1 s2 by auto
        define D where "D = More bef \<circle> aft"
        have cr:"(r1 @ w, l1 @ w, w3 @ r2) \<in> sts_critical_peaks R" 
          unfolding sts_critical_peaks_def 
          using len lr1 lr2 w_def weq
          by (smt (z3) UnCI mem_Collect_eq)
        have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> (l, m, r) \<in> sts_critical_peaks R"
          by (rule exI[of _ D], rule exI[of _ "r1 @ w"], rule exI[of _ "l1 @ w"], rule exI[of _ "w3 @ r2"], 
              insert cr assms,  simp add:s1 s2 t u D_def weq)
        then show ?thesis by auto
      qed
    qed
  next
    assume asm1:"(w1 \<noteq> [] \<and> w3 = [])"
    then show ?thesis
    proof(cases "length w1 \<ge> length l2")
      case True
      hence "take (length l2) w1 = l2" using s1 s2 asm1
        by (metis append_eq_append_conv_if self_append_conv2)
      then obtain w5 where w5:"w1 = l2 @ w5"
        by (metis append_take_drop_id)
      hence s:"s = bef @ l2 @ w5  @ l1 @ w2 @ aft" using s1 w5 by simp
      hence t:"t = bef @ l2 @ w5 @ r1 @ w2 @ aft" using t asm1 s1 by simp
      have u:"u = bef @ r2 @ w5  @ l1 @ w2 @ aft" using u w5 asm1 s s2 by auto
      define v where "v = bef @ r2 @ w5 @ r1 @ w2 @ aft"
      have tv:"(t, v) \<in> ststep R" unfolding v_def using lr2 t by auto
      have uv:"(u, v) \<in> ststep R" unfolding v_def using lr1 u 
        by (metis (no_types, lifting) append_assoc ststep.simps)
      from tv uv have "(t, u) \<in> join (ststep R)" by auto
      then show ?thesis by auto
    next
      case False
      hence len:"length l2 > length w1" by auto
      from w24e show ?thesis
      proof
        assume asm2:"w2 = []"
        from asm1 asm2 have leq:"w1 @ l1 = l2 @ w4" using s1 s2 by simp
        have s1:"s = bef @ w1 @ l1 @ aft" using asm1 asm2 s1 by simp
        have s2:"s = bef @ l2 @ w4 @ aft" using s2 asm1 by auto
        have t:"t = bef @ w1 @ r1 @ aft" using t asm1 asm2 by simp
        have u:"u = bef @ r2 @ w4 @ aft" using u asm1 by auto
        have cr:"(r2 @ w4, w1 @ l1, w1 @ r1 ) \<in> sts_critical_peaks R"
          unfolding sts_critical_peaks_def using lr1 lr2 leq len
          by (smt (z3) UnI1 mem_Collect_eq)
        define D where "D = More bef \<circle> aft"
        have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> (r, m, l) \<in> sts_critical_peaks R"
          by (rule exI[of _ D], rule exI[of _ "w1 @ r1"], rule exI[of _ "w1 @ l1"], rule exI[of _ "r2 @ w4"],
              insert cr lr1 lr2, simp add:s1 s2 t u D_def leq) 
        then show ?thesis by auto
      next
        assume asm2:"w4 = []"
        from asm1 asm2 have leq:"l2 = w1 @ l1 @ w2" using s1 s2 by fastforce
        have s1:"s = bef @ w1 @ l1 @ w2 @ aft" using asm1 asm2 s1 by auto
        have s2:"s = bef @ l2 @ aft" using asm1 asm2 s2 by auto
        have t:"t = bef @ w1 @ r1 @ w2 @ aft" using asm1 asm2 t by auto
        have u:"u = bef @ r2 @ aft" using asm1 asm2 u by auto
        define D where "D = More bef \<circle> aft"
        have cr:"(r2, l2, w1 @ r1 @ w2) \<in> sts_critical_peaks R" 
          unfolding sts_critical_peaks_def using len lr1 lr2 leq by blast
        have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> (r, m, l) \<in> sts_critical_peaks R"
          by (rule exI[of _ D], rule exI[of _ "w1 @ r1 @ w2"], rule exI[of _ "l2"], rule exI[of _ "r2"], 
              insert cr asm1 asm2 leq,  simp add:s1 s2 t u D_def) 
        then show ?thesis by auto
      qed
    qed
  qed
qed

lemma sts_critical_peaks_main_root:
  fixes R :: "sts"
  assumes st: "(s, t) \<in> R" and su: "(s, u) \<in> ststep R"
  shows "(\<exists> C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, m, r) \<in> sts_critical_peaks R \<or> (r, m, l) \<in> sts_critical_peaks R))" 
proof -
  from su obtain C l1 r1 where lr1: "(l1, r1) \<in> R" and s2: "s = C\<llangle>l1\<rrangle>" and ur1: "u = C\<llangle>r1\<rrangle>" 
    by (metis sctxt.closure.cases ststep_eq_closure)
  from s2 have id: "s = C\<llangle>l1\<rrangle>" by auto
  show ?thesis
  proof(cases C)
    case Hole
    hence "s = l1" by (simp add: s2)
    hence "(t, s, r1) \<in> sts_critical_peaks R" unfolding sts_critical_peaks_def
      using st ur1 by (smt (verit, best) UnI2 lr1 mem_Collect_eq ststepE ststep_rule)
    then show ?thesis
      by (metis Hole sctxt_apply_string.simps(1) ur1)
  next
    case (More bef D aft)
    hence "s = bef @ D\<llangle>l1\<rrangle> @ aft" by (simp add: s2)
    hence "(t, s, bef @ D\<llangle>r1\<rrangle> @ aft) \<in> sts_critical_peaks R" unfolding sts_critical_peaks_def
      using lr1 st ur1 More ststepE su sctxt_apply_string.simps
      by (smt (verit) UnI2 mem_Collect_eq) 
    then show ?thesis 
      by (metis More sctxt_apply_string.simps ur1)
  qed
qed

lemma sts_critical_peaks_main_ststep:
  fixes R :: "sts"
  assumes st: "(s, t) \<in> ststep R" and su: "(s, u) \<in> ststep R"
  shows "(t, u) \<in> join (ststep R) \<or>
    (\<exists> C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, m, r) \<in> sts_critical_peaks R \<or> (r, m, l) \<in> sts_critical_peaks R))" 
proof - 
  from st obtain C1 l1 r1 where lr1: "(l1, r1) \<in> R" and s1: "s = C1\<llangle>l1\<rrangle>" and t: "t = C1\<llangle>r1\<rrangle>" 
    using sctxt.closure.simps ststep_eq_closure by auto
  from su obtain C2 l2 r2 where lr2: "(l2, r2) \<in> R" and s2: "s = C2\<llangle>l2\<rrangle>" and u: "u = C2\<llangle>r2\<rrangle>"
    using sctxt.closure.simps ststep_eq_closure by auto
  from s1 s2 u t show ?thesis
  proof (induct C1 arbitrary: C2 s t u)
    case Hole
    hence sl1:"s = l1" and tr1:"t = r1" and sl2:"s = C2\<llangle>l2\<rrangle>" and ur2:"u = C2\<llangle>r2\<rrangle>"  by auto
    hence st:"(s, t) \<in> R" and su:"(s, u) \<in> ststep R" 
      by (auto simp add: lr1 lr2 sl2  ur2  ststep_sctxt ststep_rule)
    from sts_critical_peaks_main_root[OF st su] 
    show ?case by auto
  next
    case (More bef1 D1 aft1) note C1 = this
    then show ?case
    proof(cases C2)
      case Hole
      from C1 have s:"s = More bef1 D1 aft1\<llangle>l1\<rrangle>"  by simp
      from C1 have t:"t = More bef1 D1 aft1\<llangle>r1\<rrangle>" by simp
      from C1 Hole have s2:"s = l2" by auto 
      from C1 Hole have u:"u = r2" by auto
      have seq:"More bef1 D1 aft1\<llangle>l1\<rrangle> = l2" using s s2 by simp
      hence st:"(s, t) \<in> ststep R" using lr1 s t by blast
      have su:"(s, u) \<in> R" using s2 u lr2 by simp 
      from sts_critical_peaks_main_root[OF su st] 
      show ?thesis by auto
    next
      case (More bef2 D2 aft2) note C2 = this
      have id: "(More bef1 D1 aft1)\<llangle>l1\<rrangle> = (More bef2 D2 aft2)\<llangle>l2\<rrangle>" using C1 C2 by blast
      have s1:"s = bef1 @ D1\<llangle>l1\<rrangle> @ aft1"
        by (simp add: More.prems(1))
      have s2:"s = bef2 @ D2\<llangle>l2\<rrangle> @ aft2" using id 
        by (simp add: More.prems(1))
      have "\<exists>bef3 aft3. D1\<llangle>l1\<rrangle> = bef3 @ l1 @ aft3" by simp
      then obtain bef3 aft3 where d1l1:"D1\<llangle>l1\<rrangle> = bef3 @ l1 @ aft3"
        and d1r1:"D1\<llangle>r1\<rrangle> = bef3 @ r1 @ aft3" using sctxt_app_step by meson
      have "\<exists>bef4 aft4. D2\<llangle>l2\<rrangle> = bef4 @ l2 @ aft4" by simp
      then obtain bef4 aft4 where d2l2:"D2\<llangle>l2\<rrangle> = bef4 @ l2 @ aft4"
        and d2r2:"D2\<llangle>r2\<rrangle> = bef4 @ r2 @ aft4" using sctxt_app_step by meson
      from d1l1 s1 have ss1:"s = bef1 @  bef3 @ l1 @ aft3 @  aft1" by simp
      from d2l2 s2 have ss2:"s = bef2 @  bef4 @ l2 @ aft4 @  aft2" by simp
      define minbef where "minbef = min (length (bef1 @ bef3)) (length (bef2 @ bef4))"
      define minaft where "minaft = min (length (aft3 @ aft1)) (length (aft4 @ aft2))"
      define bef where "bef = take minbef s"
      define aft where "aft = drop (length s - minaft) s"
      note defs = minbef_def minaft_def bef_def aft_def
      have pr1:"prefix bef (bef1 @ bef3)" unfolding defs 
        by (metis append.assoc bef_def dual_order.irrefl length_take max.strict_coboundedI2 max_min_same(1) min.commute minbef_def not_le_imp_less prefix_def prefix_length_prefix ss1 take_is_prefix)
      have pr2:"prefix bef (bef2 @ bef4)" unfolding defs 
        by (metis append.assoc append_eq_conv_conj ss2 take_is_prefix take_take)
      have len1:"length (aft3 @ aft1) \<ge> length aft" unfolding defs by auto 
      from suffix_drop suffix_length_suffix len1 ss1
      have su1:"suffix aft (aft3 @ aft1)" 
        unfolding defs by (metis ss1 suffixI suffix_appendD)
      have len2:"length (aft4 @ aft2) \<ge> length aft" unfolding defs by auto
      from suffix_drop suffix_length_suffix len2 ss2
      have su2:"suffix aft (aft4 @ aft2)" 
        unfolding defs by (metis suffix_appendD suffix_def)  
      from pr1 obtain w1 where bw1:"bef @ w1 = bef1 @ bef3" 
        by (auto elim: prefixE)
      from su1 obtain w2 where wa2:"w2 @ aft = aft3 @ aft1"
        by (auto elim:suffixE)
      from pr2 obtain w3 where bw3:"bef @ w3 = bef2 @ bef4" 
        by (auto elim:prefixE)
      from su2 obtain w4 where wa4:"w4 @ aft = aft4 @ aft2" 
        by (auto elim:suffixE)
      hence s1:"s = bef @ w1 @ l1 @ w2 @ aft" using ss1 
        by (simp add: bw1 wa2)
      hence s2:"s = bef @ w3 @ l2 @ w4 @ aft" using ss2 
        by (metis append.assoc bw3 wa4)
      have t:"t = bef @ w1 @ r1 @ w2 @ aft" using bw1 wa2 C1 d1r1 by simp
      have u:"u = bef @ w3 @ r2 @ w4 @ aft" using More bw3 d2r2 wa4 
        by (simp add: More.prems(3))
      have w13e:"w1 = [] \<or> w3 = []" unfolding defs using s1 s2 
        by (metis append.assoc append_eq_conv_conj append_self_conv bef_def bw1 bw3 min_def minbef_def)
      have w24e:"w2 = [] \<or> w4 = []" using wa2 wa4 unfolding aft_def minaft_def 
        by (cases "length (aft3 @ aft1) \<ge> length (aft4 @aft2)", auto)
          (simp add: ss2, metis append_take_drop_id length_append s1 same_append_eq self_append_conv2 
            suffixI suffix_order.trans suffix_take wa2)
      then show ?thesis
      proof(cases "length (bef @ w3) \<ge> length (bef @ w1 @ l1) \<or>
          length (bef @ w1) \<ge> length (bef @ w3 @ l2)")
        case True
        with sts_critical_peaks_disjoint[OF lr1 lr2 s1 s2 t u True]
        show ?thesis by simp
      next
        case False
        then show ?thesis
        proof(cases "w1 = w3")
          case True note T1 = this
          then show ?thesis
          proof(cases "w2 = w4")
            case True note T2 = this 
            hence leq:"l1 = l2" using s1 s2 T1 by auto
            define E where "E = Hole"
            define D where "D = More (bef @ w1) \<circle> (w2 @ aft)" 
            define m where "m = size E + size E"
            have s:"s = D\<llangle>l1\<rrangle>" using s1 T2 unfolding D_def by simp
            have t:"t = D\<llangle>r1\<rrangle>" using t T2 unfolding D_def by simp
            have u:"u = D\<llangle>r2\<rrangle>" using u unfolding D_def 
              by (simp add: T1 T2)
            have cr:"(r1, l1, r2) \<in> sts_critical_peaks R" using leq lr1 lr2
              unfolding sts_critical_peaks_def 
              by (smt (verit, del_insts) UnI2 append.right_neutral append_Nil mem_Collect_eq)
            have "\<exists>C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and>
                (l, m, r) \<in> sts_critical_peaks R"
              by (rule exI[of _ D], rule exI[of _ r1], rule exI[of _ l1],
                  rule exI[of _ r2], simp add: s t u cr)  
            then show ?thesis by auto
          next
            case False
            define befadd where "befadd = bef @ w1"
            hence s:"s = befadd @ l1 @ w2 @ aft" unfolding befadd_def using s1 by simp
            have t:"t = befadd @ r1 @ w2 @ aft" unfolding befadd_def using t by simp
            have u:"u = befadd @ r2 @ w4 @ aft" unfolding befadd_def using u T1 by simp
            from sts_critical_peaks_left_overlap[of l1 r1 R l2 r2 s befadd w2 aft w4 t u]
            show ?thesis using T1 befadd_def lr1 lr2 s s2 t u False by fastforce 
          qed
        next
          case False
          from sts_critical_peaks_overlap[of l1 r1 R l2 r2 s bef w1 w2 aft w3 w4 t u]
          show ?thesis using False lr1 lr2 s1 s2 t u w13e w24e by blast
        qed
      qed
    qed
  qed
qed

lemma sts_critical_pairs_peak:
  fixes R :: "sts"
  assumes cp: "(l, r) \<in> sts_critical_pairs R"
  shows "\<exists>m. (l, m, r) \<in> sts_critical_peaks R"
proof -
  from cp have sts_un:"(l, r) \<in> {(v @ y, x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}"  (is "_ \<in> ?X \<union> ?Y") unfolding sts_critical_pairs_def by simp
  then show "\<exists>m. (l, m, r) \<in> sts_critical_peaks R"
  proof(cases "(l, r) \<in> ?X")
    case True
    then show ?thesis
    proof(clarsimp)
      fix x y u v u' v'
      assume uv:"(u, v) \<in> R" and "r = x @ v'" and "l = v @ y"
      and u'v:"(u', v') \<in> R"
      and u'y:"u @ y = x @ u'"
      and "length x < length u"
      then show "\<exists>m. (v @ y, m, x @ v') \<in> sts_critical_peaks R" using u'y uv u'v
        by (intro exI[of _ "x @ u'"], simp add:sts_critical_peaks_def, metis)
    qed
  next
    case False
    then have "(l, r) \<in> ?Y" using sts_un by blast
    then show ?thesis by blast
  qed
qed


lemma sts_critical_peak_pairs:
  fixes R :: "sts"
  assumes cp: "(l, m, r) \<in> sts_critical_peaks R"
  shows "(l, r) \<in> sts_critical_pairs R"
proof -
  from cp have sts_un:"(l, m, r) \<in> {(v @ y, x @ u', x @ v') | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u @ y = x @ u' \<and> length x < length u} \<union> {(v, x @ u' @ y, x @ v' @ y) | x y u v u' v'. (u, v) \<in> R \<and> (u', v') \<in> R \<and>
    u = x @ u' @ y}"  (is "_ \<in> ?X \<union> ?Y") unfolding sts_critical_peaks_def by simp
  then show "(l, r) \<in> sts_critical_pairs R"
  proof(cases "(l, m, r) \<in> ?X")
    case True
    then show ?thesis
    proof(clarsimp)
      fix x y u v u' v'
      assume uv:"(u, v) \<in> R" and "r = x @ v" and "l = v' @ y"
      and u'v:"(u', v') \<in> R"
      and u'y:"u' @ y = x @ u"
      and "length x < length u'"
      then show "(v' @ y, x @ v) \<in> sts_critical_pairs R" using u'y uv u'v
        by (simp add:sts_critical_pairs_def, metis)
    qed
  next
    case False
    then have "(l, m, r) \<in> ?Y" using sts_un by blast
    then show ?thesis 
      by (smt (verit, best) Pair_inject UnI2 mem_Collect_eq sts_critical_pairs_def)
  qed
qed

lemma sts_critical_pairs_ststeps:
  fixes R :: "sts"
  assumes cp: "(l, r) \<in> sts_critical_pairs R"
  shows "(l, r) \<in> (ststep R)\<inverse> O ststep R"
proof -
  from cp obtain m where ml:"(m, l) \<in> ststep R" and mr:"(m, r) \<in> ststep R"
    unfolding sts_critical_pairs_def sts_critical_peaks_def
    using cp sts_critical_peak_steps
    by (meson sts_critical_pairs_peak) 
  then show "(l, r) \<in> (ststep R)\<inverse> O ststep R" by auto
qed

lemma sts_critical_pairs_complete:
  fixes R :: "sts"
  assumes cp: "(l, r) \<in> sts_critical_pairs R"
    and no_join: "(l, r) \<notin> (ststep R)\<^sup>\<down>"
  shows "\<not> WCR (ststep R)"
proof 
  assume asm:"WCR (ststep R)"
  from sts_critical_pairs_ststeps[OF cp]
  obtain u where ul:"(u, l) \<in> ststep R" and ur:"(u, r) \<in> ststep R" by auto
  with ul ur asm have "(l, r) \<in> (ststep R)\<^sup>\<down>" by auto
  with no_join show False by simp
qed

(* Lemma 7 *)
lemma sts_critical_pairs_main:
  fixes R :: "sts"
  assumes st: "(s, t) \<in> ststep R" and su: "(s, u) \<in> ststep R"
  shows "(t, u) \<in> (ststep R)\<^sup>\<down> \<or>
    (\<exists> C l r. t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, r) \<in> sts_critical_pairs R \<or> (r, l) \<in> sts_critical_pairs R))"
proof -
  from sts_critical_peaks_main_ststep[OF st su]
  have "(t, u) \<in> (ststep R)\<^sup>\<down> \<or>
    (\<exists> C l m r. s = C\<llangle>m\<rrangle> \<and> t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, m, r) \<in> sts_critical_peaks R \<or> (r, m, l) \<in> sts_critical_peaks R))" by auto
  with sts_critical_peak_pairs
  show ?thesis by blast    
qed

lemma sts_critical_pairs: assumes cp: "\<And> l r. (l, r) \<in> sts_critical_pairs R \<Longrightarrow> (l, r) \<in> (ststep R)\<^sup>\<down>"
  shows "WCR (ststep R)"
proof
  fix s t u
  assume st:"(s, t) \<in> ststep R" and su:"(s, u) \<in> ststep R"
  from sts_critical_pairs_main[OF st su]
  have main:"(t, u) \<in> (ststep R)\<^sup>\<down> \<or>
    (\<exists> C l r. t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, r) \<in> sts_critical_pairs R \<or> (r, l) \<in> sts_critical_pairs R))" by auto
  let ?cp = "(\<exists> C l r. t = C\<llangle>l\<rrangle> \<and> u = C\<llangle>r\<rrangle> \<and> 
    ((l, r) \<in> sts_critical_pairs R \<or> (r, l) \<in> sts_critical_pairs R))"
  from main show "(t, u) \<in> (ststep R)\<^sup>\<down>"
  proof
    assume "(t, u) \<in> (ststep R)\<^sup>\<down>"
    then show ?thesis by simp
  next
    assume "?cp"
    then obtain C l r where t:"t = C\<llangle>l\<rrangle>" and u:"u = C\<llangle>r\<rrangle>" and 
      "(l, r) \<in> sts_critical_pairs R \<or> (r, l) \<in> sts_critical_pairs R" by auto
    with cp have "\<exists> s. (l, s) \<in> (ststep R)\<^sup>* \<and> (r, s) \<in> (ststep R)\<^sup>*" by blast
    hence "(l, r) \<in> (ststep R)\<^sup>\<down>" by auto
    hence "(t, u) \<in> (ststep R)\<^sup>\<down>" using t u sctxt.closed_comp sctxt.closed_converse 
      by (simp add: join_def sctxt_closed_ststep sctxt.closedD sctxt.closed_rtrancl)
    then show ?thesis by auto
  qed
qed

(* Lemma 8*)
lemma sts_critical_pair_lemma:
 "WCR (ststep R) \<longleftrightarrow> (\<forall> (s, t) \<in> sts_critical_pairs R. (s, t) \<in> (ststep R)\<^sup>\<down>)"
  (is "?lhs = ?rhs")
proof
  assume ?lhs
  with sts_critical_pairs_complete
  show ?rhs by auto
next
  assume asm:?rhs
  show ?lhs                                                
  proof (rule sts_critical_pairs)
    fix l r
    assume lr:"(l, r) \<in> sts_critical_pairs R"
    from asm obtain u where lu:"(l, u) \<in> (ststep R)\<^sup>*" and ru:"(r, u) \<in> (ststep R)\<^sup>*" unfolding join_def 
      using lr asm by fastforce
    then show "(l, r) \<in> (ststep R)\<^sup>\<down>" by (simp add: joinI)
  qed
qed

(* Theorem 9 *)
theorem sts_critical_pair_CR:
  fixes R :: "sts"
  assumes sn: "SN (ststep R)"
  shows "CR (ststep R) \<longleftrightarrow>
    (\<forall> (s, t) \<in> sts_critical_pairs R. (s, t) \<in> (ststep R)\<^sup>\<down>)"  (is "?lhs = ?rhs")
proof
  assume ?lhs
  then show ?rhs using sts_critical_pair_lemma WCR_onI 
    by (meson partially_localize_CR r_into_rtrancl sts_critical_pairs_peak sts_critical_peak_steps)
next
  assume ?rhs
  then show ?lhs
    by (simp add: Newman sn sts_critical_pairs)
qed

end