(*
Author:  Dohan Kim <dohan.kim@uibk.ac.at> (2025)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>ShortLex: Length-Lexicographic Order\<close>

theory ShortLex
  imports
   "Abstract-Rewriting.Abstract_Rewriting"
   "Ord.Term_Order"
   "Knuth_Bendix_Order.Lexicographic_Extension"
begin

datatype sctxt =
  Hole ("\<circle>") |
  More "string" "sctxt" "string"

fun sctxt_apply_string :: "sctxt \<Rightarrow> string \<Rightarrow> string" ("_\<llangle>_\<rrangle>" [900, 0] 900)
  where
    hole: "\<circle>\<llangle>s\<rrangle> = s" |
    more: "(More ss1 C ss2)\<llangle>s\<rrangle>  = (ss1 @ (C\<llangle>s\<rrangle>) @ ss2)"

fun sctxt_compose :: "sctxt \<Rightarrow> sctxt \<Rightarrow> sctxt" (infixl "\<circ>\<^sub>l" 75)
  where
    "\<circle> \<circ>\<^sub>l D = D" |
    "(More ss1 C ss2) \<circ>\<^sub>l D = More ss1 (C \<circ>\<^sub>l D) ss2"

lemma sctxt_compose[simp]: "(C \<circ>\<^sub>l D)\<llangle>t\<rrangle> = C\<llangle>D\<llangle>t\<rrangle>\<rrangle>" by (induct C) simp_all

lemma empty_append [simp]: "l = [] @ l @ []" by simp

definition cancellation_property :: "string rel \<Rightarrow> bool" where
  "cancellation_property R \<longleftrightarrow> (\<forall>u v w. (u @ w, v @ w) \<in> R  \<longrightarrow> (u, v) \<in> R)"

interpretation sctxt: rel_closure "sctxt_apply_string" "\<circle>" "(\<circ>\<^sub>l)" 
  using sctxt_compose by (simp add: rel_closure.intro)

lemma sctxt_closed_strings: assumes sc:"sctxt.closed R"
  and st:"(s, t) \<in> R"
shows "\<forall>u v. (u @ s @ v, u @ t @ v) \<in> R" using assms
proof -
  from sc st obtain C where "(C\<llangle>s\<rrangle>, C\<llangle>t\<rrangle>) \<in> R" by blast
  then show ?thesis 
    by (metis ShortLex.more sc sctxt.closure.intros sctxt.closure_id sctxt.cop_nil st)
qed

lemma sctxt_app [simp]: "\<exists>bef aft. C\<llangle>l\<rrangle> = bef @ l @ aft" 
  using  sctxt_apply_string.simps
proof (induct "C")
  case Hole
  then show ?case using empty_append by metis
next
  case (More x1 D x2)
  then show ?case 
    by (metis append.assoc)
qed

lemma sctxt_app_step [simp]: "\<exists>bef aft. C\<llangle>l\<rrangle> = (bef @  l @ aft) \<and> C\<llangle>r\<rrangle> = (bef @ r @ aft)"
  using  sctxt_apply_string.simps  sctxt_app 
proof (induct "C")
  case Hole
  then show ?case using empty_append by metis
next
  case (More x1 D x3)
  then show ?case by (metis append_eq_appendI)
qed

lemma sctxt_strings[simp]: assumes C:"(C\<llangle>s\<rrangle> , C\<llangle>t\<rrangle>) \<in> R"
  shows "\<exists>u v. (u @ s @ v , u @ t @ v) \<in> R" using assms
  by (metis sctxt_app_step)

lemma sublist_sctxt[simp]: "sublist m l \<Longrightarrow> \<exists>C. l = C\<llangle>m\<rrangle>"
proof -
  assume "sublist m l"
  hence "\<exists>bef aft. l = bef @ m @ aft" 
    by (simp add: sublist_def)
  then show "\<exists>C. l = C\<llangle>m\<rrangle>" 
    by (metis sctxt.cop_nil more)
qed

lemma sublist_sctxt2[simp]: "l = C\<llangle>m\<rrangle> \<Longrightarrow> sublist m l"
proof -
  assume "l = C\<llangle>m\<rrangle>"
  hence "\<exists>bef aft. l = bef @ m @ aft" 
    by (simp add: sublist_def)
  then show "sublist m l"
    by force
qed

locale sts_co_rewrite_pair = 
  fixes S :: "string rel"
    and NS :: "string rel"
  assumes refl_NS: "refl NS"
    and trans_NS: "trans NS"
    and sctxt_NS: "sctxt.closed NS"
    and disj_NS_S: "NS \<inter> (S^-1) = {}"
begin
  lemma refl_NS_point: "(s, s) \<in> NS" using refl_NS unfolding refl_on_def by blast
end

locale sts_co_rewrite_pair_extended = sts_co_rewrite_pair S NS   
  for S NS :: "string rel" +
  assumes sctxt_S: "sctxt.closed (S^-1)"

locale lex =
  fixes prc :: "char \<Rightarrow> char \<Rightarrow> bool"
  assumes prc_irrefl: "\<not> prc a a"
    and prc_trans: "prc a b \<Longrightarrow> prc b c \<Longrightarrow> prc a c" 
begin

abbreviation prc_s (infix "\<succ>\<^sub>p" 50) where "s \<succ>\<^sub>p t \<equiv> prc s t"
abbreviation prc_ns (infix "\<succeq>\<^sub>p" 50) where "s \<succeq>\<^sub>p t \<equiv> prc s t \<or> s = t"
abbreviation prc_inv_s (infix "\<prec>\<^sub>p" 50) where "s \<prec>\<^sub>p t \<equiv> t \<succ>\<^sub>p s"
abbreviation prc_inv_ns (infix "\<preceq>\<^sub>p" 50) where "s \<preceq>\<^sub>p t \<equiv> t \<succeq>\<^sub>p s"

fun lexorder :: "string \<Rightarrow> string \<Rightarrow> bool" where 
  "lexorder s t = (\<exists>u1 u2 u3 ch1 ch2. s = u1 @ [ch1] @ u2 \<and> t = u1 @ [ch2] @ u3 \<and> ch1 \<succ>\<^sub>p ch2)"

abbreviation lex_s (infix "\<succ>\<^sub>l\<^sub>e\<^sub>x" 50) where "s \<succ>\<^sub>l\<^sub>e\<^sub>x t \<equiv> lexorder s t"
abbreviation lex_ns (infix "\<succeq>\<^sub>l\<^sub>e\<^sub>x" 50) where "s \<succeq>\<^sub>l\<^sub>e\<^sub>x t \<equiv> lexorder s t \<or> s = t"

fun co_lexorder :: "string \<Rightarrow> string \<Rightarrow> bool" where 
  "co_lexorder s t = (\<not> (t \<succeq>\<^sub>l\<^sub>e\<^sub>x s))"

abbreviation co_lex_s (infix "\<succ>\<^sub>c\<^sub>o\<^sub>l\<^sub>e\<^sub>x" 50) where "s \<succ>\<^sub>c\<^sub>o\<^sub>l\<^sub>e\<^sub>x t \<equiv> co_lexorder s t"

abbreviation "lex_S \<equiv> {(s,t). s \<succ>\<^sub>l\<^sub>e\<^sub>x t}"
abbreviation "lex_NS \<equiv> {(s,t). s \<succeq>\<^sub>l\<^sub>e\<^sub>x t}"
abbreviation "co_lex_S \<equiv> {(s,t). s \<succ>\<^sub>c\<^sub>o\<^sub>l\<^sub>e\<^sub>x t}"

(* In the literature, if a string t is a strict prefix of s, then it is often the case that s \<succ>\<^sub>l\<^sub>e\<^sub>x t. 
  We exclude this case because in that case, \<succ>\<^sub>l\<^sub>e\<^sub>x is not closed under contexts. 
  For example, given the precedence a > b > c, aaac \<succ>\<^sub>l\<^sub>e\<^sub>x aaa does not imply baaacb \<succ>\<^sub>l\<^sub>e\<^sub>x baaab.
  In fact, baaab \<succ>\<^sub>l\<^sub>e\<^sub>x baaacb. In this example, we have aaac \<succ>\<^sub>c\<^sub>o\<^sub>l\<^sub>e\<^sub>x aaa instead of aaac \<succ>\<^sub>l\<^sub>e\<^sub>x aaa *)

lemma lexorder_trans: "lexorder s t \<Longrightarrow> lexorder t u \<Longrightarrow> lexorder s u"
proof -
  assume lst:"lexorder s t" and ltu:"lexorder t u"
  from lst have "\<exists>u1 u2 u3 v w. s = u1 @ [v] @ u2 \<and> t = u1 @ [w] @ u3 \<and> v \<succ>\<^sub>p w"
    unfolding lexorder.simps by metis
  then obtain u1 u2 u3 v w where s:"s = u1 @ [v] @ u2" and t1:"t = u1 @ [w] @ u3"
    and vw:"v \<succ>\<^sub>p w" by blast
  from ltu have "\<exists>l1 l2 l3 p q. t = l1 @ [p] @ l2 \<and> u = l1 @ [q] @ l3 \<and> p \<succ>\<^sub>p q" 
    unfolding lexorder.simps by metis
  then obtain l1 l2 l3 p q where t2:"t = l1 @ [p] @ l2" and u:"u = l1 @ [q] @ l3" 
    and pq:"p \<succ>\<^sub>p q" by blast
  then show ?thesis
  proof(cases "length u1 = length l1")
    case True
    hence "w = p" using t1 t2 by simp
    hence wq:"w \<succ>\<^sub>p q" using pq by simp
    then show ?thesis unfolding lexorder.simps using True prc_trans 
        s u wq vw t1 t2 append_eq_append_conv by metis
  next
    case False note F1 = this
    then show ?thesis
    proof(cases "length u1 < length l1")
      case True
      hence "take (length u1) l1 = u1" 
        by (metis append_eq_append_conv_if leD t1 t2)
      hence "\<exists>r. l1 = u1 @ [w] @ r" using t1 t2 True
        by (metis Cons_eq_appendI Cons_nth_drop_Suc append_eq_conv_conj append_self_conv2 nth_append_length nth_take)
      then obtain r where l1:"l1 = u1 @ [w] @ r" by auto
      from l1 u have "u = u1 @ [w] @ r @ [q] @ l3" by simp
      with vw show ?thesis
        by (simp add: lexorder.elims vw s u; blast) 
    next
      case False note F2 = this
      from F1 F2 have lu1l1:"length u1 > length l1" by simp
      hence "take (length l1) u1 = l1" using F2
        by (metis append_eq_append_conv_if linorder_le_less_linear t1 t2)
      hence "\<exists>r. u1 = l1 @ [p] @ r" using t2 t1 F1 F2 lu1l1 
      proof -
        have "u1 ! length l1 = p"
          by (metis (no_types) append_Cons append_eq_conv_conj lu1l1 nth_append_length nth_take t1 t2)
        then show ?thesis
          by (metis (no_types) \<open>take (length l1) u1 = l1\<close> append_assoc append_eq_conv_conj append_one_prefix lu1l1 prefix_def)
      qed
      then obtain r where "u1 = l1 @ [p] @ r" by auto
      then show ?thesis 
        by (metis append_assoc lexorder.elims(3) pq s u)
    qed
  qed
qed

lemma sctxt_closed_lex_S_pre[simp]: "s \<succ>\<^sub>l\<^sub>e\<^sub>x t \<Longrightarrow> (bef @ s @ aft) \<succ>\<^sub>l\<^sub>e\<^sub>x (bef @ t @ aft)"
proof -
  assume asm:"s \<succ>\<^sub>l\<^sub>e\<^sub>x t"
  then show ?thesis
  proof - 
    have "\<exists>u1 u2 u3 v w. s = u1 @ [v] @ u2 \<and> t = u1 @ [w] @ u3 \<and> v \<succ>\<^sub>p w" unfolding lexorder.simps using asm by auto
    then obtain u1 u2 u3 v w where s:"s = u1 @ [v] @ u2" and t:"t = u1 @ [w] @ u3" and vw:"v \<succ>\<^sub>p w" by auto
    have "\<exists>u1 u2 u3 v w. bef @ s @ aft = u1 @ [v] @ u2 \<and> bef @ t @ aft = u1 @ [w] @ u3 \<and> v \<succ>\<^sub>p w" 
      by (rule exI[of _ "bef @ u1"], rule exI[of _ "u2 @ aft"], rule exI[of _ "u3 @ aft"], 
          rule exI[of _ "v"], rule exI[of _ "w"], insert s t vw, auto)
    hence "bef @ s @ aft \<succ>\<^sub>l\<^sub>e\<^sub>x bef @ t @ aft" unfolding lexorder.simps using asm by auto
    then show ?thesis using asm unfolding lexorder.simps by auto
  qed
qed

lemma sctxt_closed_lex_NS_pre[simp]: "s \<succeq>\<^sub>l\<^sub>e\<^sub>x t \<Longrightarrow> (bef @ s @ aft) \<succeq>\<^sub>l\<^sub>e\<^sub>x (bef @ t @ aft)"
proof -
  assume asm:"s \<succeq>\<^sub>l\<^sub>e\<^sub>x t"
  then show ?thesis
  proof (cases "s = t")
    case True
    hence "bef @ s @ aft = bef @ t @ aft" by simp
    then show ?thesis unfolding lexorder.simps by simp
  next
    case False
    then show ?thesis using sctxt_closed_lex_S_pre asm by auto
  qed
qed

lemma sctxt_closed_lex_S[simp]: "s \<succ>\<^sub>l\<^sub>e\<^sub>x t \<Longrightarrow> C\<llangle>s\<rrangle> \<succ>\<^sub>l\<^sub>e\<^sub>x C\<llangle>t\<rrangle>" using sctxt_closed_lex_S_pre 
  by (metis sctxt_app_step)

lemma sctxt_closed_lex_NS[simp]: "s \<succeq>\<^sub>l\<^sub>e\<^sub>x t \<Longrightarrow> C\<llangle>s\<rrangle> \<succeq>\<^sub>l\<^sub>e\<^sub>x C\<llangle>t\<rrangle>" using sctxt_closed_lex_NS_pre 
  by (metis sctxt_app_step)

lemma compat_lex_NS_S_point: "(s, t) \<in> lex_NS \<Longrightarrow> (t, u) \<in> lex_S \<Longrightarrow> (s, u) \<in> lex_S"
  using lexorder_trans by blast

lemma compat_lex_S_NS_point: "(s, t) \<in> lex_S \<Longrightarrow> (t, u) \<in> lex_NS \<Longrightarrow> (s, u) \<in> lex_S"
  using lexorder_trans by blast

lemma refl_lex_NS:"refl lex_NS" by (simp add: reflI)

lemma irrefl_lex_S:"irrefl lex_S" by (simp add: irreflI prc_irrefl)

lemma co_compat_main:"lex_NS \<inter> (co_lex_S)^-1 = {}" by auto

lemma co_compat:"lex_NS \<inter> (lex_S)^-1 = {}"
proof(rule ccontr)
  assume asm:"\<not> ?thesis"
  hence ctr: "lex_NS \<inter> (lex_S)^-1 \<noteq> {}" by simp
  then obtain a b where ab:"(a, b) \<in> lex_NS" and "(a, b) \<in> (lex_S)^-1" by blast
  hence "(b, a) \<in> lex_S" by auto
  hence "(a, a) \<in> lex_S" using ab compat_lex_NS_S_point by blast
  then show False using irrefl_lex_S
    by (meson irreflD)
qed

theorem co_rewrite_pair_lex_co_lex: "sts_co_rewrite_pair co_lex_S lex_NS"
proof
  show "refl lex_NS" using refl_lex_NS by auto
  show "trans lex_NS" using lexorder_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed lex_NS" 
    using sctxt.closedI sctxt_closed_lex_NS by force
  show "lex_NS \<inter> co_lex_S\<inverse> = {}" using co_compat_main by auto
qed

proposition co_rewrite_pair_lex: "sts_co_rewrite_pair lex_S lex_NS"
proof
  show "refl lex_NS" using refl_lex_NS by auto
  show "trans lex_NS" using lexorder_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed lex_NS" 
    using sctxt.closedI sctxt_closed_lex_NS by force
  show "lex_NS \<inter> lex_S\<inverse> = {}" using co_compat by auto
qed

proposition co_rewrite_pair_extended_lex: "sts_co_rewrite_pair_extended lex_S lex_NS"
proof
  show "refl lex_NS" using refl_lex_NS by auto
  show "trans lex_NS" using lexorder_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed lex_NS" 
    using sctxt.closedI sctxt_closed_lex_NS by force
  show "lex_NS \<inter> lex_S\<inverse> = {}" using co_compat by auto
  show "sctxt.closed (lex_S\<inverse>)" using sctxt.closedI sctxt_closed_lex_S by force
qed

end

context lex
begin

fun lenorder :: "string \<Rightarrow> string \<Rightarrow> bool" where 
  "lenorder s t = (length s > length t)" 

abbreviation len_s (infix "\<succ>\<^sub>l\<^sub>e\<^sub>n" 50) where "s \<succ>\<^sub>l\<^sub>e\<^sub>n t \<equiv> lenorder s t"
abbreviation len_ns (infix "\<succeq>\<^sub>l\<^sub>e\<^sub>n" 50) where "s \<succeq>\<^sub>l\<^sub>e\<^sub>n t \<equiv> lenorder s t \<or> s = t"

abbreviation "len_S \<equiv> {(s,t). s \<succ>\<^sub>l\<^sub>e\<^sub>n t}"
abbreviation "len_NS \<equiv> {(s,t). s \<succeq>\<^sub>l\<^sub>e\<^sub>n t}"

lemma lenorder_trans: "lenorder s t \<Longrightarrow> lenorder t u \<Longrightarrow> lenorder s u"
proof -
  assume lst:"lenorder s t" and ltu:"lenorder t u"
  then show ?thesis by auto
qed

lemma sctxt_len_closed[simp]: "s \<succeq>\<^sub>l\<^sub>e\<^sub>n t \<Longrightarrow> (bef @ s @ aft) \<succeq>\<^sub>l\<^sub>e\<^sub>n (bef @ t @ aft)"
proof -
  assume asm:"s \<succeq>\<^sub>l\<^sub>e\<^sub>n t"
  then show ?thesis by (cases "s = t", auto)
qed

lemma sctxt_len_closed_S[simp]: "s \<succeq>\<^sub>l\<^sub>e\<^sub>n t \<Longrightarrow> C\<llangle>s\<rrangle> \<succeq>\<^sub>l\<^sub>e\<^sub>n C\<llangle>t\<rrangle>" using sctxt_len_closed 
  sctxt_app_step[of C s t] by force

lemma compat_len_NS_S_point: "(s, t) \<in> len_NS \<Longrightarrow> (t, u) \<in> len_S \<Longrightarrow> (s, u) \<in> len_S"
  using lenorder_trans by blast

lemma compat_len_S_NS_point: "(s, t) \<in> len_S \<Longrightarrow> (t, u) \<in> len_NS \<Longrightarrow> (s, u) \<in> len_S"
  using lenorder_trans by blast

lemma refl_len_NS:"refl len_NS" by (simp add: reflI)

lemma irrefl_len_S:"irrefl len_S" by (simp add: irreflI prc_irrefl)

lemma co_compat_lenorder:"len_NS \<inter> (len_S)^-1 = {}"
proof(rule ccontr)
  assume asm:"\<not> ?thesis"
  hence ctr: "len_NS \<inter> (len_S)^-1 \<noteq> {}" by simp
  then obtain a b where ab:"(a, b) \<in> len_NS" and "(a, b) \<in> (len_S)^-1" by blast
  hence "(b, a) \<in> len_S" by auto
  hence "(a, a) \<in> len_S" using ab compat_len_NS_S_point by blast
  then show False using irrefl_len_S
    by (meson irreflD)
qed

theorem co_rewrite_pair_len: "sts_co_rewrite_pair len_S len_NS"
proof
  show "refl len_NS" using refl_len_NS by auto
  show "trans len_NS" using lenorder_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed len_NS" using sctxt.closedI sctxt_len_closed_S by force
  show "len_NS \<inter> len_S\<inverse> = {}" using co_compat_lenorder by auto
qed

(* Compare lengths first and then use lexicographic order *)

fun shortlex :: "string \<Rightarrow> string \<Rightarrow> bool"
  where "shortlex str1 str2 = (if lenorder str1 str2 then True
          else if lenorder str2 str1 then False else lexorder str1 str2)"

abbreviation shortlex_s (infix "\<succ>\<^sub>s\<^sub>l" 50) where "s \<succ>\<^sub>s\<^sub>l t \<equiv> shortlex s t"
abbreviation shortlex_ns (infix "\<succeq>\<^sub>s\<^sub>l" 50) where "s \<succeq>\<^sub>s\<^sub>l t \<equiv> shortlex s t \<or> s = t"

abbreviation shortlex_inv_s (infix "\<prec>\<^sub>s\<^sub>l" 50) where "s \<prec>\<^sub>s\<^sub>l t \<equiv> t \<succ>\<^sub>s\<^sub>l s"

abbreviation "shortlex_S \<equiv> {(s,t). s \<succ>\<^sub>s\<^sub>l t}"
abbreviation "shortlex_NS \<equiv> {(s,t). s \<succeq>\<^sub>s\<^sub>l t}"

fun co_shortlex :: "string \<Rightarrow> string \<Rightarrow> bool" where 
  "co_shortlex s t = (\<not> (t \<succeq>\<^sub>s\<^sub>l s))" 

abbreviation co_shortlex_s (infix "\<succ>\<^sub>c\<^sub>o\<^sub>s\<^sub>l" 50) where "s \<succ>\<^sub>c\<^sub>o\<^sub>s\<^sub>l t \<equiv> co_shortlex s t"
abbreviation "co_shortlex_S \<equiv> {(s,t). s \<succ>\<^sub>c\<^sub>o\<^sub>s\<^sub>l t}"

lemma shortlex_trans[simp]: "s \<succ>\<^sub>s\<^sub>l t \<Longrightarrow> t \<succ>\<^sub>s\<^sub>l u \<Longrightarrow> s \<succ>\<^sub>s\<^sub>l u"
proof -
  assume st:"s \<succ>\<^sub>s\<^sub>l t" and tu:"t \<succ>\<^sub>s\<^sub>l u"
  then show "s \<succ>\<^sub>s\<^sub>l u"
  proof(cases "length s = length t")
    case False
    hence "length s > length u" using st tu  
        using linorder_neqE_nat by fastforce        
    then show ?thesis unfolding shortlex.simps by simp
  next
    case True note T1 = this
    then show ?thesis
    proof(cases "length t = length u")
      case False
      hence "length s > length u" using st tu  
        using linorder_neqE_nat by fastforce
      then show ?thesis unfolding shortlex.simps by simp
    next
      case True note T2 = this
      hence lenst:"length s = length t" and lentu:"length t = length u" 
        using T1 T2 by auto
      from st lenst have lst:"s \<succ>\<^sub>l\<^sub>e\<^sub>x t" unfolding shortlex.simps by auto 
      from tu lentu have ltu:"t \<succ>\<^sub>l\<^sub>e\<^sub>x u" unfolding shortlex.simps by auto
      from lexorder_trans[OF lst ltu] have lsu:"s \<succ>\<^sub>l\<^sub>e\<^sub>x u" by auto
      from lenst lentu have lensu:"length s = length u" by auto
      from lsu lensu show ?thesis unfolding shortlex.simps by simp
    qed
  qed
qed

lemma sctxt_shortlex_closed_S_pre[simp]: "s \<succ>\<^sub>s\<^sub>l t \<Longrightarrow> (bef @ s @ aft)\<succ>\<^sub>s\<^sub>l (bef @ t @ aft)"
proof -
  assume asm:"s \<succ>\<^sub>s\<^sub>l t"
  then show ?thesis
  proof(cases "lenorder s t")
    case True
    then show ?thesis by simp
  next
    case False
    hence "lexorder s t"
      by (metis asm shortlex.elims(2))
    then show ?thesis using asm sctxt_closed_lex_S_pre by auto 
  qed
qed

lemma sctxt_shortlex_closed_NS_pre[simp]: "s \<succeq>\<^sub>s\<^sub>l t \<Longrightarrow> (bef @ s @ aft) \<succeq>\<^sub>s\<^sub>l (bef @ t @ aft)"
proof -
  assume st:"s \<succeq>\<^sub>s\<^sub>l t"
  then show ?thesis
  proof (cases "s = t")
    case True
    then show ?thesis by fastforce
  next
    case False
    hence "s \<succ>\<^sub>s\<^sub>l t" using st by auto
    hence "(bef @ s @ aft) \<succ>\<^sub>s\<^sub>l (bef @ t @ aft)" using sctxt_shortlex_closed_S_pre by metis
    then show ?thesis by auto
  qed
qed

lemma sctxt_shortlex_closed_S[simp]: "s \<succ>\<^sub>s\<^sub>l t \<Longrightarrow> C\<llangle>s\<rrangle> \<succ>\<^sub>s\<^sub>l C\<llangle>t\<rrangle>" using sctxt_shortlex_closed_S_pre
  sctxt_app_step[of C s t] by metis

lemma sctxt_shortlex_closed_inv_S[simp]: "s \<prec>\<^sub>s\<^sub>l t \<Longrightarrow> C\<llangle>s\<rrangle> \<prec>\<^sub>s\<^sub>l C\<llangle>t\<rrangle>" using sctxt_shortlex_closed_S_pre
  sctxt_app_step[of C s t] by metis 

lemma sctxt_shortlex_closed_NS[simp]: "s \<succeq>\<^sub>s\<^sub>l t \<Longrightarrow> C\<llangle>s\<rrangle> \<succeq>\<^sub>s\<^sub>l C\<llangle>t\<rrangle>" using sctxt_shortlex_closed_NS_pre
  sctxt_app_step[of C s t] by metis 

lemma compat_shortlex_NS_S_point[simp]: "(s, t) \<in> shortlex_NS \<Longrightarrow> (t, u) \<in> shortlex_S \<Longrightarrow> (s, u) \<in> shortlex_S"
  using shortlex_trans by blast

lemma compat_shortlex_S_NS_point[simp]: "(s, t) \<in> shortlex_S \<Longrightarrow> (t, u) \<in> shortlex_NS \<Longrightarrow> (s, u) \<in> shortlex_S"
  using shortlex_trans by blast

lemma compat_shortlex_NS_S[simp]:"shortlex_NS O shortlex_S \<subseteq> shortlex_S"
proof
  fix x y
  assume "(x, y) \<in> shortlex_NS O shortlex_S"
  then obtain z where "(x, z) \<in> shortlex_NS" and "(z, y) \<in> shortlex_S" by auto
  then show "(x, y) \<in> shortlex_S" using compat_shortlex_NS_S_point[of x z y] by auto+
qed

lemma compat_shortlex_S_NS[simp]:"shortlex_S O shortlex_NS \<subseteq> shortlex_S"
proof
  fix x y
  assume "(x, y) \<in> shortlex_S O shortlex_NS"
  then obtain z where "(x, z) \<in> shortlex_S" and "(z, y) \<in> shortlex_NS" by auto
  then show "(x, y) \<in> shortlex_S" using compat_shortlex_S_NS_point[of x z y] by auto+
qed

lemma refl_shortlex_NS:"refl shortlex_NS" by (simp add: reflI)

lemma irrefl_shortlex_S:"irrefl shortlex_S" by (simp add: irreflI prc_irrefl)

lemma sl_left_append_pre: assumes "s \<succ>\<^sub>s\<^sub>l u"
  shows "bef @ s \<succ>\<^sub>s\<^sub>l u" using assms
  by (auto, smt (z3) append_Cons append_Nil lexorder.elims(2))

lemma sl_left_append: assumes "\<forall>(u, v) \<in> S. t \<succ>\<^sub>s\<^sub>l u @ w  \<and> t \<succ>\<^sub>s\<^sub>l v @ w "
  shows "\<forall>(u, v) \<in> S. bef @ t \<succ>\<^sub>s\<^sub>l u @ w  \<and> bef @ t \<succ>\<^sub>s\<^sub>l v @ w "
proof -
  {
    fix u v
    assume "(u, v) \<in> S"
    with assms have "t \<succ>\<^sub>s\<^sub>l u @ w  \<and> t \<succ>\<^sub>s\<^sub>l v @ w" by auto
    hence "bef @ t \<succ>\<^sub>s\<^sub>l u @ w  \<and> bef @ t \<succ>\<^sub>s\<^sub>l v @ w" using sl_left_append_pre[of t "u @ w" bef] 
      by (auto, smt (z3) append_Cons lexorder.elims(2) self_append_conv2, 
          smt (z3) append.left_neutral append_Cons lexorder.elims(2))
  } then show ?thesis  using not_less_iff_gr_or_eq by fastforce+ 
qed
 
lemma sl_cancellation_property: assumes "(u @ w) \<succeq>\<^sub>s\<^sub>l (v @ w)"
  shows "u \<succeq>\<^sub>s\<^sub>l v" using assms 
proof(cases "length u = length v")
  case True
  note T1 = this
  hence lg:"(u @ w) \<succeq>\<^sub>l\<^sub>e\<^sub>x (v @ w)" using assms by auto
  then show ?thesis
  proof(cases "u = v")
    case True
    then show ?thesis by auto
  next
    case False
    hence "u \<noteq> [] \<and> v \<noteq> []" using T1 by auto
    hence "(u @ w) \<succ>\<^sub>l\<^sub>e\<^sub>x (v @ w)" using lg False by auto
    hence "(\<exists>u1 u2 u3 q r. u @ w = u1 @ [q] @ u2 \<and> v @ w = u1 @ [r] @ u3 \<and> q \<succ>\<^sub>p r)" by auto
    then obtain u1 u2 u3 q r where uw:"u @ w = u1 @ [q] @ u2" and vw:"v @ w = u1 @ [r] @ u3" and qr:"q \<succ>\<^sub>p r" by auto
    hence nqr:"q \<noteq> r" using prc_irrefl by blast
    hence "length (u1 @ [q]) = length (u1 @ [r])" by auto
    have *:"length u \<ge> length (u1 @ [q])"
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "length (u1 @ [q]) > length u" by auto
      then show False using nqr T1 
        by (auto, metis False append_eq_append_conv_if less_Suc_eq_le uw vw)
    qed
    have **:"length v \<ge> length (u1 @ [r])" 
    proof(rule ccontr)
      assume "\<not> ?thesis"
      hence "length (u1 @ [r]) > length v" by auto
      then show False using nqr T1
        by (auto, metis False append_eq_append_conv_if less_Suc_eq_le uw vw)
    qed
    have "\<exists>z1. u = u1 @ [q] @ z1" using * uw
      by (auto, metis Suc_le_eq append_Cons_nth_middle append_eq_append_conv_if id_take_nth_drop not_less_eq_eq nth_append)
    moreover have "\<exists>z2.  v = u1 @ [r] @ z2" using ** vw
      by (auto, metis Suc_le_eq append_Cons_nth_middle append_eq_append_conv_if id_take_nth_drop not_less_eq_eq nth_append)
    moreover have "length (u @ w) = length (v @ w)" using T1 by auto
    ultimately have "\<exists>u4 u5. u2 = u4 @ w \<and> u3 = u5 @ w" using uw vw by force
    hence "u \<succ>\<^sub>l\<^sub>e\<^sub>x v" using T1 False qr uw vw by fastforce
    then show ?thesis using T1 by auto 
  qed
next
  case False
  then show ?thesis 
    using assms by auto
qed

lemma shortlex_cancellation_property: "cancellation_property shortlex_NS" 
  using sl_cancellation_property unfolding cancellation_property_def by auto

lemma co_compat_shortlex_order_main:"shortlex_NS \<inter> (co_shortlex_S)^-1 = {}"
proof(rule ccontr)
  assume asm:"\<not> ?thesis"
  hence ctr: "shortlex_NS \<inter> (co_shortlex_S)^-1 \<noteq> {}" by simp
  then obtain a b where ab:"(a, b) \<in> shortlex_NS" and co_ab:"(a, b) \<in> (co_shortlex_S)^-1" by blast
  hence "(b, a) \<in> co_shortlex_S" by auto
  then show False using ab by force
qed

lemma co_compat_shortlex_order:"shortlex_NS \<inter> (shortlex_S)^-1 = {}"
proof(rule ccontr)
  assume asm:"\<not> ?thesis"
  hence ctr: "shortlex_NS \<inter> (shortlex_S)^-1 \<noteq> {}" by simp
  then obtain a b where ab:"(a, b) \<in> shortlex_NS" and "(a, b) \<in> (shortlex_S)^-1" by blast
  hence "(b, a) \<in> shortlex_S" by auto
  hence "(a, a) \<in> shortlex_S" using ab compat_shortlex_NS_S_point by blast
  then show False using irrefl_shortlex_S by (meson irreflD)
qed

proposition co_rewrite_pair_shortlex: "sts_co_rewrite_pair shortlex_S shortlex_NS"
proof
  show "refl shortlex_NS" using refl_shortlex_NS by auto
  show "trans shortlex_NS" using shortlex_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed shortlex_NS" using sctxt.closedI sctxt_shortlex_closed_NS by fastforce
  show "shortlex_NS \<inter> shortlex_S\<inverse> = {}" using co_compat_shortlex_order by auto
qed

theorem co_rewrite_pair_shortlex_co_shortlex: "sts_co_rewrite_pair co_shortlex_S shortlex_NS"
proof
  show "refl shortlex_NS" using refl_shortlex_NS by auto
  show "trans shortlex_NS" using shortlex_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed shortlex_NS" using sctxt.closedI sctxt_shortlex_closed_NS by fastforce
  show "shortlex_NS \<inter> co_shortlex_S\<inverse> = {}" using co_compat_shortlex_order_main by auto
qed

proposition co_rewrite_pair_extended_shortlex: "sts_co_rewrite_pair_extended shortlex_S shortlex_NS"
proof
  show "refl shortlex_NS" using refl_shortlex_NS by auto
  show "trans shortlex_NS" using shortlex_trans 
    by (smt (verit, best) case_prodD case_prodI mem_Collect_eq transI)
  show "sctxt.closed shortlex_NS" using sctxt.closedI sctxt_shortlex_closed_NS by fastforce
  show "shortlex_NS \<inter> shortlex_S\<inverse> = {}" using co_compat_shortlex_order by auto
  show "sctxt.closed (shortlex_S\<inverse>)"
    by (metis case_prodD case_prodI converse_iff mem_Collect_eq sctxt.closedI sctxt_shortlex_closed_S)
qed

end

locale shortlex_total = lex prc
  for prc :: "char \<Rightarrow> char \<Rightarrow> bool" +
  fixes prc_w :: "char \<Rightarrow> nat"
   and  prc_max :: nat
  assumes prc_asym: "prc a b \<Longrightarrow> \<not> prc b a"
    and prc_total: "a \<noteq> b  \<Longrightarrow> prc a b \<or> prc b a"
    and prc_weight: "prc a b \<Longrightarrow> prc_w a > prc_w b"
    and prc_max_weight: "prc_max > prc_w a"
    and prc_finite: "finite {(a, b). prc a b}"
    and prc_SN: "SN {(a, b). prc a b}"
begin

abbreviation "length_preserving_lex_S \<equiv> {(s,t). s \<succ>\<^sub>l\<^sub>e\<^sub>x t \<and> length s = length t}"

lemma minimal_shortlex[simp]:"\<forall>t. \<not> [] \<succ>\<^sub>s\<^sub>l t" 
  unfolding shortlex.simps by simp

lemma lex_tot: assumes snt:"s \<noteq> t"
  and len:"length s = length t"
shows "lexorder s t \<or> lexorder t s"
proof -
  from snt len
  have "\<exists>u1 u2 u3 v w. s = u1 @ [v] @ u2 \<and> t = u1 @ [w] @ u3 \<and> v \<noteq> w" 
    using same_length_different by fastforce
  then obtain u1 u2 u3 v w where s:"s = u1 @ [v] @ u2" and t:"t = u1 @ [w] @ u3" and vnw:"v \<noteq> w" by auto
  from vnw have "v \<succ>\<^sub>p w \<or> w \<succ>\<^sub>p v" using prc_total by auto
  then show ?thesis
  proof
    assume "v \<succ>\<^sub>p w"
    hence "lexorder s t"  using lexorder.simps s t vnw len by force
    then show ?thesis by blast
  next
    assume "w \<succ>\<^sub>p v"
    hence "lexorder t s" using lexorder.simps len s t vnw by force 
    then show ?thesis by blast
  qed
qed

lemma shortlex_total: assumes "s \<noteq> t"
  shows "s \<succ>\<^sub>s\<^sub>l t \<or> t\<succ>\<^sub>s\<^sub>l s"
proof -
  from assms have "(length s > length t \<or> length t > length s) \<or> (length s = length t \<and> 
    s \<noteq> t)" using nat_neq_iff by blast
  then show ?thesis
  proof
    assume "length s > length t \<or> length t > length s"
    then show ?thesis
    proof
      assume "length s > length t"
      hence "s\<succ>\<^sub>s\<^sub>l t" using shortlex.simps by simp
      then show ?thesis by blast
    next
      assume "length t > length s"
      hence "t \<succ>\<^sub>s\<^sub>l s" using shortlex.simps by simp
      then show ?thesis by blast
    qed
  next
    assume "length s = length t \<and> s \<noteq> t"
    hence len:"length s = length t" and snt:"s \<noteq> t" by auto
    from lex_tot[OF snt len]
    have "lexorder s t \<or> lexorder t s" by simp
    then show ?thesis
    proof
      assume "lexorder s t"
      then show ?thesis using len by fastforce
    next
      assume "lexorder t s"
      then show ?thesis using len by fastforce
    qed 
  qed
qed

lemma shortlex_comb[simp]: "shortlex_S = length_preserving_lex_S \<union> len_S" 
  unfolding shortlex.simps lexorder.simps
proof(safe, goal_cases)
  case (1 a b)
  hence "lexorder a b" unfolding lexorder.simps
    by (auto, metis append_Cons)
  then show ?case by simp
next
  case (2 a b)
  then show ?case
    by (meson lenorder.simps linorder_neqE_nat)
next
  case (3 a b u1 u2 u3 v w)
  then show ?case 
    by (metis lenorder.simps)
qed auto 

lemma SN_len_S: "SN len_S"
proof -
  let ?A = "{(a::nat, b). a > b}"
  from SN_nat_gt have SNA:"SN ?A" by simp
  then show ?thesis
  proof -
    {
      fix s :: string
      let ?S = "\<lambda>x. SN_on len_S {x}"
      have "?S s" unfolding SN_on_def
      proof (rule notI)
        assume "\<exists>f. f 0 \<in> {s} \<and> (\<forall>i. (f i, f (Suc i)) \<in> {(s, t). lenorder s t})" 
        then obtain S where s:"S 0 = s" and chainl:"chain len_S S" by auto
        let ?T = "\<lambda>i. length (S i)"
        from chainl have init:"?T 0 = length s" and chainT:"chain ?A ?T"  
          using s case_prod_conv chainl by auto
        from init chainT have "\<not> SN_on ?A {length s}"
          by (auto simp add:SN_def SN_on_def)
        hence *:"\<not> SN ?A" unfolding SN_def by auto
        then show False using SNA using * by blast
      qed
    } 
    from SN_I[OF this] show ?thesis by blast
  qed
qed

fun lex_ext_string :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool"
  where "lex_ext_string f [] [] = False" |
    "lex_ext_string f (_ # _) [] = False" |
    "lex_ext_string f [] (_ # _) = False" |
    "lex_ext_string f (a # as) (b # bs) =
      (if length (a # as) \<noteq> length (b # bs) then False else if f a b then True
      else if a = b then lex_ext_string f as bs
      else False)"

lemma lex_ext_string_irrefl[simp]:"\<not> lex_ext_string prc s s" 
  by (induct s, auto simp add: prc_irrefl)

lemma lex_ext_string_append[simp]: assumes "lex_ext_string prc s t"
  shows "lex_ext_string prc (s @ u) (t @ u)" using assms
proof(induct s arbitrary: t u)
  case Nil
  then show ?case using lex_ext_string.elims(2) by blast
next
  case (Cons c str)
  then show ?case
    by (smt (z3) append_Cons length_append lex_ext_string.elims(2) lex_ext_string.simps(4))
qed

lemma lex_ext_string_prepend[simp]: assumes "lex_ext_string prc s t"   
  shows "lex_ext_string prc (u @ s) (u @ t)" using assms
  by (induct u arbitrary: s t, auto, insert lex_ext_string.elims(2), fastforce)

lemma lex_ext_prc:assumes "s = u1 @ [v] @ u2"
  and t:"t = u1 @ [w] @ u3"
  and "length s = length t"
  and vw:"v \<succ>\<^sub>p w"
shows "lex_ext_string prc s t" using assms lex_ext_string_prepend by auto

lemma lex_prc_len:assumes "s \<succ>\<^sub>l\<^sub>e\<^sub>x t"
    and len:"length s = length t"
  shows "lex_ext_string prc s t" using assms
proof -
  from assms obtain u1 u2 u3 v w where s:"s = u1 @ [v] @ u2" and t:"t = u1 @ [w] @ u3" and vw:"v \<succ>\<^sub>p w"  and "length u2 = length u3" using len
    by auto
  then show ?thesis using lex_ext_prc[of s u1 v u2 t w u3] by auto
qed

lemma len_same_lex_ext_string: assumes "lex_ext_string prc s t"
  shows "length s = length t" using assms 
  by (induct s arbitrary:t, insert lex_ext_string.elims(2),auto, fastforce)

lemma pos_SN_lex_ext_string: assumes "SN {(s, t). lex_ext_string prc s t}"
  shows "\<forall>m. SN {(s, t). lex_ext_string prc s t \<and> length s = m}" using assms by fastforce

lemma lex_ext_string_characteristic :"\<forall>(u, v) \<in> {(s, t). lex_ext_string prc s t}. length u = length v" 
  using len_same_lex_ext_string by force

fun string_prc_weight :: "string \<Rightarrow> nat"
  where "string_prc_weight [] = 0" |
    "string_prc_weight (x # xs) = (prc_w x * (prc_max + 2)^(length xs + 1)) + string_prc_weight xs"

lemma prc_max_pow: "(prc_max + 2)^(length xs + 1) > string_prc_weight xs" using prc_max_weight
proof(induct xs)
  case Nil
  then show ?case using bot_nat_0.not_eq_extremum by force
next
  case (Cons c ss)
  hence "(prc_max + 2) ^ (length ss + 1) > string_prc_weight ss" by auto
  moreover have "string_prc_weight (c # ss) = (prc_w c * (prc_max + 2)^(length ss + 1)) + string_prc_weight ss" by auto
  moreover have "... < prc_w c * (prc_max + 2)^(length ss + 1) + (prc_max + 2)^(length ss + 1)" using calculation(1) by force
  moreover have "... < (prc_w c + 2) * (prc_max + 2)^(length ss + 1)" using prc_max_weight by fastforce
  moreover have "... < (prc_max + 2) * (prc_max + 2)^(length ss + 1)" using prc_max_weight by auto
  ultimately show ?case using prc_max_weight by (simp add: add.commute add_mono_thms_linordered_field(5) trans_less_add2)
qed

lemma lex_ext_string_prc_weight: assumes "lex_ext_string prc s t"
  shows "string_prc_weight s > string_prc_weight t" using assms
proof(induct s arbitrary: t)
  case Nil
  then show ?case using lex_ext_string.elims(2) by blast
next
  case (Cons a ss)
  then obtain b ts where t:"t = b # ts" using lex_ext_string.elims(2) by blast
  from Cons(2) have "a \<succ>\<^sub>p b \<or> (a = b \<and> lex_ext_string (\<succ>\<^sub>p) ss ts)" using t 
    by (auto, metis, argo)
  then show ?case
  proof
    assume asm:"a \<succ>\<^sub>p b"
    have "string_prc_weight (a # ss) = (prc_w a * (prc_max + 2)^(length ss + 1)) + string_prc_weight ss" by auto
    moreover have "string_prc_weight (b # ts) = (prc_w b * (prc_max + 2)^(length ts + 1)) + string_prc_weight ts" by auto
    moreover have "prc_w a > prc_w b" using asm by (simp add: prc_weight)
    moreover have "length ss = length ts" by (metis Cons.prems add_right_imp_eq list.size(4) 
          shortlex_total.len_same_lex_ext_string shortlex_total_axioms t)
    moreover have "(prc_w a * (prc_max + 2)^(length ss + 1)) - (prc_w b * (prc_max +2 )^(length ts + 1)) \<ge> (prc_max + 2)^(length ts + 1)"
      by (metis One_nat_def calculation(3) calculation(4) diff_is_0_eq diff_mult_distrib less_eq_Suc_le mult.commute mult.right_neutral mult_eq_0_iff zero_less_diff)
    ultimately show ?thesis using prc_max_weight t prc_max_pow[of ts] asm by auto
  next
    assume asm:"a = b \<and> lex_ext_string (\<succ>\<^sub>p) ss ts"
    hence "string_prc_weight ss > string_prc_weight ts" using Cons(1) by auto
    then show ?thesis using t asm len_same_lex_ext_string by auto
  qed
qed

lemma SN_prc_lex_ext: "SN {(s, t). lex_ext_string prc s t}" (is "SN ?T")
proof -
  {
    let ?A = "{(a::nat, b). a > b}"
    from SN_nat_gt have SNA:"SN ?A" by simp
    fix s :: string
    let ?S = "\<lambda>x. SN_on ?T {x}"
    have "?S s" unfolding SN_on_def
    proof (rule notI)
      assume "\<exists>f. f 0 \<in> {s} \<and> (\<forall>i. (f i, f (Suc i)) \<in> {(s, t). lex_ext_string prc s t})" 
      then obtain S where s:"S 0 = s" and chainl:"chain ?T S" by auto
      let ?U = "\<lambda>i. string_prc_weight (S i)"
      from chainl have init:"?U 0 = string_prc_weight s" and chainT:"chain ?A ?U"  
        using s case_prod_conv chainl lex_ext_string_prc_weight by auto
      from init chainT have "\<not> SN_on ?A {string_prc_weight s}"
        by (auto simp add:SN_def SN_on_def)
      hence *:"\<not> SN ?A" unfolding SN_def by auto
      then show False using SNA using * by blast
    qed
  } 
  from SN_I[OF this] show ?thesis by blast
qed

lemma lexcomp_SN: "SN length_preserving_lex_S"
proof -
  let ?A = "{(a::char, b). a \<succ>\<^sub>p b}"
  from prc_SN have SNA:"SN ?A" by simp
  then show ?thesis using lex_prc_len SN_prc_lex_ext
    by (smt (verit, ccfv_SIG) SN_on_def case_prodD case_prodI mem_Collect_eq)
qed

lemma disjoint_lexcomp_len:"len_S \<inter> length_preserving_lex_S = {}" by auto 

lemma shortlex_SN: "SN shortlex_S"
proof -
  have "shortlex_S = length_preserving_lex_S \<union> len_S" (is "_ = ?r \<union> ?s") using shortlex_comb by auto
  hence "trans (?r \<union> ?s)" using shortlex_trans 
    by (auto, smt (verit, best) case_prodD case_prodI mem_Collect_eq trans_onI)
  from SN_Un_conv[OF this]
  show ?thesis using SN_len_S lexcomp_SN shortlex_comb by argo
qed

sublocale shorlex_pair: SN_order_pair shortlex_S shortlex_NS
proof(unfold_locales) 
  show "refl shortlex_NS" by (simp add: reflI)
  show "trans shortlex_S" using shortlex_trans unfolding trans_def by blast
  show "trans shortlex_NS" using shortlex_trans unfolding trans_def by blast
  show "shortlex_NS O shortlex_S \<subseteq> shortlex_S" using compat_shortlex_NS_S by auto
  show "shortlex_S O shortlex_NS \<subseteq> shortlex_S" using compat_shortlex_S_NS by auto
  show "SN shortlex_S" using shortlex_SN by simp
qed

end
end