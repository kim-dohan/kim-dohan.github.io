(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012, 2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013, 2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Context_Substitution
imports
  First_Order_Rewriting.Trs
  "HOL-Library.Monad_Syntax"
begin


fun ctxt_subst :: "('f,'v)ctxt \<Rightarrow> ('f,'v)subst \<Rightarrow> nat \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term"
  where "ctxt_subst _ _ 0 t = t"
     |  "ctxt_subst C \<mu> (Suc n) t = C\<langle>(ctxt_subst C \<mu> n t) \<cdot> \<mu>\<rangle>"

fun ctxt_subst_ctxt :: "('f,'v)ctxt \<Rightarrow> ('f,'v)subst \<Rightarrow> nat \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)ctxt"
  where "ctxt_subst_ctxt _ _ 0 D = D"
     |  "ctxt_subst_ctxt C \<mu> (Suc n) D = C \<circ>\<^sub>c (ctxt_subst_ctxt C \<mu> n D \<cdot>\<^sub>c \<mu>)"


lemma ctxt_subst_ctxt: "ctxt_subst C \<mu> n (D\<langle>t\<rangle>) = (ctxt_subst_ctxt C \<mu> n D)\<langle>t \<cdot> \<mu>^^n\<rangle>"
  by (induct n, auto simp: subst_left_right)

lemma ctxt_subst_add[simp]: "ctxt_subst C \<mu> (n + m) t = ctxt_subst C \<mu> n (ctxt_subst C \<mu> m t)"
  by (induct n, auto)

lemma ctxt_subst_ctxt_add[simp]: "ctxt_subst_ctxt C \<mu> (n + m) D = ctxt_subst_ctxt C \<mu> n (ctxt_subst_ctxt C \<mu> m D)"
  by (induct n, auto)

lemma ctxt_subst_Suc: "ctxt_subst C \<mu> (Suc n) t = ctxt_subst C \<mu> n (C\<langle>t\<cdot>\<mu>\<rangle>)" (is "?l = _")
proof -
  have "?l = ctxt_subst C \<mu> (n + Suc 0) t" by simp
  from this[unfolded ctxt_subst_add] show ?thesis by simp
qed

lemma ctxt_subst_ctxt_Suc: "ctxt_subst_ctxt C \<mu> (Suc n) D = ctxt_subst_ctxt C \<mu> n (C \<circ>\<^sub>c (D \<cdot>\<^sub>c \<mu>))" (is "?l = _")
proof -
  have "?l = ctxt_subst_ctxt C \<mu> (n + Suc 0) D" by simp
  from this[unfolded ctxt_subst_ctxt_add] show ?thesis by simp
qed

lemma ctxt_subst_hole_pos[simp]: "hole_pos C ^ n \<in> poss (ctxt_subst C \<mu> n t)"
  by (induct n, auto)

lemma ctxt_subst_ctxt_hole_pos[simp]: "hole_pos (ctxt_subst_ctxt C \<mu> n D) = hole_pos C ^ n @ hole_pos D"
  by (induct n, auto)

lemma ctxt_subst_subst: "(ctxt_subst C \<mu> n t) \<cdot> \<mu> = ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu> n (t \<cdot> \<mu>)"
  by (induct n, auto)

lemma ctxt_subst_subst_pow: "(ctxt_subst C \<mu> n t) \<cdot> \<mu> ^^ k= ctxt_subst (C \<cdot>\<^sub>c (\<mu> ^^ k)) \<mu> n (t \<cdot> (\<mu> ^^ k))"
proof (induct k, force)
  case (Suc j)
  have "(ctxt_subst C \<mu> n t) \<cdot> \<mu> ^^ (Suc j) = ((ctxt_subst C \<mu> n t) \<cdot> \<mu> ^^ j) \<cdot> \<mu>" using subst_right_left by auto
  also have "\<dots> =  ctxt_subst (C \<cdot>\<^sub>c (\<mu> ^^ j)) \<mu> n (t \<cdot> (\<mu> ^^ j)) \<cdot> \<mu> " using Suc by auto
  also have "\<dots> =  ctxt_subst (C \<cdot>\<^sub>c (\<mu> ^^ j) \<cdot>\<^sub>c \<mu>) \<mu> n (t \<cdot> (\<mu> ^^ j) \<cdot> \<mu>)" using ctxt_subst_subst by blast
  finally show ?case using ctxt_compose_subst_compose_distrib subst_subst subst_power_Suc by metis
qed

lemma ctxt_subst_subt_at[simp]: "(ctxt_subst C \<mu> n t) |_ (hole_pos C ^ n) = t \<cdot> \<mu>^^n"
proof (induct n)
  case (Suc n)
  let ?p = "hole_pos C"
  have "(ctxt_subst C \<mu> (Suc n) t) |_ (?p ^ Suc n) = C\<langle>ctxt_subst C \<mu> n t \<cdot> \<mu>\<rangle> |_ (?p @ ?p ^ n)" by simp
  also have "... = (ctxt_subst C \<mu> n t \<cdot> \<mu>) |_ (?p ^ n)" using subt_at_append[OF hole_pos_poss[of C]] by simp
  also have "... = ((ctxt_subst C \<mu> n t) |_ (?p ^ n)) \<cdot> \<mu>" by (rule subt_at_subst[OF ctxt_subst_hole_pos])
  also have "... = (t \<cdot> \<mu>^^n) \<cdot> \<mu>" unfolding Suc by simp
  finally show ?case using subst_left_right by simp
qed simp

lemma ctxt_subst_ctxt_of_pos_term: assumes q: "q \<in> poss s"
  shows "ctxt_subst_ctxt C \<mu> n (ctxt_of_pos_term q s) = ctxt_of_pos_term ((hole_pos C)^n @ q) (ctxt_subst C \<mu> n s)"
proof (induct n)
  case (Suc n)
  have hp: "hole_pos C ^ Suc n = hole_pos C @ hole_pos C ^ n" by auto
  have poss: "hole_pos C ^ n @ q \<in> poss (ctxt_subst C \<mu> n s)"
    unfolding poss_append_poss using q by auto
  show ?case 
    unfolding ctxt_subst_ctxt.simps
    unfolding Suc
    unfolding ctxt_subst.simps
    unfolding hp 
    by (simp add: ctxt_of_pos_term_append[OF hole_pos_poss] ctxt_of_pos_term_subst[OF poss])
qed simp

lemma ctxt_subst_step: fixes C :: "('f,'v)ctxt"
  defines p: "p \<equiv> hole_pos C"
  assumes step: "(s,t) \<in> rstep_r_p_s R lr q \<sigma>"
  shows "(ctxt_subst C \<mu> n s, ctxt_subst C \<mu> n t) \<in> rstep_r_p_s R lr ((p^n) @ q) (\<sigma> \<circ>\<^sub>s \<mu>^^n)"
proof -
  obtain l r where l_r: "lr = (l,r)" by force
  from step[unfolded rstep_r_p_s_def' l_r]
  have q: "q \<in> poss s" and lr: "(l,r) \<in> R" and s: "s |_ q = l \<cdot> \<sigma>" and t: "t = replace_at s q (r \<cdot> \<sigma>)" by auto
  show ?thesis unfolding rstep_r_p_s_def'
  proof(rule, unfold split l_r fst_conv snd_conv, intro conjI)
    show "(l,r) \<in> R" by (rule lr)
  next
    show "p ^ n @ q \<in> poss (ctxt_subst C \<mu> n s)" 
      unfolding poss_append_poss p
      using q by auto
  next
    show "(ctxt_subst C \<mu> n s) |_ (p ^ n @ q) = l \<cdot> \<sigma> \<circ>\<^sub>s \<mu> ^^ n"
      unfolding p
      unfolding subt_at_append[OF ctxt_subst_hole_pos]
      unfolding ctxt_subst_subt_at
      unfolding subt_at_subst[OF q] s
      by simp
  next
    show "ctxt_subst C \<mu> n t = (replace_at (ctxt_subst C \<mu> n s) (p ^ n @ q) (r \<cdot> \<sigma> \<circ>\<^sub>s \<mu> ^^ n))" (is "?l = ?r")
    proof -        
      have "?l = ctxt_subst C \<mu> n (replace_at s q (r \<cdot> \<sigma>))" unfolding t ..
      also have "... = ?r" unfolding ctxt_subst_ctxt p unfolding ctxt_subst_ctxt_of_pos_term[OF q] by simp
      finally show "?l = ?r" .
    qed
  qed
qed



lemma ctxt_subst_pos_cases: assumes "p \<in> poss(ctxt_subst C \<mu> n t)" shows
"(\<exists>p'. p = hole_pos C ^ n @ p' \<and> p' \<in> poss t) \<or>
 (\<exists>x p' p''. p = hole_pos C ^ n @ p' @ p'' \<and> p' \<in> poss t \<and> t|_p' = Var x \<and> 
  p'' \<in> poss (Var x \<cdot> \<mu> ^^ n) \<and> n > 0) \<or>
 (\<exists> k p'. k < n \<and> p = hole_pos C ^ k @ p' \<and> p' \<in> possc C) \<or>
 (\<exists> k x p' p''. k < n \<and> p = hole_pos C ^ k @ p' @ p'' \<and> p' \<in> possc C - {hole_pos C} \<and> 
  C\<langle>t\<rangle>|_p' = Var x \<and> p'' \<in> poss (Var x \<cdot> \<mu> ^^ k))"
proof-
 let ?case1 = "\<lambda> C t n p p'. p = hole_pos C ^ n @ p' \<and> p' \<in> poss t"
 let ?case2 = "\<lambda> C t n p p' p'' x. p = hole_pos C ^ n @ p' @ p'' \<and> p' \<in> poss t \<and> 
  t|_p' = Var x \<and> p'' \<in> poss (Var x \<cdot> \<mu> ^^ n) \<and> n > 0"
 let ?case3 = "\<lambda> C t n k p p'. k < n \<and> p = hole_pos C ^ k @ p' \<and> p' \<in> possc C"
 let ?case4 = "\<lambda> C t n k p p' p'' x.  k < n \<and> p = hole_pos C ^ k @ p' @ p'' \<and> 
  p' \<in> possc C - {hole_pos C} \<and> C\<langle>t\<rangle>|_p' = Var x \<and> p'' \<in> poss (Var x \<cdot> \<mu> ^^ k)"
 let ?th = "\<lambda> C t n p. (\<exists> p'. ?case1 C t n p p') \<or> (\<exists> x p' p''. ?case2 C t n p p' p'' x) \<or> 
  (\<exists> k p'. ?case3 C t n k p p') \<or> (\<exists> k x p' p''. ?case4 C t n k p p' p'' x)"  
 from assms show ?thesis proof(induct n arbitrary:C t p)
 case 0
  then have "p \<in> poss t" by simp
  then show ?case by auto
 next
 case (Suc n)
  then have pposs:"p \<in> poss (C\<langle>ctxt_subst C \<mu> n t \<cdot> \<mu>\<rangle>)" and 
   IH:"\<And>q' C t. q' \<in> poss (ctxt_subst C \<mu> n t) \<Longrightarrow> ?th C t n q'" by auto
  let ?q = "hole_pos C"
  show ?case
  proof (cases "?q \<le>\<^sub>p p")
   case False note Case3=this
     with pos_cases have "p <\<^sub>p ?q \<or> ?q \<bottom> p" by blast
     from this[unfolded less_pos_def ] par_hole_pos_in_possc[OF _ pposs] less_eq_hole_pos_in_possc 
      have "p \<in> possc C" by blast
     then have "?case3 C t (Suc n) 0 p p" by auto
     then show ?thesis by blast
   next
   case True 
    then obtain q where p:"p = ?q @ q" unfolding less_eq_pos_def by auto
    show ?thesis proof(cases "q \<in> poss (ctxt_subst C \<mu> n t)")
     case True 
      with p IH have ih:"?th C t n q" (is "?A \<or> ?B \<or> ?C \<or> ?D") by auto
       show ?thesis proof(cases "\<not> ?A", cases "\<not> ?B", cases "\<not> ?C")
         (* case (iv) *)
         assume "\<not> ?A" and "\<not> ?B" and "\<not> ?C"
         with ih have "?D" by fast
         then obtain k x p' p'' where a:"k < n" and b:"q = ?q ^ k @ p' @ p''" and 
           c:"p' \<in> possc C - {hole_pos C} \<and> C\<langle>t\<rangle> |_ p' = Var x" and d:"p'' \<in> poss (Var x \<cdot> \<mu> ^^ k)" by auto
         then have a:"Suc k < Suc n" and b:"p = ?q ^(Suc k) @ p' @ p''" unfolding p by auto
         from poss_imp_subst_poss[OF d, of \<mu>] 
           subst_subst[of "Var x" "\<mu> ^^ k" \<mu>, unfolded subst_power_Suc[symmetric]] 
           have d':"p'' \<in> poss (Var x \<cdot> \<mu> ^^ (Suc k))" by fastforce
         with a b c have "?case4 C t (Suc n) (Suc k) p p' p'' x" by fast
         then show ?thesis by metis
        next
         (* case (iii) *)
         assume "\<not> \<not>(\<exists> k p'. ?case3 C t n k q p')" 
         then obtain k p' where "k < n \<and> q = ?q ^ k @ p' \<and> p' \<in> possc C" by auto
         then have "Suc k < Suc n \<and> p = ?q ^ Suc k @ p' \<and> p' \<in> possc C" using p by auto
         then show ?thesis by blast
        next
         (* case (ii) *)
         assume "\<not> \<not>(\<exists> x p' p''. ?case2 C t n q p' p'' x)"
         then obtain x p' p'' where "q = ?q ^ n @ p' @ p''" and 
           a:"p' \<in> poss t \<and> t |_ p' = Var x" and b:"p'' \<in> poss (Var x \<cdot> \<mu> ^^ n)" by auto
         then have c:"p = hole_pos C ^ Suc n @ p' @ p''" unfolding p by auto
         from  subst_subst[of "Var x" "\<mu> ^^ n" \<mu>, unfolded subst_power_Suc[symmetric]] 
            poss_imp_subst_poss[OF b, of \<mu>] have "p'' \<in> poss (Var x \<cdot> \<mu> ^^ Suc n)" by auto
         with a c show ?thesis by blast
        next
         (* case (i) *)
         assume "\<not> \<not>(\<exists> p'. ?case1 C t n q p')"
         with p show ?thesis by auto
       qed
     next
      assume qn:"q \<notin> poss (ctxt_subst C \<mu> n t)"
      from pposs p have qposs:"q \<in> poss (ctxt_subst C \<mu> n t \<cdot> \<mu>)" using hole_pos_poss_conv by fast
      have s:"hole_pos (C \<cdot>\<^sub>c \<mu>) = ?q" by simp
      from qposs have "q \<in> poss (ctxt_subst (C \<cdot>\<^sub>c \<mu>) \<mu> n (t \<cdot> \<mu>))" unfolding ctxt_subst_subst by simp
      with IH[OF this] have ih:"?th (C \<cdot>\<^sub>c \<mu>) (t \<cdot> \<mu>) n q" (is "?A \<or> ?B \<or> ?C \<or> ?D") by auto
      show ?thesis proof(cases "\<not> ?A", cases "\<not> ?B", cases "\<not> ?C")
      (* case (iv) *)
      assume  "\<not> ?A" and "\<not> ?B" and "\<not> ?C"
        with ih have "?D" by fast
        then obtain k x p' p'' where kn:"k < n" and q:"q = ?q ^ k @ p' @ p''" and 
          pposs0:"p' \<in> possc (C \<cdot>\<^sub>c \<mu>) - {hole_pos C}" and x:"C\<langle>t\<rangle> \<cdot> \<mu> |_ p' = Var x" and 
          pposs'':"p'' \<in> poss (Var x \<cdot> \<mu> ^^ k)" unfolding s by auto
        from pposs0[unfolded possc_def] have pposs':"p' \<in> poss (C\<langle>t\<rangle> \<cdot> \<mu>)" 
         using subst_apply_term_ctxt_apply_distrib[of C t \<mu>] by simp
        have "\<not> (is_Fun (C\<langle>t\<rangle> \<cdot> \<mu> |_ p'))" using x by auto
        then have yeah:"\<not> (p' \<in> poss C\<langle>t\<rangle> \<and> is_Fun (C\<langle>t\<rangle> |_ p'))"
          by (metis is_VarE is_VarI subst_apply_eq_Var subt_at_subst)
        with pos_into_subst[OF _ pposs', of "C\<langle>t\<rangle>"] obtain q' q'' y where 
          p':"p' = q' @ q''" and 2:"q' \<in> poss C\<langle>t\<rangle>" and 3:"C\<langle>t\<rangle> |_ q' = Var y" by blast
        have q':"q' \<in> possc (C \<cdot>\<^sub>c \<mu>)" unfolding possc_def proof(rule,simp, rule allI) 
         fix t
         from DiffD1[OF pposs0[unfolded p']] 
         show "q' \<in> poss (C \<cdot>\<^sub>c \<mu>)\<langle>t\<rangle>" using poss_append_poss poss_imp_possc by metis
        qed
        from possc_subst_not_possc_not_poss[OF q'] 2 have 22:"q' \<in> possc C" by fast
        from pposs0 have "p' \<noteq> hole_pos C" by fast
        with p' possc_not_below_hole_pos[OF DiffD1[OF pposs0], unfolded hole_pos_subst] have "q' \<noteq> hole_pos C" 
         using less_pos_def by fastforce
        with q' 22 have 22:"q' \<in> possc C - {hole_pos C}" by auto
        from p[unfolded q p'] have 1:"p = ?q ^ (Suc k) @ q' @ q'' @ p''" by auto
        from subt_at_subst[OF 2] x[unfolded p' subt_at_append[OF poss_imp_subst_poss[OF 2]]] 3
          have "Var y \<cdot> \<mu> |_ q'' = Var x" by metis
        then have 42:"Var y \<cdot> \<mu> |_ q'' \<cdot> \<mu> ^^ k = Var x \<cdot> \<mu> ^^ k" by auto
        from poss_append_poss[of q' q'' "C\<langle>t\<rangle> \<cdot> \<mu>"] pposs'[unfolded p'] 3 have 
          41:"q'' \<in> poss (Var y \<cdot> \<mu>)" by (metis "2" subt_at_subst)
        then have "q'' \<in> poss (Var y \<cdot> \<mu> \<cdot> \<mu> ^^ k)" by (metis poss_imp_subst_poss)
        then have 40:"q'' \<in> poss (Var y \<cdot> \<mu> ^^ Suc k)"
          by (simp add: subst_compose)
        have "Var y \<cdot> \<mu> ^^ Suc k |_ q'' = Var y \<cdot> \<mu> |_ q'' \<cdot> \<mu> ^^ k" using subt_at_subst[OF 41] by (auto simp add: subst_compose)
        with pposs''[unfolded 42[symmetric]] have "p'' \<in> poss (Var y \<cdot> \<mu> ^^ Suc k |_ q'')" by auto
        with 40 poss_append_poss[of q'' p'' "Var y \<cdot> \<mu> ^^ (Suc k)"] 
        have 4:"(q'' @ p'') \<in> poss (Var y \<cdot> \<mu> ^^ (Suc k))" by fast
        from kn 1 22 3 4 have  "?case4 C t (Suc n) (Suc k) p q' (q''@ p'') y" by (metis Suc_less_eq)
        then show ?thesis by metis
      next
      (* case (iii) *)
      assume "\<not> \<not>(\<exists> k p'. ?case3 (C \<cdot>\<^sub>c \<mu>) (t \<cdot> \<mu>) n k q p')" 
      with s obtain k p' where ih:"k < n \<and> q = ?q ^ k @ p'" and ppossc':"p' \<in> possc (C \<cdot>\<^sub>c \<mu>)" by auto
      then have kn:"Suc k < Suc n" and p:"p = ?q ^ Suc k @ p'" using p by auto
      show ?thesis proof(cases "p' \<in> possc C")
        case True
          with kn p show ?thesis by blast
        next
        case False
         have np:"p' \<notin> poss C\<langle>t\<rangle>" using possc_subst_not_possc_not_poss[OF ppossc' False] by auto
         from False have 33:"p' \<noteq> hole_pos C" using hole_pos_in_possc by auto
         from ppossc'[unfolded possc_def] subst_apply_term_ctxt_apply_distrib[of C t \<mu>] 
          have pposs':"p' \<in> poss (C\<langle>t\<rangle> \<cdot> \<mu>)" by fastforce
         from pos_into_subst[OF _ this, of "C\<langle>t\<rangle>"] np 
         have "\<exists>q q' x. p' = q @ q' \<and> q \<in> poss C\<langle>t\<rangle> \<and> C\<langle>t\<rangle> |_ q = Var x" by fast
         then obtain q' q'' x where p':"p' = q' @ q''" and 3:"q' \<in> poss C\<langle>t\<rangle>" and 
           4:"C\<langle>t\<rangle> |_ q' = Var x" by blast
         from 33 hole_pos_poss_conv possc_subst_not_possc_not_poss[OF ppossc', unfolded p'] 
          have 33:"q' \<noteq> hole_pos C" by (metis False p' poss_append_poss pposs')
         have a3:"q' \<in> possc C - {hole_pos C}" 
          proof-
           from possc_not_below_hole_pos[OF ppossc', unfolded hole_pos_subst] have nlt:"\<not> hole_pos C <\<^sub>p p'" by auto
           with pos_cases 33 less_pos_def have "p' <\<^sub>p hole_pos C \<or> p' \<bottom> hole_pos C" 
             by (metis False hole_pos_in_possc)
           with p' pos_cases[of "q'" "hole_pos C"] have "q' \<le>\<^sub>p hole_pos C \<or> q' \<bottom> hole_pos C"
             apply auto
             using less_pos_simps(5) order_pos.less_trans apply blast
             by (metis append_Nil2 less_pos_simps(1) nlt order_pos.dual_order.strict_implies_order order_pos.dual_order.strict_trans2)
           then show ?thesis using less_eq_hole_pos_in_possc[of q' C] par_hole_pos_in_possc[OF _ 3] parallel_pos_sym 33 by fast
          qed 
          from poss_append_poss[of q' q'' "C\<langle>t\<rangle> \<cdot> \<mu>"] pposs'[unfolded p'] have 
           "q'' \<in> poss (C\<langle>t\<rangle> \<cdot> \<mu> |_ q')" by auto
         with subt_at_subst[OF 3] 4 have 5:"q'' \<in> poss (Var x \<cdot> \<mu>)" by metis
         then have 5:"q'' \<in> poss (Var x \<cdot> \<mu> ^^ Suc k)" using poss_imp_subst_poss by (auto simp add: subst_compose)
         from kn p[unfolded p'] a3 4 5 have "?case4 C t (Suc n) (Suc k) p q' q'' x" by blast
         then show ?thesis by blast
        qed
        next
       (* case (ii) *)
          assume "\<not> \<not>(\<exists> x p' p''. ?case2 (C \<cdot>\<^sub>c \<mu>) (t \<cdot> \<mu>) n q p' p'' x)"
          then obtain x p' p'' where q:"q = ?q ^ n @ p' @ p''" and 
           a:"p' \<in> poss (t \<cdot> \<mu>)" and x:"(t \<cdot> \<mu>) |_ p' = Var x" and 
           c:"p'' \<in> poss (Var x \<cdot> \<mu> ^^ n)" by auto
          have "\<not> (is_Fun (t \<cdot> \<mu> |_ p'))" using x by auto
          then have yeah:"\<not> (p' \<in> poss t \<and> is_Fun (t |_ p'))"
             by (metis is_VarE is_VarI subst_apply_eq_Var subt_at_subst)
          with pos_into_subst[OF _ a] have 
             "\<exists>q' q'' y. p' = q' @ q'' \<and> q' \<in> poss t \<and> t |_ q' = Var y" by auto
          then obtain q' q'' y where p':"p' = q' @ q''" and 2:"q' \<in> poss t"
             and 3:"t |_ q' = Var y" by auto
          from p[unfolded q p'] have 1:"p = ?q ^ (Suc n) @ q' @ q'' @ p''" by auto
          from x[unfolded p' subt_at_append[OF poss_imp_subst_poss[OF 2]]  subt_at_subst[OF 2]]
             have "t |_ q' \<cdot> \<mu> |_ q'' = Var x" by fast
          with 3 have 42:"Var y \<cdot> \<mu> |_ q'' \<cdot> \<mu> ^^ n = Var x \<cdot> \<mu> ^^ n" by auto
          from poss_append_poss[of q' q'' "t \<cdot> \<mu>", unfolded subt_at_subst[OF 2] 3] a[unfolded p']
            poss_imp_subst_poss[OF 2] have 41:"q'' \<in> poss (Var y \<cdot> \<mu>)" by auto
          then have "q'' \<in> poss (Var y \<cdot> \<mu> \<cdot> \<mu> ^^ n)" by (metis poss_imp_subst_poss)
          then have 40:"q'' \<in> poss (Var y \<cdot> \<mu> ^^ Suc n)" by (auto simp add: subst_compose)
          have "Var y \<cdot> \<mu> ^^ Suc n |_ q'' = Var y \<cdot> \<mu> |_ q'' \<cdot> \<mu> ^^ n" using subt_at_subst[OF 41] by (auto simp add: subst_compose)
          with c[unfolded 42[symmetric]] have "p'' \<in> poss (Var y \<cdot> \<mu> ^^ Suc n |_ q'')" by auto
          with 40 poss_append_poss[of q'' p'' "Var y \<cdot> \<mu> ^^ (Suc n)"] 
            have 4:"(q'' @ p'') \<in> poss (Var y \<cdot> \<mu> ^^ (Suc n))" by fast
          from 1 2 3 4 have  "?case2 C t (Suc n) p q' (q''@ p'') y" by auto
          then show ?thesis by metis
          next
           assume "\<not> \<not>(\<exists> p'. ?case1 (C \<cdot>\<^sub>c \<mu>) (t \<cdot> \<mu>) n q p')"
           then obtain p' where q:"q = ?q ^ n @ p'" and pposs':"p' \<in> poss (t \<cdot> \<mu>)" by auto
           show ?thesis proof(cases "p' \<in> poss t")
            case True
             with p[unfolded q] have "?case1 C t (Suc n) p p'" by auto
             then show ?thesis by blast
            next
            case False
             from pos_into_subst[OF _ pposs', of t] False have
               "\<exists>q q' x. p' = q @ q' \<and> q \<in> poss t \<and> t |_ q = Var x" by auto
             then obtain q q' x where p':"p' = q @ q'" and 2:"q \<in> poss t"
               and 3:"t |_ q = Var x" by auto
             from p[unfolded q p'] have 1:"p = ?q ^ Suc n @ q @ q'" by auto
             from poss_append_poss[of q q'] pposs'[unfolded p'] poss_imp_subst_poss[OF 2]
              have "q' \<in> poss (t \<cdot> \<mu> |_ q)" by auto
             with subt_at_subst[OF 2] 3 have "q' \<in> poss (Var x \<cdot> \<mu>)" by metis
             with poss_imp_subst_poss[OF this] have 4:"q' \<in> poss (Var x \<cdot> \<mu> ^^ Suc n)" by (force simp add: subst_compose)
             from 1 2 3 4 have  "?case2 C t (Suc n) p q q' x" by auto
             then show ?thesis by blast
            qed
          qed
     qed
   qed
 qed
qed

end
