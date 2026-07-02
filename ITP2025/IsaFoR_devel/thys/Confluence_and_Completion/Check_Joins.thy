(* Author: C. Kohl, J. Nagele, R. Thiemann, D. Kim *)

section \<open>Checking Various Joins\<close>
(* checking various kinds of joins, collected from various theories, might be extended and unified! *)
theory Check_Joins
  imports 
    First_Order_Rewriting.Rewrite_Relations_Impl
begin 

fun is_par_rsteps_join where
  "is_par_rsteps_join R S (Some n) s t =
    (\<not> Option.is_none (List.find (\<lambda>v. (s,v) \<in> par_rstep (set R)) (reachable_terms S t n)))"
| "is_par_rsteps_join R S None s t =
    (\<not> Option.is_none (List.find (\<lambda>v. (s,v) \<in> par_rstep (set R)) (parallel_rewrite S t)))"

lemma is_par_rsteps_join[dest]: assumes "is_par_rsteps_join R S hint s t" 
  shows "\<exists>v. (s, v) \<in> par_rstep (set R) \<and> (t, v) \<in> (rstep (set S))\<^sup>*" 
proof (cases hint)
  case (Some n)
  let ?find = "\<lambda> v. (s,v) \<in> par_rstep (set R)" 
  from Some assms have "\<not> Option.is_none (List.find ?find (reachable_terms S t n))"  
    by auto
  then obtain v where "List.find ?find (reachable_terms S t n) = Some v"
    by force
  then have "(s,v) \<in> par_rstep (set R)" and "v \<in> set (reachable_terms S t n)"
    unfolding find_Some_iff by auto
  then show ?thesis
    using reachable_terms by blast
next
  case None
  let ?find = "\<lambda> v. (s,v) \<in> par_rstep (set R)" 
  from None assms have "\<not> Option.is_none (List.find ?find (parallel_rewrite S t))"
    by auto
  then obtain v where  "List.find ?find (parallel_rewrite S t) = Some v"
    by force
  then have "(s,v) \<in> par_rstep (set R)" and "v \<in> set (parallel_rewrite S t)"
    unfolding find_Some_iff by auto
  then show ?thesis using parallel_rewrite_par_step par_rstep_rsteps by blast
qed

declare is_par_rsteps_join.simps[simp del]



subsection \<open>Checking the conditions just by some number of steps; 
  Advantage: easy certificates; 
  disadvantage: this won't work for TRSs with extra variables.\<close>

definition is_rsteps_reachable where
  "is_rsteps_reachable R n s t =
   (t \<in> set (reachable_terms R s n))"

lemma is_rsteps_reachable[dest]: "is_rsteps_reachable R h s t \<Longrightarrow> (s,t) \<in> (rstep (set R))^*" 
  by (auto simp: is_rsteps_reachable_def dest: reachable_terms)

definition "is_rsteps_join R S n s t = (let SS = reachable_terms S t n in 
   (\<exists> u \<in> set (reachable_terms R s n). u \<in> set SS))"

lemma is_rsteps_join[dest]: "is_rsteps_join R S n s t \<Longrightarrow> \<exists> u. (s,u) \<in> (rstep (set R))^* \<and> (t,u) \<in> (rstep (set S))^*" 
  by (auto simp: is_rsteps_join_def dest: reachable_terms)

(* this is clearly just a sufficient criterion *)
definition "is_rsteps_conversion R S = is_rsteps_join R S"

lemma is_rsteps_conversion_conv'': assumes "is_rsteps_conversion R S n s t"
  shows "(s,t) \<in> (rstep (set R) \<union> (rstep (set S))^-1)^*" 
proof -
  from assms[unfolded is_rsteps_conversion_def] obtain u
    where "(s,u) \<in> (rstep (set R))^*" "(t,u) \<in> (rstep (set S))^*" by auto
  hence "(s, t) \<in> (rstep (set R))^* O ((rstep (set S))^*)^-1" by auto
  thus ?thesis unfolding converse_inward by regexp
qed

lemma is_rsteps_conversion[dest]: assumes "is_rsteps_conversion R R n s t"
  shows "(s,t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" 
  using is_rsteps_conversion_conv''[OF assms] unfolding conversion_def .


fun is_mstep_join where
  "is_mstep_join R S (Some n) s t = 
  (\<not> Option.is_none (List.find (\<lambda>v. (s,v) \<in> mstep (set R)) (reachable_terms S t n)))"
| "is_mstep_join R S None s t =
  (\<not> Option.is_none (List.find (\<lambda>v. (s,v) \<in> mstep (set R)) (mstep_rewrite S t)))"


lemma is_mstep_join[dest]: assumes "is_mstep_join R S hint s t" 
  shows "\<exists>v. (s,v) \<in> mstep (set R) \<and> (t, v) \<in> (rstep (set S))\<^sup>*" 
proof (cases hint)
  case (Some n)
  let ?find = "\<lambda> v. (s, v) \<in> mstep (set R)" 
  from Some assms have "\<not> Option.is_none (List.find ?find (reachable_terms S t n))"
    by auto  
  then obtain v where "List.find ?find (reachable_terms S t n) = Some v"
    by force
  then have "(s, v) \<in> mstep (set R)" and "v \<in> set (reachable_terms S t n)"
    unfolding find_Some_iff by auto
  then show ?thesis
    using reachable_terms by force
next
  case None
  let ?find = "\<lambda> v. (s, v) \<in> mstep (set R)" 
  from None assms have "\<not> Option.is_none (List.find ?find (mstep_rewrite S t))"
    by force
  then obtain v where  "List.find ?find (mstep_rewrite S t) = Some v"
    by force
  then have "(s,v) \<in> mstep (set R)" and "v \<in> set (mstep_rewrite S t)"
    unfolding find_Some_iff by auto
  from mstep_rewrite_mstep[OF this(2)] this(1)
  show ?thesis using mstep_rsteps_subset 
    by auto
qed

declare is_mstep_join.simps[simp del]



subsection \<open>Checking joining sequences where the intermediate terms are provided.
  Advantage: also works for TRSs with extra-variables;
  Disadvantage: more tedious certificates; requires alignment between variable names\<close>

fun check_steps :: "(('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<times> ('f,'v)term list" where
  "check_steps f s [] u = (if f s u then (u,[]) else (s,[]))" 
| "check_steps f s (t # ts) u = (if s = t \<or> f s t then check_steps f t ts u else (s, t # ts))" 

lemma check_steps: assumes "\<And> s t. f s t \<Longrightarrow> (s,t) \<in> R" 
  and "check_steps f s ts u = (t, ts')" 
shows "(s,t) \<in> R^*" 
  using assms(2)
  by (induct ts arbitrary: s t ts')
    (force split: if_splits dest!: assms(1))+

fun check_optional_step :: "(('f,'v)term \<Rightarrow> ('f,'v)term \<Rightarrow> bool) \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term \<times> ('f,'v)term list" where
  "check_optional_step f s [] u = (if f s u then (u,[]) else (s,[]))" 
| "check_optional_step f s (t # ts) u = (if s = t then check_optional_step f s ts u 
         else if f s t then (t,ts) else (s,(t # ts)))" 

lemma check_optional_step: assumes "\<And> s t. f s t \<Longrightarrow> (s,t) \<in> R" 
  and "check_optional_step f s ts u = (t, ts')" 
shows "(s,t) \<in> R^=" 
  using assms(2)
  by (induct ts arbitrary: s t ts')
    (force split: if_splits dest!: assms(1))+

definition finalize_steps :: "'a :: showl \<Rightarrow> 'a list \<Rightarrow> 'a \<Rightarrow> showsl check" where
  "finalize_steps x xs y = check (x = y) (let z = case xs of [] \<Rightarrow> y | z # zs \<Rightarrow> z in showsl_lit (STR ''got stuck at step from '') o showsl x 
       o showsl_lit (STR '' to '') o showsl z o showsl_nl)" 

lemma finalize_steps[simp]: "isOK (finalize_steps x xs y) = (x = y)"  
  unfolding finalize_steps_def by auto

(* we check a condition to join ordinary critical pairs: s -||-R -> v <-S-* t *)
(* the terms must be the intermediate terms leading from s to t *)
definition check_par_rsteps_join_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> String.literal \<Rightarrow> ('f,'v)rules \<Rightarrow> String.literal \<Rightarrow>
   ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_par_rsteps_join_sequence R R' S S' s t terms = 
     (case check_optional_step (\<lambda> s t. (s,t) \<in> par_rstep (set R)) s terms t
       of (v, vs) \<Rightarrow> case check_steps (\<lambda> s t. (t, s) \<in> rstep (set S)) v vs t
       of (w, ws) \<Rightarrow> finalize_steps w ws t
         <+? (\<lambda> e. 
      showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit (STR '' -||,'' + R' + STR ''-> . *<-'' + S' + STR ''- '') o showsl t o
      showsl_nl o e))" 

lemma check_par_rsteps_join_sequence:
  assumes "isOK(check_par_rsteps_join_sequence R R' S S' s t terms)"
  shows "\<exists> v. (s, v) \<in> par_rstep (set R) \<and> (t, v) \<in> (rstep (set S))^*" 
proof -
  let ?check_par = "check_optional_step (\<lambda> s t. (s,t) \<in> par_rstep (set R)) s terms t" 
  obtain v vs where ch: "?check_par = (v,vs)" by (cases ?check_par, auto)
  let ?check_steps = "check_steps (\<lambda>s t. (t, s) \<in> rstep (set S)) v vs t" 
  obtain w ws where ch2: "?check_steps = (w,ws)" by (cases ?check_steps, auto) 
  from assms[unfolded check_par_rsteps_join_sequence_def ch split ch2, simplified] have wt: "w = t" .
  show ?thesis
  proof (intro exI[of _ v] conjI)
    have "(v,t) \<in> ((rstep (set S))^-1)^*" using check_steps[OF _ ch2] unfolding wt by auto
    thus "(t, v) \<in> (rstep (set S))\<^sup>*" by (rule rtrancl_converseD)
    from check_optional_step[OF _ ch] have "(s,v) \<in> (par_rstep (set R))^=" by auto
    thus "(s, v) \<in> par_rstep (set R)" by blast
  qed
qed


definition check_generic_decreasing_sequence :: 
  "(('f :: showl,'v :: showl)rule \<Rightarrow> bool) \<Rightarrow> 
   (('f,'v)rule \<Rightarrow> bool) \<Rightarrow> (('f,'v)rule \<Rightarrow> bool) \<Rightarrow> (('f,'v)rule \<Rightarrow> bool) \<Rightarrow> (('f,'v)rule \<Rightarrow> bool) \<Rightarrow> (('f,'v)rule \<Rightarrow> bool) \<Rightarrow> 
   String.literal \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_generic_decreasing_sequence RSk Sm RSkm RSkm' Rk RSm rel_descr s t terms = 
     (case check_steps (\<lambda> s t. RSk (s,t)) s terms t
       of (v, vs) \<Rightarrow> case check_optional_step (\<lambda> s t. Sm (s,t)) v vs t  
       of (w, ws) \<Rightarrow> case check_steps (\<lambda> s t. RSkm (s,t)) w ws t
       of (w', ws') \<Rightarrow> case check_steps (\<lambda> s t. RSkm' (s,t)) w' ws' t
       of (u, us) \<Rightarrow> case check_optional_step (\<lambda> s t. Rk (s,t)) u us t
       of (z, zs) \<Rightarrow> case check_steps (\<lambda> s t. RSm (s,t)) z zs t
       of (y, ys) \<Rightarrow> finalize_steps y ys t
         <+? (\<lambda> e. 
        showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit rel_descr o showsl t o
        showsl_nl o e))" 

lemma check_generic_decreasing_sequence: assumes "isOK(check_generic_decreasing_sequence RSk Sm RSkm RSkm' Rk RSm descr s t terms)" 
  shows "(s,t) \<in> (Collect RSk)^* O (Collect Sm)^= O (Collect RSkm)^* O (Collect RSkm')^* O
         (Collect Rk)^= O (Collect RSm)^*" 
proof -
  let ?c1 = "check_steps (\<lambda>s t. RSk (s,t)) s terms t" 
  obtain v vs where c1: "?c1 = (v,vs)" by force
  let ?c2 = "check_optional_step (\<lambda>s t. Sm (s, t)) v vs t" 
  obtain w ws where c2: "?c2 = (w,ws)" by force
  let ?c3 = "check_steps (\<lambda>s t. RSkm (s, t)) w ws t" 
  obtain u us where c3: "?c3 = (u,us)" by force
  let ?c3' = "check_steps (\<lambda>s t. RSkm' (s, t)) u us t" 
  obtain u' us' where c3': "?c3' = (u',us')" by force
  let ?c4 = "check_optional_step (\<lambda>s t. Rk (s,t)) u' us' t" 
  obtain z zs where c4: "?c4 = (z, zs)" by force
  let ?c5 = "check_steps (\<lambda>s t. RSm (s, t)) z zs t" 
  obtain y ys where c5: "?c5 = (y, ys)" by force
  from assms[unfolded check_generic_decreasing_sequence_def c1 c2 c3 c3' c4 c5 split] 
  have yt: "y = t" by auto
  from check_optional_step[OF _ c2] have vw: "(v,w) \<in> (Collect Sm)^=" by force
  from check_optional_step[OF _ c4] have uz: "(u', z) \<in> (Collect Rk)^=" by force
  show ?thesis unfolding yt[symmetric] par_rsteps_rsteps[symmetric]
    apply (intro relcompI)
         apply (rule check_steps[OF _ c1], force)
        apply (rule vw)
       apply (rule check_steps[OF _ c3], force)
      apply (rule check_steps[OF _ c3'], force)
     apply (rule uz)
    apply (rule check_steps[OF _ c5], force)
    done
qed

(* root labeling with parallel critical pairs *)
definition check_rl_par_decreasing_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> 
   ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
   'v set \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_rl_par_decreasing_sequence RSk Sm RSkm Rk RSm V = 
      check_generic_decreasing_sequence 
          (\<lambda> (s,t). (s,t) \<in> par_rstep (set RSk))
          (\<lambda> (s,t). (s,t) \<in> par_rstep (set Sm)) 
          (\<lambda> (s,t). (s,t) \<in> par_rstep (set RSkm))
          (\<lambda> _. False)  
          (\<lambda> (s,t). (t,s) \<in> par_rstep_var_restr (set Rk) V)
          (\<lambda> (s,t). (s,t) \<in> par_rstep (set RSm))
          (STR '' <->* . -||-> . <->* . <-||- . <->* '')" 

lemma check_rl_par_decreasing_sequence: assumes "isOK(check_rl_par_decreasing_sequence RSk Sm RSkm Rk RSm V s t terms)" 
  shows "(s,t) \<in> (rstep (set RSk))^* O par_rstep (set Sm) O (rstep (set RSkm))^* O
         (par_rstep_var_restr (set Rk) V)^-1 O (rstep (set RSm))^*" 
  using check_generic_decreasing_sequence[OF assms[unfolded check_rl_par_decreasing_sequence_def]]
  by (auto simp: par_rsteps_rsteps) force+

(* root labeling with ordinary critical pairs, join-version *)
definition check_rl_decreasing_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> 
   ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules \<Rightarrow> 
   ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_rl_decreasing_sequence Rlk Rm Rkm Rk Rlm = 
      check_generic_decreasing_sequence 
          (\<lambda> (s,t). (s,t) \<in> rstep (set Rlk))
          (\<lambda> (s,t). (s,t) \<in> rstep (set Rm)) 
          (\<lambda> (s,t). (s,t) \<in> rstep (set Rkm))
          (\<lambda> (s,t). (t,s) \<in> rstep (set Rkm)) 
          (\<lambda> (s,t). (t,s) \<in> rstep (set Rk))
          (\<lambda> (s,t). (t,s) \<in> rstep (set Rlm))
          (STR '' ->* . -> . ->* . *<- . <- . *<- '')" 

lemma swap_inverse: "{(s, t). (t, s) \<in> R} = R^-1" by auto
lemma prod_swap_image[simp]: "prod.swap ` R = R^-1" by auto

lemma check_rl_decreasing_sequence: assumes "isOK(check_rl_decreasing_sequence Rlk Rm Rkm Rk Rlm s t terms)" 
  shows "(s,t) \<in> (rstep (set Rlk))^* O (rstep (set Rm))^= O (rstep (set Rkm))^* O
          ((rstep (set Rkm))^*)^-1 O ((rstep (set Rk))^=)^-1 O ((rstep (set Rlm))^*)^-1" 
proof -
  note [simp] = rtrancl_converse
  show ?thesis
    using check_generic_decreasing_sequence[OF assms[unfolded check_rl_decreasing_sequence_def]]
    by (auto simp: swap_inverse) blast+
qed



definition check_conversion_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> 
   ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_conversion_sequence R s t terms = (let C = R @ map prod.swap R in
     (case check_steps (\<lambda> s t. (s,t) \<in> par_rstep (set C)) s terms t
       of (y, ys) \<Rightarrow> finalize_steps y ys t
         <+? (\<lambda> e. 
        showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit (STR '' <->* '') o showsl t o
        showsl_nl o e)))" 

lemma check_conversion_sequence: assumes "isOK(check_conversion_sequence R s t terms)" 
  shows "(s,t) \<in> (rstep (set R))\<^sup>\<leftrightarrow>\<^sup>*" 
proof -
  let ?C = "R @ map prod.swap R" 
  let ?c1 = "check_steps (\<lambda>s t. (s, t) \<in> par_rstep (set ?C)) s terms t" 
  obtain y ys where c1: "?c1 = (y,ys)" by force
  have conv: "(rstep (set R))\<^sup>\<leftrightarrow>\<^sup>* = (rstep (set ?C))^*" 
    unfolding conversion_def set_append rstep_union set_map
    by (rule arg_cong[of _ _ rtrancl], fastforce) 
  from assms[unfolded check_conversion_sequence_def c1 Let_def split] 
  have yt: "y = t" by auto
  show ?thesis unfolding yt[symmetric] par_rsteps_rsteps[symmetric] conv
    by (rule check_steps[OF _ c1])
qed

definition check_join_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> ('f,'v)rules \<Rightarrow>
   ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_join_sequence R S s t terms = (
     (case check_steps (\<lambda> s t. (s,t) \<in> par_rstep (set R)) s terms t
       of (x, xs) \<Rightarrow> case check_steps (\<lambda> s t. (t,s) \<in> par_rstep (set S)) x xs t
       of (y, ys) \<Rightarrow> finalize_steps y ys t
         <+? (\<lambda> e. 
        showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit (STR '' ->* . *<- '') o showsl t o
        showsl_nl o e)))" 

lemma check_join_sequence: assumes "isOK(check_join_sequence R S s t terms)" 
  shows "\<exists> v. (s,v) \<in> (rstep (set R))^* \<and> (t,v) \<in> (rstep (set S))^*" 
proof -
  let ?c1 = "check_steps (\<lambda>s t. (s, t) \<in> par_rstep (set R)) s terms t" 
  obtain y ys where c1: "?c1 = (y,ys)" by force
  let ?c2 = "check_steps (\<lambda>s t. (t, s) \<in> par_rstep (set S)) y ys t" 
  obtain z zs where c2: "?c2 = (z,zs)" by force
  from assms[unfolded check_join_sequence_def c1 c2 Let_def split] 
  have zt: "z = t" by auto
  show ?thesis unfolding zt[symmetric] par_rsteps_rsteps[symmetric] 
    apply (intro exI[of _ y])
    using check_steps[OF _ c1, of "par_rstep (set R)"] check_steps[OF _ c2, of "(par_rstep (set S))^-1"] 
    by (auto dest: rtrancl_converseD)
qed

definition check_rewrite_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> 
   ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_rewrite_sequence R s t terms = (
     (case check_steps (\<lambda> s t. (s,t) \<in> par_rstep (set R)) s terms t
       of (y, ys) \<Rightarrow> finalize_steps y ys t
         <+? (\<lambda> e. 
        showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit (STR '' ->* '') o showsl t o
        showsl_nl o e)))" 

lemma check_rewrite_sequence: assumes "isOK(check_rewrite_sequence R s t terms)" 
  shows "(s,t) \<in> (rstep (set R))^*" 
proof -
  let ?c1 = "check_steps (\<lambda>s t. (s, t) \<in> par_rstep (set R)) s terms t" 
  obtain y ys where c1: "?c1 = (y,ys)" by force
  from assms[unfolded check_rewrite_sequence_def c1 Let_def split] 
  have yt: "y = t" by auto
  show ?thesis unfolding yt[symmetric] par_rsteps_rsteps[symmetric] 
    using check_steps[OF _ c1, of "par_rstep (set R)"] by auto 
qed



definition is_toyama_par_rstep_join  where
  "is_toyama_par_rstep_join n R S C s peak t = (\<exists> v \<in> set (reachable_terms S s n).
      (t,v) \<in> par_rstep_var_restr (set R) (vars_mctxt C))"

lemma is_toyama_par_rsteps_join[dest]: assumes "is_toyama_par_rstep_join n R S C s peak t"
  shows "\<exists> v. (s,v) \<in> (rstep (set S))^* 
      \<and> (t, v) \<in> par_rstep_var_restr (set R) (vars_mctxt C)" 
proof -
  let ?V = "vars_mctxt C" 
  from assms have 
    " (\<exists> v \<in> set (reachable_terms S s n).
      (t,v) \<in> par_rstep_var_restr (set R) ?V)"
    unfolding is_toyama_par_rstep_join_def by fastforce
  then obtain v where rv:"v \<in> set (reachable_terms S s n)" and
      "(t,v) \<in> par_rstep_var_restr (set R) ?V"
    by force
  then have "(t,v) \<in> par_rstep_var_restr (set R) ?V" and "v \<in> set (reachable_terms S s n)"
    unfolding find_Some_iff apply simp  using rv by blast
  then show ?thesis by (meson reachable_terms)
qed


definition check_toyama_pcp_join_sequence :: 
  "('f :: showl,'v :: showl)rules \<Rightarrow> String.literal \<Rightarrow> ('f,'v)rules \<Rightarrow> String.literal \<Rightarrow>
   'v set \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v) term \<Rightarrow> ('f,'v)term list \<Rightarrow> showsl check" where
  "check_toyama_pcp_join_sequence R R' S S' V s t terms = 
     (case check_steps (\<lambda> s t. (s,t) \<in> rstep (set S)) s terms t
       of (v, vs) \<Rightarrow> case check_optional_step (\<lambda> s t. (t,s) \<in> par_rstep_var_restr (set R) V) v vs t
       of (w, ws) \<Rightarrow> finalize_steps w ws t
         <+? (\<lambda> e. 
        showsl_lit (STR ''could not ensure '') o showsl s o showsl_lit (STR '' -'' + S' + STR ''->* . <-||,'' + R' + STR ''- '') o showsl t o
       e))" 

lemma check_toyama_pcp_join_sequence:
  assumes "isOK(check_toyama_pcp_join_sequence R R' S S' V s t terms)"
  shows "\<exists> v. (s,v) \<in> (rstep (set S))^* 
      \<and> (t, v) \<in> par_rstep_var_restr (set R) V" 
proof -
  let ?check = "check_steps (\<lambda> s t. (s,t) \<in> rstep (set S)) s terms t" 
  obtain v vs where ch: "?check = (v,vs)" by (cases ?check, auto)
  let ?check2 = "check_optional_step (\<lambda>s t. (t, s) \<in> par_rstep_var_restr (set R) V) v vs t" 
  obtain w ws where ch2: "?check2 = (w,ws)" by (cases ?check2, auto)
  from assms[unfolded check_toyama_pcp_join_sequence_def ch ch2 split, simplified] have wt: "w = t" by auto
  show ?thesis
  proof (intro exI[of _ v] conjI)
    show "(s, v) \<in> (rstep (set S))\<^sup>*" 
      by (rule check_steps[OF _ ch])
    from check_optional_step[OF _ ch2, unfolded wt] 
    have "(v, t) \<in> ((par_rstep_var_restr (set R) V)^-1)^=" by blast
    thus "(t, v) \<in> par_rstep_var_restr (set R) V" by auto
  qed
qed

\<comment> \<open>We consider a critical peak/pair s <- t -root -> u and
   demand that there is a list of intermediate terms which is the joining sequence (excluding s and u itself)
   One might also provide information on the positions of the overlap, and the labels of rules.

   For parallel critical pairs, the positions must be provided!
   For rule labeling, it is strongly encouraged that the labels are provided; in combination with parallel CPs, they are mandatory!
   For parallel critical pairs, the peak must be provided.
   \<close>
datatype ('f,'v)crit_pair_info = 
  Crit_Pair_Info (cp_left: "('f,'v)term") (cp_peak: "('f,'v)term option") (cp_right: "('f,'v)term") (cp_join: "('f,'v)term list")
     (cp_poss: "pos list option") (cp_labels: "(nat \<times> nat) option")

(* Auto = limit on breadth-first-search, otherwise joining sequences for each critical pair/peak *)
datatype ('f,'v) cp_join_hints = CP_Auto nat | CP_Sequences "('f, 'v) crit_pair_info list" 

definition "cpPeak = the o cp_peak" 

fun is_rsteps_conversion' where 
  "is_rsteps_conversion' R S (CP_Auto n) = return (\<lambda> s t. check (is_rsteps_conversion R S n s t) 
      (showsl n o showsl_lit (STR '' steps do not suffice to show convertibility of '') 
      o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))" 
| "is_rsteps_conversion' R S (CP_Sequences cp_infos) = (let RS = R @ map prod.swap S in do {
        check_allm (\<lambda> cp. check_rewrite_sequence RS (cp_left cp) (cp_right cp) (cp_join cp)) cp_infos
          <+? (\<lambda>err. err o showsl_lit (STR ''\<newline>underlying TRS:\<newline>'') o showsl_rules RS);
        return (\<lambda> s t. check (s = t \<or> (\<exists> cp \<in> set cp_infos. instance_rule (s,t) (cp_left cp, cp_right cp)))
        (showsl (STR '' could not find conversion for '') o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))
     }) 
    "

lemma is_rsteps_conversion': assumes "is_rsteps_conversion' R S info = return checker"
  and "isOK(checker s t)" 
  shows "(s,t) \<in> (rstep (set R) \<union> (rstep (set S))^-1)^*" 
proof (cases info)
  case (CP_Auto n)
  show ?thesis apply (rule is_rsteps_conversion_conv''[of _ _ n])
    using assms CP_Auto by auto
next
  case *: (CP_Sequences cp_infos)
  show ?thesis
  proof (cases "s = t")
    case False
    with assms[unfolded *, simplified, unfolded Let_def] obtain cp where 
      inst: "instance_rule (s,t) (cp_left cp, cp_right cp)" 
      and ok: "isOK(check_rewrite_sequence (R @ map prod.swap S) (cp_left cp) (cp_right cp) (cp_join cp))" by auto
    have [simp]: "prod.swap ` set S = (set S)^-1" by auto
    from check_rewrite_sequence[OF ok, simplified] 
    have conv: "(cp_left cp, cp_right cp) \<in> (rstep (set R \<union> (set S)\<inverse>))\<^sup>*" by auto
    from inst[unfolded instance_rule_def, simplified] obtain \<sigma> where 
      st: "s = cp_left cp \<cdot> \<sigma>" "t = cp_right cp \<cdot> \<sigma>" by auto
    from conv have "(s,t) \<in> (rstep (set R \<union> (set S)\<inverse>))\<^sup>*" unfolding st by (rule rsteps_closed_subst)
    thus ?thesis unfolding rstep_union rstep_converse .
  qed auto
qed

fun is_rsteps_join_two where 
  "is_rsteps_join_two R S (CP_Auto n) = return (\<lambda> (s,t). check (is_rsteps_join R S n s t) 
      (showsl n o showsl_lit (STR '' steps do not suffice to show joinability of '') 
      o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))" 
| "is_rsteps_join_two R S (CP_Sequences cp_infos) = (do {
        check_allm (\<lambda> cp. check_join_sequence R S (cp_left cp) (cp_right cp) (cp_join cp)) cp_infos
          <+? (\<lambda>err. err o showsl_lit (STR ''\<newline>underlying TRSs:\<newline>'') o showsl_rules R o showsl_nl o showsl_nl o showsl_rules S);
        return (\<lambda> (s,t). check (s = t \<or> (\<exists> cp \<in> set cp_infos. instance_rule (s,t) (cp_left cp, cp_right cp)))
        (showsl (STR '' could not find joining sequence for '') o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))
     }) 
    "

lemma is_rsteps_join_two: assumes "is_rsteps_join_two R S info = return checker"
  and "isOK(checker (s,t))" 
  shows "\<exists> v. (s,v) \<in> (rstep (set R))^* \<and> (t,v) \<in> (rstep (set S))^*" 
proof (cases info)
  case (CP_Auto n)
  show ?thesis apply (rule is_rsteps_join[of _ _ n])
    using assms CP_Auto by auto
next
  case *: (CP_Sequences cp_infos)
  show ?thesis
  proof (cases "s = t")
    case False
    with assms[unfolded *, simplified, unfolded Let_def] obtain cp where 
      inst: "instance_rule (s,t) (cp_left cp, cp_right cp)" 
     and ok: "isOK(check_join_sequence R S (cp_left cp) (cp_right cp) (cp_join cp))" by auto
    have [simp]: "prod.swap ` set S = (set S)^-1" by auto
    from check_join_sequence[OF ok, simplified] obtain v
      where join: "(cp_left cp, v) \<in> (rstep (set R))\<^sup>* \<and> (cp_right cp, v) \<in> (rstep (set S))\<^sup>*" by auto
    from inst[unfolded instance_rule_def, simplified] obtain \<sigma> where 
      st: "s = cp_left cp \<cdot> \<sigma>" "t = cp_right cp \<cdot> \<sigma>" by auto
    from join have "(s, v \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>* \<and> (t, v \<cdot> \<sigma>) \<in> (rstep (set S))\<^sup>*" unfolding st using rsteps_closed_subst by blast
    thus ?thesis ..
  qed auto
qed

fun is_rsteps_join_one where 
  "is_rsteps_join_one R (CP_Auto n) = return (\<lambda> (s,t). check (is_rsteps_join R R n s t) 
      (showsl n o showsl_lit (STR '' steps do not suffice to show joinability of '') 
      o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))" 
| "is_rsteps_join_one R (CP_Sequences cp_infos) = (do {
        check_allm (\<lambda> cp. check_join_sequence R R (cp_left cp) (cp_right cp) (cp_join cp)) cp_infos
          <+? (\<lambda>err. err o showsl_lit (STR ''\<newline>underlying TRS:\<newline>'') o showsl_rules R);
        return (\<lambda> (s,t). check (s = t \<or> (\<exists> cp \<in> set cp_infos. instance_rule (s,t) (cp_left cp, cp_right cp) \<or> instance_rule (s,t) (cp_right cp, cp_left cp)))
        (showsl (STR '' could not find joining sequence for '') o showsl s o showsl_lit (STR '' and '') o showsl t o showsl_nl))
     }) 
    "

lemma is_rsteps_join_one: assumes "is_rsteps_join_one R info = return checker"
  and "isOK(checker (s,t))" 
  shows "\<exists> v. (s,v) \<in> (rstep (set R))^* \<and> (t,v) \<in> (rstep (set R))^*" 
proof (cases info)
  case (CP_Auto n)
  show ?thesis apply (rule is_rsteps_join[of _ _ n])
    using assms CP_Auto by auto
next
  case *: (CP_Sequences cp_infos)
  show ?thesis
  proof (cases "s = t")
    case False 
    with assms[unfolded *, simplified, unfolded Let_def] obtain cp where 
      inst: "instance_rule (s,t) (cp_left cp, cp_right cp) \<or> instance_rule (s,t) (cp_right cp, cp_left cp)" 
      and ok: "isOK(check_join_sequence R R (cp_left cp) (cp_right cp) (cp_join cp))" by force
    have [simp]: "prod.swap ` set R = (set R)^-1" by auto
    from check_join_sequence[OF ok, simplified] obtain v
      where join: "(cp_left cp, v) \<in> (rstep (set R))\<^sup>* \<and> (cp_right cp, v) \<in> (rstep (set R))\<^sup>*" by auto
    from inst show ?thesis
    proof
      assume inst: "instance_rule (s,t) (cp_left cp, cp_right cp)" 
      from inst[unfolded instance_rule_def, simplified] obtain \<sigma> where 
        st: "s = cp_left cp \<cdot> \<sigma>" "t = cp_right cp \<cdot> \<sigma>" by auto
      from join have "(s, v \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>* \<and> (t, v \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*" unfolding st using rsteps_closed_subst by blast
      thus ?thesis ..
    next
      assume inst: "instance_rule (s,t) (cp_right cp, cp_left cp)" 
      from inst[unfolded instance_rule_def, simplified] obtain \<sigma> where 
        st: "t = cp_left cp \<cdot> \<sigma>" "s = cp_right cp \<cdot> \<sigma>" by auto
      from join have "(s, v \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>* \<and> (t, v \<cdot> \<sigma>) \<in> (rstep (set R))\<^sup>*" unfolding st using rsteps_closed_subst by blast
      thus ?thesis ..
    qed
  qed auto
qed

end
