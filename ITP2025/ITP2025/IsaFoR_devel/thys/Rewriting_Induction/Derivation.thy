(*
  Author: Main development by group of Takahito Aoto
  (added to IsaFoR and adjusted to current Isabelle version by RT)
*)

theory Derivation
  imports
    Weighted_Path_Order.Multiset_Extension2
begin

definition is_proof_of ::"('a list) \<Rightarrow> 'a rel \<Rightarrow> bool" where
  [simp]:"is_proof_of ss R \<equiv> (\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in>R\<^sup>\<leftrightarrow>)"

definition is_derivation_of ::"('a list) \<Rightarrow> 'a rel \<Rightarrow> bool" where
  [simp]:"is_derivation_of ss R \<equiv> (\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in>R)"

lemma zero_proof:
  "length ss \<le> 1 \<Longrightarrow> is_proof_of ss R"
  by (cases ss, auto)

lemma zero_derivation:
  "length ss \<le> 1 \<Longrightarrow> is_derivation_of ss R"
  by (cases ss, auto)

lemma cons_subproof_is_proof: "is_proof_of (s#ss) R \<Longrightarrow> is_proof_of ss R" 
  by (induct ss) auto

lemma cons_subderivation_is_derivation: "is_derivation_of (s#ss) R \<Longrightarrow> is_derivation_of ss R" 
  by (induct ss) auto

lemma derivation_rtrancl:"ss\<noteq>[] \<and> hd ss = s \<and> is_derivation_of ss R \<longrightarrow> (\<forall>u\<in>set ss. (s,u)\<in>R^*)"
proof (rule impI)
  assume "ss\<noteq>[] \<and> hd ss = s \<and> is_derivation_of ss R"
  then show "(\<forall>u\<in>set ss. (s,u)\<in>R^*)"
  proof (induction ss arbitrary:s)
    case (Cons a ss)
    then have *:"is_derivation_of (a#ss) R" by auto
    then have **:"is_derivation_of ss R" apply (rule cons_subderivation_is_derivation) done
    then show ?case 
    proof (cases "ss=[]")
      case True
      then have "a#ss = [a]" by simp
      also have "hd (a#ss) = a" by simp
      ultimately show ?thesis using Cons.prems by auto
    next
      case False
      then obtain t where t:"hd ss = t" by simp
      then have "(\<forall>u\<in>set ss. (t,u)\<in>R^*)" using Cons ** by fastforce
      also have "(a,t)\<in>R" using Cons.prems False hd_conv_nth list.sel(1) t by force
      ultimately have "(\<forall>u\<in>set (a#ss). (a,u)\<in>R^*)" by auto
      then show ?thesis using Cons.prems by auto
    qed
  qed simp
qed    

lemma length_div_sublemma:
  assumes "\<forall>i<length ss-1. i\<ge>j \<longrightarrow> P(ss!i,ss!(i+1))"
    and "\<forall>i<length ss-1. i<j \<longrightarrow> P(ss!i,ss!(i+1))" 
  shows "\<forall>i<length ss-1. P(ss!i,ss!(i+1))" using assms by auto

lemma length_div_sublemma':
  assumes "\<forall>i<length ss-1. i\<ge>j \<longrightarrow> P(ss!i,ss!(i+1))"
    and "\<forall>i<length ss-1. i=j-1 \<longrightarrow> P(ss!i,ss!(i+1))"
    and "\<forall>i<length ss-1. i<j-1 \<longrightarrow> P(ss!i,ss!(i+1))" 
  shows "\<forall>i<length ss-1. P(ss!i,ss!(i+1))"
proof -
  have "\<forall>i<length ss-1. i\<ge>j-1 \<longrightarrow> P(ss!i,ss!(i+1))" using assms(1) assms(2) by fastforce
  then show ?thesis using length_div_sublemma assms(3) by blast
qed      



lemma cons_P_sublemma:
  assumes "\<forall>i<length list-1. P (list!i,list!(i+1))"
    and "P(a,hd list)"
  shows "\<forall>i<length (a#list)-1. P((a#list)!i,(a#list)!(i+1))"
proof (cases list)
  case (Cons c list')
  then have t1:"(a#c#list')!0 = a \<and> (a#c#list')!1 =c " by simp
  have t2:"hd list = c" using Cons by simp
  have "\<forall>i<length (c#list')-1. P((c#list')!i,(c#list')!(i+1))" using assms Cons by simp
  then have t3:"\<forall>i<length (a#c#list')-1. i\<ge>1 \<longrightarrow> P((a#c#list')!i,(a#c#list')!(i+1))" by simp
  then have t4:"\<forall>i<length (a#c#list')-1. i<1 \<longrightarrow> P((a#c#list')!i,(a#c#list')!(i+1))" using assms t1 t2 by simp
  then have t5:"\<forall>i<length (a#c#list')-1. P((a#c#list')!i,(a#c#list')!(i+1))" using t3 t4 length_div_sublemma by blast
  have "a#c#list' = a#list " using Cons by simp
  then show ?thesis using t5 by simp
qed simp


lemma app_P_sublemma:
  assumes "\<forall>i<length list-1. P(list!i,list!(i+1))"
    and "\<forall>i<length list'-1. P(list'!i,list'!(i+1))"
    and "P(last list,hd list')" and "list \<noteq>[]" and "list' \<noteq> []" 
  shows "\<forall>i<length (list@list')-1. P((list@list')!i,(list@list')!(i+1))"
proof -
  have "\<forall>i<length (list@list')-1. i<length list-1 \<longrightarrow> (list@list')!i = list!i \<and> (list@list')!(i+1) = list!(i+1)" using nth_append 
    by (metis add_lessD1 less_diff_conv)
  then have t1:"\<forall>i<length (list@list')-1. i<length list-1 \<longrightarrow> P((list@list')!i,(list@list')!(i+1))" using assms(1) by simp
  have "\<forall>i<length (list@list')-1. i\<ge>length list \<longrightarrow> (list@list')!i = list'!(i-length list) \<and> (list@list')!(i+1) = list'!(i-length list+1)" 
    using nth_append  Nat.add_diff_assoc add.commute add_lessD1 not_less by metis
  also have "\<forall>i<length (list@list')-1.  i\<ge>length list \<longrightarrow> i-length list<length list'-1" by auto
  ultimately have t2:"\<forall>i<length (list@list')-1. i\<ge>length list \<longrightarrow> P((list@list')!i,(list@list')!(i+1))" using assms(2) by simp 
  have "\<forall>i<length (list@list')-1. i=length list-1 \<longrightarrow> (list@list')!i = list!(length list-1) \<and> (list@list')!(i+1) = list'!0 "
    by (simp add: nth_append assms(4))
  also have "list!(length list-1) = last list" " list'!0 = hd list'" 
    using last_conv_nth[of list] assms(4) apply simp using hd_conv_nth[of list'] assms(5) by simp
  ultimately have t3:"\<forall>i<length (list@list')-1. i=length list-1 \<longrightarrow> P((list@list')!i,(list@list')!(i+1))" using assms(3) by simp
  then show ?thesis using t1 t2 t3 length_div_sublemma'[of "list@list'" "length list" P] by blast
qed

lemma app_Cons_P_sublemma:
  assumes "\<forall>i<length list-1. P(list!i,list!(i+1))"
    and "\<forall>i<length list'-1. P(list'!i,list'!(i+1))"
    and "P(last list,hd list')"
    and "P(a,hd list)" and "list \<noteq>[]" and "list' \<noteq> []"
  shows "\<forall>i<length (a#list@list')-1. P((a#list@list')!i,(a#list@list')!(i+1))"
proof -
  have "\<forall>i<length (list@list')-1. P((list@list')!i,(list@list')!(i+1))" using app_P_sublemma[of list P list'] assms(1) assms(2) assms(3) assms(5) assms(6) by simp
  also have "hd list = hd (list@list')" using assms(5) by simp
  then have "P(a,hd (list@list'))" using assms(4) by argo
  ultimately show ?thesis using cons_P_sublemma[of "list@list'" P a] by simp
qed

lemma derivation_propagation:
  assumes "\<forall>a b. P a \<and> (a,b)\<in>R \<longrightarrow> P b"
    and "is_derivation_of ss R" and "ss\<noteq>[]"
    and "P(hd ss)"
  shows "\<forall>i<length ss. P (ss!i)" 
proof -
  obtain a xs where ss:" ss= (a#xs)" using assms(3) list.exhaust_sel by auto
  then have "is_derivation_of (a#xs) R" using assms(2) by simp
  also have "P a" using assms(4) ss by simp
  ultimately have "\<forall>i<length (a#xs). P ((a#xs)!i)"
  proof (induction xs arbitrary:a)
    case (Cons b xs)
    then have "(a,b)\<in>R" by auto
    then have "P(b)" using Cons(3) assms(1) by blast
    also have "is_derivation_of (b#xs) R" using Cons(2) by force
    ultimately have "\<forall>i<length (b#xs).  P ((b#xs)!i)" using Cons(1) by simp
    then have "\<forall>x\<in>set(b#xs). P x" using all_set_conv_all_nth[of "b#xs" P] by blast
    then have "\<forall>x\<in>set(a#b#xs). P x" using Cons(3) by simp
    then show ?case using all_set_conv_all_nth[of "a#b#xs" P] by blast
  qed auto
  then show ?thesis using ss by simp
qed


lemma cons_is_proof:
  assumes "is_proof_of ss R"  
    and "ss =[] \<or> (s,hd ss)\<in>R\<^sup>\<leftrightarrow>"
  shows "is_proof_of (s#ss) R"  
proof (cases ss)
  case (Cons a list)
  let ?P = "\<lambda>(x,y). (x,y)\<in>R\<^sup>\<leftrightarrow>"
  have *:"\<forall>i<length ss-1. ?P (ss!i,ss!(i+1))" using assms  by simp
  have "?P(s,hd ss)" using assms Cons by simp
  then have"\<forall>i<length (s#ss)-1. ?P((s#ss)!i,(s#ss)!(i+1))" using * cons_P_sublemma by metis
  then show ?thesis  by simp
qed auto

lemma cons_is_derivation:
  assumes "is_derivation_of ss R"  
    and "ss =[] \<or> (s,hd ss)\<in>R"
  shows "is_derivation_of (s#ss) R"  
proof (cases ss)
  case (Cons a list)
  let ?P = "\<lambda>(x,y). (x,y)\<in>R"
  have *:"\<forall>i<length ss-1. ?P (ss!i,ss!(i+1))" using assms  by simp
  have "?P(s,hd ss)" using assms Cons by simp
  then have"\<forall>i<length (s#ss)-1. ?P((s#ss)!i,(s#ss)!(i+1))" using * cons_P_sublemma by metis
  then show ?thesis  by simp
qed auto


lemma cons_R_ref:
  assumes "is_proof_of (s#ss) R"
  shows "ss=[] \<or> (s,hd ss)\<in>R\<^sup>\<leftrightarrow>"
proof (cases ss)
  case (Cons a list)
  then have *:"hd ss = a" by simp
  {
    assume "(s,a)\<notin>R\<^sup>\<leftrightarrow>" 
    then have "\<not>is_proof_of(s#ss) R" using Cons  by auto
    then have False using assms by auto
  }
  then show ?thesis using * by auto
qed auto


lemma app_subproof_is_proof:
  assumes "is_proof_of (ss@ts) R"
  shows "is_proof_of ss R \<and> is_proof_of ts R" using assms 
proof (induction "length ss" arbitrary:ss)
  case (Suc n)
  then obtain a ss' where ss':" ss= a#ss'" using length_Suc_conv by metis
  then have *:"ss'=[] \<or> (a,hd ss')\<in>R\<^sup>\<leftrightarrow>" using cons_R_ref Suc.prems
    by (metis append_Cons append_is_Nil_conv hd_append2)
  have ss'len:"length ss'=n" using Suc ss' by simp
  then have "is_proof_of ((a#ss')@ts) R " using Suc ss'  by simp
  then have "is_proof_of (ss'@ts)  R" using cons_subproof_is_proof by (metis append_Cons)
  then have "is_proof_of ss' R \<and> is_proof_of ts R" using Suc.hyps ss'len ss' by auto  
  then show ?case using *  cons_is_proof ss' by metis
qed auto

lemma derivation_ordered:
  assumes "ss\<noteq>[]" "is_derivation_of ss (R\<inter>S)"
    and "trans S" and "refl S"
  shows "is_derivation_of ss R"(is ?a) "\<forall>i<length ss. (hd ss,ss!i)\<in>S"(is ?b)
proof -
  show ?a using assms by simp
  show ?b using assms(1) assms(2)
  proof (induction ss)
    case (Cons a ss)
    then show ?case 
    proof (cases "ss=[]")
      case True
      then have "a#ss = [a]" by simp
      then have "\<forall>i<length (a#ss). (hd (a#ss),(a#ss)!i)\<in>S" using assms(4) 
        by (simp add: refl_on_def)
      then show ?thesis by simp
    next
      case False
      also have "is_derivation_of ss (R\<inter>S)" using cons_subderivation_is_derivation Cons by fast  
      ultimately have "\<forall>i<length ss. (hd ss,ss!i)\<in>S" using Cons by simp
      also have "((a#ss)!0, (a#ss)!1)\<in>R\<inter>S" using False Cons(3) by auto
      then have "(a, ss!0)\<in>R\<inter>S" using nth_Cons by auto
      then have "(a, hd ss)\<in>R\<inter>S " using hd_conv_nth False by metis
      ultimately have "\<forall>i<length ss. (a,ss!i)\<in>S" using assms(3) transD IntD2 by metis
      also then have "\<forall>i<length (a#ss). (a, (a#ss)!i)\<in>S" using assms(4) 
          IntD2 One_nat_def Suc_leI \<open>(a, hd ss) \<in> R \<inter> S\<close> less_diff_conv2 list.size(4) not_gr0 nth_Cons' nth_Cons_0 refl_onD refl_onD1
        by metis
      then show ?thesis using assms(4) Cons by simp
    qed
  qed auto
qed

lemma rtrancl_iff_derivation:
  "(x,y)\<in>R^* \<longleftrightarrow> (\<exists>ss. ss\<noteq>[] \<and>  hd ss = x \<and> last ss = y \<and> is_derivation_of ss R)"(is "?L \<longleftrightarrow>?R")
proof 
  assume ?L 
  then obtain i where i:"(x,y)\<in>R^^i" by auto
  then show ?R
  proof (induction i arbitrary:x)
    case (Suc i)
    then obtain u where u:"(x,u)\<in>R \<and> (u,y)\<in>R^^i" using relpow_Suc_E2 by metis
    then obtain ts where ts:"ts\<noteq>[] \<and>  hd ts = u \<and> last ts = y \<and> is_derivation_of ts R" using Suc by presburger
    then have "x#ts \<noteq> [] \<and> hd (x#ts) = x \<and> last (x#ts) = y \<and> is_derivation_of (x#ts) R" using cons_is_derivation last_ConsR u list.sel(1) list.simps(3) by fast
    then show ?case by blast
  qed auto
next 
  assume ?R
  then obtain ss where ss:"ss\<noteq>[]\<and> hd ss = x \<and> last ss = y \<and> is_derivation_of ss R" by auto
  show ?L using ss
  proof (induction "length ss" arbitrary:ss x)
    case (Suc n)
    then obtain a ss' where ss':"ss = a#ss'" using length_Suc_conv by metis 
    have ss'len:"length ss' = n" using Suc ss' by simp
    consider "ss'=[]" | "ss'\<noteq>[]" by auto
    then show "(x, y) \<in> R\<^sup>*"
    proof cases
      case 1
      then have " hd ss = a \<and> last ss = a" using Cons ss' by simp
      then have " (x,y) = (a,a)" using ss Suc by simp
      then show ?thesis 
        using "1" Suc.hyps(2) Suc.prems ss'len by auto
    next
      case 2
      then obtain s where st:"hd ss' = s \<and> last ss' = y \<and> is_derivation_of ss' R" 
        using Suc.prems cons_subderivation_is_derivation ss' by (metis last_ConsR)
      then have *:"ss'\<noteq>[] \<longrightarrow> (a,s)\<in>R" using ss' cons_R_ref Suc.prems hd_conv_nth by fastforce
      have **:"(s,y)\<in>R\<^sup>*" using Suc.hyps 
      proof (cases "length ss'\<le>1")
        case True
        then have "ss' = [s] \<and> s = y" using st 2 
          by (metis Suc_length_conv ex_least_nat_less last_ConsL le_SucE length_greater_0_conv less_numeral_extra(3) less_one list.sel(1))          
        then show ?thesis using 2 by simp
      next
        case False
        then have"length ss' \<ge>2" by simp
        then show ?thesis using Suc.hyps st ss'len 2 by blast
      qed      
      then show"(x,y)\<in>R\<^sup>*" 
      proof -
        have "(a,s)\<in>R" using 2 * by simp
        then have t:"(a,y)\<in>R^*" using ** by simp
        then have "a=x" using Suc ss' by simp
        then have "(x,y)\<in>R\<^sup>*" using t by simp
        then show ?thesis by simp
      qed
    qed
  qed auto
qed


lemma rtrancl_iff_proof:
  "(x,y)\<in>R\<^sup>\<leftrightarrow>\<^sup>* \<longleftrightarrow> (\<exists>ss. ss\<noteq>[] \<and>  hd ss = x \<and> last ss = y \<and> is_proof_of ss R)" (is "?L \<longleftrightarrow>?R")
proof 
  assume ?L 
  then obtain i where i:"(x,y)\<in>R\<^sup>\<leftrightarrow>^^i"  by auto
  then show ?R 
  proof (induction i arbitrary:x)
    case (Suc i)        
    then obtain u where u:"(x,u)\<in>R\<^sup>\<leftrightarrow>\<and> (u,y)\<in>R\<^sup>\<leftrightarrow>^^i" by (meson relpow_Suc_E2)
    then obtain ts where ts:"ts\<noteq>[] \<and>  hd ts = u \<and> last ts = y \<and> is_proof_of ts R" using Suc by auto
    then have "x#ts \<noteq> [] \<and> hd (x#ts) = x \<and> last (x#ts) = y \<and> is_proof_of (x#ts) R" by (metis cons_is_proof last_ConsR list.sel(1) list.simps(3) u)
    then show ?case by blast
  qed auto
next
  assume ?R
  then obtain ss where ss:"ss\<noteq>[]\<and> hd ss = x \<and> last ss = y \<and> is_proof_of ss R" by auto
  show ?L using ss
  proof (induction "length ss" arbitrary:ss x)
    case (Suc n)
    then obtain a ss' where ss':"ss = a#ss'" using length_Suc_conv by metis 
    have ss'len:"length ss' = n" using Suc ss' by simp
    consider "ss'=[]" | "ss'\<noteq>[]" by auto
    then show "(x, y) \<in> R\<^sup>\<leftrightarrow>\<^sup>*"
    proof cases
      case 1
      then have " hd ss = a \<and> last ss = a" using Cons ss' by simp
      then have " (x,y) = (a,a)" using ss Suc by simp
      then show ?thesis 
        using "1" Suc.hyps(2) Suc.prems ss'len by auto
    next
      case 2
      then obtain s where st:"hd ss' = s \<and> last ss' = y \<and> is_proof_of ss' R" 
        using Suc.prems cons_subproof_is_proof ss' by (metis last_ConsR)
      then have *:"ss'=[] \<or> (a,s)\<in>R\<^sup>\<leftrightarrow>" using ss' ss cons_R_ref Suc.prems by metis
      have **:"(s,y)\<in>R\<^sup>\<leftrightarrow>\<^sup>*" using Suc.hyps 
      proof (cases "length ss'\<le>1")
        case True
        then have "ss' = [s] \<and> s = y" using st 2
          by (metis Suc_length_conv ex_least_nat_less last_ConsL le_SucE length_greater_0_conv less_numeral_extra(3) less_one list.sel(1))
        then show ?thesis using 2 by simp
      next
        case False
        then have"length ss' \<ge>2" by simp
        then show ?thesis using Suc.hyps st ss'len 2 by blast
      qed      
      then show"(x,y)\<in>R\<^sup>\<leftrightarrow>\<^sup>*" 
      proof -
        have "(a,s)\<in>R\<^sup>\<leftrightarrow>" using 2 * by simp
        then have t:"(a,y)\<in>R\<^sup>\<leftrightarrow>\<^sup>*" using **  by (simp add: converse_rtrancl_into_rtrancl conversion_def)
        then have "a=x" using Suc ss' by simp
        then have "(x,y)\<in>R\<^sup>\<leftrightarrow>\<^sup>*" using t by simp
        then show ?thesis by simp
      qed
    qed
  qed auto
qed

lemma trancl_proof_length_2:
  assumes "(x,y)\<in>R^+" 
    and "(ss\<noteq>[] \<and>  hd ss = x \<and> last ss = y \<and> is_derivation_of ss R)"
    and "SN R"
  shows "length ss\<ge>2"
proof (rule ccontr)
  assume "\<not>length ss\<ge>2" 
  then have "length ss \<le>1 " by simp
  then have "length ss = 1 " using assms(2) by (simp add: Suc_leI dual_order.antisym)
  then have "x = y" using assms(2) hd_conv_nth last_conv_nth by fastforce
  then have "(x,y)\<notin>R^+" using assms(3) by (meson SN_imp_SN_trancl refl_not_SN)
  then show False using assms(1) by simp
qed  

lemma [simp]:" (s,t)\<in>R\<^sup>\<leftrightarrow>\<^sup>* \<longrightarrow> (s,t)\<in>(R\<union>E)\<^sup>\<leftrightarrow>\<^sup>*"
proof (rule impI)
  assume a:"(s,t)\<in>R\<^sup>\<leftrightarrow>\<^sup>*"
  have "R\<subseteq>(R\<union>E)" by simp
  then have "R\<^sup>\<leftrightarrow>\<subseteq>(R\<union>E)\<^sup>\<leftrightarrow>" by auto
  then have "R\<^sup>\<leftrightarrow>\<^sup>*\<subseteq>(R\<union>E)\<^sup>\<leftrightarrow>\<^sup>*" by (simp add: conversion_mono)
  then show "(s,t)\<in>(R\<union>E)\<^sup>\<leftrightarrow>\<^sup>*" using a by auto
qed  

lemma length_P_sublemma[simp]:
  assumes "\<forall>i<length (a#list)-1. P ((a#list)!i,(a#list)!(i+1))"
  shows "\<forall>i<length (list)-1. P((list)!i,(list)!(i+1))" using assms
proof (induction list)
  case (Cons c list)
  then have "\<forall>i<length (c#list)-1. P((c#list)!i,(c#list)!(i+1))" by auto
  then show ?case by simp
qed auto


lemma cons_proof:
  assumes "is_proof_of (s#ss) R"  
  shows "is_proof_of ss R" 
proof -
  have "is_proof_of (s#ss) R" using assms by simp
  then have "\<forall>i<length (s#ss)-1. ((s#ss)!i,(s#ss)!(i+1))\<in>R\<^sup>\<leftrightarrow>" using is_proof_of_def by blast
  then have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in>R\<^sup>\<leftrightarrow>" proof (rule length_P_sublemma) qed
  then show ?thesis using is_proof_of_def by auto
qed



lemma app_proof:
  assumes "is_proof_of ss R"
    and "is_proof_of ts S"
    and "length ss >0 " 
    and "(last ss,hd ts) \<in>(R\<union>S)\<^sup>\<leftrightarrow>"
  shows "is_proof_of (ss@ts) (R\<union>S)" using assms(1) assms(3) assms(4) 
proof (induction "length ss" arbitrary:ss) 
  case (Suc n)
  then obtain ss' s where ss':"ss = s#ss'" using length_Suc_conv by metis
  then have lenss':"length ss' = n" using Suc.hyps by simp
  then have h1:"is_proof_of ss' R" using cons_proof ss' Suc by metis
  then have "is_proof_of (ss@ts) (R\<union>S)"
  proof (cases "length ss' = 0")
    case True
    then have ss:"ss = [s]" using ss' Suc by simp
    then have lastss:"last ss = s" by simp
    then have t1:"ss@ts = s#ts" using ss by simp
    then have shd:"(s,hd ts)\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using ss Suc lastss by argo
    have t2:"\<forall>i<length ts-1. (ts!i,ts!(i+1))\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using assms is_proof_of_def by auto
    have "\<forall>i<length (s#ts)-1. ((s#ts)!i,(s#ts)!(i+1))\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using t2 shd proof (rule cons_P_sublemma) qed
    then show ?thesis using t1 is_proof_of_def by metis
  next
    case False    
    then have lenss:"length ss \<ge>2 " using lenss' Suc.hyps(2) by simp
    then have "ss'\<noteq>[]" using False by simp
    then have "hd ss' = ss'!0" using hd_conv_nth by auto 
    then have f1:"ss!0 =s \<and> ss!1 = hd ss'" using ss' by simp
    have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in>R\<^sup>\<leftrightarrow>" using Suc.prems(1) is_proof_of_def f1 by auto
    then have shdssts:"(s,hd (ss'@ts))\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using Suc.prems(1) ss' is_proof_of_def f1 lenss False by fastforce
    have "(last ss',hd ts)\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using Suc False ss' by simp
    then have "is_proof_of (ss'@ts) (R\<union>S)" using Suc.hyps(1) lenss' h1 False is_proof_of_def by auto
    then have "\<forall>i<length (ss'@ts)-1. ((ss'@ts)!i,(ss'@ts)!(i+1))\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using is_proof_of_def by metis
    then have t1:"\<forall>i<length (s # ss'@ts) - 1. ((s # ss'@ts) ! i, (s # ss'@ts) ! (i + 1))\<in>(R\<union>S)\<^sup>\<leftrightarrow>" using shdssts by(rule cons_P_sublemma)
    have "ss@ts = s#ss'@ts" using ss' by simp
    then show ?thesis using is_proof_of_def t1 by metis
  qed
  then show ?case by simp
qed auto

lemma app_proof2:
  assumes "is_proof_of ss R"
    and "is_proof_of ts R"
    and "length ss >0" 
    and "(last ss,hd ts) \<in> R\<^sup>\<leftrightarrow>"
  shows "is_proof_of (ss@ts) R" 
  using app_proof assms by (metis sup.idem)

lemma rev_proof:
  assumes "is_proof_of ss R"
  shows "is_proof_of (rev ss) R"
proof -
  from assms have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in>R\<^sup>\<leftrightarrow>" using is_proof_of_def by auto
  then have "\<forall>i<length ss-1. (ss!(i+1),ss!i)\<in>R\<^sup>\<leftrightarrow>" by auto
  then have "\<forall>i<length (rev ss)-1. ((rev ss)!i,(rev ss)!(i+1))\<in>R\<^sup>\<leftrightarrow>"
    by (smt Suc_diff_Suc Suc_eq_plus1 add_lessD1 length_rev less_add_one less_diff_conv rev_nth)
  then show ?thesis using is_proof_of_def by blast
qed


lemma derivation_is_proof[simp]:
  "is_derivation_of ss R \<longrightarrow> is_proof_of ss R" by simp

lemma derivation_is_proof_rev[simp]:
  "is_derivation_of ss R \<longrightarrow> is_proof_of (rev ss) R" using derivation_is_proof 
  by (metis rev_proof)

lemma rev_derivation_is_proof[simp]:
  "is_derivation_of (rev ss) R \<longrightarrow> is_proof_of ss R" using derivation_is_proof 
  by (metis List.rev_rev_ident rev_proof)

lemma derivation_hd_nth_rtrancl:
  "is_derivation_of ss R \<longrightarrow> (\<forall>i<length ss. (hd ss,ss!i)\<in>R^*)"
proof (rule impI)
  assume "is_derivation_of ss R"
  then have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in> R^*" by auto
  then show "(\<forall>i<length ss. (hd ss,ss!i)\<in>R^*)"
  proof (induction ss)
    case (Cons a ss)
    then have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<in> R^*" using length_P_sublemma[of a ss "\<lambda>x. x\<in>R^*"] by blast
    then have *:"\<forall>i<length ss. (hd ss,ss!i)\<in>R^*" using Cons by blast
    then show ?case 
    proof (cases "length ss=0")
      case False
      then have "(a,ss!0)\<in>R^*" using Cons by auto
      also have "\<forall>x\<in>set ss. (hd ss,x)\<in>R^*" using * all_set_conv_all_nth[of ss "\<lambda>x. (hd ss,x)\<in>R^*"] by blast
      moreover have "ss\<noteq>[]" using False by simp
      ultimately have "\<forall>x\<in>set (a#ss). (a,x)\<in>R^*" using rtrancl_trans[of a "hd ss" R] hd_conv_nth[of ss] False by simp
      then show ?thesis using all_set_conv_all_nth[of "a#ss" "\<lambda>x. (hd (a#ss),x)\<in>R^*"] by auto
    qed auto
  qed auto
qed

lemma superset_proof:
  assumes "is_proof_of ss R"
  shows "\<forall>S. is_proof_of ss (R\<union>S)" 
  by (metis UnCI assms is_proof_of_def symcl_Un)

lemma rev_hd_last:
  assumes "hd list = h \<and> last list = l"
    and "length list > 0"
  shows "hd (rev list) = l \<and> last (rev list) = h"  
  using assms(1) assms(2) hd_rev last_rev less_numeral_extra(3) by auto



definition strict_ge ::"'a rel \<Rightarrow> 'a rel"
  where "strict_ge ge \<equiv> ge - ge\<inverse>"

(****************************************************************************************************)
definition Rgestar ::" ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> 'a rel" 
  where [simp]:"Rgestar ns s R = 
          {(x,y)| x y xs. xs \<noteq>[] \<and> hd xs =x \<and> last xs = y \<and> is_proof_of xs R 
                          \<and> (\<forall>i<length xs. (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s)}"

definition Rgestar_on ::" 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a rel \<Rightarrow> 'a set \<Rightarrow> 'a rel" 
  where [simp]:"Rgestar_on ns s R A = 
          {(x,y)| x y xs. xs \<noteq>[] \<and> hd xs =x \<and> last xs = y \<and> is_proof_of xs R 
                          \<and> (\<forall>i<length xs. (xs!i)\<in>A) 
                          \<and> (\<forall>i<length xs. (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s)}"

definition R\<^sub>1geR\<^sub>2gtstar:: "('a rel) \<Rightarrow> ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> 'a rel" 
  where [simp]: "R\<^sub>1geR\<^sub>2gtstar ns s R\<^sub>1 R\<^sub>2 = 
          {(x,y)| x y xs. xs\<noteq>[]  \<and> hd xs = x \<and> last xs = y \<and> is_proof_of xs (R\<^sub>1\<union>R\<^sub>2) 
                          \<and> (\<forall>i<length xs. (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s) 
                          \<and> (\<forall>i<length xs - 1. (xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow> 
                                               ({#x,y#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext ns s)}"

definition R\<^sub>1geR\<^sub>2gtstar_on:: "('a rel) \<Rightarrow> ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> ('a rel) \<Rightarrow> 'a set \<Rightarrow> 'a rel" 
  where [simp]: "R\<^sub>1geR\<^sub>2gtstar_on ns s R\<^sub>1 R\<^sub>2 A = 
          {(x,y)| x y xs. xs\<noteq>[]  \<and> hd xs = x \<and> last xs = y \<and> is_proof_of xs (R\<^sub>1\<union>R\<^sub>2) 
                          \<and> (\<forall>i<length xs. (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s) 
                          \<and> (\<forall>i<length xs. (xs!i)\<in>A) 
                          \<and> (\<forall>i<length xs - 1. (xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow> 
                                               ({#x,y#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext ns s)}"    

(****************************************************************************************************)
lemma r1r2_on_intro:
  "xs\<noteq>[]  \<and> hd xs = x \<and> last xs = y \<and> 
            is_proof_of xs (R\<^sub>1\<union>R\<^sub>2) \<and>
            (\<forall>i<length xs .  (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s) \<and> (\<forall>i<length xs .  (xs!i)\<in>A) \<and>
            (\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow> ({#x,y#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext ns s)
  \<Longrightarrow> (x,y)\<in>R\<^sub>1geR\<^sub>2gtstar_on ns s R\<^sub>1 R\<^sub>2 A " by auto


end