(*
  Author: Main development by group of Takahito Aoto
  The following changes were done by RT: 
  - added to IsaFoR and adjusted to current Isabelle version
  - changed unification part to use mgu_var_disjoint to get finitely many Expd-Rules
  - added another set of RI rules (ri_step') and show that these can be simulated by ri_step
*)

theory Rewriting_Induction
  imports 
    Basic_Term
    First_Order_Rewriting.Unification_More
begin   
  (*************************************************************************************************)    
locale standard_basic = reduction_order_pair  +
  fixes R:: "('a,'b)trs"
    and D C ::"'a sig"
    and ren_a ren_b :: "'b \<Rightarrow> 'b" 
  assumes wf_R: "wf_trs R" 
    and DC1:" defined_funas R \<subseteq> D"
    and DC2:" constr_funas R \<subseteq> C"
    and DC3: "D\<inter>C ={}"
    (* RT: DC4 must be weakened! 
         currently this is practically not satisfiable;
         in particular choosing D = UNIV - C is not possible since then
         quasi-reducible is not satisfied *)
    and DC4:"\<forall>t::('a,'b) term. funas_term t \<subseteq> D\<union>C"
    and RI1:"R \<subseteq> S"
    and RI2:"quasi_reducible D C R"
    and REN:"inj ren_a" "inj ren_b" "range ren_a \<inter> range ren_b = {}"       
begin

lemma TRS1:"\<forall>rule\<in>R. is_Fun (fst rule)"
   and TRS2:"\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l"
  using wf_R unfolding wf_trs_def by force+

lemma rstep_R_S: "(s,t)\<in>rstep R \<Longrightarrow> (s,t)\<in>S" using RI1 ctxt_S subst_S by blast

lemma rstep_rtrancl_NS_S:"(s,t)\<in>(rstep R)^*\<Longrightarrow> (s,t)\<in>NS\<union>S"
proof (induct rule: rtrancl_induct)
  case base
  then show ?case by (meson UNIV_I refl_NS_S refl_onD)
next
  case (step y z)
  then show ?case 
    by (meson Un_iff trans rstep_R_S transD)
qed

lemma derivation_all_NS_S:
  assumes "is_derivation_of ss (NS\<union>S)"
  shows "\<forall>i<length ss. (ss!0,ss!i)\<in>(NS\<union>S)" using assms 
proof (induction ss)
  case (Cons a ss)
  then have "is_derivation_of ss (NS\<union>S)" using cons_subderivation_is_derivation by metis
  then have *:"\<forall>i<length ss.  (ss!0,ss!i)\<in>(NS\<union>S)" using Cons by simp
  then show ?case 
  proof (cases "ss\<noteq>[]")
    case True
    then have "length (a#ss) \<ge>0 " using Cons by simp
    then have "((a#ss)!0,(a#ss)!1)\<in>(NS\<union>S)" using Cons True unfolding is_derivation_of_def by auto
    then have "\<forall>i<length ss. ((a#ss)!0,ss!i)\<in>(NS\<union>S)" using * trans One_nat_def less_one nth_Cons_Suc transD by metis
    then have "\<forall>i<length (a#ss).  i\<ge>1 \<longrightarrow>((a#ss)!0,(a#ss)!i)\<in>(NS\<union>S)" using * True by simp
    also have "\<forall>i<length (a#ss).  i<1 \<longrightarrow>((a#ss)!0,(a#ss)!i)\<in>(NS\<union>S)" using refl_NS_S refl_onD[of UNIV "NS\<union>S"] by blast
    ultimately show ?thesis by fastforce
  next
    case False
    then show ?thesis using refl_NS_S refl_onD[of UNIV "NS\<union>S"] by simp
  qed
qed simp

lemma derivation_all_S:
  assumes "is_derivation_of ss (rstep R)"
  shows "\<forall>i<length ss. i\<ge>1 \<longrightarrow> (ss!0,ss!i)\<in>S" using assms 
proof (induction ss)
  case (Cons a ss)
  then have "is_derivation_of ss (rstep R)" using cons_subderivation_is_derivation by metis
  then have *:"\<forall>i<length ss. i\<ge>1 \<longrightarrow> (ss!0,ss!i)\<in>S" using Cons by simp
  then show ?case 
  proof (cases "ss\<noteq>[]")
    case True
    then have "length (a#ss) \<ge>0 " using Cons by simp
    then have "((a#ss)!0,(a#ss)!1)\<in>(rstep R)" using Cons True unfolding is_derivation_of_def by auto
    then have "((a#ss)!0,(a#ss)!1)\<in>S" using rstep_R_S by simp
    then have "\<forall>i<length ss. ((a#ss)!0,ss!i)\<in>S" using * trans_S One_nat_def less_one not_less nth_Cons_Suc transD by metis
    then have "\<forall>i<length (a#ss).  i\<ge>1 \<longrightarrow>((a#ss)!0,(a#ss)!i)\<in>S" using * trans_S True by simp
    then show ?thesis by simp
  qed simp
qed simp

lemma refl_NS': "(v,v)\<in>NS" 
  using refl_NS unfolding refl_on_def by auto

lemma refl_multpw_NS:"(M,M)\<in>multpw (NS\<inverse>)" 
  by (simp add: locally_refl_def multpw_refl' refl_NS')

lemma one_same_s_mul_ext:
  "(s,s1)\<in>S \<longrightarrow> ({#s,t#},{#s1,t#})\<in>s_mul_ext NS S "
  using ns_mul_ext_refl refl_NS s_ns_mul_ext_union_compat by fastforce

lemma add_mset_s_mul_ext:
  "({#s,t#},{#s#})\<in>s_mul_ext NS S"
  by (metis add_mset_add_single empty_not_add_mset ns_mul_ext_refl refl_NS s_mul_ext_ne_extend_left)

lemma stricts_s_mul_ext':
  "(s,s1)\<in>S \<and> (s,s2)\<in>S \<longrightarrow>  ({#s#},{#s1,s2#})\<in>s_mul_ext NS S "
  by (simp add: all_s_s_mul_ext)


lemma stricts_s_mul_ext:
  "(s,s1)\<in>S \<and> (s,s2)\<in>S \<longrightarrow>  ({#s,t#},{#s1,s2#})\<in>s_mul_ext NS S "
  by (metis add_mset_add_single s_mul_ext_extend_left stricts_s_mul_ext')

lemma length_2_s_mul_ext:
  assumes "length ss\<ge>2 \<longrightarrow> (ss!0,ss!(length ss-1))\<in>S"
    and "length ts\<ge>2 \<longrightarrow> (ts!(length ts-1),ts!0)\<in>S" 
    and "(ts!(length ts-1), (ss @ ts) ! (length ss-1)) \<in> NS \<union> S \<or> (ss!0, (ss @ ts) ! (length ss-1)) \<in> NS \<union> S " 
    and "(ts!(length ts-1), (ss @ ts) ! ((length ss-1)+1)) \<in> NS \<union> S \<or> (ss!0, (ss @ ts) ! ((length ss-1)+1)) \<in> NS \<union> S"
    and "ts\<noteq>[]" and "ss\<noteq>[]" and "length ss>1 \<or> length ts >1"
  shows "({#ss!0,ts!(length ts-1)#},{#(ss @ ts) ! (length ss-1),(ss @ ts) ! (length ss)#})\<in>s_mul_ext NS S"
proof (cases "length ss\<ge>2")
  case True
  then show ?thesis 
    by (metis (no_types, lifting) One_nat_def Suc_1 add_mset_add_single assms(1) assms(2) assms(6) 
        bot_nat_0.not_eq_extremum cancel_comm_monoid_add_class.diff_cancel diff_less le_simps(3) 
        length_greater_0_conv ns_mul_ext_singleton2 nth_append one_same_s_mul_ext s_mul_ext_singleton 
        s_ns_mul_ext_union_compat zero_less_Suc zero_less_diff)
next
  case False
  then show ?thesis
    by (metis (no_types, lifting) Suc_1 assms(2) assms(6) assms(7) bot_nat_0.not_eq_extremum 
        cancel_comm_monoid_add_class.diff_cancel le_simps(3) length_greater_0_conv nth_append 
        one_same_s_mul_ext s_mul_ext_rev s_mul_ext_rev' zero_less_diff)
qed


lemma SN_rstep_R:"SN (rstep R)"
  using rstep_R_S SN_S by (metis SN_on_def) 

lemma derivation_all_ground:
  assumes "ss\<noteq>[] \<and>  is_derivation_of ss (rstep R)"
    and "ground (hd ss) "
  shows "\<forall>i<length ss. ground (ss!i)" using assms 
proof (induction ss)
  case (Cons a ss) 
  then show ?case 
  proof (cases "ss=[]")
    case True
    then show ?thesis using Cons by simp
  next
    case False
    also have "is_derivation_of ss (rstep R)" using Cons cons_subderivation_is_derivation by (metis)
    ultimately have *:"ground (hd ss) \<longrightarrow> (\<forall>i<length ss. ground (ss!i))" using Cons False by simp
    have "((a#ss)!0,(a#ss)!1)\<in>(rstep R)" unfolding is_derivation_of_def using Cons False by auto
    then have "(a,hd ss)\<in>(rstep R)" apply(auto simp add: nth_Cons) using  False  hd_conv_nth by (metis)
    also have "ground a "using Cons.prems(2) by simp
    ultimately have "ground (hd ss)" using TRS2 ground_rstep_ground by metis
    then have "(\<forall>i<length ss. ground (ss!i))" using * by simp
    also note \<open>ground a\<close> ultimately show ?thesis by (rule cons_P)
  qed
qed simp

lemma root_defined:"\<forall>(l,r)\<in>R. \<exists>f ss. l = Fun f ss \<and> (f, length ss) \<in> D"
proof -
  have "\<forall>(l,r)\<in>R. \<exists>f ss. l = Fun f ss \<and> (f, length ss) \<in> defined_funas R" using  TRS1 DC3 rule_defined[of R] by auto
  then show ?thesis using DC1 by blast
qed

lemma root_not_constr:"\<forall>(l,r)\<in>R. \<exists>f ss. l = Fun f ss \<and> (f, length ss)\<notin> C" using root_defined DC3 by blast

lemma basic_match_defined: 
  assumes a1:"basic D C s" 
    and a2:"(l,r)\<in>R \<and> (\<exists>Ctx \<theta>. s = Ctx\<langle>l\<cdot>\<theta>\<rangle>)"    
  shows "\<exists>f ss ts. l = Fun f ts \<and> s = Fun f ss \<and> (f,length ss) \<in>D " 
proof -
  from a1 obtain f ss where es:"s = Fun f ss \<and> (f, length ss) \<in>D \<and> (\<forall>s\<in>set ss. constr C s)" by (meson basic.elims(2))
  from DC1 TRS1 a2 this obtain g ts where el:"l = Fun g ts \<and> (g,length ts)\<in> D" using root_defined by blast
  from this have 1:"\<forall>\<theta>. \<exists>ws. l\<cdot>\<theta> = Fun g ws" by simp
  from a2 obtain u where eu:"u\<unlhd>s \<and> (\<exists>\<theta>. l\<cdot>\<theta> = u) " by auto
  then have 2:"(\<exists>h us. (u = Fun h us \<and> (h, length us) \<in> D)) \<longrightarrow> u = s"
  proof (intro impI)
    assume a:"(\<exists>h us. (u = Fun h us \<and> (h, length us) \<in> D))"
    then have "(\<exists>h\<in>funas_term u. h \<notin> C)" using DC3 by fastforce
    then have "\<not>constr C u " using not_constr by blast
    also have "\<forall>u\<lhd>s. constr C u" using assms(1) DC3 subt_of_basic_constr by blast    
    ultimately show " u = s" using eu by auto
  qed
  from this eu 1 have 3:"\<exists>us. u = Fun g us" by auto
  from this have "\<exists>us. u = Fun g us \<and>(g,length us) \<in>D"
    by (metis Term.term.simps(2) \<open>\<And>thesis. (\<And>g ts. l = Fun g ts \<and> (g, length ts) \<in> D \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> eu length_map eval_term.simps(2))
  from this 2 have "u=s" by auto
  from this 3 es have " f = g" by auto
  from this es el have "l = Fun f ts \<and> s = Fun f ss \<and> (f,length ss) \<in>D" by simp
  from this show ?thesis by simp
qed

lemma basic_constr_subts:
  assumes "basic D C s"
  shows "\<forall>u\<lhd>s. constr C u" using assms 
  by (simp add: DC1 DC2 DC3 subt_of_basic_constr)


lemma basic_context:
  assumes "basic D C (Ctxt\<langle>s\<rangle>)" 
    and "\<exists>f. root s = Some f \<and> f\<in> D"
  shows "Ctxt\<langle>s\<rangle> = s"
proof -
  {
    assume "Ctxt\<langle>s\<rangle>\<noteq> s"
    then have *:"s \<lhd> (Ctxt\<langle>s\<rangle>)" by auto
    have **:"\<forall>f. root s = Some f \<longrightarrow> f\<in>funas_term s" using assms(2) 
      by (metis covered_sig option.inject option.simps(3) root.elims)
    obtain f where "root s = Some f \<and> f\<in>D" using assms by auto
    then have "\<exists>f\<in>funas_term s. f\<notin>C " using ** DC1 DC2 DC3 by auto
    then have "\<not>constr C s" using DC1 DC2 DC3 assms(2) by (metis "**" def_not_constr)
    then have False using basic_constr_subts * assms by auto
  }
  then show ?thesis by auto
qed 


lemma qr_instance:
  assumes a1: "ground_basic D C u"
    and a2: "quasi_reducible D C R"
  shows "\<exists>(l,r)\<in>R. l \<preceq> u"
proof-
  from a1 a2 have 1:"\<exists>(s,t)\<in>(rstep R). s = u" by fastforce
  from this show ?thesis 
  proof -
    from 1 obtain s t where 2:"(s,t)\<in>(rstep R) \<and>  s = u" by auto
    from this a1 obtain l r Ctx \<theta> where 3:"(l,r)\<in>R\<and> (Ctx\<langle>l\<cdot>\<theta>\<rangle>=s  \<and>  Ctx\<langle>r\<cdot>\<theta>\<rangle>= t)" by auto
    from this 2 a1 a2 have "basic D C s" by auto
    from this 3 have lbasic:"basic D C Ctx\<langle>l\<cdot>\<theta>\<rangle>" by auto
    from this 3 have "\<exists>f. Some f = root Ctx\<langle>l\<cdot>\<theta>\<rangle> \<and> f \<in>D" 
      using basic_match_defined by fastforce
    from 2 3 have "\<exists>f. Some f = root (l\<cdot>\<theta>) \<and> f \<in>D"
      using root_defined by auto
    from this lbasic have "l\<cdot>\<theta> = Ctx\<langle>l\<cdot>\<theta>\<rangle>" using basic_context by metis
    from this 3 have "l\<cdot>\<theta> = s" by simp
    from this 2 have "l\<cdot>\<theta> = u" by simp
    from this have "l \<preceq> u" by auto
    from this 3 show ?thesis by auto
  qed
qed

lemma d_c_unrewritable:
  assumes "constr C s"
  shows "s \<in> NF (rstep R)"
proof (rule ccontr)
  assume 1:"s\<notin> NF(rstep R)" 
  from this have "\<exists>t. (s,t)\<in>(rstep R)" by auto
  from this obtain l r where 2:"(l,r)\<in>R \<and> (\<exists>Ctx \<sigma>. Ctx\<langle>l\<cdot>\<sigma>\<rangle>=s)" by blast
  from this DC2 have "\<exists>f\<in>funas_term l. f\<in>D" using root_defined by fastforce
  then have "\<exists>f\<in>funas_term s. f\<in>D" using funas_term_subst 2 by fastforce
  from this DC1 DC2 DC3 have "\<not>(constr C s)" 
    using def_not_constr by metis
  from assms this show "False" by simp
qed

lemma constr_csubst:
  assumes a1:"constr_subst C \<sigma>" and a2:"constr C s" shows "constr C (s\<cdot>\<sigma>)"
proof -  
  from a1 have 1:"\<forall>t\<in>(\<sigma> ` vars_term s). constr C t" using notin_subst_domain_imp_Var by fastforce
  from this have 2:"\<forall>t\<in>(\<sigma> ` vars_term s). \<forall>ft\<in> funas_term t. ft\<in>C" using Basic_Term.constr_funas by blast
  from a2 have 3:"\<forall>ft \<in> funas_term s. ft\<in>C" 
  proof (induction s)
    case (Fun f ss)
    have "funas_term (Fun f ss) = {(f,length ss)}\<union>(\<Union>t\<in>(set ss). funas_term t)" by simp
    have "(f,length ss)\<in> C" using Fun.prems by auto
    thus ?case using Fun.IH Fun.prems by auto
  qed simp
  have "funas_term (s\<cdot>\<sigma>) = funas_term s \<union> \<Union>(funas_term ` \<sigma> ` vars_term s)" using funas_term_subst by auto
  from this and 1 a2 show "constr C (s\<cdot>\<sigma>)" by (metis "2" "3" UN_E UnE constr_funas)
qed



lemma gcsubst:
  assumes a1:"gc_subst C \<sigma>\<^sub>g"
    and a2:"vars_term s\<subseteq> subst_domain \<sigma>\<^sub>g"
    and a3:"basic D C s"
  shows "ground_basic D C (s\<cdot>\<sigma>\<^sub>g)" 
proof - 
  from groundsubst a1 a2 have t1:"ground (s\<cdot>\<sigma>\<^sub>g)" by auto
  from a3 have "\<exists>f ss. (s = Fun f ss) \<and> ((f,length ss)\<in>D) \<and> (\<forall>t\<in>(set ss). constr C t)" by (meson basic.elims(2))
  from this obtain f ss where 1:" (s = Fun f  ss) \<and> ((f,length ss)\<in>D) \<and> (\<forall>t\<in>(set ss). constr C t)" by auto
  from this and a1 have 2:"\<forall>t \<in> set ss. constr C (t\<cdot>\<sigma>\<^sub>g)"  by (simp add: constr_csubst constr_funas gc_subst.elims(2))
  from this and 1 2 have "basic D C(s\<cdot>\<sigma>\<^sub>g)" by simp
  from this and t1 show "ground_basic D C (s\<cdot>\<sigma>\<^sub>g)" by simp
qed


type_synonym ('f,'v) ri_state = "('f,'v) equations \<times> ('f,'v) trs"  
type_synonym ('f,'v) ri_run = "nat \<times> (nat \<Rightarrow> ('f,'v) ri_state)"

definition basic_subts :: "('a,'b) term \<Rightarrow> ('a,'b) term set" 
  where
    "basic_subts t = {s| s. basic D C s \<and> s \<unlhd> t}"  

definition basic_ctxts :: "('a,'b) term \<Rightarrow> ('a,'b) ctxt set" 
  where
    "basic_ctxts t = {Cx| Cx. (\<exists>s. (t = Cx\<langle>s\<rangle>) \<and>  basic D C s) }"  

lemma basic_ctxt_subts: "Cx \<in> basic_ctxts w \<Longrightarrow> \<exists>u. (w = Cx\<langle>u\<rangle>) \<and> u \<in> basic_subts w"
proof -
  assume "Cx \<in> basic_ctxts w"
  then have "\<exists>s. (w = Cx\<langle>s\<rangle>) \<and>  basic D C s" using basic_ctxts_def by auto
  then obtain s where s1: "(w = Cx\<langle>s\<rangle>)" and s2: "basic D C s" by auto
  hence "s \<unlhd> w" using s1 Subterm_and_Context.ctxt_supteq by auto
  then have "s \<in> basic_subts w" using s2 basic_subts_def by auto
  then have "(w = Cx\<langle>s\<rangle>) \<and> s \<in> basic_subts w" using s1 by auto
  then show "\<exists>u. (w = Cx\<langle>u\<rangle>) \<and> u \<in> basic_subts w" by auto 
qed

abbreviation mgu_vd :: "('a, 'b) term \<Rightarrow> ('a, 'b) term \<Rightarrow> _" where "mgu_vd \<equiv> mgu_var_disjoint_generic ren_a ren_b" 

(* RT: changed so that only one unifier is required *)
fun Expd_rename::"('a,'b) ctxt \<Rightarrow> ('a,'b) term \<Rightarrow> ('a,'b) term \<Rightarrow> ('a,'b) trs" where
  "Expd_rename Cx s t = 
      {((Cx \<cdot>\<^sub>c \<sigma>) \<langle>r \<cdot> \<theta>\<rangle>, t \<cdot> \<sigma>) | u \<theta> l r \<sigma>. s = Cx\<langle>u\<rangle> \<and> mgu_vd u l = Some (\<sigma>, \<theta>) \<and> (l,r)\<in>R }" 

inductive_set expand_eq_set::"('a,'b) trs \<Rightarrow> (('a,'b) equation\<times>('a,'b) equations) set" for H 
  where 
    "Cx\<in>basic_ctxts s 
     \<and> (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i)\<in>Expd_rename Cx s t \<longrightarrow> 
                                    (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in>(((rstep H)\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))
     \<Longrightarrow> ((s,t),E')\<in>expand_eq_set H" 

inductive_set simplifyl_eq::"('a,'b) trs \<Rightarrow> ('a,'b) equation rel" for H where
  "(s,s')\<in>rstep (R\<union>H)\<inter>S \<and> (s',s'')\<in>(rstep (H\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<Longrightarrow> ((s,t),(s'',t))\<in>simplifyl_eq H"  

inductive_set simplifyr_eq::"('a,'b) trs \<Rightarrow> ('a,'b) equation rel" for H where
  "(t,t')\<in>rstep (R\<union>H)\<inter>S \<and> (t',t'')\<in>(rstep (H\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<Longrightarrow> ((s,t),(s,t''))\<in>simplifyr_eq H"

inductive_set delete_eq::"('a,'b) trs \<Rightarrow> ('a,'b) equations" for H where
  "(s,t)\<in>(rstep H)^= \<or> (t,s)\<in>(rstep H)^= \<Longrightarrow> (s,t)\<in>delete_eq H"

inductive_set ri_step::"('a,'b) ri_state rel" where 
  expand: "((s,t)\<in>E \<or> (t,s)\<in>E) \<and> ((s,t),E')\<in>expand_eq_set H 
            \<Longrightarrow> (((E,H),((E-{(s,t),(t,s)})\<union>E',H\<union>{(s,t)}))\<in>ri_step)"
| simplifyl: "(s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H
            \<Longrightarrow>  ((E,H),((E-{(s,t)})\<union>{(s'',t)},H))\<in>ri_step"
| simplifyr: "(s,t)\<in>E \<and>((s,t),(s,t''))\<in>simplifyr_eq H 
            \<Longrightarrow>((E,H),((E-{(s,t)})\<union>{(s,t'')},H))\<in>ri_step"
| delete: "(s,t)\<in>E \<and> (s,t)\<in>delete_eq H 
            \<Longrightarrow> ((E,H),(E-{(s,t)},H))\<in>ri_step"    

lemma expand_eq_set:
  "((s,t),E') \<in> expand_eq_set H \<longleftrightarrow> 
    (\<exists>Cx.  Cx\<in>basic_ctxts s \<and> 
    (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx s t \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep H)\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (s\<^sub>i',t\<^sub>i)\<in>E')))"
  using expand_eq_set.cases expand_eq_set.intros by metis

lemma simplifyl_eq:
  "((s,t),(s'',t))\<in>simplifyl_eq H \<longleftrightarrow> (\<exists>s'. (s,s') \<in> (rstep (R\<union>H)\<inter>S) \<and> (s',s'')\<in> (rstep (H\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*)" 
  using simplifyl_eq.cases simplifyl_eq.intros by metis

lemma simplifyr_eq:
  "((s,t),(s,t''))\<in>simplifyr_eq H \<longleftrightarrow> (\<exists>t'. (t,t') \<in> (rstep (R\<union>H)\<inter>S) \<and> (t',t'')\<in> (rstep (H\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*)" 
  using simplifyr_eq.cases simplifyr_eq.intros by metis

lemma delete_eq:
  "(s,t)\<in>delete_eq H\<longleftrightarrow>(s,t)\<in> (rstep H)^= \<or> (t,s)\<in>(rstep H)^=" 
  using delete_eq.cases delete_eq.intros by metis


definition ri_run :: "('a, 'b) ri_run \<Rightarrow> bool" where 
  "ri_run rirun \<equiv> (case rirun of (n,EHi) \<Rightarrow> (\<forall>i < n. (EHi i, EHi (Suc i))\<in>ri_step))"

lemma rirun_ristep :"ri_run (n,EHi) \<Longrightarrow> \<forall>i<n. (EHi i,EHi (Suc i))\<in> ri_step" 
  by (smt case_prod_conv ri_run_def rtrancl_fun_conv)

lemma ristep_rirun : "\<forall>i<n. (EHi i,EHi (Suc i))\<in>ri_step \<Longrightarrow>ri_run(n,EHi)"
proof (induction n)
  case 0
  then show ?case using ri_run_def by simp
next
  case (Suc n)
  then have "ri_run (n,EHi)" using Suc.IH by simp
  then have "\<forall>i<n. (EHi i,EHi(Suc i))\<in>ri_step" using ri_run_def by simp
  then have "(EHi n,EHi (Suc n))\<in>ri_step \<Longrightarrow> ri_run (Suc n,EHi)"
    by (simp add: less_Suc_eq ri_run_def)
  then have "\<forall>i<(Suc n). (EHi i,EHi (Suc i))\<in>ri_step \<Longrightarrow> ri_run (Suc n,EHi)" by simp
  then show ?case
    by (simp add: Suc.prems)
qed

definition full_ri_run::"('a,'b) equations \<Rightarrow> ('a,'b) ri_run \<Rightarrow> bool" 
  where "full_ri_run E rirun \<longleftrightarrow> 
         ri_run rirun \<and> (case rirun of (n,EHi) \<Rightarrow> EHi 0 = (E,{}) \<and> fst (EHi n) = {})"

lemma rgtstar_imp_rstep:
  assumes "(s,t)\<in> Rgestar NS S (rstep R)"
  shows "(s,t)\<in> (rstep R)\<^sup>\<leftrightarrow>\<^sup>*" 
proof - 
  obtain xs where "xs\<noteq>[] \<and> hd xs =s \<and> last xs = t \<and> is_proof_of xs (rstep R) " using assms unfolding Rgestar_def by auto
  then show ?thesis using rtrancl_iff_proof by metis    
qed

definition eqns :: "('a, 'b) ri_state \<Rightarrow> ('a, 'b) equations"
  where "eqns EH \<equiv> fst EH"

definition Einf :: "('a,'b) ri_run \<Rightarrow> ('a,'b)equations"
  where "Einf rirun \<equiv> \<Union>i\<le>(fst rirun). fst (snd rirun i)"

lemma EinEinf:
  assumes "\<exists>i\<le> fst rirun. snd rirun i = (E,H)"
  shows "E \<subseteq> (Einf rirun)" 
proof -
  from assms have "E \<subseteq> (\<Union>i\<le>(fst rirun).fst (snd rirun i))" by fastforce
  from this show ?thesis  by (simp add: Einf_def)
qed   

lemma E\<^sub>0inEinf:
  assumes "EHi 0 = (E\<^sub>0,{})"
  shows "E\<^sub>0 \<subseteq> (Einf (n,EHi))" using EinEinf assms by force

fun fair::"('a, 'b) ri_run \<Rightarrow> bool"
  where "fair rirun= 
    ((\<Union>j\<le>fst rirun. (\<Inter>i\<le>fst rirun. if j\<le>i then fst (snd rirun i) else fst(snd rirun j))) = {})"

lemma expd_prop':
  assumes "Cx \<in> basic_ctxts s"
    and "gc_subst C (\<sigma>\<^sub>g|s vars_term s)"
    and "vars_term s  \<union> vars_term t = subst_domain \<sigma>\<^sub>g"
  shows "(s\<cdot>\<sigma>\<^sub>g,t\<cdot>\<sigma>\<^sub>g)\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
proof -
  obtain u where  uu: "s = Cx\<langle>u\<rangle> \<and> u \<in> basic_subts s" using basic_ctxt_subts using assms(1) by auto 
  then have basic:"basic D C u" using basic_subts_def assms(1) by auto  
  have tdom:"vars_term t\<subseteq> subst_domain \<sigma>\<^sub>g" using assms by auto
  have sdom:"vars_term s\<subseteq> subst_domain \<sigma>\<^sub>g" using assms by auto
  then have us:"vars_term u\<subseteq> vars_term s" using supteq_imp_vars_term_subset uu unfolding basic_subts_def by auto
  then have "u\<cdot>\<sigma>\<^sub>g = u\<cdot>(\<sigma>\<^sub>g|s vars_term s)" using coincidence_lemma' by metis
  also have udom: "vars_term u\<subseteq> subst_domain \<sigma>\<^sub>g" using us sdom by simp
  have udoms:"vars_term u\<subseteq>subst_domain (\<sigma>\<^sub>g|s vars_term s)" using sdom us by simp
  ultimately have gcs:"ground_basic D C (u\<cdot>\<sigma>\<^sub>g)" using basic assms(2) gcsubst[of "\<sigma>\<^sub>g|s vars_term s" u ] by presburger
  from qr_instance[OF gcs RI2] obtain l r where lr: "(l,r) \<in> R" and lu: "l \<preceq> u \<cdot> \<sigma>\<^sub>g" by auto
  from lu obtain \<tau> where "l \<cdot> \<tau> = u \<cdot> \<sigma>\<^sub>g" by (meson subst_instance.cases)
  hence "u \<cdot> \<sigma>\<^sub>g = l \<cdot> \<tau>" by simp
  from mgu_var_disjoint_generic_complete[OF REN this]
  obtain \<tau>' \<sigma>' \<delta> where mgu: "mgu_vd u l = Some (\<sigma>', \<tau>')" 
    and tau: "\<tau> = \<tau>' \<circ>\<^sub>s \<delta>" and sigma: "\<sigma>\<^sub>g = \<sigma>' \<circ>\<^sub>s \<delta>" and eq: "u \<cdot> \<sigma>' = l \<cdot> \<tau>'" 
    by auto
  have expd: "((Cx \<cdot>\<^sub>c \<sigma>')\<langle>r \<cdot> \<tau>'\<rangle>, t \<cdot> \<sigma>') \<in> Expd_rename Cx s t"
    using uu lr mgu by auto
  have "s \<cdot> \<sigma>\<^sub>g = (Cx \<cdot>\<^sub>c \<sigma>' \<cdot>\<^sub>c \<delta>)\<langle>l \<cdot> (\<tau>' \<circ>\<^sub>s \<delta>)\<rangle>" using uu sigma eq by auto
  also have "(\<dots>, (Cx \<cdot>\<^sub>c \<sigma>' \<cdot>\<^sub>c \<delta>)\<langle>r \<cdot> (\<tau>' \<circ>\<^sub>s \<delta>)\<rangle>) \<in> rstep R" using lr by blast
  also have "(Cx \<cdot>\<^sub>c \<sigma>' \<cdot>\<^sub>c \<delta>)\<langle>r \<cdot> (\<tau>' \<circ>\<^sub>s \<delta>)\<rangle> = ((Cx \<cdot>\<^sub>c \<sigma>')\<langle>r \<cdot> \<tau>'\<rangle>) \<cdot> \<delta>" by simp
  finally have Rstep: "(s \<cdot> \<sigma>\<^sub>g, (Cx \<cdot>\<^sub>c \<sigma>')\<langle>r \<cdot> \<tau>'\<rangle> \<cdot> \<delta>) \<in> rstep R" .
  have "((Cx \<cdot>\<^sub>c \<sigma>')\<langle>r \<cdot> \<tau>'\<rangle> \<cdot> \<delta>, t \<cdot> \<sigma>' \<cdot> \<delta>) \<in> rstep (Expd_rename Cx s t)" using expd by blast
  also have "t \<cdot> \<sigma>' \<cdot> \<delta> = t \<cdot> \<sigma>\<^sub>g" unfolding sigma by simp
  finally show ?thesis using Rstep by blast
qed

lemma expd_prop:
  assumes "Cx \<in> basic_ctxts s"
    and "gc_subst C (\<sigma>\<^sub>g|s vars_term s)"
    and "vars_term s  \<union> vars_term t \<subseteq> subst_domain \<sigma>\<^sub>g"
  shows "(s\<cdot>\<sigma>\<^sub>g,t\<cdot>\<sigma>\<^sub>g)\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
proof-
  let ?\<sigma> = "(\<sigma>\<^sub>g|s (vars_term s \<union> vars_term t))" 
  have "vars_term s \<union> vars_term t = subst_domain ?\<sigma>" using assms(3) by auto
  also have "gc_subst C (?\<sigma>|s vars_term s)" using assms(2) by simp
  ultimately have "(s\<cdot>?\<sigma>,t\<cdot>?\<sigma>)\<in>((rstep R) O (rstep (Expd_rename Cx s t)))"
    using expd_prop' assms(1) assms(2) by blast
  also have "s\<cdot>\<sigma>\<^sub>g = s\<cdot>?\<sigma>" "t\<cdot>\<sigma>\<^sub>g = t\<cdot>?\<sigma>" 
    using coincidence_lemma'[of s ] apply simp using coincidence_lemma'[of t] by simp
  ultimately show ?thesis by simp
qed

lemma rstep_star_imp_ex_derivation:
  assumes "(s,t)\<in> R^*"
  shows "\<exists>ss. ss\<noteq>Nil \<and> hd ss = s \<and> last ss = t \<and> is_derivation_of ss R" 
proof -

  let ?s = s
  obtain i where i:"(s,t)\<in>(R^^i)" using assms by auto
  then show ?thesis 
  proof (induction i arbitrary:s)
    case 0
    let ?th = "\<lambda>ss. ss\<noteq>Nil \<and> hd ss = s \<and> last ss = t \<and> is_derivation_of ss R "
    have "(s,t)\<in>Id" using assms i 0 by simp
    then have "s=t" by simp
    then have 01:"hd [s] = s \<and> last [s] = t \<and> [s]\<noteq>[]" by simp
    have "length [s]\<le>1 " by simp
    then have "is_derivation_of [s] R" using zero_derivation by blast
    then have "?th [s]" using 01 by simp
    then show ?case by auto
  next
    case (Suc i)
    let ?th = "\<lambda>ss. ss\<noteq>Nil \<and> hd ss = s \<and> last ss = t \<and> is_derivation_of ss R"
    have "(s,t)\<in>(R^^(Suc i))" using Suc by simp
    then obtain u where u:"(s,u)\<in>R \<and> (u,t)\<in>R^^i" using relpow_Suc_D2 by metis
    then obtain ss where ss:"ss\<noteq>Nil \<and> hd ss = u \<and> last ss = t \<and> is_derivation_of ss R" using Suc by auto
    then have "(s,hd ss)\<in>R" using u by simp
    then have t1:"is_derivation_of (s#ss) R" using u ss cons_is_derivation by metis
    have "(s#ss)\<noteq>Nil \<and> hd (s#ss) = s \<and> last (s#ss) = t" using ss by simp
    then have "?th (s#ss)" using u ss t1 by simp
    then show ?case by auto
  qed
qed    

lemma rstep_plus_imp_ex_derivation:
  assumes "(s,t)\<in>R^+"
  shows "\<exists>ss. ss\<noteq>[] \<and> hd ss = s \<and> last ss = s \<and> is_derivation_of ss R" using assms rstep_star_imp_ex_derivation trancl_into_rtrancl
  by simp


lemma derivation_rstepR_imp_ordered:
  assumes "is_derivation_of ss (rstep R)"
    and "ss \<noteq> Nil"
  shows "\<forall>i<length ss. (hd ss,ss!i)\<in>(NS\<union>S)" 
proof -
  show ?thesis using assms(1)
  proof (induction "length ss" arbitrary:ss)
    case (Suc x)
    then obtain s ss' where ss':"ss = s#ss'" using length_Suc_conv by metis
    then have ss'len:" length ss'=x" using Suc by simp
    have "is_derivation_of ss' (rstep R)" using Suc.prems ss' cons_subderivation_is_derivation by fast
    then have *:"\<forall>i<length ss'. (hd ss',ss'!i)\<in>(NS\<union>S)" using Suc ss'len by simp
    then show ?case 
    proof (cases "ss'=[]")
      case True
      then have *:"ss = [s]" using ss' by simp
      then have **:"hd ss = s " using refl_NS by simp
      have "(s,s)\<in>NS" using refl_NS by (simp add: refl_on_def)
      then show ?thesis using refl_NS * ** by simp
    next
      case False
      then have "(s,hd ss')\<in>(rstep R)" using ss' assms Suc 
        by (metis One_nat_def Suc_eq_plus1 Suc_le_eq diff_Suc_1 is_derivation_of_def length_greater_0_conv nth_Cons_0 second_cons_equal_hd ss'len)
      then have "(s,hd ss')\<in>(NS\<union>S)" using Suc rstep_R_S by simp
      then have "\<forall>i<length ss'. (s,ss'!i)\<in>(NS\<union>S)" using * trans transD by metis
      then have f1:"\<forall>i<length (s#ss'). i\<ge>1 \<longrightarrow> (s,(s#ss')!i)\<in>(NS\<union>S)" using ss' by simp
      have "\<forall>i<length (s#ss'). i<1 \<longrightarrow> (s,(s#ss')!i)\<in>(NS\<union>S)" using refl_NS_S 
        by (metis One_nat_def less_Suc0 local.trans nth_Cons_0 rtrancl.rtrancl_refl trans_refl_imp_rtrancl_id)
      then have "\<forall>i<length (s#ss'). (s,(s#ss')!i)\<in>(NS\<union>S)" using f1 by fastforce
      then show ?thesis using ss' by simp
    qed
  qed simp
qed      



lemma vars_in_notsubstituted:
  "\<forall>v\<in> vars_term t. v\<notin>subst_domain \<sigma> \<longrightarrow> v\<in>vars_term (t\<cdot>\<sigma>)" using notin_subst_domain_imp_Var apply (induction t) apply fastforce by auto

lemma ground_subst_domain_is_vars_term:
  assumes "ground_subst (\<sigma>|s (vars_term s \<union> vars_term t))" and "ground (s\<cdot>\<sigma>) \<and> ground (t\<cdot>\<sigma>)"
  shows "subst_domain (\<sigma>|s (vars_term s \<union> vars_term t)) = (vars_term s \<union> vars_term t)" (is "?l = ?r")
proof 
  show "?l\<subseteq>?r"
  proof -
    have "\<forall>vs \<sigma>. subst_domain (\<sigma>|s vs)\<subseteq> vs"
      using notin_subst_restrict subst_domain_def by fast
    then show ?thesis by fast
  qed
next  
  show "?r \<subseteq>?l"
  proof (rule ccontr)
    assume " \<not> vars_term s \<union> vars_term t \<subseteq> subst_domain (\<sigma> |s (vars_term s \<union> vars_term t))"
    then obtain v where v:"v \<in> vars_term s \<union> vars_term t \<and> v\<notin>subst_domain (\<sigma> |s (vars_term s \<union> vars_term t))" by auto
    then consider "v \<in>vars_term s" | "v \<in>vars_term t" by auto
    then show False
    proof cases
      case 1
      then have "v\<in>vars_term (s\<cdot>(\<sigma> |s (vars_term s \<union> vars_term t)))" using v vars_in_notsubstituted by metis
      then have "\<not>ground (s\<cdot>(\<sigma> |s (vars_term s \<union> vars_term t)))" using ground_vars_term_empty by fast
      then show ?thesis using assms by simp
    next
      case 2
      then have "v\<in>vars_term (t\<cdot>(\<sigma> |s (vars_term s \<union> vars_term t)))" using v vars_in_notsubstituted by metis
      then have "\<not>ground (t\<cdot>(\<sigma> |s (vars_term s \<union> vars_term t)))" using ground_vars_term_empty by fast
      then show ?thesis using assms by simp
    qed
  qed
qed

lemma fair_En_empty_rev:
  assumes "fst (snd rirun (fst rirun)) = {}" 
  shows "fair rirun"
proof -
  let ?n = "fst rirun" let ?E = "\<lambda>n. fst ((snd rirun) n)"
  have "?E ?n  = {}" using assms by auto 
  then have "(\<Inter>i\<le>?n. if ?n\<le>i then ?E i else ?E ?n) = {}" by auto
  then have "(\<Union>j\<le>?n. (\<Inter>i\<le>?n. if j\<le>i then ?E i else ?E j)) = {}" using assms by auto
  thus "fair rirun" by auto
qed

lemma fair_En_empty:
  assumes "fair rirun"
  shows "fst (snd rirun (fst rirun)) = {}" 
proof (rule ccontr)
  let ?n = "fst rirun" let ?E = "\<lambda>n. fst ((snd rirun) n)"
  assume "fst (snd rirun (fst rirun)) \<noteq> {}"
  then obtain st where "st\<in>?E ?n" by auto
  then have "(\<Inter>i\<le>?n. if ?n\<le>i then ?E i else ?E ?n) \<noteq>{}" by auto
  also have "(\<Union>j\<le>?n. (\<Inter>i\<le>?n. if j\<le>i then ?E i else ?E j)) = {}" using assms by simp
  ultimately show "False" using assms by blast
qed

lemma fair_iff:
  "fair rirun \<longleftrightarrow> fst (snd rirun (fst rirun)) = {}"
proof - 
  show ?thesis using fair_En_empty fair_En_empty_rev  by blast
qed

lemma fair_0:
  "fair (0,EHi) \<longleftrightarrow> fst (EHi 0) = {}" by simp


lemma sub_deriv_fair:
  assumes "fair (Suc n,EHi)"
    and "\<forall>i. EHi' i = EHi (i+1)"
  shows "fair (n,EHi')" 
proof -
  have "fst (EHi (Suc n)) = {}" using assms(1) by force
  then have "fst (EHi' n) = {}" using assms(2) by simp
  then show ?thesis by fastforce
qed

lemma all_Suc_conv:
  "\<forall>i\<le>n. i>(j::nat) \<longrightarrow>  P (i+1) \<Longrightarrow> (\<forall>i\<le>Suc n. i>(j+1)\<longrightarrow> P(i))"
  by (metis Suc_eq_plus1 le_Suc_eq' linorder_not_le)

lemma all_Suc_conv':
  "\<forall>j\<le>n. P (j+1) \<Longrightarrow> \<forall>j\<le>Suc n. j>0 \<longrightarrow> P j"
  by (metis Suc_eq_plus1 le_Suc_eq' less_le_not_le)

lemma fair_imp_eliminated:
  assumes "fair rirun"
  shows "\<forall>st\<in>Einf rirun. \<exists>i<(fst rirun). st\<in>(fst ((snd rirun) i)) \<and> (\<forall>j\<le>(fst rirun). j>i \<longrightarrow>st\<notin>(fst ((snd rirun) j)))"
proof -
  obtain n EHi where rirun:"rirun  = (n,EHi)" by fastforce
  then have "fair (n,EHi)" using assms by fast
  then have "\<forall>st\<in>Einf (n,EHi). \<exists>i<(fst (n,EHi)). st\<in>(fst ((snd (n,EHi)) i)) \<and> (\<forall>j\<le>n. j>i\<longrightarrow> st\<notin>(fst ((snd (n,EHi)) j)))"
  proof (induction n arbitrary:EHi)
    case 0
    let ?E = "\<lambda>n. fst (EHi n)" and ?H = "\<lambda>n. snd (EHi n)"
    have "fst (EHi 0) = {}" using 0 by (simp add:fair_0) 
    then have "Einf (0,EHi) = {}" using 0 assms Einf_def by simp
    then show ?case using 0 by simp
  next      
    case (Suc x)
    let ?E = "\<lambda>n. fst (EHi n)"
    obtain EHi' where EHi':"\<forall>i. EHi (i+1) = EHi' i" by fast
    let ?E' = "\<lambda>n. fst (EHi' n)"
    have "fair (x,EHi')" using Suc EHi' by (metis sub_deriv_fair)
    then have h:"\<forall>st\<in>Einf (x,EHi'). \<exists>i<x. st\<in>?E' i \<and> (\<forall>j\<le>x. j>i\<longrightarrow> st\<notin>?E' j)" using Suc by simp
    have "\<forall>st\<in>Einf (Suc x, EHi). \<exists>i<Suc x. st\<in>?E i \<and> (\<forall>j\<le>Suc x. j>i \<longrightarrow> st\<notin>?E j)"
    proof (rule ballI)
      fix st assume a:"st\<in>Einf (Suc x, EHi)"
      then show "\<exists>i<Suc x. st\<in>?E i \<and> (\<forall>j\<le>Suc x. j>i \<longrightarrow>st\<notin>?E j)" 
      proof (cases "st\<in>Einf (x,EHi')")
        case True
        then have "\<exists>i<x. st\<in>?E' i \<and> (\<forall>j\<le>x. j>i \<longrightarrow> st\<notin>?E' j)" using h by simp
        then have "\<exists>i<x. st\<in>?E (i+1) \<and> (\<forall>j\<le>x. j>i\<longrightarrow> st\<notin>?E (j+1))" using EHi' by auto
        then obtain i where i:"i<x \<and> st\<in>?E (i+1) \<and> (\<forall>j\<le>x. j>i \<longrightarrow> st\<notin>?E (j+1))" by auto
        then have "(i+1)<Suc x" "st\<in>?E (i+1)" "(\<forall>j\<le>Suc x. j>(i+1) \<longrightarrow>st\<notin>?E j)" apply (simp,simp) using i apply (intro all_Suc_conv) by simp
        then show ?thesis by auto
      next
        case False  
        then have "\<forall>j\<le>x. st\<notin>?E' j" using Einf_def by simp
        then have "\<forall>j\<le>x. st\<notin>?E (j+1)" using EHi' by simp
        then have "\<forall>j\<le>Suc x. j>0 \<longrightarrow>st\<notin>?E j" by (rule all_Suc_conv')
        also then have "st\<in>?E 0" using a False Einf_def by auto
        ultimately show ?thesis by auto
      qed
    qed
    then show ?case by simp
  qed
  then show ?thesis using rirun by simp
qed


lemma ri_step_cases:
  "((E,H),(E',H'))\<in>ri_step \<longleftrightarrow>
              (\<exists>s t. (\<exists>E''. ((s,t)\<in>E\<or> (t,s)\<in>E) \<and> ((s,t),E'')\<in>expand_eq_set H \<and> E' = (E-{(s,t),(t,s)})\<union>E'' \<and> H' = H\<union>{(s,t)}) \<or>
              ((\<exists>s''. (s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = (E-{(s,t)})\<union>{(s'',t)}) \<and> H' = H) \<or>
              ((\<exists>t''. (s,t)\<in>E \<and> ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = (E-{(s,t)})\<union>{(s,t'')}) \<and> H' = H) \<or> 
              ((s,t)\<in>E\<and> (s,t)\<in>delete_eq H \<and> E' = E- {(s,t)} \<and>  H' = H))" (is "?l \<longleftrightarrow>?r")
proof
  assume ?r
  then obtain s t where "(\<exists>E''. ((s,t)\<in>E\<or> (t,s)\<in>E) \<and> ((s,t),E'')\<in>expand_eq_set H \<and> E' = (E-{(s,t),(t,s)})\<union>E'' \<and> H' = H\<union>{(s,t)}) \<or>
              ((\<exists>s''. (s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = (E-{(s,t)})\<union>{(s'',t)}) \<and> H' = H) \<or>
              ((\<exists>t''. (s,t)\<in>E \<and> ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = (E-{(s,t)})\<union>{(s,t'')}) \<and> H' = H) \<or> 
              ((s,t)\<in>E\<and> (s,t)\<in>delete_eq H \<and> E' = E- {(s,t)} \<and>  H' = H)" by force
  then consider " (\<exists> E''. ((s,t)\<in>E\<or> (t,s)\<in>E) \<and> ((s,t),E'')\<in>expand_eq_set H \<and> E' = (E-{(s,t),(t,s)})\<union>E'' \<and> H' = H\<union>{(s,t)})"|
    "  ((\<exists>s''. (s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = (E-{(s,t)})\<union>{(s'',t)}) \<and> H' = H)"|
    "  ((\<exists> t''. (s,t)\<in>E \<and> ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = (E-{(s,t)})\<union>{(s,t'')}) \<and> H' = H)"|
    "  ((s,t)\<in>E\<and> (s,t)\<in>delete_eq H \<and> E' = E- {(s,t)} \<and>  H' = H)" by fast
  then show ?l
  proof cases
    case 1
    then show ?l using ri_step.expand by blast
  next
    case 2
    then obtain s t s'' where st:"(s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = (E-{(s,t)})\<union>{(s'',t)} \<and> H' = H" by blast
    then show ?l using ri_step.simplifyl by metis
  next
    case 3
    then obtain s t t'' where st:"(s,t)\<in>E \<and> ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = (E-{(s,t)})\<union>{(s,t'')} \<and> H' = H" by blast
    then show ?l using ri_step.simplifyr by metis
  next
    case 4
    then obtain s t where st:"(s,t)\<in>E \<and> (s,t)\<in>delete_eq H \<and> E' = E- {(s,t)} \<and>  H' = H" by blast
    then show ?l using ri_step.delete by metis
  qed
next
  assume l:?l 
  then show ?r 
    by (cases rule: ri_step.cases, metis, auto) 
qed    

lemma rirun_H_expanding:
  assumes "ri_run rirun" 
  shows "\<forall>i< fst rirun. \<forall>j<i. snd (snd rirun j)\<subseteq> snd (snd rirun i)"
proof (intro allI impI)
  let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
  fix i assume a:"i< fst rirun" fix j assume b:"j<i"
  then show "?H j\<subseteq> ?H i" using a 
  proof (induction i)
    case (Suc i)
    then have "j < Suc i" by simp
    then have *:"?H j \<subseteq>?H i"
    proof (cases "j<i")
      case True
      then show ?thesis using Suc by simp
    next
      case False
      then have "j = i" using Suc by simp
      then show ?thesis by simp
    qed
    also have "((?E i,?H i),(?E (i+1),?H (i+1))) \<in>ri_step " using Suc.prems  assms(1) ri_run_def[of rirun] by auto
    then obtain s t where 
      "((\<exists>E''. ((s, t) \<in> (?E i) \<or> (t, s) \<in> (?E i)) \<and> ((s, t), E'') \<in> expand_eq_set (?H i) \<and> 
                    (?E (i+1)) = (?E i) - {(s, t), (t, s)} \<union> E'' \<and> (?H (i+1)) = (?H i) \<union> {(s, t)})) \<or>
           ((\<exists>s''. (s, t) \<in> (?E i) \<and> ((s, t), s'', t) \<in> simplifyl_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<union> {(s'', t)}) \<and> (?H (i+1)) = (?H i)) \<or>
           ((\<exists>t''. (s, t) \<in> (?E i) \<and> ((s, t), s, t'') \<in> simplifyr_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<union> {(s, t'')}) \<and> (?H (i+1)) = (?H i)) \<or>
           ((s, t) \<in> (?E i) \<and> (s, t) \<in> delete_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<and> (?H (i+1)) = (?H i))" 
      using ri_step_cases[of "?E i" "?H i" "?E (i+1)" "?H (i+1)"] by force
    then consider "((\<exists>E''. ((s, t) \<in> (?E i) \<or> (t, s) \<in> (?E i)) \<and> ((s, t), E'') \<in> expand_eq_set (?H i) \<and> 
                    (?E (i+1)) = (?E i) - {(s, t), (t, s)} \<union> E'' \<and> (?H (i+1)) = (?H i) \<union> {(s, t)})) "|
      "((\<exists>s''. (s, t) \<in> (?E i) \<and> ((s, t), s'', t) \<in> simplifyl_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<union> {(s'', t)}) \<and> (?H (i+1)) = (?H i)) \<or>
           ((\<exists>t''. (s, t) \<in> (?E i) \<and> ((s, t), s, t'') \<in> simplifyr_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<union> {(s, t'')}) \<and> (?H (i+1)) = (?H i)) \<or>
           ((s, t) \<in> (?E i) \<and> (s, t) \<in> delete_eq (?H i) \<and> (?E (i+1)) = (?E i) - {(s, t)} \<and> (?H (i+1)) = (?H i))" by fast
    then show ?case
    proof cases
      case 1
      then have "?H i \<subseteq> ?H (i+1)" by blast
      then show ?thesis using * by simp
    next
      case 2
      then have "?H i = ?H (i+1)" by auto
      then show ?thesis using * by simp
    qed
  qed simp
qed


lemma rirun_H_subset_Einf:
  assumes "snd (snd rirun 0) = {}" and "ri_run rirun"
  shows "\<forall>i\<le> fst rirun. (snd (snd rirun i))\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow>"
proof (intro allI impI)
  let ?n = "fst rirun" let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
  fix i assume "i\<le>fst rirun"
  then show "(?H i)\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow>"
  proof (induction i)
    case 0
    then show ?case using assms by simp
  next
    case (Suc x)
    then have "((?E x,?H x),(?E (Suc x),?H (Suc x)))\<in>ri_step" using assms(2) ri_run_def by auto
    then have "(\<exists>s t. (\<exists>E''. ((s,t)\<in>(?E x)\<or> (t,s)\<in>(?E x)) \<and> ((s,t),E'')\<in>expand_eq_set (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t),(t,s)})\<union>E'' \<and> (?H (x+1)) = (?H x)\<union>{(s,t)}) \<or>
                ((\<exists>s''. (s,t)\<in>(?E x) \<and> ((s,t),(s'',t))\<in>simplifyl_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s'',t)}) \<and> (?H (x+1)) = (?H x)) \<or>
                ((\<exists>t''. (s,t)\<in>(?E x) \<and> ((s,t),(s,t''))\<in>simplifyr_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s,t'')}) \<and> (?H (x+1)) = (?H x)) \<or> 
                ((s,t)\<in>(?E x)\<and> (s,t)\<in>delete_eq (?H x) \<and> (?E (x+1)) = (?E x)- {(s,t)} \<and>  (?H (x+1)) = (?H x)))" 
      using ri_step_cases[of "?E x" "?H x" "?E (x+1)" "?H (x+1)"] by simp
    then obtain s t where "(\<exists>E''. ((s,t)\<in>(?E x)\<or> (t,s)\<in>(?E x)) \<and> ((s,t),E'')\<in>expand_eq_set (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t),(t,s)})\<union>E'' \<and> (?H (x+1)) = (?H x)\<union>{(s,t)}) \<or>
                ((\<exists>s''. (s,t)\<in>(?E x) \<and> ((s,t),(s'',t))\<in>simplifyl_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s'',t)}) \<and> (?H (x+1)) = (?H x)) \<or>
                ((\<exists>t''. (s,t)\<in>(?E x) \<and> ((s,t),(s,t''))\<in>simplifyr_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s,t'')}) \<and> (?H (x+1)) = (?H x)) \<or> 
                ((s,t)\<in>(?E x)\<and> (s,t)\<in>delete_eq (?H x) \<and> (?E (x+1)) = (?E x)- {(s,t)} \<and>  (?H (x+1)) = (?H x))" by force
    then consider"(\<exists>E''. ((s,t)\<in>(?E x)\<or> (t,s)\<in>(?E x)) \<and> ((s,t),E'')\<in>expand_eq_set (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t),(t,s)})\<union>E'' \<and> (?H (x+1)) = (?H x)\<union>{(s,t)})"|
      "((\<exists>s''. (s,t)\<in>(?E x) \<and> ((s,t),(s'',t))\<in>simplifyl_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s'',t)}) \<and> (?H (x+1)) = (?H x))"|
      "((\<exists>t''. (s,t)\<in>(?E x) \<and> ((s,t),(s,t''))\<in>simplifyr_eq (?H x) \<and> (?E (x+1)) = ((?E x)-{(s,t)})\<union>{(s,t'')}) \<and> (?H (x+1)) = (?H x))"| 
      "((s,t)\<in>(?E x)\<and> (s,t)\<in>delete_eq (?H x) \<and> (?E (x+1)) = (?E x)- {(s,t)} \<and>  (?H (x+1)) = (?H x))" by fast
    then show ?case 
    proof cases
      case 1
      then have *:"?H (x+1) =  (?H x)\<union>{(s,t)}" by auto
      also have "(s,t)\<in>?E x\<or> (t,s)\<in>?E x" using 1 by simp
      then have "(s,t)\<in>Einf rirun \<or> (t,s)\<in>Einf rirun" using Suc.prems Einf_def by auto
      ultimately have "(?H x)\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow> \<and> {(s,t)}\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow>" using Suc by auto
      then show ?thesis using * by auto
    next
      case 2
      then have "?H x = ?H(x+1)" by simp
      then show ?thesis using Suc by simp
    next
      case 3
      then have "?H x = ?H(x+1)" by simp
      then show ?thesis using Suc by simp
    next
      case 4
      then have "?H x = ?H(x+1)" by simp
      then show ?thesis using Suc by simp
    qed
  qed
qed    

lemma rirun_H_subset_Einf_rstep:
  assumes "snd (snd rirun 0) = {}" and "ri_run rirun"
  shows "\<forall>i\<le>fst rirun. (rstep (snd (snd rirun i)))\<^sup>\<leftrightarrow>\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" 
proof -
  have "\<forall>i\<le>fst rirun.  (snd (snd rirun i))\<^sup>\<leftrightarrow>\<subseteq>  (Einf rirun)\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf assms by simp
  then have "\<forall>i\<le>fst rirun.  rstep ((snd (snd rirun i))\<^sup>\<leftrightarrow>)\<subseteq> rstep ((Einf rirun)\<^sup>\<leftrightarrow>)" by fast
  then show ?thesis using rstep_simps(5) by metis
qed

lemma ri_step_eq_cases:
  assumes"(s,t)\<in>E" and "(s,t)\<notin>E'"
    and "((E,H),(E',H'))\<in>ri_step"
  shows "((\<exists>E''. (((t,s),E'')\<in>expand_eq_set H \<or> ((s,t),E'')\<in>expand_eq_set H)\<and> E' = E - {(s,t),(t,s)} \<union> E'') \<or> 
          (\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = E- {(s,t)}\<union>{(s'',t)}) \<or> 
          (\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = E- {(s,t)}\<union>{(s,t'')}) \<or>
          ((s,t)\<in>delete_eq H \<and> E' = E - {(s,t)}))"
proof -
  let ?e ="\<lambda> s t. (\<exists>E''. ((s,t)\<in>E\<or> (t,s)\<in>E) \<and> ((s,t),E'')\<in>expand_eq_set H \<and> E' = (E-{(s,t),(t,s)})\<union>E'' \<and> H' = H\<union>{(s,t)})"
  let ?sl = "\<lambda>s t.((\<exists>s''. (s,t)\<in>E \<and> ((s,t),(s'',t))\<in>simplifyl_eq H \<and> E' = (E-{(s,t)})\<union>{(s'',t)}) \<and> H' = H)"
  let ?sr = "\<lambda>s t.((\<exists>t''. (s,t)\<in>E \<and> ((s,t),(s,t''))\<in>simplifyr_eq H \<and> E' = (E-{(s,t)})\<union>{(s,t'')}) \<and> H' = H)"
  let ?d = "\<lambda>s t.((s,t)\<in>E\<and> (s,t)\<in>delete_eq H \<and> E' = E- {(s,t)} \<and>  H' = H)"
  have "\<exists>s' t'. ?e s' t' \<or> ?sl s' t' \<or> ?sr s' t' \<or> ?d s' t'" using ri_step_cases[of "E" "H" "E'" "H'"] assms(3) by simp
  then obtain s' t' where "?e s' t' \<or> ?sl s' t' \<or> ?sr s' t' \<or> ?d s' t'" by force
  then consider "?e s' t'" | " ?sl s' t'" |"?sr s' t'" |"?d s' t'" by fast
  then show ?thesis 
  proof cases
    case 1
    then have "(s,t)\<in>{(s',t'),(t',s')}" using assms(1) assms(2) by fast
    then have "(s = s' \<and> t= t') \<or> (s = t' \<and> t= s')" by fast
    then have "\<exists>E''. (((t,s),E'')\<in>expand_eq_set H \<or> ((s,t),E'')\<in>expand_eq_set H)\<and> E' = E - {(s,t),(t,s)} \<union> E''" using 1 by auto
    then show ?thesis using 1 by blast
  next
    case 2
    then have "(s,t)\<notin>(E-{(s',t')})" using assms(2) by auto
    then have "(s,t) = (s',t')" using assms(1) by simp
    then show ?thesis using 2 by auto
  next
    case 3
    then have "(s,t)\<notin>(E-{(s',t')})" using assms(2) by fast
    then have "(s,t) = (s',t')" using assms(1) by simp
    then show ?thesis using 3 by auto
  next
    case 4
    then have "(s,t)\<notin>E - {(s',t')}" using assms(2) by fast
    then have "(s,t) \<in>{(s',t')}" using assms(1) by simp
    then show ?thesis using 4 by simp
  qed
qed

lemma Einf_eq_cases:
  assumes "fair rirun" and "ri_run rirun"
  shows "\<forall>(s,t)\<in>Einf rirun. \<exists>i<(fst rirun).  
          (\<exists>E'. (((t,s),E')\<in>expand_eq_set (snd((snd rirun) i)) \<or> ((s,t),E')\<in>expand_eq_set (snd ((snd rirun) i))) 
                  \<and> fst (snd rirun (i+1)) = fst (snd rirun i) - {(s,t),(t,s)} \<union> E') \<or>
          (\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq (snd ((snd rirun) i)) \<and> (fst ((snd rirun) (i+1))) = (fst ((snd rirun) i))- {(s,t)} \<union>{(s'',t)} ) \<or> 
          (\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq (snd ((snd rirun) i)) \<and> (fst ((snd rirun) (i+1))) = (fst ((snd rirun) i))- {(s,t)} \<union>{(s,t'')} ) \<or>
          ((s,t)\<in>delete_eq (snd ((snd rirun) i))\<and> (fst ((snd rirun) (i+1))) = (fst ((snd rirun) i)-{(s,t)}))"  
proof -
  let ?n = "fst rirun" let ?E = "\<lambda>i. fst (snd rirun i)" and ?H = "\<lambda>i. snd (snd rirun i)" and ?EH = "\<lambda>i. snd rirun i"
  let ?th = "\<lambda> s t i.   
          (\<exists>E'. (((t,s),E')\<in>expand_eq_set (?H i) \<or> ((s,t),E')\<in>expand_eq_set (?H i)) \<and> 
                  ?E (i+1) = ?E i - {(s,t),(t,s)} \<union> E')  \<or>
          (\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq (?H i) \<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s'',t)} ) \<or> 
          (\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq (?H i) \<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s,t'')}) \<or>
          ((s,t)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(s,t)})"
  {
    fix s t assume st:"(s,t)\<in>Einf rirun"
    then obtain i where i:"i<?n \<and> (s,t)\<in>(fst ((snd rirun) i)) \<and> (\<forall>j\<le>(fst rirun). j>i \<longrightarrow>(s,t)\<notin>(fst ((snd rirun) j)))" 
      using assms fair_imp_eliminated by fast
    then have ristepi:"(?EH i,?EH (i+1))\<in>ri_step" using assms(2) ri_run_def by auto
    also have "(s,t)\<in>?E i \<and> (s,t)\<notin>?E(i+1)" using i by simp
    ultimately have "?th s t i" using ri_step_eq_cases[of "s" "t" "?E i" "?E(i+1)" "?H i" "?H (i+1)"] by auto
    then have "\<exists>i<?n. ?th s t i" using i by meson
  }
  then show ?thesis by force
qed


lemma rtrancl_closed_ctxt_subst:
  assumes "\<forall>(s,t)\<in>A. (Ctx\<langle>s\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<theta>\<rangle>)\<in>A "
  shows "(s,t)\<in>A^* \<longrightarrow> (Ctx\<langle>s\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<theta>\<rangle>)\<in>A^*" 
  using rtrancl_map[of A "\<lambda> t. Ctx\<langle>t\<cdot>\<theta>\<rangle>" A s t] assms by blast

lemma all_H_eq_expanded:
  assumes "ri_run rirun" "snd (snd rirun 0) = {}" 
  shows "\<forall>i<fst rirun. \<forall>(s,t)\<in>snd (snd rirun i). 
          (\<exists>j<i. \<exists>E'. fst (snd  rirun (j+1)) = fst (snd rirun j)-{(s,t),(t,s)}\<union>E' 
                        \<and> snd (snd rirun (j+1)) = snd (snd rirun j)\<union>{(s,t)} \<and> ((s,t),E')\<in>expand_eq_set (snd (snd rirun j)))"
proof -
  let ?n = "fst rirun" let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
  {
    fix i s' t' assume a:"i<?n" "(s',t')\<in> ?H i"
    have "\<forall>j<i. ?H j \<subseteq> ?H i" using rirun_H_expanding[of rirun] a(1) assms(1) by simp
    have "\<exists>j<i. (s',t')\<notin>?H j \<and> (s',t')\<in> ?H (j+1)" using a 
    proof (induction i)
      case 0
      then show ?case using assms(2) by simp
    next
      case (Suc i)
      then show ?case
      proof (cases " (s', t') \<in> snd (snd rirun i)")
        case True
        also have "i<?n" using Suc by simp  
        ultimately have "\<exists>j<i. (s', t') \<notin> snd (snd rirun j) \<and> (s', t') \<in> snd (snd rirun (j + 1))" using Suc.IH by blast
        moreover have "\<forall>j<i. j< Suc i" by simp
        ultimately show ?thesis by blast
      next
        case False
        then have "(s', t') \<notin> snd (snd rirun i) \<and> (s', t') \<in> snd (snd rirun (i + 1))" using Suc by simp
        also have "\<forall>j\<le>i. j\<le> Suc i" by simp
        ultimately show ?thesis by blast
      qed
    qed
    then obtain j where j:"j<i\<and> (s',t')\<notin>?H j \<and> (s',t')\<in> ?H (j+1)" by auto
    then have "((?E j,?H j),?E(j+1),?H(j+1))\<in> ri_step " using assms(1) a ri_run_def by auto
    then obtain s t
      where "(\<exists>E''. ((s, t) \<in> (?E j) \<or> (t, s) \<in> (?E j)) \<and> ((s, t), E'') \<in> expand_eq_set (?H j) \<and> 
                (?E (j+1)) = (?E j) - {(s, t), (t, s)} \<union> E'' \<and> (?H (j+1)) = (?H j) \<union> {(s, t)}) \<or>
           (\<exists>s''. (s, t) \<in> (?E j) \<and> ((s, t), s'', t) \<in> simplifyl_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<union> {(s'', t)}) \<and> (?H (j+1)) = (?H j) \<or>
           (\<exists>t''. (s, t) \<in> (?E j) \<and> ((s, t), s, t'') \<in> simplifyr_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<union> {(s, t'')}) \<and> (?H (j+1)) = (?H j) \<or>
           (s, t) \<in> (?E j) \<and> (s, t) \<in> delete_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<and> (?H (j+1)) = (?H j)" 
      using ri_step_cases[of "?E j" "?H j" "?E (j+1)" "?H (j+1)"] by force
    then consider "(\<exists>E''. ((s, t) \<in> (?E j) \<or> (t, s) \<in> (?E j)) \<and> ((s, t), E'') \<in> expand_eq_set (?H j) \<and> 
                (?E (j+1)) = (?E j) - {(s, t), (t, s)} \<union> E'' \<and> (?H (j+1)) = (?H j) \<union> {(s, t)})"|
      "(\<exists>s''. (s, t) \<in> (?E j) \<and> ((s, t), s'', t) \<in> simplifyl_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<union> {(s'', t)}) \<and> (?H (j+1)) = (?H j) \<or>
           (\<exists>t''. (s, t) \<in> (?E j) \<and> ((s, t), s, t'') \<in> simplifyr_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<union> {(s, t'')}) \<and> (?H (j+1)) = (?H j) \<or>
           (s, t) \<in> (?E j) \<and> (s, t) \<in> delete_eq (?H j) \<and> (?E (j+1)) = (?E j) - {(s, t)} \<and> (?H (j+1)) = (?H j)" by fast
    then have "\<exists>j<i. \<exists>E'.  ((s',t'),E')\<in>expand_eq_set (?H j) \<and> ?E (j+1) = ?E j-{(s',t'),(t',s')}\<union>E' \<and> ?H (j+1) = ?H j\<union>{(s',t')}"
    proof cases
      case 1
      then obtain E'' where E'':"((s, t) \<in> (?E j) \<or> (t, s) \<in> (?E j)) \<and> ((s, t), E'') \<in> expand_eq_set (?H j) \<and> 
              (?E (j+1)) = (?E j) - {(s, t), (t, s)} \<union> E'' \<and> (?H (j+1)) = (?H j) \<union> {(s, t)}" by presburger
      then have H:"?H (j+1) = ?H j \<union> {(s,t)}" by fast
      have sts't':"(s,t) = (s',t')"
      proof (cases "(s,t)\<in>?H j")
        case True
        then have "?H (j+1) = ?H j" using H by blast
        then show ?thesis using j by argo
      next
        case False
        then have *:"\<forall>(x,y)\<in>?H (j+1). (x,y)\<noteq>(s,t) \<longrightarrow>(x,y)\<in>?H j" using H by blast
        show ?thesis 
        proof (rule ccontr)
          assume "(s, t) \<noteq> (s', t')"
          also have "(s',t')\<in>?H (j+1)" using j by fastforce
          ultimately also have "(s',t')\<in>?H j" using * by fastforce
          ultimately show False using j by blast
        qed
      qed
      then have " ((s', t'), E'') \<in> expand_eq_set (?H j)" using E'' by force
      then show ?thesis using j E'' by auto
    next
      case 2
      then have "?H (j+1) = ?H j" by auto
      then show ?thesis using j by simp
    qed
  }
  then show ?thesis 
    by fastforce
qed


lemma expand_r1r2_case:
  assumes "(s,s1)\<in>rstep R" "(s1,s2)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(s2,t)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" "ground s" "ground t"
  shows "(s,t)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
proof -
  let ?R1 = "rstep R" let ?R2 = "rstep (Einf rirun)" 
  have *:"(\<exists>xs.  xs\<noteq>[]  \<and> hd xs = s \<and> last xs = t \<and> 
            is_proof_of xs (?R1\<union>?R2) \<and>
            (\<forall>i<length xs .  (s,(xs!i))\<in>(NS\<union>S) \<or> (t,(xs!i))\<in>NS\<union>S) \<and> (\<forall>i<length xs .  (xs!i)\<in>ground_terms) \<and>
            (\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S)) \<longrightarrow> ?thesis" by simp
  obtain ss where ss:" ss\<noteq>[]  \<and> hd ss = s1 \<and> last ss = s2 \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
    using assms(2) rtrancl_iff_derivation[of s1 s2 "(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))"] by blast

  let ?xs = "s#ss@[t]"
  have t1:" ?xs\<noteq>[]  \<and> hd ?xs = s \<and> last ?xs = t " by simp
  have t2:"is_proof_of ?xs (?R1\<union>?R2)" 
  proof -
    have "\<forall>i<length ss - 1. (ss ! i, ss ! (i+1)) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" using ss is_derivation_of_def[of ss "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by simp
    then have "\<forall>i<length ss - 1. case (ss ! i, ss ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by blast
    also have "\<forall>i<length [t] - 1. case ([t] ! i, [t] ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by simp
    moreover have " case (last ss, hd [t]) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(3) ss by fastforce
    moreover have " case (s, hd ss) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) ss by simp
    moreover have "ss\<noteq>[]" "[t]\<noteq>[]" using ss by auto 
    ultimately have "\<forall>i<length (s # ss @ [t]) - 1. case ((s # ss @ [t]) ! i, (s # ss @ [t]) ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" 
      using app_Cons_P_sublemma[of ss "\<lambda>(x,y). (x,y)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow>" "[t]" s] by fastforce
    then show ?thesis by simp
  qed
  have t3:"(\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S)"
  proof -
    have "\<forall>x t. (s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (s,t)\<in>S"
    proof (intro allI impI)
      fix x t assume a:"(s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"
      then have t:"(x,t)\<in>(NS\<union>S)" by simp
      then show "(s,t)\<in>S" 
      proof (cases "(x,t)\<in>S")
        case True
        then show ?thesis using trans_S transD[of S s x t ] a by simp
      next
        case False
        then have "(x,t)\<in>NS" using t by simp
        then have "(s,t)\<in>S O NS " using a by auto
        then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
      qed
    qed
    also have "(s, hd ss)\<in>S" using assms(1) rstep_R_S ss by simp
    ultimately have S:"\<forall>i<length ss. (s,ss!i)\<in>S" 
      using  derivation_propagation[of "\<lambda>x. (s,x)\<in>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by argo
    then have "\<forall>x\<in>set ss. (s,x)\<in>S" using all_set_conv_all_nth[of ss] by simp
    then have "\<forall>x\<in>set ss. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)" by simp
    also have "(s,s)\<in>(NS\<union>S)" using refl_NS_S refl_onD[of UNIV "NS\<union>S" s ] by simp
    moreover have "(t,t)\<in>(NS\<union>S)" using refl_NS_S refl_onD[of UNIV "NS\<union>S" t ] by simp
    ultimately have "\<forall>x\<in>set ?xs. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)" by auto
    then show ?thesis using all_set_conv_all_nth[of ?xs "\<lambda>x. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)"] by blast
  qed
    (*****************************************************************************)
  have t4:"(\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms)"
  proof - 
    have "ground s" using assms(4) by simp
    also have "(s,s1)\<in>S" using rstep_R_S assms(1) by simp
    moreover 
    {
      have "is_derivation_of ss (NS\<union>S)" using ss by auto
      then have "\<forall>i<length ss. (s1,ss!i)\<in>(NS\<union>S)^*" using derivation_hd_nth_rtrancl[of ss "NS\<union>S"] ss by meson
    }
    ultimately have "\<forall>i<length ss. ground (ss!i)" using ground_NS_S_rtrancl[of s s1] by blast
    then have "\<forall>x\<in>set ss. ground x" using all_set_conv_all_nth[of ss ground] by blast
    then have "\<forall>x\<in>set (s#ss@[t]). ground x" using assms(4) assms(5) by simp
    then show ?thesis using all_set_conv_all_nth[of ?xs ground] by force
  qed
    (*****************************************************************************)
  have t5:"\<forall>i<length ?xs -1. (?xs!i,?xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S"
  proof -
    have "\<forall>x t. (s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (s,t)\<in>S"
    proof (intro allI impI)
      fix x t assume a:"(s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"
      then have t:"(x,t)\<in>(NS\<union>S)" by simp
      then show "(s,t)\<in>S" 
      proof (cases "(x,t)\<in>S")
        case True
        then show ?thesis using trans_S transD[of S s x t ] a by simp
      next
        case False
        then have "(x,t)\<in>NS" using t by simp
        then have "(s,t)\<in>S O NS " using a by auto
        then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
      qed
    qed
    also have "(s, hd ss)\<in>S" using assms(1) rstep_R_S ss by simp
    ultimately have S:"\<forall>i<length ss. (s,ss!i)\<in>S" 
      using  derivation_propagation[of "\<lambda>x. (s,x)\<in>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by argo
    then have "\<forall>i<length ss-1. ({#s,t#},{#ss!i, ss!(i+1)#})\<in>s_mul_ext NS S" using stricts_s_mul_ext by force
    then have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<notin>?R1 \<longrightarrow> ({#s,t#},{#ss!i, ss!(i+1)#})\<in>s_mul_ext NS S" by simp
    also have "(s,hd ss)\<notin>(?R1) \<longrightarrow>({#s,t#},{#s, hd ss#}) \<in>s_mul_ext NS S" using assms(1) ss by force
    moreover have "(s,last ss)\<in>S" using S ss last_conv_nth[of ss] by simp
    then have "({#s,t#},{#last ss,t#})\<in>s_mul_ext NS S" using one_same_s_mul_ext by simp
    then have "(last ss,t)\<notin>?R1 \<longrightarrow> ({#s,t#},{#last ss,t#})\<in>s_mul_ext NS S" by simp
    moreover have "ss\<noteq>[]" "[t] \<noteq>[]" using ss by auto
    ultimately show ?thesis using app_Cons_P_sublemma[of ss "\<lambda>(x,y). (x,y)\<notin>?R1 \<longrightarrow>({#s,t#},{#x,y#})\<in>s_mul_ext NS S" "[t]" s] by force
  qed
  then have "?xs\<noteq>[]  \<and> hd ?xs = s \<and> last ?xs = t \<and> 
            is_proof_of ?xs (?R1\<union>?R2) \<and>
            (\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S) \<and> (\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms) \<and>
            (\<forall>i<length ?xs -1. (?xs!i,?xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S)" using t1 t2 t3 t4 by simp
  then show ?thesis using * by blast
qed      

lemma expand_r1r2_case':
  assumes "(s,s1)\<in>rstep R" "(s1,s2)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(s2,t1)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" "ground s" "ground t1" and "(s,t1)\<in>S"
  shows "\<exists>xs. xs \<noteq> [] \<and>
               hd xs =s \<and>
               last xs = t1 \<and>
               is_proof_of xs (rstep R \<union> rstep (Einf rirun)) \<and>
               (\<forall>i<length xs. (s, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) \<and>
               (\<forall>i<length xs. xs ! i \<in> ground_terms) \<and>
               (\<forall>i<length xs - 1.
               (xs ! i, xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
                   ({#s, t#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext NS S)"
proof -
  let ?R1 = "rstep R" let ?R2 = "rstep (Einf rirun)" 
  have *:"(\<exists>xs.  xs\<noteq>[]  \<and> hd xs = s \<and> last xs = t1 \<and> 
            is_proof_of xs (?R1\<union>?R2) \<and>
            (\<forall>i<length xs .  (s,(xs!i))\<in>(NS\<union>S) \<or> (t,(xs!i))\<in>NS\<union>S) \<and> (\<forall>i<length xs .  (xs!i)\<in>ground_terms) \<and>
            (\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S)) \<longrightarrow> ?thesis" by blast
  obtain ss where ss:" ss\<noteq>[]  \<and> hd ss = s1 \<and> last ss = s2 \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
    using assms(2) rtrancl_iff_derivation[of s1 s2 "(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))"] by blast
  let ?xs = "s#ss@[t1]"
  have t1:" ?xs\<noteq>[]  \<and> hd ?xs = s \<and> last ?xs = t1 " by simp
  have t2:"is_proof_of ?xs (?R1\<union>?R2)" 
  proof -
    have "\<forall>i<length ss - 1. (ss ! i, ss ! (i+1)) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" using ss is_derivation_of_def[of ss "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by simp
    then have "\<forall>i<length ss - 1. case (ss ! i, ss ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by blast
    also have "\<forall>i<length [t1] - 1. case ([t1] ! i, [t1] ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by simp
    moreover have " case (last ss, hd [t1]) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(3) ss by fastforce
    moreover have " case (s, hd ss) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) ss by simp
    moreover have "ss\<noteq>[]" "[t1]\<noteq>[]" using ss by auto 
    ultimately have "\<forall>i<length (s # ss @ [t1]) - 1. case ((s # ss @ [t1]) ! i, (s # ss @ [t1]) ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" 
      using app_Cons_P_sublemma[of ss "\<lambda>(x,y). (x,y)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow>" "[t1]" s] by fast
    then show ?thesis by simp
  qed
  have t3:"(\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S)"
  proof -    
    have "\<forall>x t. (s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (s,t)\<in>S"
    proof (intro allI impI)
      fix x t assume a:"(s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"
      then have t:"(x,t)\<in>(NS\<union>S)" by simp
      then show "(s,t)\<in>S" 
      proof (cases "(x,t)\<in>S")
        case True
        then show ?thesis using trans_S transD[of S s x t ] a by simp
      next
        case False
        then have "(x,t)\<in>NS" using t by simp
        then have "(s,t)\<in>S O NS " using a by auto
        then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
      qed
    qed
    also have "(s, hd ss)\<in>S" using assms(1) rstep_R_S ss by simp
    ultimately have S:"\<forall>i<length ss. (s,ss!i)\<in>S" 
      using  derivation_propagation[of "\<lambda>x. (s,x)\<in>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by argo
    then have "\<forall>x\<in>set ss. (s,x)\<in>S" using all_set_conv_all_nth[of ss] by simp
    then have "\<forall>x\<in>set ss. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)" by simp
    also have "(s,s)\<in>(NS\<union>S)" using refl_NS_S refl_onD[of UNIV "NS\<union>S" s ] by simp
    moreover have "(s,t1)\<in> NS\<union>S" using assms(6) by simp
    ultimately have "\<forall>x\<in>set ?xs. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)" by auto
    then show ?thesis using all_set_conv_all_nth[of ?xs "\<lambda>x. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>(NS\<union>S)"] by blast
  qed
    (*****************************************************************************)
  have t4:"(\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms)"
  proof - 
    have "ground s" using assms(4) by simp
    also have "(s,s1)\<in>S" using rstep_R_S assms(1) by simp
    moreover 
    {have "\<forall>i<length ss. (s1,ss!i)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using ss derivation_hd_nth_rtrancl[of ss] by meson
      also have "   (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<subseteq> (NS\<union>S)^*" using rtrancl_mono[of "(?R2\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by simp
      ultimately have "\<forall>i<length ss. (s1,ss!i)\<in>(NS\<union>S)^*" by auto
    }
    ultimately have "\<forall>i<length ss. ground (ss!i)" using ground_NS_S_rtrancl[of s s1] by blast
    then have "\<forall>x\<in>set ss. ground x" using all_set_conv_all_nth[of ss ground] by blast
    then have "\<forall>x\<in>set (s#ss@[t1]). ground x" using assms(4) assms(5) by simp
    then show ?thesis using all_set_conv_all_nth[of ?xs ground] by force
  qed
    (*****************************************************************************)
  have t5:"\<forall>i<length ?xs -1. (?xs!i,?xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S"
  proof -
    have "\<forall>x t. (s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (s,t)\<in>S"
    proof (intro allI impI)
      fix x t assume a:"(s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"
      then have t:"(x,t)\<in>(NS\<union>S)" by simp
      then show "(s,t)\<in>S" 
      proof (cases "(x,t)\<in>S")
        case True
        then show ?thesis using trans_S transD[of S s x t ] a by simp
      next
        case False
        then have "(x,t)\<in>NS" using t by simp
        then have "(s,t)\<in>S O NS " using a by auto
        then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
      qed
    qed
    also have "(s, hd ss)\<in>S" using assms(1) rstep_R_S ss by simp
    ultimately have S:"\<forall>i<length ss. (s,ss!i)\<in>S" 
      using  derivation_propagation[of "\<lambda>x. (s,x)\<in>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by argo
    then have "\<forall>i<length ss-1. ({#s,t#},{#ss!i, ss!(i+1)#})\<in>s_mul_ext NS S" using stricts_s_mul_ext by force
    then have "\<forall>i<length ss-1. (ss!i,ss!(i+1))\<notin>?R1 \<longrightarrow> ({#s,t#},{#ss!i, ss!(i+1)#})\<in>s_mul_ext NS S" by simp
    also have "(s,hd ss)\<notin>(?R1) \<longrightarrow>({#s,t#},{#s, hd ss#}) \<in>s_mul_ext NS S" using assms(1) ss by force
    moreover have "(s,last ss)\<in>S \<and> (s,t1)\<in>S " using S ss last_conv_nth[of ss] assms(6) by simp
    then have "({#s,t#},{#last ss,t1#})\<in>s_mul_ext NS S" using stricts_s_mul_ext by simp
    then have "(last ss,t1)\<notin>?R1 \<longrightarrow> ({#s,t#},{#last ss,t1#})\<in>s_mul_ext NS S" by simp
    moreover have "ss\<noteq>[]" "[t1] \<noteq>[]" using ss by auto
    ultimately show ?thesis using app_Cons_P_sublemma[of ss "\<lambda>(x,y). (x,y)\<notin>?R1 \<longrightarrow>({#s,t#},{#x,y#})\<in>s_mul_ext NS S" "[t1]" s] by force
  qed
  then have "?xs\<noteq>[]  \<and> hd ?xs = s \<and> last ?xs = t1 \<and> 
            is_proof_of ?xs (?R1\<union>?R2) \<and>
            (\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S) \<and> (\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms) \<and>
            (\<forall>i<length ?xs -1. (?xs!i,?xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S)" using t1 t2 t3 t4 by simp
  then show ?thesis using * by blast
qed      



lemma gc\<rho>_case:
  assumes "(s1,t1)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" and "(s,s1)\<in>(rstep R)^+"
    "((t,t1)\<in>(rstep R)^* \<and> (s,s1)\<in>(rstep R)^*)"
    "ground s" "ground t"
  shows "(s,t)\<in>(R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms)"
proof -
  have "(s,s1)\<in>(rstep R)^*" using assms(2) by simp
  then obtain ss where ss:"ss\<noteq>[] \<and> hd ss = s  \<and> last ss = s1 \<and> is_derivation_of ss (rstep R)" using assms(2) rtrancl_iff_derivation[of s s1 "rstep R"] by auto
  then have rgss:"\<forall>i<length ss. ground (ss!i) " using derivation_all_ground assms(4) by simp
  have "\<forall>u\<in> set ss. (s,u)\<in>(rstep R)^*" using ss derivation_hd_nth_rtrancl[of ss "rstep R"] all_set_conv_all_nth[of ss]  by auto
  then have rss:"\<forall>i<length ss. (s,ss!i)\<in>NS\<union>S" using rstep_rtrancl_NS_S by simp
  have "(t,t1)\<in>(rstep R)^*" using assms(3) by auto
  then obtain ts where ts: "ts\<noteq>[] \<and> hd ts = t \<and> last ts = t1 \<and> is_derivation_of ts (rstep R)" using rtrancl_iff_derivation[of t t1 ] by auto
  then have rgts:"\<forall>i<length ts. ground (ts!i)" using derivation_all_ground assms(5) by simp
  have revts:"(rev ts)\<noteq>[] " " hd (rev ts) = t1" "last (rev ts) = t" "is_proof_of (rev ts) (rstep R)"
    using ts apply simp using rev_hd_last apply simp using ts apply fast using rev_hd_last apply simp using ts apply fast using derivation_is_proof_rev ts by blast 
  have "\<forall>u\<in> set ts. (t,u)\<in>(rstep R)^*" using ts derivation_hd_nth_rtrancl[of ts "rstep R"] all_set_conv_all_nth[of ts]  by auto
  then have rts:"\<forall>i<length (rev ts). (t,(rev ts)!i)\<in>NS\<union>S" using rstep_rtrancl_NS_S by (metis nth_mem set_rev)
  then have ns_s:"\<forall>i<length(ss@(rev ts)). (t,(ss@(rev ts))!i)\<in>NS\<union>S \<or> (s,(ss@(rev ts))!i)\<in>NS\<union>S"
  proof -
    have "\<forall>i<length(ss@(rev ts)).  i<length ss \<longrightarrow> ((ss@(rev ts))!i = ss!i)" by (simp add: nth_append)
    then have "\<forall>i<length(ss@(rev ts)).  i<length ss \<longrightarrow> (s,(ss@(rev ts))!i)\<in>NS\<union>S" using rss by simp
    also have "\<forall>i<length(ss@(rev ts)). i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i = (rev ts)!(i-length ss))" by (simp add:nth_append)
    then have "\<forall>i<length(ss@(rev ts)). i\<ge>length ss \<longrightarrow> (t,(ss@(rev ts))!i)\<in>NS\<union>S" using rts by simp
    ultimately have "\<forall>i<length(ss@(rev ts)). (t,(ss@(rev ts))!i)\<in>NS\<union>S \<or> (s,(ss@(rev ts))!i)\<in>NS\<union>S"
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    then show ?thesis using assms(1) assms(3) by simp
  qed
  have pof:"\<forall>i<length(ss@(rev ts))-1. ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>"
  proof -
    have "\<forall>i<length(ss@(rev ts))-1. i<length ss-1 \<longrightarrow> (ss@(rev ts))!i = ss!i \<and> (ss@(rev ts))!(i+1) = ss!(i+1)" by (auto simp add:nth_append)
    then have f1:"\<forall>i<length(ss@(rev ts))-1. i<length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" using ss by simp
    have "\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> (ss@(rev ts))!i = (rev ts)!(i-length ss) \<and> (ss@(rev ts))!(i+1) = (rev ts)!(i+1-length ss)" by (auto simp add:nth_append) 
    also have "\<forall>i<length (rev ts)-1. ((rev ts)!i,(rev ts)!(i+1))\<in>((rstep R))\<^sup>\<leftrightarrow>" using ts is_proof_of_def derivation_is_proof_rev by blast
    moreover have "\<forall>i<length (ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> i-length ss <length (rev ts) \<and> i+1 - length ss <length (rev ts)" by fastforce
    ultimately have "\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" apply(auto simp add:nth_append) 
      by (metis (no_types, lifting) Nat.add_diff_assoc Suc_diff_le Suc_leI le_add_diff_inverse length_greater_0_conv nat_add_left_cancel_less ts)
    then have f2:"\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" 
      apply (simp add:nth_append) by blast
    have "ss\<noteq>[]" "(rev ts)\<noteq>[]" using ss ts apply (simp,simp) done
    then have "\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> (ss@(rev ts))!i = ss!(length ss-1) \<and> (ss@(rev ts))!(i+1) = ((rev ts)!0) " by(auto simp add:nth_append)
    also have "ss!(length ss-1) = s1" using ss last_conv_nth by metis
    moreover have "(rev ts)!0 = t1" using \<open>(rev ts)\<noteq>[]\<close> apply (simp add:rev_nth) using ts last_conv_nth by fastforce
    ultimately have "\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) by presburger
    then have f3:"\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" by blast
    show ?thesis apply (rule length_div_sublemma') using f1 f2 f3 apply (blast,blast,blast) done
  qed
  then have "(s,t)\<in> (R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms)"               
  proof -
    obtain xs where xs:"xs = ss@(rev ts)" by simp
    have "\<forall>i<length xs. ground (xs!i)" using xs rgss rgts by (simp add: nth_append rev_nth)
    also have "xs\<noteq>[]" "hd xs = s" "last xs = t" using xs ss apply (simp,simp)
    proof -
      have "last xs = last(rev ts) " using xs ts by simp
      then have "last xs = hd (rev (rev ts)) " using last_rev ts by auto 
      then show "last xs = t" using ts by simp
    qed
    moreover have "is_proof_of xs ((rstep R) \<union> (rstep (Einf rirun)))" using pof xs using is_proof_of_def by simp
    moreover have "(\<forall>i<length xs. (s, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) " using ns_s xs by auto
    moreover have "\<forall>i<length xs-1. (xs!i,xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S"
    proof -
      {
        fix i assume i1:"i<length xs-1" 
        {assume iss:"i<length ss-1" then have "xs!i = ss!i \<and> xs!(i+1) = ss!(i+1)" using xs i1 apply (simp add:nth_append) by auto
          then have "(xs!i,xs!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" using xs ss iss by fastforce
          then have "(xs!i,xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S" by simp}
        moreover{assume iss:"i\<ge>length ss" 
          then have "xs!i = (rev ts)!(i-length ss) \<and> xs!(i+1) = (rev ts)!(i+1-length ss)" using xs by (auto simp add:nth_append) 
          also have "\<forall>i<length (rev ts)-1. ((rev ts)!i,(rev ts)!(i+1))\<in>((rstep R))\<^sup>\<leftrightarrow>" using ts is_proof_of_def derivation_is_proof_rev by blast
          moreover have " i-length ss <length (rev ts) \<and> i+1 - length ss <length (rev ts)" using iss i1 xs by fastforce
          ultimately have "(xs!i,xs!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" using i1 iss xs apply(simp add:nth_append) 
            using revts Nat.add_diff_assoc Suc_diff_le Suc_leI le_add_diff_inverse length_greater_0_conv nat_add_left_cancel_less by simp
          then have "(xs!i,xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S" by simp }
        moreover{assume iss:"i=length ss-1" 
          have "ss\<noteq>[]" "(rev ts)\<noteq>[]" using ss ts apply (simp,simp) done
          then have "xs!i = ss!(length ss-1) \<and> xs!(i+1) =(rev ts)!0" using xs iss by (auto simp add:nth_append)
          also have "ss!(length ss-1) = s1" using ss last_conv_nth by metis
          moreover have "(rev ts)!0 = t1" using \<open>(rev ts)\<noteq>[]\<close> apply (simp add:rev_nth) using ts last_conv_nth by fastforce
          ultimately have h:"xs!i = s1" "xs!(i+1) = t1" "(xs!i,xs!(i+1))\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) by auto
          then have "({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S" 
          proof -
            have "\<forall>i<length ss. i\<ge>1 \<longrightarrow> (ss!0,ss!i)\<in>S" using ss derivation_all_S by simp
            then have "length ss\<ge>2 \<longrightarrow> (ss!0,ss!(length ss-1))\<in>S" by simp
            also have "\<forall>i<length ts. i\<ge>1 \<longrightarrow> (ts!0,ts!i)\<in>S" using ts derivation_all_S by simp
            then have "length ts\<ge>2 \<longrightarrow> (ts!0,ts!(length ts-1))\<in>S" by simp
            then have "length (rev ts)\<ge>2 \<longrightarrow> ((rev ts)!(length (rev ts)-1),(rev ts)!0)\<in>S" 
              by (metis \<open>rev ts ! 0 = t1\<close> hd_conv_nth last_conv_nth length_rev revts(1) revts(3) ts)
            moreover have h2:"s = ss!0" "t = (rev ts)!(length (rev ts)-1)" using ss apply (metis hd_conv_nth) using revts apply (metis last_conv_nth)done
            then have "((rev ts)!(length (rev ts)-1), (ss @ rev ts) ! i) \<in> NS \<union> S \<or> (ss!0, (ss @ rev ts) ! i) \<in> NS \<union> S " 
              "((rev ts)!(length (rev ts)-1), (ss @ rev ts) ! (i+1)) \<in> NS \<union> S \<or> (ss!0, (ss @ rev ts) ! (i+1)) \<in> NS \<union> S"
              using ns_s i1 xs ns_s i1 xs by auto
            moreover have lenss:"length ss>1" using SN_rstep_R trancl_proof_length_2 ss assms(2)
              by (metis SN_S calculation(1) diff_is_0_eq h2(1) not_less refl_not_SN)
            moreover have "ss\<noteq>[]" using ss by simp
            ultimately have "({#ss ! 0, rev ts ! (length (rev ts) - 1)#}, {#(ss @ (rev ts)) ! (length ss - 1), (ss @ (rev ts)) ! length ss#}) \<in> s_mul_ext NS S"
              using iss revts(1) length_2_s_mul_ext  by blast
            then have "({#s,t#}, {#(ss @ (rev ts)) ! (length ss - 1), (ss @ (rev ts)) ! length ss#})\<in> s_mul_ext NS S" using h2 h iss xs by presburger
            then have "({#s,t#}, {#(ss @ (rev ts)) ! i, (ss @ (rev ts)) ! (i+1)#})\<in> s_mul_ext NS S" using iss lenss h2 h xs 
              by (metis (no_types, lifting) add.commute add_mset_commute le_add_diff_inverse less_imp_le_nat)
            then show ?thesis using h2 h xs iss by force
          qed
          then have "(xs!i,xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S" by simp}            
        ultimately have "(xs!i,xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow>\<longrightarrow>({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S" by linarith
      }
      then show ?thesis by simp
    qed 
    ultimately show ?thesis by auto
  qed
  then show ?thesis by blast   
qed             

lemma gc\<rho>_case':
  assumes "(w1,w'1)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" and "(w,w1)\<in>(rstep R)^+" 
    "((w',w'1)\<in>(rstep R)^* \<and> (w,w1)\<in>(rstep R)^*)"
    "ground w" "ground w'" "(w,w')\<in>S" 
  shows "\<exists>xs.  xs \<noteq> [] \<and>
                 hd xs = w \<and>
                 last xs = w' \<and>
                 is_proof_of xs (rstep R \<union> rstep (Einf rirun)) \<and>
                 (\<forall>i<length xs. (w, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) \<and>
                 (\<forall>i<length xs. xs ! i \<in> ground_terms) \<and>
                 (\<forall>i<length xs - 1. (xs ! i, xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#w, t#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext NS S)"
proof -
  have "(w,w1)\<in>(rstep R)^*" using assms(2) by simp
  then obtain ss where ss:"ss\<noteq>[] \<and> hd ss = w  \<and> last ss = w1 \<and> is_derivation_of ss (rstep R)" using assms(2) rtrancl_iff_derivation[of w w1 "rstep R"] by auto
  then have rgss:"\<forall>i<length ss. ground (ss!i) " using derivation_all_ground assms(4) by simp
  have "\<forall>u\<in> set ss. (w,u)\<in>(rstep R)^*" using ss derivation_hd_nth_rtrancl[of ss] all_set_conv_all_nth[of ss] by auto
  then have rss:"\<forall>i<length ss. (w,ss!i)\<in>NS\<union>S" using rstep_rtrancl_NS_S by simp
  have "(w',w'1)\<in>(rstep R)^*" using assms(3) by auto
  then obtain ts where ts: "ts\<noteq>[] \<and> hd ts = w' \<and> last ts = w'1 \<and> is_derivation_of ts (rstep R)" using rtrancl_iff_derivation[of w' w'1 ] by auto
  then have rgts:"\<forall>i<length ts. ground (ts!i)" using derivation_all_ground assms(5) by simp
  have revts:"(rev ts)\<noteq>[] " " hd (rev ts) = w'1" "last (rev ts) = w'" "is_proof_of (rev ts) (rstep R)"
    using ts apply simp using rev_hd_last apply simp using ts apply fast using rev_hd_last apply simp using ts apply fast using derivation_is_proof_rev ts by blast 
  have "\<forall>u\<in> set ts. (w',u)\<in>(rstep R)^*" using ts derivation_hd_nth_rtrancl[of ts] all_set_conv_all_nth[of ts] by simp
  then have rts:"\<forall>i<length (rev ts). (w',(rev ts)!i)\<in>NS\<union>S" using rstep_rtrancl_NS_S by (metis nth_mem set_rev)
  then have ns_s:"\<forall>i<length(ss@(rev ts)). (w',(ss@(rev ts))!i)\<in>NS\<union>S \<or> (w,(ss@(rev ts))!i)\<in>NS\<union>S"
  proof -
    have "\<forall>i<length(ss@(rev ts)).  i<length ss \<longrightarrow> ((ss@(rev ts))!i = ss!i)" by (simp add: nth_append)
    then have "\<forall>i<length(ss@(rev ts)).  i<length ss \<longrightarrow> (w,(ss@(rev ts))!i)\<in>NS\<union>S" using rss by simp
    also have "\<forall>i<length(ss@(rev ts)). i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i = (rev ts)!(i-length ss))" by (simp add:nth_append)
    then have "\<forall>i<length(ss@(rev ts)). i\<ge>length ss \<longrightarrow> (w',(ss@(rev ts))!i)\<in>NS\<union>S" using rts by simp
    ultimately have "\<forall>i<length(ss@(rev ts)). (w',(ss@(rev ts))!i)\<in>NS\<union>S \<or> (w,(ss@(rev ts))!i)\<in>NS\<union>S"
      by (metis eq_imp_le less_imp_le_nat linorder_neqE_nat)
    then show ?thesis using assms(1) assms(3) by simp
  qed
  have pof:"\<forall>i<length(ss@(rev ts))-1. ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>"
  proof -
    have "\<forall>i<length(ss@(rev ts))-1. i<length ss-1 \<longrightarrow> (ss@(rev ts))!i = ss!i \<and> (ss@(rev ts))!(i+1) = ss!(i+1)" by (auto simp add:nth_append)
    then have f1:"\<forall>i<length(ss@(rev ts))-1. i<length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" using ss by simp
    have "\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> (ss@(rev ts))!i = (rev ts)!(i-length ss) \<and> (ss@(rev ts))!(i+1) = (rev ts)!(i+1-length ss)" by (auto simp add:nth_append) 
    also have "\<forall>i<length (rev ts)-1. ((rev ts)!i,(rev ts)!(i+1))\<in>((rstep R))\<^sup>\<leftrightarrow>" using ts is_proof_of_def derivation_is_proof_rev by blast
    moreover have "\<forall>i<length (ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> i-length ss <length (rev ts) \<and> i+1 - length ss <length (rev ts)" by fastforce
    ultimately have "\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" apply(auto simp add:nth_append) 
      by (metis (no_types, lifting) Nat.add_diff_assoc Suc_diff_le Suc_leI le_add_diff_inverse length_greater_0_conv nat_add_left_cancel_less ts)
    then have f2:"\<forall>i<length(ss@(rev ts))-1. i\<ge>length ss \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in> ((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" 
      apply (simp add:nth_append) by blast
    have "ss\<noteq>[]" "(rev ts)\<noteq>[]" using ss ts apply (simp,simp) done
    then have "\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> (ss@(rev ts))!i = ss!(length ss-1) \<and> (ss@(rev ts))!(i+1) = ((rev ts)!0) " by(auto simp add:nth_append)
    also have "ss!(length ss-1) = w1" using ss last_conv_nth by metis
    moreover have "(rev ts)!0 = w'1" using \<open>(rev ts)\<noteq>[]\<close> apply (simp add:rev_nth) using ts last_conv_nth by fastforce
    ultimately have "\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) by presburger
    then have f3:"\<forall>i<length(ss@(rev ts))-1. i=length ss-1 \<longrightarrow> ((ss@(rev ts))!i,(ss@(rev ts))!(i+1))\<in>((rstep R)\<union>(rstep (Einf rirun)))\<^sup>\<leftrightarrow>" by blast
    show ?thesis apply (rule length_div_sublemma') using f1 f2 f3 apply (blast,blast,blast) done
  qed
  then have "\<exists>xs.      xs \<noteq> [] \<and>
                         hd xs = w \<and>
                         last xs = w' \<and>
                         is_proof_of xs (rstep R \<union> rstep (Einf rirun)) \<and>
                         (\<forall>i<length xs. (w, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) \<and>
                         (\<forall>i<length xs. xs ! i \<in> ground_terms) \<and>
                         (\<forall>i<length xs - 1. (xs ! i, xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#w, t#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext NS S)"      
  proof -
    let ?xs ="ss@(rev ts)" 
    have "\<forall>i<length ?xs. ground (?xs!i)" using rgss rgts by (simp add: nth_append rev_nth)
    also have "?xs\<noteq>[]" "hd ?xs = w" "last ?xs = w'" using ss apply (simp,simp)
    proof -
      have "last ?xs = last(rev ts) " using ts by simp
      then have "last ?xs = hd (rev (rev ts)) " using last_rev ts by auto 
      then show "last ?xs = w'" using ts by simp
    qed
    moreover have "is_proof_of ?xs ((rstep R) \<union> (rstep (Einf rirun)))" using pof using is_proof_of_def by simp
    moreover have "(\<forall>i<length ?xs. (w, ?xs ! i) \<in> NS \<union> S \<or> (t, ?xs ! i) \<in> NS \<union> S) "
    proof -
      have "\<forall>i<length ss.  i\<ge> 1\<longrightarrow> (ss!0, ?xs ! i) \<in> NS\<union>S" using derivation_all_S[of ss] ss nth_append[of ss "rev ts" ] by simp
      also have "\<forall>i<length ss.  i = 0\<longrightarrow> (ss!0, ?xs ! i) \<in> NS\<union>S" using nth_append[of ss "rev ts"] refl_NS refl_onD[of UNIV NS] by simp
      ultimately have "\<forall>i<length ss. (ss!0, ?xs ! i) \<in> NS\<union>S" by fastforce
      then have "\<forall>i<length ?xs. i<length ss \<longrightarrow> (w, ?xs ! i) \<in> NS\<union>S" using ss hd_conv_nth[of ss] by simp
      also 
      { have "\<forall>i<length ts. i\<ge>1\<longrightarrow>(ts!0, ts!i) \<in> NS\<union>S" using derivation_all_S[of ts] ts nth_append by simp
        also have "\<forall>i<length ts. i=0 \<longrightarrow> (ts!0, ts!i) \<in> NS\<union>S" using refl_NS refl_onD[of UNIV NS] by simp
        ultimately have "\<forall>i<length ts. (ts!0, ts!i) \<in> NS\<union>S" by fastforce
        also have "ts!0 = w' " using ts hd_conv_nth[of ts] by simp
        ultimately have "\<forall>i<length ts. (w, ts!i) \<in> NS\<union>S" using ts assms(6) S_NS_S_S[of w w'] by blast
        then have "\<forall>x\<in> set ts. (w, x)\<in> NS\<union>S" using all_set_conv_all_nth[of ts] by presburger
        then have "\<forall>x\<in> set (rev ts). (w, x)\<in> NS\<union>S" by simp
        then have "\<forall>i<length (rev ts). (w, (rev ts)!i) \<in> NS\<union>S" using all_set_conv_all_nth[of "rev ts"] by simp
        also have "\<forall>n<length ?xs. n\<ge>length ss \<longrightarrow>(n - length ss)<length (rev ts)" by auto
        moreover have "\<forall>i<length ?xs. i\<ge> length ss \<longrightarrow>  ?xs!i = (rev ts)!(i - length ss) " using nth_append[of ss "rev ts"] by simp
        ultimately have "\<forall>i<length ?xs. i\<ge> length ss \<longrightarrow> (w, ?xs!i) \<in> NS\<union>S" using nth_append[of ss "rev ts"] by metis
      }
      ultimately show ?thesis by fastforce
    qed
    moreover have "(\<forall>i<length ?xs. ?xs ! i \<in> ground_terms) "
    proof -
      have "\<forall>x\<in>set ss. x\<in>ground_terms " using rgss all_set_conv_all_nth[of ss "\<lambda>x. x\<in>ground_terms"] by force
      also have "\<forall>x\<in>set ts. x\<in>ground_terms" using rgts all_set_conv_all_nth[of ts "\<lambda>x. x\<in>ground_terms"] by force
      then have "\<forall>x\<in>set (rev ts). x\<in>ground_terms" by simp
      ultimately have "\<forall>x\<in>set ?xs. x\<in>ground_terms" by auto
      then show ?thesis using all_set_conv_all_nth[of ?xs] by auto
    qed
    moreover have "\<forall>i<length ?xs-1. (?xs!i,?xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S"
    proof -
      {
        fix i assume i1:"i<length ?xs-1" 
        {assume iss:"i<length ss-1" then have "?xs!i = ss!i \<and> ?xs!(i+1) = ss!(i+1)" using i1 apply (simp add:nth_append) by auto
          then have "(?xs!i,?xs!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" using ss iss by fastforce
          then have "(?xs!i,?xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S" by simp}
        moreover{assume iss:"i\<ge>length ss" 
          then have "?xs!i = (rev ts)!(i-length ss) \<and> ?xs!(i+1) = (rev ts)!(i+1-length ss)" by (auto simp add:nth_append) 
          also have "\<forall>i<length (rev ts)-1. ((rev ts)!i,(rev ts)!(i+1))\<in>((rstep R))\<^sup>\<leftrightarrow>" using ts is_proof_of_def derivation_is_proof_rev by blast
          moreover have " i-length ss <length (rev ts) \<and> i+1 - length ss <length (rev ts)" using iss i1 by fastforce
          ultimately have "(?xs!i,?xs!(i+1))\<in>(rstep R)\<^sup>\<leftrightarrow>" using i1 iss apply(simp add:nth_append) 
            using revts Nat.add_diff_assoc Suc_diff_le Suc_leI le_add_diff_inverse length_greater_0_conv nat_add_left_cancel_less by simp
          then have "(?xs!i,?xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S" by simp }
        moreover{assume iss:"i=length ss-1" 
          have "ss\<noteq>[]" "(rev ts)\<noteq>[]" using ss ts apply (simp,simp) done
          then have "?xs!i = ss!(length ss-1) \<and> ?xs!(i+1) =(rev ts)!0" using iss by (auto simp add:nth_append)
          also have "ss!(length ss-1) = w1" using ss last_conv_nth by metis
          moreover have "(rev ts)!0 = w'1" using \<open>(rev ts)\<noteq>[]\<close> apply (simp add:rev_nth) using ts last_conv_nth by fastforce
          ultimately have h:"?xs!i = w1" "?xs!(i+1) = w'1" "(?xs!i,?xs!(i+1))\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(1) by auto
          then have "({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S" 
          proof -
            have ss2:"length ss \<ge>2 " using assms  trancl_proof_length_2[of _ _ "rstep R"] ss ts SN_rstep_R by presburger
            have "\<forall>i<length ss. i\<ge>1 \<longrightarrow> (ss!0,ss!i)\<in>S" using ss derivation_all_S by simp
            then have "(ss!0,ss!(length ss-1))\<in>S" using ss2 by simp
            also 
            {have "\<forall>i<length ts. i\<ge>1 \<longrightarrow> (ts!0,ts!i)\<in>S" using ts derivation_all_S by simp
              then have "length ts\<ge>2 \<longrightarrow> (ts!0,ts!(length ts-1))\<in>NS\<union>S" by simp
              also have "length ts = 1 \<longrightarrow> (ts!0,ts!(length ts-1))\<in>NS\<union>S" using refl_NS refl_onD[of UNIV "NS"] by simp
              ultimately have "(ts!0,ts!(length ts-1))\<in>NS\<union>S" using ts length_0_conv[of ts] by linarith
            }
            then have "((rev ts)!(length (rev ts)-1),(rev ts)!0)\<in>NS\<union>S" 
              by (metis \<open>rev ts ! 0 = w'1\<close> hd_conv_nth last_conv_nth length_rev revts(1) revts(3) ts)
            moreover have h2:"w = ss!0" "w' = (rev ts)!(length (rev ts)-1)" using ss apply (metis hd_conv_nth) using revts apply (metis last_conv_nth)done
            ultimately also have "((rev ts)!(length (rev ts)-1),(rev ts)!0)\<in>NS\<union>S" "(ss!0,ss!(length ss-1))\<in>S" by auto
            ultimately have "(w',rev ts!0)\<in>NS\<union>S" "(w,ss!(length ss-1))\<in>S" by auto
            also then  have "(w,rev ts!0)\<in>S" using assms(6) S_NS_S_S by blast
            moreover have "ss\<noteq>[]" using ss by simp
            moreover have "(ss @ (rev ts)) ! (length ss - 1) = ss!(length ss-1)" "(ss @ (rev ts)) ! length ss = (rev ts)!0" using nth_append[of ss "rev ts"] ss by auto
            ultimately have "({#w,t#}, {#(ss @ (rev ts)) ! (length ss - 1), (ss @ (rev ts)) ! length ss#})\<in> s_mul_ext NS S" 
              using stricts_s_mul_ext[of] by simp
            then show ?thesis using iss ss by force
          qed
          then have "(?xs!i,?xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S" by simp}            
        ultimately have "(?xs!i,?xs!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow>\<longrightarrow>({#w,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S" by linarith
      }
      then show ?thesis by simp
    qed 
    ultimately show ?thesis by blast
  qed
  then show ?thesis by blast   
qed  


lemma rtrancl_not_trancl_imp_eq:
  "(s,t)\<in>RR^* \<and> (s,t)\<notin>RR^+ \<longrightarrow> s = t"
proof(rule impI)
  assume a:"(s,t)\<in>RR^* \<and> (s,t)\<notin>RR^+"
  then obtain i where "(s,t)\<in>RR^^i" by auto
  then show "s = t"
  proof (induction i)
    case (Suc i)
    then have "\<exists>u. (s,u)\<in> RR \<and> (u,t)\<in>RR^*" by blast
    then have "(s,t)\<in>RR^+" by auto
    then show ?case using a by simp
  qed simp
qed

lemma simplify_b':
  assumes "(s,s1)\<in>(rstep (snd (snd rirun i)))\<^sup>\<leftrightarrow>" and "gc_subst C (\<sigma>::('a,'b)subst)" 
    and "ground s" "ground s1" and "snd (snd rirun 0) = {}" "ri_run rirun" "i<fst rirun"
  shows "(s,s1)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
proof -
  let ?R1 = "(rstep R)" let ?R2 = "rstep (Einf rirun)" let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
  have asm6:"(?H i)\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow>" using assms(5) assms(6) rirun_H_subset_Einf[of rirun] assms(7) by simp
  obtain w w' Ctx' \<theta> where ww':"(w,w')\<in>(?H i)\<^sup>\<leftrightarrow> \<and> Ctx'\<langle>w\<cdot>\<theta>\<rangle> = s \<and> Ctx'\<langle>w'\<cdot>\<theta>\<rangle> = s1" using assms(1) by blast
  then have gCww':"ground Ctx'\<langle>w\<cdot>\<theta>\<rangle>""ground Ctx'\<langle>w'\<cdot>\<theta>\<rangle>" using assms(3) assms(4) by auto
  then have gC:"ground_ctxt Ctx'" by simp
  have gws:"ground (w\<cdot>\<theta>)" "ground (w'\<cdot>\<theta>)" using gCww' by auto
  then have g\<theta>:"ground_subst (\<theta>|s (vars_term w\<union>vars_term w'))" by auto
  then have g\<theta>\<sigma>:"ground_subst ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" using assms(2) assms(3) 
  proof -
    have *:"\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) . ground (\<theta> v)" using g\<theta> by simp
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')).  ground ((\<theta> v)\<cdot>\<sigma>)" 
      by (simp add: ground_subst_apply)
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')). ground ((\<theta>\<circ>\<^sub>s\<sigma>) v)" using subst_compose[of \<theta> \<sigma>] by simp
    also have "subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) = subst_domain ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" 
      using gws * g\<theta>
      by (metis (no_types, lifting) ground_subst_apply ground_subst_domain_is_vars_term subst_compose subst_ext)
    ultimately show ?thesis by simp
  qed
  let ?\<rho> = "((\<theta>\<circ>\<^sub>s\<sigma>) |s (vars_term w \<union>vars_term w'))"
  have "w\<cdot>?\<rho> = w\<cdot>(\<theta>\<circ>\<^sub>s\<sigma>)" "w'\<cdot>?\<rho> = w'\<cdot>(\<theta>\<circ>\<^sub>s\<sigma>)" using coincidence_lemma'[of w "vars_term w\<union>vars_term w'" ] apply blast
    using coincidence_lemma'[of w' "vars_term w\<union>vars_term w'" ] by blast
  then have "w\<cdot>?\<rho> = (w\<cdot>\<theta>)\<cdot>\<sigma>" "w'\<cdot>?\<rho> = (w'\<cdot>\<theta>)\<cdot>\<sigma>" by auto
  then have w\<rho>w\<theta>:"w\<cdot>?\<rho> = (w\<cdot>\<theta>) \<and> w'\<cdot>?\<rho> = (w'\<cdot>\<theta>)" using ground_subst_apply[of "w\<cdot>\<theta>" \<sigma>] ground_subst_apply[of "w'\<cdot>\<theta>" \<sigma>] gws by argo
  then have gw\<rho>:"ground (w \<cdot> ?\<rho>) \<and> ground (w' \<cdot> ?\<rho>)" using gws by argo
  also then have gCw\<rho>:"ground Ctx'\<langle>w\<cdot>?\<rho>\<rangle> \<and>ground Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" using gC by simp
  have "ground_subst ((\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w')) |s (vars_term w \<union> vars_term w')) " using g\<theta>\<sigma> by simp
  ultimately have dom:"subst_domain (?\<rho> |s (vars_term w \<union>vars_term w')) =  vars_term w \<union> vars_term w' " 
    using ground_subst_domain_is_vars_term[of ?\<rho> w w'] by fast
  then have domrl:"vars_term w \<union> vars_term w' \<subseteq>subst_domain (?\<rho> |s (vars_term w \<union>vars_term w'))" by simp
  consider "gc_subst C ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w \<union> vars_term w'))"|"\<not>gc_subst C ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union> vars_term w'))" by auto
  then show ?thesis
  proof cases
    case 1
    then have "(w,w')\<in>(?H i)\<or> (w',w)\<in> ?H i" using ww' by simp
    also
    { assume "(w,w')\<in>?H i"
      then obtain j E' where E':" j<i \<and> ((w,w'),E')\<in> expand_eq_set (?H j) \<and> ?E (j+1) = ?E j-{(w,w'),(w',w)}\<union>E' "
        using all_H_eq_expanded[of rirun] assms(5) assms(6) assms(7) by blast
      then obtain Cx where Cx: "Cx\<in>basic_ctxts w \<and> 
        (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx w w' \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* 
       \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))"
        using expand_eq_set by  auto
      then have Cx2:"Cx\<in>basic_ctxts w" by auto
      then obtain u where u: "w = Cx\<langle>u\<rangle> \<and> u \<in> basic_subts w" using basic_ctxt_subts by auto
      then have "u\<in>basic_subts w" by auto
      also have "gc_subst C (?\<rho> |s vars_term w)" using 1 by simp
      moreover have "vars_term w  \<union> vars_term w' = subst_domain ?\<rho>" using dom by simp 
      ultimately have "(w\<cdot>?\<rho>,w'\<cdot>?\<rho>)\<in>((rstep R) O (rstep (Expd_rename Cx w w')))" using Cx2 expd_prop'[of Cx w ?\<rho> w'] by blast
      then obtain w\<^sub>i where w\<^sub>i:"(w\<cdot>?\<rho>, w\<^sub>i)\<in>(rstep R) \<and> (w\<^sub>i,w'\<cdot>?\<rho>)\<in>(rstep (Expd_rename Cx w w'))" by blast
      then have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx'\<langle>w\<^sub>i\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>(rstep (Expd_rename Cx w w'))" by auto
      from this(2) obtain w\<^sub>ir Ctx'' \<theta> w'\<^sub>ir where w\<^sub>ir:"(w\<^sub>ir, w'\<^sub>ir)\<in>Expd_rename Cx w w' \<and> Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx'\<langle>w\<^sub>i\<rangle> \<and> Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" 
        apply (rule rstepE) by metis
      have "?E (j+1) = ?E j-{(w,w'),(w',w)}\<union>E'" using E' by simp
      then obtain w\<^sub>i' where w\<^sub>i':" (w\<^sub>ir, w\<^sub>i')\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (w\<^sub>i',w'\<^sub>ir)\<in>E'"  using E' Cx  w\<^sub>ir by blast
      then have cs\<^sub>i':"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
      proof -
        have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)" by auto
        also have "\<forall>s t. (s,t)\<in>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
        ultimately have "\<forall>s t . (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
        then have "(w\<^sub>ir,w\<^sub>i')\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using  rtrancl_closed_ctxt_subst[of "((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx'' \<theta> w\<^sub>ir w\<^sub>i'] by blast
        then show ?thesis using w\<^sub>i' by fast
      qed
      also have HEinf:"(rstep (?H j))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep assms(5) assms(6) E' assms(7) by simp
      then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
      then have "((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
      ultimately have t1:"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
      note HEinf then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
      then have"((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
      then have t2:"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
      then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
        using rtrancl_iff_derivation[of "Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
      then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  
        using derivation_ordered trans refl_NS_S by blast
      have "(w\<^sub>i',w'\<^sub>ir)\<in>E'" using w\<^sub>i' w\<^sub>ir Cx by  metis
      also have "E'\<subseteq>?E (j+1)" using E' by simp
      moreover have "j+1\<le> fst rirun" using E' assms(7) by simp
      ultimately have "(w\<^sub>i',w'\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
      then have "(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
      then have w\<^sub>i'w':"(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun) " using w\<^sub>ir by argo
      have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<^sub>i\<rangle>)\<in>rstep R" "(Ctx'\<langle>w\<^sub>i\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun)"
        using w\<^sub>i apply force using w\<^sub>ir t2 apply force using w\<^sub>i'w' by simp
      then have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>, Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
        using expand_r1r2_case[of "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w\<^sub>i\<rangle>" "Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>"] gCw\<rho> by blast
      then have ?thesis using ww' w\<rho>w\<theta> by auto
    }
    moreover 
    { assume "(w',w)\<in>?H i"
      then obtain j E' where E':" j<i \<and> ((w',w),E')\<in> expand_eq_set (?H j) \<and> ?E (j+1) = ?E j-{(w',w),(w,w')}\<union>E' "
        using all_H_eq_expanded[of rirun] assms(5) assms(6) assms(7) by blast
      then obtain Cx where Cx:"Cx\<in>basic_ctxts w' \<and> 
             (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx w' w \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* 
            \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))"
        using expand_eq_set by auto
      also have "gc_subst C (?\<rho> |s vars_term w')" using 1 by simp
      moreover have "vars_term w' \<union> vars_term w = subst_domain ?\<rho>" using dom by auto
      ultimately have "(w'\<cdot>?\<rho>,w\<cdot>?\<rho>)\<in>((rstep R) O (rstep (Expd_rename Cx w' w)))" using expd_prop'[of Cx w' ?\<rho> w] by fast
      then obtain w'\<^sub>i where w'\<^sub>i:"(w'\<cdot>?\<rho>, w'\<^sub>i)\<in>(rstep R) \<and> (w'\<^sub>i,w\<cdot>?\<rho>)\<in>(rstep (Expd_rename Cx w' w))" by blast
      then have "(Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx'\<langle>w'\<^sub>i\<rangle>,Ctx'\<langle>w\<cdot>?\<rho>\<rangle>)\<in>(rstep (Expd_rename Cx w' w))" by auto
      from this(2) obtain w'\<^sub>ir Ctx'' \<theta> w\<^sub>ir where w\<^sub>ir:"(w'\<^sub>ir, w\<^sub>ir)\<in>Expd_rename Cx w' w \<and> Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx'\<langle>w'\<^sub>i\<rangle> \<and> Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx'\<langle>w\<cdot>?\<rho>\<rangle>" 
        apply (rule rstepE) by metis
      have "?E (j+1) = ?E j-{(w',w),(w,w')}\<union>E'" using E' by simp
      then obtain w\<^sub>i where w\<^sub>i:" (w'\<^sub>ir, w\<^sub>i)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (w\<^sub>i,w\<^sub>ir)\<in>E'"  using E' Cx  w\<^sub>ir by blast
      then have cs\<^sub>i':"(Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
      proof -
        have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)" by auto
        also have "\<forall>s t. (s,t)\<in>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
        ultimately have "\<forall>s t . (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
        then have "(w'\<^sub>ir,w\<^sub>i)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using  rtrancl_closed_ctxt_subst[of "((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx'' \<theta> w'\<^sub>ir w\<^sub>i] by blast
        then show ?thesis using w\<^sub>i by fast
      qed
      also have HEinf:"(rstep (?H j))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep assms(5) assms(6) E' assms(7) by simp
      then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
      then have "((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
      ultimately have t1:"(Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
      note HEinf then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
      then have"((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
      then have t2:"(Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
      then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
        using rtrancl_iff_derivation[of "Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
      then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
      have "(w\<^sub>i,w\<^sub>ir)\<in>E'" using w\<^sub>i w\<^sub>ir Cx by metis

      also have "E'\<subseteq>?E (j+1)" using E' by simp
      moreover have "j+1\<le> fst rirun" using E' assms(7) by simp
      ultimately have "(w\<^sub>i,w\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
      then have "(Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
      then have w\<^sub>i'w':"(Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>,Ctx'\<langle>w\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun) " using w\<^sub>ir by argo
      have "(Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<^sub>i\<rangle>)\<in>rstep R" "(Ctx'\<langle>w'\<^sub>i\<rangle>,Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>,Ctx'\<langle>w\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun)"
        using w'\<^sub>i apply auto[1] using w\<^sub>ir t2 apply simp using w\<^sub>i'w' by simp

      then have "(Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>, Ctx'\<langle>w\<cdot>?\<rho>\<rangle>)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
        using expand_r1r2_case[of "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w'\<^sub>i\<rangle>" "Ctx''\<langle>w\<^sub>i\<cdot>\<theta>\<rangle>" "rirun" "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>"] gCw\<rho> by blast
      then have "(s1,s)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" using ww' w\<rho>w\<theta> by argo
      then have ?thesis using r1r2gtstar_on_rev[of s1 s NS S "rstep R" "rstep (Einf rirun)" ground_terms] by auto
    }
    ultimately show ?thesis by fastforce
  next
    case 2
    then have a':"ground_subst (?\<rho>|s (vars_term w \<union> vars_term w'))" "\<not>constr_subst C (?\<rho>|s (vars_term w \<union> vars_term w'))" using g\<theta>\<sigma> 2 by auto
    have "ground_subst (?\<rho>|s (vars_term w \<union> vars_term w'))" "\<not>constr_subst C (?\<rho>|s (vars_term w \<union> vars_term w'))" using a' by auto
    then have "\<exists>\<rho>. ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^+) \<and> 
                ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^* \<and> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term w\<union> vars_term w')) "
      using domrl DC4 RI2 SN_rstep_R TRS2 ground_not_constr_subst_rewritable'[of ?\<rho> w w' R D C ] by blast
    then obtain \<rho> where gcs\<rho>:"((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^+) \<and> 
                ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^* \<and> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term w\<union> vars_term w')) " by blast
    then have \<rho>:"((Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+ \<or> (Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+) \<and> 
                  ((Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)^* \<and> (Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep R)^*)" 
      using rsteps_closed_ctxt[of _ _ R] trancl_rstep_ctxt[of _ _ R] by meson    

    then have *:"(Ctx'\<langle>w\<cdot>\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using ww' asm6 by blast
    then show ?thesis
    proof (cases "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+")
      case True 
      then have fa:"(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+" by auto
      moreover have "(Ctx'\<langle>w \<cdot> \<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using * by auto
      moreover then have "(Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>* \<and> (Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>*" using \<rho> by meson
      moreover have "ground Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle> \<and> ground Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>" using gCw\<rho> by blast
      ultimately have " (Ctx'\<langle>w \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>, Ctx'\<langle>w' \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>)
                            \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
        using gc\<rho>_case[of "Ctx'\<langle>w\<cdot>\<rho>\<rangle>" "Ctx'\<langle>w'\<cdot>\<rho>\<rangle>"rirun "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>"] by fast
      then show ?thesis using w\<rho>w\<theta> ww' by auto
    next
      case False 
      then have fa:"(Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+" using \<rho> by auto
      moreover have "(Ctx'\<langle>w \<cdot> \<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using * by auto
      moreover then have "(Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>* \<and> (Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>*" using \<rho> by meson
      moreover have "ground Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle> \<and> ground Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>" using gCw\<rho> by blast
      ultimately have " (Ctx'\<langle>w' \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>, Ctx'\<langle>w \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>)
                            \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
        using gc\<rho>_case[of "Ctx'\<langle>w'\<cdot>\<rho>\<rangle>" "Ctx'\<langle>w\<cdot>\<rho>\<rangle>"rirun "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>"] by fast
      then have "(s1,s)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" using w\<rho>w\<theta> ww' by argo
      then show ?thesis using r1r2gtstar_on_rev[of s1 s NS S "(rstep R)" "(rstep (Einf rirun))" ground_terms] by blast
    qed
  qed
qed

lemma simplify_b:
  assumes "(s,s1)\<in>(rstep (snd (snd rirun i)))\<inter>S" and "gc_subst C (\<sigma>::('a,'b)subst)" 
    and "ground s" "ground s1" and "snd (snd rirun 0) = {}" "ri_run rirun" "i<fst rirun"
  shows "\<exists>ts. length ts\<ge>2 \<and> hd ts = s \<and> last ts = s1 \<and> is_proof_of ts ((rstep R)\<union>(rstep (Einf rirun))) \<and> (\<forall>i<length ts .  (ts!i)\<in>ground_terms) \<and>
        (\<forall>i<length ts. (s,ts!i)\<in>NS\<union>S \<or> (t,ts!i)\<in>NS\<union>S) \<and>
        (\<forall>i<length ts -1. (ts!i,ts!(i+1))\<notin>(rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#ts!i,ts!(i+1)#})\<in>s_mul_ext NS S)"
proof -
  let ?R1 = "(rstep R)" let ?R2 = "rstep (Einf rirun)" let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
  have asm6:"(?H i)\<^sup>\<leftrightarrow>\<subseteq>(Einf rirun)\<^sup>\<leftrightarrow>" using assms(5) assms(6) rirun_H_subset_Einf[of rirun] assms(7) by simp
  have ss1:"s\<noteq>s1" using assms(1) SN_S by fast
  have tslength:"\<forall>ts. ts\<noteq>[] \<and> hd ts = s \<and> last ts = s1 \<and> is_proof_of ts (?R1\<union>?R2) \<longrightarrow> length ts \<ge>2"
  proof (intro allI impI,rule ccontr)
    fix ts assume a1:"ts\<noteq>[] \<and> hd ts = s \<and> last ts = s1 \<and> is_proof_of ts (?R1\<union>?R2)"  assume "\<not>(length ts \<ge>2)"
    then have "length ts = 1" using length_0_conv[of ts] a1 by linarith
    then have "hd ts = last ts" using length_Suc_conv[of ts 0] by auto
    then show False using a1 ss1 by simp      
  qed
  obtain w w' Ctx' \<theta> where ww':"(w,w')\<in>?H i \<and> Ctx'\<langle>w\<cdot>\<theta>\<rangle> = s \<and> Ctx'\<langle>w'\<cdot>\<theta>\<rangle> = s1" using assms(1) by auto
  then have gCww':"ground Ctx'\<langle>w\<cdot>\<theta>\<rangle>""ground Ctx'\<langle>w'\<cdot>\<theta>\<rangle>" using assms(3) assms(4) by auto
  then have gC:"ground_ctxt Ctx'" by simp
  have gws:"ground (w\<cdot>\<theta>)" "ground (w'\<cdot>\<theta>)" using gCww' by auto
  then have g\<theta>:"ground_subst (\<theta>|s (vars_term w\<union>vars_term w'))" by auto
  then have g\<theta>\<sigma>:"ground_subst ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" using assms(2) assms(3) 
  proof -
    have *:"\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) . ground (\<theta> v)" using g\<theta> by simp
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')).  ground ((\<theta> v)\<cdot>\<sigma>)" 
      by (simp add: ground_subst_apply)
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')). ground ((\<theta>\<circ>\<^sub>s\<sigma>) v)" using subst_compose[of \<theta> \<sigma>] by simp
    also have "subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) = subst_domain ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" 
      using gws * g\<theta>
      by (metis (no_types, lifting) ground_subst_apply ground_subst_domain_is_vars_term subst_compose subst_ext)
    ultimately show ?thesis by simp
  qed
  let ?\<rho> = "((\<theta>\<circ>\<^sub>s\<sigma>) |s (vars_term w \<union>vars_term w'))"
  have "w\<cdot>?\<rho> = w\<cdot>(\<theta>\<circ>\<^sub>s\<sigma>)" "w'\<cdot>?\<rho> = w'\<cdot>(\<theta>\<circ>\<^sub>s\<sigma>)" using coincidence_lemma'[of w "vars_term w\<union>vars_term w'" ] apply blast
    using coincidence_lemma'[of w' "vars_term w\<union>vars_term w'" ] by blast
  then have "w\<cdot>?\<rho> = (w\<cdot>\<theta>)\<cdot>\<sigma>" "w'\<cdot>?\<rho> = (w'\<cdot>\<theta>)\<cdot>\<sigma>" by auto
  then have w\<rho>w\<theta>:"w\<cdot>?\<rho> = (w\<cdot>\<theta>) \<and> w'\<cdot>?\<rho> = (w'\<cdot>\<theta>)" using ground_subst_apply[of "w\<cdot>\<theta>" \<sigma>] ground_subst_apply[of "w'\<cdot>\<theta>" \<sigma>] gws by argo
  then have gw\<rho>:"ground (w \<cdot> ?\<rho>) \<and> ground (w' \<cdot> ?\<rho>)" using gws by argo
  also then have gCw\<rho>:"ground Ctx'\<langle>w\<cdot>?\<rho>\<rangle> \<and>ground Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" using gC by simp
  have "ground_subst ((\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w')) |s (vars_term w \<union> vars_term w')) " using g\<theta>\<sigma> by simp
  ultimately have dom:"subst_domain (?\<rho> |s (vars_term w \<union>vars_term w')) =  vars_term w \<union> vars_term w' " 
    using ground_subst_domain_is_vars_term[of ?\<rho> w w'] by fast
  then have domrl:"vars_term w \<union> vars_term w' \<subseteq>subst_domain (?\<rho> |s (vars_term w \<union>vars_term w'))" by simp
  consider "gc_subst C ((\<theta>\<circ>\<^sub>s\<sigma>)|s vars_term w)"|"\<not>gc_subst C ((\<theta>\<circ>\<^sub>s\<sigma>)|s vars_term w)" by auto
  then show ?thesis
  proof cases
    case 1
    then have "(w,w')\<in>?H i" using ww' by simp
    then obtain j E' where E':" j<i \<and> ((w,w'),E')\<in> expand_eq_set (?H j) \<and> ?E (j+1) = ?E j-{(w,w'),(w',w)}\<union>E' "
      using all_H_eq_expanded[of rirun] assms(5) assms(6) assms(7) by blast
    then obtain Cx where Cx: "Cx\<in>basic_ctxts w \<and> 
        (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx w w' \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* 
            \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))"
      using expand_eq_set basic_ctxt_subts by auto
    then have "\<exists>u. (w = Cx\<langle>u\<rangle>) \<and> u \<in> basic_subts w" using  basic_ctxt_subts by auto
    then obtain u where u:"u\<in>basic_subts w" and Cxu: "w = Cx\<langle>u\<rangle>"
      using expand_eq_set basic_ctxt_subts by auto
    then have "u\<in>basic_subts w" by simp
    also have "gc_subst C (?\<rho> |s vars_term w)" using 1 by simp
    moreover have "vars_term w  \<union> vars_term w' = subst_domain ?\<rho>" using dom by simp 
    ultimately have "(w\<cdot>?\<rho>,w'\<cdot>?\<rho>)\<in>((rstep R) O (rstep (Expd_rename Cx w w')))" 
      using Cx expd_prop'[of Cx w ?\<rho> w'] by blast
    then obtain w\<^sub>i where w\<^sub>i:"(w\<cdot>?\<rho>, w\<^sub>i)\<in>(rstep R) \<and> (w\<^sub>i,w'\<cdot>?\<rho>)\<in>(rstep (Expd_rename Cx w w'))" by blast
    then have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx'\<langle>w\<^sub>i\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>(rstep (Expd_rename Cx w w'))" by auto
    from this(2) obtain w\<^sub>ir Ctx'' \<theta> w'\<^sub>ir where w\<^sub>ir:"(w\<^sub>ir, w'\<^sub>ir)\<in>Expd_rename Cx w w' \<and> Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx'\<langle>w\<^sub>i\<rangle> \<and> Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" 
      apply (rule rstepE) by metis
    have "?E (j+1) = ?E j-{(w,w'),(w',w)}\<union>E'" using E' by simp
    then obtain w\<^sub>i' where w\<^sub>i':" (w\<^sub>ir, w\<^sub>i')\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (w\<^sub>i',w'\<^sub>ir)\<in>E' "  using E' w\<^sub>ir Cx  by blast
    then have cs\<^sub>i':"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
    proof -
      have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)" by auto
      also have "\<forall>s t. (s,t)\<in>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
      ultimately have "\<forall>s t . (s,t)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (Ctx''\<langle>s\<cdot>\<theta>\<rangle>,Ctx''\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
      then have "(w\<^sub>ir,w\<^sub>i')\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
        using  rtrancl_closed_ctxt_subst[of "((rstep (?H j))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx'' \<theta> w\<^sub>ir w\<^sub>i'] by blast
      then show ?thesis using w\<^sub>i' by fast
    qed
    also have HEinf:"(rstep (?H j))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep assms(5) assms(6) E' assms(7) by simp
    then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
    then have "((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
    ultimately have t1:"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
    note HEinf then have "(rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
    then have"((rstep (?H j))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
    then have t2:"(Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
    then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
      using rtrancl_iff_derivation[of "Ctx''\<langle>w\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
    then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
    have "(w\<^sub>i',w'\<^sub>ir)\<in>E'" using w\<^sub>i' w\<^sub>ir Cx by blast
    also have "E'\<subseteq>?E (j+1)" using E' by simp
    moreover have "j+1\<le> fst rirun" using E' assms(7) by simp
    ultimately have "(w\<^sub>i',w'\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
    then have "(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx''\<langle>w'\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
    then have w\<^sub>i'w':"(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun) " using w\<^sub>ir by argo
    have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<^sub>i\<rangle>)\<in>rstep R" "(Ctx'\<langle>w\<^sub>i\<rangle>,Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>rstep (Einf rirun)"
      using w\<^sub>i apply auto[1] using w\<^sub>ir t2 apply simp using w\<^sub>i'w' by simp
    also have "(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>)\<in>S" using ww' assms(1) w\<rho>w\<theta> by simp
    ultimately have "\<exists>xs. xs \<noteq> [] \<and>
               hd xs = Ctx'\<langle>w\<cdot>?\<rho>\<rangle> \<and>
               last xs = Ctx'\<langle>w'\<cdot>?\<rho>\<rangle> \<and>
               is_proof_of xs (rstep R \<union> rstep (Einf rirun)) \<and>
               (\<forall>i<length xs. (Ctx'\<langle>w\<cdot>?\<rho>\<rangle>, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) \<and>
               (\<forall>i<length xs. xs ! i \<in> ground_terms) \<and>
               (\<forall>i<length xs - 1.
               (xs ! i, xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
                   ({#Ctx'\<langle>w\<cdot>?\<rho>\<rangle>, t#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext NS S)"
      using expand_r1r2_case'[of "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w\<^sub>i\<rangle>" "Ctx''\<langle>w\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" t] gCw\<rho> by blast
    then show ?thesis using ww' w\<rho>w\<theta> tslength by auto
  next
    case 2
    then have a':"ground_subst (?\<rho>|s (vars_term w \<union> vars_term w'))" "\<not>constr_subst C (?\<rho>|s (vars_term w))" using g\<theta>\<sigma> 2 by auto
    have "ground_subst (?\<rho>|s (vars_term w \<union> vars_term w'))" "\<not>constr_subst C (?\<rho>|s (vars_term w \<union> vars_term w'))" using a' by auto
    then have "\<exists>\<rho>. ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^+) \<and> 
                ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^* \<and> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term w\<union> vars_term w')) "
      using domrl DC4 RI2 SN_rstep_R TRS2 ground_not_constr_subst_rewritable'[of ?\<rho> w w' R D C ] by blast
    then obtain \<rho> where gcs\<rho>:"((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^+) \<and> 
                ((w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^* \<and> (w'\<cdot>?\<rho>,w'\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term w\<union> vars_term w')) " by blast
    then have \<rho>:"((Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+ \<or> (Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+) \<and> 
                  ((Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)^* \<and> (Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep R)^*)" 
      using rsteps_closed_ctxt[of _ _ R] trancl_rstep_ctxt[of _ _ R] by meson
    have "(w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^+"
    proof (rule ccontr)
      assume "(w\<cdot>?\<rho>,w\<cdot>\<rho>)\<notin>(rstep R)^+"
      also have "(w\<cdot>?\<rho>,w\<cdot>\<rho>)\<in>(rstep R)^*" using gcs\<rho> by blast
      ultimately have "w\<cdot>?\<rho> =w\<cdot>\<rho> " using rtrancl_not_trancl_imp_eq[of "w\<cdot>?\<rho>" "w\<cdot>\<rho>" "rstep R"] by blast
      then have "\<forall>v\<in>vars_term w. ?\<rho> v = \<rho> v " using term_subst_eq_rev by blast
      also obtain v where v:"v\<in>subst_domain (?\<rho>|s vars_term w) \<and> \<not>constr C (?\<rho> v) " using 2 a'(2) by fastforce 
      { then have "v\<in>subst_domain (\<rho>|s vars_term w) \<longrightarrow>  constr C (\<rho> v)" using gcs\<rho> domrl by simp
        then have "v\<in>subst_domain (\<rho>|s vars_term w) \<longrightarrow>  (\<rho>|s vars_term w) v \<noteq> (?\<rho>|s vars_term w) v" using v by auto
        also have "v\<notin>subst_domain (\<rho>|s vars_term w) \<longrightarrow>  (\<rho>|s vars_term w) v = Var v" using subst_domain_def[of "\<rho>|s vars_term w"] by simp
        then have "v\<notin>subst_domain (\<rho>|s vars_term w) \<longrightarrow>  (\<rho>|s vars_term w) v \<noteq> (?\<rho>|s vars_term w) v" using v by auto
        ultimately have "(\<rho>|s vars_term w) v \<noteq> (?\<rho>|s vars_term w) v" by auto
      }
      then have " (\<exists>v\<in>vars_term w. (?\<rho>|s vars_term w) v  \<noteq> (\<rho>|s vars_term w) v)" using v by force
      ultimately show False by simp
    qed
    then have fa:"(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+" using trancl_rstep_ctxt by auto
    then have *:"(Ctx'\<langle>w\<cdot>\<rho>\<rangle>,Ctx'\<langle>w'\<cdot>\<rho>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using ww' asm6 by fast 
    then show ?thesis
    proof -
      have fa:"(Ctx'\<langle>w\<cdot>?\<rho>\<rangle>,Ctx'\<langle>w\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+" using fa by auto
      also have "(Ctx'\<langle>w\<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle>)\<in>S" 
      proof -
        have "(Ctx'\<langle>w\<cdot>\<theta>\<rangle>,Ctx'\<langle>w'\<cdot>\<theta>\<rangle>)\<in>S" using assms(1) ww' by simp
        also have "Ctx'\<langle>w\<cdot>?\<rho>\<rangle> = Ctx'\<langle>w\<cdot>\<theta>\<rangle>" "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle> = Ctx'\<langle>w'\<cdot>\<theta>\<rangle>" using w\<rho>w\<theta> by auto
        ultimately show ?thesis by simp
      qed
      moreover have "(Ctx'\<langle>w' \<cdot> \<rho>\<rangle>, Ctx'\<langle>w \<cdot> \<rho>\<rangle>) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using * by auto
      moreover then have " ((Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+ \<or> (Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+) \<and>
                       (Ctx'\<langle>w' \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w' \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>* \<and> (Ctx'\<langle>w \<cdot> ?\<rho>\<rangle>, Ctx'\<langle>w \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>*" using \<rho> by meson
      ultimately obtain xs where "xs \<noteq> [] \<and>
               hd xs = Ctx'\<langle>w \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle> \<and>
               last xs = Ctx'\<langle>w' \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle> \<and>
               is_proof_of xs (rstep R \<union> rstep (Einf rirun)) \<and>
               (\<forall>i<length xs. (Ctx'\<langle>w \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>, xs ! i) \<in> NS \<union> S \<or> (t, xs ! i) \<in> NS \<union> S) \<and>
               (\<forall>i<length xs. xs ! i \<in> ground_terms) \<and>
               (\<forall>i<length xs - 1.
               (xs ! i, xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
                   ({#Ctx'\<langle>w \<cdot> (\<theta> \<circ>\<^sub>s \<sigma> |s (vars_term w \<union> vars_term w'))\<rangle>, t#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext NS S)"
        using gc\<rho>_case'[of "Ctx'\<langle>w\<cdot>\<rho>\<rangle>" "Ctx'\<langle>w'\<cdot>\<rho>\<rangle>"rirun "Ctx'\<langle>w\<cdot>?\<rho>\<rangle>" "Ctx'\<langle>w'\<cdot>?\<rho>\<rangle>" t] \<rho> gCw\<rho> by blast
      then show ?thesis using w\<rho>w\<theta> ww' tslength by auto
    qed
  qed
qed

lemma simplify_r1r2_case:
  assumes "(s,s1)\<in>(rstep (snd (snd rirun i)))" "(s1,s2)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
    "(s2,t)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" "ground s" "ground t" "(s,s1)\<in>S" "ri_run rirun" "i< fst rirun" "snd (snd rirun 0) = {}"
    and "gc_subst C (\<sigma>::('a,'b)subst)" 
  shows "(s,t)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"  
proof -
  let ?R1 = "rstep R" let ?R2 = "rstep (Einf rirun)" let ?H = "\<lambda>i. snd (snd rirun i)"
  have "(s,s1)\<in>(rstep (snd (snd rirun i)))" using assms(1) by simp
  also have i:"i\<le> fst rirun" using assms(8) by simp
  ultimately have sEs1:"(s,s1)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(7) assms(8) assms(9) rirun_H_subset_Einf_rstep[of rirun] by blast
  have HsubEinf:"(?H i)\<^sup>\<leftrightarrow> \<subseteq> (Einf rirun)\<^sup>\<leftrightarrow>" using assms(7) assms(8) assms(9) rirun_H_subset_Einf[of rirun] by simp
  have *:"(\<exists>xs.  xs\<noteq>[]  \<and> hd xs = s \<and> last xs = t \<and> 
            is_proof_of xs (?R1\<union>?R2) \<and>
            (\<forall>i<length xs .  (s,(xs!i))\<in>(NS\<union>S) \<or> (t,(xs!i))\<in>NS\<union>S) \<and> (\<forall>i<length xs .  (xs!i)\<in>ground_terms) \<and>
            (\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext NS S)) \<longrightarrow> ?thesis" by simp
  obtain ss where ss:" ss\<noteq>[]  \<and> hd ss = s1 \<and> last ss = s2 \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
    using assms(2) rtrancl_iff_derivation[of s1 s2 "(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))"] by blast
  obtain w w' Ctx' \<theta> where ww':"(w,w')\<in>(?H i) \<and> Ctx'\<langle>w\<cdot>\<theta>\<rangle> = s \<and> Ctx'\<langle>w'\<cdot>\<theta>\<rangle> = s1" using assms(1) by auto
  also have asm5:"ground s1" using assms(4) assms(6) ground_S by blast
  ultimately have gCww':"ground Ctx'\<langle>w\<cdot>\<theta>\<rangle>""ground Ctx'\<langle>w'\<cdot>\<theta>\<rangle>" using assms(4) asm5 by auto
  then have gC:"ground_ctxt Ctx'" by simp
  have gws:"ground (w\<cdot>\<theta>)" "ground (w'\<cdot>\<theta>)" using gCww' by auto
  then have g\<theta>:"ground_subst (\<theta>|s (vars_term w\<union>vars_term w'))" by auto
  then have g\<theta>\<sigma>:"ground_subst ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" using assms(2) assms(3)  
  proof -
    have *:"\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) . ground (\<theta> v)" using g\<theta> by simp
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')).  ground ((\<theta> v)\<cdot>\<sigma>)" 
      by (simp add: ground_subst_apply)
    then have "\<forall>v\<in>subst_domain (\<theta>|s (vars_term w\<union> vars_term w')). ground ((\<theta>\<circ>\<^sub>s\<sigma>) v)" using subst_compose[of \<theta> \<sigma>] by simp
    also have "subst_domain (\<theta>|s (vars_term w\<union> vars_term w')) = subst_domain ((\<theta>\<circ>\<^sub>s\<sigma>)|s (vars_term w\<union>vars_term w'))" 
      using gws * g\<theta>
      by (metis (no_types, lifting) ground_subst_apply ground_subst_domain_is_vars_term subst_compose subst_ext)
    ultimately show ?thesis by simp
  qed
  have "(s,s1)\<in>(rstep (snd (snd rirun i)))\<inter>S" using assms(1) assms(6) by blast
  also have "gc_subst C \<sigma>"  using assms(10) by simp
  moreover have "ground s" using assms(4) by blast
  moreover have "ground s1" using asm5 by simp
  moreover have "snd (snd rirun 0) = {}" "ri_run rirun" "i<fst rirun" using assms(7,8,9) by auto
  ultimately have "\<exists>ts. length ts\<ge>2 \<and> hd ts = s \<and> last ts = s1 \<and> is_proof_of ts (?R1\<union>?R2) \<and> (\<forall>i<length ts .  (ts!i)\<in>ground_terms) \<and>
        (\<forall>i<length ts. (s,ts!i)\<in>NS\<union>S \<or> (t,ts!i)\<in>NS\<union>S) \<and>
        (\<forall>i<length ts -1. (ts!i,ts!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#ts!i,ts!(i+1)#})\<in>s_mul_ext NS S)" 
    using simplify_b[of s s1 rirun i \<sigma>] by presburger
  then obtain ts where ts:"length ts\<ge>2 \<and>hd ts = s \<and> last ts = s1" "is_proof_of ts (?R1\<union>?R2)" "(\<forall>i<length ts .  (ts!i)\<in>ground_terms)"
    "(\<forall>i<length ts. (s,ts!i)\<in>NS\<union>S \<or> (t,ts!i)\<in>NS\<union>S)"
    "(\<forall>i<length ts -1. (ts!i,ts!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#ts!i,ts!(i+1)#})\<in>s_mul_ext NS S)" by blast
  let ?ts = "(take (length ts -1) ts)"
  have ts'nil:"?ts\<noteq>[]" using ts by fastforce
  then have "last ?ts = ?ts!(length ?ts-1)" 
    using last_conv_nth[of ?ts] by simp
  also have "length ?ts-1 = length ts - 1 -1 " by fastforce
  moreover have " length ts - 1 -1 <  length ts - 1 " using ts(1) by linarith
  then have "?ts!(length ts - 1 -1) = ts!(length ts -1-1)" 
    using nth_take[of"length ts -1-1" "length ts-1"] by fast
  ultimately have lastts:"last ?ts = ts!(length ts -1-1)" by argo
  also have "(length ts -1 -1) < length ts -1" using ts(1) by fastforce
  then have "(ts!(length ts -1 -1),ts!(length ts -1-1+1))\<in> (?R1\<union>?R2)\<^sup>\<leftrightarrow>" using ts(2) by simp
  {
    also have "length ts -1 -1 +1 = length ts -1" using ts(1) by linarith
    ultimately have "(ts!(length ts -1 -1),ts!(length ts -1))\<in> (?R1\<union>?R2)\<^sup>\<leftrightarrow>" using ts(1) by simp}
  moreover have "ts\<noteq>[]" using ts(1) by auto
  ultimately have "(last ?ts,last ts)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow> " using ts(1) last_conv_nth[of ts] by simp
  then have h:"(last ?ts,s1)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow> " using ts(1) by simp

  have ts':"?ts\<noteq>[] \<and> hd ?ts = s \<and> last ?ts = last ?ts" "is_proof_of ?ts (?R1\<union>?R2)" "(\<forall>i<length ?ts .  (s,(?ts!i))\<in>(NS\<union>S) \<or> (t,(?ts!i))\<in>NS\<union>S)"
    "(\<forall>i<length ?ts .  (?ts!i)\<in>ground_terms)"
    "(\<forall>i<length ?ts -1. (?ts!i,?ts!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?ts!i,?ts!(i+1)#})\<in>s_mul_ext NS S)" 
  proof -
    have " hd ?ts = s" using hd_conv_nth[of ?ts] nth_take[of 0 "length ts -1" ts] hd_conv_nth[of ts] using ts(1) by force
    then show "?ts\<noteq>[] \<and> hd ?ts = s \<and> last ?ts = last ?ts" using ts'nil by simp
    have "ts = ?ts@(drop (length ts-1) ts)" by simp
    then show "is_proof_of ?ts (?R1\<union>?R2)" using app_subproof_is_proof[of ?ts "drop (length ts-1) ts" "?R1\<union>?R2"] using ts(2) by argo
    show "(\<forall>i<length ?ts .  (s,(?ts!i))\<in>(NS\<union>S) \<or> (t,(?ts!i))\<in>NS\<union>S)" using ts(4) by simp
    show "(\<forall>i<length ?ts .  (?ts!i)\<in>ground_terms)" using ts(3) by simp
    show "(\<forall>i<length ?ts -1. (?ts!i,?ts!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?ts!i,?ts!(i+1)#})\<in>s_mul_ext NS S)"
      using ts(5) by auto 
  qed
  let ?xs =  "?ts@ss@[t]"
  have t1:" ?xs\<noteq>[]  \<and> hd ?xs = s \<and> last ?xs = t " using ts' by simp
  have t2: "is_proof_of ?xs (?R1\<union>?R2)" 
  proof -
    have "\<forall>i<length ss - 1. (ss ! i, ss ! (i+1)) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" using ss is_derivation_of_def[of ss "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by simp
    then have "\<forall>i<length ss - 1. case (ss ! i, ss ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by blast
    also have "\<forall>i<length [t] - 1. case ([t] ! i, [t] ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" by simp
    moreover have " case (last ss, hd [t]) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms(3) ss by fastforce
    moreover have "ss\<noteq>[]" "[t]\<noteq>[]" using ss by auto 
    ultimately have "\<forall>i<length (ss @ [t]) - 1. case ((ss @ [t]) ! i, (ss @ [t]) ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" 
      using app_P_sublemma[of ss "\<lambda>(x,y). (x,y)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow>" "[t]"] by fastforce
    also have "\<forall>i<length ?ts - 1. case (?ts ! i, ?ts ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (rstep R \<union> rstep (Einf rirun))\<^sup>\<leftrightarrow>" using ts' by auto
    moreover have "?ts \<noteq>[]" "ss@[t] \<noteq>[]" using ts'nil by auto
    moreover have "hd (ss@[t]) = hd ss" using ss(1) by simp
    then have "(last ?ts,hd (ss@[t]))\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow>" using h ss(1) by simp
    ultimately have " \<forall>i<length (?xs) - 1.
       case (?xs! i, ?xs ! (i + 1)) of (x, y) \<Rightarrow> (x, y) \<in> (?R1\<union>?R2)\<^sup>\<leftrightarrow>" using app_P_sublemma[of ?ts "\<lambda>(x,y). (x,y)\<in>(?R1\<union>?R2)\<^sup>\<leftrightarrow>" "ss@[t]"] by fast
    then show ?thesis by force
  qed
  have t3:"(\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S)" "(\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms)"
  proof -
    have "\<forall>x\<in>set ?ts.  (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" "(\<forall>x\<in>set ?ts .  x\<in>ground_terms)"using ts'(3) ts'(4) all_set_conv_all_nth[of ?ts] by auto
    also have "\<forall>x\<in> set ss.(s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" "(\<forall>x\<in>set ss .  x\<in>ground_terms)"
    proof -
      have "(s,hd ss)\<in>S \<or> (t,hd ss)\<in>S" using assms(6) ss by simp
      also have "\<forall>a b. ((s, a) \<in> NS \<union> S \<or> (t, a) \<in> NS \<union> S) \<and> (a, b) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S) \<longrightarrow> (s, b) \<in> NS \<union> S \<or> (t, b) \<in> NS \<union> S"
      proof -
        have "\<forall>a b. (a,b)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S) \<longrightarrow> (a,b)\<in>NS\<union>S" by simp
        then show ?thesis using trans transD[of "NS\<union>S"] by meson
      qed       
      ultimately have "\<forall>i<length ss .  (s,(ss!i))\<in>(NS\<union>S) \<or> (t,(ss!i))\<in>NS\<union>S" 
        using derivation_propagation[of "\<lambda>x.  (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by blast
      then show "\<forall>x\<in> set ss.(s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" using all_set_conv_all_nth[of ss] by simp
      have shdss:"(s, hd ss)\<in>S" using assms(6) ss by simp
      also have "is_derivation_of ss (NS\<union>S)" using ss by simp
      then have "\<forall>i<length ss. (ss!0,ss!i)\<in>(NS\<union>S)" using derivation_all_NS_S by blast
      then have "\<forall>i<length ss. (s,ss!i)\<in>S" using S_NS_S_S[of s] shdss hd_conv_nth[of ss] ss by metis
      then have "\<forall>i<length ss. ground (ss!i)" using assms(4) ground_S by blast
      ultimately show "\<forall>x\<in>set ss. x\<in>ground_terms" 
        using all_set_conv_all_nth[of ss] by simp
    qed
    moreover have "\<forall>x\<in>set [t]. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" "(\<forall>x\<in>set [t].  x\<in>ground_terms)"using refl_NS_S refl_onD[of UNIV "NS\<union>S" t] assms(5) by auto
    ultimately have *:"\<forall>x\<in>set ?xs. (s,x)\<in>(NS\<union>S) \<or> (t,x)\<in>NS\<union>S" "(\<forall>x\<in>set ?xs.  x\<in>ground_terms)" by auto
    then show "(\<forall>i<length ?xs .  (s,(?xs!i))\<in>(NS\<union>S) \<or> (t,(?xs!i))\<in>NS\<union>S)" "(\<forall>i<length ?xs .  (?xs!i)\<in>ground_terms)" 
      using all_set_conv_all_nth [of ?xs] apply fast using all_set_conv_all_nth[of ?xs] *(2)  by presburger
  qed
  have t4:"(\<forall>i<length ?xs -1. (?xs!i,?xs!(i+1))\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#?xs!i,?xs!(i+1)#})\<in>s_mul_ext NS S)"
  proof-
    let ?t = "\<lambda>x y. (x,y)\<notin>?R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#s,t#},{#x,y#})\<in>s_mul_ext NS S"
    have "\<forall>i<length ?ts-1. ?t (?ts!i) (?ts!(i+1))" using ts'(5) by blast
    also {
      have "\<forall>x t. (s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (s,t)\<in>S"
      proof (intro allI impI)
        fix x t assume a:"(s,x)\<in>S \<and> (x,t)\<in>((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"
        then have t:"(x,t)\<in>(NS\<union>S)" by simp
        then show "(s,t)\<in>S" 
        proof (cases "(x,t)\<in>S")
          case True
          then show ?thesis using trans_S transD[of S s x t ] a by simp
        next
          case False
          then have "(x,t)\<in>NS" using t by simp
          then have "(s,t)\<in>S O NS " using a by auto
          then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
        qed
      qed
      then have S:"\<forall>i<length ss. (s,ss!i)\<in>S" using assms(6) using  derivation_propagation[of "\<lambda>x. (s,x)\<in>S" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" ss] ss by argo
      then have "\<forall>i<length ss-1. ?t (ss!i) (ss!(i+1))"
      proof -  
        have "\<forall>i<length ss-1. ({#s,t#},{#ss!i, ss!(i+1)#})\<in>s_mul_ext NS S" using stricts_s_mul_ext S by force           
        then show ?thesis by simp
      qed
      also have "\<forall>i<length [t]-1. ?t ([t]!i) ([t]!(i+1))" by simp
      moreover have "(s,last ss)\<in>S" using S ss last_conv_nth[of ss] by fastforce
      then have "({#s,t#},{#last ss,t#})\<in>s_mul_ext NS S" using one_same_s_mul_ext by simp
      then have "?t (last ss) (hd [t]) " by simp
      ultimately have "\<forall>i<length (ss@[t])-1. ?t ((ss@[t])!i) ((ss@[t])!(i+1))" using app_P_sublemma[of ss "\<lambda>(x,y). ?t x y" "[t]"] ss by auto
    }
    moreover have "?t (last ?ts) (hd ss)" using ts 
    proof - 
      have "last ?ts = ts!(length ts-1-1)" using lastts by simp
      also 
      { have "hd ss = s1 " using ss by simp
        also have "ts!(length ts-1) = last ts" using last_conv_nth[of ts] ts(1) by fastforce
        ultimately have "ts!(length ts-1) = hd ss" using ts(1) by simp
      }
      moreover
      { have "length ts-1-1 < length ts-1" using ts(1) by auto
        also then have  "(ts ! (length ts-1-1 ), ts ! (length ts-1-1 +1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
                         ({#s, t#}, {#ts ! (length ts-1-1), ts ! (length ts-1-1 + 1)#}) \<in> s_mul_ext NS S" using ts(5) by blast
        moreover have "length ts -1-1 +1 = length ts -1" using ts(1) by linarith
        ultimately have "?t (ts ! (length ts-1-1 )) (ts ! (length ts-1))" by simp
      }
      ultimately show "?t (last ?ts) (hd ss)" by simp
    qed
    then have "?t (last ?ts) (hd (ss@[t]))" using ss by simp
    moreover have "?ts \<noteq>[]" "ss@[t]\<noteq>[]" using ts'nil by auto
    ultimately show ?thesis using app_P_sublemma[of ?ts "\<lambda>(x,y). ?t x y" "ss@[t]"] by fast
  qed
  have "?xs \<noteq> [] \<and>
          hd ?xs = s \<and>
          last ?xs = t \<and>
          is_proof_of ?xs (rstep R \<union> rstep (Einf rirun)) \<and>
          (\<forall>i<length ?xs. (s, ?xs ! i) \<in> NS \<union> S \<or> (t, ?xs ! i) \<in> NS \<union> S) \<and>
          (\<forall>i<length ?xs. ?xs ! i \<in> ground_terms) \<and>
          (\<forall>i<length ?xs - 1. (?xs ! i, ?xs ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow> ({#s, t#}, {#?xs ! i, ?xs ! (i + 1)#}) \<in> s_mul_ext NS S)" using t1 t2 t3 t4 by meson
  then show ?thesis using r1r2_on_intro[of ?xs s t ?R1 ?R2 NS S ground_terms] by fast
qed      


lemma lemma8:
  assumes "ground s\<^sub>g" and "ground t\<^sub>g" and "(s\<^sub>g,t\<^sub>g)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" 
    and "full_ri_run E\<^sub>0 rirun"
  shows "(s\<^sub>g,t\<^sub>g)\<in> (R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms)"
proof -
  have assms4: "fst (snd rirun (fst rirun)) = {}" using assms full_ri_run_def by auto
  have assms5: "ri_run rirun" using assms full_ri_run_def by auto
  have "snd rirun 0 = (fst (snd rirun 0), {})" using assms full_ri_run_def by auto
  then have assms6: "snd (snd rirun 0) = {}" using BNF_Def.sndI by fastforce
  have fair: "fair rirun" using fair_iff assms4 by auto
  obtain s t Ctx and \<sigma>::"('a,'b)subst" where st:"((s,t)\<in>Einf rirun \<or> (t,s)\<in>Einf rirun) \<and> Ctx\<langle>s\<cdot>\<sigma>\<rangle> = s\<^sub>g \<and> Ctx\<langle>t\<cdot>\<sigma>\<rangle> = t\<^sub>g" using assms by blast
  then have gCtxsts:"ground Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> ground Ctx\<langle>t\<cdot>\<sigma>\<rangle>" using assms by simp
  then have gsts:"ground (s\<cdot>\<sigma>) \<and> ground (t\<cdot>\<sigma>)" by simp
  then have gCtx:"ground_ctxt Ctx" using gCtxsts by simp
  then have g\<sigma>:"ground_subst (\<sigma> |s (vars_term s \<union>vars_term t))" 
    using gCtxsts st assms(1) assms(2) empty_iff ground_subst.simps ground_vars_term_empty subst_domain_Var subst_restrict_empty sup_bot.left_neutral
  proof -
    obtain bb :: "('b \<Rightarrow> ('a, 'b) Term.term) \<Rightarrow> ('a, 'b) Term.term \<Rightarrow> 'b" where
      "\<forall>x0 x1. (\<exists>v2. v2 \<in> vars_term x1 \<and> \<not> ground (x0 v2)) = (bb x0 x1 \<in> vars_term x1 \<and> \<not> ground (x0 (bb x0 x1)))"
      by moura
    then have f1: "\<forall>t f. (\<not> ground (t \<cdot> f) \<or> (\<forall>b. b \<notin> vars_term t \<or> ground (f b))) \<and> (ground (t \<cdot> f) \<or> bb f t \<in> vars_term t \<and> \<not> ground (f (bb f t)))"
      by (metis (no_types) ground_subst)
    obtain bba :: "('b \<Rightarrow> ('a, 'b) Term.term) \<Rightarrow> 'b" where
      "\<forall>f. (\<not> ground_subst f \<or> (\<forall>b. b \<notin> subst_domain f \<or> ground (f b))) \<and> (ground_subst f \<or> bba f \<in> subst_domain f \<and> \<not> ground (f (bba f)))"
      by moura
    moreover
    { assume "bba (\<sigma> |s (vars_term s \<union> vars_term t)) \<notin> vars_term s \<union> vars_term t"
      then have "bba (\<sigma> |s (vars_term s \<union> vars_term t)) \<notin> subst_domain (\<sigma> |s (vars_term s \<union> vars_term t)) \<or> ground ((\<sigma> |s (vars_term s \<union> vars_term t)) (bba (\<sigma> |s (vars_term s \<union> vars_term t))))"
        by (simp add: subst_domain_def) }
    ultimately show ?thesis
      using f1 by (metis (no_types) gCtxsts Un_iff ground_ctxt_apply subst_restrict_def)
  qed  
  then have dom:"subst_domain (\<sigma> |s (vars_term s \<union>vars_term t)) = vars_term s \<union> vars_term t " using gsts by (rule ground_subst_domain_is_vars_term)      
  then have domrl:" vars_term s \<union> vars_term t \<subseteq>subst_domain (\<sigma> |s (vars_term s \<union>vars_term t))" by auto
  consider (gc\<rho>)"\<not>gc_subst C (\<sigma> |s (vars_term s \<union>vars_term t))" |(gc\<sigma>) "gc_subst C (\<sigma> |s (vars_term s \<union>vars_term t))"by blast
  then show ?thesis 
  proof cases
    case gc\<rho>
    then have "\<not>constr_subst C (\<sigma> |s (vars_term s \<union>vars_term t))" "ground_subst (\<sigma> |s (vars_term s \<union>vars_term t))" using gc\<rho> g\<sigma> apply simp using g\<sigma> by simp
    then have "\<exists>\<rho>. ((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^+) \<and> ((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^* \<and> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term s\<union> vars_term t)) " 
      using domrl DC4 RI2 SN_rstep_R TRS2 by (intro ground_not_constr_subst_rewritable') 
    then obtain \<rho> where gcs\<rho>:"((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^+) \<and> ((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^* \<and> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst C (\<rho>|s (vars_term s\<union> vars_term t)) " by blast
    then have \<rho>:"((Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+ \<or> (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+) \<and> ((Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<rho>\<rangle>)\<in>(rstep R)^* \<and> (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<cdot>\<rho>\<rangle>)\<in>(rstep R)^*)" by (metis rsteps_closed_ctxt trancl_rstep_ctxt) 
    then have *:"(Ctx\<langle>s\<cdot>\<rho>\<rangle>,Ctx\<langle>t\<cdot>\<rho>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using st by fast
    then show ?thesis
    proof (cases "(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<cdot>\<rho>\<rangle>)\<in>(rstep R)^+")
      case True
      also have "(Ctx\<langle>s \<cdot> \<rho>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using * by simp
      moreover then have " ((Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+ \<or> (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+) \<and>
                         (Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>* \<and> (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>*" using \<rho> by simp
      ultimately have "(Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
        using gc\<rho>_case[of  "Ctx\<langle>s\<cdot>\<rho>\<rangle>" "Ctx\<langle>t\<cdot>\<rho>\<rangle>"rirun "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" ] \<rho> gCtxsts by fast
      then show ?thesis using st by force
    next
      case False
      then have fa:"(Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<rho>\<rangle>)\<in>(rstep R)\<^sup>+" using \<rho> by auto
      also have "(Ctx\<langle>s \<cdot> \<rho>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using * by simp
      moreover then have " ((Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+ \<or> (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>+) \<and>
                         (Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>* \<and> (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<rho>\<rangle>) \<in> (rstep R)\<^sup>*" using \<rho> by simp
      ultimately have "(Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
        using gc\<rho>_case[of  "Ctx\<langle>t\<cdot>\<rho>\<rangle>" "Ctx\<langle>s\<cdot>\<rho>\<rangle>"rirun "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" ] \<rho> gCtxsts by fast
      then have "(t\<^sub>g,s\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"using st by force
      then show ?thesis using r1r2gtstar_on_rev[of t\<^sub>g s\<^sub>g NS S "rstep R" "rstep (Einf rirun)" ground_terms] by blast 
    qed
  next
    let ?E = "\<lambda>i. fst (snd rirun i)" let ?H = "\<lambda>i. snd (snd rirun i)"
    case gc\<sigma>
    have"(s,t)\<in> Einf rirun \<or> (t,s)\<in>Einf rirun" using st by simp
    also 
    {
      assume "(s,t)\<in>Einf rirun" 
      then have "\<exists>i<(fst rirun).  
          ((\<exists>E'. (((t,s),E')\<in>expand_eq_set (?H i) \<or> ((s,t),E')\<in>expand_eq_set (?H i)) \<and>
                ?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E') \<or> 
          (\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s'',t)} ) \<or> 
          (\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s,t'')} ) \<or>
          ((s,t)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(s,t)}))" using Einf_eq_cases fair assms5  by fast
      then obtain i where i:"i<fst rirun" 
        "(\<exists>E'. (((t,s),E')\<in>expand_eq_set (?H i) \<or> ((s,t),E')\<in>expand_eq_set (?H i)) \<and> ?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E') \<or> 
          (\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s'',t)} ) \<or> 
          (\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s,t'')} ) \<or>
          ((s,t)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(s,t)})" by force
      then consider (expand)"\<exists>E'. (((t,s),E')\<in>expand_eq_set ((?H i)) \<or> ((s,t),E')\<in>expand_eq_set ((?H i)))
                                \<and> ?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'" |
        (simplifyl)"\<exists>s''. ((s,t),(s'',t))\<in>simplifyl_eq (?H i) \<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s'',t)} " |
        (simplifyr)"\<exists>t''. ((s,t),(s,t''))\<in>simplifyr_eq (?H i) \<and>?E (i+1) = ?E i- {(s,t)} \<union>{(s,t'')}" |
        (delete)"(s,t)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(s,t)}" by fast
      then have ?thesis 
      proof cases
        case expand
        then obtain E' where E':" ((t,s),E')\<in>expand_eq_set (?H i) \<or> ((s,t),E')\<in>expand_eq_set (?H i)" "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'"
          using expand by blast
        then consider "((s,t),E')\<in>expand_eq_set (?H i)" | "((t,s),E')\<in>expand_eq_set (?H i) " by auto
        then show ?thesis 
        proof cases
          case 1
          then obtain Cx where Cx:"Cx\<in>basic_ctxts s \<and> 
                          (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx s t \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* 
                      \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))"
            using expand_eq_set by blast
          also have "gc_subst C ((\<sigma> |s (vars_term s \<union>vars_term t)) |s vars_term s)" using gc\<sigma> by simp
          ultimately have "(s\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)),t\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)))\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
            using expd_prop'[of Cx s "(\<sigma> |s (vars_term s \<union>vars_term t))"] dom g\<sigma> gc\<sigma> by presburger
          then have "(s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
            using coincidence_lemma'[of "s" "vars_term s\<union> vars_term t" \<sigma>] coincidence_lemma'[of "t" "vars_term s\<union> vars_term t" \<sigma>] by simp
          then obtain s\<^sub>i where "(s\<cdot>\<sigma>,s\<^sub>i)\<in>(rstep R)" "(s\<^sub>i,t\<cdot>\<sigma>)\<in>(rstep (Expd_rename Cx s t))" by auto
          then have s\<^sub>i:"(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx\<langle>s\<^sub>i\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Expd_rename Cx s t))" by auto
          from this(2) obtain s\<^sub>ir Ctx' \<theta> t\<^sub>ir where s\<^sub>ir:"(s\<^sub>ir, t\<^sub>ir)\<in>Expd_rename Cx s t \<and> Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx\<langle>s\<^sub>i\<rangle> \<and> Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx\<langle>t\<cdot>\<sigma>\<rangle>" 
            apply (rule rstepE) by metis
          have "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'" using E'(2) by simp
          then obtain s\<^sub>i' where s\<^sub>i':" (s\<^sub>ir, s\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (s\<^sub>i',t\<^sub>ir)\<in>E'"  
            using E' Cx s\<^sub>ir  by blast
          then have cs\<^sub>i':"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          proof -
            have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)" by auto
            also have "\<forall>s t. (s,t)\<in>(NS\<union>S) \<longrightarrow> (Ctx'\<langle>s\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
            ultimately have "\<forall>s t . (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (Ctx'\<langle>s\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
            then have "(s\<^sub>ir,s\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
              using  rtrancl_closed_ctxt_subst[of "((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx' \<theta> s\<^sub>ir s\<^sub>i'] by blast
            then show ?thesis using s\<^sub>i' by blast
          qed
          also have HEinf:"(rstep (?H i))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms5 assms6 i rirun_H_subset_Einf_rstep by simp
          then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          then have "((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
          ultimately have t1:"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
          note HEinf then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
          then have"((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
          then have t2:"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
          then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
            using rtrancl_iff_derivation[of "Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
          then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
          have "(s\<^sub>i',t\<^sub>ir)\<in>E'" using s\<^sub>i' s\<^sub>ir Cx by blast
          also have "E'\<subseteq>?E (i+1)" using E' by simp
          moreover have "i+1\<le> fst rirun" using i by simp
          ultimately have "(s\<^sub>i',t\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
          then have "(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
          then have s\<^sub>i't:"(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun) " using s\<^sub>ir by argo
          have "(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<^sub>i\<rangle>)\<in>rstep R" "(Ctx\<langle>s\<^sub>i\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun)"
            using s\<^sub>i apply simp using s\<^sub>ir t2 apply simp using s\<^sub>i't by simp
          then have "(Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" "Ctx\<langle>s\<^sub>i\<rangle>" "Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx\<langle>t\<cdot>\<sigma>\<rangle>"] gCtxsts by blast
          then show ?thesis using st by fast
        next
          case 2
          then obtain Cx where Cx:  "Cx\<in>basic_ctxts t \<and> 
                                        (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx t s \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* 
                                          \<and> (s\<^sub>i',t\<^sub>i)\<in>E'))"
            using expand_eq_set by blast
          also have "gc_subst C ((\<sigma> |s (vars_term s \<union>vars_term t))|s vars_term t)" using gc\<sigma> by simp
          ultimately have "(t\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)),s\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)))\<in>((rstep R) O (rstep (Expd_rename Cx t s)))" 
            using expd_prop[of Cx t "(\<sigma> |s (vars_term s \<union>vars_term t))" s] dom g\<sigma> gc\<sigma> by blast
          then have "(t\<cdot>\<sigma>,s\<cdot>\<sigma>)\<in>((rstep R) O (rstep (Expd_rename Cx t s)))" 
            using coincidence_lemma'[of "t" "vars_term s\<union> vars_term t" \<sigma>] coincidence_lemma'[of "s" "vars_term s\<union> vars_term t" \<sigma>] by simp
          then obtain t\<^sub>i where "(t\<cdot>\<sigma>,t\<^sub>i)\<in>(rstep R)" "(t\<^sub>i,s\<cdot>\<sigma>)\<in>(rstep (Expd_rename Cx t s))" by auto
          then have s\<^sub>i:"(Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx\<langle>t\<^sub>i\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>(rstep (Expd_rename Cx t s))" by auto
          from this(2) obtain t\<^sub>ir Ctx' \<theta> s\<^sub>ir where t\<^sub>ir:"(t\<^sub>ir, s\<^sub>ir)\<in>Expd_rename Cx t s \<and> Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx\<langle>t\<^sub>i\<rangle> \<and> Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx\<langle>s\<cdot>\<sigma>\<rangle>" 
            apply (rule rstepE) by metis
          have "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'" using E'(2) by simp
          then obtain t\<^sub>i' where t\<^sub>i':" (t\<^sub>ir, t\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (t\<^sub>i',s\<^sub>ir)\<in>E'"  
            using E' Cx t\<^sub>ir  by blast
          then have cs\<^sub>i':"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          proof -
            have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)" by auto
            also have "\<forall>s t C \<theta>. (s,t)\<in>(NS\<union>S) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
            ultimately have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
            then have " (t\<^sub>ir,t\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
              using  rtrancl_closed_ctxt_subst[of "((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx' \<theta>  "t\<^sub>ir" "t\<^sub>i'" ] by blast
            then show ?thesis using t\<^sub>i' by blast
          qed
          also have HEinf:"(rstep (?H i))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms5 assms6 i rirun_H_subset_Einf_rstep by simp
          then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          then have "((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
          ultimately have t1:"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
          note HEinf then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
          then have"((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
          then have t2:"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
          then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
            using rtrancl_iff_derivation[of "Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
          then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
          have "(t\<^sub>i',s\<^sub>ir)\<in>E'" using t\<^sub>i' t\<^sub>ir Cx by blast
          also have "E'\<subseteq>?E (i+1)" using E' by simp
          moreover have "i+1\<le> fst rirun" using i by simp
          ultimately have "(t\<^sub>i',s\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
          then have "(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
          then have s\<^sub>i't:"(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun) " using t\<^sub>ir by argo
          have "(Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<^sub>i\<rangle>)\<in>rstep R" "(Ctx\<langle>t\<^sub>i\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun)"
            using s\<^sub>i apply simp using t\<^sub>ir t2 apply simp using s\<^sub>i't by simp
          then have "(Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" "Ctx\<langle>t\<^sub>i\<rangle>" "Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx\<langle>s\<cdot>\<sigma>\<rangle>"] gCtxsts by blast
          then have "(t\<^sub>g,s\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" using st by meson
          then have "(s\<^sub>g,t\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using r1r2gtstar_on_rev[of "t\<^sub>g" "s\<^sub>g" NS S "rstep R" "rstep (Einf rirun)" ground_terms] by fast
          then show ?thesis by blast
        qed
      next
        let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
        case simplifyl
        then obtain s'' where s'':"((s,t),(s'',t))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s'',t)}" by auto
        then obtain s' where s':" (s,s') \<in> (rstep (R\<union>?H i)\<inter>S)" "(s',s'')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using simplifyl_eq rstep_simps(5)[of "?H i"] by auto
        then have s':"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> (rstep (R\<union>?H i)\<inter>S)" "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using ctxt_S subst_S apply auto[1] 
        proof -
          have "\<forall>(s,t)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S)). (Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S))" using subst ctxt by blast
          then show  "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            using s'(2) rtrancl_closed_ctxt_subst[of "(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" Ctx ?\<sigma> s' s''] by blast
        qed
        also have "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by simp
        then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto 
        then have s'2:"(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using s'(2) rtrancl_mono by blast
        have "(s'',t)\<in>?E(i+1)" using s''  by simp
        then have t:"(s'',t)\<in>Einf rirun" using i(1) Einf_def by auto
        obtain ss where ss:"ss\<noteq>[] \<and> hd ss = Ctx\<langle>s'\<cdot>?\<sigma>\<rangle> \<and> last ss = Ctx\<langle>s''\<cdot>?\<sigma>\<rangle> \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
          using s'2 rtrancl_iff_derivation[of "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
        consider"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> rstep R" | "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> rstep (?H i)" using s' ss by blast
        then show ?thesis 
        proof cases
          case 1
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>rstep R" "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            "(Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>rstep (Einf rirun)" "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" 
                apply simp using s'2 apply simp using t apply auto[1] using gCtxsts by auto 
          then have "  (Ctx\<langle>s \<cdot>?\<sigma>\<rangle>, Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" rirun "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>"] by fastforce
          then show ?thesis using st coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma> ] by simp
        next
          case 2
          then have *:"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow> "using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by auto
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          also have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>S" using s' by simp
          moreover have "(Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using t by auto
          moreover have "(Ctx\<langle>s' \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>s'' \<cdot> ?\<sigma>\<rangle>) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S))\<^sup>* " using s'2 by simp
          moreover have "gc_subst C ?\<sigma>" using gc\<sigma> by simp
          moreover have " ground Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>\<and> ground Ctx\<langle>t \<cdot> ?\<sigma>\<rangle> " using gCtxsts by simp
          ultimately have "(Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using simplify_r1r2_case[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" rirun i
                "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "(\<sigma>|s (vars_term s \<union> vars_term t))"] 2 assms5 assms6 i(1) by fast
          then show ?thesis using st coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma>] by auto
        qed
      next
        let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
        case simplifyr
        then obtain t'' where t'':"((s,t),(s,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(s,t)} \<union>{(s,t'')}" by auto
        then obtain t' where t':" (t,t') \<in> (rstep (R\<union>?H i)\<inter>S)" "(t',t'')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using simplifyr_eq rstep_simps(5)[of "?H i"] by auto
        then have t':"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> (rstep (R\<union>?H i)\<inter>S)" "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using ctxt_S subst_S apply auto[1] 
        proof -
          have "\<forall>(s,t)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S)). (Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S))" using subst ctxt by blast
          then show  "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            using t'(2) rtrancl_closed_ctxt_subst[of "(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" Ctx ?\<sigma> t' t''] by blast
        qed
        also have "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by simp
        then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto 
        then have t'2:"(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using t'(2) rtrancl_mono by blast
        have "(t'',s)\<in>(?E(i+1))\<^sup>\<leftrightarrow>" using t''  by simp
        then have t:"(t'',s)\<in>(Einf rirun)\<^sup>\<leftrightarrow>" using i(1) Einf_def by auto
        obtain ss where ss:"ss\<noteq>[] \<and> hd ss = Ctx\<langle>t'\<cdot>?\<sigma>\<rangle> \<and> last ss = Ctx\<langle>t''\<cdot>?\<sigma>\<rangle> \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
          using t'2 rtrancl_iff_derivation[of "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
        consider"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> rstep R" | "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> rstep (?H i)" using t' ss by blast
        then show ?thesis 
        proof cases
          case 1
          then have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>rstep R" "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            "(Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" 
                apply simp using t'2 apply simp using t apply auto[1] using gCtxsts by auto
          then have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s\<cdot>?\<sigma>\<rangle>)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" rirun "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>"] by fast
          then have "(t\<^sub>g,s\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using st coincidence_lemma'[of _  "vars_term s\<union> vars_term t" \<sigma>] by simp
          then show ?thesis using r1r2gtstar_on_rev[of "t\<^sub>g" "s\<^sub>g" NS S ] by blast
        next
          case 2
          then have *:"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow> "using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by auto
          then have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          also have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>S" using t' by simp
          moreover have "(Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using t by auto
          moreover have "(Ctx\<langle>t' \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>t'' \<cdot> ?\<sigma>\<rangle>) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S))\<^sup>* " using t'2 by simp
          moreover have "gc_subst C ?\<sigma>" using gc\<sigma> by simp
          moreover have " ground Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>\<and> ground Ctx\<langle>t \<cdot> ?\<sigma>\<rangle> " using gCtxsts by simp
          ultimately have "(Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using simplify_r1r2_case[of "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" rirun i
                "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "(\<sigma>|s (vars_term s \<union> vars_term t))"] 2 assms5 assms6 i(1) by fast
          then have "(t\<^sub>g,s\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using st coincidence_lemma'[of _ "vars_term s \<union> vars_term t" \<sigma>] by simp
          then show ?thesis using r1r2gtstar_on_rev[of t\<^sub>g s\<^sub>g NS S "rstep R" "rstep (Einf rirun)" ground_terms] by fast
        qed
      next
        case delete
        then consider "s = t" | "(s,t)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" using delete_eq[of s t "?H i"] by blast
        then show ?thesis 
        proof cases
          case 1
          let ?xs = "[Ctx\<langle>s\<cdot>\<sigma>\<rangle>]"
          have "?xs \<noteq> []" by simp
          also have "hd ?xs = Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> last ?xs = Ctx\<langle>t\<cdot>\<sigma>\<rangle>" using 1 by simp
          moreover have "\<forall>i<length ?xs. (?xs!i)\<in>ground_terms" using gCtxsts by simp
          moreover have "is_proof_of ?xs (rstep R \<union> (rstep (Einf rirun)))" by simp
          moreover have "(\<forall>i<length [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] - 1.
              ([Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
              ({#Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<sigma>\<rangle>#}, {#[Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! (i + 1)#}) \<in> s_mul_ext NS S) " by simp
          moreover have "(\<forall>i<length [Ctx\<langle>s \<cdot> \<sigma>\<rangle>]. (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i) \<in> NS \<union> S \<or> (Ctx\<langle>t \<cdot> \<sigma>\<rangle>, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i) \<in> NS \<union> S)" 
            using 1 refl_NS_S refl_onD[of UNIV "NS\<union>S"] by auto          
          ultimately show ?thesis using r1r2_on_intro[of ?xs "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" "rstep R" "rstep (Einf rirun)" NS S ground_terms ] st by fast
        next 
          let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
          case 2
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>, Ctx\<langle>t\<cdot>?\<sigma>\<rangle>) \<in> (rstep (snd (snd rirun i)))\<^sup>\<leftrightarrow>" by auto
          also have "gc_subst C (\<sigma> |s (vars_term s \<union> vars_term t))" using gc\<sigma> by blast
          moreover have "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" using gCtxsts by auto
          ultimately have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using simplify_b'[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" rirun i ?\<sigma> ] assms5 assms6 i(1) by fastforce
          then have "(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma>] by force
          then show ?thesis using st by force
        qed
      qed
    }
    moreover 
    {
      assume "(t,s)\<in>Einf rirun" 
      then have "\<exists>i<(fst rirun).  
          ((\<exists>E'. (((s,t),E')\<in>expand_eq_set (?H i) \<or> ((t,s),E')\<in>expand_eq_set (?H i)) \<and>
                ?E (i+1) = ?E i -{(t,s),(s,t)}\<union>E') \<or> 
          (\<exists>s''. ((t,s),(s'',s))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(s'',s)} ) \<or> 
          (\<exists>t''. ((t,s),(t,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(t,t'')} ) \<or>
          ((t,s)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(t,s)}))" using Einf_eq_cases fair assms5 by fast
      then obtain i where i:"i<fst rirun" 
        "(\<exists>E'. (((s,t),E')\<in>expand_eq_set (?H i) \<or> ((t,s),E')\<in>expand_eq_set (?H i)) \<and> ?E (i+1) = ?E i -{(t,s),(s,t)}\<union>E') \<or> 
          (\<exists>s''. ((t,s),(s'',s))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(s'',s)} ) \<or> 
          (\<exists>t''. ((t,s),(t,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(t,t'')} ) \<or>
          ((t,s)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(t,s)})" by force
      then consider (expand)"\<exists>E'. (((s,t),E')\<in>expand_eq_set ((?H i)) \<or> ((t,s),E')\<in>expand_eq_set ((?H i)))
                                \<and> ?E (i+1) = ?E i -{(t,s),(s,t)}\<union>E'" |
        (simplifyl)"\<exists>s''. ((t,s),(s'',s))\<in>simplifyl_eq (?H i) \<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(s'',s)} " |
        (simplifyr)"\<exists>t''. ((t,s),(t,t''))\<in>simplifyr_eq (?H i) \<and>?E (i+1) = ?E i- {(t,s)} \<union>{(t,t'')}" |
        (delete)"(t,s)\<in>delete_eq (?H i) \<and> ?E(i+1) = ?E i-{(t,s)}" by fast
      then have ?thesis 
      proof cases
        case expand
        then obtain E' where E':" ((t,s),E')\<in>expand_eq_set (?H i) \<or> ((s,t),E')\<in>expand_eq_set (?H i)" "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'"
          using expand by blast
        then consider "((s,t),E')\<in>expand_eq_set (?H i)" | "((t,s),E')\<in>expand_eq_set (?H i) " by auto
        then show ?thesis 
        proof cases
          case 1
          then obtain Cx where Cx:"(Cx\<in>basic_ctxts s \<and>  
                              (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx s t \<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> 
                                 (s\<^sub>i',t\<^sub>i)\<in>E')))"
            using expand_eq_set by blast
          also have "gc_subst C ((\<sigma> |s (vars_term s \<union>vars_term t))|s vars_term s)" using gc\<sigma> by force
          ultimately have "(s\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)),t\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)))\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
            using expd_prop dom g\<sigma> gc\<sigma> Cx by blast
          then have "(s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>((rstep R) O (rstep (Expd_rename Cx s t)))" 
            using coincidence_lemma'[of "s" "vars_term s\<union> vars_term t" \<sigma>] coincidence_lemma'[of "t" "vars_term s\<union> vars_term t" \<sigma>] by simp
          then obtain s\<^sub>i where "(s\<cdot>\<sigma>,s\<^sub>i)\<in>(rstep R)" "(s\<^sub>i,t\<cdot>\<sigma>)\<in>(rstep (Expd_rename Cx s t))" by auto
          then have s\<^sub>i:"(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx\<langle>s\<^sub>i\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Expd_rename Cx s t))" by auto
          from this(2) obtain s\<^sub>ir Ctx' \<theta> t\<^sub>ir where s\<^sub>ir:"(s\<^sub>ir, t\<^sub>ir)\<in>Expd_rename Cx s t \<and> Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx\<langle>s\<^sub>i\<rangle> \<and> Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx\<langle>t\<cdot>\<sigma>\<rangle>" 
            apply (rule rstepE) by metis
          have "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'" using E'(2) by simp
          then obtain s\<^sub>i' where s\<^sub>i':" (s\<^sub>ir, s\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (s\<^sub>i',t\<^sub>ir)\<in>E'"
            using E' Cx s\<^sub>ir  by blast
          then have cs\<^sub>i':"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          proof -
            have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)" by auto
            also have "\<forall>s t. (s,t)\<in>(NS\<union>S) \<longrightarrow> (Ctx'\<langle>s\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
            ultimately have "\<forall>s t . (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (Ctx'\<langle>s\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
            then have "(s\<^sub>ir,s\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
              using  rtrancl_closed_ctxt_subst[of "((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx' \<theta> s\<^sub>ir s\<^sub>i'] by blast
            then show ?thesis using s\<^sub>i' by blast
          qed
          also have HEinf:"(rstep (?H i))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms5 assms6 i rirun_H_subset_Einf_rstep by simp
          then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          then have "((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
          ultimately have t1:"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
          note HEinf then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
          then have"((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
          then have t2:"(Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
          then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
            using rtrancl_iff_derivation[of "Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
          then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
          have "(s\<^sub>i',t\<^sub>ir)\<in>E'" using s\<^sub>i' s\<^sub>ir Cx by blast 
          also have "E'\<subseteq>?E (i+1)" using E' by simp
          moreover have "i+1\<le> fst rirun" using i by simp
          ultimately have "(s\<^sub>i',t\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
          then have "(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
          then have s\<^sub>i't:"(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun) " using s\<^sub>ir by argo
          have "(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>s\<^sub>i\<rangle>)\<in>rstep R" "(Ctx\<langle>s\<^sub>i\<rangle>,Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun)"
            using s\<^sub>i apply simp using s\<^sub>ir t2 apply simp using s\<^sub>i't by simp
          then have "(Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" "Ctx\<langle>s\<^sub>i\<rangle>" "Ctx'\<langle>s\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx\<langle>t\<cdot>\<sigma>\<rangle>"] gCtxsts by blast
          then show ?thesis using st by fast
        next
          case 2
          then obtain Cx where Cx:"(Cx\<in>basic_ctxts t \<and> 
                       (\<forall>s\<^sub>i t\<^sub>i. (s\<^sub>i,t\<^sub>i) \<in> Expd_rename Cx t s\<longrightarrow> (\<exists>s\<^sub>i'. (s\<^sub>i,s\<^sub>i')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> 
                       (s\<^sub>i',t\<^sub>i)\<in>E')))"
            using expand_eq_set by blast
          also have "gc_subst C ((\<sigma> |s (vars_term s \<union>vars_term t))|s vars_term t)" using gc\<sigma> by force
          ultimately have "(t\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)),s\<cdot>(\<sigma> |s (vars_term s \<union>vars_term t)))\<in>((rstep R) O (rstep (Expd_rename Cx t s)))" 
            using expd_prop dom g\<sigma> gc\<sigma> by blast
          then have "(t\<cdot>\<sigma>,s\<cdot>\<sigma>)\<in>((rstep R) O (rstep (Expd_rename Cx t s)))" 
            using coincidence_lemma'[of "t" "vars_term s\<union> vars_term t" \<sigma>] coincidence_lemma'[of "s" "vars_term s\<union> vars_term t" \<sigma>] by simp
          then obtain t\<^sub>i where "(t\<cdot>\<sigma>,t\<^sub>i)\<in>(rstep R)" "(t\<^sub>i,s\<cdot>\<sigma>)\<in>(rstep (Expd_rename Cx t s))" by auto
          then have s\<^sub>i:"(Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<^sub>i\<rangle>)\<in>(rstep R)" "(Ctx\<langle>t\<^sub>i\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>(rstep (Expd_rename Cx t s))" by auto
          from this(2) obtain t\<^sub>ir Ctx' \<theta> s\<^sub>ir where t\<^sub>ir:"(t\<^sub>ir, s\<^sub>ir)\<in>Expd_rename Cx t s \<and> Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>=Ctx\<langle>t\<^sub>i\<rangle> \<and> Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle> = Ctx\<langle>s\<cdot>\<sigma>\<rangle>" 
            apply (rule rstepE) by metis
          have "?E (i+1) = ?E i -{(s,t),(t,s)}\<union>E'" using E'(2) by simp
          then obtain t\<^sub>i' where t\<^sub>i':" (t\<^sub>ir, t\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<and> (t\<^sub>i',s\<^sub>ir)\<in>E'"     
            using E' Cx  t\<^sub>ir by blast
          then have cs\<^sub>i':"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          proof -
            have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)" by auto
            also have "\<forall>s t C \<theta>. (s,t)\<in>(NS\<union>S) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>(NS\<union>S)" using subst ctxt by simp
            ultimately have "\<forall>s t C \<theta>. (s,t)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S) \<longrightarrow> (C\<langle>s\<cdot>\<theta>\<rangle>,C\<langle>t\<cdot>\<theta>\<rangle>)\<in>((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" by blast
            then have " (t\<^sub>ir,t\<^sub>i')\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^* \<longrightarrow> (Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
              using  rtrancl_closed_ctxt_subst[of "((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)" Ctx' \<theta>  "t\<^sub>ir" "t\<^sub>i'" ] by blast
            then show ?thesis using t\<^sub>i' by blast
          qed
          also have HEinf:"(rstep (?H i))\<^sup>\<leftrightarrow> \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" using assms5 assms6 i rirun_H_subset_Einf_rstep by simp
          then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          then have "((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>)^*" using rtrancl_mono by blast
          ultimately have t1:"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>))^*" by blast
          note HEinf then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S) \<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto
          then have"((rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^* \<subseteq> ((rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S))^*" using rtrancl_mono by blast
          then have t2:"(Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>, Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in> (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using cs\<^sub>i' by auto
          then obtain ss where "is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)) \<and> hd ss = Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle> \<and> last ss = Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle> \<and> ss\<noteq>[]" 
            using rtrancl_iff_derivation[of "Ctx'\<langle>t\<^sub>ir\<cdot>\<theta>\<rangle>" "Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
          then have t3:"is_derivation_of ss ((rstep (Einf rirun))\<^sup>\<leftrightarrow>) \<and> (\<forall>i<length ss. (hd ss,ss!i)\<in>NS\<union>S)"  using derivation_ordered trans refl_NS_S by blast
          have "(t\<^sub>i',s\<^sub>ir)\<in>E'" using t\<^sub>i' t\<^sub>ir Cx by blast
          also have "E'\<subseteq>?E (i+1)" using E' by simp
          moreover have "i+1\<le> fst rirun" using i by simp
          ultimately have "(t\<^sub>i',s\<^sub>ir)\<in>Einf rirun" using Einf_def by auto
          then have "(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx'\<langle>s\<^sub>ir\<cdot>\<theta>\<rangle>)\<in>rstep (Einf rirun)" by blast
          then have s\<^sub>i't:"(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun) " using t\<^sub>ir by argo
          have "(Ctx\<langle>t\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<^sub>i\<rangle>)\<in>rstep R" "(Ctx\<langle>t\<^sub>i\<rangle>,Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" "(Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>,Ctx\<langle>s\<cdot>\<sigma>\<rangle>)\<in>rstep (Einf rirun)"
            using s\<^sub>i apply simp using t\<^sub>ir t2 apply simp using s\<^sub>i't by simp
          then have "(Ctx\<langle>t \<cdot> \<sigma>\<rangle>, Ctx\<langle>s \<cdot> \<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" "Ctx\<langle>t\<^sub>i\<rangle>" "Ctx'\<langle>t\<^sub>i'\<cdot>\<theta>\<rangle>" "rirun" "Ctx\<langle>s\<cdot>\<sigma>\<rangle>"] gCtxsts by blast
          then have "(t\<^sub>g,s\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" using st by meson
          then have "(s\<^sub>g,t\<^sub>g) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using r1r2gtstar_on_rev[of "t\<^sub>g" "s\<^sub>g" NS S "rstep R" "rstep (Einf rirun)" ground_terms] by fast
          then show ?thesis by blast
        qed
      next
        let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
        case simplifyl
        then obtain s'' where s'':"((t,s),(s'',s))\<in>simplifyl_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(s'',s)}" by auto
        then obtain s' where s':" (t,s') \<in> (rstep (R\<union>?H i)\<inter>S)" "(s',s'')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using simplifyl_eq rstep_simps(5)[of "?H i"] by auto
        then have s':"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> (rstep (R\<union>?H i)\<inter>S)" "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using ctxt_S subst_S apply auto[1] 
        proof -
          have "\<forall>(s,t)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S)). (Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S))" using subst ctxt by blast
          then show  "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            using s'(2) rtrancl_closed_ctxt_subst[of "(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" Ctx ?\<sigma> s' s''] by blast
        qed
        also have "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by simp
        then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto 
        then have s'2:"(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using s'(2) rtrancl_mono by blast
        have "(s'',s)\<in>?E(i+1)" using s''  by simp
        then have t:"(s'',s)\<in>Einf rirun" using i(1) Einf_def by auto
        obtain ss where ss:"ss\<noteq>[] \<and> hd ss = Ctx\<langle>s'\<cdot>?\<sigma>\<rangle> \<and> last ss = Ctx\<langle>s''\<cdot>?\<sigma>\<rangle> \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
          using s'2 rtrancl_iff_derivation[of "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
        consider"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> rstep R" | "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>) \<in> rstep (?H i)" using s' ss by blast
        then show ?thesis 
        proof cases
          case 1
          then have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>rstep R" "(Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            "(Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s\<cdot>?\<sigma>\<rangle>)\<in>rstep (Einf rirun)" "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" 
                apply simp using s'2 apply simp using t apply auto[1] using gCtxsts by auto 
          then have "  (Ctx\<langle>t \<cdot>?\<sigma>\<rangle>, Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" rirun "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>"] by blast
          then have "(t\<^sub>g,s\<^sub>g)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using st coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma> ] by simp
          then show ?thesis using r1r2gtstar_on_rev[of t\<^sub>g s\<^sub>g NS S "(rstep R)" "(rstep (Einf rirun))" ground_terms] by blast
        next
          case 2
          then have *:"(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow> "using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by auto
          then have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          also have "(Ctx\<langle>t\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>)\<in>S" using s' by simp
          moreover have "(Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>s\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using t by auto
          moreover have "(Ctx\<langle>s' \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>s'' \<cdot> ?\<sigma>\<rangle>) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S))\<^sup>* " using s'2 by simp
          moreover have "gc_subst C ?\<sigma>" using gc\<sigma> by simp
          moreover have " ground Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>\<and> ground Ctx\<langle>s \<cdot> ?\<sigma>\<rangle> " using gCtxsts by simp
          ultimately have "(Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using simplify_r1r2_case[of "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s'\<cdot>?\<sigma>\<rangle>" rirun i
                "Ctx\<langle>s''\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "(\<sigma>|s (vars_term s \<union> vars_term t))"] 2 assms5 assms6 i(1) by fast
          then have "(t\<^sub>g,s\<^sub>g)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using st coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma> ] by simp
          then show ?thesis using r1r2gtstar_on_rev[of t\<^sub>g s\<^sub>g NS S "(rstep R)" "(rstep (Einf rirun))" ground_terms] by blast
        qed
      next
        let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
        case simplifyr
        then obtain t'' where t'':"((t,s),(t,t''))\<in>simplifyr_eq ((?H i))\<and> ?E (i+1) = ?E i- {(t,s)} \<union>{(t,t'')}" by auto
        then obtain t' where t':" (s,t') \<in> (rstep (R\<union>?H i)\<inter>S)" "(t',t'')\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
          using simplifyr_eq rstep_simps(5)[of "?H i"] by auto
        then have t':"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> (rstep (R\<union>?H i)\<inter>S)" "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using ctxt_S subst_S apply auto[1] 
        proof -
          have "\<forall>(s,t)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S)). (Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>((rstep ((?H i)\<^sup>\<leftrightarrow>))\<inter>(NS\<union>S))" using subst ctxt by blast
          then show  "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in> (((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            using t'(2) rtrancl_closed_ctxt_subst[of "(((rstep (?H i))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" Ctx ?\<sigma> t' t''] by blast
        qed
        also have "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by simp
        then have "(rstep (?H i))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)\<subseteq>(rstep (Einf rirun))\<^sup>\<leftrightarrow>\<inter>(NS\<union>S)" by auto 
        then have t'2:"(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" using t'(2) rtrancl_mono by blast
        have "(t'',t)\<in>(?E(i+1))\<^sup>\<leftrightarrow>" using t''  by simp
        then have t:"(t'',t)\<in>(Einf rirun)\<^sup>\<leftrightarrow>" using i(1) Einf_def by auto
        obtain ss where ss:"ss\<noteq>[] \<and> hd ss = Ctx\<langle>t'\<cdot>?\<sigma>\<rangle> \<and> last ss = Ctx\<langle>t''\<cdot>?\<sigma>\<rangle> \<and> is_derivation_of ss (((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))" 
          using t'2 rtrancl_iff_derivation[of "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" "((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S)"] by blast
        consider"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> rstep R" | "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>) \<in> rstep (?H i)" using t' ss by blast
        then show ?thesis 
        proof cases
          case 1
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>rstep R" "(Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>)\<in>(((rstep (Einf rirun))\<^sup>\<leftrightarrow>)\<inter>(NS\<union>S))^*" 
            "(Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" 
                apply simp using t'2 apply simp using t apply auto[1] using gCtxsts by auto
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using expand_r1r2_case[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" rirun "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>"] by fast
          then show ?thesis using  st coincidence_lemma'[of _  "vars_term s\<union> vars_term t" \<sigma>] by simp
        next
          case 2
          then have *:"(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" "(rstep (?H i))\<^sup>\<leftrightarrow>\<subseteq> (rstep (Einf rirun))\<^sup>\<leftrightarrow> "using rirun_H_subset_Einf_rstep[of rirun] assms5 assms6 i(1) by auto
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" by auto
          also have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>)\<in>S" using t' by simp
          moreover have "(Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in>(rstep (Einf rirun))\<^sup>\<leftrightarrow>" using t by auto
          moreover have "(Ctx\<langle>t' \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>t'' \<cdot> ?\<sigma>\<rangle>) \<in> ((rstep (Einf rirun))\<^sup>\<leftrightarrow> \<inter> (NS \<union> S))\<^sup>* " using t'2 by simp
          moreover have "gc_subst C ?\<sigma>" using gc\<sigma> by simp
          moreover have " ground Ctx\<langle>t \<cdot> ?\<sigma>\<rangle>\<and> ground Ctx\<langle>s \<cdot> ?\<sigma>\<rangle> " using gCtxsts by simp
          ultimately have "(Ctx\<langle>s \<cdot> ?\<sigma>\<rangle>, Ctx\<langle>t\<cdot> ?\<sigma>\<rangle>) \<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms" 
            using simplify_r1r2_case[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t'\<cdot>?\<sigma>\<rangle>" rirun i
                "Ctx\<langle>t''\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" "(\<sigma>|s (vars_term s \<union> vars_term t))"] 2 assms5 assms6 i(1) by fast
          then show ?thesis using st coincidence_lemma'[of _ "vars_term s \<union> vars_term t" \<sigma>] by simp
        qed
      next
        case delete
        then have "t = s \<or> (t,s)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" using delete_eq[of t s "?H i"] by blast
        then consider "s = t" | "(s,t)\<in>(rstep (?H i))\<^sup>\<leftrightarrow>" by blast
        then show ?thesis 
        proof cases
          case 1
          let ?xs = "[Ctx\<langle>s\<cdot>\<sigma>\<rangle>]"
          have "?xs \<noteq> []" by simp
          also have "hd ?xs = Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> last ?xs = Ctx\<langle>t\<cdot>\<sigma>\<rangle>" using 1 by simp
          moreover have "\<forall>i<length ?xs. (?xs!i)\<in>ground_terms" using gCtxsts by simp
          moreover have "is_proof_of ?xs (rstep R \<union> (rstep (Einf rirun)))" by simp
          moreover have "(\<forall>i<length [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] - 1.
              ([Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! (i + 1)) \<notin> (rstep R)\<^sup>\<leftrightarrow> \<longrightarrow>
              ({#Ctx\<langle>s \<cdot> \<sigma>\<rangle>, Ctx\<langle>t \<cdot> \<sigma>\<rangle>#}, {#[Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! (i + 1)#}) \<in> s_mul_ext NS S) " by simp
          moreover have "(\<forall>i<length [Ctx\<langle>s \<cdot> \<sigma>\<rangle>]. (Ctx\<langle>s \<cdot> \<sigma>\<rangle>, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i) \<in> NS \<union> S \<or> (Ctx\<langle>t \<cdot> \<sigma>\<rangle>, [Ctx\<langle>s \<cdot> \<sigma>\<rangle>] ! i) \<in> NS \<union> S)" 
            using 1 refl_NS_S refl_onD[of UNIV "NS\<union>S"] by auto          
          ultimately show ?thesis using r1r2_on_intro[of ?xs "Ctx\<langle>s\<cdot>\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>\<sigma>\<rangle>" "rstep R" "rstep (Einf rirun)" NS S ground_terms ] st by fast
        next 
          let ?\<sigma> = "\<sigma>|s (vars_term s \<union> vars_term t)"
          case 2
          then have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>, Ctx\<langle>t\<cdot>?\<sigma>\<rangle>) \<in> (rstep (snd (snd rirun i)))\<^sup>\<leftrightarrow>" by auto
          also have "gc_subst C (\<sigma> |s (vars_term s \<union> vars_term t))" using gc\<sigma> by blast
          moreover have "ground Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "ground Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" using gCtxsts by auto
          ultimately have "(Ctx\<langle>s\<cdot>?\<sigma>\<rangle>,Ctx\<langle>t\<cdot>?\<sigma>\<rangle>)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using simplify_b'[of "Ctx\<langle>s\<cdot>?\<sigma>\<rangle>" "Ctx\<langle>t\<cdot>?\<sigma>\<rangle>" rirun i ?\<sigma> ] assms5 assms6 i(1) by fastforce
          then have "(Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in> R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf rirun)) ground_terms"
            using coincidence_lemma'[of _ "vars_term s\<union> vars_term t" \<sigma>] by force
          then show ?thesis using st by force
        qed
      qed
    }
    ultimately show ?thesis by fast
  qed
qed

lemma lemma9:
  assumes "\<exists>rirun. full_ri_run E\<^sub>0 rirun"
  shows "bounded_ground_convertible_eqs R NS S E\<^sub>0"    
proof -
  obtain EHi n where rirun:"ri_run (n,EHi) \<and> EHi 0 = (E\<^sub>0,{}) \<and> fst (EHi n) = {}" 
    using assms full_ri_run_def by auto
  let ?rirun = "(n,EHi)"
  have fair:"fair ?rirun" using rirun by fastforce
  then have "\<forall>s\<^sub>g\<in>ground_terms. \<forall>t\<^sub>g\<in>ground_terms.  
                (s\<^sub>g,t\<^sub>g)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow> \<longrightarrow> (s\<^sub>g,t\<^sub>g)\<in>R\<^sub>1geR\<^sub>2gtstar_on NS S (rstep R) (rstep (Einf ?rirun)) ground_terms  "
    using lemma8[of _ _ ?rirun] rirun full_ri_run_def by force
  then have *:"\<forall>s\<^sub>g\<in>ground_terms. \<forall>t\<^sub>g\<in>ground_terms.
                (s\<^sub>g,t\<^sub>g)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow> \<longrightarrow> (s\<^sub>g,t\<^sub>g)\<in>Rgestar_on NS S (rstep R) ground_terms" using conversion_lemmma by presburger
  then have "\<forall>s. \<forall>t. \<forall>\<sigma>. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t \<subseteq>subst_domain \<sigma> \<longrightarrow> 
                (s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow> \<longrightarrow> (s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>Rgestar_on NS S (rstep R) ground_terms" 
  proof (intro allI impI)
    fix s t::"('a,'b)term" fix  \<sigma>::"('a,'b)subst"
    assume a1:"ground_subst \<sigma> \<and> vars_term s \<union>vars_term t \<subseteq>subst_domain \<sigma>" assume a2:"(s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow>"
    have "ground (s\<cdot>\<sigma>) \<and> ground (t\<cdot>\<sigma>)" using a1 by auto
    then have "s\<cdot>\<sigma>\<in>ground_terms \<and> t\<cdot>\<sigma>\<in>ground_terms " by simp
    then show "(s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>Rgestar_on NS S (rstep R) ground_terms" using * a2 by auto
  qed
  then have"\<forall>s t \<sigma> Ctx. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t \<subseteq>subst_domain \<sigma> \<and> ground_ctxt Ctx \<longrightarrow> 
                (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow> \<longrightarrow> (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>Rgestar_on NS S (rstep R) ground_terms"
    by (metis "*" CollectI ground_ctxt_apply ground_terms_def groundsubst sup.boundedE)
  then have "\<forall>s t \<sigma> Ctx. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t \<subseteq>subst_domain \<sigma> \<and> ground_ctxt Ctx \<longrightarrow> 
                    (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow>\<longrightarrow> 
                      (\<exists>us. us\<noteq>[]\<and> hd us = Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> last us = Ctx\<langle>t\<cdot>\<sigma>\<rangle> \<and> is_proof_of us (rstep R)\<and> (\<forall>i<length us. us!i\<in>ground_terms) \<and> 
                        (\<forall>i<length us. (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S) \<or> (Ctx\<langle>t\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S)))" using Rgestar_def by simp
  then have **:"\<forall>Ctx. \<forall>s t. (\<forall>\<sigma>. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t \<subseteq>subst_domain \<sigma> \<and> ground_ctxt Ctx \<longrightarrow> 
                    (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow> \<longrightarrow> 
                      (\<exists>us. us\<noteq>[]\<and> hd us = Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> last us = Ctx\<langle>t\<cdot>\<sigma>\<rangle> \<and> is_proof_of us (rstep R)\<and>
                        (\<forall>i<length us. (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S) \<or> (Ctx\<langle>t\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S))))" by meson
  have "\<forall>Ctx. \<forall>s t. (s,t)\<in>E\<^sub>0 \<longrightarrow> (\<forall>\<sigma>. (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,Ctx\<langle>t\<cdot>\<sigma>\<rangle>)\<in>(rstep (Einf ?rirun))\<^sup>\<leftrightarrow>)" using rirun E\<^sub>0inEinf by blast
  then have ***:"\<forall>Ctx. \<forall>s t. (s,t)\<in>E\<^sub>0 \<longrightarrow> (\<forall>\<sigma>. ground_subst \<sigma> \<and> ground_ctxt Ctx \<and> vars_term s \<union>vars_term t\<subseteq>subst_domain \<sigma> \<longrightarrow>  
                      (\<exists>us. us\<noteq>[]\<and> hd us = Ctx\<langle>s\<cdot>\<sigma>\<rangle> \<and> last us = Ctx\<langle>t\<cdot>\<sigma>\<rangle> \<and> is_proof_of us (rstep R)\<and>
                        (\<forall>i<length us. (Ctx\<langle>s\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S) \<or> (Ctx\<langle>t\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S))))" using ** by presburger
  have "ground_ctxt Hole" by auto
  then have "\<forall>(s,t)\<in>E\<^sub>0.\<forall>\<sigma>. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t\<subseteq>subst_domain \<sigma> \<longrightarrow>  
                      (\<exists>us. us\<noteq>[] \<and> hd us = Hole\<langle>s\<cdot>\<sigma>\<rangle> \<and> last us = Hole\<langle>t\<cdot>\<sigma>\<rangle> \<and> is_proof_of us (rstep R)\<and>
                        (\<forall>i<length us. (Hole\<langle>s\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S) \<or> (Hole\<langle>t\<cdot>\<sigma>\<rangle>,us!i)\<in>(NS\<union>S)))" using *** by blast
  then have ***:"\<forall>(s,t)\<in>E\<^sub>0.\<forall>\<sigma>. ground_subst \<sigma> \<and> vars_term s \<union>vars_term t\<subseteq>subst_domain \<sigma> \<longrightarrow>  
                      (\<exists>us. us\<noteq>[]  \<and> hd us = s\<cdot>\<sigma> \<and> last us = t\<cdot>\<sigma> \<and> is_proof_of us (rstep R)\<and>
                        (\<forall>i<length us. (s\<cdot>\<sigma>,us!i)\<in>(NS\<union>S) \<or> (t\<cdot>\<sigma>,us!i)\<in>(NS\<union>S)))" by simp
  then have "\<forall>(s,t)\<in>E\<^sub>0. bounded_ground_convertible_terms R NS S s t" using bounded_ground_convertible_terms_def by simp
  then show ?thesis by simp
qed

theorem soundness_ri:
  assumes "\<exists>rirun. full_ri_run E\<^sub>0 rirun"
  shows "R \<Turnstile>\<^sub>i E\<^sub>0"
proof -
  have "bounded_ground_convertible_eqs R NS S E\<^sub>0" using lemma9 assms by blast
  then show ?thesis using b_g_c_imp_inductive_theorem by blast
qed      


(* a simplified set of inference rules that might be used by other tools *)
inductive_set expand_eq_set'::"('a,'b) trs \<Rightarrow> (('a,'b) equation\<times>('a,'b) equations) set" for H 
  where 
    "Cx\<in>basic_ctxts s 
     \<Longrightarrow> ((s,t),Expd_rename Cx s t)\<in>expand_eq_set' H" 

inductive_set ri_step' ::"('a,'b) ri_state rel" where 
  expand': "((s,t)\<in>E \<or> (t,s)\<in>E) \<and> ((s,t),E')\<in>expand_eq_set' H 
            \<Longrightarrow> (((E,H),((E-{(s,t),(t,s)})\<union>E',H\<union>{(s,t)}))\<in>ri_step')"
| simplifyl': "(s,t)\<in>E \<and> (s,s')\<in>rstep (R\<union>H) 
            \<Longrightarrow>  ((E,H),((E-{(s,t)})\<union>{(s',t)},H))\<in>ri_step'"
| simplifyr': "(s,t)\<in>E \<and> (t,t')\<in>rstep (R\<union>H) 
            \<Longrightarrow>((E,H),((E-{(s,t)})\<union>{(s,t')},H))\<in>ri_step'"
| delete': "(s,s)\<in>E \<Longrightarrow> ((E,H),(E-{(s,s)},H))\<in>ri_step'"  

(* RT: why are runs defined as functions from nat, and not just via *-steps,
  might be simplifiable *)
definition ri_run' :: "('a, 'b) ri_run \<Rightarrow> bool" where 
  "ri_run' rirun \<equiv> (case rirun of (n,EHi) \<Rightarrow> (\<forall>i < n. (EHi i, EHi (Suc i))\<in>ri_step'))"

definition full_ri_run'::"('a,'b) equations \<Rightarrow> ('a,'b) ri_run \<Rightarrow> bool" 
  where "full_ri_run' E rirun \<longleftrightarrow> 
         ri_run' rirun \<and> (case rirun of (n,EHi) \<Rightarrow> EHi 0 = (E,{}) \<and> fst (EHi n) = {} \<and> R \<union> snd (EHi n) \<subseteq> S)"

lemma ri_step'_incr: assumes "((E,H), (E',H')) \<in> ri_step'"
  shows "H \<subseteq> H'" 
  using assms 
  by (cases rule: ri_step'.cases, auto)

lemma full_ri_run'_is_full_ri_run: assumes "full_ri_run' E rirun" 
  shows "full_ri_run E rirun" 
proof -
  obtain n EHi where rirun: "rirun = (n, EHi)" by force
  from assms[unfolded full_ri_run'_def rirun split]
  have run: "ri_run' (n, EHi)" and 
    init: "EHi 0 = (E, {})" and
    last: "fst (EHi n) = {}" and 
    RS: "R \<subseteq> S" and nS: "snd (EHi n) \<subseteq> S" by auto
  from run[unfolded ri_run'_def, simplified]
  have steps: "\<forall>i<n. (EHi i, EHi (Suc i)) \<in> ri_step'" by auto
  hence "i \<le> n \<Longrightarrow> snd (EHi i) \<subseteq> snd (EHi n)" for i
  proof (induct n arbitrary: i)
    case (Suc n i)
    hence IH: "\<And> i. i \<le> n \<Longrightarrow> snd (EHi i) \<subseteq> snd (EHi n)"
      and step: "(EHi n, EHi (Suc n)) \<in> ri_step'" by auto
    have n: "snd (EHi n) \<subseteq> snd (EHi (Suc n))" 
      by (rule ri_step'_incr[of "fst (EHi n)" _ "fst (EHi (Suc n))"], insert step, auto)
    from Suc(2) have "i \<le> n \<or> i = Suc n" by auto
    with IH[of i] IH[of n] n show ?case by auto
  qed auto
  hence HS: "\<And> i. i \<le> n \<Longrightarrow> snd (EHi i) \<subseteq> S" using nS by auto
  {
    fix i
    assume i: "i < n" 
    obtain Ei Hi where idi: "EHi i = (Ei, Hi)" by force
    obtain Esi Hsi where idsi: "EHi (Suc i) = (Esi, Hsi)" by force
    from HS[of "Suc i"] i idsi have HS: "Hsi \<subseteq> S" by auto
    {
      fix H s t
      assume "H \<subseteq> S" and st: "(s,t) \<in> rstep (R \<union> H)" 
      hence "(s,t) \<in> rstep S" using RS by fast
      also have "\<dots> \<subseteq> S" using ctxt_S subst_S by auto
      finally have "(s,t) \<in> rstep (R \<union> H) \<inter> S" using st by auto
    } note add_S = this
    from steps i idi idsi have "((Ei,Hi), (Esi,Hsi)) \<in> ri_step'" by auto
    from this HS
    have "(EHi i, EHi (Suc i)) \<in> ri_step" unfolding idi idsi
    proof (induct rule: ri_step'.induct)
      case *: (expand' s t E E' H)
      from * have "((s, t), E') \<in> expand_eq_set' H" by auto
      hence "((s, t), E') \<in> expand_eq_set H" 
        by (induct rule: expand_eq_set'.induct, intro expand_eq_set.intros, auto simp del: Expd_rename.simps)
      with * show ?case by (intro ri_step.expand, auto)
    next
      case *: (simplifyl' s t E s' H)
      from * add_S[of H] show ?case by (intro ri_step.simplifyl, auto simp: simplifyl_eq)
    next
      case *: (simplifyr' s t E t' H)  
      from * add_S[of H] show ?case by (intro ri_step.simplifyr, auto simp: simplifyr_eq)
    next
      case (delete' s E H)
      then show ?case by (intro ri_step.delete, auto simp: delete_eq)
    qed
  }
  with init last show ?thesis unfolding rirun full_ri_run_def ri_run_def by auto
qed

end
end