(*
  Author: Main development by group of Takahito Aoto
  The following changes were done by RT: 
  - added to IsaFoR and adjusted to current Isabelle version
  - deleted everything related to renaming, since this is no longer required
*)
theory Basic_Term
  imports 
    First_Order_Rewriting.Trs
    First_Order_Rewriting.Unification_More
    TRS.Unifiers_More
    Derivation
begin

fun constr :: "'f sig \<Rightarrow> ('f,'v) term \<Rightarrow> bool" where
  "constr C (Var x) \<longleftrightarrow>  True" |
  "constr C (Fun f ts) \<longleftrightarrow> (f,length ts) \<in> C \<and>(\<forall>t \<in> set ts. constr C t)"


lemma not_constr:
  "(\<exists>h\<in>funas_term t. h\<notin>c) \<longrightarrow> \<not>constr c t"
proof (rule impI)
  assume a:"\<exists>h\<in>funas_term t. h\<notin>c"
  show "\<not>constr c t" 
  proof (rule ccontr)
    assume "\<not>\<not>constr c t"
    then have "constr c t" by simp
    then show False using a
    proof (induct t)
      case (Var x)
      then have "\<forall>h\<in>funas_term (Var x). h\<in>c" by simp
      then show ?case using Var by simp
    next
      case (Fun x1a x2)
      then have "\<forall>x\<in> set x2. constr c x" by simp
      then have "\<exists>x\<in>set x2. (\<exists>h\<in>funas_term x. h \<notin> c) \<Longrightarrow> False" using Fun by blast
      also
      { assume "\<forall>x\<in>set x2. \<forall>h\<in>funas_term x. h \<in> c"
        then have "(x1a,length x2)\<notin> c" using Fun by simp
        then have "\<not>constr c (Fun x1a x2)" by simp
        then have ?case using Fun by simp
      }
      ultimately show ?case by auto
    qed
  qed
qed

lemma covered_sig:
  assumes "\<forall>f\<in>funas_term t. f\<in>sig"
    and "t = (Fun f ts)"
  shows "(f,length ts) \<in>sig"
proof -
  from assms have "(f,length ts)\<in>funas_term (Fun f ts)" by simp
  from this show ?thesis 
    using assms  by blast
qed


lemma funas_constr:"\<forall>g\<in>funas_term t . g\<in>c \<Longrightarrow> constr c t"
proof (induction t)
  case (Fun f ss)
  from this have 1:"\<forall>s\<in> set ss. constr c s" by simp
  from this have "(f, length ss)\<in>c " by (simp add: Fun.prems)
  from this 1 show ?case by simp
qed auto



lemma constr_funas:"constr c t \<Longrightarrow> \<forall>g\<in>funas_term t. g\<in>c"
proof (induction t)
  case (Fun g ts)
  assume a1:"constr c (Fun g ts)"
  then have 2:"(g,length ts)\<in>c" by simp
  from a1 have "\<forall>t\<in> set ts. constr c t" by simp
  from this Fun.IH have "\<forall>t\<in>set ts. \<forall>f \<in> (funas_term t). f \<in> c" by simp
  from 2 this show ?case by simp 
qed auto

lemma def_not_constr:
  assumes "\<exists>f\<in>funas_term t. f\<in>d"
    and "d\<inter>c = {}" 
  shows "\<not>constr c t"
proof -
  {
    assume "constr c t"
    then have *:"\<forall>g\<in>funas_term t. g\<in>c" using constr_funas by auto
    obtain f where "f\<in>funas_term t \<and> f\<in>d" using assms(1) by auto
    then have "f \<in>d \<and> f\<in>c" using * by simp
    then have False using assms(2) by auto
  }
  then show ?thesis by auto
qed 

lemma not_constr_def:
  assumes a1:"\<not>constr c t"
  shows "is_Var t \<or> (\<exists>f\<in>funas_term t. f\<notin>c)" using assms funas_constr by blast

definition ground_terms ::"('f,'v) term set" where
  [simp]:"ground_terms = {t | t. ground t}"

lemma ground_terms:
  "ground s \<longleftrightarrow> s\<in>ground_terms " by simp

fun basic :: "'f sig \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "basic D C (Var x) \<longleftrightarrow> False" |
  "basic D C (Fun f ts) \<longleftrightarrow> (f,length ts)\<in>D \<and> (\<forall>t \<in> set ts. constr C t)"

fun ground_basic :: "'f sig \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where
    "ground_basic d c t \<longleftrightarrow> ground t \<and> basic d c t"


fun ground_subst :: " ('f, 'v) subst  \<Rightarrow> bool" where
  "ground_subst \<sigma>  \<longleftrightarrow> (\<forall>v \<in> subst_domain \<sigma>. ground (\<sigma> v))"

fun constr_subst :: "'f sig \<Rightarrow> ('f,'v) subst \<Rightarrow> bool" where
  "constr_subst c \<sigma>  \<longleftrightarrow> (\<forall>t \<in> subst_range \<sigma>. constr c t)"

lemma constr_subst[simp]:"constr_subst c \<sigma> \<longleftrightarrow>(\<forall>v \<in> subst_domain \<sigma>. constr c (\<sigma> v))" by simp

fun subst_union::"('f,'v) subst \<Rightarrow> ('f,'v) subst \<Rightarrow> ('f,'v) subst" (infixl "\<union>\<^sub>s" 67)
  where [intro]:"\<sigma> \<union>\<^sub>s \<rho> = (\<lambda>x. if x\<in>subst_domain \<sigma> then \<sigma> x else \<rho> x)"

lemma  subst_domain_covered:
  assumes "vars_term s\<subseteq>subst_domain \<sigma>"
  shows "\<forall>\<rho>. s\<cdot>(\<sigma>\<union>\<^sub>s \<rho>) = s\<cdot>\<sigma>" 
proof -
  have "\<forall>v\<in>vars_term s. v\<in>subst_domain \<sigma>" using assms by auto
  then have "\<forall>\<rho>. \<forall>v\<in>vars_term s. \<sigma> v = (\<sigma>\<union>\<^sub>s\<rho>) v" by simp
  then show ?thesis by (metis term_subst_eq)
qed

fun gc_subst ::" 'f sig \<Rightarrow> ('f, 'v) subst  \<Rightarrow> bool" where
  "gc_subst c \<sigma> \<longleftrightarrow> (\<forall>t \<in> subst_range \<sigma>. constr c t) \<and> (ground_subst \<sigma> )" 

lemma gc_subst:
  "gc_subst c \<sigma> \<longleftrightarrow> ((\<forall>v \<in> subst_domain \<sigma>. constr c (\<sigma> v) \<and> ground (\<sigma> v)))"  by auto


lemma range_imp_domain_AllP:
  assumes "\<forall>t\<in>subst_range \<sigma>. P t"
    and "vars_term s \<subseteq> subst_domain \<sigma>"
  shows "\<forall>v\<in> vars_term s. P (\<sigma> v)" 
proof -
  have "\<forall>v\<in>subst_domain (\<sigma>|s(vars_term s)).\<exists>t\<in>subst_range(\<sigma>|s(vars_term s)). \<sigma> v = t"
    using image_eqI in_subst_restrict subsetCE subst_domain_vars_term_subset subst_range.simps by metis
  then have *:"\<forall>v\<in>(vars_term s).\<exists>t\<in>subst_range(\<sigma>|s(vars_term s)). \<sigma> v = t" using assms(2) 
    using notin_subst_domain_imp_Var subst_domain_def by fastforce
  have "\<forall>t\<in>subst_range (\<sigma>|s(vars_term s)). \<forall>v\<in>(vars_term s). \<sigma> v = t \<longrightarrow> P (\<sigma> v)" using assms by fastforce
  then show ?thesis 
    using * by blast
qed

lemma range_imp_domain_ExP:
  assumes "\<exists>t\<in>subst_range (\<sigma>|s vars_term s). P t"
    and "vars_term s \<subseteq> subst_domain \<sigma>"
  shows "\<exists>v\<in> vars_term s. P (\<sigma> v)" 
proof -
  obtain t where t:"t\<in>subst_range (\<sigma>|s vars_term s) \<and> P t" using assms by auto
  then have "\<exists>v\<in>subst_domain (\<sigma>|s vars_term s). \<sigma> v = t" 
    using assms(2) subst_domain_vars_term_subset subst_range.simps by fastforce
  then have "\<exists>v\<in> vars_term s. \<sigma> v = t" using assms(2) t 
    by (meson contra_subsetD subst_domain_vars_term_subset)
  then show ?thesis using t by auto
qed  

lemma subst_range_restrict[simp]:
  "subst_range (\<sigma>|s vs) \<subseteq> subst_range \<sigma>" 
proof (rule subsetI)
  fix t
  assume "t\<in>subst_range (\<sigma>|s vs)"
  then obtain v where "v\<in>subst_domain (\<sigma>|s vs) \<and> (\<sigma>|s vs) v = t" by auto
  then have "\<sigma> v = t \<and> t \<noteq> Var v" 
    by (metis (mono_tags, lifting) in_subst_restrict mem_Collect_eq notin_subst_restrict subst_domain_def)
  then show "t\<in>subst_range \<sigma>" 
    using notin_subst_domain_imp_Var by fastforce
qed

lemma subst_domain_restrict[simp]:
  "subst_domain (\<sigma>|s vs) = subst_domain \<sigma> \<inter>vs " (is "?l= ?r")
proof
  show "?l \<subseteq>?r"
  proof(rule subsetI)
    fix v assume "v\<in>subst_domain (\<sigma>|s vs)"
    then have a:"(\<sigma>|s vs) v \<noteq>Var v" using subst_domain_def by fast
    have "v\<in>subst_domain \<sigma> \<and> v\<in>vs"
    proof (rule ccontr)
      assume "\<not>(v\<in>subst_domain \<sigma> \<and> v\<in>vs)"
      then consider "v\<notin>subst_domain \<sigma>" | "v\<notin>vs" by auto
      then show False
      proof cases
        case 1
        then have "(\<sigma> |s vs) v = \<sigma> v" using subst_restrict_def a by metis
        also have "\<sigma> v = Var v" using 1 notin_subst_domain_imp_Var by fast
        ultimately show ?thesis using a by simp
      next
        case 2
        then have "(\<sigma> |s vs) v = Var v" by simp
        then show ?thesis using a by simp
      qed
    qed
    then show "v\<in>subst_domain \<sigma>\<inter>vs" by simp 
  qed
next
  show "?r\<subseteq>?l"
  proof (rule subsetI)
    fix v assume "v\<in>subst_domain \<sigma>\<inter>vs"
    then also have "(\<sigma>|s vs) v = \<sigma> v" by simp
    ultimately also have "\<sigma> v \<noteq>Var v" using subst_domain_def by fast
    ultimately have "(\<sigma>|s vs) v \<noteq> Var v" by simp
    then show "v\<in>?l" using subst_domain_def by fast
  qed        
qed


lemma csubst_constrraint:"constr_subst c (\<sigma>|s vs) \<and> ws \<subseteq>vs \<Longrightarrow> constr_subst c (\<sigma>|s ws) " 
proof -
  assume *:"constr_subst c (\<sigma>|s vs) \<and> ws\<subseteq> vs"
  then have "subst_range(\<sigma>|s ws) = subst_range((\<sigma>|s vs)|s ws)" by (metis inf.absorb_iff2 subst_restrict_Int)
  then have **:"subst_range(\<sigma>|s ws) \<subseteq>subst_range(\<sigma>|s vs)" using subst_range_restrict by blast
  then have "\<forall>t \<in> subst_range (\<sigma> |s vs). constr c t" using * by simp
  then show ?thesis using ** by auto
qed

lemma csubst_constrraint_union:
  "constr_subst c (\<sigma>|s (vs\<union>ws))\<Longrightarrow> constr_subst c (\<sigma>|s vs) \<and> constr_subst c (\<sigma>|s ws)"
proof -
  assume "constr_subst c (\<sigma>|s (vs\<union>ws))" 
  then have "vs \<subseteq>(vs\<union>ws) \<and> ws\<subseteq>(vs\<union>ws) \<and> constr_subst c (\<sigma>|s (vs\<union>ws))" by simp
  then show ?thesis using csubst_constrraint by blast
qed

lemma [simp]:"subst_domain (\<sigma>|s (vs\<union>ws)) =subst_domain (\<sigma>|s vs) \<union> subst_domain (\<sigma>|s ws)" (is "?l=?r") by auto


lemma csubst_constrraint_union':
  "\<not>constr_subst c (\<sigma>|s (vs\<union>ws))\<Longrightarrow> \<not>constr_subst c (\<sigma>|s vs) \<or> \<not>constr_subst c (\<sigma>|s ws)" using csubst_constrraint_union 
proof -
  assume a1:"\<not>constr_subst c (\<sigma>|s (vs\<union>ws))"
  {
    assume a2:"constr_subst c (\<sigma>|s vs) \<and> constr_subst c (\<sigma>|s ws)"
    then have "subst_domain (\<sigma>|s (vs\<union>ws)) =subst_domain (\<sigma>|s vs) \<union> subst_domain (\<sigma>|s ws)" by auto
    have "\<forall>v\<in>subst_domain (\<sigma>|s vs). constr c ((\<sigma>|s vs) v) \<and> (\<forall>v\<in>subst_domain(\<sigma>|s ws). constr c ((\<sigma>|s ws) v))" using a2 constr_subst apply auto done
    then have "\<forall>v\<in>subst_domain (\<sigma>|s vs)\<union>subst_domain (\<sigma>|s ws). constr c ((\<sigma>|s (vs\<union>ws)) v) " using a2 subst_domain_restrict apply auto done
    then have False using a1 by force
  }
  then show ?thesis using csubst_constrraint by blast
qed


lemma g_subst_ground :
  assumes "ground_subst \<sigma>"
    and "vars_term s \<subseteq> subst_domain \<sigma>"
  shows "ground (s\<cdot>\<sigma>)"
proof -
  from assms have "\<forall>t\<in>subst_range \<sigma>. ground t" by simp
  from this assms(2) have "\<forall>v\<in>vars_term s. ground (\<sigma> v)" 
    using range_imp_domain_AllP by blast
  from this show ?thesis by simp
qed

lemma subt_not_constr[simp]:
  assumes "u\<unlhd>s"
    and "\<not>constr c u"
  shows "\<not>constr c s"
  by (meson assms(1) assms(2) constr_funas funas_constr set_mp supteq_imp_funas_term_subset)

lemma g_subst_not_constr:
  assumes "\<not>(constr_subst c (\<sigma>|s vars_term s))"
    and "vars_term s \<subseteq> subst_domain \<sigma>"
  shows "\<not>constr c (s\<cdot>\<sigma>)"
proof -
  have "\<not>(constr_subst c \<sigma>)" using assms by (metis csubst_constrraint subst_restrict_domain)
  from assms have "\<exists>t\<in>subst_range (\<sigma>|s vars_term s). \<not>constr c t" by simp
  then have "\<exists>v\<in>vars_term s. \<not>constr c (\<sigma> v)" using range_imp_domain_ExP assms by auto
  from this assms obtain v where v:"v \<in> vars_term s \<and> \<not>constr c (\<sigma> v)" by auto
  from this assms have "\<exists>u\<unlhd>(s\<cdot>\<sigma>). u = \<sigma> v"
    by (metis ctxt_imp_supteq eval_term.simps(1) subst_apply_term_ctxt_apply_distrib supteq_ctxtE vars_term_supteq)
  from this v have "\<exists>u\<unlhd>(s\<cdot>\<sigma>). \<not>constr c u" by blast
  from this subt_not_constr show ?thesis by auto
qed

lemma gc_subst_ground :
  assumes "gc_subst C \<sigma>"
    and "vars_term s \<subseteq> subst_domain \<sigma>"
  shows "ground (s\<cdot>\<sigma>)"
proof -
  have "\<forall>t\<in>subst_range \<sigma>. ground t" using assms by simp
  then have "\<forall>v\<in>vars_term s. ground (\<sigma> v)" using range_imp_domain_AllP assms by auto
  from this show ?thesis by simp
qed



(* t\<sigma> is instance of t *)
(* then, s is instance of t if s=t\<sigma> *)
inductive
  ground_subst_instance :: "('f, 'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" ("(_/ \<preceq>\<^sub>g _)" [56, 56] 55)
  where
    ground_subst_instanceI [intro]:
    "\<exists>\<sigma>\<^sub>g. ground (s\<cdot>\<sigma>\<^sub>g) \<and> s \<cdot> \<sigma>\<^sub>g = t \<Longrightarrow> s \<preceq>\<^sub>g t"

lemma csubst: 
  assumes "\<forall>g\<in> funas_term t. g\<in>c" 
    and "constr_subst c \<sigma>\<^sub>g" 
    and "vars_term t\<subseteq>subst_domain \<sigma>\<^sub>g" 
  shows "(\<forall>g\<in> funas_term (t\<cdot>\<sigma>\<^sub>g). g \<in>c )"
proof -
  have "\<forall>t\<in>subst_range \<sigma>\<^sub>g. constr c t" using assms by simp
  also then have "\<forall>v\<in>(vars_term t). constr c (\<sigma>\<^sub>g v)" using assms range_imp_domain_AllP by blast
  then have "\<forall>v\<in>(vars_term t). \<forall>f\<in> funas_term (\<sigma>\<^sub>g v). f\<in>c" using constr_funas by blast
  ultimately have "\<Union> (funas_term ` (\<sigma>\<^sub>g ` vars_term t)) \<subseteq> c" by blast
  then show "\<forall>g\<in> funas_term (t\<cdot>\<sigma>\<^sub>g). g\<in>c" using assms funas_term_subst[of t \<sigma>\<^sub>g] by force
qed



lemma rstep_funas_lhs:"f\<in>(\<Union> t\<in> lhss R. funas_term t) \<Longrightarrow> (f\<in> (\<Union>t\<in>lhss (rstep R). funas_term t))" by auto

lemma csubst_constr_constr:
  assumes "constr_subst c \<sigma>"
    and "constr c s"
    and "vars_term s\<subseteq> subst_domain \<sigma>"
  shows "constr c (s\<cdot>\<sigma>)" 
proof -
  have "\<forall>f\<in>funas_term s. f\<in>c" using assms(2) constr_funas by auto
  then have "\<forall>f\<in>funas_term (s\<cdot>\<sigma>). f\<in>c" using csubst assms by simp
  then show ?thesis using funas_constr by auto
qed

lemma gc_subst_basic:
  assumes "constr_subst c \<sigma>\<^sub>g" 
    and "basic d c s"
    and "vars_term s \<subseteq> subst_domain \<sigma>\<^sub>g"
    and "d\<inter>c ={}"
  shows "basic d c (s\<cdot>\<sigma>\<^sub>g)"
proof -
  have "\<exists>f ss. s = Fun f ss \<and> (f,length ss)\<in>d \<and> (\<forall>t\<in> set ss . constr c t)"  by (meson assms(2) basic.elims(2))
  from this obtain f ss where fss:"s = Fun f ss \<and> (f,length ss)\<in>d \<and> (\<forall>t\<in> set ss . constr c t)" by auto
  have f1:"\<forall>t\<in>set ss. vars_term t \<subseteq>subst_domain \<sigma>\<^sub>g" using fss assms(3) by auto
  have *:"\<forall>t\<in>set ss. vars_term t \<subseteq>vars_term s" using fss by auto
  then have "\<forall>t\<in>set ss. constr_subst c \<sigma>\<^sub>g" using fss assms by metis
  then have f2:"\<forall>t\<in>set ss. constr c (t\<cdot>\<sigma>\<^sub>g)" using fss assms(1) assms(3) csubst_constr_constr using * by blast
  have "\<forall>t\<in>subst_range \<sigma>\<^sub>g. constr c t" using assms by simp
  then have "\<forall>v\<in>(vars_term s). constr c (\<sigma>\<^sub>g v)" using range_imp_domain_AllP assms(3) by blast
  then have "\<forall>t\<in>set ss. \<forall>g \<in>funas_term t. g \<in> c" using constr_funas fss by blast 
  then have "\<forall>t\<in>set ss. constr c (t\<cdot>\<sigma>\<^sub>g)" using csubst_constr_constr f2 by simp
  from this fss show "basic d c (s\<cdot>\<sigma>\<^sub>g)" by simp
qed

fun quasi_reducible :: "'f sig \<Rightarrow> 'f sig \<Rightarrow> ('f, 'v) trs \<Rightarrow> bool" where
  "quasi_reducible D C R \<longleftrightarrow> (\<forall>t. ground t \<and> basic D C t \<longrightarrow> t\<notin> (NF (rstep R)))"

lemma basic: "(d \<inter> c = {}) \<and> basic d c t \<Longrightarrow>(\<exists>f ts. t = Fun f ts \<and> (f,length ts)\<in>d \<and> (\<forall>t\<in>set ts. constr c t))"
  by (meson basic.elims(2))

inductive_set defined_funas ::"('f,'v) trs\<Rightarrow> 'f sig" for R  where
  "f \<in> funas_trs R \<and> (\<exists>rule\<in>R. root (fst rule) = Some f) \<Longrightarrow> f \<in> defined_funas R"

inductive_set constr_funas ::"('f,'v)trs \<Rightarrow> 'f sig" for R where
  "f \<in> funas_trs R \<and> f \<notin> defined_funas R \<Longrightarrow> f \<in> constr_funas R"    


lemma rule_defined:
  assumes "\<forall>rule \<in>R. \<not> is_Var(fst rule)"
  shows " \<forall>rule\<in>R.(\<exists> f ss. fst rule = Fun f ss \<and> (f,length ss) \<in> (defined_funas R))" 
proof
  fix rule 
  show "rule\<in>R \<Longrightarrow> (\<exists> f ss. fst rule = Fun f ss \<and> (f,length ss) \<in> (defined_funas R))" 
  proof (rule impE, force)
    assume a1:"rule\<in>R"
    from assms a1 have "\<exists> f ss. fst rule = Fun f ss" by blast
    then obtain f ss where t1:"fst rule = Fun f ss" by auto
    then have "root (fst rule) =  Some (f,length ss)" by simp
    then have t2:"(f, length ss) \<in> (defined_funas R)" 
      by (metis a1 defined_def defined_funas.intros defined_funas_trs prod.collapse)
    from t1 t2 have "fst rule = (Fun f ss) \<and> (f,length ss) \<in> (defined_funas R)" by simp
    then have " (\<exists>f ss. fst rule = (Fun f ss) \<and> (f,length ss) \<in> (defined_funas R))" by simp
    then show "rule \<in> R \<Longrightarrow> True \<Longrightarrow> \<exists>f ss. fst rule = Fun f ss \<and> (f, length ss) \<in> defined_funas R" by simp
  qed
qed




lemma d_c_disjoint:
  "defined_funas R \<inter> constr_funas R = {} \<and> defined_funas R \<union> constr_funas R = funas_trs R" 
proof -
  have t1:"defined_funas R \<inter> constr_funas  R= {}"
    using constr_funas.cases by blast
  have "\<forall>f \<in> funas_trs R . f\<in> defined_funas R \<union> constr_funas R" 
    using constr_funas.intros defined_funas.cases defined_funas.intros by blast
  from this have 1:"funas_trs R \<subseteq> defined_funas R \<union> constr_funas R " by auto
  have "\<forall>f \<in> defined_funas R \<union> constr_funas R. f\<in>funas_trs R " using defined_funas.cases constr_funas.cases by blast
  from this have 2:"defined_funas R \<union> constr_funas R \<subseteq> funas_trs R" by auto
  from 1 2 have t2:"defined_funas R \<union> constr_funas R = funas_trs R" by simp
  from t1 t2 show ?thesis by simp
qed    
lemma subt_of_basic_constr:
  assumes "basic d c s"
    and "d \<inter> c = {}"
    and "u\<lhd>s"
  shows "constr c u" 
proof -
  from assms obtain f ss where es:"s = Fun f ss \<and> (f, length ss) \<in>d \<and> (\<forall>t\<in>set ss. constr c t)" by (meson basic.elims(2))
  from this have t1:"\<forall>g\<in>(\<Union>t\<in> set ss. funas_term t). g \<in> c" using constr_funas by auto
  from this es have 1:"(f,length ss) \<notin> (\<Union>t\<in>set ss. funas_term t)" using assms(2) constr_funas.simps by blast
  from this es have 2:"(f,length ss)\<notin> funas_term u" using assms(3) es by fastforce
  from es have 3:"funas_term s = (\<Union>t\<in>set ss. funas_term t) \<union> {(f,length ss)}" by simp
  from this 1 have "funas_term s -{(f,length ss)} =  (\<Union>t\<in>set ss. funas_term t)" by blast
  from this 2 3 have t2:"funas_term u \<subseteq> (\<Union>t\<in>set ss. funas_term t)" using assms(3) supteq_imp_funas_term_subset
    by (smt Un_insert_right assms(3) insert_iff set_mp subrelI subterm.dual_order.strict_implies_order sup_bot.right_neutral )
  from t1 t2 show ?thesis 
    by (meson funas_constr set_mp)
qed


lemma subt_of_basic_deined_eq:
  assumes "basic d c s"
    and "d \<inter> c = {}"
    and "u \<unlhd> s"
    and "\<not>constr c u"
  shows "u = s"
proof -
  from assms(3) have 1:" u \<lhd> s \<or> u = s" by auto
  from assms have "u\<lhd> s \<Longrightarrow> constr c u" using subt_of_basic_constr by blast
  from this 1 assms show "u = s" by auto
qed  


lemma ground_not_constr_ex_root_not_constr:
  assumes "ground t \<and> \<not>constr c t"
  shows "\<exists>f ss. (Fun f ss)\<unlhd>t \<and>  (f,length ss)\<notin>c \<and> (\<forall>s\<in>set ss. constr c s)" using assms
proof (induction t)
  case (Fun f xs)
  then have gx:"\<forall>x\<in>set xs. ground x" by simp
  have "ground (Fun f xs) \<and> \<not>constr c (Fun f xs)" using Fun by simp
  then show "\<exists>g ss. (Fun g ss)\<unlhd> (Fun f xs) \<and>  (g,length ss)\<notin>c \<and> (\<forall>s\<in>set ss. constr c s)"
  proof(cases "(f,length xs)\<in>c")
    case True
    then have "\<exists>x\<in>set xs. ground x \<and> \<not>constr c x" using Fun by auto
    then have "\<exists>x\<in>set xs. (\<exists>g ss. (Fun g ss)\<unlhd>(Fun f xs) \<and>
                  (g,length ss)\<notin>c \<and> (\<forall>s\<in>set ss. constr c s))" using Fun by blast
    then show ?thesis by simp
  next
    case False
    then show ?thesis 
    proof (cases "\<forall>x\<in>set xs. constr c x")
      case True
      then have "(Fun f xs)\<unlhd>(Fun f xs) \<and>(f,length xs)\<notin>c \<and> (\<forall>s\<in>set xs. constr c s)" using False
        by (meson Fun_supteq constr_funas subsetI)
      then show ?thesis by auto
    next
      case False
      then have "\<exists>x\<in>set xs. ground x \<and> \<not>constr c x" using gx by simp
      then show ?thesis using Fun by blast
    qed
  qed
qed simp



lemma ground_not_constr_ex_defined:
  assumes "ground t \<and> \<not>constr c t"
    and "\<forall>t. funas_term t \<subseteq>d\<union>c" and "d\<inter>c = {}" 
  shows "\<exists>u\<unlhd>t. basic d c u \<and> ground u"
proof- 
  have "\<forall>f\<in>funas_term t. f\<in>d\<union>c" using assms(2) funas_term_subst by blast
  also obtain f ss where u:"(Fun f ss)\<unlhd>t\<and> (f,length ss)\<notin>c \<and> (\<forall>s\<in>set ss. constr c s)" using assms(1) ground_not_constr_ex_root_not_constr by blast
  ultimately have "(f,length ss)\<in>d" using assms by auto
  also have "ground (Fun f ss)" using u assms(1) by auto
  ultimately show ?thesis using u by auto
qed

lemma rstep_preserve_ground:
  assumes "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l"
    and "ground s" and "(s,t)\<in>rstep R" 
  shows "ground t" using assms by fastforce


lemma subst_one_change_rewritable:
  assumes "v\<in>vars_term (t::('a,'b)term)"
    and "\<forall>w. w\<noteq>v \<longrightarrow> \<sigma> w =\<rho> w"  
    and "(\<sigma> v, \<rho> v)\<in> (rstep R)^+"
  shows "(t\<cdot>\<sigma>,t\<cdot>(\<rho>::('a,'b)subst))\<in>(rstep R)^+" using assms(1)
proof (induction t)
  case (Var x)
  then have "v\<in> vars_term (Var x)" using assms by simp
  then show ?case using assms by simp
next
  case (Fun x1a x2)
  then have "\<forall>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). v\<in>vars_term (x2!i) \<longrightarrow> ((x2!i)\<cdot>\<sigma>,(x2!i)\<cdot>\<rho>)\<in>(rstep R)^+" using assms(2) Fun by simp
  then have *:"\<forall>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). v\<in>vars_term (x2!i) \<longrightarrow> ((map (\<lambda>s. s\<cdot>\<sigma>) x2)!i,(map (\<lambda>s. s\<cdot>\<rho>) x2)!i)\<in>(rstep R)^+" by simp
  also have "\<exists>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). v\<in>vars_term (x2!i)" using assms Fun using var_imp_var_of_arg by force      
  ultimately have "\<exists>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). (((map (\<lambda>s. s\<cdot>\<sigma>) x2)!i),((map (\<lambda>s. s\<cdot>\<rho>) x2)!i))\<in>(rstep R)^+" by auto
  then have **:"\<exists>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). ((map (\<lambda>s. s\<cdot>\<sigma>) x2)!i,(map (\<lambda>s. s\<cdot>\<rho>) x2)!i)\<in>(rstep R)^+" using in_set_idx nth_map by simp
  have "\<forall>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). v\<notin>vars_term (x2!i) \<longrightarrow>(map (\<lambda>s. s\<cdot>\<sigma>) x2)!i = (map (\<lambda>s. s\<cdot>\<rho>) x2)!i" 
    using assms(2) length_map nth_map term_subst_eq by metis
  then have "(\<forall>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). ((map (\<lambda>s. s\<cdot>\<sigma>) x2)!i,(map (\<lambda>s. s\<cdot>\<rho>) x2)!i)\<in>(rstep R)^*) \<and> 
              (\<exists>i<length (map (\<lambda>s. s\<cdot>\<sigma>) x2). ((map (\<lambda>s. s\<cdot>\<sigma>) x2)!i,(map (\<lambda>s. s\<cdot>\<rho>) x2)!i)\<in>(rstep R)^+)" using * ** by auto
  then have "(Fun x1a(map (\<lambda>s. s\<cdot>\<sigma>) x2), Fun x1a (map (\<lambda>s. s\<cdot>\<rho>) x2))\<in>(rstep R)^+" using * ctxt_closed_rstep rtrancl_trancl_into_trancl length_map 
    by metis
  then show ?case by simp
qed

lemma min_iff_wf:
  "(\<forall>S. S\<noteq>{} \<longrightarrow> (\<exists>m\<in>S. \<forall>s\<in>S. (s,m)\<notin>r)) \<longleftrightarrow> wf r" (is "?L \<longleftrightarrow> ?R")
proof (rule)
  assume a:?L show "?R" using a all_not_in_conv wfI_min by metis
next
  assume a:?R show "?L" using a by (meson wfE_min')
qed    

lemma min_iff_wfP:
  "(\<forall>S. S\<noteq>{} \<longrightarrow> (\<exists>m\<in>S. \<forall>s\<in>S. \<not>r s m)) \<longleftrightarrow> wfP r" (is "?L \<longleftrightarrow> ?R") using wfP_eq_minimal all_not_in_conv by metis  


lemma count_list_member:"count_list vs a  \<ge> 1 \<longleftrightarrow> List.member vs a" (is "?l \<longleftrightarrow>?r")
proof 
  assume ?l thus ?r  using in_set_member by fastforce
next
  assume ?r thus ?l apply (induct vs) apply (simp ) apply (simp add:member_rec)
    using member_rec(1) by fastforce
qed

lemma remdups_count_1:"(\<forall>v\<in>set (remdups vs).  count_list (remdups vs) v = 1 )" 
proof (rule ccontr)
  assume "\<not>(\<forall>v\<in>set (remdups vs).  count_list (remdups vs) v = 1 )"
  then have "(\<exists>v\<in>set (remdups vs).  count_list (remdups vs) v \<noteq> 1)" by simp
  then obtain v where v:"v\<in>set (remdups vs) \<and> ( count_list (remdups vs) v \<noteq>1)" by fastforce
  then consider " count_list (remdups vs) v = 0" | "count_list (remdups vs) v \<ge> 2" by linarith
  then show False
  proof cases
    case 1
    then have "\<not>List.member  (remdups vs) v" using count_list_member by force
    then have "v\<notin>set (remdups vs)" using member_def by fast
    then show ?thesis using v by simp
  next
    case 2
    then have "count_list (remdups vs) v \<ge> 2" by simp
    also have "count_list (remdups vs) v \<le>1" apply (induct vs) apply simp by simp
    ultimately show ?thesis by simp
  qed
qed

lemma nondup_vs:
  "finite S \<longrightarrow> (\<exists>vs. set vs = S \<and> (\<forall>v\<in>S. count_list vs v = 1))" 
proof (intro impI)
  assume a:"finite S"
  show "(\<exists>vs. set vs = S \<and> (\<forall>v\<in>S. count_list vs v = 1))"
  proof -
    obtain vs where vs:"set vs = S" using finite_list a by blast
    then obtain ws where ws:"ws = remdups vs"  by simp
    then have "set ws = set vs" by simp
    also then have "\<forall>v\<in>set ws.  count_list ws v = 1" using remdups_count_1 ws by fast
    ultimately show ?thesis using vs by auto
  qed
qed

lemma nondup_nonmember:
  "(\<forall>v\<in>set (a#vs). count_list (a#vs) v = 1) \<longrightarrow> a\<notin>set vs"
proof (rule impI,rule ccontr)
  assume a:"(\<forall>v\<in>set (a#vs). count_list (a#vs) v = 1)" assume "\<not>a\<notin>set vs"
  then have "a\<in>set vs" by simp
  then have "count_list vs a \<ge>1" 
    by (meson count_list_member in_set_member)
  then have "count_list (a#vs) a \<ge> 2" by simp
  then show False using a by simp
qed

lemma list_count_1_cons:
  "(\<forall>v\<in>set (a#vs). count_list (a#vs) v = 1) \<longrightarrow>  (\<forall>v\<in>set (vs). count_list (vs) v = 1)" 
  by (metis count_list.simps(2) insert_iff list.set(2) nondup_nonmember)

lemma not_constr_basic:
  "\<not>constr c t \<and> (funas_term t \<subseteq> d\<union>c) \<longrightarrow> (\<exists>u\<unlhd>t. basic d c u)"
proof (rule impI)
  assume "\<not>constr c t \<and>  (funas_term t \<subseteq> d\<union>c)"
  then show "(\<exists>u\<unlhd>t. basic d c u)"
  proof (induction t)
    case (Fun g ss)
    then have "(\<forall>f\<in>funas_term(Fun g ss). f\<in>c\<union>d)" by auto
    then have "\<forall>s\<in>set ss. (\<forall>f\<in>funas_term s. f\<in>c\<union>d)" by simp
    then have *:"\<forall>s\<in>set ss. \<not>constr c s \<longrightarrow> (\<exists>u\<unlhd>s. basic d c u)" using Fun by blast
    have "\<not>constr c (Fun g ss)" using Fun by simp
    then have **:"(g,length ss)\<notin>c \<or> (\<exists>s\<in>set ss. \<not>constr c s)" using constr.cases by simp
    then show ?case 
    proof (cases "\<exists>s\<in>set ss. \<not>constr c s")
      case True
      then obtain s where s: "s\<in>set ss \<and> \<not>constr c s" by auto
      then have "(\<exists>u\<unlhd>s. basic d c u)" using * by simp
      then show ?thesis using Fun s by blast
    next
      case False
      then have "\<forall>s\<in>set ss. constr c s" using False by simp
      also have "(g,length ss)\<notin>c" using ** False by simp
      ultimately show ?thesis using Fun by auto
    qed
  qed simp
qed

lemma ground_not_constr_rewritable:
  "\<not>constr c t \<and> (funas_term t \<subseteq> d\<union>c) \<and> ground t \<and> quasi_reducible d c R \<longrightarrow> t\<notin>NF(rstep R)"
proof (rule impI)
  assume a:"\<not>constr c t \<and>  (funas_term t \<subseteq> d\<union>c) \<and> ground t \<and> quasi_reducible d c R"
  then obtain u where u:"u\<unlhd>t\<and> basic d c u" using not_constr_basic by metis
  also then have "ground u" using a by auto
  ultimately have "u\<notin> NF(rstep R)" using a by simp
  also have "\<exists>C. C\<langle>u\<rangle> = t" using u by auto
  ultimately show "t\<notin>NF(rstep R)" by auto
qed                                  

lemma ground_rstep_ground:
  assumes "ground (s::('a,'b)term)" and "(s,u)\<in>rstep R" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" 
  shows "ground u" 
proof -
  obtain l1 r1 C1 and \<sigma>1::"('a,'b)subst" 
    where *:"(l1,r1)\<in>R \<and> s = C1\<langle>l1\<cdot>\<sigma>1\<rangle> \<and> u = C1\<langle>r1\<cdot>\<sigma>1\<rangle> " using assms by fast
  then have "ground C1\<langle>l1\<cdot>\<sigma>1\<rangle>" using assms by simp
  then have "ground C1\<langle>r1\<cdot>\<sigma>1\<rangle>" using assms(3) * apply simp  by blast
  then show ?thesis using * by simp
qed

lemma ground_rstep_rtrancl_ground:
  assumes "ground (s::('a,'b)term)" and "(s,u)\<in>(rstep R)^*" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" 
  shows "ground u"
proof-
  obtain i where "(s,u)\<in>(rstep R)^^i" using assms(2) by auto
  then show ?thesis
  proof (induction i arbitrary:u)
    case 0
    then show ?case using assms(1) by simp
  next
    case (Suc i)
    then obtain u' where u':"(s,u')\<in>(rstep R)^^i \<and> (u',u)\<in>rstep R" by auto
    then have "ground u'" using Suc(1) by blast
    then show ?case using ground_rstep_ground assms(3) u' by blast
  qed
qed    

lemma ground_imp_ex_reachable_constr:
  assumes "SN (rstep R)"
    and "quasi_reducible d c R"
    and "\<forall>t. funas_term t\<subseteq>d\<union>c" and "ground t" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l"
  shows "\<exists>t'. (t,t')\<in>(rstep R)^* \<and> constr c t'"
proof (cases "constr c t")
  case False
  also have "funas_term t\<subseteq>d\<union>c" using assms(3) funas_term_subst by blast
  ultimately have "t\<notin>NF(rstep R)" using ground_not_constr_rewritable assms(2) assms(4) by blast
  show ?thesis
  proof (rule ccontr)
    assume "\<not>(\<exists>t'. (t,t')\<in>(rstep R)^* \<and> constr c t')"
    then have *:"\<forall>t'. (t,t')\<in>(rstep R)^* \<longrightarrow> \<not>constr c t'" by simp
    {fix t'
      assume a2:"(t,t')\<in>(rstep R)^*" 
      then have "\<not>constr c t'" using * by simp
      also have "ground t'" using a2 assms(4) assms(5) ground_rstep_ground apply (induct rule:rtrancl_induct) apply blast by blast
      moreover have "funas_term t'\<subseteq>c\<union>d" using assms(3) funas_term_subst by blast
      ultimately have "t'\<notin>NF(rstep R)" using ground_not_constr_rewritable assms(2) by blast
    }
    show False
      by (meson SN_imp_WN WN_onE \<open>\<And>t'. (t, t') \<in> (rstep R)\<^sup>* \<Longrightarrow> t' \<notin> NF_trs R\<close> assms(1) iso_tuple_UNIV_I normalizability_E)
  qed
qed auto

lemma exchange_V_subst:
  assumes "finite V"
    and "V\<subseteq>subst_domain \<sigma>" and "\<forall>v\<in>V. (\<exists>u. (\<sigma> v,u)\<in>(rstep R)^+ \<and> P u)"
  shows "\<exists>\<rho>. (\<forall>w. w\<notin>V \<longrightarrow> \<sigma> w = \<rho> w) \<and>(\<forall>v\<in>V. (\<sigma> v, \<rho> v)\<in> (rstep R)^+ \<and> P (\<rho> v))"
proof -
  obtain vs where vs:"set vs = V \<and> (\<forall>v\<in>V. count_list vs v = 1) " using assms nondup_vs by blast
  then have "set vs \<subseteq> subst_domain \<sigma> \<and> (\<forall>v\<in>set vs. \<exists>u. (\<sigma> v,u)\<in>(rstep R)^+ \<and> P u)" using assms by simp
  also have "set vs \<subseteq> subst_domain \<sigma> \<and> (\<forall>v\<in>set vs. \<exists>u. (\<sigma> v,u)\<in>(rstep R)^+ \<and> P u) \<longrightarrow>
             (\<exists>\<rho>. (\<forall>w. w\<notin>(set vs) \<longrightarrow> \<sigma> w = \<rho> w) \<and>(\<forall>v\<in>(set vs). (\<sigma> v, \<rho> v)\<in> (rstep R)^+\<and> P(\<rho> v)))" 
  proof (rule impI)
    assume "set vs \<subseteq> subst_domain \<sigma> \<and> (\<forall>v\<in>set vs. \<exists>u. (\<sigma> v,u)\<in>(rstep R)^+ \<and> P u)"
    also have "(\<forall>v\<in>set vs. count_list vs v = 1)" using vs by simp
    ultimately show "(\<exists>\<rho>. (\<forall>w. w\<notin>(set vs) \<longrightarrow> \<sigma> w = \<rho> w) \<and>(\<forall>v\<in>(set vs). (\<sigma> v, \<rho> v)\<in> (rstep R)^+ \<and> P (\<rho> v)))" 
    proof (induction vs)
      case Nil
      then show ?case by auto
    next
      case (Cons a vs)
      then have *:"\<forall>v\<in> set (a#vs). count_list (a#vs) v = 1" by fast
      then have "\<forall>v\<in>set vs. count_list vs v = 1" using list_count_1_cons by fast
      also have "set vs \<subseteq>subst_domain \<sigma> \<and> (\<forall>v\<in>set vs. \<exists>u. (\<sigma> v,u)\<in>(rstep R)^+ \<and> P u)" using Cons by simp
      ultimately obtain \<rho> where "((\<forall>w. w\<notin>(set vs) \<longrightarrow> \<sigma> w = \<rho> w) \<and>(\<forall>v\<in>(set vs). (\<sigma> v, \<rho> v)\<in> (rstep R)^+ \<and> P (\<rho> v)))" using Cons by presburger
      also have "a\<notin>set vs" using Cons * nondup_nonmember by fast
      moreover obtain t where "(\<sigma> a,t)\<in>(rstep R)^+ \<and> P t" using Cons by auto
      ultimately have "(\<forall>w. w\<notin>(set (a#vs)) \<longrightarrow> \<sigma> w = (\<rho>(a:=t)) w) \<and>(\<forall>v\<in>(set (a#vs)). (\<sigma> v, (\<rho>(a:=t)) v)\<in> (rstep R)^+ \<and> P ((\<rho>(a:=t)) v))" by simp
      then show ?case by blast
    qed
  qed
  ultimately show ?thesis using vs by simp
qed  



lemma exchange_V_rewritable:
  assumes "finite V" 
    and "V\<inter> vars_term t \<noteq>{}"
    and "\<forall>w. w\<notin>V \<longrightarrow> \<sigma> w = \<rho> w"  
    and "\<forall>v\<in>V. (\<sigma> v, \<rho> v)\<in> (rstep R)^+"  
  shows "(t\<cdot>\<sigma>,t\<cdot>(\<rho>::('a,'b)subst))\<in>(rstep R)^+ " 
proof -
  obtain vs where vs:"set vs=V \<and> (\<forall>v\<in>V. count_list vs v = 1)" using assms  nondup_vs by metis
  also have "set vs\<inter> vars_term t \<noteq>{}\<and> (\<forall>w. w\<notin>set vs \<longrightarrow> \<sigma> w = \<rho> w) \<and> (\<forall>v\<in>set vs. (\<sigma> v, \<rho> v)\<in> (rstep R)^+) \<longrightarrow>(t\<cdot>\<sigma>,t\<cdot>(\<rho>::('a,'b)subst))\<in>(rstep R)^+" 
  proof (rule impI)
    assume a:"set vs\<inter> vars_term t \<noteq>{}\<and> (\<forall>w. w\<notin>set vs \<longrightarrow> \<sigma> w = \<rho> w) \<and> (\<forall>v\<in>set vs. (\<sigma> v, \<rho> v)\<in> (rstep R)^+)"
    also have "(\<forall>v\<in>set vs. count_list vs v = 1)" using vs by simp
    ultimately show "(t\<cdot>\<sigma>,t\<cdot>(\<rho>::('a,'b)subst))\<in>(rstep R)^+" 
    proof (induct vs arbitrary: \<rho>)
      case Nil
      then show ?case using Nil by simp
    next
      case (Cons a vs)
      then have anotinvs:"a\<notin>set vs" using nondup_nonmember by metis
      have vs_count_1:"(\<forall>v\<in>set vs. count_list vs v = 1)" using Cons list_count_1_cons by metis
      obtain \<rho>'::"('a,'b)subst" where \<rho>':"\<rho>' = \<rho>(a:= \<sigma> a)" by simp
      then have h1:"\<forall>w. w\<notin>set vs \<longrightarrow> \<sigma> w = \<rho>' w" using Cons by simp 
      then show ?case
      proof (cases "set vs\<inter> vars_term t \<noteq>{}")
        case True
        then have *:" (\<forall>v\<in>set vs. (\<sigma> v, \<rho>' v)\<in> (rstep R)^+)\<longrightarrow> (t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^+" using Cons vs_count_1 h1 
          by presburger
        have "\<forall>w\<in>set (a#vs). (\<sigma> w, \<rho> w)\<in> (rstep R)^+" using Cons by simp
        then have "\<forall>w\<in>set (vs). (\<sigma> w, \<rho> w)\<in> (rstep R)^+" by simp
        then have h3:"\<forall>w\<in>set vs. (\<sigma> w, \<rho>' w)\<in> (rstep R)^+" using \<rho>' by (simp add: anotinvs)
        then have "set vs \<noteq>{}" using True by auto
        then have **:"(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^+" using * Cons vs_count_1 h1 h3 by fast
        then show ?thesis 
        proof (cases "a\<in>vars_term t")
          case True
          then have "\<forall>w. w\<noteq>a \<longrightarrow> \<rho>' w =\<rho> w " using \<rho>' by simp
          moreover have "(\<rho>' a, \<rho> a)\<in>(rstep R)^+" using Cons \<rho>' by simp
          ultimately have "(t\<cdot>\<rho>',t\<cdot>\<rho>)\<in>(rstep R)^+" using subst_one_change_rewritable True by metis
          then show ?thesis using ** by simp
        next
          case False
          then have "t\<cdot>(\<rho>'|s vars_term t) = t\<cdot>(\<rho>|s vars_term t)" using \<rho>' fun_upd_other subst_ext by metis
          then have "t\<cdot>\<rho>' = t\<cdot>\<rho>" using coincidence_lemma by metis
          then show ?thesis using ** by simp
        qed
      next
        case False
        then have f1:"\<forall>v\<in>set vs. v\<notin>vars_term t " by auto
        then have "(\<forall>w. w \<noteq> a \<longrightarrow> (\<sigma>|s vars_term t) w = (\<rho>|s vars_term t) w)" using Cons notin_subst_restrict subst_restrict_def insert_iff list.simps(15) by metis
        then have "(\<forall>w. w \<noteq> a \<longrightarrow> (\<sigma>|s vars_term t) w = (\<rho>'|s vars_term t) w)" using \<rho>' unfolding subst_restrict_def by auto
        also have "\<forall>w. w=a \<longrightarrow> (\<sigma>|s vars_term t) w = (\<rho>'|s vars_term t) w" using \<rho>' apply (cases "a\<in>vars_term t") apply simp by simp
        ultimately have "(\<rho>'|s vars_term t) = (\<sigma>|s vars_term t)" using f1 h1 subst_ext by metis
        then have "t\<cdot>\<rho>' = t\<cdot>\<sigma>" using coincidence_lemma by metis
        have "a\<in>vars_term t" using Cons False by force
        also then have "(\<rho>' a,\<rho> a)\<in>(rstep R)^+" using Cons \<rho>' by force
        moreover have "\<forall>w. w\<noteq> a \<longrightarrow> \<rho>' w = \<rho> w" using \<rho>' by simp
        ultimately have "(t\<cdot>\<rho>',t\<cdot>\<rho>)\<in>(rstep R)^+" by (intro subst_one_change_rewritable)
        then show ?thesis by (simp add: \<open>t \<cdot> \<rho>' = t \<cdot> \<sigma>\<close>)
      qed
    qed 
  qed
  then show ?thesis using vs assms by simp
qed

lemma exchange_V_rewritable':
  assumes "finite V" 
    and "V\<inter> vars_term t \<noteq>{}"
    and "\<forall>w. w\<notin>V \<longrightarrow> \<sigma> w = \<rho> w"
    and "\<forall>v\<in>V. (\<sigma> v, \<rho> v)\<in> (rstep R)^+ \<and>  P (\<rho> v)"  
  shows "(\<forall>v\<in>vars_term t. ((\<sigma>::('a,'b)subst) v,(\<rho>::('a,'b)subst) v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^+)" 
proof -
  obtain vs where vs:"set vs=V \<and> (\<forall>v\<in>V. count_list vs v = 1)" using assms  nondup_vs by metis
  also have "set vs\<inter> vars_term t \<noteq>{}\<and> (\<forall>w. w\<notin>set vs \<longrightarrow> \<sigma> w = \<rho> w) \<and> (\<forall>v\<in>set vs. (\<sigma> v, \<rho> v)\<in> (rstep R)^+) \<longrightarrow> (\<forall>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^+)" 
  proof (intro impI)
    assume a:"set vs\<inter> vars_term t \<noteq>{}\<and> (\<forall>w. w\<notin>set vs \<longrightarrow> \<sigma> w = \<rho> w) \<and> (\<forall>v\<in>set vs. (\<sigma> v, \<rho> v)\<in> (rstep R)^+)"
    also have "(\<forall>v\<in>set vs. count_list vs v = 1)" using vs a by simp
    ultimately have "\<forall>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^*" 
    proof (intro ballI)
      fix v assume b:"v\<in>vars_term t" then show "(\<sigma> v,\<rho> v)\<in>(rstep R)^*"
      proof (cases "v\<in>set vs")
        case True
        then have "(\<sigma> v,\<rho> v)\<in>(rstep R)^+" using a by simp
        then show ?thesis using a trancl_into_rtrancl by simp
      next
        case False
        then show ?thesis using a by simp
      qed
    qed
    also have "\<exists>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^+"
    proof -
      obtain v where v:"v\<in> set vs\<inter> vars_term t " using a by auto
      then have "(\<sigma> v, \<rho> v)\<in>(rstep R)^+" using a by simp
      then show ?thesis using v by auto
    qed
    ultimately show "(\<forall>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^+)" by simp
  qed
  ultimately show ?thesis using assms by force
qed  



lemma ground_subst_domain_ex_reachable_constr:
  assumes "ground_subst \<sigma>" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R" 
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c"
  shows "\<forall>v\<in>subst_domain \<sigma>. \<exists>t. (\<sigma> v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t"
proof -
  have "\<forall>v\<in>subst_domain \<sigma>. ground (\<sigma> v)" using assms(1) unfolding ground_subst.simps by blast
  also then have "\<forall>v\<in>subst_domain \<sigma>. (\<exists>t'. (\<sigma> v,t')\<in>(rstep R)^* \<and> constr c t')" using ground_imp_ex_reachable_constr assms by blast
  ultimately also have "\<forall>v\<in>subst_domain \<sigma>. \<forall>t. (\<sigma> v,t)\<in>(rstep R)^* \<longrightarrow> ground t" using assms(2) ground_rstep_rtrancl_ground by blast
  ultimately show ?thesis by blast
qed

lemma ground_notconstr_subst_domain_ex_reachable_constr':   
  assumes "ground_subst \<sigma>" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R" 
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c" and "\<not>constr_subst c \<sigma>" 
  shows "\<forall>v\<in>subst_domain \<sigma>.\<not>constr c (\<sigma> v) \<longrightarrow>(\<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)"
proof -
  {fix v assume "v\<in>subst_domain \<sigma>"
    also have "\<forall>v\<in>subst_domain \<sigma>. \<exists>t. (\<sigma> v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t" using ground_subst_domain_ex_reachable_constr assms by blast
    ultimately obtain t where "(\<sigma> v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t" by blast
    also then have "\<not>constr c (\<sigma> v) \<longrightarrow> \<sigma> v \<noteq> t" by auto
    ultimately have "\<not>constr c (\<sigma> v) \<longrightarrow> (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t" by (meson rtranclD)
    then have "\<not>constr c (\<sigma> v) \<longrightarrow>(\<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)" by auto
  }
  then show "\<forall>v\<in>subst_domain \<sigma>.\<not>constr c (\<sigma> v) \<longrightarrow>(\<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)"by simp  
qed
lemma ground_notconstr_subst_domain_ex_reachable_constr:   
  assumes "ground_subst \<sigma>" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R" 
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c" and "\<not>constr_subst c \<sigma>" 
  shows "\<exists>v\<in>subst_domain \<sigma>.  \<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and>ground t \<and> constr c t " 
proof- 
  {fix v assume "v\<in>subst_domain \<sigma>"
    also have "\<forall>v\<in>subst_domain \<sigma>. \<exists>t. (\<sigma> v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t" using ground_subst_domain_ex_reachable_constr assms by blast
    ultimately obtain t where "(\<sigma> v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t" by blast
    also then have "\<not>constr c (\<sigma> v) \<longrightarrow> \<sigma> v \<noteq> t" by auto
    ultimately have "\<not>constr c (\<sigma> v) \<longrightarrow> (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t" by (meson rtranclD)
    then have "\<not>constr c (\<sigma> v) \<longrightarrow>(\<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)" by auto
  }
  then have "\<forall>v\<in>subst_domain \<sigma>.\<not>constr c (\<sigma> v) \<longrightarrow>(\<exists>t. (\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)"by simp
  also have "\<exists>v\<in>subst_domain \<sigma>. \<not>constr c (\<sigma> v) " using assms(6) by simp
  ultimately show ?thesis by blast
qed

lemma ground_not_constr_var_subst:
  assumes "ground_subst (\<sigma>|s vars_term s)" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R"
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c"  and "\<not>constr_subst c (\<sigma>|s vars_term s)"  and "vars_term s\<subseteq> subst_domain \<sigma>"
  shows "\<exists>\<rho>'. (\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term s)"
proof -
  have "\<forall>v\<in>subst_domain (\<sigma>|s vars_term s).  \<exists>t. ((\<sigma>|s vars_term s) v,t)\<in>(rstep R)^* \<and>ground t \<and> constr c t" 
    using assms(1) assms(2) assms(3) assms(4) assms(5) apply (rule ground_subst_domain_ex_reachable_constr) done 
  have "\<forall>v\<in>subst_domain (\<sigma>|s vars_term s). \<not>constr c ((\<sigma>|s vars_term s) v) \<longrightarrow> (\<exists>t.((\<sigma>|s vars_term s) v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)" 
    using assms(1) assms(2) assms(3) assms(4) assms(5) assms(6) apply (rule ground_notconstr_subst_domain_ex_reachable_constr') done
  then have *:"\<forall>v\<in>subst_domain (\<sigma>|s vars_term s). \<not>constr c (\<sigma> v) \<longrightarrow> (\<exists>t.(\<sigma> v,t)\<in>(rstep R)^+ \<and> ground t \<and> constr c t)" using coincidence_lemma by simp
  also obtain V where V:"V = {v|v. v\<in>subst_domain (\<sigma>|s vars_term s) \<and> \<not>constr c ((\<sigma>|s vars_term s) v)}" by simp
  ultimately have "\<forall>v\<in>V. (\<exists>t.(\<sigma> v,t)\<in>(rstep R)^+ \<and> (ground t \<and> constr c t))" by fastforce
  also have **:"finite V" "V\<subseteq>subst_domain \<sigma>" using V by auto
  ultimately have "\<exists>\<rho>. (\<forall>v. v\<notin>V \<longrightarrow> \<sigma> v = \<rho> v) \<and> (\<forall>v\<in>V. (\<sigma> v,\<rho> v)\<in>(rstep R)^+ \<and> (ground (\<rho> v) \<and> constr c (\<rho> v)))" 
    apply(intro exchange_V_subst) apply blast apply simp by simp
  then obtain \<rho> where \<rho>:"(\<forall>v. v\<notin>V \<longrightarrow> \<sigma> v = \<rho> v) \<and> (\<forall>v\<in>V. (\<sigma> v,\<rho> v)\<in>(rstep R)^+ \<and> (ground (\<rho> v) \<and> constr c (\<rho> v)))" by auto
  also have "V\<inter> vars_term s \<noteq>{}"
  proof -
    have "V\<subseteq>vars_term s" using V by auto
    also have "\<exists>v\<in>vars_term s. \<not>constr c (\<sigma> v)" using assms(6) by auto
    then have "V\<noteq>{}" using V assms(7) by auto
    ultimately show ?thesis by auto
  qed
  ultimately have "(\<forall>v\<in>vars_term s. (\<sigma> v,\<rho> v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term s. (\<sigma> v,\<rho> v)\<in>(rstep R)^+)" using ** * exchange_V_rewritable' by blast
  also have "\<forall>v\<in>subst_domain (\<rho> |s vars_term s). ground ( (\<rho> |s vars_term s) v) \<and> constr c( (\<rho> |s vars_term s) v)" 
  proof (rule ballI)
    fix v assume a:"v\<in>subst_domain(\<rho> |s vars_term s)"
    show "ground ( (\<rho> |s vars_term s) v) \<and> constr c ((\<rho> |s vars_term s) v)"
    proof (cases "v\<in>V")
      case True
      then have "ground ( (\<rho> |s vars_term s) v)" using \<rho> a by simp
      also have " constr c ((\<rho> |s vars_term s) v)" using \<rho> a True by simp
      ultimately show ?thesis by simp
    next

      case False
      have "\<forall>v\<in>subst_domain (\<sigma>|s vars_term s). v\<notin>V \<longrightarrow> constr c (\<sigma> v)" using V a False by simp
      also have "\<sigma> v = \<rho> v" using \<rho> False by simp
      ultimately have "constr c ((\<rho> |s vars_term s) v)" using a False \<rho> assms(7) by auto
      also then have "ground ( (\<rho> |s vars_term s) v)" using \<rho> a assms(1) 
        by (metis Int_iff assms(7) ground_subst.elims(2) in_subst_restrict inf.absorb_iff2 subst_domain_restrict)
      ultimately show ?thesis by simp
    qed    
  qed      
  ultimately show ?thesis by auto
qed

lemma ground_not_constr_var_subst':
  assumes "ground_subst (\<sigma>|s vars_term t)" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R"
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c"  and "vars_term t\<subseteq> subst_domain \<sigma>"
  shows "\<exists>\<rho>''. (\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>'' v)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>''|s vars_term t)"
proof (cases "constr_subst c (\<sigma>|s vars_term t)")
  case True
  also have "\<forall>v\<in>vars_term t. (\<sigma> v,\<sigma> v)\<in>(rstep R)^*" by simp
  ultimately show ?thesis using assms(1) by auto
next
  case False
  then have "\<not>constr_subst c (\<sigma>|s vars_term t)" by simp
  then have "\<exists>\<rho>'. (\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term t)"
    using assms apply (metis ground_not_constr_var_subst) done
  then show ?thesis by auto
qed 



lemma all_vars_rstar_imp_term_rstar[simp]:
  assumes "\<forall>v\<in>vars_term t. ((\<sigma>::('a,'b)subst) v,\<rho>' v)\<in>(rstep R)^*"
    and "vars_term t \<subseteq> subst_domain \<rho>'"
  shows "(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^*" using assms subst_rsteps_imp_rsteps by blast

lemma all_vars_rstar_imp_term_rplus'[simp]:
  assumes "\<forall>v\<in>vars_term t. ((\<sigma>::('a,'b)subst) v,\<rho>' v)\<in>(rstep R)^*"
    and "\<exists>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+" and "vars_term t \<subseteq> subst_domain \<rho>'"
  shows "(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^+" using assms 
proof -
  have "(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^*" using assms by simp
  also then have "(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^+" using assms(2) rtranclD subst_one_change_rewritable term_subst_eq_rev by metis
  ultimately show ?thesis by simp
qed




lemma ground_subst_vars_term_subset_dom:
  assumes "ground_subst (\<sigma>|s vars_term s)" 
    and "(\<forall>v\<in>vars_term s. (\<sigma> v,\<rho> v)\<in>(rstep R)^*)"
    and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l"
    and "vars_term s\<subseteq>subst_domain \<sigma>" 
  shows "vars_term s\<subseteq>subst_domain \<rho>"
proof -
  have "\<forall>v\<in>vars_term s. ground (\<sigma> v)" using assms(1) assms(4) by auto
  then have "\<forall>v\<in>vars_term s. ground (\<rho> v)" using assms(2) assms(3) ground_rstep_rtrancl_ground by blast
  then have "\<forall>v\<in>vars_term s. \<not>is_Var(\<rho> v)" by fastforce
  then have "\<forall>v\<in>vars_term s. v\<in>subst_domain \<rho>" using notin_subst_domain_imp_Var by fastforce
  then show ?thesis by auto
qed

lemma ground_not_constr_subst_rewritable':
  assumes "ground_subst (\<sigma> |s (vars_term s \<union>vars_term t))" and "\<forall>(l,r)\<in>R. vars_term r\<subseteq>vars_term l" and "quasi_reducible d c R" 
    and "SN (rstep R)" and "\<forall>t. funas_term t\<subseteq>d\<union>c" and "\<not>constr_subst c (\<sigma>|s (vars_term s\<union>vars_term t))" 
    and "vars_term s\<union>vars_term t\<subseteq>subst_domain (\<sigma> |s (vars_term s \<union>vars_term t)) "
  shows "\<exists>\<rho>. ((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^+ \<or> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^+) \<and> ((t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^* \<and> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>|s (vars_term s\<union> vars_term t)) "
proof -
  consider "\<not>constr_subst c ((\<sigma>|s (vars_term s \<union>vars_term t))|s (vars_term s))" | "\<not>constr_subst c ((\<sigma>|s (vars_term s \<union>vars_term t))|s (vars_term t))" using assms(6) by auto
  then show ?thesis 
  proof cases
    case 1
    then have "\<not>constr_subst c (\<sigma>|s vars_term s)" by auto
    also have "ground_subst (\<sigma>|s vars_term s)" using assms(1) by simp
    moreover have "vars_term s\<subseteq>subst_domain \<sigma>" using assms(1) assms(7) by simp
    ultimately have "\<exists>\<rho>'. (\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term s)" 
      using  assms(2) assms(3) assms(4) assms(5) apply (metis ground_not_constr_var_subst) done
    then obtain \<rho>' where \<rho>':"(\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term s)" by auto
    then have "(\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*)" using \<rho>' by simp
    then have "vars_term s \<subseteq> subst_domain \<rho>'" using \<open>ground_subst (\<sigma>|s vars_term s)\<close> \<open>vars_term s\<subseteq>subst_domain \<sigma>\<close> assms(2) apply (metis ground_subst_vars_term_subset_dom) done
    then have t1:"vars_term s \<subseteq> subst_domain (\<rho>'|s vars_term s)" by simp
    then have "\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*" "(\<exists>v\<in>vars_term s. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+)" using \<rho>' apply (simp,simp) done
    then have t2:"(s\<cdot>\<sigma>,s\<cdot>\<rho>')\<in>(rstep R)^+ " using t1 by simp
    have "ground_subst (\<sigma>|s vars_term t)" using assms(1) by simp
    also have "vars_term t\<subseteq>subst_domain \<sigma>" using assms(7) by simp
    ultimately have "\<exists>\<rho>''. (\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>'' v)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>'' |s vars_term t)" 
      using assms(2) assms(3) assms(4) assms(5) apply(metis ground_not_constr_var_subst') done
    then obtain \<rho>'' where \<rho>'':"(\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>'' v)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>'' |s vars_term t)" by auto
    then have t3:"vars_term t \<subseteq> subst_domain \<rho>''" using \<open>ground_subst (\<sigma>|s vars_term t)\<close> \<open>vars_term t\<subseteq>subst_domain \<sigma>\<close> assms(2) apply (metis ground_subst_vars_term_subset_dom) done
    obtain \<rho> where \<rho>:"\<rho> = (\<rho>'|s vars_term s)\<union>\<^sub>s(\<rho>''|s vars_term t)" by simp
    then have *:"s\<cdot>\<rho> = s\<cdot>(\<rho>'|s vars_term s)" using t1 subst_domain_covered by blast
    then have "(s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^+" "gc_subst c (\<rho>|s vars_term s)" 
      using \<rho>' t1 t2 coincidence_lemma * apply simp 
    proof -
      have "\<forall>v\<in>vars_term s. v\<in>subst_domain \<rho>'" using t1 by auto
      then have "\<forall>v\<in>vars_term s. \<rho> v = \<rho>' v" using \<rho> by simp
      then have "\<forall>v\<in>vars_term s. ground (\<rho> v)\<and> constr c (\<rho> v)" using \<rho>' t1 by auto
      then show "gc_subst c (\<rho> |s vars_term s)" by simp
    qed
    also have f1:"\<forall>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^* \<and> ground (\<rho> v) \<and> constr c (\<rho> v)"
    proof (rule ballI)
      fix v assume a:"v\<in>vars_term t"
      show "(\<sigma> v,\<rho> v)\<in>(rstep R)^* \<and> ground (\<rho> v)\<and> constr c (\<rho> v)" 
      proof (cases "v\<in>vars_term s")
        case True
        then have "\<rho> v =\<rho>' v" using \<rho> t1 by auto
        also then have "ground (\<rho> v) \<and> constr c (\<rho> v)" using \<rho>' True t1 by auto
        ultimately show ?thesis using \<rho>' True by simp
      next
        case False
        then have "\<rho> v = \<rho>'' v" using \<rho> a by simp
        also then have "ground (\<rho> v) \<and> constr c (\<rho> v)" using \<rho>'' t3 a by auto
        ultimately show ?thesis using \<rho>'' a by simp
      qed
    qed
    then have "\<forall>v\<in>vars_term t. (\<sigma> v,\<rho> v)\<in>(rstep R)^*" "\<forall>v\<in>vars_term t. ground (\<rho> v) \<and> constr c (\<rho> v)" apply simp using f1 by simp
    then have "(t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^*" "gc_subst c (\<rho>|s vars_term t)" using subst_rsteps_imp_rsteps apply blast using \<open>\<forall>v\<in>vars_term t. ground (\<rho> v) \<and> constr c (\<rho> v)\<close> by simp
    ultimately have "(t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^* \<and> (s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^+ \<and> gc_subst c (\<rho>|s (vars_term s\<union>vars_term t))" by auto
    then show ?thesis by fast
  next
    case 2
    then have "\<not>constr_subst c (\<sigma>|s vars_term t)" by auto
    also have "ground_subst (\<sigma>|s vars_term t)" using assms(1) by simp
    moreover have "vars_term t\<subseteq>subst_domain \<sigma>" using assms(7) by simp
    ultimately have "\<exists>\<rho>'. (\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term t)" 
      using  assms(2) assms(3) assms(4) assms(5) apply (metis ground_not_constr_var_subst) done
    then obtain \<rho>' where \<rho>':"(\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*) \<and> (\<exists>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+) \<and> gc_subst c (\<rho>'|s vars_term t)" by auto
    then have "(\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*)" using \<rho>' by simp
    then have "vars_term t \<subseteq> subst_domain \<rho>'" using \<open>ground_subst (\<sigma>|s vars_term t)\<close> \<open>vars_term t\<subseteq>subst_domain \<sigma>\<close> assms(2) apply (metis ground_subst_vars_term_subset_dom) done
    then have t1:"vars_term t \<subseteq> subst_domain (\<rho>'|s vars_term t)" by simp
    then have "\<forall>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^*" "(\<exists>v\<in>vars_term t. (\<sigma> v,\<rho>' v)\<in>(rstep R)^+)" using \<rho>' apply (simp,simp) done
    then have t2:"(t\<cdot>\<sigma>,t\<cdot>\<rho>')\<in>(rstep R)^+ " using t1 by simp
    have "ground_subst (\<sigma>|s vars_term s)" using assms(1) by simp
    also have "vars_term s\<subseteq>subst_domain \<sigma>" using assms(7) by simp
    ultimately have "\<exists>\<rho>''. (\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>'' v)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>'' |s vars_term s)" 
      using assms(2) assms(3) assms(4) assms(5) apply(metis ground_not_constr_var_subst') done
    then obtain \<rho>'' where \<rho>'':"(\<forall>v\<in>vars_term s. (\<sigma> v,\<rho>'' v)\<in>(rstep R)^*) \<and> gc_subst c (\<rho>'' |s vars_term s)" by auto
    then have t3:"vars_term s \<subseteq> subst_domain \<rho>''" using \<open>ground_subst (\<sigma>|s vars_term s)\<close> \<open>vars_term s\<subseteq>subst_domain \<sigma>\<close> assms(2) apply (metis ground_subst_vars_term_subset_dom) done
    obtain \<rho> where \<rho>:"\<rho> = (\<rho>'|s vars_term t)\<union>\<^sub>s(\<rho>''|s vars_term s)" by simp
    then have *:"t\<cdot>\<rho> = t\<cdot>(\<rho>'|s vars_term t)" using t1 subst_domain_covered by blast
    then have "(t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^+" "gc_subst c (\<rho>|s vars_term t)" 
      using \<rho>' t1 t2 coincidence_lemma * apply simp 
    proof -
      have "\<forall>v\<in>vars_term t. v\<in>subst_domain \<rho>'" using t1 by auto
      then have "\<forall>v\<in>vars_term t. \<rho> v = \<rho>' v" using \<rho> by simp
      then have "\<forall>v\<in>vars_term t. ground (\<rho> v)\<and> constr c (\<rho> v)" using \<rho>' t1 by auto
      then show "gc_subst c (\<rho> |s vars_term t)" by simp
    qed
    also have f1:"\<forall>v\<in>vars_term s. (\<sigma> v,\<rho> v)\<in>(rstep R)^* \<and> ground (\<rho> v) \<and> constr c (\<rho> v)"
    proof (rule ballI)
      fix v assume a:"v\<in>vars_term s"
      show "(\<sigma> v,\<rho> v)\<in>(rstep R)^* \<and> ground (\<rho> v)\<and> constr c (\<rho> v)" 
      proof (cases "v\<in>vars_term t")
        case True
        then have "\<rho> v =\<rho>' v" using \<rho> t1 by auto
        also then have "ground (\<rho> v) \<and> constr c (\<rho> v)" using \<rho>' True t1 by auto
        ultimately show ?thesis using \<rho>' True by simp
      next
        case False
        then have "\<rho> v = \<rho>'' v" using \<rho> a by simp
        also then have "ground (\<rho> v) \<and> constr c (\<rho> v)" using \<rho>'' t3 a by auto
        ultimately show ?thesis using \<rho>'' a by simp
      qed
    qed
    then have "\<forall>v\<in>vars_term s. (\<sigma> v,\<rho> v)\<in>(rstep R)^*" "\<forall>v\<in>vars_term s. ground (\<rho> v) \<and> constr c (\<rho> v)" apply simp using f1 by simp
    then have "(s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^*" "gc_subst c (\<rho>|s vars_term s)" using subst_rsteps_imp_rsteps apply blast using \<open>\<forall>v\<in>vars_term s. ground (\<rho> v) \<and> constr c (\<rho> v)\<close> by simp
    ultimately have "(s\<cdot>\<sigma>,s\<cdot>\<rho>)\<in>(rstep R)^* \<and> (t\<cdot>\<sigma>,t\<cdot>\<rho>)\<in>(rstep R)^+ \<and> gc_subst c (\<rho>|s (vars_term s\<union>vars_term t))" by auto
    then show ?thesis by fast

  qed
qed

lemma SN_imp_ex_nf:
  "SN A \<Longrightarrow> \<exists>y. (x,y)\<in>A^* \<and> y\<in>NF A"
  by (simp add: SN_def SN_reaches_NF)


definition ground_convertible_terms :: "('f,'v) trs \<Rightarrow> ('f,'v) term \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
  where [simp]: "ground_convertible_terms R s t \<longleftrightarrow> 
                 (\<forall>\<sigma>. ((ground_subst \<sigma>)
                  \<and> ((vars_term s\<union>vars_term t)\<subseteq>subst_domain \<sigma>) \<longrightarrow> ((s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>(rstep R)\<^sup>\<leftrightarrow>\<^sup>*)))"

definition inductive_theorem_terms :: "('f,'v) trs \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool"
  where [simp]: "inductive_theorem_terms R s t \<longleftrightarrow> ground_convertible_terms R s t"

definition inductive_theorem_eqs :: "('f,'v) trs \<Rightarrow> ('f,'v) equations \<Rightarrow> bool" (infixr "\<Turnstile>\<^sub>i" 50) 
  where [simp]: "R \<Turnstile>\<^sub>i E \<longleftrightarrow> (\<forall>(s,t)\<in>E. inductive_theorem_terms R s t)"  

definition bounded_ground_convertible_terms::
  "('f,'v)trs \<Rightarrow> ('f,'v) term rel \<Rightarrow> ('f,'v) term rel \<Rightarrow>('f,'v) term \<Rightarrow> ('f,'v) term \<Rightarrow> bool" 
  where [simp]:"bounded_ground_convertible_terms R ns s t1 t2 \<longleftrightarrow> 
        (\<forall>\<sigma>. ((ground_subst \<sigma>) \<and> (vars_term t1\<union>vars_term t2)\<subseteq> subst_domain \<sigma>)\<longrightarrow>
             (\<exists>us. us\<noteq>[] \<and> hd us = (t1\<cdot>\<sigma>) \<and> last us = t2\<cdot>\<sigma> \<and> is_proof_of us (rstep R) 
                   \<and> (\<forall>i<length us. (t1\<cdot>\<sigma>,us!i)\<in>(ns\<union>s) \<or> (t2\<cdot>\<sigma>,us!i)\<in>(ns\<union>s))))"

definition bounded_ground_convertible_eqs::
  "('f,'v)trs \<Rightarrow> ('f,'v) term rel \<Rightarrow> ('f,'v) term rel \<Rightarrow> ('f,'v) equations \<Rightarrow> bool" 
  where [simp]:"bounded_ground_convertible_eqs R ns s E \<longleftrightarrow> 
        (\<forall>(t1,t2)\<in>E. bounded_ground_convertible_terms R ns s t1 t2)"

lemma b_g_convertible_imp_ground_convertible:
  assumes "bounded_ground_convertible_terms R ns s t1 t2"
  shows "ground_convertible_terms R t1 t2" using assms 
proof -
  have "\<forall>\<sigma>. ((ground_subst \<sigma>) \<and> (vars_term t1\<union>vars_term t2)\<subseteq> subst_domain \<sigma>)\<longrightarrow> 
        (\<exists>us. us \<noteq>[]\<and>  hd us = t1\<cdot>\<sigma> \<and> last us = t2\<cdot>\<sigma> \<and> is_proof_of us (rstep R) \<and> (\<forall>i<length us. (t1\<cdot>\<sigma>,us!i)\<in>(ns\<union>s) \<or> (t2\<cdot>\<sigma>,us!i)\<in>(ns\<union>s)))" using assms by simp
  then have "\<forall>\<sigma>. ((ground_subst \<sigma>) \<and> (vars_term t1\<union>vars_term t2)\<subseteq> subst_domain \<sigma>)\<longrightarrow> (t1\<cdot>\<sigma>,t2\<cdot>\<sigma>)\<in>(rstep R)\<^sup>\<leftrightarrow>\<^sup>*" using rtrancl_iff_proof by metis
  then show ?thesis by simp
qed

lemma b_g_convertible_imp_inductive_theorem_term[simp]:
  assumes "bounded_ground_convertible_terms R ns s t1 t2"
  shows "inductive_theorem_terms R t1 t2" 
  using assms b_g_convertible_imp_ground_convertible inductive_theorem_terms_def by blast

lemma b_g_c_imp_inductive_theorem:
  assumes "bounded_ground_convertible_eqs R ns s E"
  shows "R \<Turnstile>\<^sub>i E" 
proof -
  have "(\<forall>(t1,t2)\<in>E. bounded_ground_convertible_terms R ns s t1 t2)" using assms by simp
  then have "(\<forall>(t1,t2)\<in>E. inductive_theorem_terms R t1 t2)" using b_g_convertible_imp_inductive_theorem_term by blast
  then show ?thesis by simp
qed



fun order_fun_rel::"('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> ('a rel)" where
  "order_fun_rel ord_fun = {(x,y)|x y. ord_fun x y}"
fun order_rel_fun::"('a rel) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool)" where
  "order_rel_fun ord_rel = (\<lambda>x y. (x,y)\<in>ord_rel)"

lemma order_rel_rel_order_eq:
  "(order_rel_fun (order_fun_rel ord)) = ord" by simp



(* ******************************************* *) 
(* s_mul_ext:: NS S*)
(* order_pair :: S NS *)  

locale reduction_order_pair = 
  fixes NS ::"('a,'b) term rel"
    and  S ::"('a,'b) term rel"
  assumes ctxt_S: "(s,t)\<in>S \<Longrightarrow> (C\<langle>s\<rangle>,C\<langle>t\<rangle>)\<in>S"
    and ctxt_NS: "(s,t)\<in>NS \<Longrightarrow> (C\<langle>s\<rangle>,C\<langle>t\<rangle>)\<in>NS"
    and subst_S: "(s,t)\<in> S \<Longrightarrow> (s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>S"
    and subst_NS: "(s,t)\<in>NS \<Longrightarrow> (s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>NS"
    and order_pair:"order_pair S NS"
    and SN_S:"SN S"

(*********************)

(*********************)
begin
lemma trans_S[order_simps]:"trans S" using order_pair order_pair_def pre_order_pair.trans_S by blast
lemma trans_NS[order_simps]:"trans NS" using order_pair order_pair_def pre_order_pair.trans_NS by blast
lemma trans[simp]:"trans (NS\<union>S)"
proof (rule transI)
  fix x y z assume "(x,y)\<in>(NS\<union>S)" "(y,z)\<in>(NS\<union>S)" 
  then show "(x,z)\<in>(NS\<union>S)" by (metis (no_types, lifting) Un_iff compat_pair.compat_NS_S_point compat_pair.compat_S_NS_point order_pair order_pair.axioms(2) transD trans_NS trans_S)
qed
lemma refl_NS :"refl NS" using order_pair order_pair_def pre_order_pair.refl_NS by auto
lemma refl_NS_S: "refl (NS\<union>S)" using refl_NS by (simp add: refl_O_iff sup.coboundedI1)
lemma ctxt: "(s,t)\<in>(NS\<union>S) \<Longrightarrow> (C\<langle>s\<rangle>,C\<langle>t\<rangle>)\<in>(NS\<union>S)" using ctxt_S ctxt_NS by auto
lemma subst: "(s,t)\<in> (NS\<union>S) \<Longrightarrow> (s\<cdot>\<sigma>,t\<cdot>\<sigma>)\<in>(NS\<union>S)" using subst_S subst_NS by auto
lemma S_NS_S_S: "(s,s1)\<in>S \<and> (s1,t)\<in>NS\<union>S \<Longrightarrow> (s,t)\<in>S"
proof -
  assume a:"(s,s1)\<in>S \<and> (s1,t)\<in>NS\<union>S"
  then show "(s,t)\<in>S" 
  proof (cases "(s1,t)\<in>NS")
    case True
    then have "(s,t)\<in>S O NS" using a by auto
    then show ?thesis using order_pair unfolding order_pair_def compat_pair_def by auto
  next
    case False
    then show ?thesis using trans_S transD[of S s s1 t] a by simp
  qed
qed 


inductive_set f_closed_set::"('c\<Rightarrow>'c) \<Rightarrow>'c \<Rightarrow> 'c set" for p and t where 
  axiom:"t\<in> f_closed_set p t" |
  expand:"a\<in> f_closed_set p t \<Longrightarrow> p a \<in>f_closed_set p t" 

fun f_n::"('c\<Rightarrow>'c) \<Rightarrow> nat \<Rightarrow> 'c \<Rightarrow> 'c"  where
  "f_n f 0 x = x"|
  "f_n f (Suc n) x = f(f_n f n  x)"

lemma f_closed_set_iff_f_n:
  "s\<in>f_closed_set f t \<longleftrightarrow> (\<exists>i. s =  f_n f i t)"(is "?L\<longleftrightarrow>?R")
proof
  assume ?L 
  then show ?R apply induct apply auto  apply (metis f_n.simps(1)) 
    by (metis f_n.simps(2)) 
next
  assume r:?R
  then obtain i where a:"s = f_n f i t" by auto 
  then show ?L using r apply (induction i arbitrary:s ) apply auto using f_closed_set.intros apply fast 
    using f_closed_set.expand by fastforce
qed


lemma f_n_not_wf:
  "(\<forall>i. ( f_n p (i+1) s, f_n p i s)\<in>r) \<longrightarrow> \<not>wf r"
proof (rule impI,rule ccontr)
  assume a1:"\<forall>i. (f_n p (i+1) s, f_n p i s)\<in>r" 
  assume "\<not>\<not>wf r"
  then have a2:"wf r" by simp    
  then have "(\<exists>S. S\<noteq>{} \<and> (\<forall>m\<in>S. \<exists>s\<in>S. (s,m)\<in>r))"
  proof-
    obtain S where S:"S = f_closed_set p s" by simp
    then have *:"S\<noteq>{}" using f_closed_set.axiom by fast
    have **:"\<forall>m\<in>S. p s \<in>S" using S by (simp add: f_closed_set.axiom f_closed_set.expand)
    have "\<forall>m\<in>S. \<exists>i. m = f_n p i s" using S by (simp add: f_closed_set_iff_f_n)
    then have "\<forall>m\<in>S. (p m,m)\<in>r" using a1 by auto
    then have "\<forall>m\<in>S. \<exists>s\<in>S. (s,m)\<in>r" using S ** by (meson f_closed_set.expand)
    then show ?thesis using * ** by auto
  qed
  then have "\<not>wf r" using min_iff_wf by metis
  then show False using a2 by simp
qed

lemma ctxt_f_n:
  assumes "(s,Ctx\<langle>s\<rangle>)\<in>r" and "\<forall>x y Ctx. (x,y)\<in>r \<longrightarrow> (Ctx\<langle>x\<rangle>,Ctx\<langle>y\<rangle>)\<in>r"
  shows "(\<forall>i. ( f_n (\<lambda>t. Ctx\<langle>t\<rangle>) i s, f_n (\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s)\<in>r)"
proof (rule allI)
  fix i
  show "(f_n (\<lambda>t. Ctx\<langle>t\<rangle>) i s, f_n (\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s)\<in>r"
  proof (induction i)
    case 0
    then have " f_n (\<lambda>t. Ctx\<langle>t\<rangle>) 0 s = s \<and> f_n (\<lambda>t. Ctx\<langle>t\<rangle>) 1 s = Ctx\<langle>s\<rangle>" by simp
    then show ?case using assms by simp
  next
    case (Suc i)
    then have "( f_n (\<lambda>t. Ctx\<langle>t\<rangle>) i s, f_n (\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s)\<in>r" by simp
    then have "(Ctx\<langle>f_n(\<lambda>t. Ctx\<langle>t\<rangle>) i s\<rangle>,Ctx\<langle>f_n(\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s\<rangle>)\<in>r" using assms by simp
    then show ?case by simp
  qed
qed      


lemma ctxt_More:
  assumes "ts!i = u" and "length ts>i"
  shows "(More f (take i ts) Hole (drop (i+1) ts))\<langle>u\<rangle> = (Fun f ts)"
proof -
  have "(take i ts)@(drop (i) ts) = ts" using append_take_drop_id by simp
  also have "(drop (i) ts) = (ts!i)# drop (i+1) ts"
  proof -
    have *:"\<forall>ss. ss\<noteq>[] \<longrightarrow> (drop 0 ss) = hd ss# drop 1 ss" by (simp add: drop_Suc)
    have "length (drop (i) ts) >0" using assms by simp
    then have **:"(drop (i) ts)\<noteq>[]" by simp
    then have "hd (drop (i) ts) = ts!i" proof(intro hd_drop_conv_nth, simp) qed
    then show ?thesis using * ** by (simp add: Cons_nth_drop_Suc)
  qed
  finally have "(take i ts)@(ts!i)#(drop (i+1) ts) = ts" by simp
  then have "(take i ts)@u#(drop (i+1) ts) = ts" using assms by simp
  then show ?thesis by simp
qed

lemma subst_apply_app_cons:
  assumes "ts = ss@z#us"
  shows "(Fun f ts)\<cdot>\<sigma> = Fun f ((map (\<lambda>t. t\<cdot>\<sigma>) ss)@(z\<cdot>\<sigma>)#(map (\<lambda>t. t \<cdot> \<sigma>) us))" using assms by simp

lemma not_ground_ex_substituted_ctxt:
  assumes "\<not>ground t" 
  shows "\<exists>Ctx. t\<cdot>(\<lambda>x. s) = Ctx\<langle>s\<rangle>" using assms
proof (induction t )
  case (Var x)
  then have "(Var x)\<cdot>(\<lambda>x. s) = Hole\<langle>s\<rangle>" by simp
  then show ?case by blast
next
  case (Fun f ts)  
  then have "\<exists>u\<in>set ts. \<not>ground u" by simp
  then obtain u Ctx where u:"u\<in>set ts \<and> (u\<cdot>(\<lambda>x. s) = Ctx\<langle>s\<rangle>)" using Fun by blast
  then obtain i where i:"i<length ts \<and> ts!i = u" by (meson in_set_conv_nth)
  then have "(More f (take i ts) Hole (drop (i+1) ts))\<langle>u\<rangle> = Fun f ts" using Fun ctxt_More by auto
  then have "Fun f ((take i ts)@u#(drop (i+1) ts)) = Fun f ts" by simp
  then have "ts =((take i ts)@u#(drop (i+1) ts))" by simp
  then have "(Fun f ts)\<cdot>(\<lambda>x. s) = Fun f ((map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (take i ts))@(u\<cdot> (\<lambda>x. s))#(map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (drop (i+1) ts)))" by (intro subst_apply_app_cons)
  then have "Fun f ((map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (take i ts))@(Ctx\<langle>s\<rangle>)#(map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (drop (i+1) ts))) = (Fun f ts)\<cdot>(\<lambda>x. s)" using u by simp
  then have "(More f (map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (take i ts)) (Ctx) (map (\<lambda>t. t \<cdot> (\<lambda>x. s)) (drop (i+1) ts)))\<langle>s\<rangle> = (Fun f ts)\<cdot>(\<lambda>x. s)" by simp 
  then show ?case by metis
qed

lemma ground_S: "ground s \<and> (s,t)\<in>S \<Longrightarrow> ground t"
proof (rule ccontr)
  assume a1:"ground s \<and> (s,t)\<in>S"
  assume a2:"\<not>ground t"
  let ?sigma = "(\<lambda>x. s)"
  have "(s\<cdot>?sigma,t\<cdot>?sigma)\<in>S" using a1 a2 subst_S by simp
  then have "(s,t\<cdot>?sigma)\<in>S" using ground_subst_apply a1 by metis
  also obtain Ctx where Ctx:"t\<cdot>?sigma = Ctx\<langle>s\<rangle>" using a2 not_ground_ex_substituted_ctxt by fastforce
  ultimately have "(s,Ctx\<langle>s\<rangle>)\<in>S" by simp
  then have "(\<forall>i. ( f_n (\<lambda>t. Ctx\<langle>t\<rangle>) i s, f_n (\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s)\<in>S)" using ctxt_S ctxt_f_n by blast
  then have "(\<forall>i. ( f_n (\<lambda>t. Ctx\<langle>t\<rangle>) (i+1) s, f_n (\<lambda>t. Ctx\<langle>t\<rangle>) i s)\<in>(S\<inverse>))" by simp
  then have "\<not>wf (S\<inverse>)" using f_n_not_wf by metis
  then show False using SN_S SN_imp_wf by auto
qed

lemma ground_NS_S:
  assumes "ground s" "(s,s')\<in>S" "(s',t)\<in>NS"
  shows "ground t"
proof -
  have "(s,t)\<in>S O NS " using assms(2) assms(3) by blast
  then have "(s,t)\<in>S" using order_pair unfolding order_pair_def compat_pair_def by auto
  then show ?thesis using assms(1) ground_S[of s t] by simp
qed     

lemma ground_NS_S_rtrancl:
  assumes "ground s" "(s,s')\<in>S" "(s',t)\<in>(NS\<union>S)^*"
  shows "ground t"
proof -
  obtain i where "(s',t)\<in>(NS\<union>S)^^i" using assms(3) by auto
  then show ?thesis using assms(2)
  proof (induct i arbitrary:s')
    case 0
    have "(s',t)\<in>NS" using refl_NS refl_onD[of UNIV NS] 0 by simp
    then show ?case using ground_NS_S[of s s' t] 0(2) assms(1) by simp
  next
    case (Suc i)
    then obtain t' where t':"(s',t')\<in>NS\<union>S \<and> (t',t)\<in>(NS\<union>S)^^i" using relpow_Suc_D2 by metis
    then have "(s,t')\<in>S" using S_NS_S_S[of s s' t'] using Suc(3) by simp
    then show ?case using Suc(1) t' by auto
  qed
qed     

definition vars_terms ::"('f,'v) term set \<Rightarrow> 'v set" where 
  "vars_terms ts = (\<Union>t\<in>ts. vars_term t)"

definition funas_terms ::"('f,'v)term set \<Rightarrow> 'f sig" where
  "funas_terms ts = (\<Union>t\<in>ts. funas_term t)"


lemma subst_vars: assumes "\<exists>y. x\<in> vars_term (\<sigma> y)" shows "x \<in> vars_terms(subst_range \<sigma>) \<or> \<sigma> x = Var x"
proof -
  from assms obtain y where 1: "x\<in> vars_term (\<sigma> y)" by auto
  then have 3:"\<sigma> y \<in> subst_range \<sigma> \<or> \<sigma> y = Var y" using notin_subst_domain_imp_Var by fastforce
  from this and 1 show "x\<in>vars_terms(subst_range \<sigma>)\<or> \<sigma> x = Var x" using vars_terms_def by fastforce 
qed

lemma subst_y: "x\<in>vars_term (\<sigma> y) \<and> \<sigma> y = Var y \<Longrightarrow> \<sigma> y = Var x" by auto

lemma subst_vars_rest:"\<forall>x\<in> (vars_term (s\<cdot>\<sigma>)). x \<in> vars_term s \<or> x \<in> vars_terms (subst_range \<sigma>)" 
proof rule
  fix \<sigma>::"('f,'v)subst"
  fix x s
  assume a1:"x \<in> (vars_term (s\<cdot>\<sigma>))"
  then have 1:"\<forall> t\<unlhd>s\<cdot>\<sigma>. (\<exists>u. u \<unlhd> s \<and> is_Fun u \<and> t = u\<cdot>\<sigma>) \<or> (\<exists>y. y \<in> vars_term s \<and> t \<unlhd> \<sigma> y)" using supteq_subst_cases' by blast
  from a1 have 2:"\<exists> t\<unlhd>s\<cdot>\<sigma>. Var x = t" by simp
  from 1 and 2 have "\<exists>t\<unlhd>s\<cdot>\<sigma>. Var x = t \<and> (\<exists>y. y \<in> vars_term s \<and> t \<unlhd> \<sigma> y)" by (metis is_VarI subst_apply_eq_Var)
  then have "\<exists>t\<unlhd>s\<cdot>\<sigma>. Var x = t \<and> (\<exists>y. y\<in> vars_term s \<and>(x\<in> vars_term (\<sigma> y)))" by (meson subteq_Var_imp_in_vars_term)
  then have "\<exists>y. y\<in> vars_term s \<and> x\<in>vars_term(\<sigma> y)" by simp
  then obtain y where 3:"y\<in> vars_term s \<and> x\<in> vars_term(\<sigma> y)" by auto
  then have 4:"\<sigma> y = Var y \<or> x \<in> vars_term (\<sigma> y)" by simp
  then have "\<sigma> y = Var y \<or> \<sigma> x = Var x \<or> x\<in> vars_terms(subst_range \<sigma>)" by (meson subst_vars)
  from this and subst_vars have " \<sigma> y = Var y \<or> x \<in> vars_terms (subst_range \<sigma>)" using 4 vars_terms_def notin_subst_domain_imp_Var by fastforce
  from this show "x \<in> vars_term s \<or> x\<in> vars_terms (subst_range \<sigma>) " using "3" by force
qed

lemma vars_subst_sub:
  assumes "vars_term s \<subseteq> subst_domain \<sigma>" and "x\<in> vars_term s" shows "\<sigma> x \<noteq> Var x"
proof -
  from assms have "x\<in> subst_domain \<sigma>" by auto
  from this show "\<sigma> x \<noteq> Var x" using CollectD subst_domain_def by fastforce
qed  


lemma groundsubst:
  assumes a1:"ground_subst \<sigma>\<^sub>g"
    and a2:"vars_term s \<subseteq> subst_domain \<sigma>\<^sub>g"
  shows "ground (s\<cdot>\<sigma>\<^sub>g)" using assms by auto


lemma constr_funas: "\<forall>ft\<in> funas_term s. ft\<in> C \<Longrightarrow> constr C s" 
proof (induction s)
  case (Var x)
  show ?case by simp
next
  case (Fun f ss)
  have 1:"(f,length ss) \<in> C" by (simp add: Fun.prems)
  have "\<forall>t\<in> set ss. \<forall>st\<in> funas_term t. st\<in>C" using Fun.prems by auto
  from this and 1 show ?case using Fun.IH by auto
qed




lemma s_mul_ext_rev:
  assumes "({#x,y#},{#a,b#})\<in>s_mul_ext ns s"
  shows "({#x,y#},{#b,a#})\<in>s_mul_ext ns s" 
proof -
  have "{#a,b#} = {#b,a#}" by simp
  then show ?thesis using assms by metis
qed

lemma s_mul_ext_rev':
  assumes "({#x,y#},{#a,b#})\<in>s_mul_ext ns s"
  shows "({#y,x#},{#a,b#})\<in>s_mul_ext ns s" 
proof -
  have "{#x,y#} = {#y,x#}" by simp
  then show ?thesis using assms by metis
qed

lemma r1r2gtstar_on_rev:
  assumes "(x,y)\<in>R\<^sub>1geR\<^sub>2gtstar_on ns s  R1 R2 A"
  shows "(y,x)\<in>R\<^sub>1geR\<^sub>2gtstar_on ns s  R1 R2 A"
proof -
  obtain xs where xs:"xs\<noteq>[]  \<and> hd xs = x \<and> last xs = y"
    "is_proof_of xs (R1\<union>R2)"
    "(\<forall>i<length xs .  (x,(xs!i))\<in>(ns\<union>s) \<or> (y,(xs!i))\<in>ns\<union>s)"
    "\<forall>i<length xs . xs!i\<in>A"
    "(\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#x,y#},{#xs!i,xs!(i+1)#})\<in>s_mul_ext ns s)" using assms by fastforce
  then have t1:"rev xs\<noteq>[]  \<and> hd (rev xs) = y \<and> last (rev xs) = x" using rev_hd_last[of xs] by simp
  also have t2:"is_proof_of (rev xs) (R1\<union>R2)" using xs rev_proof by blast
  moreover have t3:"(\<forall>i<length (rev xs).  (x,((rev xs)!i))\<in>(ns\<union>s) \<or> (y,((rev xs)!i))\<in>ns\<union>s)" using xs by (simp add: rev_nth)
  moreover have t4:"(\<forall>i<length (rev xs) -1. ((rev xs!i,rev xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#y,x#},{#rev xs!i,rev xs!(i+1)#})\<in>s_mul_ext ns s))" 
  proof -
    have *:"\<forall>i<length (rev xs)-1.  (rev xs) !i = (xs !(length xs-(i+1))) \<and>  (rev xs)!(i+1) = (xs !(length xs -(i+1+1)))" 
      using rev_nth t1  One_nat_def Suc_eq_plus1 Suc_leI le_add_diff_inverse2 length_greater_0_conv length_rev less_SucI less_diff_conv by metis
    {
      fix i assume a:"i<length (rev xs) -1" 
      also 
      {
        have "(rev xs!i,rev xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longleftrightarrow> (rev xs!(i+1),rev xs!i)\<notin>R1\<^sup>\<leftrightarrow>" by auto
        have "(length xs -(i+1+1)+1) = length xs - (i+ 1)" using a by simp
        then have "(rev xs!i,rev xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longleftrightarrow> (xs!(length xs -(i+1+1)+1),xs!(length xs -(i+1+1)))\<notin>R1\<^sup>\<leftrightarrow>" using a * by simp
      }
      moreover
      {
        have "length xs-(i+1+1)<length xs-1 " using a by simp
        then have "(xs!(length xs -(i+1+1)),xs!(length xs -(i+1+1)+1))\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow>
                 ({#x,y#},{#xs !(length xs -(i+1+1)),xs !((length xs -(i+1+1))+1)#})\<in>s_mul_ext ns s" using xs(5) by simp
        also have "(length xs -(i+1+1)+1) = length xs - (i+ 1)" using a by simp
        ultimately have "((rev xs)!(i+1),(rev xs)!i)\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow>
                 ({#x,y#},{#(rev xs)!(i+1),(rev xs)!i#})\<in>s_mul_ext ns s" using * a by metis
      }
      then have "((rev xs)!(i+1),(rev xs)!i)\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#x,y#},{#rev xs!i,rev xs!(i+1)#})\<in>s_mul_ext ns s" using s_mul_ext_rev * by metis
      ultimately have "((rev xs!i,rev xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#x,y#},{#rev xs!i,rev xs!(i+1)#})\<in>s_mul_ext ns s)" by auto
      then have "((rev xs!i,rev xs!(i+1))\<notin>R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#y,x#},{#rev xs!i,rev xs!(i+1)#})\<in>s_mul_ext ns s)" using s_mul_ext_rev' by metis
    }
    then show ?thesis by simp
  qed
  moreover have t5:"\<forall>i<length (rev xs) . (rev xs)!i\<in>A" using xs(4) by (simp add: rev_nth)
  ultimately have "\<exists>xs. 
                   xs \<noteq> [] \<and>
                   hd xs = y \<and>
                   last xs = x \<and>
                   is_proof_of xs (R1 \<union> R2) \<and>
                   (\<forall>i<length xs. xs!i\<in>A) \<and>
                   (\<forall>i<length xs. (y, xs ! i) \<in> ns \<union> s \<or> (x, xs ! i) \<in> ns \<union> s) \<and>
                   (\<forall>i<length xs - 1. (xs ! i, xs ! (i + 1)) \<notin> R1\<^sup>\<leftrightarrow> \<longrightarrow> ({#y, x#}, {#xs ! i, xs ! (i + 1)#}) \<in> s_mul_ext ns s)" by blast
  then show ?thesis using R\<^sub>1geR\<^sub>2gtstar_on_def[of ns s R1 R2 A] by blast
qed  

lemma multpw_size:
  assumes "(X,Y)\<in> multpw ns"
  shows "size X = size Y" using assms 
proof (induction X arbitrary:Y) 
  case empty
  then have "({#},Y)\<in> multpw ns " by simp
  then show ?case by simp
next
  case (add x X')
  then obtain Y' y where Y':"add_mset y Y' = Y \<and> (X',Y')\<in>multpw ns \<and> (x,y)\<in>ns "using add.IH 
    by (metis multpw_split1R)
  then have "size Y' = size X'" using add.IH by auto
  then have "size (add_mset y Y') =  size (add_mset x X')" by simp
  then show ?case using add Y' by simp
qed

lemma two_elem_mset_subset_case:
  assumes "X\<subseteq>#{#x,y#}"
  shows "X = {#} \<or> X = {#x#} \<or> X = {#y#} \<or> X = {#x,y#}" using assms
proof (induction X)
  case empty
  then show ?case by simp
next
  case (add w X')
  then have subset:"(add_mset w X')\<subseteq>#{#x,y#}" using assms add by simp
  have "X'\<subseteq>#{#x,y#}" using add assms
    by (meson mset_subset_eq_insertD subset_mset.less_imp_le)
  then have *:"X' = {#} \<or> X' = {#x#} \<or> X' = {#y#} \<or> X' = {#x,y#}" using add.IH by simp
  then have "w\<in>#{#x,y#}" using add by auto
  then have w:"w = x \<or> w = y" by simp
  {
    assume "X' = {#x,y#}"
    then have "add_mset w X' = {#x,y,w#} " by simp
    then have False using subset by simp
  }
  then have "X' \<noteq>{#x,y#}" by auto
  then have X':"X' = {#} \<or> X' = {#x#} \<or> X' = {#y#}" using add.IH * by simp
  then show ?case
  proof (cases "y=x")
    case True
    then have "X' = {#} \<or> X' = {#x#}" using X' by simp
    then show ?thesis using True w by simp
  next
    case False
    then show ?thesis 
    proof (cases "w=x")
      case True
      moreover{
        assume "X' = {#x#}"
        then have "add_mset w X' = {#x,x#} " using True by simp
        then have "False" using subset False by simp
      }
      moreover{
        assume "X' = {#y#}"
        then have "add_mset w X' = {#x,y#}" using True by simp
        then have ?thesis by simp
      }
      moreover{
        assume "X' = {#}"
        then have "add_mset w X' = {#x#}" using True by simp
        then have ?thesis by simp
      }
      then show ?thesis using calculation X' by auto
    next
      case False
      then have wy:"w = y" using w by simp
      moreover{
        assume "X' = {#x#}"
        then have "add_mset w X' = {#x,y#} " using wy by simp
        then have ?thesis by simp
      }
      moreover{
        assume "X' = {#y#}"
        then have "add_mset w X' = {#y,y#}" using wy by simp
        then have False using subset False wy by simp
      }
      moreover{
        assume "X' = {#}"
        then have "add_mset w X' = {#y#}" using wy by simp
        then have ?thesis by simp
      }
      then show ?thesis using calculation X' by auto
    qed
  qed
qed

lemma s_mul_ext_closed_under_ctxt:
  assumes "({#s,t#},{#u,v#})\<in> s_mul_ext NS S"      
  shows "({#C\<langle>s\<rangle>,C\<langle>t\<rangle>#},{#C\<langle>u\<rangle>,C\<langle>v\<rangle> #})\<in> s_mul_ext NS S" 
  using mul_ext_list.s_map[of S "\<lambda> s. C \<langle> s \<rangle>" NS "[s,t]" "[u,v]", OF ctxt_S ctxt_NS] assms
  by auto

lemma Rgtstar_ctxt_sublemma:
  assumes "length ss \<ge> 2 \<and> is_proof_of ss R"
    and "\<forall>C s t. (s,t)\<in>R \<longrightarrow> (C\<langle>s\<rangle>,C\<langle>t\<rangle>)\<in>R "
  shows "\<forall>C xs. xs = map (\<lambda>u. (C\<langle>u\<rangle>)) ss \<longrightarrow> (hd xs = C\<langle>(hd ss)\<rangle> \<and> last xs = C\<langle>(last ss)\<rangle> \<and> is_proof_of xs R)"
proof -
  from assms have *:"ss \<noteq> Nil" by auto
  from assms have "\<forall>i<length ss-1. (ss!i,ss!(i+1)) \<in> R\<^sup>\<leftrightarrow>" using is_proof_of_def by blast
  then have "\<forall>C. \<forall>i<length ss-1. (C\<langle>ss!i\<rangle>,C\<langle>ss!(i+1)\<rangle>) \<in> R\<^sup>\<leftrightarrow>" using assms(2) by auto
  then have t1:"\<forall>C. is_proof_of (map (\<lambda>u. C\<langle>u\<rangle>) ss) R" by (simp add: less_diff_conv)
  from assms have "(\<forall>C. \<forall>i<length ss. (map (\<lambda>u. C\<langle>u\<rangle>) ss)!i =  C\<langle>(ss!i)\<rangle>)"by simp
  then have t2:"\<forall>C xs. xs = map (\<lambda>u. (C\<langle>u\<rangle>)) ss \<longrightarrow> hd xs = C\<langle>(hd ss)\<rangle> \<and> last xs = C\<langle>(last ss)\<rangle>" by (simp add: * assms hd_map last_map)
  then show ?thesis using t1 t2 by simp
qed

lemma all_two_elem_subproof:
  assumes "is_proof_of xs R"
  shows "\<forall>i<length xs-1. is_proof_of [xs!i,xs!(i+1)] R"
  using assms  by simp

lemma proof_sublemma:
  assumes "length xs \<ge>2"
    and "hd xs = x"
    and "last xs = y"
  shows "x#(drop 1 ((take (length xs -1) xs)))@[y] = xs" 
proof -
  have *:"(take (length xs -1) xs)@[y] = xs" by (metis append_butlast_last_id assms(1) assms(3) butlast_conv_take list.size(3) not_numeral_le_zero)
  then have "hd (take (length xs -1) xs) = x" 
    by (metis Suc_1 Suc_le_mono assms(1) assms(2) hd_append2 length_append_singleton list.size(3) not_one_le_zero)
  then have "x#(drop 1 ((take (length xs -1) xs))) = (take (length xs -1) xs)"
    by (metis "*" Cons_nth_drop_Suc One_nat_def Suc_1 Suc_le_eq assms(1) butlast_snoc drop_0 hd_conv_nth length_butlast less_numeral_extra(3) list.size(3) zero_less_diff)
  then show ?thesis
    by (metis "*" append_Cons)
qed

lemma sublist_ys:
  assumes "\<forall>i<length (a#xs')-1. \<exists>ys. length ys \<ge>2  \<and> hd ys = ((a#xs')!i) \<and> last ys = ((a#xs')!(i+1)) \<and> P(ys)"
  shows"\<forall>i<length xs'-1. \<exists>ys. length ys \<ge>2  \<and> hd ys = (xs'!i) \<and> last ys = (xs'!(i+1)) \<and> P(ys)" using assms 
  by (metis One_nat_def Suc_eq_plus1 diff_Suc_Suc diff_zero length_Cons less_diff_conv nth_Cons_Suc)

lemma sublist_ys':
  assumes "\<forall>i<length (a#xs')-1. \<exists>ys. ys \<noteq>[]  \<and> hd ys = ((a#xs')!i) \<and> last ys = ((a#xs')!(i+1)) \<and> P(ys)"
  shows"\<forall>i<length xs'-1. \<exists>ys. ys\<noteq>[]  \<and> hd ys = (xs'!i) \<and> last ys = (xs'!(i+1)) \<and> P(ys)" using assms 
  by (metis One_nat_def Suc_eq_plus1 diff_Suc_Suc diff_zero length_Cons less_diff_conv nth_Cons_Suc)    

lemma second_cons_equal_hd:
  assumes "length xs \<ge>1"
  shows "(a#xs)!1 = hd xs" using assms 
  by (metis One_nat_def Suc_n_not_le_n hd_conv_nth list.size(3) nth_Cons_Suc)

lemma (in reduction_order_pair) s_mul_ext_SN:
  "SN (s_mul_ext NS S)" 
  by (simp add: SN_S SN_s_mul_ext order_pair)

lemma ex_sublist_ys:
  assumes "\<forall>i<length (b#list)-1. ((b#list)!i,(b#list)!(i+1))\<in>R\<^sub>2 \<longrightarrow>
              (\<exists>ys. length ys \<ge> 1 \<and> hd ys = ((b#list)!i) \<and> last ys = ((b#list)!(i+1)) \<and>  (\<forall>j<length ys-1. (ys!j,ys!(j+1))\<in>R\<^sub>1))" 
  shows "\<forall>i<length (list)-1. (((list)!i,(list)!(i+1))\<in>R\<^sub>2 \<longrightarrow> 
            (\<exists>ys. length ys \<ge>1 \<and>  hd ys = ((list)!i) \<and> last ys = ((list)!(i+1)) \<and>  (\<forall>j<length ys-1. (ys!j,ys!(j+1))\<in>R\<^sub>1)))" using assms 
proof (induction list)
  case Nil
  then show ?case by simp
next
  case (Cons c list)
  then have"\<forall>i<length (b#c#list)-1. ((b#c#list)!i,(b#c#list)!(i+1))\<in>R\<^sub>2 \<longrightarrow>
              (\<exists>ys. length ys \<ge> 1 \<and> hd ys = ((b#c#list)!i) \<and> last ys = ((b#c#list)!(i+1)) \<and>  (\<forall>j<length ys-1. (ys!j,ys!(j+1))\<in>R\<^sub>1))" by simp
  then have"\<forall>i<length (c#list)-1. ((c#list)!i,(c#list)!(i+1))\<in>R\<^sub>2 \<longrightarrow>
              (\<exists>ys. length ys \<ge> 1 \<and> hd ys = ((c#list)!i) \<and> last ys = ((c#list)!(i+1)) \<and>  (\<forall>j<length ys-1. (ys!j,ys!(j+1))\<in>R\<^sub>1))" by fastforce
  then show ?case by simp
qed

lemma append_in_R:
  assumes "\<forall>i<length (b#zs)-1. (((b#zs)!i),((b#zs)!(i+1)))\<in>R"
    and "\<forall>i<length ys-1. ((ys!i),(ys!(i+1)))\<in>R"
    and "length ys \<ge>1 "
    and "last ys = b"
  shows "\<forall>i<length (ys@zs)-1. ((ys@zs)!i,(ys@zs)!(i+1))\<in>R" using assms(2) assms(3) assms(4)
proof (induction "length ys" arbitrary:ys)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain ys' c where ys':"ys = c#ys'" using length_Suc_conv by metis
  then have h1:"length ys' = n" using Suc by simp
  have "\<forall>i<length (ys)-1. (((ys)!i),((ys)!(i+1)))\<in>R" using assms Suc.prems by simp
  then have h2:"\<forall>i<length (ys')-1. ((ys'!i),(ys'!(i+1)))\<in>R" 
    by (metis Suc.hyps(2) Suc_eq_plus1 diff_Suc_1 less_diff_conv nth_Cons_Suc ys' h1)
  consider (a)"length ys'\<ge>1" | (b)"length ys' = 0 " by linarith
  then have "\<forall>i<length (ys@zs)-1. ((ys@zs)!i,(ys@zs)!(i+1))\<in>R" 
  proof (cases)
    case a
    then have "last ys' = b" using ys' Suc.prems by auto
    then have "\<forall>i<length (ys'@zs)-1. ((ys'@zs)!i,(ys'@zs)!(i+1))\<in>R" using Suc.hyps ys' h1 h2 a by simp
    also have "\<forall>i<length (c#ys'@zs)-1. i\<ge> 1 \<longrightarrow> (c#ys'@zs)!i = (ys'@zs)!(i-1) \<and> (c#ys'@zs)!(i+1) = (ys'@zs)!i" by simp
    moreover have "\<forall>i<length (c#ys'@zs)-1. i\<ge>1 \<longrightarrow> (i-1)<length (ys'@zs)-1" by auto
    ultimately have t1:"\<forall>i<length (c#ys'@zs)-1. i\<ge>1\<longrightarrow> ((c#ys'@zs)!i,(c#ys'@zs)!(i+1))\<in>R" by auto
    have "length ys \<ge>2 " using a ys' by simp
    then have "(ys!0,ys!1)\<in>R" using Suc.prems by simp
    then have f1:"(c,ys'!0)\<in>R" using ys' by simp
    then have "(c#ys'@zs)!0 = c \<and> (c#ys'@zs)!1 = ys'!0" using a 
      by (metis One_nat_def append_is_Nil_conv hd_append2 hd_conv_nth length_greater_0_conv less_le_trans nth_Cons_0 nth_Cons_Suc zero_less_one)
    then have t2:"\<forall>i<length (c#ys'@zs)-1. i=0 \<longrightarrow> ((c#ys'@zs)!i,(c#ys'@zs)!(i+1))\<in>R" using f1 by simp
    have "ys@zs = c#ys'@zs" using ys' by simp
    then show ?thesis using ys' t1 t2 by fastforce
  next
    case b
    then have g1:"ys = [c]" using ys' by simp
    then have "b = c" using Suc.prems by simp
    then have "ys@zs = b#zs" using g1 by simp
    then show ?thesis using assms(1) by simp
  qed      
  then show ?case by simp
qed

lemma cons_P:
  assumes "\<forall>i<length xs. P(xs!i)"  
    and "P(x)"
  shows "\<forall>i<length (x#xs). P((x#xs)!i)"
proof -
  have "\<forall>i<length (x#xs). i\<ge>1 \<longrightarrow> P((x#xs)!i)" using assms by simp
  also have "\<forall>i<length (x#xs). i=0 \<longrightarrow> P((x#xs)!i)" using assms by simp
  then show ?thesis using calculation by fastforce
qed

lemma app_bounded:
  assumes "\<forall>i<length xs. xs!i\<in>A" and "\<forall>i<length (y#ys). (y#ys)!i\<in>A"
  shows "\<forall>i<length (xs@ys). (xs@ys)!i\<in>A" 
proof -
  have "\<forall>i<length (xs@ys). i<length xs \<longrightarrow> (xs@ys)!i = xs!i" by (simp add: nth_append) 
  then have *:"\<forall>i<length (xs@ys). i<length xs \<longrightarrow> (xs@ys)!i\<in>A" using assms by simp
  have "\<forall>i<length (xs@ys). i\<ge>length xs \<longrightarrow> (xs@ys)!i = ys!(i-length xs)" by (simp add: nth_append)
  also have "\<forall>i<length ys. ys!i\<in>A" using assms by auto
  ultimately have "\<forall>i<length (xs@ys). i\<ge>length xs \<longrightarrow> (xs@ys)!i \<in>A" using assms by simp
  then show ?thesis using * by auto
qed

lemma sublemma':
  assumes "(\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)"
    and "(\<forall>j<length zs. (x,(zs!j))\<in>(NS\<union>S) \<or> (y,(zs!j))\<in>(NS\<union>S)) \<and> is_proof_of zs R\<^sub>1 \<and> (\<forall>j<length zs. zs!j\<in>A)"
    and "ys\<noteq>[]" and "zs\<noteq>[]"
    and "hd ys = last zs"
  shows "\<exists>ys' c. ys = (c#ys') \<and>  (\<forall>j<length (zs@ys'). (x,((zs@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs@ys')!j))\<in>(NS\<union>S)) 
              \<and> is_proof_of (zs@ys') R\<^sub>1 \<and>(\<forall>j<length (zs@ys'). (zs@ys')!j\<in>A)" 
proof -
  obtain c ys' where ys':"ys = c#ys'" using assms by (metis hd_Cons_tl)
  then have "(\<forall>j<length (zs@ys'). (x,((zs@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs@ys')!j))\<in>(NS\<union>S)) \<and> is_proof_of (zs@ys') R\<^sub>1 \<and> (\<forall>j<length (zs@ys'). (zs@ys')!j\<in>A)"
    using assms(2) assms(4) assms(5)
  proof (induction "length zs" arbitrary:zs) 
    case 0
    then show ?case by simp
  next
    case (Suc n)
    then obtain d zs' where zs':" zs =d#zs'" using length_Suc_conv by metis 
    then have "(\<forall>j<length zs. (x,(zs!j))\<in>(NS\<union>S) \<or> (y,(zs!j))\<in>(NS\<union>S)) \<and> is_proof_of zs R\<^sub>1 \<and> (\<forall>j<length zs. zs!j\<in>A)"  using Suc by simp
    then show ?case
    proof (cases "length zs'<2")
      case True
      then have t1:"zs' = [] \<or> (\<exists>z. zs' =[z])" using zs' Suc 
        by (metis length_0_conv length_Suc_conv less_Suc0 less_SucE numeral_2_eq_2)
      then show ?thesis
      proof (cases "zs' = []")
        case True
        then have t2:"zs = [d]" using zs' by simp
        then have "d = c" using Suc by simp
        then have "zs@ys' = ys" using ys' t2 by simp
        then show ?thesis using Suc assms by simp
      next
        case False
        then obtain z where z:"zs = [d,z]" using zs' t1 by blast
        then have f1:"(d,z)\<in>R\<^sub>1\<^sup>\<leftrightarrow>" using Suc.prems by fastforce
        have zsys:"zs@ys' = d#ys" using Suc.prems z by fastforce
        then have f2:" is_proof_of (zs@ys') R\<^sub>1" using f1 Suc.prems
          by (metis False assms(1) cons_is_proof last.simps list.inject z zs')
        have "(x,d)\<in>(NS\<union>S) \<or> (y,d)\<in>(NS\<union>S)" using z Suc by auto
        then have f3:"\<forall>i<length (zs@ys'). (x,(zs@ys')!i)\<in>(NS\<union>S) \<or> (y,(zs@ys')!i)\<in>(NS\<union>S)" using assms(1) zsys 
          by (metis (no_types, lifting) diff_less length_Cons less_Suc_eq less_le_trans nat_less_le neq0_conv nth_Cons' zero_less_one)
        have "\<forall>j<length zs. zs!j\<in>A" using Suc by simp
        also have "\<forall>j<length (c#ys'). (c#ys')!j\<in>A" using ys' assms by simp
        ultimately have "\<forall>j<length (zs@ys'). (zs@ys')!j\<in>A" by (rule app_bounded)
        then show ?thesis using f2 f3 Suc by simp
      qed
    next
      case False
      then have zs'nonnil:"zs'\<noteq>[]" by auto
      have "(\<forall>j<length zs. (x,(zs!j))\<in>(NS\<union>S) \<or> (y,(zs!j))\<in>(NS\<union>S)) \<and> is_proof_of zs R\<^sub>1 \<and> (\<forall>i<length zs. zs!i\<in>A)" using Suc False by simp
      then have "(\<forall>j<length zs'. (x,(zs'!j))\<in>(NS\<union>S) \<or> (y,(zs'!j))\<in>(NS\<union>S)) \<and> is_proof_of zs' R\<^sub>1 \<and> (\<forall>i<length zs'. zs'!i\<in>A)" using zs' by (metis Suc_mono cons_proof length_Cons nth_Cons_Suc)
      then have F1:" (\<forall>j<length (zs'@ys'). (x,((zs'@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs'@ys')!j))\<in>(NS\<union>S)) 
                    \<and> is_proof_of (zs'@ys') R\<^sub>1 \<and> (\<forall>i<length (zs'@ys'). (zs'@ys')!i\<in>A)" using False Suc 
        using less_Suc_eq numeral_2_eq_2 zs' by force
      then have F1':" (\<forall>j<length (zs'@ys'). (x,((zs'@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs'@ys')!j))\<in>(NS\<union>S))"by simp
      then have F2:"(x,d)\<in>(NS\<union>S) \<or> (y,d)\<in>(NS\<union>S)" using zs' Suc.prems(2) by auto
      have F3:"(\<forall>j<length (d#(zs'@ys')). (x,((d#(zs'@ys'))!j))\<in>(NS\<union>S) \<or> (y,((d#(zs'@ys'))!j))\<in>(NS\<union>S))" using F1' F2 by (rule cons_P)
      have "(d,hd zs')\<in>R\<^sub>1\<^sup>\<leftrightarrow>" using zs'nonnil Suc zs' One_nat_def by (meson cons_R_ref)
      then have F4:"(d,hd (zs'@ys'))\<in>R\<^sub>1\<^sup>\<leftrightarrow>" using zs'nonnil by simp
      have F1'':"is_proof_of (zs'@ys') R\<^sub>1" using F1 by simp
      then have F5:"is_proof_of (d#(zs'@ys')) R\<^sub>1" using F4 by (meson cons_is_proof)
      have "d\<in>A" using Suc.prems zs'  by force
      also have "(\<forall>i<length (zs'@ys'). (zs'@ys')!i\<in>A)" using F1 by simp
      ultimately have F6:"\<forall>i<length (d#(zs'@ys')). (d#(zs'@ys'))!i\<in>A" by (simp add: nth_Cons')
      have "zs@ys' = d#(zs'@ys')" using zs' by simp
      then show ?thesis using F5 F3 F6 by simp
    qed
  qed
  then show ?thesis using ys' by simp
qed

lemma ex_each_conv_imp_ex_allof_list':
  assumes "xs\<noteq>[]" and "\<forall>i<length xs. (x,(xs!i))\<in>(NS\<union>S) \<or> (y,(xs!i))\<in>(NS\<union>S)" and "\<forall>i<length xs. xs!i\<in>A"
    and "\<forall>i<length xs-1. \<exists>ys. ys\<noteq>[]  \<and> hd ys = xs!i \<and> last ys =xs!(i+1) \<and> (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)"
  shows "\<exists>ys. ys\<noteq>[]  \<and> hd ys = hd xs \<and> last ys =last xs \<and> (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)" using assms
proof (induct "length xs" arbitrary:xs)
  case (Suc n)
  then obtain a xs' where xs':" xs = a#xs'" using length_Suc_conv by metis
  then have xs'len:"length xs' = n" using Suc by simp
  have *:" \<forall>i<length (a#xs') - 1.
   \<exists>ys. ys\<noteq>[] \<and> hd ys = (a#xs') ! i \<and> last ys = (a#xs') ! (i + 1) \<and> ((\<forall>j<length ys. (x, ys ! j) \<in> NS \<union> S \<or> (y, ys ! j) \<in> NS \<union> S) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A))" 
    using Suc xs' by simp 
  then have h1:" \<forall>i<length xs' - 1.
     \<exists>ys. ys\<noteq>[] \<and> hd ys = xs' ! i \<and> last ys = xs' ! (i + 1) \<and> ((\<forall>j<length ys. (x, ys ! j) \<in> NS \<union> S \<or> (y, ys ! j) \<in> NS \<union> S) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A))" 
  proof -
    {
      fix i assume "i<length xs'-1"
      then have "\<exists>ys. ys\<noteq>[] \<and> hd ys = xs' ! i \<and> last ys = xs' ! (i + 1) \<and> 
                ((\<forall>j<length ys. (x, ys ! j) \<in> NS \<union> S \<or> (y, ys ! j) \<in> NS \<union> S) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A))"using xs' *
        by (metis Suc.hyps(2) Suc_eq_plus1 \<open>length xs' = n\<close> diff_Suc_1 less_diff_conv nth_Cons_Suc)      
    }
    then show ?thesis by simp
  qed
  then show ?case using Suc
  proof (cases "length xs'\<ge>2")
    case False
    then consider "length xs' = 0" |"length xs'=1" by linarith
    then show ?thesis
    proof cases
      case 1
      then have *:"xs = [a]" using xs' by simp
      then have "a\<in>A" using Suc by fastforce
      then show ?thesis using Suc * by fastforce
    next
      case 2
      then obtain b where " xs' = [b]" using xs' False Suc le_antisym length_0_conv length_Suc_conv not_less_eq_eq numeral_2_eq_2 One_nat_def by metis
      then have f1:"xs = [a,b]" using xs' by simp
      then have "\<exists>ys. ys\<noteq>[] \<and> hd ys = ([a,b]) ! 0 \<and> last ys = [a,b] ! (1) \<and> ((\<forall>j<length ys. (x, ys ! j) \<in> NS \<union> S \<or> (y, ys ! j) \<in> NS \<union> S) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A))" using Suc by simp
      then show ?thesis using f1 by simp
    qed    
  next
    case True
    then have xs'nonnil:"xs'\<noteq>[]" by auto
    have "\<forall>i<length xs. ((x,(xs!i))\<in>(NS\<union>S) \<or> (y,(xs!i))\<in>(NS\<union>S)) \<and> xs!i\<in>A" using xs' Suc by simp
    then have "\<forall>i<length xs'. ((x,(xs'!i))\<in>(NS\<union>S) \<or> (y,(xs'!i))\<in>(NS\<union>S)) \<and> xs'!i\<in>A" by (metis Suc.hyps(2) Suc_mono xs'len nth_Cons_Suc xs')
    then have "\<exists>ys. ys\<noteq>[] \<and> hd ys = hd xs' \<and> last ys =last xs' \<and> 
            (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)" using Suc.hyps(1) xs'len xs'nonnil h1 by simp
    then obtain ys where ys:"ys\<noteq>[] \<and> hd ys = hd xs' \<and> last ys =last xs' \<and> 
            (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)" using xs' Suc.hyps(1) xs'len h1 by auto
    obtain zs where zs:"zs\<noteq>[] \<and> hd zs = a \<and> last zs = hd xs' \<and>
          (\<forall>j<length zs. (x,(zs!j))\<in>(NS\<union>S) \<or> (y,(zs!j))\<in>(NS\<union>S)) \<and> is_proof_of zs R\<^sub>1 \<and> (\<forall>j<length zs. zs!j\<in>A)" using True * xs' 
      by (metis One_nat_def Suc.hyps(2) Suc_eq_plus1 \<open>length xs' = n\<close> add_leD2 diff_Suc_1 length_greater_0_conv list.size(3) not_one_le_zero nth_Cons_0 one_add_one second_cons_equal_hd)        
    then have "last zs = hd ys" using ys zs Suc by simp
    then have "\<exists>ys' c. ys = c#ys'\<and> (\<forall>j<length (zs@ys'). (x,((zs@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs@ys')!j))\<in>(NS\<union>S)) \<and> is_proof_of (zs@ys') R\<^sub>1 \<and> (\<forall>j<length (zs@ys'). (zs@ys')!j\<in>A)" 
      using zs ys sublemma' by simp
    then obtain ys' c where T1:"ys = c#ys'\<and> (\<forall>j<length (zs@ys'). (x,((zs@ys')!j))\<in>(NS\<union>S) \<or> (y,((zs@ys')!j))\<in>(NS\<union>S)) \<and> is_proof_of (zs@ys') R\<^sub>1 \<and> (\<forall>j<length (zs@ys'). (zs@ys')!j\<in>A)" by auto
    then have T2:"hd (zs@ys') = hd xs \<and> last (zs@ys') = last xs" using xs' zs ys 
      by (metis True add_leD2 append_Nil2 hd_append2 last.simps last_ConsR last_appendR list.sel(1) list.size(3) not_one_le_zero one_add_one)
    have "(zs@ys')\<noteq>[] " using T1 zs by simp
    then show ?thesis using zs ys T1 T2 by meson
  qed
qed simp

lemma ex_each_conv_imp_ex_allof_list'':
  assumes "xs\<noteq>[]" and "\<forall>i<length xs. (x,(xs!i))\<in>(NS\<union>S) \<or> (y,(xs!i))\<in>(NS\<union>S)" and "\<forall>i<length xs. xs!i\<in>A"
    and "\<forall>i<length xs-1. \<exists>ys. ys\<noteq>[]  \<and> hd ys = xs!i \<and> last ys =xs!(i+1) \<and> (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)"
  shows "\<exists>ys. ys\<noteq>[]  \<and> hd ys = hd xs \<and> last ys =last xs \<and> (\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)" 
proof -
  show ?thesis using assms by (rule ex_each_conv_imp_ex_allof_list')
qed

definition two_elem_mset_order::"'c rel\<Rightarrow> 'c rel \<Rightarrow> ('c\<times>'c) rel" where
  "two_elem_mset_order ns s = {((x,y),(z,w)). ({#x,y#},{#z,w#})\<in>s_mul_ext ns s}"

fun pair_to_mset:: "'c \<times>'c \<Rightarrow> 'c multiset" where
  "pair_to_mset (x,y) = {#x,y#}"  

definition pair_mset_set :: "('c\<times>'c) set\<Rightarrow> 'c multiset set" where
  "pair_mset_set A = {{#x,y#}|x y. (x,y)\<in>A}"

lemma pair_mset_set:
  "{#x,y#} \<in>pair_mset_set A \<longrightarrow> (\<exists>s t. {#s,t#} = {#x,y#} \<and> (s,t)\<in>A)" using pair_mset_set_def[of A]by fastforce

lemma pair_mset_set_intro:
  "(s,t)\<in>A \<or> (t,s)\<in>A \<longrightarrow> {#s,t#} \<in>pair_mset_set A" (is "?L\<longrightarrow>?R") 
proof 
  assume ?L 
  then have *:"{#s,t#} \<in>pair_mset_set A \<or> {#t,s#} \<in>pair_mset_set A" using pair_mset_set_def by fast
  have "{#s,t#} = {#t,s#}" by simp
  thus ?R using * by metis   
qed

lemma pair_to_mset_pair_mset_set_intro:
  "(s,t)\<in>A \<longrightarrow> pair_to_mset (s,t) \<in>pair_mset_set A" using pair_mset_set_intro pair_to_mset.simps by metis

lemma wf_twoelem_s_mul:
  assumes "wf ((s_mul_ext ns s)\<inverse>)"
  shows "wf ((two_elem_mset_order ns s)\<inverse>)"  
proof (rule ccontr)  
  let ?r = "((s_mul_ext ns s)\<inverse>)" let ?R = "((two_elem_mset_order ns s)\<inverse>)"
  assume "\<not>wf ?R"
  then have "\<exists>S. S\<noteq>{} \<and> (\<forall>m\<in>S. \<exists>s\<in>S. (s,m)\<in>?R)" by (meson min_iff_wf)
  then obtain S where S:"S\<noteq>{} \<and> (\<forall>m\<in>S. \<exists>s\<in>S. (s,m)\<in>?R)" by auto
  then obtain S' where S':"pair_mset_set S = S' " by auto    
  then have S'notempty:"S'\<noteq>{}" using S by (metis ex_in_conv pair_mset_set_intro pair_to_mset.elims)
  {
    fix m assume m:"m\<in>S"
    then obtain s where s:"S\<noteq>{} \<and> s\<in>S\<and> (s,m)\<in>?R" using S by blast
    then obtain m' where m':"m' = pair_to_mset m" by simp
    then obtain s' where s':" s' = pair_to_mset s" by simp
    then have t1:"s'\<in>pair_mset_set S \<and> m' \<in> pair_mset_set S" using pair_to_mset_pair_mset_set_intro s s' m' m 
      by (metis S' pair_to_mset.elims)
    then have *:"(s',m')\<in>?r" using s m' s' unfolding two_elem_mset_order_def by auto
    then have "s' \<in>S' \<and> (s',m')\<in>?r" using * s s' S' pair_mset_set t1 by simp
    then have "S'\<noteq>{} \<and> m'\<in>S' \<and> s'\<in>S'\<and> (s',m')\<in>?r" using m' s' S' m t1 by auto
    then have "S'\<noteq>{} \<and> m'\<in>S' \<and> (\<exists>s'\<in>S'. (s',m')\<in>?r)" by auto
    then have "(\<exists>s'\<in>S'. (s',m')\<in>?r)" using m m' S' by auto
    then have "(\<exists>s'\<in>S'. (s',pair_to_mset m)\<in>?r)" using m' by simp
  }
  then have t2:"\<forall>m\<in>S. (\<exists>s'\<in>S'. (s',pair_to_mset m)\<in>?r)" by simp
  also have "\<And>P. (\<forall>m\<in>S. P (pair_to_mset m)  \<Longrightarrow> (\<forall>m'\<in>S'. P m'))" using S'  pair_mset_set_def[of S] by auto
  ultimately have "\<forall>m'\<in>S'. (\<exists>s'\<in>S'. (s', m')\<in>?r)" by presburger
  then have "\<exists>S'. S'\<noteq>{}\<and>(\<forall>m'\<in>S'. (\<exists>s'\<in>S'. (s', m')\<in>?r))" using S' S S'notempty by auto
  then have "\<not>wf ?r" by (meson min_iff_wf)
  then show False using assms by simp
qed

lemma conversion_lemmma:
  assumes "\<forall>x\<in>A. \<forall>y\<in>A. (x,y)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<longrightarrow> (x,y)\<in>(R\<^sub>1geR\<^sub>2gtstar_on NS S R\<^sub>1 R\<^sub>2 A)"
  shows "\<forall>x\<in>A. \<forall>y\<in>A. (x,y)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<longrightarrow>  (x,y)\<in>(Rgestar_on NS S R\<^sub>1 A)"
proof -
  {
    fix x y assume a:"x\<in>A" assume b:"y\<in>A"
    let ?R = "(two_elem_mset_order NS S)\<inverse>"
    let ?r = "s_mul_ext NS S"
    have wf_two_elem_s_mul_NS_S: "wf ?R" 
      using SN_iff_wf s_mul_ext_SN wf_twoelem_s_mul by auto
    let ?s = "\<lambda>ys. ys\<noteq>[] \<and> hd ys = x \<and> last ys = y \<and>is_proof_of ys R\<^sub>1 \<and>
    (\<forall>j<length ys. ys!j\<in>A) \<and>(\<forall>j<length ys. (x,(ys!j))\<in>(NS\<union>S) \<or> (y,(ys!j))\<in>(NS\<union>S))"
    let ?ind = "\<lambda>(u,v). \<exists>ys. ys \<noteq>[] \<and> hd ys = u \<and> last ys = v \<and>is_proof_of ys R\<^sub>1\<and> 
    (\<forall>j<length ys. ys!j\<in>A) \<and>(\<forall>j<length ys. (u,(ys!j))\<in>(NS\<union>S) \<or> (v,(ys!j))\<in>(NS\<union>S))"
    let ?xy = "(x,y)"
    have " (x,y)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<and> (x,y)\<in>A\<times>A \<longrightarrow>?ind (x,y)"
    proof (rule wf_induct[of ?R, OF wf_two_elem_s_mul_NS_S] )
      fix w
      assume ih:"\<forall>s. ((s,w)\<in>?R) \<longrightarrow> (s\<in>R\<^sub>2\<^sup>\<leftrightarrow>) \<and> s\<in>A\<times>A \<longrightarrow> ?ind s"
      then obtain u v where uv:" w= (u,v)" by fastforce
      let ?t = "\<lambda>(x1,x2). \<exists>ys. ys\<noteq>[] \<and> hd ys = x1 \<and> last ys = x2  \<and>
                (\<forall>j<length ys. (u,(ys!j))\<in>(NS\<union>S) \<or> (v,(ys!j))\<in>(NS\<union>S)) \<and>
                  is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)"
      {
        assume asm:"(u,v)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<and> (u,v)\<in>A\<times>A"
        have "(u,v)\<in>(R\<^sub>1geR\<^sub>2gtstar_on NS S R\<^sub>1 R\<^sub>2 A)" using assms asm by auto
        then obtain xs where xs:"xs\<noteq>[]  \<and> hd xs = u \<and> last xs = v \<and>
                is_proof_of xs (R\<^sub>1\<union>R\<^sub>2) \<and> (\<forall>i<length xs. xs!i\<in>A) \<and> 
                (\<forall>i<length xs .  (u,(xs!i))\<in>(NS\<union>S) \<or> (v,(xs!i))\<in>(NS\<union>S)) \<and>
                (\<forall>i<length xs -1. (xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow> ({#u,v#},{#xs!i,xs!(i+1)#})\<in>?r)" 
          unfolding R\<^sub>1geR\<^sub>2gtstar_def by auto
        then have xslen:"length xs\<ge>1 " by (simp add: Suc_leI)
        have h1:"\<forall>i<length xs-1. (xs!i,xs!(i+1))\<in> R\<^sub>1\<^sup>\<leftrightarrow> \<or>(xs!i,xs!(i+1))\<in> R\<^sub>2\<^sup>\<leftrightarrow>" using xs  by auto
        have h':"\<forall>i<length xs-1.xs!i\<in>A \<and> xs!(i+1)\<in>A" using xs by simp
        {
          fix i assume a2:"i<length xs-1" assume a1:"(xs!i,xs!(i+1))\<in>R\<^sub>1\<^sup>\<leftrightarrow>"
          have "?t(xs!i,xs!(i+1))"
          proof -
            let ?i= "[xs!i,xs!(i+1)]"
            have "(xs!i,xs!(i+1))\<in>R\<^sub>1\<^sup>\<leftrightarrow>" using a1 a2 by simp
            then have f1:"is_proof_of ?i R\<^sub>1"  by simp
            then have f2:"?i\<noteq>[] \<and> hd ?i = xs!i \<and> last ?i = xs!(i+1)" by simp
            then have f3:"\<forall>j<length ?i. ?i!j\<in>A" using less_Suc_eq h' a2 by force
            have *:"((u,?i!0)\<in>(NS\<union>S)\<or> (v,?i!0)\<in>(NS\<union>S)) \<and> ((u,?i!1)\<in>(NS\<union>S)\<or>(v,?i!1)\<in>(NS\<union>S))" using a2 xs by simp
            then have "\<forall>j<length ?i. (u,?i!j)\<in>(NS\<union>S) \<or> (v,?i!j)\<in>(NS\<union>S)" using xs a2 * by (simp add: less_Suc_eq)
            thus "?t(xs!i,xs!(i+1))"  using f1 f2 f3 by blast
          qed
        }
        then have h2:"\<forall>i<length xs-1. (xs!i,xs!(i+1))\<in>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow> ?t(xs!i,xs!(i+1))" by simp  
        {
          fix i assume i:"i<length xs-1" assume r2:"(xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow>" then have r2':"(xs!i,xs!(i+1))\<in>R\<^sub>2\<^sup>\<leftrightarrow>" using h1 i by auto
          have "((xs!i,xs!(i+1)),(u,v))\<in>?R " unfolding two_elem_mset_order_def using xs i r2 by auto
          then have "?ind (xs!i,xs!(i+1)) " using ih r2' asm uv h' i by auto
          then obtain ys where ys:"ys\<noteq>[] \<and> hd ys = xs!i \<and> last ys = xs!(i+1) \<and>is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A) \<and> 
                                (\<forall>j<length ys. (xs!i,(ys!j))\<in>(NS\<union>S) \<or> (xs!(i+1),(ys!j))\<in>(NS\<union>S))" by auto
          have it:"i<length xs \<and> i+1<length xs"using i by auto
          then have t1:"((u,xs!i)\<in>(NS\<union>S) \<or> (v,xs!i)\<in>NS\<union>S)" using xs by simp
          also have t2:"((u,xs!(i+1))\<in>(NS\<union>S) \<or> (v,xs!(i+1))\<in>NS\<union>S)" using xs it by simp
          have trans_NS_S:"trans (NS\<union>S)" by simp
          {
            fix j assume aj:"j<length ys"
            then consider "(xs!i,(ys!j))\<in>(NS\<union>S)"| "(xs!(i+1),(ys!j))\<in>(NS\<union>S)" using ys t1 by auto
            then have "(u,(ys!j))\<in>(NS\<union>S)\<or>(v,(ys!j))\<in>(NS\<union>S)"
            proof (cases)
              case 1
              then show ?thesis using t1 transD trans_NS_S by fast
            next
              case 2
              then show ?thesis using t2 transD trans_NS_S by fast
            qed
          }
          then have "\<forall>j<length ys. (u,(ys!j))\<in>(NS\<union>S)\<or>(v,(ys!j))\<in>(NS\<union>S)" by simp
          then have "?t (xs!i,xs!(i+1))" using ys by auto
        }
        then have h3:"\<forall>i<length xs-1. (xs!i,xs!(i+1))\<notin>R\<^sub>1\<^sup>\<leftrightarrow> \<longrightarrow>  ?t(xs!i,xs!(i+1))" by auto
        then have k1:"\<forall>i<length xs-1. ?t (xs!i,xs!(i+1))" using h1 h2 h3 by auto
        then have k1':"\<forall>i<length xs. xs!i\<in>A" using xs by simp
        have xsnonnil:"xs\<noteq>[]" using xs by simp
        have "\<forall>i<length xs. (u,(xs!i))\<in>(NS\<union>S) \<or> (v,(xs!i))\<in>(NS\<union>S)" using xs by simp
        then have "\<exists>ys. ys\<noteq>[]  \<and> hd ys = hd xs \<and> last ys =last xs \<and> 
                  (\<forall>j<length ys. (u,(ys!j))\<in>(NS\<union>S) \<or> (v,(ys!j))\<in>(NS\<union>S)) \<and> is_proof_of ys R\<^sub>1 \<and> (\<forall>j<length ys. ys!j\<in>A)" 
          using  k1 k1' xsnonnil  ex_each_conv_imp_ex_allof_list' by simp
        then have  k2:"?t (hd xs,last xs)" by simp
        have "hd xs = u \<and> last xs = v" using xs by simp
        then have "?ind (u,v)" using k2 by auto
      } 
      then show "w\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<and> w\<in>A\<times>A \<longrightarrow> ?ind w" using uv by simp 
    qed
    also have "(x,y)\<in>A\<times>A" using a b by simp
    ultimately have "(x,y)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<longrightarrow>(x,y)\<in>(Rgestar_on NS S R\<^sub>1 A)" using a unfolding Rgestar_def by simp
  }
  then show "\<forall>x\<in>A.\<forall>y\<in>A. (x,y)\<in>R\<^sub>2\<^sup>\<leftrightarrow> \<longrightarrow> (x,y)\<in>(Rgestar_on NS S R\<^sub>1 A)" by auto
qed

end    
end
