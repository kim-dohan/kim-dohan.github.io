(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Monotone_Algebra
imports 
  Term_Order
begin

locale wf_algebra = compat_pair S NS for NS S :: "'a rel" +  
  fixes A :: "'a set" 
    and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a"
    and "typ" :: "'v itself"
  assumes I_A: "set as \<subseteq> A \<Longrightarrow> I f as \<in> A"
    and wm: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> set (bef @ aft) \<subseteq> A 
      \<Longrightarrow> (a,b) \<in> NS \<Longrightarrow> (I f (bef @ a # aft), I f (bef @ b # aft)) \<in> NS"
    and S_imp_NS: "S \<subseteq> NS"
    and SN: "SN_on S A" 
    and refl_NS: "refl_on A NS"
    and trans_NS: "trans_on A NS" 
    and trans_S: "trans_on A S" 
begin

abbreviation eval :: "('f,'v)term \<Rightarrow> ('v \<Rightarrow> 'a) \<Rightarrow> 'a" where
  "eval \<equiv> eval_term I" 

lemma eval_A: assumes ran: "range \<alpha> \<subseteq> A"
  shows "eval t \<alpha> \<in> A"
proof (induct t)
  case Var then show ?case using ran by auto
next
  case (Fun f ts)
  then show ?case unfolding eval_term.simps by (intro I_A, auto)
qed

definition S_A :: "('f,'v)term rel" where
  "S_A = {(s,t) . (\<forall> \<alpha>. range \<alpha> \<subseteq> A \<longrightarrow> (eval s \<alpha>, eval t \<alpha>) \<in> S)}"

definition NS_A :: "('f,'v)term rel" where
  "NS_A = {(s,t) . (\<forall> \<alpha>. range \<alpha> \<subseteq> A \<longrightarrow> (eval s \<alpha>, eval t \<alpha>) \<in> NS)}"

lemma NS_A_I[intro]: assumes "\<And> \<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval s \<alpha>, eval t \<alpha>) \<in> NS"
  shows "(s,t) \<in> NS_A" using assms unfolding NS_A_def by blast

lemma S_A_I[intro]: assumes "\<And> \<alpha>. range \<alpha> \<subseteq> A \<Longrightarrow> (eval s \<alpha>, eval t \<alpha>) \<in> S"
  shows "(s,t) \<in> S_A" using assms unfolding S_A_def by blast

lemma eval_subst: "eval (t \<cdot> \<delta>) \<alpha> = eval t (\<lambda> x. eval (\<delta> x) \<alpha>)"
  by (simp add: eval_subst eval_subst_def)

lemma S_NS_stable: assumes "((s,t)) \<in> {(s,t) . (\<forall> \<alpha>. range \<alpha> \<subseteq> A \<longrightarrow> (eval s \<alpha>, eval t \<alpha>) \<in> S_NS)}" (is "_ \<in> ?r")
  shows "(s \<cdot> (\<delta> :: ('f,'v)subst), t \<cdot> \<delta>) \<in> ?r"
proof -
  {
    fix \<alpha> :: "'v \<Rightarrow> 'a"
    assume "range \<alpha> \<subseteq> A"
    then have "range (\<lambda> x. eval (\<delta> x) \<alpha>) \<subseteq> A" using eval_A[of \<alpha>] by auto
  }
  then show ?thesis using assms by (auto simp: eval_subst)
qed
  
lemma S_A_stable: "(s,t) \<in> S_A \<Longrightarrow> (s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> S_A"
  using S_NS_stable unfolding S_A_def .

lemma NS_A_stable: "(s,t) \<in> NS_A \<Longrightarrow> (s \<cdot> \<delta>, t \<cdot> \<delta>) \<in> NS_A"
  using S_NS_stable unfolding NS_A_def .

lemma NS_A_mono: assumes st: "(s,t) \<in> NS_A" shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> NS_A"
proof 
  fix \<alpha> :: "'v \<Rightarrow> 'a"
  assume ran: "range \<alpha> \<subseteq> A"
  from st ran have "(eval s \<alpha>, eval t \<alpha>) \<in> NS" unfolding NS_A_def by auto
  from wm[OF eval_A eval_A _ this, of "map (\<lambda> t. eval t \<alpha>) bef" "map (\<lambda> t. eval t \<alpha>) aft" f] ran eval_A
  show "(eval (Fun f (bef @ s # aft)) \<alpha>, eval (Fun f (bef @ t # aft)) \<alpha>) \<in> NS" by auto
qed

lemma NS_A_NS_A: "(x,y) \<in> NS_A \<Longrightarrow> (y,z) \<in> NS_A \<Longrightarrow> (x,z) \<in> NS_A"
  using trans_NS unfolding NS_A_def trans_on_def using eval_A[of _ x] eval_A[of _ y] eval_A[of _ z]
  by blast

lemma S_A_S_A: "(x,y) \<in> S_A \<Longrightarrow> (y,z) \<in> S_A \<Longrightarrow> (x,z) \<in> S_A"
  using trans_S unfolding S_A_def trans_on_def using eval_A[of _ x] eval_A[of _ y] eval_A[of _ z]
  by blast

lemma NS_A_S_A: "(x,y) \<in> NS_A \<Longrightarrow> (y,z) \<in> S_A \<Longrightarrow> (x,z) \<in> S_A"
  using compat_NS_S unfolding S_A_def NS_A_def by blast

lemma S_A_NS_A: "(x,y) \<in> S_A \<Longrightarrow> (y,z) \<in> NS_A \<Longrightarrow> (x,z) \<in> S_A"
  using compat_S_NS unfolding S_A_def NS_A_def by blast

lemma refl_NS_A: "(x,x) \<in> NS_A"
  using refl_NS unfolding NS_A_def refl_on_def using eval_A[of _ x] by blast

lemma S_A_imp_NS_A: "st \<in> S_A \<Longrightarrow> st \<in> NS_A"
  unfolding S_A_def NS_A_def using S_imp_NS by blast

lemma SN_S_A: "SN (S_A)" 
proof
  fix f
  assume all: "\<forall> i. (f i, f (Suc i)) \<in> S_A"
  define \<alpha> where "\<alpha> = (\<lambda> x :: 'v. I undefined [])"
  define g where "g = (\<lambda> i. eval (f i) \<alpha>)"
  have ran: "range \<alpha> \<subseteq> A" using I_A[of Nil] unfolding \<alpha>_def by auto
  with all[unfolded S_A_def] have "\<And> i. (g i, g (Suc i)) \<in> S" 
    unfolding g_def by auto
  with SN[unfolded SN_on_def] have "g 0 \<notin> A" by auto
  thus False using eval_A[OF ran] unfolding g_def by auto
qed

lemma redtriple_order: "redtriple_order S_A NS_A NS_A"
proof 
  show "SN S_A" using SN_S_A .
  show "ctxt.closed NS_A" by (rule one_imp_ctxt_closed[OF NS_A_mono])
  show "subst.closed S_A" using S_A_stable by auto
  show "subst.closed NS_A" using NS_A_stable by auto
  show "refl NS_A" using refl_NS_A unfolding refl_on_def by auto
  show "trans S_A" using S_A_S_A unfolding trans_def by blast
  show "trans NS_A" using NS_A_NS_A unfolding trans_def by blast
  show "NS_A O S_A \<subseteq> S_A" using NS_A_S_A by blast
  show "S_A O NS_A \<subseteq> S_A" using S_A_NS_A by blast
  show "S_A \<subseteq> NS_A" using S_A_imp_NS_A by blast
qed
end

locale mono_wf_algebra = wf_algebra NS S A I "typ" for
    NS S :: "'a rel" and A :: "'a set" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" and "typ" :: "'v itself" 
  + assumes sm: "a \<in> A \<Longrightarrow> b \<in> A \<Longrightarrow> set (bef @ aft) \<subseteq> A 
      \<Longrightarrow> (a,b) \<in> S \<Longrightarrow> (I f (bef @ a # aft), I f (bef @ b # aft)) \<in> S"
begin

lemma S_A_mono: assumes st: "(s,t) \<in> S_A" shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> S_A"
proof 
  fix \<alpha> :: "'v \<Rightarrow> 'a"
  assume ran: "range \<alpha> \<subseteq> A"
  from st ran have "(eval s \<alpha>, eval t \<alpha>) \<in> S" unfolding S_A_def by auto
  from sm[OF eval_A eval_A _ this, of "map (\<lambda> t. eval t \<alpha>) bef" "map (\<lambda> t. eval t \<alpha>) aft" f] ran eval_A
  show "(eval (Fun f (bef @ s # aft)) \<alpha>, eval (Fun f (bef @ t # aft)) \<alpha>) \<in> S" by auto
qed

lemma mono_redtriple_order: "mono_redtriple_order S_A NS_A NS_A" 
proof -
  interpret redtriple_order S_A NS_A NS_A by (rule redtriple_order)
  show ?thesis
  proof
    show "ctxt.closed S_A" using one_imp_ctxt_closed[OF S_A_mono] by auto
  qed
qed
end
 


locale ws_wf_algebra = wf_algebra NS S A I "typ" for
    NS S :: "'a rel" and A :: "'a set" and I :: "'f \<Rightarrow> 'a list \<Rightarrow> 'a" and "typ" :: "'v itself" 
    and \<sigma> :: "'f status" +
  assumes ws: "i \<in> set (status \<sigma> (f,length ss)) \<Longrightarrow> (I f ss, (ss ! i)) \<in> NS"
begin
lemma NS_A_arg: assumes i: "i \<in> set (status \<sigma> (f,length ts))"
  shows "(Fun f ts, ts ! i) \<in> NS_A"
proof 
  fix \<alpha> :: "'v \<Rightarrow> 'a"
  assume "range \<alpha> \<subseteq> A"
  from i status[of \<sigma> f "length ts"] have ii: "i < length ts" by auto
  then have id: "eval (ts ! i) \<alpha> = (map (\<lambda> t. eval t \<alpha>) ts) ! i" by auto
  show "(eval (Fun f ts) \<alpha>, eval (ts ! i) \<alpha>) \<in> NS" 
    unfolding eval_term.simps id
    by (rule ws, insert i, auto)
qed

lemma ws_redpair_order: "ws_redpair_order S_A NS_A \<sigma>"
proof -
  interpret redtriple_order S_A NS_A NS_A by (rule redtriple_order)
  show ?thesis
    by (unfold_locales, insert NS_A_arg S_A_imp_NS_A, auto simp: simple_arg_pos_def)
qed
end

end
