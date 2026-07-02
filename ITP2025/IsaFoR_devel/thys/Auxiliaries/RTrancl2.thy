(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory RTrancl2
imports 
  "Transitive-Closure-II.RTrancl"
  "Collections.RBTSetImpl"
begin

subsection \<open>Instantiation using list operations\<close>

text \<open>It follows an implementation based on lists. 
 Here, the working list algorithm is implemented outside the locale so that
 it can be used for code generation. In general, it is not terminating, 
 therefore we use partial\_function instead of function.\<close>

partial_function(tailrec) mk_rtrancl_set_main where 
 [code]:  "mk_rtrancl_set_main r todo fin = (case todo of [] \<Rightarrow> fin
     | Cons a tod \<Rightarrow> 
             (if rs.memb a fin then mk_rtrancl_set_main r tod fin
                 else mk_rtrancl_set_main r (r a @ tod) (rs.ins_dj a fin)))" 

definition mk_rtrancl_set where 
  "mk_rtrancl_set r init \<equiv> mk_rtrancl_set_main r init (rs.empty ())"


locale subsumption_set = 
  fixes r :: "'a \<Rightarrow> 'a list" 

sublocale subsumption_set \<subseteq> subsumption r "(=)" set
  by (unfold_locales, auto)

locale relation_subsumption_set = subsumption_set r for r :: "'a :: linorder \<Rightarrow> 'a list" +
  assumes rtrancl_fin: "\<And> a. finite {b. (a,b) \<in> { (a,b) . b \<in> set (r a)}^*}"

abbreviation(input) sel_list where "sel_list x \<equiv> case x of Cons h t \<Rightarrow> (h,t)"

sublocale subsumption_set \<subseteq> subsumption_impl r "(=)" set sel_list append length 
proof(unfold_locales, rule finite_set)
  fix b a c
  assume "set b \<noteq> {}" and "sel_list b = (a,c)"
  then show "set b = insert a (set c) \<and> length c < length b" 
    by (cases b, auto)
qed auto

sublocale relation_subsumption_set \<subseteq> relation_subsumption_impl r "(=)" set sel_list append length 
  by (unfold_locales, rule rtrancl_fin)

context relation_subsumption_set
begin

text \<open>The main equivalence proof between the generic work list algorithm
and the one operating on sets\<close>
lemma mk_rtrancl_set_main: "rs.\<alpha> fins = fin \<Longrightarrow> rs.\<alpha> (mk_rtrancl_set_main r todo fins) = mk_rtrancl_main todo fin"
proof (induct todo fin arbitrary: fins rule: mk_rtrancl_main.induct)
  case (1 todo fin fins)
  note simp = mk_rtrancl_set_main.simps[of _ todo fins] mk_rtrancl_main.simps[of todo fin]
  show ?case (is "?l = ?r")
  proof (cases todo)
    case Nil
    show ?thesis unfolding simp unfolding Nil using 1(3) by simp
  next
    case (Cons a tod)
    show ?thesis 
    proof (cases "a \<in> fin")
      case True
      from True have l: "?l = rs.\<alpha> (mk_rtrancl_set_main r tod fins)" 
        unfolding simp unfolding Cons using 1(3) by (simp add: rs.correct)
      from True have r: "?r = mk_rtrancl_main tod fin" 
        unfolding simp unfolding Cons by auto
      show ?thesis unfolding l r
        by (rule 1(1), insert 1(2,3) Cons True, auto)
    next
      case False
      from False have l: "?l = rs.\<alpha> (mk_rtrancl_set_main r (r a @ tod) (rs.ins_dj a fins))" 
        unfolding simp unfolding Cons using 1(3) by (simp add: rs.correct)
      from False have r: "?r = mk_rtrancl_main (r a @ tod) (insert a fin)" 
        unfolding simp unfolding Cons by auto
      show ?thesis unfolding l r
        by (rule 1(2), insert False Cons 1(3), auto simp: rs.correct)
    qed
  qed
qed

lemma mk_rtrancl_set: "rs.\<alpha> (mk_rtrancl_set r init) = mk_rtrancl init"
  unfolding mk_rtrancl_set_def mk_rtrancl_def
  by (rule mk_rtrancl_set_main, simp add: rs.correct)
  
end
end
