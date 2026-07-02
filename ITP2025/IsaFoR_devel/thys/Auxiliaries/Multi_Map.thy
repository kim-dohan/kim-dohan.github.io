(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Multi_Map
imports
  "HOL-Library.Mapping"
begin

text \<open>Multimaps store for each key multiple values.
  In contrast to theory Multimap, there is special treatment of None and Some,
  there is a dedicated type for multimaps, but at the moment there are no delete operations.\<close>

fun option_list_to_list :: "'a list option \<Rightarrow> 'a list" where
  "option_list_to_list None = []"
| "option_list_to_list (Some as) = as"

typedef ('k,'a)multimap = "{(f,m :: ('k,'a list)mapping,all) | f m all. 
  (\<forall> k as. (Mapping.lookup m k = Some as \<longrightarrow> f ` set as = {k})) \<and> 
  set all = \<Union> ((set o option_list_to_list o Mapping.lookup m) ` Mapping.keys m)}"
  by (rule exI[of _ "(undefined, Mapping.empty, [])"], transfer, auto)

setup_lifting type_definition_multimap

context
begin
qualified lift_definition empty :: "('a \<Rightarrow> 'k) \<Rightarrow> ('k,'a)multimap" is "\<lambda> f. (f,Mapping.empty,[])"
  by (transfer, auto)

qualified lift_definition insert :: "'a \<Rightarrow> ('k,'a)multimap \<Rightarrow> ('k,'a)multimap" is
  "\<lambda> a (f,m,all). let 
     k = f a;
     old = option_list_to_list (Mapping.lookup m k);
     new = a # old
     in (f,Mapping.update k new m, a # all)" 
proof (clarify, unfold Let_def, intro exI, rule conjI[OF refl], unfold keys_update, 
       intro conjI allI impI)
  fix a aa ad b f m k as all
  assume prev: "\<forall>k as. Mapping.lookup m k = Some as \<longrightarrow> f ` set as = {k}"
  and upd: "Mapping.lookup (Mapping.update (f a) (a # 
       (option_list_to_list (Mapping.lookup m (f a)))) m) k =
       Some as"
  from prev have prev: "\<And> k as. Mapping.lookup m k = Some as \<Longrightarrow> f ` set as = {k}" by auto
  show "f ` set as = {k}"
  proof (cases "k = f a")
    case False
    with upd have "Mapping.lookup m k = Some as" by (transfer, auto)
    from prev[OF this] show ?thesis .
  next
    case True
    with upd have as: "as = (a # (option_list_to_list (Mapping.lookup m (f a))))" 
      by (transfer, auto)
    show ?thesis unfolding as using prev[of "f a"] True
      by (cases "Mapping.lookup m (f a)", auto)
  qed
next
  fix all ad a and f :: "'a \<Rightarrow> 'k" and m :: "('k,'a list)mapping"
  let ?look = "Mapping.lookup m"
  let ?keys = "Mapping.keys m"
  let ?g = "(set \<circ> option_list_to_list \<circ> ?look)"
  let ?look' = "Mapping.lookup
         (Mapping.update (f a) (a # (option_list_to_list (?look (f a)))) m)"
  assume all: "set all = \<Union>(?g ` ?keys)"
  let ?f = "(set \<circ> option_list_to_list \<circ> ?look')"
  show "set (a # all) =
    \<Union>(?f ` Set.insert (f a) (Mapping.keys m))" (is "?l = ?r")
  proof -
    define l where "l = ?l" 
    define r where "r = ?r" 
    have "a \<in> ?l" by simp
    have "f a \<in> Set.insert (f a) ?keys" by auto
    moreover have "a \<in> ?f (f a)" by (transfer, auto)
    ultimately have "a \<in> ?r" by auto
    {
      fix b
      assume ba: "b \<noteq> a"
      {
        assume "b \<in> ?l"
        with ba all obtain k where k: "k \<in> ?keys" and b: "b \<in> ?g k" by auto
        then obtain as where look: "?look k = Some as" and b: "b \<in> set as"
          by (cases "?look k", (transfer, auto)+)
        from look b obtain bs where "?look' k = Some bs" and b: "b \<in> set bs"
          by (cases "k = f a", (transfer, force)+)
        then have "b \<in> ?f k" by auto
        with k have "b \<in> ?r" by auto
      }
      moreover
      {
        assume "b \<in> ?r"
        then obtain k where k: "k \<in> Set.insert (f a) ?keys" and b: "b \<in> ?f k" by blast
        have "b \<in> ?l"
        proof (cases "k = f a")
          case False
          with k have k: "k \<in> ?keys" by auto
          from False k b
          have "b \<in> ?g k" by (transfer, auto)
          with k show ?thesis using all by auto
        next
          case True
          from b obtain as where look: "?look' k = Some as" and b: "b \<in> set as"
            by (cases "?look' k", (transfer, auto)+)
          from look have as: "as = a # (option_list_to_list (?look k))" unfolding True
            by (transfer, auto)
          with b ba have "b \<in> set (option_list_to_list (?look k))" by auto
          then obtain as where look: "?look k = Some as" and b: "b \<in> set as"
            by (cases "?look k", (transfer, force)+)
          from look have k: "k \<in> ?keys" by (transfer, auto)
          from look b have b: "b \<in> ?g k" by auto
          from b k show "b \<in> ?l" using all by auto
        qed
      }
      ultimately have "(b \<in> ?l) = (b \<in> ?r)" by blast
    }
    with \<open>a \<in> ?l\<close> \<open>a \<in> ?r\<close> show "?l = ?r" 
      unfolding l_def[symmetric] r_def[symmetric]
      by force
  qed
qed  

qualified lift_definition lookup :: "('k,'a)multimap \<Rightarrow> 'k \<Rightarrow> 'a list" is
  "\<lambda> (f,m,all) k. option_list_to_list (Mapping.lookup m k)" .

qualified lift_definition "values" :: "('k,'a)multimap \<Rightarrow> 'a list" is
  "\<lambda> (f,m,all). all" .

qualified lift_definition key_fun :: "('k,'a)multimap \<Rightarrow> 'a \<Rightarrow> 'k" is fst .

lemma key_fun_empty[simp]: "key_fun (empty f) = f" by (transfer, auto)

lemma key_fun_insert[simp]: "key_fun (insert a m) = key_fun m" by (transfer, auto simp: Let_def)

lemma values_empty[simp]: "set (values (empty f)) = {}"
  by (transfer, auto)

lemma values_insert[simp]: "set (values (insert a m)) = Set.insert a (set (values m))" 
  by (transfer, auto simp: Let_def)

lemma lookup[simp]: "set (lookup m k) = set (values m) \<inter> {a. key_fun m a = k}"
proof (transfer, clarify, unfold fst_conv)
  fix a b k f all and m :: "('k,'a list)mapping"
  let ?look = "Mapping.lookup m"
  assume "\<forall>k as. ?look k = Some as \<longrightarrow> f ` set as = {k}"
  and all: "set all = \<Union>((set \<circ> option_list_to_list \<circ> ?look) ` Mapping.keys m)"
  then have inv: "\<And>k  as. ?look k = Some as \<Longrightarrow> f ` set as = {k}" by auto
  let ?l = "set (option_list_to_list (?look k))"
  let ?r = "\<Union>((set \<circ> option_list_to_list \<circ> ?look) ` Mapping.keys m) \<inter> {a. f a = k}"
  {
    fix a
    assume "a \<in> ?r"
    then obtain k' where fk: "f a = k" and "k' \<in> Mapping.keys m" and 
      a: "a \<in> set (option_list_to_list (?look k'))" by auto
    then obtain as where look: "?look k' = Some as" and as: "a \<in> set as" by (cases "?look k'", auto)
    from inv[OF look] as fk have "k' = k" by auto
    then have "\<exists> as. ?look k = Some as \<and> f a = k \<and> a \<in> set as" using look fk as by auto
  } note mem_r = this
  have "?l = ?r"
  proof (cases "?look k")
    case None
    with mem_r show ?thesis by auto
  next
    case (Some as)
    then have "?l = set as" by auto
    also have "\<dots> = ?r"
    proof 
      show "?r \<subseteq> set as" using mem_r unfolding Some by auto
      show "set as \<subseteq> ?r" using inv[OF Some] Some by (transfer, auto)
    qed
    finally show ?thesis .
  qed
  with all show "?l = set all \<inter> {a. f a = k}" by simp
qed
end

hide_const option_list_to_list

end
