theory Map_Of
imports 
  "HOL-Library.Mapping"
  Show.Shows_Literal
begin
  
definition map_of_default :: "'b \<Rightarrow> ('a \<times> 'b)list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "map_of_default d xs = Mapping.lookup_default d (Mapping.of_alist xs)" 

lemma map_of_default_Nil[simp]: "map_of_default d [] = (\<lambda>x. d)"
  and map_of_default_Cons:
   "map_of_default d (a#alist) k = (if fst a = k then snd a else map_of_default d alist k)"
  by (auto simp: map_of_default_def lookup_default_def lookup_of_alist)

lemma map_of_defaultI: assumes "\<And> a b. (a,b) \<in> set xs \<Longrightarrow> P b" "P d"
  shows "P (map_of_default d xs a)"
proof -
  note d = map_of_default_def lookup_default_def lookup_of_alist
  show ?thesis
  proof (cases "map_of xs a")
    case None
    then show ?thesis unfolding d using assms(2) by auto
  next
    case (Some b)
    then have ab: "(a,b) \<in> set xs" by (rule map_of_SomeD)
    from assms(1)[OF this]
    show ?thesis unfolding d Some by auto
  qed
qed

lemma map_of_defaultI2: assumes "\<And> b. (a,b) \<in> set xs \<Longrightarrow> P b" "a \<notin> fst ` set xs \<Longrightarrow> P d"
  shows "P (map_of_default d xs a)"
proof -
  note d = map_of_default_def lookup_default_def lookup_of_alist
  show ?thesis
  proof (cases "map_of xs a")
    case None with this[unfolded map_of_eq_None_iff] assms(2) show ?thesis by (auto simp: d)
  next
    case (Some b)
    then have ab: "(a,b) \<in> set xs" by (rule map_of_SomeD)
    from assms(1)[OF this]
    show ?thesis unfolding d Some by auto
  qed
qed

definition map_of :: "('a \<times> 'b)list \<Rightarrow> 'a \<Rightarrow> 'b option" where
  "map_of xs = Mapping.lookup (Mapping.of_alist xs)" 
  
hide_const(open) map_of
  
lemma map_of[simp]: "Map_Of.map_of = map_of" 
  by (intro ext, unfold Map_Of.map_of_def, rule lookup_of_alist) 

definition map_of_total :: "('a \<Rightarrow> showsl) \<Rightarrow> ('a \<times> 'b)list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "map_of_total err xys = (let m = Mapping.of_alist xys in (\<lambda> x. case Mapping.lookup m x of
     Some y \<Rightarrow> y | None \<Rightarrow> Code.abort (err x (STR '''')) (\<lambda> _. the None)))" 
  
lemma map_of_total[simp]: "map_of_total err xs = the o map_of xs"
  unfolding lookup_of_alist map_of_total_def Let_def
  by (intro ext, auto split: option.splits)
    
end
