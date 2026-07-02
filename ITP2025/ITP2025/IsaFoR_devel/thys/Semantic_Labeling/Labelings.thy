(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Labelings 
imports 
  First_Order_Rewriting.Trs
  Deriving.Countable_Generator
begin


datatype ('f,'l) lab =
  Lab "('f, 'l) lab" 'l
| FunLab "('f, 'l) lab" "('f, 'l) lab list"
| UnLab 'f
| Sharp "('f, 'l) lab"

derive countable lab

text \<open>An alternative induction scheme for labs.\<close>
lemma
  fixes P :: "('f,'l)lab \<Rightarrow> bool"
  assumes "\<And>f. P(UnLab f)"
    and "\<And>f l. P f \<Longrightarrow> P(Lab f l)"
    and "\<And>f. P f \<Longrightarrow> P(Sharp f)"
    and "\<And>f ls. P f \<Longrightarrow> (\<And>l. l \<in> set ls \<Longrightarrow> P l) \<Longrightarrow> P(FunLab f ls)"
  shows lab_induct[case_names UnLab Lab Sharp FunLab,induct type: lab]: "P f"
  by (rule lab.induct, insert assms, auto)

fun label_depth :: "('f,'l)lab \<Rightarrow> nat"
where "label_depth (UnLab _) = 0"
   |  "label_depth (Lab f _) = Suc (label_depth f)"
   |  "label_depth (FunLab f _) = Suc (label_depth f)"
   |  "label_depth (Sharp f) = Suc (label_depth f)"

fun gen_label :: "('f,'l)lab \<Rightarrow> nat \<Rightarrow> ('f,'l)lab"
where "gen_label f 0 = f"
   |  "gen_label f (Suc n) = FunLab (gen_label f n) []"

lemma label_depth_gen_label: "label_depth (gen_label f n) = n + label_depth f"
  by (induct n, auto)


lemma gen_label_inj_i: "inj (gen_label f)"
  unfolding inj_on_def
proof (intro ballI, simp, rule)
  fix n m
  assume "gen_label f n = gen_label f m"
  then have "label_depth (gen_label f n) = label_depth (gen_label f m)" 
    by simp  
  then show "n = m" unfolding label_depth_gen_label by auto
qed

lemma gen_label_inj_f: "inj (\<lambda> f. gen_label f i)"
  unfolding inj_on_def
proof (intro ballI, simp, rule)
  fix f g
  assume "gen_label f i = gen_label g i"
  then show "f = g"
    by (induct i arbitrary: f g, auto)
qed

lemma infinite_lab: "infinite (UNIV :: ('f,'v)lab set)" (is "infinite ?U")
proof
  assume "finite ?U"
  from finite_list[OF this]
  obtain L where L: "set L = ?U" by auto
  let ?n = "Suc (max_list (map label_depth L))"
  have "gen_label f ?n \<notin> set L"
  proof
    assume "gen_label f ?n \<in> set L"
    then have "label_depth (gen_label f ?n) \<in> set (map label_depth L)" by force
    from max_list[OF this] have "label_depth (gen_label f ?n) < ?n" by auto
    then show False unfolding label_depth_gen_label by simp
  qed
  then show False unfolding L by auto
qed

(* unlab removes one layer of labelings *)
fun unlab :: "('f, 'l) lab \<Rightarrow> ('f, 'l) lab" where
  "unlab (Lab f l) = f"
| "unlab (FunLab f l) = f"
| "unlab x = x"

abbreviation unlab_term :: "(('f,'l)lab,'v)term \<Rightarrow> (('f,'l)lab,'v)term"
where "unlab_term \<equiv> map_funs_term unlab"

abbreviation unlab_subst :: "(('f,'l)lab,'v)subst \<Rightarrow> (('f,'l)lab,'v)subst"
where "unlab_subst \<equiv> map_funs_subst unlab"

(* init_lab adds empty labelings to all function symbols *)
fun init_lab :: "'f \<Rightarrow> ('f, 'l) lab" where
  "init_lab f = UnLab f"

abbreviation init_lab_term :: "('f,'v)term \<Rightarrow> (('f,'l)lab,'v)term"
where "init_lab_term \<equiv> map_funs_term init_lab"

abbreviation init_lab_subst :: "('f,'v)subst \<Rightarrow> (('f,'l)lab,'v)subst"
where "init_lab_subst \<equiv> map_funs_subst init_lab"


lemma unlab_init_lab_term_sound: "unlab_term (init_lab_term t) = init_lab_term t"
proof (induct t, simp)
  case (Fun f ss)
  then show ?case by (induct ss, auto)
qed


abbreviation unlab_trs :: "(('f,'l)lab,'v)trs \<Rightarrow> (('f,'l)lab,'v)trs"
where "unlab_trs \<equiv> map_funs_trs unlab"

abbreviation init_lab_rule :: "('f,'v)rule \<Rightarrow> (('f,'l)lab,'v)rule"
where "init_lab_rule \<equiv> map_funs_rule init_lab"

abbreviation init_lab_trs :: "('f,'v)trs \<Rightarrow> (('f,'l)lab,'v)trs"
where "init_lab_trs \<equiv> map_funs_trs init_lab"

lemma unlab_init_lab_trs_sound: "unlab_trs (init_lab_trs R) = (init_lab_trs R)"
  by (force simp: unlab_init_lab_term_sound map_funs_trs.simps)

text \<open>use semantic labeling with concrete symbol type\<close>

fun
  label :: "('f, 'l) lab \<Rightarrow> nat \<Rightarrow> ('l + ('f, 'l) lab list) \<Rightarrow> ('f, 'l) lab"
where
  "label f n (Inl l) = Lab f l" |
  "label f n (Inr l) = FunLab f l"

fun label_decomp :: "('f,'l)lab \<Rightarrow> ('f,'l)lab \<times> ('l + ('f,'l) lab list)"
where "label_decomp (Lab f l) = (f, Inl l)"
    | "label_decomp (FunLab f l) = (f, Inr l)"

lemma label_decomp_label: "label_decomp (label f n l) = (f,l)" by (cases l, auto)

end

