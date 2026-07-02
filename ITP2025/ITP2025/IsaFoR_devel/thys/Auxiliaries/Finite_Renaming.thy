(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2023)
License: LGPL (see file COPYING.LESSER)
*)

text \<open>Given a finite renaming as a list of pairs, we generate a computable extension to a bijective
  function (and its inverse) for the full type.\<close>

theory Finite_Renaming
  imports Main
begin


definition extend_finite_map :: "('a \<times> 'a)list \<Rightarrow> ('a \<Rightarrow> 'a) \<times> ('a \<Rightarrow> 'a)" where
  "extend_finite_map xs = (let d = map fst xs; r = map snd xs;
     only_r = filter (\<lambda> y. y \<notin> set d) r;  
     only_d = filter (\<lambda> x. x \<notin> set r) d; 
     ys = xs @ zip only_r only_d;
     ys' = map (\<lambda> (x,y). (y,x)) ys;
     fg = map_of ys;
     gf = map_of ys'
     in (\<lambda> x. case fg x of Some y \<Rightarrow> y | None \<Rightarrow> x,
         \<lambda> y. case gf y of Some x \<Rightarrow> x | None \<Rightarrow> y))"

lemma extend_finite_map:
  assumes "distinct (map fst xs)" "distinct (map snd xs)"
    and "extend_finite_map xs = (fg, gf)"
  shows 
    "gf (fg x) = x" 
    "fg (gf y) = y" 
    "bij fg" 
    "fg o gf = id" 
    "gf o fg = id" 
    "x \<in> fst ` set xs \<Longrightarrow> map_of xs x = Some (fg x)"
proof -
  define d where "d = map fst xs"  
  define r where "r = map snd xs"  
  define o_r where "o_r = filter (\<lambda> y. y \<notin> set d) r"
  define o_d where "o_d = filter (\<lambda> x. x \<notin> set r) d" 
  note dist_1 = assms(1-2)[folded d_def r_def]
  have dist_2: "distinct o_r" "distinct o_d" unfolding o_r_def o_d_def using dist_1 by auto
  have dist_3: "distinct (d @ o_r)" "distinct (r @ o_d)" using dist_1 dist_2
    by (auto simp: o_d_def o_r_def)
  have set: "set (d @ o_r) = set (r @ o_d)" unfolding o_r_def o_d_def by auto
  from set distinct_card[OF dist_3(1)] distinct_card[OF dist_3(2)]
  have "length (d @ o_r) = length (r @ o_d)"
    by simp
  hence len: "length d = length r" "length o_r = length o_d"
    unfolding d_def r_def by auto
  define ys where "ys = xs @ zip o_r o_d"
  let ?iys = "map (\<lambda>(x, y). (y, x)) ys"
  have map_fst: "map fst ys = d @ o_r" unfolding ys_def map_append d_def[symmetric] using len by auto
  have map_snd: "map snd ys = r @ o_d" unfolding ys_def map_append r_def[symmetric] using len by auto
  have dom_is_ran: "fst ` set ys = snd ` set ys" unfolding set_map[symmetric] map_fst map_snd by fact
  have dist: "distinct (map fst ys)" "distinct (map snd ys)" unfolding map_fst map_snd by fact+
  have map: "map fst ?iys = map snd ys" "map snd ?iys = map fst ys" by auto
  have dist': "distinct (map fst ?iys)" "distinct (map snd ?iys)" using dist unfolding map by auto
  from assms(3)[unfolded extend_finite_map_def Let_def, folded d_def r_def, folded o_r_def o_d_def, folded ys_def]
  have fg: "fg = (\<lambda> x. case map_of ys x of None \<Rightarrow> x | Some y \<Rightarrow> y)"
    and gf: "gf = (\<lambda> y. case map_of ?iys y of None \<Rightarrow> y | Some x \<Rightarrow> x)" by auto
  {
    fix x
    show "gf (fg x) = x"
    proof (cases "map_of ys x")
      case N1: None
      hence "x \<notin> fst ` set ys"
        by (meson map_of_eq_None_iff)
      hence "x \<notin> snd ` set ys" using dom_is_ran by auto
      hence "x \<notin> fst ` set ?iys" by force
      hence N2: "map_of ?iys x = None"
        by (meson map_of_eq_None_iff)
      show ?thesis unfolding fg gf N1 N2 option.simps by simp
    next
      case S1: (Some y)
      hence "(x,y) \<in> set ys" by (meson map_of_SomeD)
      hence "(y,x) \<in> set ?iys" by auto
      with dist'(1) have S2: "map_of ?iys y = Some x" by simp
      show ?thesis unfolding fg gf S1 S2 option.simps by simp
    qed
  } note gf_fg = this
  {
    fix x
    show "fg (gf x) = x"
    proof (cases "map_of ?iys x")
      case N1: None
      hence "x \<notin> fst ` set ?iys"
        by (meson map_of_eq_None_iff)
      hence "x \<notin> snd ` set ys" by force
      hence "x \<notin> fst ` set ys" using dom_is_ran by auto
      hence N2: "map_of ys x = None"
        by (meson map_of_eq_None_iff)
      show ?thesis unfolding fg gf N1 N2 option.simps by simp
    next
      case S1: (Some y)
      hence "(x,y) \<in> set ?iys" by (meson map_of_SomeD)
      hence "(y,x) \<in> set ys" by auto
      with dist(1) have S2: "map_of ys y = Some x" by simp
      show ?thesis unfolding fg gf S1 S2 option.simps by simp
    qed
  } note fg_gf = this
  show "bij fg" using fg_gf gf_fg
    by (metis bijI')
  show "fg \<circ> gf = id" unfolding o_def fg_gf by auto
  show "gf \<circ> fg = id" unfolding o_def gf_fg by auto
  assume "x \<in> fst ` set xs"
  then obtain y where xy: "(x,y) \<in> set xs" by auto
  with assms(1)
  have map_xs: "map_of xs x = Some y" by auto
  from xy have "(x,y) \<in> set ys" unfolding ys_def by auto
  with dist(1) have "map_of ys x = Some y" by auto
  thus "map_of xs x = Some (fg x)" unfolding fg map_xs by auto
qed

end