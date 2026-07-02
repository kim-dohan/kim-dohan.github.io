(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Pointwise_Extension
imports
  Knuth_Bendix_Order.Lexicographic_Extension
begin

fun pointwise_ext :: "('a \<Rightarrow> 'a \<Rightarrow> bool \<times> bool) \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> bool \<times> bool"
where "pointwise_ext f [] [] = (False, True)"
    | "pointwise_ext f (_ # _) [] = (False, False)"
    | "pointwise_ext f [] (_ # _) = (False, False)"
    | "pointwise_ext f (a # as) (b # bs) = (let (stri,nstri) = f a b in 
         (if nstri then (let (strir,nstrir) = pointwise_ext f as bs in if nstrir then (stri \<or> strir, True) else (False, False))
                   else (False, False)))"

lemma pointwise_ext_iff: "(pointwise_ext f xs ys) = (length xs = length ys \<and> 
  ((\<exists> i < length ys. fst (f (xs ! i) (ys !i))) \<and> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i)))),
  length xs = length ys \<and> 
  (\<forall> i < length ys. snd (f (xs ! i) (ys ! i))))
  " (is "?pw xs ys = (?stri xs ys, ?nstri xs ys)")
proof (induct xs arbitrary: ys)
  case Nil then show ?case by (cases ys, auto)
next
  case (Cons a as)
  note oCons = this
  from oCons show ?case 
  proof (cases ys, simp)
    case (Cons b bs)
    show ?thesis 
    proof (cases "f a b")
      case (Pair stri nstri) note oPair = this
      show ?thesis
      proof (cases nstri)
        case False
        with Pair Cons show ?thesis by auto
      next
        case True
        show ?thesis 
        proof (cases "?pw as bs")
          case (Pair strir nstrir)
          note IH = Pair[unfolded oCons, simplified]
          note strir = IH[THEN conjunct1, symmetric]
          note nstrir = IH[THEN conjunct2, symmetric]
          show ?thesis 
            by (simp add: Cons oPair Pair all_Suc_conv ex_Suc_conv nstrir strir)
        qed
      qed
    qed
  qed
qed

lemma pointwise_ext_imp_lex_ext:
  "fst (pointwise_ext f xs ys) \<Longrightarrow> fst (lex_ext f m xs ys)"
  unfolding pointwise_ext_iff lex_ext_iff by auto

lemma pointwise_ext_SN_2: assumes compat: "\<And> x y z. \<lbrakk>snd (g x y); fst (g y z)\<rbrakk> \<Longrightarrow> fst (g x z)"
  and SN:  "SN {(s,t). fst (g s t)}"
  shows "SN { (ys, xs). fst (pointwise_ext g ys xs) }"
  by (rule SN_subset, rule lex_ext_SN_2[OF compat SN], auto simp: pointwise_ext_imp_lex_ext) 

lemma pointwise_ext_snd_neq_imp_fst: 
  assumes snd_neq_imp_fst: "\<And> x y. \<lbrakk>snd (g x y); x \<noteq> y\<rbrakk> \<Longrightarrow> fst (g x y)"
  and snd: "snd (pointwise_ext g as bs)"
  and neq: "as \<noteq> bs"
  shows "fst (pointwise_ext g as bs)"
proof -
  from snd[unfolded pointwise_ext_iff] have ge: "\<And> j. j < length bs \<Longrightarrow> snd (g (as ! j) (bs ! j))" 
        and len: "length as = length bs" by auto
  from neq len obtain j where j: "j < length bs" and neq: "as ! j \<noteq> bs ! j" 
    unfolding list_eq_iff_nth_eq by auto
  with ge[OF j] snd_neq_imp_fst have gt: "fst (g (as ! j) (bs ! j))" by auto
  with j have "\<exists> j < length bs. fst (g (as ! j) (bs ! j))" by auto
  with snd show ?thesis 
    unfolding pointwise_ext_iff by auto
qed

lemma pointwise_ext_refl:
  assumes "\<And> x. snd (g x x)"
  shows "snd (pointwise_ext g xs xs)"
using assms
by (unfold pointwise_ext_iff, auto)

lemma pointwise_ext_trans:
  assumes compat: "\<And> x y z. \<lbrakk>fst(g x y); snd(g y z)\<rbrakk> \<Longrightarrow> fst(g x z)"
  assumes snd_trans: "\<And> x y z. \<lbrakk>snd(g x y); snd(g y z)\<rbrakk> \<Longrightarrow> snd(g x z)"
  and one: "fst (pointwise_ext g xs ys)"
  and two: "fst (pointwise_ext g ys zs)"
  shows "fst (pointwise_ext g xs zs)"
proof -
  let ?nx = "length xs"  
  let ?ny = "length ys"
  let ?nz = "length zs"
  from one[unfolded pointwise_ext_iff] obtain i where i: "i < ?nx" and stri: "fst (g (xs ! i) (ys ! i))" and len1: "?nx = ?ny" and nstri1: "\<forall> i < ?nx. snd (g (xs ! i) (ys ! i))" by auto
  from two[unfolded pointwise_ext_iff] have len2: "?ny = ?nz" and nstri2: "\<forall> i < ?ny. snd (g (ys ! i) (zs ! i))" by auto
  from nstri1 nstri2 snd_trans have nstri: "\<forall> i < ?nx. snd (g (xs ! i) (zs ! i))" unfolding len1 len2 by blast
  from compat[OF stri ] nstri2[THEN spec] len1 i have stri: "fst (g (xs ! i) (zs ! i))" by simp
  from stri nstri i len2[unfolded len1[symmetric]] 
  show ?thesis unfolding pointwise_ext_iff by auto
qed

lemma pointwise_snd_trans:
  assumes snd_trans: "\<And> x y z. \<lbrakk>snd(g x y); snd(g y z)\<rbrakk> \<Longrightarrow> snd(g x z)"
  and one: "snd (pointwise_ext g xs ys)"
  and two: "snd (pointwise_ext g ys zs)"
  shows "snd (pointwise_ext g xs zs)"
proof -
  let ?nx = "length xs"  
  let ?ny = "length ys"
  let ?nz = "length zs"
  from one[unfolded pointwise_ext_iff] have len1: "?nx = ?ny" and nstri1: "\<forall> i < ?nx. snd (g (xs ! i) (ys ! i))" by auto
  from two[unfolded pointwise_ext_iff] have len2: "?ny = ?nz" and nstri2: "\<forall> i < ?ny. snd (g (ys ! i) (zs ! i))" by auto
  from nstri1 nstri2 snd_trans have nstri: "\<forall> i < ?nx. snd (g (xs ! i) (zs ! i))" unfolding len1 len2 by blast
  from nstri len2[unfolded len1[symmetric]] 
  show ?thesis unfolding pointwise_ext_iff by auto
qed

end
