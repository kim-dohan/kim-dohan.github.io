(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Size_Change_Termination
imports
  "HOL-Library.Ramsey"
  Deriving.Compare_Order_Instances
  "Abstract-Rewriting.Abstract_Rewriting"
  Auxx.RTrancl2
  Auxx.Util
begin

no_notation eqpoll (infixl "\<approx>" 50)
          
subsection \<open>Size change graphs and algorithms working on them\<close>

datatype ('pp, 'ap) scg =
  Null  \<comment> \<open>zero element to make composition total\<close>
| Scg 'pp 'pp "('ap * 'ap) list" "('ap * 'ap) list"

text \<open>Composition\<close>

definition comp :: "('ap :: linorder * 'ap) list \<Rightarrow> ('ap * 'ap) list \<Rightarrow> ('ap * 'ap) list"
where "comp es es' = remdups_sort [ (x, z). (x,y) \<leftarrow> es, (y',z) \<leftarrow> es', y = y' ]"

lemma set_comp[simp]:
 "set (comp es es') = set es O set es'"
unfolding comp_def by (auto split: if_splits intro!: relcompI) 

text \<open>
 Scg composition depends on an (executable) relation @{term conn} that describes
 connectedness of program points
\<close>

fun scg_comp :: "('pp \<Rightarrow> 'pp \<Rightarrow> bool) \<Rightarrow> ('pp, 'ap :: linorder) scg \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> ('pp, 'ap) scg"
where
 "scg_comp conn (Scg p q str wk) (Scg p' q' str' wk') =
    (if \<not> conn q p' then Null else
     let strs = remdups_sort (comp str str' @ comp str wk' @ comp wk str');
         wks = subtract_list_sorted (remdups_sort (comp wk wk')) strs
     in Scg p q' strs wks)"
| "scg_comp conn Null G = Null"
| "scg_comp conn G Null = Null"

text \<open>Subsumption\<close>

fun subsumes :: "('pp, 'ap) scg \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> bool"
where
 "subsumes (Scg p q str wk) (Scg p' q' str' wk') =
    (p = p' \<and> q = q' \<and> set str \<subseteq> set str' \<and> set wk \<subseteq> set (str' @ wk'))"
| "subsumes G Null = True"
| "subsumes Null G = False"

lemma subsumes_refl[simp]: "subsumes G G"
by (cases G) auto

lemma subsumes_trans[trans]:
 "subsumes F G \<Longrightarrow> subsumes G H \<Longrightarrow> subsumes F H"
by (cases H, simp, induct F G rule: subsumes.induct) auto

lemma subsumes_comp_mono:
 "subsumes G G' \<Longrightarrow> subsumes H H'
 \<Longrightarrow> subsumes (scg_comp conn G H) (scg_comp conn G' H')"
apply (induct G G' rule: subsumes.induct)
apply auto
apply (induct H H' rule: subsumes.induct)
apply (auto simp: Let_def)
apply blast+
done

definition subsume :: "('pp, 'ap) scg set \<Rightarrow> ('pp, 'ap) scg set \<Rightarrow> bool"
where
 "subsume Gs Hs = (\<forall>H\<in>Hs. H \<noteq> Null \<longrightarrow> (\<exists>G\<in>Gs. subsumes G H))"

lemma subsume_refl[simp]: "subsume Gs Gs"
by (force simp: subsume_def)

lemma subsume_trans[trans]:
  assumes "subsume Fs Gs" "subsume Gs Hs"
  shows "subsume Fs Hs"
unfolding subsume_def
proof (intro ballI impI)
  fix H assume "H \<in> Hs" "H \<noteq> Null"
  with \<open>subsume Gs Hs\<close>
  obtain G where G: "G \<in> Gs" "subsumes G H" unfolding subsume_def by auto
  with \<open>H \<noteq> Null\<close> have "G \<noteq> Null" by (cases G, cases H, auto)
  with \<open>subsume Fs Gs\<close> G
  obtain F where F: "F \<in> Fs" "subsumes F G" unfolding subsume_def by auto
  from F G show "\<exists>F\<in>Fs. subsumes F H" using subsumes_trans by auto
qed

lemma subsume_Un[simp]:
 "subsume Fs (Gs \<union> Hs) = (subsume Fs Gs \<and> subsume Fs Hs)"
by (auto simp: subsume_def)

lemma subsume_insert:
 "subsume Fs (insert G Gs) = (subsume Fs {G} \<and> subsume Fs Gs)"
by (auto simp: subsume_def)

text \<open>Transitivity check\<close>

definition trans_scgs
where
 "trans_scgs conn Gs =
   (\<forall>G\<in>set Gs. \<forall>H\<in>set Gs.
     let GH = scg_comp conn G H
     in (\<exists>G'\<in>set Gs. subsumes G' GH))"

subsubsection \<open>Checking the Scgs for descent\<close>

text \<open>Check for in-situ descent\<close>

primrec in_situ :: "('pp, 'ap) scg \<Rightarrow> bool"
where
 "in_situ Null = True"
| "in_situ (Scg p q str wk) = (\<exists>(x,y)\<in>set str. x = y)"

lemma subsumes_in_situ:
 "subsumes G H \<Longrightarrow> in_situ G \<Longrightarrow> in_situ H"
by (induct G H rule: subsumes.induct) auto

text \<open>Sagiv's test (aka cycles check): Some power of G has a strict descent:\<close>

primrec exp :: "('pp \<Rightarrow> 'pp \<Rightarrow> bool) \<Rightarrow> ('pp, 'ap :: linorder) scg \<Rightarrow> nat \<Rightarrow> ('pp, 'ap) scg"
where
 "exp conn G 0 = G"
| "exp conn G (Suc n) = scg_comp conn (exp conn G n) G"

lemma exp_Null[simp]: "exp conn Null n = Null"
by (induct n) auto 


definition sagiv
where
 [code del]: "sagiv conn G = (\<exists>n. in_situ (exp conn G n))"

text \<open>Executable version:\<close>

fun combine :: "('pp, 'ap :: linorder) scg \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> ('pp, 'ap) scg"
where
 "combine (Scg p q str wk) (Scg p' q' str' wk') =
    Scg p q (union_list_sorted str str') (union_list_sorted wk wk')"
| "combine Null S = Null"
| "combine S Null = Null"

lemma in_situ_combine: "in_situ (combine G H) = (in_situ G \<or> in_situ H)"
by (induct G H rule: combine.induct) auto

inductive scg_eqv where
  "scg_eqv Null Null"
| "set str = set str' \<Longrightarrow> set str \<union> set wk = set str' \<union> set wk'
  \<Longrightarrow> scg_eqv (Scg p q str wk) (Scg p q str' wk')"

lemma equiv_class_eq:
  fixes R :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<approx>" 70)
  assumes refl: "\<And>x. x \<approx> x"
  assumes trans: "\<And>x y z. x \<approx> y \<Longrightarrow> y \<approx> z \<Longrightarrow> x \<approx> z"
  assumes sym: "\<And>x y. x \<approx> y \<Longrightarrow> y \<approx> x"
  shows "x \<approx> y = (R x = R y)"
proof
  { fix x y assume "x \<approx> y"
    have "{z. R x z} \<subseteq> {z. R y z}"
    proof
      fix z assume "z \<in> {z. R x z}" then have "x \<approx> z" by simp
      from trans[OF sym[OF this] \<open>x \<approx> y\<close>, THEN sym]
        show "z \<in> {z. R y z}" by simp
    qed
  } note sub = this
  assume "x \<approx> y"
  from sub[OF this] and sub[OF sym[OF this]]
    have "{z. x \<approx> z} = {z. y \<approx> z}" by simp
  then have eq: "\<And>z. z \<in> {z. x \<approx> z} \<longleftrightarrow> z \<in> {z. y \<approx> z}" by simp
  show "R x = R y" by (rule ext) (rule eq[to_pred])
next
  assume "R x = R y" then show "x \<approx> y" by (simp add: refl)
qed

lemma scg_eqv: "scg_eqv G H = (scg_eqv G = scg_eqv H)"
proof (rule equiv_class_eq)
  fix G show "scg_eqv G G"
    by (cases G) (auto intro: scg_eqv.intros)
next
  fix F G H assume "scg_eqv F G" "scg_eqv G H"
  then show "scg_eqv F H" by (auto elim!: scg_eqv.cases intro!: scg_eqv.intros)
next
  fix F G assume "scg_eqv F G"
  then show "scg_eqv G F" by (auto elim!: scg_eqv.cases intro!: scg_eqv.intros)
qed

lemma scg_eqv1: "scg_eqv G = scg_eqv H \<Longrightarrow> scg_eqv G H"
by (rule iffD2[OF scg_eqv])
lemma scg_eqv2: "scg_eqv G H \<Longrightarrow> scg_eqv G = scg_eqv H"
by (rule iffD1[OF scg_eqv])

lemma comp_assoc: 
  "scg_eqv (scg_comp conn (scg_comp conn F G) H)
  (scg_comp conn F (scg_comp conn G H))"
proof (cases "scg_comp conn (scg_comp conn F G) H")
  case Null
  then show ?thesis using scg_eqv.intros[intro]
    by (cases F, auto, cases G, auto, cases H, auto simp: Let_def)
next
  case Scg
  then obtain p1 q1 s1 w1 p2 q2 s2 w2 p3 q3 s3 w3
    where "F = Scg p1 q1 s1 w1"
    "G = Scg p2 q2 s2 w2"
    "H = Scg p3 q3 s3 w3" "conn q1 p2" "conn q2 p3"
    by (cases F, simp, cases G, simp, cases H, simp_all add: Let_def split: if_splits)

  then show ?thesis 
    apply (simp add: Let_def)
    apply (rule scg_eqv.intros)
    apply (auto 0 0)
    apply (blast 16)+
    done
qed

lemma comp_cong: 
assumes G: "scg_eqv G = scg_eqv G'" and H: "scg_eqv H = scg_eqv H'"
shows "scg_eqv (scg_comp conn G H) = scg_eqv (scg_comp conn G' H')"
proof (cases G)
  case Null 
  from G[THEN scg_eqv1] have Null': "G' = Null"
    by (rule scg_eqv.cases) (auto simp: Null)
  show ?thesis 
    by (rule scg_eqv2) (auto simp: Null Null' intro: scg_eqv.intros)
next  
  case (Scg p q s w)
  note scg' = this
  with G[THEN scg_eqv1] obtain sa wa
    where G': "G' = Scg p q sa wa"
    and G_eq: "set s = set sa" "set s \<union> set w = set sa \<union> set wa"
    by (auto elim!: scg_eqv.cases)

  show ?thesis
  proof (cases H)
    case Null
    from H[THEN scg_eqv1] have Null': "H' = Null"
      by (rule scg_eqv.cases) (auto simp: Null)
    show ?thesis 
      by (rule scg_eqv2) (auto simp: scg' G' Null Null' intro: scg_eqv.intros)
  next
    case (Scg p' q' s' w')
    with H[THEN scg_eqv1] obtain sa' wa'
      where H': "H' = Scg p' q' sa' wa'"
      and H_eq: "set s' = set sa'"
      "set s' \<union> set w' = set sa' \<union> set wa'"
      by (auto elim!: scg_eqv.cases)

    show ?thesis
    proof (cases "conn q p'")
      case True
 
      have "set s O (set s' \<union> set w')
        \<union> (set s \<union> set w) O set s'
        = set sa O (set sa' \<union> set wa')
        \<union> (set sa \<union> set wa) O set sa'"
        by (simp only: G_eq(2) H_eq(2), simp only: G_eq H_eq)
      then have 1:
        "(set s O set s' \<union> (set s O set w' \<union> set w O set s'))
=        (set sa O set sa' \<union> (set sa O set wa' \<union> set wa O set sa'))"
  by (simp add: Un_ac)

      have 2: "(set s \<union> set w) O (set s' \<union> set w')
        = (set sa \<union> set wa) O (set sa' \<union> set wa')"
        by (simp only: G_eq(2) H_eq(2))

      show ?thesis unfolding scg' Scg G' H'
        apply (rule scg_eqv2)
        apply (simp add: Let_def True)
        apply (rule scg_eqv.intros)
        apply (simp add: 1)
        apply (insert 2, simp add: Un_ac)
        done
      next
      case False
      show ?thesis unfolding scg' Scg G' H'
        by (rule scg_eqv2)
      (auto simp: Let_def False intro: scg_eqv.intros)
    qed
  qed
qed


lemma exp_cong: "scg_eqv G = scg_eqv H 
  \<Longrightarrow> scg_eqv (exp conn G n) = scg_eqv (exp conn H n)"
by (induct n) (auto intro!: comp_cong)

lemma exp_comm: "scg_eqv (scg_comp conn G (exp conn G n))
  = scg_eqv (scg_comp conn (exp conn G n) G)"
proof (induct n)
  case 0 show ?case by simp
next
  case (Suc n)
  show ?case
    apply simp
    apply (unfold comp_assoc[THEN scg_eqv2, symmetric])
    apply (rule comp_cong)
    apply (unfold Suc[symmetric])
    by auto
qed

lemma exp_compose:
  "scg_eqv (scg_comp conn (exp conn G n) (exp conn G m))
  = scg_eqv (exp conn G (Suc (n + m)))"
proof (induct n)
  case 0 show ?case by (simp add: exp_comm)
next
  case (Suc n)
  have "scg_eqv (scg_comp conn (scg_comp conn (exp conn G n) G) (exp conn G m)) 
    = scg_eqv (scg_comp conn (exp conn G n) (scg_comp conn G (exp conn G m)))"
    by (simp add: comp_assoc[THEN scg_eqv2])
  also have "... = scg_eqv (scg_comp conn (exp conn G n) (scg_comp conn (exp conn G m) G))"
    by (rule comp_cong) (auto simp: exp_comm)
  also have "... = scg_eqv (scg_comp conn (scg_comp conn (exp conn G n) (exp conn G m)) G)"
    by (simp add: comp_assoc[THEN scg_eqv2])
  also have  "... = scg_eqv (scg_comp conn (exp conn G (Suc (n + m))) G)"   
    by (rule comp_cong) (auto simp: Suc)
  finally show ?case by simp
qed

primrec strict_edge :: "'ap \<Rightarrow> 'ap \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> bool"
where
  "strict_edge i j Null = True"
| "strict_edge i j (Scg _ _ str _) = ((i,j)\<in>set str)"

primrec weak_edge :: "'ap \<Rightarrow> 'ap \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> bool"
where
  "weak_edge i j Null = True"
| "weak_edge i j (Scg _ _ str wk) = ((i,j)\<in>set wk \<union> set str)"

lemma edge_combine[simp]: 
  "strict_edge i j (combine G H) = (strict_edge i j G \<or> strict_edge i j H)"
  "weak_edge i j (combine G H) = (weak_edge i j G \<or> weak_edge i j H)"
by (induct G H rule: combine.induct) auto

lemma weak_edge_decompose: 
  assumes "scg_comp conn G H \<noteq> Null"
  assumes "weak_edge i k (scg_comp conn G H)"
  obtains j where "weak_edge i j G" "weak_edge j k H"
using assms
by (induct conn G H rule: scg_comp.induct) (auto simp: Let_def split: if_splits)

lemma strict_edge_decompose: 
  assumes "scg_comp conn G H \<noteq> Null"
  assumes "strict_edge i k (scg_comp conn G H)"
  obtains j where "strict_edge i j G" "strict_edge j k H"
  | j where "strict_edge i j G" "weak_edge j k H"
  | j where "weak_edge i j G" "strict_edge j k H"
using assms
by (induct conn G H rule: scg_comp.induct) (auto simp: Let_def split: if_splits)


lemma exp_compose_strict: "strict_edge i j (scg_comp conn (exp conn G n) (exp conn G m))
 = strict_edge i j (exp conn G (Suc (n + m)))"
using exp_compose[THEN scg_eqv1, of conn G n m]
by rule auto 

lemma exp_compose_weak: "weak_edge i j (scg_comp conn (exp conn G n) (exp conn G m))
 = weak_edge i j (exp conn G (Suc (n + m)))"
using exp_compose[THEN scg_eqv1, of conn G n m]
by rule auto 

lemma subsumes_exp_mono:
assumes "subsumes G H"
  shows "subsumes (exp conn G n) (exp conn H n)"
by (induct n) (auto intro: subsumes_comp_mono assms)

lemma combine_subsumes: "subsumes G (combine G H)"
by (induct G H rule: combine.induct) auto

lemma in_situ_subsumes:
  "subsumes G H \<Longrightarrow> in_situ G \<Longrightarrow> in_situ H"
by (induct G H rule: subsumes.induct) auto

lemma sagiv_subsumes: 
assumes sub: "subsumes G H" and G: "sagiv conn G"
shows "sagiv conn H"
proof -
  from G obtain n where 1: "in_situ (exp conn G n)" unfolding sagiv_def ..
  from sub have "subsumes (exp conn G n) (exp conn H n)" 
    by (rule subsumes_exp_mono)
  from this 1 have "in_situ (exp conn H n)" by (rule in_situ_subsumes)
  then show ?thesis unfolding sagiv_def ..
qed

lemma sagiv_step:
  "sagiv conn G \<longleftrightarrow> sagiv conn (combine G (scg_comp conn G G))"
  (is "?A \<longleftrightarrow> ?B")
proof
  assume ?A 
  then show ?B by (rule sagiv_subsumes[OF combine_subsumes])
next
  let ?G' = "combine G (scg_comp conn G G)"
  assume ?B show ?A
  proof (cases ?G')
    case Null 
    then have "G = Null \<or> scg_comp conn G G = Null" by (cases G) (auto simp: Let_def)
    then show ?thesis
    proof
      assume "G = Null" then show ?thesis 
        by (auto simp: sagiv_def)
    next
      assume "scg_comp conn G G = Null"
      then have "in_situ (exp conn G 1)" by auto
      then show ?thesis unfolding sagiv_def ..
    qed
  next
    case (Scg p q str wk)
    then obtain str' wk' where Scg': "G = Scg p q str' wk'" 
      by (cases G) (auto split: if_splits simp: Let_def)
    with Scg have composable: "conn q p" by (auto split: if_splits)
    {
      fix n
      from composable Scg
      have "\<exists>s w. exp conn ?G' n = Scg p q s w" by (induct n) (auto simp: Let_def)
      then have "exp conn ?G' n \<noteq> Null" by auto
    }
    note nonnull = this

    {
      fix i j
      assume "strict_edge i j ?G'"
      from this[simplified]
      have "\<exists>m. strict_edge i j (exp conn G m)"
      proof
        assume "strict_edge i j G" then have "strict_edge i j (exp conn G 0)" by auto
        then show ?thesis ..
      next
        assume "strict_edge i j (scg_comp conn G G)" then have "strict_edge i j (exp conn G 1)" by auto
        then show ?thesis ..
      qed
    }
    note strict_step = this

    {
      fix i j
      assume "weak_edge i j ?G'"
      from this[simplified]
      have "\<exists>m. weak_edge i j (exp conn G m)"
      proof
        assume "weak_edge i j G" then have "weak_edge i j (exp conn G 0)" by auto
        then show ?thesis ..
      next
        assume "weak_edge i j (scg_comp conn G G)" then have "weak_edge i j (exp conn G 1)" by auto
        then show ?thesis ..
      qed
    }
    note weak_step = this


    {
      fix i j n
      have "strict_edge i j (exp conn ?G' n) \<Longrightarrow> \<exists>m. strict_edge i j (exp conn G m)"
       and "weak_edge i j (exp conn ?G' n) \<Longrightarrow> \<exists>m. weak_edge i j (exp conn G m)"
      proof (induct n arbitrary: i j)
        case 0 case 1 then show ?case by (simp add: strict_step)
      next
        case 0 case 2
         then have "weak_edge i j G \<or> weak_edge i j (scg_comp conn G G)" 
          (is "?X \<or> ?Y") by auto
        then show ?case
        proof
          assume ?X then have "weak_edge i j (exp conn G 0)" by auto
          then show ?thesis ..
        next
          assume ?Y then have "weak_edge i j (exp conn G 1)" by auto
          then show ?thesis ..
        qed
      next
        case (Suc n) case (1 i k)
        then have a: "strict_edge i k (scg_comp conn (exp conn ?G' n) ?G')" by simp
        show ?case
        proof (rule strict_edge_decompose[OF nonnull[of "Suc n", simplified] a])
          fix j
          assume 1: "strict_edge i j (exp conn ?G' n)"
             and 2: "strict_edge j k ?G'"
          from Suc(1)[OF 1] strict_step[OF 2]
          obtain m m' 
            where "strict_edge i j (exp conn G m)" "strict_edge j k (exp conn G m')"
            by auto
          then have "strict_edge i k (scg_comp conn (exp conn G m) (exp conn G m'))"
            by (cases "exp conn G m", auto, cases "exp conn G m'", auto simp: Let_def)
          then have "strict_edge i k (exp conn G (Suc (m + m')))" unfolding exp_compose_strict .
          then show "\<exists>m. strict_edge i k (exp conn G m)" ..
        next
          fix j
          assume 1: "strict_edge i j (exp conn ?G' n)"
             and 2: "weak_edge j k ?G'"
          from Suc(1)[OF 1] weak_step[OF 2]
          obtain m m' 
            where "strict_edge i j (exp conn G m)" "weak_edge j k (exp conn G m')"
            by auto
          then have "strict_edge i k (scg_comp conn (exp conn G m) (exp conn G m'))"
            by (cases "exp conn G m", auto, cases "exp conn G m'", auto simp: Let_def)
          then have "strict_edge i k (exp conn G (Suc (m + m')))" unfolding exp_compose_strict .
          then show "\<exists>m. strict_edge i k (exp conn G m)" ..
        next
          fix j
          assume 1: "weak_edge i j (exp conn ?G' n)"
             and 2: "strict_edge j k ?G'"
          from Suc(2)[OF 1] strict_step[OF 2]
          obtain m m' 
            where "weak_edge i j (exp conn G m)" "strict_edge j k (exp conn G m')"
            by auto
          then have "strict_edge i k (scg_comp conn (exp conn G m) (exp conn G m'))"
            apply (cases "exp conn G m", auto)
            apply (cases "exp conn G m'", auto simp: Let_def)
            apply (cases "exp conn G m'", auto simp: Let_def) done
          then have "strict_edge i k (exp conn G (Suc (m + m')))" unfolding exp_compose_strict .
          then show "\<exists>m. strict_edge i k (exp conn G m)" ..
        qed        
      next
        case (Suc n) case (2 i k)
        then have a: "weak_edge i k (scg_comp conn (exp conn ?G' n) ?G')" by simp
        show ?case
        proof (rule weak_edge_decompose[OF nonnull[of "Suc n", simplified] a])
          fix j
          assume 1: "weak_edge i j (exp conn ?G' n)"
             and 2: "weak_edge j k ?G'"
          from Suc(2)[OF 1] weak_step[OF 2]
          obtain m m' 
            where "weak_edge i j (exp conn G m)" "weak_edge j k (exp conn G m')"
            by auto
          then have "weak_edge i k (scg_comp conn (exp conn G m) (exp conn G m'))"
            apply (cases "exp conn G m", auto)
            apply (cases "exp conn G m'", auto simp: Let_def)
            apply (cases "exp conn G m'", auto simp: Let_def) done
          then have "weak_edge i k (exp conn G (Suc (m + m')))" unfolding exp_compose_weak .
          then show "\<exists>m. weak_edge i k (exp conn G m)" ..
        qed        
      qed       
    }
    note r = this(1)
    from \<open>?B\<close> obtain n
      where "in_situ (exp conn ?G' n)"
      unfolding sagiv_def .. 
    with nonnull
    obtain i 
      where "strict_edge i i (exp conn ?G' n)"
      by (cases "exp conn (combine G (scg_comp conn G G)) n") auto
    from r[OF this]
    obtain m where "strict_edge i i (exp conn G m)" ..
    then
    have "in_situ (exp conn G m)"
      by (cases "exp conn G m") auto
    then show "sagiv conn G"
      unfolding sagiv_def ..
  qed
qed

lemma sagiv_code[code]:
 "sagiv conn G =
  (if in_situ G
     then True
     else let GG = scg_comp conn G G
          in if subsumes GG G then False
             else sagiv conn (combine G GG))"
proof cases
 assume G: "in_situ G"
 then have "in_situ (exp conn G 0)" by simp
 then have "sagiv conn G" unfolding sagiv_def ..
 with G show ?thesis by simp
next
 assume nG: "\<not> in_situ G"
 show ?thesis
 proof cases
   assume sub: "subsumes (scg_comp conn G G) G"
   {
     fix n have "subsumes (exp conn G n) G"
     proof (induct n)
       case 0 show ?case by simp
     next
       case (Suc n)
       from this subsumes_refl
       have "subsumes (scg_comp conn (exp conn G n) G) (scg_comp conn G G)"
         by (rule subsumes_comp_mono)
       also have "subsumes (\<dots>) G" by (fact sub)
       finally show ?case by simp
     qed
   }
   from subsumes_in_situ[OF this] and nG
   have "\<not> sagiv conn G" unfolding sagiv_def by auto
   with nG sub show ?thesis by auto
 next
   assume nsub: "\<not> subsumes (scg_comp conn G G) G"
   with nG sagiv_step
   show ?thesis by auto
 qed
qed

subsection \<open>Transition system semantics\<close>

locale sct_semantics =
 fixes S NS :: "'a rel"
 fixes conn :: "'pp :: compare_order \<Rightarrow> 'pp \<Rightarrow> bool"
 assumes wf_S: "SN S"
 assumes SN_compat: "NS O S \<subseteq> S"
begin

abbreviation "trN == (NS \<union> S)^*"
abbreviation "trS == trN O S O trN"

lemma tr_subset: "trS \<subseteq> trN"
proof -
 have "trS \<subseteq> trN O trN O trN"
   by (intro relcomp_mono) auto
 also have "\<dots> \<subseteq> trN" by auto
 finally show ?thesis .
qed

lemma SN_compat': "trN O trS \<subseteq> trS"
  by (simp add: O_assoc[symmetric])

lemma NS_compat': "trS O trN \<subseteq> trS"
  by (simp add: O_assoc)

lemma SS_compat': "trS O trS \<subseteq> trS"
  using tr_subset NS_compat'
  by (blast 7)

lemma NN_compat': "trN O trN \<subseteq> trN"
  by auto

lemma SN_trS: "SN trS"
  using SN_compat wf_S by (rule compatible_SN')

primrec steps :: "('pp, 'ap) scg \<Rightarrow> ('pp \<times> ('ap \<Rightarrow> 'a)) rel"
where
 "steps Null = {}"
| "steps (Scg p q str wk) =
  { ((p, f) , (r, g)) | f g r.
      (\<forall>(x,y)\<in>set str. (f x, g y) \<in> trS)
    \<and> (\<forall>(x,y)\<in>set wk. (f x, g y) \<in> trN) \<and> conn q r }"


lemma steps_subsumes: "subsumes G G' \<Longrightarrow> steps G' \<subseteq> steps G"
using tr_subset
by (induct G G' rule: subsumes.induct) (auto, blast+)

lemma steps_comp:
shows "steps G O steps G' \<subseteq> steps (scg_comp conn G G')"
proof (induct "c::'pp\<Rightarrow>'pp\<Rightarrow>bool" G G' rule: scg_comp.induct)
 case (1 _ p q str wk p' q' str' wk')
 have FalseI: "\<And> P. \<not> P \<Longrightarrow> P \<Longrightarrow> False" by auto
 from 1 show ?case
 proof (rule, simp_all only: split_paired_all)
   fix pa qa f g
   assume "((pa,f), (qa,g))
         \<in> steps (Scg p q str wk) O steps (Scg p' q' str' wk')"
   then obtain r h where
   "((pa,f), (r,h)) \<in> steps (Scg p q str wk)"
   "((r,h), (qa,g)) \<in> steps (Scg p' q' str' wk')"
     by auto
   then show "((pa,f), (qa,g))
         \<in> steps (scg_comp conn (Scg p q str wk) (Scg p' q' str' wk'))"
     apply (auto 1 0 simp: Let_def)
     apply (rule subsetD[OF SS_compat'])
     apply (rule_tac b="h y" in relcompI, force, force)
     apply (rule subsetD[OF NS_compat'])
     apply (rule_tac b="h y" in relcompI, force, force)
     apply (rule subsetD[OF SN_compat'])
     apply (rule_tac b="h y" in relcompI, force, force)
     apply (rule ccontr, rule_tac FalseI[of "(f x, g z) \<in> trN" for x z], force)
     apply (rule subsetD[OF NN_compat'])
     apply (rule_tac b="h y" in relcompI, force, force)
     done
 qed
qed auto

lemma trans_scgs:
 assumes tr: "trans_scgs conn Gs"
 shows "trans (\<Union>G\<in>set Gs. steps G)" (is "trans ?R")
proof (rule transI, simp only: split_paired_all)
 fix p q r f g h
 assume "((p, f), (q, g)) \<in> ?R" "((q, g), (r, h)) \<in> ?R"
 then obtain G H where GH: "G \<in> set Gs" "H \<in> set Gs"
   and "((p, f), (q, g)) \<in> steps G"
   "((q, g), (r, h)) \<in> steps H"
   by auto
 then have comp: "((p, f), (r, h)) \<in> steps (scg_comp conn G H)" using steps_comp by auto
 from tr GH obtain G' where "G' \<in> set Gs"
   and "subsumes G' (scg_comp conn G H)"
   unfolding trans_scgs_def by auto
 with comp have "((p, f), (r, h)) \<in> steps G'" using steps_subsumes by auto
 with \<open>G' \<in> set Gs\<close> show "((p, f), (r, h)) \<in> ?R" by auto
qed

lemma in_situ_SN:
 "in_situ G \<Longrightarrow> SN (steps G)"
proof (induct G)
 case (Scg p q str wk)
 then obtain x where "(x,x) \<in> set str" by auto
 then have subset: "steps (Scg p q str wk) \<subseteq> inv_image trS (\<lambda>(p,f). f x)"
   unfolding inv_image_def by auto
 have "SN (inv_image trS (\<lambda>(p,f). f x))"
   by (intro SN_inv_image SN_trS)
 then show ?case using subset
   by (rule SN_subset)
qed auto

lemma steps_exp: "steps G ^^ Suc n \<subseteq> steps (exp conn G n)"
proof (induct n)
 case (Suc n)
 have "steps G ^^ (Suc (Suc n)) = steps G ^^ (Suc n) O steps G" by simp
 also have "... \<subseteq> steps (exp conn G n) O steps G" by (intro relcomp_mono Suc subset_refl)
 also have "... \<subseteq> steps (scg_comp conn (exp conn G n) G)" by (rule steps_comp)
 also have "... \<subseteq> steps (exp conn G (Suc n))" by simp
 finally show ?case .
qed auto

lemma sagiv_SN: 
  assumes a: "sagiv conn G" 
  shows "SN (steps G)"
using a
unfolding sagiv_def
proof 
 fix n assume "in_situ (exp conn G n)"
 then have "SN (steps (exp conn G n))" by (rule in_situ_SN)
 from this steps_exp
 have "SN (steps G ^^ Suc n)" by (rule SN_subset)
 then show "SN (steps G)" unfolding SN_pow[symmetric] .
qed

text \<open>Version that assumes that the closure is already given\<close>

lemma SCT_correctness:
 fixes R :: "('pp \<times> ('ap :: linorder \<Rightarrow> 'a)) rel"
 assumes abst:  "R \<subseteq> (\<Union>G\<in>set Gs. steps G)"
 assumes trans: "trans_scgs conn Ts"
 assumes super: "subsume (set Ts) (set Gs)"
 assumes good:  "\<forall>G\<in>set Ts. sagiv conn G"
 shows "SN R"
proof -
 from good
 have "\<And>G. G \<in> set Ts \<Longrightarrow> SN (steps G)"
   by (auto dest!: sagiv_SN)
 then have disj: "disj_wf ((\<Union>G\<in>set Ts. steps G)^-1)"
   unfolding disj_wf_def
   apply (rule_tac x = "\<lambda>i. (steps (Ts ! i))^-1" in exI)
   apply (rule_tac x = "length Ts" in exI)
   apply (simp add: SN_iff_wf)
   apply auto
   apply (metis in_set_conv_nth lessThan_iff)
   apply (metis in_set_conv_nth)
   done
 from trans
 have "trans (\<Union>G\<in>set Ts. steps G)"
   by (rule trans_scgs)
 from this and disj
 have SN: "SN (\<Union>G\<in>set Ts. steps G)"
   unfolding SN_iff_wf
   by (auto intro: trans_disj_wf_implies_wf)
 note abst
 also from super have
   "(\<Union>G\<in>set Gs. steps G) \<subseteq> (\<Union>G\<in>set Ts. steps G)"
   by (force simp: subsume_def dest!: steps_subsumes)
 finally 
 show "SN R" by (rule SN_subset[OF SN]) 
qed
end

text \<open>Transitive closure computation\<close>

definition generate_scgs :: "('pp \<Rightarrow> 'pp \<Rightarrow> bool) \<Rightarrow> ('pp, 'ap :: linorder) scg list \<Rightarrow> ('pp, 'ap) scg \<Rightarrow> ('pp,'ap) scg list" 
  where "generate_scgs conn base g \<equiv> filter (\<lambda> g. g \<noteq> Null) (map (scg_comp conn g) base)"

fun pps_of :: "('pp, 'ap) scg \<Rightarrow> 'pp set"
where
  "pps_of Null = {}"
| "pps_of (Scg p q _ _) = {p,q}"
fun aps_of :: "('pp, 'ap) scg \<Rightarrow> 'ap set"
where
  "aps_of Null = {}"
| "aps_of (Scg _ _ str wk) = set (map fst str) \<union> set (map snd str) \<union> set (map fst wk) \<union> set (map snd wk)"

lemma finite_pps[simp]: "finite (pps_of G)" by (cases G) auto
lemma finite_aps[simp]: "finite (aps_of G)" by (cases G) auto

lemma image_fst_snd: "(a,b)\<in>S \<Longrightarrow> a \<in> fst ` S" "(a,b)\<in>S \<Longrightarrow> b \<in> snd ` S"
by force+

lemma pps_of_comp: "pps_of (scg_comp conn G H) \<subseteq> pps_of G \<union> pps_of H"
by (induct conn G H rule: scg_comp.induct) (auto simp: Let_def)
lemma aps_of_comp: "aps_of (scg_comp conn G H) \<subseteq> aps_of G \<union> aps_of H"
by (induct conn G H rule: scg_comp.induct) (auto simp: image_fst_snd Let_def)

definition graph_bound where
  "graph_bound T =
  (let P = (\<Union>H\<in>T. pps_of H); A = (\<Union>H\<in>T. aps_of H)
   in (\<lambda>(p,q,str,wk). Scg p q str wk) ` (P \<times> P \<times> {xs . distinct xs \<and> set xs \<subseteq> A \<times> A} \<times> {xs . distinct xs \<and> set xs \<subseteq> A \<times> A})) \<union> {Null}"

lemma finite_distinct_subset: "finite X \<Longrightarrow> finite {xs. distinct xs \<and> set xs \<subseteq> X}" 
  using finite_subset_distinct[of X]
  by (metis (no_types, lifting) Collect_cong)

lemma finite_graph_bound[intro]: "finite G \<Longrightarrow> finite (graph_bound G)"
  unfolding graph_bound_def Let_def 
  by (intro finite_UnI finite_imageI,
    intro finite_SigmaI finite_distinct_subset, auto)

lemma graph_bound_subsetI:
"(\<Union>G\<in>S. pps_of G) \<subseteq> (\<Union>G\<in>T. pps_of G)
\<Longrightarrow> (\<Union>G\<in>S. aps_of G) \<subseteq> (\<Union>G\<in>T. aps_of G)
\<Longrightarrow> graph_bound S \<subseteq> graph_bound T"
unfolding graph_bound_def Let_def 
by (intro Un_mono image_mono, auto)

lemma graph_bound_mono: "Gs \<subseteq> Hs \<Longrightarrow> graph_bound Gs \<subseteq> graph_bound Hs"
by (rule graph_bound_subsetI) auto

lemma graph_boundI:
  assumes G: "G = Scg p q str wk"
  and disj: "distinct str" "distinct wk"
  shows "G \<in> graph_bound {G}"
  unfolding graph_bound_def assms G Let_def
  using disj
  by (intro UnI1 image_eqI[of _ _ "(p,q,str,wk)"], 
    auto simp: image_fst_snd)

lemma graph_bound_scg_comp: 
  assumes GT: "G \<in> graph_bound T \<union> T"
  and BT: "B \<in> T"
  shows "scg_comp conn G B \<in> graph_bound T"
proof -
  let ?G = "scg_comp conn G B"
  show ?thesis 
  proof (cases "?G = Null")
    case True
    then show ?thesis unfolding graph_bound_def by auto
  next
    case False
    then obtain p1 q1 s1 w1 where G: "G = Scg p1 q1 s1 w1" by (cases G, auto)
    from False G obtain p2 q2 s2 w2 where B: "B = Scg p2 q2 s2 w2" by (cases B, auto)
    from False G B have c: "conn q1 p2 = True" by (cases "conn q1 p2", auto)
    from B BT have q: "q2 \<in> \<Union> {pps_of B | B. B \<in> T}" by auto
    from G GT have p: "p1 \<in> \<Union> {pps_of B | B. B \<in> T}" 
      unfolding graph_bound_def by auto
    let ?A = "\<Union> (aps_of ` T)"
    let ?D = "{xs. distinct xs \<and> set xs \<subseteq> ?A \<times> ?A}"
    let ?s = "(remdups_sort (comp s1 s2 @ comp s1 w2 @ comp w1 s2))"
    let ?w = "(subtract_list_sorted (remdups_sort (comp w1 w2)) ?s)"
    have GG: "?G = Scg p1 q2 ?s ?w"
      unfolding G B using c by (simp add: Let_def)
    have mem: "?G \<in> graph_bound {?G}"
      by (rule graph_boundI[OF GG], auto)
    let ?all = "set s1 \<union> set s2 \<union> set w1 \<union> set w2"
    show ?thesis 
    proof (rule set_mp[OF graph_bound_subsetI mem])
      show "(\<Union> G \<in> {?G}. pps_of G) \<subseteq> (\<Union>G\<in>T. pps_of G)" unfolding GG using p q by auto
    next
      have "(\<Union> G \<in> {?G}. aps_of G) = aps_of ?G" unfolding GG by simp
      also have "... \<subseteq> fst ` ?all \<union> snd ` ?all" unfolding GG 
        by (auto simp add: image_fst_snd)
      also have "... \<subseteq> (aps_of B \<union> aps_of G)" unfolding B G by auto
      also have "... \<subseteq> (\<Union>G \<in> T. aps_of G) \<union> aps_of G" using BT by auto
      also have "... \<subseteq> (\<Union>G \<in> T. aps_of G)" using GT
      proof
        assume "G \<in> T" then show ?thesis by auto
      next
        assume GT: "G \<in> graph_bound T"
        from GT 
        have "(s1,w1) \<in> ?D \<times> ?D" using GT 
          unfolding G graph_bound_def Let_def by auto
        then have "aps_of G \<subseteq> (\<Union>G \<in> T. aps_of G)" unfolding G aps_of.simps
          by (auto simp: image_fst_snd, force+)
        then show ?thesis by auto
      qed
      finally show "(\<Union> G \<in> {?G}. aps_of G) \<subseteq> (\<Union> G \<in> T. aps_of G)" .
    qed
  qed
qed

lemma finite_generate_scgs: "finite {g'. (g,g') \<in> {(a,b). b \<in> set (generate_scgs conn Gs a)}^*}" (is "finite ?S")
proof -
  let ?G = "graph_bound (insert g (set Gs)) \<union> (insert g (set Gs))"
  have fin: "finite ?G" by auto
  show ?thesis
  proof (rule finite_subset[OF _ fin], rule)
    fix g'
    assume "g' \<in> ?S"
    then have "(g,g') \<in> {(a,b). b \<in> set (generate_scgs conn Gs a)}^*" by auto
    then show "g' \<in> ?G"
    proof (induct rule: rtrancl_induct)
      case base show ?case by simp
    next
      case (step g1 g2)
      from step(2)[unfolded generate_scgs_def] 
      obtain b where g2: "g2 = scg_comp conn g1 b" and b: "b \<in> insert g (set Gs)" by auto
      from graph_bound_scg_comp[OF step(3) b] 
      show ?case unfolding g2 by auto
    qed
  qed
qed        

derive compare_order scg

definition check_SCT :: "('pp :: compare_order \<Rightarrow> 'pp \<Rightarrow> bool) \<Rightarrow> ('pp, 'ap :: compare_order) scg list \<Rightarrow> bool"
where
 "check_SCT conn Gs =
     rs.ball (mk_rtrancl_set (generate_scgs conn Gs) Gs) (sagiv conn)"

lemma scg_eqv_subsumes: "scg_eqv G = scg_eqv H \<Longrightarrow> subsumes I G = subsumes I H"
  unfolding scg_eqv[symmetric]
  by (induct rule: scg_eqv.induct, auto, (cases I, auto)+)


lemma (in sct_semantics) SCT_correctness2:
 fixes R :: "('pp \<times> ('ap :: compare_order \<Rightarrow> 'a)) rel"
 assumes abst:  "R \<subseteq> (\<Union>G\<in>set Gs. steps G)"
 assumes check: "check_SCT conn Gs"
 shows "SN R"
proof -
  let ?r = "generate_scgs conn Gs"
  let ?R = "{(a,b). b \<in> set (?r a)}"
  let ?S = "mk_rtrancl_set ?r Gs"
  note d = generate_scgs_def
  note sub_refl = subsumes_refl
  interpret relation_subsumption_set ?r
  proof
    fix g
    show "finite {g'. (g,g') \<in> {(a,b). b \<in> set (?r a)}^*}" by (rule finite_generate_scgs) 
  qed  
  have S: "rs.\<alpha> ?S = mk_rtrancl Gs" unfolding mk_rtrancl_set ..
  define S where "S = rs.to_list ?S"
  have SS: "set S = rs.\<alpha> ?S" unfolding S_def by (auto simp: rs.correct)
  note abst
  moreover
  have "trans_scgs conn S" 
    unfolding trans_scgs_def
    unfolding S SS Let_def 
    unfolding mk_rtrancl_no_subsumption[OF refl]
  proof (clarify)
    fix G BG H BH
    assume BG: "BG \<in> set Gs" and BGG: "(BG,G) \<in> ?R^*"
    assume BH: "BH \<in> set Gs" and BHH: "(BH,H) \<in> ?R^*"
    let ?C = "scg_comp conn"
    from BHH 
    have "\<exists> I. scg_eqv (?C G H) = scg_eqv I \<and> ((BG,I) \<in> ?R^* \<or> I = Null)"
    proof (induct rule: rtrancl_induct)
      case base     
      have "BH \<in> set Gs \<Longrightarrow> (BG,?C G BH) \<in> ?R^* \<or> ?C G BH = Null" 
        using BGG
      proof (induct arbitrary: BH rule: rtrancl_induct)
        case base
        then show ?case using BG unfolding d by auto
      next
        case (step G H)
        from step(2) have GH: "H \<in> set (?r G)" by simp
        then obtain B where B: "B \<in> set Gs" and H: "H = ?C G B" and N: "H \<noteq> Null" unfolding d by auto
        from step(1) have BGG: "(BG, G) \<in> ?R^*" .
        from step(3)[OF B] have H: "(BG,H) \<in> ?R^* \<or> H = Null" unfolding H .
        show ?case
        proof (cases "?C H BH = Null")
          case True
          then show ?thesis by simp
        next
          case False
          then have "(H,?C H BH) \<in> ?R" using step(4) unfolding d by auto
          moreover from False H have H: "(BG,H) \<in> ?R^*" by (cases H, auto)
          ultimately have steps: "(BG,?C H BH) \<in> ?R^* O ?R" by auto
          have "(BG, ?C H BH) \<in> ?R^*"
            by (rule set_mp[OF _ steps], regexp)
          then show ?thesis by auto
        qed
      qed
      from this[OF BH] 
      show ?case by auto
    next
      case (step H I)
      from step(3) obtain J where eq: "scg_eqv (?C G H) = scg_eqv J"
        and BGI: "(BG, J) \<in> ?R^* \<or> J = Null" by auto
      from step(2) obtain B where B: "B \<in> set Gs" and 
        I: "I = ?C H B" and N: "I \<noteq> Null" unfolding d by auto
      have assoc: "scg_eqv (scg_comp conn G (scg_comp conn G1 H)) = scg_eqv (scg_comp conn (scg_comp conn G G1) H)"
        for G1 H 
        by (rule sym, subst scg_eqv[symmetric], rule comp_assoc)
      note J = comp_cong[OF eq refl, of conn B] 
      show ?case unfolding I J assoc
      proof (cases "?C J B = Null")
        case True
        then show "\<exists> I. scg_eqv (?C J B) = scg_eqv I \<and> ((BG,I) \<in> ?R^* \<or> I = Null)"
          by auto
      next
        case False
        then have R: "(J, ?C J B) \<in> ?R" using B unfolding d by auto
        from False have J: "J \<noteq> Null" by auto
        with BGI R
        have steps: "(BG, ?C J B) \<in> ?R^* O ?R" by auto
        have "(BG, ?C J B) \<in> ?R^*"
          by (rule set_mp[OF _ steps], regexp)
        then show "\<exists> I. scg_eqv (?C J B) = scg_eqv I \<and> ((BG,I) \<in> ?R^* \<or> I = Null)"
          by auto
      qed
    qed
    then obtain I where eq: "scg_eqv (?C G H) = scg_eqv I"
      and BGI: "(BG,I) \<in> ?R^* \<or> I = Null" by auto
    from scg_eqv_subsumes[OF eq] 
    have eq: "\<And> J. subsumes J (?C G H) = subsumes J I" by simp
    from BGI BG have "I \<in> ?R^* `` set Gs \<or> I = Null" by auto
    then show "\<exists> J \<in> ?R^* `` set Gs. subsumes J (?C G H)" 
    proof 
      assume "I \<in> ?R^* `` set Gs"
      then show ?thesis unfolding eq using sub_refl by blast
    next
      assume "I = Null"
      then show ?thesis using BG unfolding eq by auto
    qed
  qed
  moreover have "subsume (set S) (set Gs)" 
    unfolding subsume_def S SS
    unfolding mk_rtrancl_no_subsumption[OF refl]
  proof (clarify)
    fix G
    assume G: "G \<in> set Gs" 
    then have "G \<in> ?R^* `` set Gs" by auto
    then show "\<exists> H \<in> ?R^* `` set Gs. subsumes H G" 
      using sub_refl[of G] by blast
  qed
  moreover from check[unfolded check_SCT_def Let_def]
  have "\<forall>G\<in>set S. sagiv conn G"  by (simp add: rs.correct S SS)
  ultimately show "SN R"
    by (rule SCT_correctness)
qed


end
