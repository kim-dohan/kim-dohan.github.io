(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Ground_Context
  imports 
    First_Order_Terms.Term_More
begin

no_notation Subterm_and_Context.Hole ("\<box>")

subsection \<open>Ground Contexts\<close>

text \<open>Ground contexts are terms containing arbitrary occurrences of holes
instead of variables.\<close>

(* If 'v is dropped we get a problem with equiv_class below. *)
datatype ('f,'v) gctxt = 
  GCHole ("\<box>")
| GCFun 'f "('f, 'v) gctxt list"

fun equiv_class :: "('f, 'v) gctxt \<Rightarrow> ('f, 'v) terms" ("[_]") where
  "[\<box>] = UNIV"
| "[GCFun f Cs] = {Fun f ts | ts. length ts = length Cs \<and> (\<forall>i<length Cs. (ts ! i) \<in> [Cs ! i])}"

lemma equiv_class_GCFunE:
  assumes "t \<in> [GCFun f Cs]" obtains ts
  where "t = Fun f ts" and "length ts = length Cs" and "\<forall>i<length Cs. (ts ! i) \<in> [Cs ! i]"
  using assms by force

lemma equiv_class_nonempty: "\<exists>t. t \<in> [C]"
proof (induct C)
  case (GCFun f Cs)
  then have "\<forall>i<length Cs. \<exists>t. t \<in> [Cs ! i]" by simp
  with bchoice[of "{0..<length Cs}" "\<lambda>i t. t \<in> [Cs ! i]"]
    obtain g where 1: "\<forall>i<length Cs. g i \<in> [Cs ! i]" by (auto simp: all_nat_less_eq)
  let ?ts = "map g [0..<length Cs]"
  have "length ?ts = length Cs" by simp
  moreover have "\<forall>i<length Cs. (?ts ! i) \<in> [Cs ! i]" by (simp add: 1)
  ultimately show ?case unfolding equiv_class.simps by best
qed simp

lemma equiv_class_GCFun_subset:
  assumes "([GCFun f Cs]::('f, 'v) terms) \<subseteq> [GCFun g Ds]" (is "?T \<subseteq> ?S")
  shows "f = g"
    and "length Cs = length Ds"
    and "\<forall>i<length Cs. ([Cs ! i]::('f, 'v) terms) \<subseteq> [Ds ! i]"
    (is "\<forall>i<length Cs. ?Cs i \<subseteq> ?Ds i")
proof -
  obtain ss and ts where 1: "Fun f ss \<in> ?T" and 2:"Fun g ts \<in> ?S"
    using equiv_class_nonempty[of "GCFun f Cs"]
      and equiv_class_nonempty[of "GCFun g Ds"] by auto
  show f: "f = g" by (rule ccontr) (insert 1 2 assms, auto)
  from equiv_class_GCFunE[OF 1] have len1: "length ss = length Cs"
    and in1: "\<forall>i<length Cs. ss ! i \<in> ?Cs i" by auto
  from equiv_class_GCFunE[OF 2] have len2: "length ts = length Ds"
    and in2: "\<forall>i<length Ds. ts ! i \<in> ?Ds i" by auto
  show len: "length Cs = length Ds"
  proof -
    from equiv_class_GCFunE 
    have "\<forall>t \<in> [GCFun g Ds]. num_args t = length Ds" by auto
    with assms(1) have "\<And> t. t \<in> [GCFun f Cs] \<Longrightarrow> num_args t = length Ds" by auto
    from this[OF 1] len1 len2 show ?thesis by simp
  qed
  show "\<forall>i<length Cs. ?Cs i \<subseteq> ?Ds i"
  proof (intro allI impI)
    fix i
    assume i: "i < length Cs"
    {
      fix t
      assume "t \<in> ?Cs i" and "t \<notin> ?Ds i"
      then have notin: "\<forall>ts. length ts = length Ds \<and> ts ! i = t \<longrightarrow> ts ! i \<notin> ?Ds i" by simp
      from equiv_class_nonempty have "\<forall>i<length Cs. \<exists>t. t \<in> ?Cs i" by force
      from Ex_list_of_length_P[OF this]
        obtain ts where 1: "length ts = length Cs" and 2: "\<forall>i<length Cs. (ts ! i) \<in> ?Cs i"
        by auto
      let ?ts = "ts[i := t]"
      from 1 have 3: "length ?ts = length Cs" by simp
      have 4: "\<forall>i<length Cs. (?ts ! i) \<in> ?Cs i"
      proof (intro allI impI)
        fix j assume j: "j < length Cs"
        show "?ts ! j \<in> ?Cs j"
          using i 1 2 j \<open>t \<in> ?Cs i\<close> by (cases "i = j") simp_all
      qed
      from 3 and 4 have inT: "Fun f ?ts \<in> ?T" by simp
      from notin[THEN spec[of _ "?ts"]] and 3[unfolded len] and i[unfolded len]
        have "?ts ! i \<notin> ?Ds i" by simp
      then have "Fun f ?ts \<notin> ?S" using i[unfolded len] by (auto simp: f)
      with inT and assms have False by blast
    }
    then show "?Cs i \<subseteq> ?Ds i" by blast
  qed
qed

lemma equiv_class_GCFun_eq:
  assumes "([GCFun f Cs]::('f, 'v) terms) = [GCFun g Ds]" (is "?T = ?S")
  shows "f = g" (is ?A)
    and "length Cs = length Ds" (is ?B)
    and "\<forall>i<length Cs. ([Cs ! i]::('f, 'v) terms) = [Ds ! i]" (is ?C)
proof -
  from assms have 1: "?T \<subseteq> ?S" and 2: "?S \<subseteq> ?T" by auto
  from equiv_class_GCFun_subset[OF 1] equiv_class_GCFun_subset[OF 2]
  show ?A and ?B and ?C by auto
qed

text \<open>
Equality of two equiv_classes is the same as syntactic equality of ground contexts.
\<close>
lemma equiv_class_eq_eq_conv:
  shows "([C]::('f, 'v) terms) = [D] \<longleftrightarrow> C = D"
    (is "?T = ?S \<longleftrightarrow> _")
proof
  assume "C = D" then show "?T = ?S" by simp
next
  assume "?T = ?S"
  then show "C = D"
  proof (induct C arbitrary: D)
    case GCHole then show ?case by (cases D) (force)+
  next
    case (GCFun f Cs)
    note IH = this
    then show ?case
    proof (induct D)
      case GCHole then show ?case by force
    next
      case (GCFun g Ds)
      let ?Cs = "\<lambda>i. [Cs ! i]::('f, 'v) terms"
      let ?Ds = "\<lambda>i. [Ds ! i]::('f, 'v) terms"     
      from equiv_class_GCFun_eq[OF GCFun(3)]
        have f: "f = g" and len: "length Cs = length Ds" and "\<forall>i<length Cs. ?Cs i = ?Ds i"
        by simp_all
      from GCFun(2) and this(3) have "\<forall>i<length Cs. Cs ! i = Ds ! i" by force
      with len have "Cs = Ds" by (metis nth_equalityI)
      with f show ?case by simp
    qed
  qed
qed

lemma equiv_class_mono:
  assumes "[s] \<subseteq> [t]"
  shows "[GCFun f (bef @ s # aft)] \<subseteq> [GCFun f (bef @ t # aft)]"
    (is "[GCFun f ?bsa] \<subseteq> [GCFun f ?bta]")
proof -
  {
    fix i u
    assume i: "i < Suc (length bef + length aft)" (is "i < ?n")
    assume elem: "u \<in> [?bsa ! i]"
    from i have "i < length bef \<or> i = length bef \<or> (\<exists> k. i = Suc (length bef) + k \<and> k < length aft)" (is "?one \<or> ?two \<or> ?three") by arith
    then have "u \<in> [?bta ! i]" 
    proof 
      assume ?one
      then have "?bta ! i = ?bsa ! i" by (auto simp: nth_append)
      then show ?thesis using elem by auto 
    next
      assume "?two \<or> ?three"
      then show ?thesis
      proof
	assume ?two
	then have "?bsa ! i = s \<and> ?bta ! i = t" by (auto simp: nth_append)
	with assms elem show ?thesis by auto
      next
	assume ?three
	from this obtain k where "i = Suc (length bef) + k \<and> k < length aft" by auto
	then have "?bta ! i = ?bsa ! i" by (auto simp: nth_append)
	with elem show ?thesis by auto	
      qed
    qed
  }
  then show ?thesis by auto
qed


subsection \<open>Ground Context Matching\<close>

context
begin

qualified definition match :: "('f, 'v) gctxt \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "match h t \<longleftrightarrow> (\<exists>\<sigma>. t \<cdot> \<sigma> \<in> [h])"


qualified definition "unifiable s t \<longleftrightarrow> [s] \<inter> [t] \<noteq> {}"

fun pos_gctxt :: "('f,'v)gctxt \<Rightarrow> pos set" where
  "pos_gctxt \<box> = {[]}"
| "pos_gctxt (GCFun f Cs) = {[]} \<union> \<Union> ((\<lambda> (C,i). (\<lambda> p. i # p) ` pos_gctxt C) ` set (zip Cs [0..< length Cs]))"

lemma pos_gctxt_simps: 
  "pos_gctxt \<box> = {[]}" 
  "pos_gctxt (GCFun f Cs) = {[]} \<union> { i # p | i p. i < length Cs \<and> p \<in> pos_gctxt (Cs ! i)}"
  by (auto simp: set_zip)

declare pos_gctxt.simps[simp del]
declare pos_gctxt_simps[simp]

lemma pos_gctxt_epsilon[simp]: "[] \<in> pos_gctxt C" by (cases C, auto)

lemma pos_gctxt_mono:  "[C] \<subseteq> [D] \<Longrightarrow> pos_gctxt C \<supseteq> pos_gctxt D"
proof (induct D arbitrary: C)
  case (GCFun f Ds C) note IH = this
  show ?case
  proof (cases C)
    case GCHole
    from IH(2)[unfolded this] show ?thesis by auto
  next
    case (GCFun g Cs)
    note IH = IH[unfolded this]
    from equiv_class_GCFun_subset[OF IH(2)]
    have id: "g = f" and len: "length Cs = length Ds"
      and rec: "\<And> i. i < length Ds \<Longrightarrow> [Cs ! i] \<subseteq> [Ds ! i]" by auto
    show ?thesis unfolding GCFun
    proof 
      fix p
      assume mem: "p \<in> pos_gctxt (GCFun f Ds)"
      then show "p \<in> pos_gctxt (GCFun g Cs)"
      proof (cases p)
        case (Cons i q) note p = this
        from mem[unfolded p] have i: "i < length Ds" and q: "q \<in> pos_gctxt (Ds ! i)" by auto
        from equiv_class_nonempty[of "GCFun g Cs"] obtain t where t: "t \<in> [GCFun g Cs]" by blast
        from len i have Di: "Ds ! i \<in> set Ds" by auto
        have "pos_gctxt (Cs ! i) \<supseteq> pos_gctxt (Ds ! i)"
          by (rule IH(1)[OF Di rec[OF i]])
        with q i show ?thesis by (auto simp: len p)
      qed simp
    qed 
  qed
qed simp
end

(* reestablish "default" setup *)
no_notation Ground_Context.GCHole ("\<box>")
no_notation Ground_Context.equiv_class ("[_]")
notation Subterm_and_Context.Hole ("\<box>")

end
