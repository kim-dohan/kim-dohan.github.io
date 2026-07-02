(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Embedding_Trs
imports
  First_Order_Rewriting.Trs
  "HOL-Library.Sublist"
begin

definition "Emb F P =
  {(Fun f ts, t) | f ts t. (f, length ts) \<in> F \<and> t \<in> set ts} \<union>
  {(Fun f ss, Fun g ts) | f ss g ts.
    P (f, length ss) (g, length ts) \<and> (f, length ss) \<in> F \<and> (g, length ts) \<in> F \<and> subseq ts ss}"

definition "emb F P = (rstep (Emb F P))\<^sup>+"
definition "embeq F P = (rstep (Emb F P))\<^sup>*"

lemma Emb_arg:
  assumes "(f, length ts) \<in> F" and "t \<in> set ts"
  shows "(Fun f ts, t) \<in> Emb F P"
  using assms by (auto simp: Emb_def)

lemma Emb_subseq:
  assumes "P (f, length ss) (g, length ts)"
    and "(f, length ss) \<in> F" and "(g, length ts) \<in> F"
    and "subseq ts ss"
  shows "(Fun f ss, Fun g ts) \<in> Emb F P"
  using assms by (auto simp: Emb_def)

lemma embeq_arg:
  assumes "(f, length ts) \<in> F" and "t \<in> set ts"
  shows "(Fun f ts, t) \<in> embeq F P"
  using Emb_arg [OF assms, of P] by (auto simp: embeq_def)

lemma embeq_subseq:
  assumes "P (f, length ss) (g, length ts)"
    and "(f, length ss) \<in> F" and "(g, length ts) \<in> F"
    and "subseq ts ss"
  shows "(Fun f ss, Fun g ts) \<in> embeq F P"
  using Emb_subseq [of P, OF assms] by (auto simp: embeq_def)

lemma embeq_trans:
  "(s, t) \<in> embeq F P \<Longrightarrow> (t, u) \<in> embeq F P \<Longrightarrow> (s, u) \<in> embeq F P"
  by (auto simp: embeq_def)

inductive pairwise for P
where
  Nil [simp, intro]: "pairwise P [] []" |
  Cons [intro]: "P x y \<Longrightarrow> pairwise P xs ys \<Longrightarrow> pairwise P (x # xs) (y # ys)"

lemma pairwise_refl:
  "pairwise P\<^sup>=\<^sup>= xs xs"
  by (induct xs) auto

lemma list_emb_subseq_left:
  assumes "list_emb P xs zs"
  obtains ys where "subseq xs ys" and "pairwise P\<^sup>=\<^sup>= ys zs"
  using assms and pairwise_refl by (induct) (auto)

lemma list_emb_subseq_right:
  assumes "list_emb P xs zs"
  obtains ys where "pairwise P\<^sup>=\<^sup>= xs ys" and "subseq ys zs"
  using assms by (induct) auto

lemma pairwiseD:
  assumes "pairwise P xs ys"
  shows "length xs = length ys \<and> (\<forall>i < length xs. P (xs ! i) (ys ! i))"
  using assms by (induct) (auto simp: nth_Cons split: nat.splits)

lemma list_emb_conjunct2:
  assumes "list_emb (\<lambda>x y. P x y \<and> Q x y) xs ys"
  shows "list_emb Q xs ys"
  using assms by (induct) auto

lemma pairwise_rsteps:
  assumes "pairwise (\<lambda>s t. (s, t) \<in> (rstep R)\<^sup>*) ss ts"
  shows "(Fun f ss, Fun f ts) \<in> (rstep R)\<^sup>*"
proof (rule args_rsteps_imp_rsteps)
  show "length ss = length ts"
    and "\<forall>i < length ss. (ss ! i, ts ! i) \<in> (rstep R)\<^sup>*"
    using pairwiseD [OF assms] by auto
qed

lemma pairwise_length:
  assumes "pairwise P xs ys"
  shows "length xs = length ys"
  using assms by (induct) simp_all

lemma pairwise_embeq:
  assumes "pairwise (\<lambda>s t. (t, s) \<in> embeq F P)\<^sup>=\<^sup>= ss ts"
  shows "(Fun f ts, Fun f ss) \<in> embeq F P"
proof (unfold embeq_def, rule args_rsteps_imp_rsteps)
  show "length ts = length ss"
    and "\<forall>i < length ts. (ts ! i, ss ! i) \<in> (rstep (Emb F P))\<^sup>*"
    using pairwiseD [OF assms] by (auto simp: embeq_def)
qed

lemma emb_reflcl_embeq [simp]:
  "(emb F P)\<^sup>= = embeq F P"
  by (auto simp: embeq_def emb_def)

lemma Emb_cases [consumes 1, case_names arg subseq, cases set: Emb]:
  assumes "(s, t) \<in> Emb F P"
    and "\<And>f ts. \<lbrakk>(f, length ts) \<in> F; t \<in> set ts; s = Fun f ts\<rbrakk> \<Longrightarrow> Q"
    and "\<And>f ss g ts. \<lbrakk>P (f, length ss) (g, length ts); (f, length ss) \<in> F; (g, length ts) \<in> F;
      subseq ts ss; s = Fun f ss; t = Fun g ts\<rbrakk> \<Longrightarrow> Q"
  shows Q
  using assms by (auto simp: Emb_def)

lemma contains_Emb:
  assumes "\<And>t f ts. t \<in> set ts \<Longrightarrow> (Fun f ts, t) \<in> R"
    and "\<And>f g ss ts. \<lbrakk>P (f, length ss) (g, length ts); subseq ts ss\<rbrakk> \<Longrightarrow> (Fun f ss, Fun g ts) \<in> R"
    and *: "(s, t) \<in> Emb F P"
  shows "(s, t) \<in> R"
  using * and assms by (cases) auto

lemma emb_subsetI:
  fixes R :: "('f, 'v) term rel"
  assumes trans: "\<And>s t u. (s, t) \<in> R \<Longrightarrow> (t, u) \<in> R \<Longrightarrow> (s, u) \<in> R"
    and ctxt: "\<And>C s t. (s, t) \<in> R \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> R"
    and subst: "\<And>\<sigma> s t. (s, t) \<in> R \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> R"
    and *: "\<And>t f ts. t \<in> set ts \<Longrightarrow> (Fun f ts, t) \<in> R"
      "\<And>f g ss ts. \<lbrakk>P (f, length ss) (g, length ts); subseq ts ss\<rbrakk> \<Longrightarrow> (Fun f ss, Fun g ts) \<in> R"
  shows "emb F P \<subseteq> R"
proof
  { fix s t :: "('f, 'v) term"
    assume "(s, t) \<in> rstep (Emb F P)"
    then have "(s, t) \<in> R"
    proof (induct)
      case (IH C \<sigma> l r)
      with contains_Emb [OF *, of P]
        have "(l, r) \<in> R" by blast
      then show ?case by (auto dest: subst ctxt)
   qed }
  note * = this
  fix s t :: "('f, 'v) term"
  assume "(s, t) \<in> emb F P"
  then show "(s, t) \<in> R"
    unfolding emb_def by (induct s t) (auto dest: * trans)
qed

end

