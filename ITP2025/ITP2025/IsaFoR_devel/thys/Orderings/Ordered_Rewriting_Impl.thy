(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2016, 2018)
License: LGPL (see file COPYING.LESSER)
*)
theory Ordered_Rewriting_Impl
  imports
    Ordered_Rewriting
    First_Order_Rewriting.Trs_Impl
begin

fun root_ordstep_list
  where
    "root_ordstep_list c ord ((l, r) # R) t =
      (case match t l of
        Some \<sigma> \<Rightarrow>
          let V = vars_term l in
          let s = r \<cdot> (\<lambda>x. if x \<in> V then \<sigma> x else Fun c []) in
          if ord t s then s # root_ordstep_list c ord R t
          else root_ordstep_list c ord R t
      | None \<Rightarrow> root_ordstep_list c ord R t)"
  | "root_ordstep_list c ord [] t = []"

lemma ext_subst_the_match [simp]:
  "ext_subst (the (match (t \<cdot> \<sigma>) t)) t c = ext_subst \<sigma> t c"
  apply (intro ext)
  apply (auto simp: ext_subst_def)
  by (metis match_complete' option.sel)

lemma root_ordstep_list [simp]:
  "t \<in> set (root_ordstep_list c ord R s) \<longleftrightarrow>
    (\<exists>(l, r) \<in> set R. \<exists>\<sigma>. match s l = Some \<sigma> \<and> ord s t \<and> s = l \<cdot> \<sigma> \<and>
      t = r \<cdot> ext_subst \<sigma> l c)"
  apply (induct c\<equiv>c ord\<equiv>ord R s arbitrary: t rule: root_ordstep_list.induct)
   apply (auto simp: Let_def ext_subst_def [abs_def] dest: match_matches split: option.splits if_splits)
  apply auto
  done

lemma set_root_ordstep_list:
  "set (root_ordstep_list c ord R s) =
    {r \<cdot> ext_subst \<sigma> l c | l r \<sigma>. (l, r) \<in> set R \<and>
      match s l = Some \<sigma> \<and> ord s (r \<cdot> ext_subst \<sigma> l c) \<and> s = l \<cdot> \<sigma>}"
by fastforce

definition "ordstep_list c ord R t = concat (map (\<lambda>p.
  map (replace_at t p) (root_ordstep_list c ord R (t |_ p))) (poss_list t))"

lemma ordstep_list_mordstep_conv [simp]:
  "t \<in> set (ordstep_list c ord R s) \<longleftrightarrow>
    (s, t) \<in> mordstep c {(x, y). ord x y} (set R)" (is "_ \<in> ?L \<longleftrightarrow> _ \<in> ?R")
proof
  assume "t \<in> ?L"
  then obtain p l r \<sigma> where "(l, r) \<in> set R" and "p \<in> poss s"
    and "match (s|_ p) l = Some \<sigma>" and "s |_ p = l \<cdot> \<sigma>" and "ord (s |_ p) (r \<cdot> ext_subst \<sigma> l c)"
    and "t = (ctxt_of_pos_term p s)\<langle>r \<cdot> ext_subst \<sigma> l c\<rangle>"
    by (auto simp: ordstep_list_def)
  with mordstep.intros [OF _ _ _ _ ext_subst, of l r "set R" \<sigma> c "{(x, y). ord x y}" s "ctxt_of_pos_term p s" t]
  show "(s, t) \<in> ?R"
    by (auto simp: subst_ext_subst' replace_at_ident)
next
  assume "(s, t) \<in> ?R"
  then obtain l r C \<sigma> where "(l, r) \<in> set R" and "ord (l \<cdot> \<sigma>) (r \<cdot> \<sigma>)"
    and "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and "\<forall>x \<in> vars_term r - vars_term l. \<sigma> x = Fun c []"
    by (cases) auto
  then show "t \<in> ?L"
    using match_complete' [of l \<sigma> "l \<cdot> \<sigma>"]
    apply (auto simp: ordstep_list_def)
    apply (intro bexI [where x = "hole_pos C"])
     apply (auto simp: inj_image_mem_iff [OF inj_ctxt_apply_term])
    apply (intro bexI [where x = "(l, r)"])
     apply (auto simp: term_subst_eq_conv ext_subst_def)
    done
qed

lemma dom_match_term_list:
  "dom m \<subseteq> V \<Longrightarrow> (\<Union>(set (map (vars_term \<circ> fst) ts))) \<subseteq> V \<Longrightarrow>
    match_term_list ts m = Some m' \<Longrightarrow> dom m' \<subseteq> V"
  apply (induct ts m arbitrary: m' rule: match_term_list.induct)
     apply (auto split: if_splits option.splits simp: decompose_def)
  apply (auto simp: zip_option_zip_conv)
  by (meson UN_subset_iff domI rev_subsetD zip_fst)

lemma match_subst_domain:
  "match t l = Some \<sigma> \<Longrightarrow> subst_domain \<sigma> \<subseteq> vars_term l"
  using dom_match_term_list [of "Map.empty" "vars_term l" "[(l, t)]"]
  by (force simp: match_def match_list_def subst_of_map_def [abs_def] subst_domain_def split: option.splits)

lemma match_Some_iff:
  "match (t \<cdot> \<sigma>) t = Some \<tau> \<longleftrightarrow> \<tau> = (\<sigma> |s vars_term t)"
  apply (auto)
  apply (metis match_matches match_subst_domain subst_domain_neutral subst_ext term_subst_eq_conv)
  by (metis match_complete' match_subst_domain subst_domain_neutral subst_ext)

lemma ordstep_list_sound:
  "t \<in> set (ordstep_list c ord R s) \<Longrightarrow> (s, t) \<in> ordstep {(x, y). ord x y} (set R)"
  by (auto dest: match_matches elim: mordstep.cases simp: ordstep.intros)


lemma (in reduction_order) ordstep_list_complete:
  assumes min_const: "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and [simp]: "\<And>s t. ord s t \<longleftrightarrow> s \<succ> t"
    and ground: "ground s"
    and step: "(s, t) \<in> ordstep {\<succ>} (set R)"
  shows "\<exists>u. u \<in> set (ordstep_list c ord R s)"
  using mordstep_complete [OF assms(1, 3, 4)] by simp

definition "first_ordstep ord c R s =
  (case ordstep_list ord c R s of
    [] \<Rightarrow> None
  | t # _ \<Rightarrow> Some t)"

definition "compute_ordstep_NF c ord R = compute_NF (first_ordstep c ord R)"

lemma compute_ordstep_NF_sound:
  assumes "compute_ordstep_NF c ord R s = Some t"
  shows "(s, t) \<in> (ordstep {(x, y). ord x y} (set R))\<^sup>*"
  apply (intro assms [unfolded compute_ordstep_NF_def, THEN compute_NF_sound])
  apply (auto simp: first_ordstep_def split: list.splits)
  by (metis list.set_intros(1) ordstep_list_sound)

lemma (in reduction_order) compute_ordstep_NF_complete:
  assumes "compute_ordstep_NF c ord R s = Some t"
    and "\<forall>t. ground t \<longrightarrow> t \<succeq> Fun c []"
    and "\<And>s t. ord s t \<longleftrightarrow> s \<succ> t"
  shows "t \<in> NF (GROUND (ordstep {\<succ>} (set R)))"
  apply (intro assms(1) [unfolded compute_ordstep_NF_def, THEN compute_NF_complete])
  apply (auto simp: first_ordstep_def NF_def GROUND_def dest: ordstep_list_complete [OF assms(2-)] split: list.splits)
  done

end
