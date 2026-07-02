(*
Author:  Bertram Felgenhauer <bertram.felgenhauer@uibk.ac.at> (2015-2017)
Author:  Franziska Rapp <franziska.rapp@uibk.ac.at> (2015-2017)
License: LGPL (see file COPYING.LESSER)
*)

section \<open>Miscellaneous\<close>

text \<open>This theory contains several trivial extensions to existing IsaFoR theories.\<close>
(* TODO: move things elsewhere *)

theory LS_Extras
  imports 
    First_Order_Rewriting.Multihole_Context 
    TRS.Renaming 
    First_Order_Rewriting.Unification_More
begin

subsection \<open>Bounded duplication\<close>

lemma image_mset_Some_None_zero [simp]:
  "count (image_mset Some M) None = 0"
  by (induct M) auto

text \<open>IsaFoR does not seem to define non-duplicating TRSs yet.\<close>

definition non_duplicating :: "('f, 'v) trs \<Rightarrow> bool" where
  "non_duplicating R \<equiv> \<forall>l r. (l, r) \<in> R \<longrightarrow> vars_term_ms r \<le># vars_term_ms l"

text \<open>Bounded duplication {cite \<open>Definition 4.2\<close> FMZvO15}. Note: @{term "undefined"} is an arbitrary fixed value.\<close>

definition bounded_duplicating :: "('f, 'v) trs \<Rightarrow> bool" where
  "bounded_duplicating R \<equiv> SN_rel (rstep {(Fun None [Var undefined], Var undefined)}) (rstep (map_funs_trs Some R))"

text \<open>Non-duplicating TRSs are bounded duplicating {cite \<open>Lemma 4.4\<close> FMZvO15}.\<close>

lemma non_duplicating_imp_bounded_duplicating:
  assumes nd: "non_duplicating R"
  shows "bounded_duplicating R"
proof -
  let ?gt = "inv_image {(n, m) . n > m} (\<lambda>t. count (funs_term_ms t) None)"
  let ?ss = "rstep {(Fun None [Var undefined], Var undefined)}"
  let ?ge = "inv_image {(n, m) . n \<ge> m} (\<lambda>t. count (funs_term_ms t) None)"
  let ?rs = "rstep (map_funs_trs Some R)"
  have "?ss \<subseteq> ?gt"
  proof
    fix s t
    assume "(s, t) \<in> ?ss"
    then have "count (funs_term_ms s) None > count (funs_term_ms t) None"
    proof
      fix C \<sigma> l r
      presume rl: "(l, r) \<in> {(Fun None [Var undefined], Var undefined)}"
        and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      show "count (funs_term_ms s) None > count (funs_term_ms t) None" using rl
        by (auto simp: s t funs_term_ms_ctxt_apply funs_term_ms_subst_apply) 
    qed auto
    then show "(s, t) \<in> ?gt" by simp
  qed
  moreover have "?rs \<subseteq>  ?ge"
  proof
    fix s t
    assume "(s, t) \<in> ?rs"
    then have "count (funs_term_ms s) None \<ge> count (funs_term_ms t) None"
    proof
      fix C \<sigma> l r
      {
        fix l r
        assume "(l, r) \<in> map_funs_trs Some R"
        then have "vars_term_ms r \<le># vars_term_ms l \<and> count (funs_term_ms l) None = 0 \<and> count (funs_term_ms r) None = 0"
          by (auto simp: nd[unfolded non_duplicating_def] map_funs_trs.simps funs_term_ms_map_funs_term)
      } note * = this
      presume rl: "(l, r) \<in> map_funs_trs Some R"
        and s: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C\<langle>r \<cdot> \<sigma>\<rangle>"
      from rl *[of l r] show "count (funs_term_ms s) None \<ge> count (funs_term_ms t) None"
        by (auto simp: s t funs_term_ms_ctxt_apply funs_term_ms_subst_apply)
           (metis image_mset_union mset_subset_eq_count subset_mset.le_iff_add sum_mset.union)
    qed auto
    then show "(s, t) \<in> ?ge" by simp
  qed
  moreover
  {
    have [simp]: "?ge\<^sup>* = ?ge"
      by (auto intro!: trans_refl_imp_rtrancl_id trans_inv_image refl_inv_image simp: refl_on_def trans_def)
    have *: "(?ge\<^sup>* O ?gt O ?ge\<^sup>*)\<inverse> \<subseteq> ?gt\<inverse>"
      by auto
    moreover have "wf (?gt\<inverse>)" by auto (auto simp: converse_def wf_less)
    ultimately have "SN_rel ?gt ?ge" unfolding SN_rel_on_def SN_iff_wf
      by (intro wf_subset[OF _ *]) auto
  }
  ultimately show ?thesis
    by (auto intro: SN_rel_mono simp: bounded_duplicating_def)
qed  

subsection \<open>Trivialities\<close>

lemma pos_diff_cons [simp]: "pos_diff (i # p) (i # q) = pos_diff p q"
  by (auto simp: pos_diff_def)

lemma max_list_append: "max_list (xs1 @ xs2) = max (max_list xs1) (max_list xs2)"
  by (induct xs1) auto

lemma max_list_bound:
  "max_list xs \<le> z \<longleftrightarrow> (\<forall>i < length xs. xs ! i \<le> z)"
  using less_Suc_eq_0_disj by (induct xs) auto

lemma max_list_bound_set:
  "max_list xs \<le> z \<longleftrightarrow> (\<forall>x \<in> set xs. x \<le> z)"
  using less_Suc_eq_0_disj by (induct xs) auto

lemma max_list_mono_concat:
  assumes "length xss = length yss" and "\<And>i. i < length xss \<Longrightarrow> max_list (xss ! i) \<le> max_list (yss ! i)"
  shows "max_list (concat xss) \<le> max_list (concat yss)"
  using assms
proof (induct yss arbitrary: xss)
  case (Cons ys yss) then show ?case by (cases xss) (force simp: max_list_append)+
qed auto

lemma max_list_mono_concat1:
  assumes "length xss = length ys" and "\<And>i. i < length xss \<Longrightarrow> max_list (xss ! i) \<le> ys ! i"
  shows "max_list (concat xss) \<le> max_list ys"
  using assms max_list_mono_concat[of xss "map (\<lambda>y. [y]) ys"] by auto

lemma take1:
  "take (Suc 0) xs = (if xs = [] then [] else [hd xs])"
  by (cases xs) auto

lemma sum_list_take':
  "i \<le> length (xs :: nat list) \<Longrightarrow> sum_list (take i xs) \<le> sum_list xs"
  by (induct xs arbitrary: i) (simp, case_tac i, auto)

lemma nth_equalityE:
  "xs = ys \<Longrightarrow> (length xs = length ys \<Longrightarrow> (\<And>i. i < length xs \<Longrightarrow> xs ! i = ys ! i) \<Longrightarrow> P) \<Longrightarrow> P"
  by simp

lemma finite_vars_mctxt [simp]: "finite (vars_mctxt C)"
  by (induct C) auto

lemma partition_by_of_zip:
  "length xs = sum_list zs \<Longrightarrow> length ys = sum_list zs \<Longrightarrow>
   partition_by (zip xs ys) zs = map (\<lambda>(x,y). zip x y) (zip (partition_by xs zs) (partition_by ys zs))"
  by (induct zs arbitrary: xs ys) (auto simp: take_zip drop_zip)

lemma distinct_count_atmost_1':
  "distinct xs = (\<forall>a. count (mset xs) a \<le> 1)"
  unfolding distinct_count_atmost_1 using dual_order.antisym by fastforce

lemma nth_subset_concat:
  assumes "i < length xss" 
  shows "set (xss ! i) \<subseteq> set (concat xss)"
  by (metis assms concat_nth concat_nth_length in_set_idx nth_mem subsetI)

lemma subst_domain_subst_of:
  "subst_domain (subst_of xs) \<subseteq> set (map fst xs)"
proof (induct xs)
  case (Cons x xs)
  moreover have "subst_domain (subst (fst x) (snd x)) \<subseteq> set (map fst [x])" by simp
  ultimately show ?case
    using subst_domain_compose[of "subst_of xs" "subst (fst x) (snd x)"] by auto
qed simp

lemma subst_apply_mctxt_cong: "(\<forall>x. x \<in> vars_mctxt C \<longrightarrow> \<sigma> x = \<tau> x) \<Longrightarrow> C \<cdot>mc \<sigma> = C \<cdot>mc \<tau>"
  by (induct C) auto

lemma distinct_concat_unique_index:
  "distinct (concat xss) \<Longrightarrow> i < length xss \<Longrightarrow> x \<in> set (xss ! i) \<Longrightarrow> j < length xss \<Longrightarrow> x \<in> set (xss ! j) \<Longrightarrow> i = j"
proof (induct xss rule: List.rev_induct)
  case (snoc xs xss) then show ?case using nth_mem[of i xss] nth_mem[of j xss]
    by (cases "i < length xss"; cases "j < length xss") (auto simp: nth_append simp del: nth_mem)
qed auto

lemma list_update_concat:
  assumes "i < length xss" "j < length (xss ! i)"
  shows "concat (xss[i := (xss ! i)[j := x]]) = (concat xss)[sum_list (take i (map length xss)) + j := x]"
  using assms
proof (induct xss arbitrary: i)
  case (Cons xs xss) then show ?case
    by (cases i) (auto simp: list_update_append)
qed auto

lemma length_filter_sum_list:
  "length (filter p xs) = sum_list (map (\<lambda>x. if p x then 1 else 0) xs)"
  by (induct xs) auto

lemma poss_mctxt_mono:
  "C \<le> D \<Longrightarrow> poss_mctxt C \<subseteq> poss_mctxt D"
  by (induct C D rule: less_eq_mctxt_induct) force+

lemma poss_append_fun_poss:
  shows "p @ q \<in> fun_poss t \<longleftrightarrow> p \<in> poss t \<and> q \<in> fun_poss (t |_ p)" (is "?L \<longleftrightarrow> ?R")
proof
  show "?L \<Longrightarrow> ?R" using fun_poss_imp_poss[of "p @ q" t] fun_poss_fun_conv[of "p @ q" t]
    poss_is_Fun_fun_poss[of q "t |_ p"] by auto
next
  show "?R \<Longrightarrow> ?L" using fun_poss_imp_poss[of q "t |_ p"] fun_poss_fun_conv[of q "t |_ p"]
    poss_is_Fun_fun_poss[of "p @ q" t] by auto
qed

text \<open>see @{thm nrrstep_preserves_root} which proves this without the length\<close>
lemma nrrstep_preserves_root':
  assumes "(Fun f ss, t) \<in> nrrstep R"
  shows "\<exists>ts. t = Fun f ts \<and> length ss = length ts"
  using assms unfolding nrrstep_def rstep_r_p_s_def Let_def by auto

text \<open>see @{thm nrrsteps_preserve_root} which proves this without the length\<close>
lemma nrrsteps_preserve_root':
  assumes "(Fun f ss, t) \<in> (nrrstep R)\<^sup>*"
  shows "\<exists>ts. t = Fun f ts \<and> length ss = length ts"
  using assms by induct (auto dest: nrrstep_preserves_root')

lemma args_joinable_imp_joinable:
  assumes "length ss = length ts" "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep R)\<^sup>\<down>"
  shows "(Fun f ss, Fun f ts) \<in> (rstep R)\<^sup>\<down>"
proof -
  obtain u where "i < length ss \<Longrightarrow> (ss ! i, u i) \<in> (rstep R)\<^sup>* \<and> (ts ! i, u i) \<in> (rstep R)\<^sup>*" for i
    using joinD[OF assms(2)] by metis
  then show ?thesis using assms(1)
    by (intro joinI[of _ "Fun f (map u [0..<length ss])"] args_rsteps_imp_rsteps) auto
qed

instance option :: (infinite) infinite
  by standard (simp add: infinite_UNIV)

lemma finite_into_infinite:
  assumes "finite A" "infinite B"
  shows "\<exists>f. f ` A \<subseteq> B \<and> inj_on f A"
proof -
  from finite_imp_inj_to_nat_seg[OF assms(1)]
  obtain f :: "_ \<Rightarrow> nat" and n where "f ` A = {i. i < n}" "inj_on f A" by auto
  moreover from infinite_countable_subset[OF assms(2)]
  obtain g :: "nat \<Rightarrow> _" where "inj g" "range g \<subseteq> B" by auto
  ultimately show ?thesis by (auto simp: inj_on_def intro!: exI[of _ "g \<circ> f"])
qed

lemma finites_into_infinites:
  fixes f :: "'a \<Rightarrow> 'b set" and g :: "'a \<Rightarrow> 'c set"
  assumes "\<And>\<alpha> \<beta>. f \<alpha> \<inter> f \<beta> \<noteq> {} \<Longrightarrow> \<alpha> = \<beta>"
  and "\<And>\<alpha>. finite (f \<alpha>)"
  and "\<And>\<alpha> \<beta>. g \<alpha> \<inter> g \<beta> \<noteq> {} \<Longrightarrow> \<alpha> = \<beta>"
  and "\<And>\<alpha>. infinite (g \<alpha>)"
  shows "\<exists>h :: 'b \<Rightarrow> 'c. inj_on h (\<Union>\<alpha>. f \<alpha>) \<and> (\<forall>\<alpha>. h ` f \<alpha> \<subseteq> g \<alpha>)"
proof -
  from finite_into_infinite[OF assms(2,4)] have "\<exists>h. h ` f \<alpha> \<subseteq> g \<alpha> \<and> inj_on h (f \<alpha>)" for \<alpha> by blast
  then obtain h where h: "h \<alpha> ` f \<alpha> \<subseteq> g \<alpha> \<and> inj_on (h \<alpha>) (f \<alpha>)" for \<alpha> by metis
  have [simp]: "x \<in> f \<alpha> \<Longrightarrow> (THE \<alpha>. x \<in> f \<alpha>) = \<alpha>" for x \<alpha> using assms(1) by auto
  then show ?thesis using assms(1,3) h
    apply (intro exI[of _ "\<lambda>x. h (THE \<alpha>. x \<in> f \<alpha>) x"])
    apply (auto simp: inj_on_def image_def)
    by blast
qed

subsection \<open>Imbalance\<close>

definition refines :: "'a list \<Rightarrow> 'b list \<Rightarrow> bool" (infix "\<propto>" 55) where
  "ss \<propto> ts \<longleftrightarrow> length ts = length ss \<and> (\<forall>i j. i < length ss \<and> j < length ts \<and> ss ! i = ss ! j \<longrightarrow> ts ! i = ts ! j)"

lemma refines_refl:
  "ss \<propto> ss"
  by (auto simp: refines_def)

lemma refines_trans:
  "ss \<propto> ts \<Longrightarrow> ts \<propto> us \<Longrightarrow> ss \<propto> us"
  by (auto simp: refines_def)

lemma refines_map:
  "ss \<propto> map f ss"
  by (auto simp: refines_def)

lemma refines_imp_map:
  assumes "ss \<propto> ts"
  obtains f where "ts = map f ss"
proof -
  note * = assms[unfolded refines_def]
  let ?P = "\<lambda>s i. (i < length ss \<and> ss ! i = s)" let ?f = "\<lambda>s. ts ! (SOME i. ?P s i)"
  { fix i assume "i < length ss"
    then have "ts ! i = ?f (ss ! i)" using conjunct1[OF *]
      conjunct2[OF *, THEN spec[of _ i], THEN spec[of _ "SOME j. ?P (ss ! i) j"]] someI[of "?P (ss ! i)" i]
      by auto
  }
  then show ?thesis using conjunct1[OF *] by (auto intro!: that[of "?f"] nth_equalityI)
qed

definition imbalance :: "'a list \<Rightarrow> nat" where
  "imbalance ts = card (set ts)"

lemma imbalance_def':
  "imbalance xs = card { i. i < length xs \<and> (\<forall>j. j < length xs \<and> xs ! i = xs ! j \<longrightarrow> i \<le> j) }"
proof (induct xs rule: List.rev_induct)
  case (snoc x xs)
  have "{ i. i < length (xs @ [x]) \<and> (\<forall>j. j < length (xs @ [x]) \<and> (xs @ [x]) ! i = (xs @ [x]) ! j \<longrightarrow> i \<le> j) } =
        { i. i < length xs \<and> (\<forall>j. j < length xs \<and> xs ! i = xs ! j \<longrightarrow> i \<le> j) } \<union> { i. i = length xs \<and> x \<notin> set xs }"
    by (simp add: set_eq_iff less_Suc_eq dnf imp_conjL nth_append)
      (metis cancel_comm_monoid_add_class.diff_cancel in_set_conv_nth nth_Cons_0)
  then show ?case using snoc by (simp add: imbalance_def card_insert_if)
qed (auto simp: imbalance_def)

lemma imbalance_mono: "set ss \<subseteq> set ts \<Longrightarrow> imbalance ss \<le> imbalance ts"
  by (simp add: imbalance_def card_mono)

lemma refines_imbalance_mono:
  "ss \<propto> ts \<Longrightarrow> imbalance ss \<ge> imbalance ts"
  (* apply (auto simp: refines_def imbalance_def' intro: card_mono) (* desired proof *) *)
  unfolding refines_def imbalance_def' by (intro card_mono) (simp_all add: Collect_mono)

lemma refines_imbalance_strict_mono:
  "ss \<propto> ts \<Longrightarrow> \<not> ts \<propto> ss \<Longrightarrow> imbalance ss > imbalance ts"
  unfolding refines_def imbalance_def'
proof (intro psubset_card_mono psubsetI, goal_cases)
  case 3 obtain i j where ij: "i < length ss" "j < length ss" "ts ! i = ts ! j" "ss ! i \<noteq> ss ! j"
    using conjunct1[OF 3(1)] 3(2) by auto
  define f where "f \<equiv> \<lambda>i. SOME j. j < length ss \<and> ss ! j = ss ! i \<and> (\<forall>i. ss ! j = ss ! i \<longrightarrow> j \<le> i)"
  let ?ssi = "{i. i < length ss \<and> (\<forall>j. j < length ss \<and> ss ! i = ss ! j \<longrightarrow> i \<le> j)}"
  let ?tsi = "{i. i < length ts \<and> (\<forall>j. j < length ts \<and> ts ! i = ts ! j \<longrightarrow> i \<le> j)}"
  note f_def = fun_cong[OF f_def[unfolded atomize_eq]]
  { fix i assume "i < length ss"
    then have "\<exists>i'. i' < length ss \<and> ss ! i' = ss ! i \<and> (\<forall>i. ss ! i' = ss ! i \<longrightarrow> i' \<le> i)"
    proof (induct i rule: less_induct)
      case (less i) then show ?case
        by (cases "i < length ss \<and> ss ! i = ss ! i \<and> (\<forall>j. ss ! i = ss ! j \<longrightarrow> i \<le> j)") auto
    qed
    then have "f i < length ss" "ss ! f i = ss ! i" "\<And>j. ss ! f i = ss ! j \<Longrightarrow> f i \<le> j"
    using someI[of "\<lambda>j. j < length ss \<and> ss ! j = ss ! i \<and> (\<forall>i. ss ! j = ss ! i \<longrightarrow> j \<le> i)", folded f_def]
      by auto
    then have "f i < length ss" "ss ! f i = ss ! i" "f i \<in> ?ssi" "f i \<in> ?tsi \<Longrightarrow> ts ! f i = ts ! i"
      using 3(1) by (auto simp: \<open>i < length ss\<close>)
  } note * = this[OF ij(1)] this[OF ij(2)]
  with ij(1,2,3,4) 3(1)[THEN conjunct1]
    3(1)[THEN conjunct2, rule_format, of i "f i"]
    3(1)[THEN conjunct2, rule_format, of j "f j"]
  have "f i \<in> ?ssi" "f j \<in> ?ssi" "ts ! f i = ts ! f j" "f i \<noteq> f j" by metis+
  moreover from this(3,4) have "f i \<notin> ?tsi \<or> f j \<notin> ?tsi" using *(4,8) ij(3)
    by (metis (mono_tags, lifting) dual_order.antisym mem_Collect_eq)
  ultimately show ?case by argo
qed (simp_all add: Collect_mono)

lemma refines_take:
  "ss \<propto> ts \<Longrightarrow> take n ss \<propto> take n ts"
  unfolding refines_def by (intro conjI impI allI; elim conjE) (simp_all add: refines_def)

lemma refines_drop:
  "ss \<propto> ts \<Longrightarrow> drop n ss \<propto> drop n ts"
  unfolding refines_def
proof ((intro conjI impI allI; elim conjE), goal_cases)
  case (2 i j) show ?case using 2(1,3-) 2(2)[rule_format, of "i + n" "j + n"]
    by (auto simp: less_diff_eq less_diff_conv ac_simps)
qed simp

subsection \<open>Abstract Rewriting\<close>

lemma join_finite:
  assumes "CR R" "finite X" "\<And>x y. x \<in> X \<Longrightarrow> y \<in> X \<Longrightarrow> (x, y) \<in> R\<^sup>\<leftrightarrow>\<^sup>*"
  obtains z where "\<And>x. x \<in> X \<Longrightarrow> (x, z) \<in> R\<^sup>*"
  using assms(2,1,3)
proof (induct X arbitrary: thesis)
  case (insert x X)
  then show ?case
  proof (cases "X = {}")
    case False
    then obtain x' where "x' \<in> X" by auto
    obtain z where *: "x' \<in> X \<Longrightarrow> (x', z) \<in> R\<^sup>*" for x' using insert by (metis insert_iff)
    from this[of x'] \<open>x' \<in> X\<close> insert(6)[of x x'] have "(x, z) \<in> R\<^sup>\<leftrightarrow>\<^sup>*"
      by (metis insert_iff converse_rtrancl_into_rtrancl conversionI' conversion_rtrancl)
    with \<open>CR R\<close> obtain z' where "(x, z') \<in> R\<^sup>*" "(z, z') \<in> R\<^sup>*" by (auto simp: CR_iff_conversion_imp_join)
    then show ?thesis by (auto intro!: insert(4)[of z'] dest: *)
  qed auto
qed simp

lemma balance_sequence:
  assumes "CR R"
  obtains (ts) ts where "length ss = length ts"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> R\<^sup>*"
    "\<And>i j. i < length ss \<Longrightarrow> j < length ss \<Longrightarrow> (ss ! i, ss ! j) \<in> R\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> ts ! i = ts ! j"
proof -
  define f where "f s \<equiv> SOME u. \<forall>t \<in> { t \<in> set ss. (s, t) \<in> R\<^sup>\<leftrightarrow>\<^sup>* }. (t, u) \<in> R\<^sup>* " for s
  { fix i assume "i < length ss"
    have "\<forall>t \<in> { t \<in> set ss. (ss ! i, t) \<in> R\<^sup>\<leftrightarrow>\<^sup>* }. (t, f (ss ! i)) \<in> R\<^sup>*"
      unfolding f_def using join_finite[OF \<open>CR R\<close>, of "{ t \<in> set ss. (ss ! i, t) \<in> R\<^sup>\<leftrightarrow>\<^sup>* }"]
        by (rule someI_ex) (auto, metis conversion_inv conversion_rtrancl rtrancl_trans)
    with \<open>i < length ss\<close> have "(ss ! i, f (ss ! i)) \<in> R\<^sup>*" by auto
  } note [intro] = this
  moreover {
    fix i j assume "i < length ss" "j < length ss" "(ss ! i, ss ! j) \<in> R\<^sup>\<leftrightarrow>\<^sup>*"
    then have "{ t \<in> set ss. (ss ! i, t) \<in> R\<^sup>\<leftrightarrow>\<^sup>* } = { t \<in> set ss. (ss ! j, t) \<in> R\<^sup>\<leftrightarrow>\<^sup>* }"
      by auto (metis conversion_inv conversion_rtrancl rtrancl_trans)+
    then have "f (ss ! i) = f (ss ! j)" by (auto simp: f_def)
  } note [intro] = this
  show ?thesis by (auto intro!: ts[of "map f ss"])
qed

lemma balance_sequences:
  assumes "CR R" and [simp]: "length ts = length ss" "length us = length ss" and
    p: "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> R\<^sup>*" "\<And>i. i < length ss \<Longrightarrow> (ss ! i, us ! i) \<in> R\<^sup>*"
  obtains (vs) vs where
    "length vs = length ss"
    "\<And>i. i < length ss \<Longrightarrow> (ts ! i, vs ! i) \<in> R\<^sup>*" "\<And>i. i < length ss \<Longrightarrow> (us ! i, vs ! i) \<in> R\<^sup>*"
    "refines ts vs" "refines us vs"
proof -
  from balance_sequence[OF \<open>CR R\<close>, of "ts @ us"]
  obtain vs where l: "length (ts @ us) = length vs" and
    r: "\<And>i. i < length (ts @ us) \<Longrightarrow> ((ts @ us) ! i, vs ! i) \<in> R\<^sup>*" and
    e: "\<And>i j. i < length (ts @ us) \<Longrightarrow> j < length (ts @ us) \<Longrightarrow> ((ts @ us) ! i, (ts @ us) ! j) \<in> R\<^sup>\<leftrightarrow>\<^sup>* \<Longrightarrow> vs ! i = vs ! j"
    by blast
  { fix i assume *: "i < length ss"
    from * have "(ts ! i, us ! i) \<in> R\<^sup>\<leftrightarrow>\<^sup>*" using p[of i]
      by (metis CR_imp_conversionIff_join assms(1) conversionI' conversion_rtrancl joinI_right rtrancl_trans)
    with * have "vs ! (length ss + i) = vs ! i"
      using e[of i "length ss + i"] by (auto simp: nth_append)
  } note lp[simp] = this
  show ?thesis
  proof (intro vs[of "take (length ss) vs"], goal_cases)
    case (2 i) then show ?case using l r[of i] by (auto simp: nth_append)
  next
    case (3 i) with 3 show ?case using l r[of "length ss + i"] by (auto simp: nth_append)
  next
    case 4
    then show ?case using l by (auto simp: refines_def nth_append intro!: e)
  next
    case 5
    { fix i j assume "i < length ss" "j < length ss" "(us ! i, us ! j) \<in> R\<^sup>\<leftrightarrow>\<^sup>*"
      then have "vs ! i = vs ! j"
        using e[of "length ss + i" "length ss + j"] by (simp add: nth_append)
    }
    then show ?case using l by (auto simp: refines_def nth_append)
  qed (auto simp: l[symmetric])
qed

lemma rtrancl_on_iff_rtrancl_restr:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> y \<in> A"
    "(x, y) \<in> R\<^sup>*" "x \<in> A" 
  shows "(x, y) \<in> (Restr R A)\<^sup>* \<and> y \<in> A"
  using assms(2,3)
proof (induct y rule: rtrancl_induct)
  case (step y z) then show ?case by (auto intro!: rtrancl_into_rtrancl[of _ y _ z] simp: assms(1))
qed auto

lemma CR_on_iff_CR_Restr:
  assumes "\<And>x y. x \<in> A \<Longrightarrow> (x, y) \<in> R \<Longrightarrow> y \<in> A"
  shows "CR_on R A \<longleftrightarrow> CR (Restr R A)"
proof ((standard; standard), goal_cases)
  let ?R' = "Restr R A"
  note * = rtrancl_on_iff_rtrancl_restr[OF assms]
  have *: "(s, t) \<in> R\<^sup>* \<Longrightarrow> s \<in> A \<Longrightarrow> (s, t) \<in> ?R'\<^sup>* \<and> t \<in> A" for s t
    using assms rtrancl_on_iff_rtrancl_restr by metis
  {
    case (1 s t u) then show ?case
    proof (cases "s \<in> A")
      case True
      with 1(3,4) have "(s, t) \<in> R\<^sup>*" "t \<in> A" "(s, u) \<in> R\<^sup>*" "u \<in> A"
        using *[of s t] *[of s u] rtrancl_mono[of ?R' R] by auto
      then show ?thesis
        using True 1(1)[unfolded CR_on_def, rule_format, of s t u] by (auto dest!: joinD *)
    next
      case False
      then have "s = t" "s = u" using 1 by (metis IntD2 converse_rtranclE mem_Sigma_iff)+
      then show ?thesis by auto
    qed
  next
    case (2 s t u)
    obtain v where "(t, v) \<in> ?R'\<^sup>*" "(u, v) \<in> ?R'\<^sup>*" using *[OF 2(3,2)] *[OF 2(4,2)] 2(1) by auto
    then show ?case using rtrancl_mono[of ?R' R] by auto
  }
qed

subsection \<open>Bijection between 'a and 'a option for infinite types\<close>

lemma infinite_option_bijection:
  assumes "infinite (UNIV :: 'a set)" shows "\<exists>f :: 'a \<Rightarrow> 'a option. bij f"
proof -
  from infinite_countable_subset[OF assms] obtain g :: "nat \<Rightarrow> 'a" where g: "inj g" "range g \<subseteq> UNIV" by blast
  let ?f = "\<lambda>x. if x \<in> range g then (case inv g x of 0 \<Rightarrow> None | Suc n \<Rightarrow> Some (g n)) else Some x"
  have "?f x = ?f y \<Longrightarrow> x = y" for x y using g(1) by (auto split: nat.splits if_splits simp: inj_on_def) auto
  moreover have "\<exists>x. ?f x = y" for y
    apply (cases y)
    subgoal using g(1) by (intro exI[of _ "g 0"]) auto
    subgoal for y using g
      apply (cases "y \<in> range g")
      subgoal by (intro exI[of _ "g (Suc (inv g y))"]) auto
      subgoal by auto
    done
  done
  ultimately have "bij ?f" unfolding bij_def surj_def by (intro conjI injI) metis+
  then show ?thesis by blast
qed

definition to_option :: "'a :: infinite \<Rightarrow> 'a option" where
  "to_option = (SOME f. bij f)"

definition from_option :: "'a :: infinite option \<Rightarrow> 'a" where
  "from_option = inv to_option"

lemma bij_from_option: "bij to_option"
  unfolding to_option_def using someI_ex[OF infinite_option_bijection[OF infinite_UNIV]] .

lemma from_to_option_comp[simp]: "from_option \<circ> to_option = id"
  unfolding from_option_def by (intro inv_o_cancel bij_is_inj bij_from_option)

lemma from_to_option[simp]: "from_option (to_option x) = x"
  by (simp add: pointfree_idE)

lemma to_from_option_comp[simp]: "to_option \<circ> from_option = id"
  unfolding from_option_def surj_iff[symmetric] by (intro bij_is_surj bij_from_option)

lemma to_from_option[simp]: "to_option (from_option x) = x"
  by (simp add: pointfree_idE)


lemma var_subst_comp: "t \<cdot> (Var \<circ> f) \<cdot> g = t \<cdot> (g \<circ> f)"
  by (simp add: comp_def subst_subst_compose[symmetric] subst_compose_def del: subst_subst_compose)

subsection \<open>More polymorphic rewriting\<close>

inductive_set rstep' :: "('f, 'v) trs \<Rightarrow> ('f, 'w) term rel" for R where
  rstep' [intro]: "(l, r) \<in> R \<Longrightarrow> (C\<langle>l \<cdot> \<sigma>\<rangle>, C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep' R"

lemma rstep_eq_rstep': "rstep R = rstep' R"
by (auto elim: rstep'.cases)

lemma rstep'_mono:
  assumes "(s, t) \<in> rstep' R" shows "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep' R"
proof -
  from assms obtain D l r \<sigma> where "(l, r) \<in> R" "s = D\<langle>l \<cdot> \<sigma>\<rangle>" "t = D\<langle>r \<cdot> \<sigma>\<rangle>" by (auto simp add: rstep'.simps)
  then show ?thesis using rstep'[of l r R "C \<circ>\<^sub>c D" \<sigma>] by simp
qed

lemma ctxt_closed_rstep' [simp]:
  shows "ctxt.closed (rstep' R)"
  by (auto simp: ctxt.closed_def rstep'_mono elim: ctxt.closure.induct)

lemma rstep'_stable:
  assumes "(s, t) \<in> rstep' R" shows "(s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> rstep' R"
proof -
  from assms obtain C l r \<tau> where "(l, r) \<in> R" "s = C\<langle>l \<cdot> \<tau>\<rangle>" "t = C\<langle>r \<cdot> \<tau>\<rangle>" by (auto simp add: rstep'.simps)
  then show ?thesis using rstep'[of l r R "C \<cdot>\<^sub>c \<sigma>" "\<tau> \<circ>\<^sub>s \<sigma>"] by simp
qed

lemma rsteps'_stable:
  "(s, t) \<in> (rstep' R)\<^sup>* \<Longrightarrow> (s \<cdot> \<sigma>, t \<cdot> \<sigma>) \<in> (rstep' R)\<^sup>*"
  by (induct rule: rtrancl_induct) (auto dest: rstep'_stable[of _ _ _ \<sigma>])

lemma rstep'_sub_vars:
  assumes "(s, t) \<in> (rstep' R)\<^sup>*" "wf_trs R"
  shows "vars_term t \<subseteq> vars_term s"
  using assms(1)
proof (induction rule: converse_rtrancl_induct)
  case (step y z)
  obtain l r C \<sigma> where props: "(l, r) \<in> R" "y = C\<langle>l \<cdot> \<sigma>\<rangle>" "z = C\<langle>r \<cdot> \<sigma>\<rangle>" "vars_term r \<subseteq> vars_term l"
    using step(1) assms(2) unfolding wf_trs_def by (auto elim: rstep'.cases) 
  then have "vars_term z \<subseteq> vars_term y"
    using var_cond_stable[OF props(4), of \<sigma>] vars_term_ctxt_apply[of C "_ \<cdot> \<sigma>"] by auto
  then show ?case using step(3) by simp
qed simp

inductive_set rstep_r_p_s' :: "('f, 'v) trs \<Rightarrow> ('f, 'v) rule \<Rightarrow> pos \<Rightarrow> ('f, 'v, 'w) gsubst \<Rightarrow> ('f, 'w) term rel"
  for R r p \<sigma> where
  rstep_r_p_s' [intro]: "r \<in> R \<Longrightarrow> p = hole_pos C \<Longrightarrow> (C\<langle>fst r \<cdot> \<sigma>\<rangle>, C\<langle>snd r \<cdot> \<sigma>\<rangle>) \<in> rstep_r_p_s' R r p \<sigma>"

declare rstep_r_p_s'.cases [elim]

(* TODO: change definition above *)

lemma rstep_r_p_s'I:
  "r \<in> R \<Longrightarrow> p = hole_pos C \<Longrightarrow> s = C\<langle>fst r \<cdot> \<sigma>\<rangle> \<Longrightarrow> t = C\<langle>snd r \<cdot> \<sigma>\<rangle> \<Longrightarrow> (s, t) \<in> rstep_r_p_s' R r p \<sigma>"
  by auto

lemma rstep_r_p_s'E:
  assumes "(s, t) \<in> rstep_r_p_s' R r p \<sigma>"
  obtains C where "r \<in> R" "p = hole_pos C" "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>"
  using rstep_r_p_s'.cases assms by metis

lemma rstep_r_p_s_eq_rstep_r_p_s': "rstep_r_p_s R r p \<sigma> = rstep_r_p_s' R r p \<sigma>"
  by (auto simp: rstep_r_p_s_def rstep_r_p_s'.simps) (metis hole_pos_ctxt_of_pos_term)

lemma rstep'_iff_rstep_r_p_s':
  "(s, t) \<in> rstep' R \<longleftrightarrow> (\<exists>l r p \<sigma>. (s, t) \<in> rstep_r_p_s' R (l, r) p \<sigma>)"
  by (auto simp: rstep'.simps rstep_r_p_s'.simps)

lemma rstep_r_p_s'_deterministic:
  assumes "wf_trs R" "(s, t) \<in> rstep_r_p_s' R r p \<sigma>" "(s, t') \<in> rstep_r_p_s' R r p \<tau>"
  shows "t = t'"
proof -
  obtain C where 1: "r \<in> R" "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "p = hole_pos C"
    using assms(2) by (auto simp: rstep_r_p_s'.simps)
  obtain D where 2: "s = D\<langle>fst r \<cdot> \<tau>\<rangle>" "t' = D\<langle>snd r \<cdot> \<tau>\<rangle>" "p = hole_pos D"
    using assms(3) by (auto simp: rstep_r_p_s'.simps)
  obtain lhs rhs where 3: "r = (lhs, rhs)" by force
  show ?thesis using 1(1) 2(1,3) unfolding 1(2,3,4) 2(2) 3
  proof (induct C arbitrary: D)
    case Hole have [simp]: "D = \<box>" using Hole by (cases D) auto
    then show ?case using \<open>wf_trs R\<close> Hole by (auto simp: wf_trs_def term_subst_eq_conv)
  next
    case (More f ss1 C' ss2) then show ?case by (cases D) auto
  qed
qed

lemma rstep_r_p_s'_preserves_funas_terms:
  assumes "wf_trs R" "(s, t) \<in> rstep_r_p_s' R r p \<sigma>" "funas_trs R \<subseteq> F" "funas_term s \<subseteq> F"
  shows "funas_term t \<subseteq> F"
proof -
  obtain C where 1: "r \<in> R" "s = C\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = C\<langle>snd r \<cdot> \<sigma>\<rangle>" "p = hole_pos C"
    using assms(2) by (auto simp: rstep_r_p_s'.simps)
  then have "funas_ctxt C \<subseteq> F" using assms(4) by auto
  obtain lhs rhs where 3: "r = (lhs, rhs)" by force
  show ?thesis using 1(1) using assms(1,3,4)
    by (force simp: 1(2,3,4) 3 funas_term_subst funas_trs_def funas_rule_def wf_trs_def)
qed

lemma rstep'_preserves_funas_terms:
  "funas_trs R \<subseteq> F \<Longrightarrow> funas_term s \<subseteq> F \<Longrightarrow> (s, t) \<in> rstep' R \<Longrightarrow> wf_trs R \<Longrightarrow> funas_term t \<subseteq> F"
  unfolding rstep'_iff_rstep_r_p_s' using rstep_r_p_s'_preserves_funas_terms by blast

lemma rstep_r_p_s'_stable:
  "(s, t) \<in> rstep_r_p_s' R r p \<sigma> \<Longrightarrow> (s \<cdot> \<tau>, t \<cdot> \<tau>) \<in> rstep_r_p_s' R r p (\<sigma> \<circ>\<^sub>s \<tau>)"
  by (auto elim!: rstep_r_p_s'E intro!: rstep_r_p_s'I simp: subst_subst simp del: subst_subst_compose)

lemma rstep_r_p_s'_mono:
  "(s, t) \<in> rstep_r_p_s' R r p \<sigma> \<Longrightarrow> (C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep_r_p_s' R r (hole_pos C @ p) \<sigma>"
proof (elim rstep_r_p_s'E)
  fix D assume "r \<in> R" "p = hole_pos D" "s = D\<langle>fst r \<cdot> \<sigma>\<rangle>" "t = D\<langle>snd r \<cdot> \<sigma>\<rangle>"
  then show "(C\<langle>s\<rangle>, C\<langle>t\<rangle>) \<in> rstep_r_p_s' R r (hole_pos C @ p) \<sigma>"
    using rstep_r_p_s'I[of r R "hole_pos C @ p" "C \<circ>\<^sub>c D" "C\<langle>s\<rangle>" \<sigma> "C\<langle>t\<rangle>"] by simp
qed

lemma rstep_r_p_s'_argE:
  assumes "(s, t) \<in> rstep_r_p_s' R (l, r) (i # p) \<sigma>"
  obtains f ss ti where "s = Fun f ss" "i < length ss" "t = Fun f (ss[i := ti])" "(ss ! i, ti) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
proof -
  thm upd_conv_take_nth_drop
  from assms obtain C where *: "hole_pos C = i # p" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "t = C\<langle>r \<cdot> \<sigma>\<rangle>" "(l, r) \<in> R" by (auto elim: rstep_r_p_s'E)
  then obtain f ls D rs where [simp]: "C = More f ls D rs" "i = length ls" by (cases C) auto
  let ?ss = "ls @ D\<langle>l \<cdot> \<sigma>\<rangle> # rs" and ?ts = "ls @ D\<langle>r \<cdot> \<sigma>\<rangle> # rs" and ?ti = "D\<langle>r \<cdot> \<sigma>\<rangle>"
  have "s = Fun f ?ss" "i < length ?ss" "t = Fun f (list_update ?ss i ?ti)" using * by simp_all
  moreover have "(?ss ! i, ?ti) \<in> rstep_r_p_s' R (l, r) p \<sigma>" using * by (auto intro: rstep_r_p_s'I)
  ultimately show ?thesis ..
qed

lemma rstep_r_p_s'_argI:
  assumes "i < length ss" "(ss ! i, ti) \<in> rstep_r_p_s' R r p \<sigma>"
  shows "(Fun f ss, Fun f (ss[i := ti])) \<in> rstep_r_p_s' R r (i # p) \<sigma>"
  using assms(1) rstep_r_p_s'_mono[OF assms(2), of "More f (take i ss) Hole (drop (Suc i) ss)"]
  by (auto simp: id_take_nth_drop[symmetric] upd_conv_take_nth_drop min_def)

lemma wf_trs_implies_fun_poss:
  assumes "wf_trs R" "(s, t) \<in> rstep_r_p_s' R (l, r) p \<sigma>"
  shows "p \<in> fun_poss s"
proof -
  obtain C where *: "(l, r) \<in> R" "s = C\<langle>l \<cdot> \<sigma>\<rangle>" "p = hole_pos C" using assms by auto
  then show ?thesis
    using assms hole_pos_in_filled_fun_poss[of "l \<cdot> \<sigma>" C Var] by (force simp: wf_trs_def')
qed

lemma NF_Var':
  assumes "wf_trs R"
  shows "(Var x, t) \<notin> rstep' R"
  unfolding rstep'_iff_rstep_r_p_s' by (auto dest: wf_trs_implies_fun_poss[OF assms])

lemma fill_holes_rsteps:
  assumes "num_holes C = length ss" "num_holes C = length ts"
    "\<And>i. i < length ss \<Longrightarrow> (ss ! i, ts ! i) \<in> (rstep' \<R>)\<^sup>*"
  shows "(fill_holes C ss, fill_holes C ts) \<in> (rstep' \<R>)\<^sup>*"
  using assms
proof (induct C ss ts rule: fill_holes_induct2)
  case (MFun f Cs xs ys)
  show ?case using MFun(1,2,4)
    by (auto intro!: MFun(3) args_steps_imp_steps  simp: partition_by_nth_nth)
qed auto

subsection \<open>@{term partition_by} stuff\<close>

fun partition_by_idcs :: "nat list \<Rightarrow> nat \<Rightarrow> (nat \<times> nat)" where
  "partition_by_idcs (y # ys) i =
    (if i < y then (0, i) else let (j, k) = partition_by_idcs ys (i - y) in (Suc j, k))"

definition partition_by_idx1 (infix "@\<^sub>1" 105) where
  "ys @\<^sub>1 i = fst (partition_by_idcs ys i)"
definition partition_by_idx2 (infix "@\<^sub>2" 105) where
  "ys @\<^sub>2 i = snd (partition_by_idcs ys i)"

lemma partition_by_predicate:
  assumes "i < length xs"
  shows "partition_by (filter P xs) (map (\<lambda>x. if P x then Suc 0 else 0) xs) ! i = (if P (xs ! i) then [xs ! i] else [])"
  using assms by (induct xs arbitrary: i) (auto simp: less_Suc_eq_0_disj)

lemma nth_by_partition_by:
  "length xs = sum_list ys \<Longrightarrow> i < sum_list ys \<Longrightarrow> xs ! i = partition_by xs ys ! ys @\<^sub>1 i ! ys @\<^sub>2 i"
  apply (induct ys arbitrary: i xs)
   apply (auto simp: partition_by_idx1_def partition_by_idx2_def split: prod.splits)
  by (metis diff_add_inverse fst_conv le_add1 length_drop less_diff_conv2 add.commute linordered_semidom_class.add_diff_inverse nth_drop snd_conv)
 
lemma nth_concat_by_shape:
  assumes "ys = map length xss" "i < sum_list ys"
  shows "concat xss ! i = xss ! ys @\<^sub>1 i ! ys @\<^sub>2 i"
  using nth_by_partition_by[of "concat xss" ys i] partition_by_concat_id[of xss ys] assms
  by (auto simp: length_concat)

lemma list_update_by_partition_by:
  "length xs = sum_list ys \<Longrightarrow> i < sum_list ys \<Longrightarrow>
   xs[i := x] = concat ((partition_by xs ys)[ys @\<^sub>1 i := (partition_by xs ys ! ys @\<^sub>1 i)[ys @\<^sub>2 i := x]])"
proof (induct ys arbitrary: i xs)
  case (Cons y ys) show ?case
    using list_update_append[of "take y xs" "drop y xs" i x] Cons(1)[of "drop y xs" "i - y"] Cons(2,3)
    by (auto simp: partition_by_idx1_def partition_by_idx2_def less_diff_conv2 min.absorb2 split: prod.splits)
qed auto

lemma list_update_concat_by_shape:
  assumes "ys = map length xss" "i < sum_list ys"
  shows "(concat xss)[i := x] = concat (xss[ys @\<^sub>1 i := (xss ! ys @\<^sub>1 i)[ys @\<^sub>2 i := x]])"
  using list_update_by_partition_by[of "concat xss" ys i] partition_by_concat_id[of xss ys] assms
  by (auto simp: length_concat)

lemma partition_by_idx1_bound:
  "i < sum_list ys \<Longrightarrow> ys @\<^sub>1 i < length ys"
  apply (induct ys arbitrary: i)
  apply (auto simp: partition_by_idx1_def split: prod.splits)
  by (metis add_diff_inverse_nat add_less_imp_less_left fst_conv)

lemma partition_by_idx2_bound:
  "i < sum_list ys \<Longrightarrow> ys @\<^sub>2 i <  ys ! ys @\<^sub>1 i"
  apply (induct ys arbitrary: i)
  apply (auto simp: partition_by_idx1_def partition_by_idx2_def split: prod.splits)
  by (metis add_diff_inverse_nat fst_conv nat_add_left_cancel_less snd_conv)

subsection \<open>From multihole contexts to terms and back\<close>

fun mctxt_term_conv :: "('f, 'v) mctxt \<Rightarrow> ('f, 'v option) term" where
  "mctxt_term_conv MHole = Var None"
| "mctxt_term_conv (MVar v) = Var (Some v)"
| "mctxt_term_conv (MFun f Cs) = Fun f (map mctxt_term_conv Cs)"

fun term_mctxt_conv :: "('f, 'v option) term \<Rightarrow> ('f, 'v) mctxt" where
  "term_mctxt_conv (Var None) = MHole"
| "term_mctxt_conv (Var (Some v)) = MVar v"
| "term_mctxt_conv (Fun f ts) = MFun f (map term_mctxt_conv ts)"

lemma mctxt_term_conv_inv [simp]:
  "mctxt_term_conv (term_mctxt_conv t) = t"
  by (induct t rule: term_mctxt_conv.induct) (auto simp: map_idI)

lemma term_mctxt_conv_inv [simp]:
  "term_mctxt_conv (mctxt_term_conv t) = t"
  by (induct t rule: mctxt_term_conv.induct) (auto simp: map_idI)
  
lemma mctxt_term_conv_bij:
  "bij mctxt_term_conv"
  by (auto intro!: o_bij[of term_mctxt_conv mctxt_term_conv])

lemma term_mctxt_conv_bij:
  "bij term_mctxt_conv"
  by (auto intro!: o_bij[of mctxt_term_conv term_mctxt_conv])

lemma mctxt_term_conv_mctxt_of_term[simp]:
  "mctxt_term_conv (mctxt_of_term t) = t \<cdot> (Var \<circ> Some)"
  by (induct t) auto

lemma term_mctxt_conv_mctxt_of_term_conv:
  "term_mctxt_conv (t \<cdot> (Var \<circ> Some)) = mctxt_of_term t"
  by (induct t) auto

lemma weak_match_mctxt_term_conv_mono:
  "C \<le> D \<Longrightarrow> weak_match (mctxt_term_conv D) (mctxt_term_conv C)"
  by (induct C D rule: less_eq_mctxt_induct) auto

definition term_of_mctxt_subst where "term_of_mctxt_subst = case_option (term_of_mctxt MHole) Var"

lemma term_of_mctxt_to_mctxt_term_conv:
  "term_of_mctxt C = mctxt_term_conv C \<cdot> term_of_mctxt_subst"
  by (induct C) (auto simp: term_of_mctxt_subst_def)

lemma poss_mctxt_term_conv[simp]:
  "poss (mctxt_term_conv C) = all_poss_mctxt C"
  by (induct C) auto

lemma funas_term_mctxt_term_conv[simp]:
  "funas_term (mctxt_term_conv C) = funas_mctxt C"
  by (induct C) auto

lemma all_poss_mctxt_term_mctxt_conv[simp]:
  "all_poss_mctxt (term_mctxt_conv t) = poss t"
  by (induct t rule: term_mctxt_conv.induct) auto

lemma funas_mctxt_term_mctxt_conv[simp]:
  "funas_mctxt (term_mctxt_conv t) = funas_term t"
  by (induct t rule: term_mctxt_conv.induct) auto

lemma subm_at_term_mctxt_conv:
  "p \<in> poss t \<Longrightarrow> subm_at (term_mctxt_conv t) p = term_mctxt_conv (subt_at t p)"
  by (induct t p rule: subt_at.induct) auto

lemma subt_at_mctxt_term_conv:
  "p \<in> all_poss_mctxt C \<Longrightarrow> subt_at (mctxt_term_conv C) p = mctxt_term_conv (subm_at C p)"
  by (induct C p rule: subm_at.induct) auto

lemma subm_at_subt_at_conv:
  "p \<in> all_poss_mctxt C \<Longrightarrow> subm_at C p = term_mctxt_conv (subt_at (mctxt_term_conv C) p)"
  by (induct C p rule: subm_at.induct) auto

lemma mctxt_term_conv_fill_holes_mctxt:
  assumes "num_holes C = length Cs"
  shows "mctxt_term_conv (fill_holes_mctxt C Cs) = fill_holes (map_vars_mctxt Some C) (map mctxt_term_conv Cs)"
  using assms by (induct C Cs rule: fill_holes_induct) (auto simp: comp_def)

lemma mctxt_term_conv_map_vars_mctxt_subst:
  shows "mctxt_term_conv (map_vars_mctxt f C) = mctxt_term_conv C \<cdot> (Var \<circ> map_option f)"
  by (induct C) auto

(* an mctxt version of fill_holes_mctxt_fill_holes *)
lemma fill_fill_holes_mctxt:
  assumes "length Cs' = num_holes L'" "length Cs = num_holes (fill_holes_mctxt L' Cs')"
  shows "fill_holes_mctxt (fill_holes_mctxt L' Cs') Cs = fill_holes_mctxt L'
     (map (\<lambda>(D, Es). fill_holes_mctxt D Es) (zip Cs' (partition_holes Cs Cs')))" (is "?L = ?R")
proof -
  note fill_holes_mctxt_fill_holes
  have "fill_holes (fill_holes_mctxt (map_vars_mctxt Some L') (map (map_vars_mctxt Some) Cs'))
    (map mctxt_term_conv Cs) = fill_holes (map_vars_mctxt Some L')
    (map (\<lambda>x. mctxt_term_conv (fill_holes_mctxt (Cs' ! x) (partition_holes Cs Cs' ! x))) [0..<num_holes L'])"
    using assms by (subst fill_holes_mctxt_fill_holes)
      (auto simp: comp_def mctxt_term_conv_fill_holes_mctxt length_partition_by_nth num_holes_fill_holes_mctxt intro!: arg_cong[of _ _ "fill_holes _"])
  then have "term_mctxt_conv (mctxt_term_conv ?L) = term_mctxt_conv (mctxt_term_conv ?R)"
    using assms by (intro arg_cong[of _ _ "term_mctxt_conv"]) (auto simp: zip_nth_conv comp_def
      mctxt_term_conv_fill_holes_mctxt map_vars_mctxt_fill_holes_mctxt)
  then show ?thesis by simp
qed

inductive_set mrstep :: "('f, 'w) trs \<Rightarrow> ('f, 'v) mctxt rel" for R where
  mrstep [intro]: "(mctxt_term_conv C, mctxt_term_conv D) \<in> rstep' R \<Longrightarrow> (C, D) \<in> mrstep R"

lemma mrstepD: "(C, D) \<in> mrstep R \<Longrightarrow> (mctxt_term_conv C, mctxt_term_conv D) \<in> rstep' R"
  by (rule mrstep.induct)

lemma mrstepI_inf: (* caveat: note the implied 'v :: infinite *)
  assumes "(mctxt_term_conv C \<cdot> (Var \<circ> from_option), mctxt_term_conv D \<cdot> (Var \<circ> from_option)) \<in> rstep R"
  shows "(C, D) \<in> mrstep R"
  using rstep'_stable[OF assms[unfolded rstep_eq_rstep'], of "Var \<circ> to_option"]
  by (intro mrstep.intros) (auto simp del: subst_subst_compose simp: subst_subst subst_compose_def)

lemma mrstepD_inf: (* caveat: note the implied 'v :: infinite *)
  "(C, D) \<in> mrstep R \<Longrightarrow> (mctxt_term_conv C \<cdot> (Var \<circ> from_option), mctxt_term_conv D \<cdot> (Var \<circ> from_option)) \<in> rstep R"
  by (metis rstep'_stable mrstepD rstep_eq_rstep')

lemma NF_MVar_MHole: 
  assumes "wf_trs R" and "C = MVar x \<or> C = MHole" 
  shows "(C, D) \<notin> mrstep R"
  using NF_Var'[OF assms(1)] assms(2) by (force dest: mrstepD)

definition fun_poss_mctxt :: "('f, 'v) mctxt \<Rightarrow> pos set" where
  "fun_poss_mctxt C = fun_poss (mctxt_term_conv C)"

lemma fun_poss_mctxt_subset_poss_mctxt:
  "fun_poss_mctxt C \<subseteq> poss_mctxt C"
  by (induct C) (force simp: fun_poss_mctxt_def)+

lemma fun_poss_mctxt_subset_all_poss_mctxt:
  "fun_poss_mctxt C \<subseteq> all_poss_mctxt C"
  by (induct C) (force simp: fun_poss_mctxt_def)+

lemma fun_poss_mctxt_mono:
  "C \<le> D \<Longrightarrow> p \<in> fun_poss_mctxt C \<Longrightarrow> p \<in> fun_poss_mctxt D"
  unfolding less_eq_mctxt_prime fun_poss_mctxt_def
  by (induct C D arbitrary: p rule: less_eq_mctxt'.induct) auto

lemma fun_poss_mctxt_compat:
  "C \<le> D \<Longrightarrow> p \<in> poss_mctxt C \<Longrightarrow> p \<in> fun_poss_mctxt D \<Longrightarrow> p \<in> fun_poss_mctxt C"
  unfolding less_eq_mctxt_prime fun_poss_mctxt_def
  by (induct C D arbitrary: p rule: less_eq_mctxt'.induct) auto

lemma fun_poss_mctxt_mctxt_of_term[simp]:
  "fun_poss_mctxt (mctxt_of_term t) = fun_poss t"
  by (induct t) (auto simp: fun_poss_mctxt_def)

lemma proper_prefix_hole_poss_imp_fun_poss:
  assumes "p \<in> hole_poss C" "q <\<^sub>p p"
  shows "q \<in> fun_poss_mctxt C"
  using assms
  apply (induct C arbitrary: p q; case_tac p; case_tac q)
  apply (auto simp: fun_poss_mctxt_def)
  apply (metis (no_types, opaque_lifting) lessThan_iff less_pos_simps(4) nth_mem list.exhaust)+
  done

subsection \<open>finiteness of prefixes\<close>

lemma finite_set_Cons:
  assumes A: "finite A" and B: "finite B"
  shows "finite (set_Cons A B)"
proof -
  have "set_Cons A B = case_prod (#) ` (A \<times> B)" by (auto simp: set_Cons_def)
  then show ?thesis
    by (simp add: finite_imageI[OF finite_cartesian_product[OF A B],of "case_prod (#)"])
qed

lemma listset_finite:
  assumes "\<forall>A \<in> set As. finite A"
  shows "finite (listset As)"
  using assms
  by (induct As) (auto simp: finite_set_Cons)

lemma elem_listset:
  "xs \<in> listset As = (length xs = length As \<and> (\<forall>i < length As. xs ! i \<in> As ! i))"
proof (induct As arbitrary: xs)
  case (Cons A As xs) then show ?case
    by (cases xs) (auto simp: set_Cons_def nth_Cons nat.splits)
qed auto

lemma finite_pre_mctxt:
  fixes C :: "('f, 'v) mctxt"
  shows "finite { N. N \<le> C }"
proof (induct C)
  case MHole
  have *: "{ N. N \<le> MHole } = { MHole }" by (auto simp: less_eq_mctxt_def)
  show ?case by (simp add: *)
next
  case (MVar x)
  have *: "{ N. N \<le> MVar x } = { MHole, MVar x }"
    by (auto simp: less_eq_mctxt_def split_ifs elim: mctxt_neq_mholeE)
  show ?case by (simp add: *)
next
  case (MFun f Cs)
  have *: "{ N. N \<le> MFun f Cs } = { MHole } \<union> MFun f ` { Ds. Ds \<in> listset (map (\<lambda>C. { N. N \<le> C }) Cs)}"
  unfolding elem_listset
    by (auto simp: image_def less_eq_mctxt_def split_ifs list_eq_iff_nth_eq elim!: mctxt_neq_mholeE) auto
  show ?case
    by (auto simp: * MFun listset_finite[of "map (\<lambda>C. { N. N \<le> C }) Cs"])
qed

text \<open>well-founded-ness of <\<close>

fun mctxt_syms :: "('f, 'v) mctxt \<Rightarrow> nat" where
  "mctxt_syms MHole = 0"
| "mctxt_syms (MVar v) = 1"
| "mctxt_syms (MFun f Cs) = 1 + sum_list (map mctxt_syms Cs)" 
  
lemma mctxt_syms_mono:
  "C \<le> D \<Longrightarrow> mctxt_syms C \<le> mctxt_syms D"
by (induct D arbitrary: C; elim less_eq_mctxtE2)
  (auto simp: map_upt_len_conv[of mctxt_syms,symmetric] intro: sum_list_mono)

lemma sum_list_strict_mono_aux:
  fixes xs ys :: "nat list"
  shows "length xs = length ys \<Longrightarrow> (\<And>i. i < length ys \<Longrightarrow> xs ! i \<le> ys ! i) \<Longrightarrow> sum_list xs < sum_list ys \<or> xs = ys"
proof (induct xs arbitrary: ys)
  case (Cons x xs zs) note * = this
  then show ?case
  proof (cases zs)
    case (Cons y ys)
    have hd: "x \<le> y" and tl: "\<And>i. i < length ys \<Longrightarrow> xs ! i \<le> ys ! i"
      using *(3) by (auto simp: Cons nth_Cons nat.splits)
    show ?thesis using hd *(1)[OF _ tl] *(2) by (auto simp: nth_Cons Cons)
  qed auto
qed auto

lemma mctxt_syms_strict_mono[simp]:
  "C < D \<Longrightarrow> mctxt_syms C < mctxt_syms D"
proof -
  assume "C < D"
  also have "C \<le> D \<Longrightarrow> C = D \<or> mctxt_syms C < mctxt_syms D"
  proof ((induct D arbitrary: C; elim less_eq_mctxtE2), goal_cases)
    case (5 f Ds C Cs)
    have "i < length Ds \<Longrightarrow> mctxt_syms (Cs ! i) \<le> mctxt_syms (Ds ! i)" for i
      using 5(1)[OF _ 5(4), of i] by (auto simp: 5(3))
    then show "C = MFun f Ds \<or> mctxt_syms C < mctxt_syms (MFun f Ds)"
      using 5(1)[OF _ 5(4)] sum_list_strict_mono_aux[of "map mctxt_syms Cs" "map mctxt_syms Ds"]
      by (auto simp: list_eq_iff_nth_eq 5(2,3))
  qed auto
  ultimately show ?thesis by (auto simp: less_mctxt_def)
qed

lemma wf_less_mctxt [simp]:
  "wf { (C :: ('f, 'v) mctxt, D). C < D }"
  by (rule wf_subset[of "inv_image { (a, b). a < b } mctxt_syms"]) (auto simp: wf_less)

lemma map_zip2 [simp]:
  "n = length xs \<Longrightarrow> zip xs (replicate n y) = map (\<lambda>x. (x,y)) xs"
  by (induct xs arbitrary: n) auto

lemma map_zip1 [simp]:
  "n = length ys \<Longrightarrow> zip (replicate n x) ys = map (\<lambda>y. (x,y)) ys"
  by (induct ys arbitrary: n) auto

subsection \<open>Hole positions, left to right\<close>

fun hole_poss' :: "('f, 'v) mctxt \<Rightarrow> pos list" where
  "hole_poss' (MVar x) = []"
| "hole_poss' MHole = [[]]"
| "hole_poss' (MFun f cs) = concat (map (\<lambda>i . map ((#) i) (hole_poss' (cs ! i))) [0..<length cs])"

lemma set_hole_poss': "set (hole_poss' C) = hole_poss C"
  by (induct C) auto

lemma length_hole_poss'[simp]: "length (hole_poss' C) = num_holes C"
  by (induct C) (auto simp: length_concat intro!: arg_cong[of _ _ sum_list] nth_equalityI)

lemma hole_poss'_map_vars_mctxt[simp]:
 "hole_poss' (map_vars_mctxt f C) = hole_poss' C"
  by (induct C rule: hole_poss'.induct) (auto intro: arg_cong[of _ _ concat])

lemma subt_at_fill_holes:
  assumes "length ts = num_holes C" and "i < num_holes C"
  shows "subt_at (fill_holes C ts) (hole_poss' C ! i) = ts ! i"
  using assms(1)[symmetric] assms(2)
proof (induct C ts arbitrary: i rule: fill_holes_induct)
  case (MFun f Cs ts)
  have "i < length (concat (map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]))"
    using MFun arg_cong[OF map_nth, of "map num_holes" Cs] by (auto simp: length_concat comp_def)
  then show ?case
    by (auto simp: nth_map[symmetric] map_concat intro!: arg_cong[of _ _ "\<lambda>x. concat x ! _"])
       (insert MFun, auto intro!: nth_equalityI)
qed auto

lemma subm_at_fill_holes_mctxt:
  assumes "length Ds = num_holes C" and "i < num_holes C"
  shows "subm_at (fill_holes_mctxt C Ds) (hole_poss' C ! i) = Ds ! i"
  using assms(1)[symmetric] assms(2)
proof (induct C Ds arbitrary: i rule: fill_holes_induct)
  case (MFun f Cs Ds)
  have "i < length (concat (map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]))"
    using MFun arg_cong[OF map_nth, of "map num_holes" Cs] by (auto simp: length_concat comp_def)
  then show ?case
    by (auto simp: nth_map[symmetric] map_concat intro!: arg_cong[of _ _ "\<lambda>x. concat x ! _"])
       (insert MFun, auto intro!: nth_equalityI)
qed auto

lemma ctxt_of_pos_term_fill_holes:
  assumes "num_holes C = length ts" "i < num_holes C"
  shows "ctxt_of_pos_term (hole_poss' C ! i) (fill_holes C (ts[i := t])) =
    ctxt_of_pos_term (hole_poss' C ! i) (fill_holes C ts)"
  using assms
proof (induct C ts arbitrary: i rule: fill_holes_induct)
  case (MFun f Cs ts)
  then show ?case using partition_by_idx1_bound[of i "map num_holes Cs"] partition_by_idx2_bound[of i "map num_holes Cs"]
  unfolding fill_holes.simps hole_poss'.simps num_holes.simps
    apply (subst (1 2) nth_concat_by_shape, (simp add: comp_def map_upt_len_conv; fail)+)
    apply (subst list_update_concat_by_shape, (simp add: comp_def map_upt_len_conv; fail)+)
    apply (subst (1 2) nth_map, simp)
    apply (subst (1 2) nth_map, simp)
    apply (subst partition_by_concat_id)
    apply (auto intro!: nth_equalityI simp: nth_list_update)
    done
qed auto

lemma hole_poss_in_poss_fill_holes:
  assumes "num_holes C = length ts" "i < num_holes C"
  shows "hole_poss' C ! i \<in> poss (fill_holes C ts)"
proof -
  have "hole_poss C \<subseteq> poss (fill_holes C ts)"
    using all_poss_mctxt_mono[OF fill_holes_suffix[of C ts]] assms by (simp add: all_poss_mctxt_conv)
  then show ?thesis using assms(2) set_hole_poss'[of C] by auto
qed

lemma replace_at_fill_holes:
  assumes "num_holes C = length ts" "i < num_holes C"
  shows "replace_at (fill_holes C ts) (hole_poss' C ! i) ti = fill_holes C (ts[i := ti])"
proof -
  show ?thesis using assms ctxt_supt_id[OF hole_poss_in_poss_fill_holes, of C "ts[i := ti]" i]
    by (simp add: ctxt_of_pos_term_fill_holes subt_at_fill_holes)
qed

lemma fill_holes_rstep_r_p_s':
  assumes "num_holes C = length ss" "i < num_holes C" "(ss ! i, ti) \<in> rstep_r_p_s' \<R> (l, r) p \<sigma>"
  shows "(fill_holes C ss, fill_holes C (ss[i := ti])) \<in> rstep_r_p_s' \<R> (l, r) (hole_poss' C ! i @ p) \<sigma>"
  using rstep_r_p_s'_mono[OF assms(3), of "ctxt_of_pos_term (hole_poss' C ! i) (fill_holes C ss)"] assms(1,2)
    hole_poss_in_poss_fill_holes[OF assms(1,2)]
  by (simp add: replace_at_fill_holes)

lemma poss_mctxt_append_poss_mctxt:
  "(p @ q) \<in> poss_mctxt C \<longleftrightarrow> p \<in> all_poss_mctxt C \<and> q \<in> poss_mctxt (subm_at C p)"
  by (induct p arbitrary: C; case_tac C) auto

lemma hole_poss_fill_holes_mctxt:
  assumes "num_holes C = length Ds"
  shows "hole_poss (fill_holes_mctxt C Ds) = {hole_poss' C ! i @ q |i q. i < length Ds \<and> q \<in> hole_poss (Ds ! i)}"
    (is "?L = ?R")
  using assms
proof -
  have "p \<in> ?L \<Longrightarrow> p \<in> ?R" for p using assms
  proof (induct C Ds arbitrary: p rule: fill_holes_induct)
    case (MFun f Cs Ds)
    obtain i p' where
      *: "i < length Cs" "p = i # p'"
      "p' \<in> hole_poss (fill_holes_mctxt (Cs ! i) (partition_holes Ds Cs ! i))"
      using MFun(1,3) by (auto)
    with MFun(2)[of i p'] obtain j q where
      "j <  length (partition_holes Ds Cs ! i)" "q \<in> hole_poss (partition_holes Ds Cs ! i ! j)"
      "p' = hole_poss' (Cs ! i) ! j @ q" by auto
    then show ?case
      using MFun(1) * partition_by_nth_nth(1)[of "map num_holes Cs" "hole_poss' (MFun f Cs)" i j,
          simplified, unfolded length_concat]
        partition_by_concat_id[of "map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]"
          "map num_holes Cs", simplified]
      by (auto intro!: exI[of _ "partition_by_idx (sum_list (map num_holes Cs)) (map num_holes Cs) i j"] exI[of _ q]
        simp: partition_by_nth_nth comp_def map_upt_len_conv)
  qed auto
  moreover have "p \<in> ?R \<Longrightarrow> p \<in> ?L" for p using assms
  proof (induct C Ds arbitrary: p rule: fill_holes_induct)
    case (MFun f Cs Ds)
    obtain i q where *: "i < length Ds" "q \<in> hole_poss (Ds ! i)"
      "p = concat (map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]) ! i @ q"
      using MFun(1,3) by auto
    let ?i = "map num_holes Cs @\<^sub>1 i" and ?j = "map num_holes Cs @\<^sub>2 i"
    have
      "?i < length Cs" "?j < num_holes (Cs ! ?i)" "q \<in> hole_poss (partition_holes Ds Cs ! ?i ! ?j)"
      "p = ?i # hole_poss' (Cs ! ?i) ! ?j @ q"
      using partition_by_idx1_bound[of _ "map num_holes Cs"] * MFun(1)
        partition_by_idx2_bound[of _ "map num_holes Cs"] nth_by_partition_by[of Ds "map num_holes Cs"]
        nth_by_partition_by[of "hole_poss' (MFun f Cs)" "map num_holes Cs" i]
        partition_by_concat_id[of "map (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i))) [0..<length Cs]"
          "map num_holes Cs"]
      by (auto simp: length_concat comp_def map_upt_len_conv )
    then show ?case using MFun(1)
      by (auto intro!: MFun(2)[of ?i "hole_poss' (Cs ! ?i) ! ?j @ q"] exI[of _ ?j] exI[of _ "q"])
  qed auto
  ultimately show ?thesis by blast
qed

lemma pos_diff_hole_possI:
  "q \<in> hole_poss C \<Longrightarrow> p \<le>\<^sub>p q \<Longrightarrow> pos_diff q p \<in> hole_poss (subm_at C p)"
  by (induct C p arbitrary: q rule: subm_at.induct) auto

lemma unfill_holes_conv:
  assumes "C \<le> mctxt_of_term t"
  shows "unfill_holes C t = map (subt_at t) (hole_poss' C)"
  using assms
proof (induct C t rule: unfill_holes.induct)
  case (3 f Cs g ts) show ?case using 3(2)
    by (auto elim!: less_eq_mctxtE2 simp: map_concat comp_def 3(1) intro!: arg_cong[of _ _ concat])
qed (auto elim: less_eq_mctxtE2)

lemma unfill_holes_by_prefix:
  assumes "C \<le> D" and "D \<le> mctxt_of_term t"
  shows "unfill_holes D t = concat (map (\<lambda>p. unfill_holes (subm_at D p) (subt_at t p)) (hole_poss' C))"
  using assms
proof (induct C arbitrary: D t)
  case (MVar x) then show ?case by (cases t) (auto elim!: less_eq_mctxtE1)
next
  case (MFun f Cs)
  obtain Ds where D[simp]: "D = MFun f Ds" "length Ds = length Cs" using MFun(2) by (auto elim: less_eq_mctxtE1)
  obtain ts where t[simp]: "t = Fun f ts" "length ts = length Cs" using MFun(3) by (cases t) (auto elim: less_eq_mctxtE1)
  have "i < length Cs \<Longrightarrow> unfill_holes (Ds ! i) (ts ! i) =
    concat (map (\<lambda>p. unfill_holes (subm_at (Ds ! i) p) (subt_at (ts ! i) p)) (hole_poss' (Cs ! i)))" for i
  proof (intro MFun(1))
    assume "i < length Cs" then show "Cs ! i \<le> Ds ! i" using MFun(2) by (auto elim: less_eq_mctxtE1)
  next
    assume "i < length Cs" then show "Ds ! i \<le> mctxt_of_term (ts ! i)" using MFun(3)
    by (auto elim: less_eq_mctxt_MFunE1)
  qed auto
  then have *: "map (\<lambda>i. unfill_holes (Ds ! i) (ts ! i)) [0..<length Cs] =
        map (concat \<circ> map (\<lambda>p. unfill_holes (subm_at (MFun f Ds) p) (Fun f ts |_ p)) \<circ>
             (\<lambda>i. map ((#) i) (hole_poss' (Cs ! i)))) [0..<length Cs]"
    by (intro nth_equalityI) (auto simp: o_def)
  then show ?case by (auto simp add: map_concat map_map[symmetric] simp del: map_map)
qed auto

lemma unfill_holes_mctxt_conv:
  assumes "C \<le> D"
  shows "unfill_holes_mctxt C D = map (subm_at D) (hole_poss' C)"
  using assms
proof (induct C D rule: unfill_holes_mctxt.induct)
  case (3 f Cs g Ds) show ?case using 3(2)
    by (auto elim!: less_eq_mctxtE2 simp: map_concat comp_def 3(1) intro!: arg_cong[of _ _ concat])
qed (auto elim: less_eq_mctxtE2)

lemma map_vars_Some_le_mctxt_of_term_mctxt_term_conv:
  "map_vars_mctxt Some C \<le> mctxt_of_term (mctxt_term_conv C)"
  by (induct C) (auto intro: less_eq_mctxtI1)

lemma unfill_holes_map_vars_mctxt_Some_mctxt_term_conv_conv:
  "C \<le> E \<Longrightarrow> unfill_holes (map_vars_mctxt Some C) (mctxt_term_conv E) = map mctxt_term_conv (unfill_holes_mctxt C E)"
  by (induct C E rule: less_eq_mctxt_induct) (auto simp: map_concat intro!: arg_cong[of _ _ concat])

lemma unfill_holes_mctxt_by_prefix':
  assumes "num_holes C = length Ds" "fill_holes_mctxt C Ds \<le> E"
  shows "unfill_holes_mctxt (fill_holes_mctxt C Ds) E = concat (map (\<lambda>(D, E). unfill_holes_mctxt D E) (zip Ds (unfill_holes_mctxt C E)))"
proof -
  have "C \<le> E" using assms(2) fill_holes_mctxt_suffix[OF assms(1)[symmetric]] by auto
  have [simp]: "i < length Ds \<Longrightarrow> Ds ! i \<le> unfill_holes_mctxt C E ! i" for i using assms
    by (subst (asm) fill_unfill_holes_mctxt[OF \<open>C \<le> E\<close>, symmetric])
      (auto simp: less_eq_fill_holes_iff \<open>C \<le> E\<close>)
  show ?thesis using \<open>C \<le> E\<close> assms
    arg_cong[OF unfill_holes_by_prefix'[of "map_vars_mctxt Some C" "map (map_vars_mctxt Some) Ds" "mctxt_term_conv E"], of "map term_mctxt_conv"]
    order.trans[OF map_vars_mctxt_mono[OF assms(2), of Some] map_vars_Some_le_mctxt_of_term_mctxt_term_conv[of E]]
    unfolding map_vars_mctxt_fill_holes_mctxt[symmetric, OF assms(1)]
    by (auto simp: zip_map1 zip_map2 comp_def unfill_holes_map_vars_mctxt_Some_mctxt_term_conv_conv
      prod.case_distrib map_concat in_set_conv_nth intro!: arg_cong[of _ _ concat])
qed

lemma hole_poss_fill_holes_mctxt_conv:
  assumes "i < num_holes C" "length Cs = num_holes C"
  shows "hole_poss' C ! i \<in> hole_poss (fill_holes_mctxt C Cs) \<longleftrightarrow> Cs ! i = MHole" (is "?L \<longleftrightarrow> ?R")
proof
  assume ?L then show ?R
    using assms arg_cong[OF unfill_holes_mctxt_conv[of C "fill_holes_mctxt C Cs"], of "\<lambda>Cs. Cs ! i"]
    by (auto simp: unfill_fill_holes_mctxt)
next
  assume ?R then show ?L using assms by (force simp: hole_poss_fill_holes_mctxt)
qed

end (* LS_Extras *)
