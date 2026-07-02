theory Indexed_Rewriting
  imports
    "Abstract-Rewriting.Relative_Rewriting" 
    Auxx.Util
    Automatic_Refinement.Misc
begin

(*TODO: move? uses $AFP/Automatic_Refinement/Lib/Misc.thy*)
lemma rtrancl_Image_Image[simp]: "R\<^sup>* `` R\<^sup>* `` X = R\<^sup>* `` X"
  by (simp add: Image_closed_trancl rtrancl_image_unfold_right)

lemma last_occ_inf:
  fixes f :: "nat \<Rightarrow> 'a"
  fixes last_occ :: "nat \<Rightarrow> nat"
  assumes "\<And> i j . lo i \<le> j \<Longrightarrow> f i \<noteq> f j"
    and cdom:"\<And> i. f i \<in> A"
  shows "infinite A"
  using assms(1,2) proof(induct A arbitrary: f lo rule:infinite_finite_induct)
  case (insert a As f lo) show ?case proof(cases "\<exists> i. f i = a")
    case True
    then obtain i where i:"f i = a" by auto
    let "?f x" = "f (x + lo i)"
    let "?lo x" = "lo (x + lo i) - lo i"
    have "\<And> x. a \<noteq> ?f x" using insert(4) unfolding i[symmetric] by simp
    then have inAs:"(\<And>i. ?f i \<in> As)" using insert by fast
    then have "\<And> i2 j2 . (?lo i2 \<le> j2 \<Longrightarrow> ?f i2 \<noteq> ?f j2)" using insert by simp
    then have "infinite As" using insert.hyps(3) inAs by meson
    then show "infinite (insert a As)" by simp
  next case False show ?thesis
    proof(rule insertE)
      fix i
      show "f i \<in> insert a As" by (rule insert)
      from False have "f i \<noteq> a" by auto
      then show "f i = a \<Longrightarrow> infinite (insert a As)" by auto
      have "infinite As" apply(rule insert, fact insert) using insert False by auto
      then show "infinite (insert a As)" by auto
    qed
  qed
qed(auto)

lemma inf_many:
  assumes "finite A"
    and "\<And>i::nat. f i \<in> A"
  shows "\<exists>k. \<forall>i>k. INFM j. (f j = f i)"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then have "\<forall>k. \<exists>i>k. finite {j. f j = f i}" by (simp add: frequently_cofinite)
  then obtain g where g:"\<And>k. g k > k \<and> finite {j. f j = f (g k)}"
    (is "\<And> k. _ \<and> finite (?set k)")  by metis
  have g_finite: "\<And> k. finite (?set k)" using g by simp
  have g_in_set: "\<And> k . g k \<in> ?set k" using g by simp
  { fix i j :: nat
    have gj_bigger:"g j > j" using g by simp
    assume sm:"Max (?set i) \<le> j"
    assume "f (g i) = f (g j)"
    then have "g j \<in> ?set i" by simp
    then have "Max (?set i) \<ge> g j" using Max_ge[OF g_finite] by simp
    then have False using gj_bigger sm by simp
  }
  then have maxSatisfiesCond:"\<And> i j . Suc(Max (?set i)) \<le> j \<Longrightarrow> f (g i) \<noteq> f (g j)" by force
  have "infinite A" using assms(2) last_occ_inf[OF maxSatisfiesCond] by meson
  then show False using assms(1) by blast
qed


lemma Infm_shift2:
  "(INFM i::nat. P (shift f n i) (shift f n (Suc i))) = (INFM i. P (f i) (f (Suc i)))" (is "?S = ?O")
proof
  assume ?S
  show ?O unfolding INFM_nat_le
  proof
    fix m
    from \<open>?S\<close> [unfolded INFM_nat_le]
    obtain k where k: "k \<ge> m" and p: "P (shift f n k) (shift f n (Suc k))" by auto
    then show "\<exists> k \<ge> m. P (f k) (f (Suc k))" by (auto intro!: exI [of _ "k + n"])
  qed
next
  assume ?O
  show ?S unfolding INFM_nat_le
  proof
    fix m
    from \<open>?O\<close> [unfolded INFM_nat_le]
    obtain k where "k \<ge> m + n" "P (f k) (f (Suc k))" by auto
    then show "\<exists> k \<ge> m. P (shift f n k) (shift f n (Suc k))" by (auto intro!: exI [of _ "k - n"])
  qed
qed

(* TODO: Move *)
text\<open>any subset of range have a minimal inverse image\<close>

lemma inverse_image_card: assumes R: "R \<subseteq> range f" shows "\<exists>D. card D = card R \<and> f ` D = R"
proof-
  from R have "\<forall>r \<in> R. \<exists>d. f d = r" by auto
  from bchoice[OF this] obtain g where g: "\<forall>r \<in> R. f (g r) = r" by auto
  then have "f ` g ` R = R" by (auto intro!: image_eqI)
  moreover from g have "inj_on g R" by (intro inj_onI, metis)
  then have "card (g ` R) = card R" by (simp add: card_image)
  ultimately show ?thesis by (intro exI[of _ "g ` R"], auto)
qed

lemma finite_range_imp_finite_domain:
  assumes fin: "finite (range f)"
  shows "\<exists>D. finite D \<and> f ` D = range f"
proof-
  from inverse_image_card[of "range f" f]
  obtain D where 1: "card D = card (range f)" and 2: "f ` D = range f" by auto
  with fin have "finite D"
    using card_0_eq finite.emptyI image_is_empty by fastforce
  with 2 show ?thesis by auto
qed


(* TODO: move? *)
fun seq_Cons where "seq_Cons s seq 0 = s" | "seq_Cons s seq (Suc i) = seq i"

lemma seq_Cons_shift[simp]: "seq_Cons (seq n) (shift seq (Suc n)) = shift seq n" (is "?l = ?r")
proof (intro ext)
  show "?l x = ?r x" for x by(cases x, auto)
qed


section\<open>Relation Induced by Rules\<close>

locale indexed_rewriting =
  fixes induce :: "'a \<Rightarrow> ('b\<times>'b) set"
begin

abbreviation Induce where "Induce R \<equiv> \<Union>r \<in> R. induce r"
abbreviation Induces where "Induces R \<equiv> (Induce R)\<^sup>*"

abbreviation "step seq i \<equiv> (seq i, seq (Suc i))"

inductive traversed where
  base: "traversed {} seq 0"
| step: "traversed R seq i \<Longrightarrow> step seq i \<in> induce r \<Longrightarrow> traversed (insert r R) seq (Suc i)"

lemma traversed_0[simp]: "traversed R seq 0 \<longleftrightarrow> R = {}"
  by(intro iffI, cases rule: traversed.cases, auto intro: traversed.intros)

lemma traversed_empty[simp]: "traversed {} seq i \<longleftrightarrow> i = 0"
  by(intro iffI, cases rule: traversed.cases, auto intro: traversed.intros)

lemma traversed_stretch:
  assumes 1: "traversed R seq i" and 2: "step seq i \<in> Induce R"
  shows "traversed R seq (Suc i)"
proof-
  from 2 obtain r where rR: "r \<in> R" and step: "(seq i, seq (Suc i)) \<in> induce r" by auto
  from 1 step have "traversed (insert r R) seq (Suc i)" by (auto intro: traversed.intros)
  with insert_absorb[OF rR] show ?thesis by auto
qed

lemma traversed_Cons:
  assumes 1: "(s, seq 0) \<in> induce r"
    and 2: "traversed R seq j"
  shows "traversed (insert r R) (seq_Cons s seq) (Suc j)"
  using 2 1
proof(induct rule:traversed.induct)
  case (base seq) then show ?case by (auto intro: traversed.intros)
next
  case IH:(step R seq j r')
  then have "traversed (insert r R) (seq_Cons s seq) (Suc j)" by auto
  with IH have "traversed (insert r' (insert r R)) (seq_Cons s seq) (Suc (Suc j))"
    by (auto intro: traversed.intros)
  then show ?case by (auto simp: insert_commute)
qed

lemma traversed_prefix:
  assumes 1: "\<forall>i < n. step seq i \<in> Induce R"
    and 2: "traversed R (shift seq n) j"
    and nj: "n + j = k"
  shows "traversed R seq k"
  using 1 2 nj
proof(induct n arbitrary: k j)
  case 0 then show ?case by auto
next
  case IH: (Suc n)
  let ?seq = "shift seq (Suc n)"
  from IH(2) obtain r where r: "r \<in> R" and *: "step seq n \<in> induce r" by auto
  from r have rR: "insert r R = R" by auto
  from * have "(seq n, ?seq 0) \<in> induce r" by auto
  note traversed_Cons[of _ ?seq _ R, OF this IH(3), unfolded seq_Cons_shift rR]
  with IH show ?case by auto
qed

lemma traversed_restrict:
  assumes 1: "\<And>j. j \<le> i \<Longrightarrow> seq j = seq' j" and 2: "traversed R seq i"
  shows "traversed R seq' i"
  using 2 1 by(induct rule: traversed.induct, auto intro: traversed.intros)

lemma traversed_imp_chain:
  "traversed R seq i \<Longrightarrow> j < i \<Longrightarrow> step seq j \<in> Induce R"
proof(induct rule:traversed.induct)
  case (step R seq i r) then show ?case by (cases "j = i", auto)
qed auto

lemma traversed_imp_used:
  "traversed R seq i \<Longrightarrow> r \<in> R \<Longrightarrow> \<exists>j<i. step seq j \<in> induce r"
proof(induct rule:traversed.induct)
  case (step R seq i r') then show ?case
  proof(cases "r' = r")
    case False with step obtain j where  "j<i" and "step seq j \<in> induce r" by auto
    then show ?thesis by (auto intro: exI[of _ j])
  qed auto
qed auto

definition "traverse R = { (seq 0, seq i) | i seq. traversed R seq i }"

lemma mem_traverseI:
  assumes "seq 0 = s" and "seq i = t" and "traversed R seq i"
  shows "(s,t) \<in> traverse R"
  unfolding traverse_def using assms by auto

lemma mem_traverseE:
  assumes "(s,t) \<in> traverse R"
  obtains seq i
  where "seq 0 = s" and "seq i = t" and "traversed R seq i"
  using assms unfolding traverse_def by auto

lemma traverse_empty[simp]: "traverse {} = Id"
proof-
  have "(x,x) \<in> traverse {}" for x
  proof(intro mem_traverseI)
    show "traversed {} (\<lambda>a. x) 0" by (auto intro: traversed.intros)
  qed auto
  moreover have "(x,y) \<in> traverse {} \<Longrightarrow> x = y" for x y by(elim mem_traverseE, auto)
  ultimately show ?thesis by auto
qed

lemma traverse_subset_Induces: "traverse R \<subseteq> Induces R"
proof (intro subrelI, elim mem_traverseE)
  fix x y seq i
  assume 0: "seq 0 = x" "seq i = y" and 1: "traversed R seq i"
  from 1 have "(seq 0, seq i) \<in> (Induce R)\<^sup>*"
  proof (induct i arbitrary: R rule: nat_induct)
    case 0
    then show ?case by auto
  next
    case IH: (Suc i)
    from IH(2) obtain r R'
      where 1: "R = insert r R'" and 2: "step seq i \<in> induce r" and 3: "traversed R' seq i"
      by(cases rule:traversed.cases, auto)
    from 1 IH(1)[OF 3] have "(seq 0, seq i) \<in> Induces R"
      by (elim rev_subsetD, intro rtrancl_mono, auto)
    moreover from 1 2 have "step seq i \<in> Induces R" by auto
    ultimately show ?case by auto
  qed
  with 0 show "(x,y) \<in> Induces R" by auto
qed

definition "recurring R seq \<equiv> \<forall>i. \<exists>j>0. traversed R (shift seq i) j"

lemma recurringI[intro]: assumes "\<And>i. \<exists>j>0. traversed R (shift seq i) j" shows "recurring R seq"
  using assms unfolding recurring_def by auto

lemma recurringD[dest]: assumes "recurring R seq" shows "\<exists>j>0. traversed R (shift seq i) j"
  using assms[unfolded recurring_def] by auto

lemma recurringE[elim]: assumes "recurring R seq" obtains j where "j > 0" "traversed R (shift seq i) j"
  using assms[unfolded recurring_def] by auto

lemma recurring_empty[simp]: "\<not> recurring {} seq" by auto

lemma recurring_imp_chain: assumes tang: "recurring R seq" shows "chain (Induce R) seq"
proof
  fix i
  from recurringD[OF tang, of i] obtain j
    where 1: "j > 0" and 2: "traversed R (shift seq i) j" by auto
  from traversed_imp_chain[OF 2, rule_format, OF 1]
  show "step seq i \<in> Induce R" by auto
qed

lemma recurring_shift:
  assumes "recurring R seq" shows "recurring R (shift seq n)"
proof
  fix i from recurringD[OF assms]
  obtain j where "j > 0" "traversed R (shift seq (n+i)) j" by auto
  then show "\<exists>j > 0. traversed R (shift (shift seq n) i) j" by (auto simp: ac_simps)
qed

lemma recurring_prefix:
  assumes 1: "\<forall>j < i. step seq j \<in> Induce R" and 2: "recurring R (shift seq i)"
  shows "recurring R seq"
proof(intro recurringI)
  fix i'
  show " \<exists>j > 0. traversed R (shift seq i') j"
  proof(cases "i' < i")
    case False with recurringD[OF 2, of "i'-i"] show ?thesis by auto
  next
    case True
    moreover from recurringD[OF 2, of 0] obtain j where "j > 0" "traversed R (shift seq i) j" by auto
    moreover from 1 have "\<forall>j < i - i'. step (shift seq i') j \<in> Induce R" by auto
    note traversed_prefix[OF this _ refl]
    ultimately show ?thesis by (intro exI[of _ "i - i' +j"], auto)
  qed
qed

lemma recurring_imp_INFM:
  assumes "recurring R seq" and rR: "r \<in> R" shows "\<exists>\<^sub>\<infinity>i. step seq i \<in> induce r"
  unfolding INFM_nat
proof
  fix i
  from assms
  obtain j where "traversed R (shift seq (Suc i)) j" by (elim recurringE)
  from traversed_imp_used[OF this rR]
  obtain k where "step (shift seq (Suc i)) k \<in> induce r" by auto
  then have "step seq (Suc i + k) \<in> induce r" by (auto simp: ac_simps)
  then show "\<exists>n>i. step seq n \<in> induce r" by (intro exI[of _ "Suc i+k"],auto)
qed

lemma chain_imp_recurring:
  assumes fin: "finite R" and chain: "chain (Induce R) seq"
  shows "\<exists>R' \<subseteq> R. \<exists>cp. recurring R' (shift seq cp)"
proof-
  from chain have "\<forall>i. \<exists>r. r \<in> R \<and> step seq i \<in> induce r" by auto
  from choice[OF this] obtain l where l: "\<And>i. l i \<in> R \<and> step seq i \<in> induce (l i)" by auto
  then have ranR: "range l \<subseteq> R" by auto

  from ranR have infm:"\<exists>k. \<forall>i>k. \<exists>\<^sub>\<infinity>j. l j = l i" by (intro inf_many[OF fin], auto)
  then obtain k' where "\<And> i. i > k' \<Longrightarrow> \<exists>\<^sub>\<infinity>j. l j = l i" by auto
  moreover obtain k where "k = Suc k'" by auto
  ultimately have k: "\<And> i. i \<ge> k \<Longrightarrow> \<exists>\<^sub>\<infinity>j. l j = l i" by auto

  have range_shift: "range (shift l (k+i)) = range (shift l k)" (is "?l = ?r") for i
  proof (safe)
    fix j
    have "shift l (k + i) j = shift l k (i+j)" by (auto simp: ac_simps)
    then show "shift l (k+i) j \<in> ?r" by auto
  next
    fix i'
    have "\<exists>\<^sub>\<infinity>j. l j = l (k+i')" by (rule k, auto)
    from this[unfolded INFM_nat] obtain j where "j > k+i" "l j = l (k+i')" by auto
    then have "shift l k i' = shift l (k+i) (j-k-i)" by (auto simp: ac_simps)
    then show "shift l k i' \<in> ?l" by auto
  qed

  show ?thesis
  proof(intro exI conjI)
    define l1 where "l1 = shift l k"
    define seq1 where "seq1 = shift seq k"
    show ran1: "range l1 \<subseteq> R" by (auto simp: l1_def l)

    show "recurring (range l1) (shift seq k)"
    proof
      fix i
      define l' where "l' = shift l1 i"
      define seq' where "seq' = shift seq1 i"
      from l have l': "\<And>i. l' i \<in> R \<and> step seq' i \<in> induce (l' i)" by (auto simp: l'_def seq'_def l1_def seq1_def)
      have fin': "finite (range l')"
      proof (rule finite_subset)
        from ranR fin finite_subset show "finite (range l)" by auto
      qed (auto simp: l'_def l1_def)
      from finite_range_imp_finite_domain[OF this] obtain D
        where finD: "finite D" and l'D: "l' ` D = range l'" by auto
      have ran: "range l1 = l' ` {0..<Suc (Max D)}" (is "?L = ?R")
      proof
        from range_shift[of i] have "range l1 = range l'" by (auto simp: l1_def l'_def ac_simps)
        then have [simp]: "range l1 = l' ` D" using l'D by auto
        show "?L \<subseteq> l' ` {0..<Suc (Max D)}" using finD by (auto simp: atLeastLessThanSuc_atLeastAtMost)
        from l'D show "?R \<subseteq> ?L" by auto
      qed
      have "R' = l' ` {0..<i} \<Longrightarrow> traversed R' seq' i" for R' i
      proof-
        assume R': "R' = l' ` {0..<i}"
        then have fin: "finite R'" by auto
        from this R' show "traversed R' seq' i"
        proof(induct R' arbitrary: i rule: finite_psubset_induct)
          case (psubset R')
          then have IH1: "\<And>B i. B \<subset> R' \<Longrightarrow> B = l' ` {0..<i} \<Longrightarrow> traversed B seq' i"
            and "R' = l' ` {0..<i}" by auto
          from this(2) show ?case
          proof (induct i)
            case IH2: (Suc i)
            define R'' where [simp]: "R'' = l' ` {0..<i}"
            with IH2 have R'': "R' = insert (l' i) R''" by (simp add: atLeastLessThanSuc)
            show ?case unfolding R''
            proof(intro traversed.intros)
              show "traversed R'' seq' i"
              proof(cases "l' i \<in> R''")
                case True
                then have "R' = R''" using R'' by auto
                from IH2[unfolded this] show ?thesis by auto
              next
                case False
                with R'' have "R' \<supset> R''" by auto
                from IH1[OF this] show ?thesis by auto
              qed
            qed (insert l', auto)
          qed auto
        qed
      qed
      from this[OF ran] show "\<exists>j > 0. traversed (range l1) (shift (shift seq k) i) j"
        by (auto simp:seq'_def seq1_def)
    qed 
  qed
qed

definition recurrent_on
  where "recurrent_on R X \<equiv> \<exists>seq. seq 0 \<in> X \<and> recurring R seq"

lemma recurrent_onI[intro]:
  assumes "seq 0 \<in> X" "recurring R seq" shows "recurrent_on R X"
  using assms by (auto simp: recurrent_on_def)

lemma recurrent_onD[dest]:
  assumes "recurrent_on R X"
  shows "\<exists>seq. seq 0 \<in> X \<and> recurring R seq"
  using assms by (auto simp: recurrent_on_def)

lemma recurrent_onE[elim]:
  assumes "recurrent_on R X"
  obtains seq where "seq 0 \<in> X" and "recurring R seq"
  using assms by (auto simp: recurrent_on_def)

lemma not_recurrent_on_empty[simp]: "\<not> recurrent_on {} X" by auto

lemma not_SN_on_imp_recurrent_on:
  assumes fin: "finite R" and nSN: "\<not> SN_on (Induce R) X"
  shows "\<exists>R' \<subseteq> R. recurrent_on R' (Induces R `` X)"
proof-
  from nSN obtain seq where 0: "seq 0 \<in> X" and chain: "chain (Induce R) seq" by auto
  from chain_imp_recurring[OF fin chain]
  obtain R' cp where R': "R' \<subseteq> R" and rec: "recurring R' (shift seq cp)" by auto
  from 0 chain have "seq cp \<in> Induces R `` X" by (meson ImageI rtrancl_fun_conv)
  with R' rec show ?thesis by(intro exI conjI recurrent_onI, auto)
qed

lemma recurrent_on_imp_not_SN_on:
  assumes R': "R' \<subseteq> R"
    and rec: "recurrent_on R' (Induces R `` X)" shows "\<not> SN_on (Induce R) X"
proof-
  from rec
  obtain seq where s0: "seq 0 \<in> Induces R `` X" and rec: "recurring R' seq" by (elim recurrent_onE)
  from R' chain_mono[OF _ recurring_imp_chain[OF rec], of "Induce R"]
  have "chain (Induce R) seq" by auto
  with s0 show ?thesis by (subst SN_on_Image_rtrancl_iff[symmetric], blast)
qed

end

declare indexed_rewriting.mem_traverseE[elim]

subsection \<open>Monotonic properties\<close>
context
  fixes R :: "'a set" and induce induce' :: "'a \<Rightarrow> ('b \<times> 'b) set"
  assumes mono: "\<And>r. r \<in> R \<Longrightarrow> induce r \<subseteq> induce' r"
begin

interpretation I: indexed_rewriting induce.
interpretation I': indexed_rewriting induce'.

lemma chain_index_mono:
  shows "chain (I.Induce R) seq \<Longrightarrow> chain (I'.Induce R) seq"
  using mono UN_iff contra_subsetD by fastforce

lemma traversed_mono: assumes "I.traversed R seq i" shows "I'.traversed R seq i"
proof-
  have "I.traversed R' seq i \<Longrightarrow> R' \<subseteq> R \<Longrightarrow> I'.traversed R' seq i" for R'
    apply(induct rule: I.traversed.induct)
    using mono by (auto intro: I'.traversed.intros)
  with assms show ?thesis by auto
qed

lemma recurring_mono: assumes "I.recurring R seq" shows "I'.recurring R seq"
  using I.recurringD[OF assms] traversed_mono by (intro I'.recurringI,force)

lemma traverse_mono: "I.traverse R \<subseteq> I'.traverse R"
proof
  fix x y assume "(x,y) \<in> I.traverse R"
  then obtain seq i where 1: "seq 0 = x" "seq i = y" and 2: "I.traversed R seq i" by auto
  from 1 traversed_mono[OF 2] show "(x,y) \<in> I'.traverse R" by (rule I'.mem_traverseI)
qed

end

locale rule_morphism =
  indexed_rewriting induce
  for f :: "'a \<Rightarrow> 'a'" and Rules :: "'r set" and f_rule :: "'r \<Rightarrow> 'r'" and induce :: "'r \<Rightarrow> 'a rel" and induce' +
  assumes morph: "\<And>r. r \<in> Rules \<Longrightarrow> (s,t) \<in> induce r \<Longrightarrow> (f s, f t) \<in> induce' (f_rule r)"
begin

sublocale target: indexed_rewriting induce'.

lemma traversed_morphism:
  assumes "traversed Rules seq i" shows "target.traversed (f_rule ` Rules) (f \<circ> seq) i"
proof-
  have "traversed R' seq i \<Longrightarrow> R' \<subseteq> Rules \<Longrightarrow> target.traversed (f_rule ` R') (f \<circ> seq) i" for R'
    by(induct rule: traversed.induct, insert morph, auto intro!: target.traversed.intros)
  from this[of Rules] assms show ?thesis by auto
qed

lemma recurring_morphism:
  assumes "recurring Rules seq" shows "target.recurring (f_rule ` Rules) (f \<circ> seq)"
proof
  fix i
  from assms obtain j where j0: "j > 0" and *: "traversed Rules (shift seq i) j" by (elim recurringE)
  from traversed_morphism[OF *] have "target.traversed (f_rule ` Rules) (f \<circ> shift seq i) j" by auto
  also have "f \<circ> shift seq i = shift (f \<circ> seq) i" by auto
  finally show "\<exists>j>0. target.traversed (f_rule ` Rules) (shift (f \<circ> seq) i) j" using j0 by auto
qed

end

subsection\<open>\<close>
context indexed_rewriting begin

lemma Induce_O_traverse: "Induce R O traverse R \<subseteq> traverse R"
proof
  fix s u assume "(s,u) \<in> Induce R O traverse R"
  then obtain t where st: "(s,t) \<in> Induce R" and tu: "(t,u) \<in> traverse R" by auto
  from st obtain r where rR: "r \<in> R" and st: "(s,t) \<in> induce r" by auto
  from tu[unfolded traverse_def] obtain seq i
    where t: "seq 0 = t"
      and u: "seq i = u"
      and tang: "traversed R seq i" by auto
  from st t have s0: "(s,seq 0) \<in> induce r" by auto
  { fix P assume "traversed P seq i"
    then have "P \<subseteq> R \<Longrightarrow> (s, seq i) \<in> traverse (insert r P)" using s0
    proof (induct rule: traversed.induct)
      case (base seq) then show ?case
        by(intro mem_traverseI[of "\<lambda>i. if i = 0 then s else (seq (i-1))"], auto intro: traversed.intros)
    next
      case (step P seq i p)
      then have "(s, seq i) \<in> traverse (insert r P)" by auto
      then obtain seq2 i2
        where s0: "seq2 0 = s" and i: "seq2 i2 = seq i" and *: "traversed (insert r P) seq2 i2" by auto
      have "(s, seq (Suc i)) \<in> traverse (insert p (insert r P))"
      proof(rule mem_traverseI)
        let ?seq = "\<lambda>j. if j \<le> i2 then seq2 j else seq (Suc i)"
        show "traversed (insert p (insert r P)) ?seq (Suc i2)"
          using i step by(intro traversed.intros traversed_restrict[OF _ *], auto)
        show "?seq 0 = s" using s0 by auto
      qed auto
      also have "insert p (insert r P) = insert r (insert p P)" by auto
      finally show ?case.
    qed
  }
  from this[OF tang] have "(s, seq i) \<in> traverse (insert r R)" by auto
  with insert_absorb[OF rR] u show "(s, u) \<in> traverse R" by auto
qed

lemma Induce_rtrancl_O_traverse[simp]: "(Induce R)\<^sup>* O traverse R = traverse R" (is "?L = ?R")
  using compat_tr_compat[OF Induce_O_traverse] by auto

subsection \<open>Relating @{term recurrent_on} and @{term SN_on}}\<close>

lemma recurrent_on_Image:
  assumes "recurrent_on R (Induces R `` X)" shows "recurrent_on R X"
proof(rule ccontr, insert assms, elim recurrent_onE)
  assume NR: "\<not> recurrent_on R X"
  fix seq
  assume "seq 0 \<in> (Induce R)\<^sup>* `` X" and rec: "recurring R seq"
  moreover from rec have "seq 0 \<in> (Induce R ^^ i) `` X \<Longrightarrow> False" for i
  proof(induct i arbitrary:seq)
    case (0 seq') with NR show False by auto
  next
    case IH: (Suc i seq')
    then obtain s where "(s, seq' 0) \<in> Induce R ^^ Suc i" and sX: "s \<in> X" by auto
    then obtain t where st: "(s,t) \<in> Induce R ^^ i" and t0: "(t, seq' 0) \<in> Induce R" by (elim relpow_Suc_E)
    define seq'' where [simp]: "seq'' = (\<lambda>i. if i = 0 then t else seq' (i-1))"
    show ?case
    proof(rule IH(1))
      from st sX show "seq'' 0 \<in> (Induce R ^^ i) `` X" by auto
      show "recurring R seq''"
      proof(rule recurring_prefix)
        note IH(3)
        also have shift'': "seq' = shift seq'' 1" by auto
        finally show "recurring R (shift seq'' 1)".
      qed(insert t0, auto)
    qed
  qed
  ultimately show False unfolding rtrancl_is_UN_relpow by auto
qed

lemma not_SN_on_traverse_empty: "\<not> SN_on (traverse {}) {x}"
proof-
  have "chain (traverse {}) (\<lambda>i. x)" by auto
  then show ?thesis by auto
qed

lemma recurring_imp_not_SN_on_traverse:
  assumes recurring: "recurring R seq" shows "\<not> SN_on (traverse R) {seq 0}"
proof
  assume SN: "SN_on (traverse R) {seq 0}"
  from recurring_imp_chain[OF recurring] have chain: "chain (Induce R) seq" by auto
  { fix n
    have "SN_on (traverse R) {seq n}"
    proof (induct n)
      case 0 show ?case by(rule SN)
    next
      case (Suc n)
      { assume "\<not> ?case"
        then obtain seq' where 0: "seq' 0 = seq (Suc n)" and chain': "chain (traverse R) seq'" by auto
        from 0 chain have "(seq n, seq' 0) \<in> Induce R" by auto
        moreover from chain' have "(seq' 0, seq' 1) \<in> traverse R" by auto
        ultimately have "(seq n, seq' 1) \<in> Induce R O traverse R" by auto
        from subsetD[OF Induce_O_traverse this] have "(seq n, seq' 1) \<in> traverse R".
        with Suc step_preserves_SN_on have "SN_on (traverse R) {seq' 1}" by auto
        with chain' have False by force
      }
      then show ?case by auto
    qed
  }
  note SN = this
  { fix n x
    assume xn: "x = seq n"
    have "(seq 0, x) \<in> (Induce R)\<^sup>*" unfolding xn using chain by (simp add: chain_imp_rtrancl)
    have "x = seq n \<Longrightarrow> recurring R (shift seq n) \<Longrightarrow> False"
    proof(induct x arbitrary: n rule:SN_on_induct[OF SN[of n]])
      case 1 from xn show ?case by auto
    next
      case (2 x n)
      from recurringD[OF \<open>recurring R (shift seq n)\<close>, of 0]
      obtain j where tang: "traversed R (shift seq n) j" by auto
      then have "(x, seq (j+n)) \<in> traverse R" unfolding 2(2) by (intro mem_traverseI, auto)
      from 2(1)[OF this refl] recurring_shift[OF recurring]
      show ?case.
    qed
  }
  from this[OF refl, of 0] recurring show False by auto
qed

lemma SN_on_traverse_imp_not_recurrent_on:
  assumes SN: "SN_on (traverse R) X" shows "\<not> recurrent_on R X"
proof(intro notI)
  assume "recurrent_on R X"
  then obtain seq where 0: "seq 0 \<in> X" and recurring: "recurring R seq" by auto
  from 0 have "SN_on (traverse R) {seq 0}" by (auto intro!: SN_on_subset2[OF _ SN])
  moreover from recurring_imp_not_SN_on_traverse[OF recurring]
  have "\<not> SN_on (traverse R) {seq 0}" by auto
  ultimately show False by auto
qed

text\<open>The other direction is tedious.\<close>
end

fun concat_list_seq where
  "concat_list_seq lseq i j =
  (let len = length (lseq i) in
   if len > 1 then
     if j < len-1 then lseq i ! j else concat_list_seq lseq (Suc i) (j-(len-1))
   else undefined)"

declare concat_list_seq.simps[simp del]

lemma shift_concat_list_seq:
  assumes len: "\<forall>i. length (lseq i) > 1"
  shows "\<exists>i' \<ge> i. \<exists> j' \<le> j. j' < length (lseq i') \<and> shift (concat_list_seq lseq i) j = shift (concat_list_seq lseq i') j'"
    (is "\<exists>i' \<ge> i. \<exists> j' \<le> j. ?goal i j i' j'")
proof(induct j arbitrary: i rule: less_induct)
  case IH: (less j)
  let ?len = "length (lseq i)"
  from len have l1: "?len > 1" by auto
  show ?case
  proof (cases "j < ?len")
    case True then show ?thesis by auto
  next
    case False
    with l1 have "j - (?len - 1) < j" by auto
    from IH[OF this, of "Suc i"] obtain i' j'
      where 1: "i' \<ge> Suc i"
        and 2: "j' \<le> j - (?len - 1)"
        and 3: "?goal (Suc i) (j - (?len - 1)) i' j'" by auto
    from 1 have 1: "i' \<ge> i" by auto
    moreover
    from 2 have 2: "j' \<le> j" by auto
    moreover
    from False l1 have "shift (concat_list_seq lseq (Suc i)) (j-(?len-1)) = shift (concat_list_seq lseq i) j"
      by(intro ext, unfold shift.simps, subst concat_list_seq.simps, auto simp: Let_def)
    note 3[unfolded this]
    ultimately show ?thesis by auto
  qed
qed

definition chain_fill_cond where
  "chain_fill_cond R s t l \<equiv>
   let last = length l - 1 in
   last > 0 \<and> s = l ! 0 \<and> l ! last = t \<and> (\<forall>j<last. (l ! j, l ! (Suc j)) \<in> R)"

lemma chain_fill_condI[intro]:
  assumes "length l > 1"
    and "s = l ! 0"
    and "\<And>j. Suc j < length l \<Longrightarrow> (l ! j, l ! (Suc j)) \<in> R"
    and "l ! (length l - 1) = t"
  shows "chain_fill_cond R s t l"
  using assms by(auto simp: chain_fill_cond_def Let_def)

lemma chain_fill_condD[dest]:
  assumes "chain_fill_cond R s t l"
  shows "length l > 1"
    and "s = l ! 0"
    and "\<forall>j < length l - 1. (l ! j, l ! (Suc j)) \<in> R"
    and "l ! (length l - 1) = t"
  using assms[unfolded chain_fill_cond_def Let_def] by auto

definition seq_fill_cond where
  "seq_fill_cond step seq lseq \<equiv> \<forall>i. step (seq i) (seq (Suc i)) (lseq i)"

lemma seq_fill_condI[intro]:
  assumes "\<And>i. step (seq i) (seq (Suc i)) (lseq i)"
  shows "seq_fill_cond step seq lseq"
  using assms by(auto simp: seq_fill_cond_def)

lemma seq_fill_condD[dest]:
  assumes "seq_fill_cond step seq lseq"
  shows "step (seq i) (seq (Suc i)) (lseq i)"
  using assms[unfolded seq_fill_cond_def] by auto

lemma chain_concat:
  assumes "seq_fill_cond (chain_fill_cond R) seq lseq"
  shows "chain R (concat_list_seq lseq i)" (is "chain _ (?s i)")
proof
  note * = seq_fill_condD[OF assms]
  fix j
  show "(?s i j, ?s i (Suc j)) \<in> R"
  proof (induct j arbitrary: i rule: less_induct)
    case (less j)
    from * have len: "length (lseq i) > 1"..
    moreover
    { assume "Suc j < length (lseq i) - 1"
      with *[of i] have "(lseq i ! j, lseq i ! Suc j) \<in> R" by auto
    } moreover
    { assume "j < length (lseq i) - 1" "\<not> Suc j < length (lseq i) - 1"
      then have j: "j = length (lseq i) - 2" by auto
      from j chain_fill_condD(3)[OF *[of i]] len
      have "(lseq i ! j, lseq i ! Suc j) \<in> R" by (auto elim: allE[of _ j])
      also from j *[of i] len have "lseq i ! Suc j = seq (Suc i)" by auto
      also with *[of "Suc i"] have "... = concat_list_seq lseq (Suc i) 0"
        by(subst concat_list_seq.simps, auto simp: len Let_def)
      finally have "(lseq i ! j, concat_list_seq lseq (Suc i) 0) \<in> R".
    } moreover
    { assume "\<not> j < length (lseq i) - 1"
      then have j: "length (lseq i) \<le> Suc j" by auto
      with len have "(Suc j - length (lseq i)) < j" by auto
      from less[OF this, of "Suc i"]
      have "(concat_list_seq lseq (Suc i) (j - (length (lseq i) - 1)),
               concat_list_seq lseq (Suc i) (Suc j - (length (lseq i) - 1))) \<in> R"
        using j len by auto
    }
    ultimately show ?case
      by (subst concat_list_seq.simps,subst(2) concat_list_seq.simps, auto simp: Let_def)
  qed
qed

context indexed_rewriting begin

lemma traverse_union: assumes "(s,t) \<in> traverse R" "(t,u) \<in> traverse S"
  shows "(s,u) \<in> traverse (R \<union> S)"
proof -
  from assms(1) obtain i seq where seq: "seq 0 = s" "seq i = t" "traversed R seq i" by auto
  from assms(2) obtain j seq' where "traversed S seq' j" "seq' 0 = t" and u: "seq' j = u" by auto
  from this(1-2) have "\<exists> seq''. seq'' 0 = s \<and> seq'' (i+j) = seq' j \<and> traversed (R \<union> S) seq'' (i + j)"
  proof (induct rule: traversed.induct)
    case (base seq')
    then show ?case by (intro exI[of _ seq], auto simp: seq)
  next
    case (step S seq2 j r)
    from step(2)[OF step(4)] obtain seq'' where 
      seq'': "seq'' 0 = s" "seq'' (i+j) = seq2 j" and tr: "traversed (R \<union> S) seq'' (i+j)" 
      by auto
    let ?seq = "seq'' (i+Suc j := seq2 (Suc j))"
    have tr: "traversed (R \<union> S) ?seq (i+j)" 
      by (rule traversed_restrict[OF _ tr], auto)
    have tr: "traversed (insert r (R \<union> S)) ?seq (Suc (i+j))" 
      by (rule traversed.step[OF tr], auto simp: seq'' step(3))
    show ?case
      by (rule exI[of _ ?seq], insert tr, auto simp: seq'' fun_upd_def)
  qed  
  from this[unfolded u] show ?thesis unfolding traverse_def by auto
qed

definition traverse_fill_cond where
  "traverse_fill_cond R s t l \<equiv>
   let last = length l - 1 in
   last > 0 \<and> s = l ! 0 \<and> l ! last = t \<and>
   traversed R (\<lambda>i. l ! i) last"

lemma traverse_fill_condI[intro]:
  assumes "length l > 1"
    and "s = l ! 0"
    and "l ! (length l - 1) = t"
    and "traversed R (\<lambda>i. l ! i) (length l - 1)"
  shows "traverse_fill_cond R s t l"
  using assms by(auto simp: traverse_fill_cond_def Let_def)

lemma traverse_fill_condD[dest]:
  assumes "traverse_fill_cond R s t l"
  shows "length l > 1"
    and "s = l ! 0"
    and "l ! (length l - 1) = t"
    and "traversed R (\<lambda>i. l ! i) (length l - 1)"
  using assms[unfolded traverse_fill_cond_def Let_def] by auto

lemma traverse_concat:
  assumes *: "seq_fill_cond (traverse_fill_cond R) seq lseq"
  shows "recurring R (concat_list_seq lseq i)" (is "recurring R ?seq")
proof
  note * = traverse_fill_condD[OF seq_fill_condD[OF *]]
  note chain = traversed_imp_chain[OF *(4)]
  fix j
  have "\<forall>i. 1 < length (lseq i)" using *(1) by auto
  from shift_concat_list_seq[OF this, of i j] obtain i' j'
    where i'i: "i' \<ge> i"
      and j'j: "j' \<le> j"
      and j': "j' < length (lseq i')"
      and shift: "shift ?seq j = shift (concat_list_seq lseq i') j'" (is "_ = shift ?seq' _") by auto

  show "\<exists>k>0. traversed R (shift ?seq j) k"
    unfolding shift
  proof(intro exI conjI;(rule traversed_prefix; clarify?)?)
    let ?i = "Suc i'"
    let ?l = "\<lambda>i. length (lseq i) - 1"
    have "traversed R (concat_list_seq lseq ?i) (?l ?i)"
    proof(rule traversed_restrict)
      from *(4) show "traversed R (\<lambda>k. lseq ?i ! k) (?l ?i)" by auto
      from * show "\<And>k. k \<le> ?l ?i \<Longrightarrow> lseq ?i ! k = concat_list_seq lseq ?i k"
        by(subst (1 1) concat_list_seq.simps, auto simp:Let_def)
    qed
    also with * have "concat_list_seq lseq ?i = shift ?seq' (?l i')"
      by(intro ext, unfold shift.simps, subst(2) concat_list_seq.simps, auto simp:Let_def)
    also with j' have "... = shift (shift ?seq' j') (?l i' - j')" by auto
    finally show "traversed R ... (?l ?i)".
    show "0 < ?l i' - j' + ?l ?i" using j' *(1)[of ?i] by auto
    fix k
    assume k: "k < ?l i' - j'"
    with j' have kj': "k + j' < ?l i'" by auto
    { assume "?l i' = Suc (k + j')"
      from *(3)[of i', unfolded this *(2)]
      have "(lseq i' ! (k + j'), lseq (Suc i') ! 0) \<in> Induce R"
        using chain[OF kj'] by auto
    }
    then show "step (shift ?seq' j') k \<in> Induce R"
      unfolding shift.simps
      apply(subst(1 2) concat_list_seq.simps, unfold Let_def if_P[OF *(1)] if_P[OF kj'])
      apply(subst concat_list_seq.simps)
      using chain kj' *(1) by (auto simp: Let_def)
  qed auto
qed


lemma not_recurrent_on_imp_SN_on_traverse:
  assumes R: "R \<noteq> {}" and NR: "\<not> recurrent_on R X" shows "SN_on (traverse R) X"
proof
  fix seq assume 0: "seq 0 \<in> X" and chain: "chain (traverse R) seq"
  have "\<forall>i. \<exists>l.
    traverse_fill_cond R (seq i) (seq (Suc i)) l" (is "\<forall>i. \<exists>l. ?goal i l")
  proof
    fix i
    from chain have "(seq i, seq (Suc i)) \<in> traverse R" by auto
    then obtain seq' i'
      where start: "seq' 0 = seq i"
        and last: "seq' i' = seq (Suc i)"
        and tang: "traversed R seq' i'" by auto
    have i'0: "i' > 0" by(rule ccontr, insert tang R, auto)
    show "\<exists>l. ?goal i l"
    proof(rule exI, intro conjI chain_fill_condI traverse_fill_condI, subst refl)
      note [simp del] = upt_Suc
      let ?l = "map seq' [0..< Suc i']"
      from i'0 show "length ?l > 1" by auto
      from start show "seq i = ?l ! 0" by auto
      from last show "?l ! (length ?l - 1) = seq (Suc i)" by auto
      have len: "length ?l - 1 = i'" by auto
      from tang
      show "traversed R (\<lambda>i. ?l ! i) (length ?l - 1)"
      proof(unfold len, induct rule: traversed.induct)
        case base show ?case by auto
      next
        case (step R seq i' r) show ?case
        proof (rule traversed_restrict)
          show "j \<le> Suc i' \<Longrightarrow> seq j = map seq [0..<Suc (Suc i')] ! j" for j by auto
          from step show "traversed (insert r R) seq (Suc i')"
            by(auto intro: traversed.intros)
        qed
      qed
    qed
  qed
  from choice[OF this] obtain lseq where *: "\<forall>i. ?goal i (lseq i)" by auto
  let ?s = "concat_list_seq lseq 0"
  from * have "seq_fill_cond (traverse_fill_cond R) seq lseq" by auto
  then have "recurring R ?s" by (rule traverse_concat)
  moreover from * have "?s 0 = seq 0"
    by (subst concat_list_seq.simps, auto simp: Let_def elim!: allE[of _ 0])
  ultimately show False using NR[unfolded recurrent_on_def] 0 by auto
qed

lemma not_recurrent_on_iff_SN_on_traverse:
  "\<not> recurrent_on R X \<longleftrightarrow> R = {} \<or> SN_on (traverse R) X"
  using not_recurrent_on_imp_SN_on_traverse SN_on_traverse_imp_not_recurrent_on by auto


subsection \<open>Cooperation Chains\<close>

(* a cooperation chain consists of a finite initial part and ends in
  an infinite run using transitions which are used infinitely often *)
definition cooperation_chain where
  "cooperation_chain R P seq \<equiv>
   \<exists>cp.
     (\<forall>i < cp. (seq i, seq (Suc i)) \<in> Induce R) \<and>
     (\<exists>\<tau>s \<subseteq> P. recurring \<tau>s (shift seq cp))"

lemma cooperation_chainI[intro]:
  assumes "\<tau>s \<subseteq> P" "recurring \<tau>s (shift seq cp)"
    "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R"
  shows "cooperation_chain R P seq"
  using assms unfolding cooperation_chain_def by auto

lemma cooperation_chainE[elim]:
  assumes "cooperation_chain R P seq"
  obtains cp P'
  where "P' \<subseteq> P"
    "recurring P' (shift seq cp)"
    "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R"
  using assms unfolding cooperation_chain_def by auto

lemma cooperation_chain_empty: "cooperation_chain {} P seq \<longleftrightarrow> (\<exists>P' \<subseteq> P. recurring P' seq)" (is "?l \<longleftrightarrow> ?r")
proof (intro iffI)
  assume ?l then obtain cp P'
    where 1: "P' \<subseteq> P" "recurring P' (shift seq cp)" and 2: "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce {}"
    by (elim cooperation_chainE, force)
  from 2 have "cp = 0" by auto
  with 1 show ?r by auto
next
  assume ?r then obtain P' where "P' \<subseteq> P" "recurring P' seq" by auto
  then show ?l by (intro cooperation_chainI[of P' _ _ 0], auto)
qed

lemma cooperation_chain_empty2[simp]: "\<not> cooperation_chain R {} seq" by(auto simp: cooperation_chain_def)

definition "cooperation_SN_on R P X \<equiv> \<not> (\<exists>seq. seq 0 \<in> X \<and> cooperation_chain R P seq)"

lemma cooperation_SN_onI[intro]:
  assumes "\<And>seq. seq 0 \<in> X \<Longrightarrow> cooperation_chain R P seq \<Longrightarrow> False"
  shows "cooperation_SN_on R P X" using assms by (auto simp: cooperation_SN_on_def)

lemma cooperation_SN_onE[elim]:
  "cooperation_SN_on R P X \<Longrightarrow> seq 0 \<in> X \<Longrightarrow> cooperation_chain R P seq \<Longrightarrow> False"
  by (auto simp: cooperation_SN_on_def)

lemma cooperation_SN_on_image:
  "cooperation_SN_on {} P (Induces R `` X) \<longleftrightarrow> cooperation_SN_on R P X" (is "?l \<longleftrightarrow> ?r")
proof(intro iffI cooperation_SN_onI)
  fix seq assume seq0: "seq 0 \<in> Induces R `` X" and chain: "cooperation_chain {} P seq"
  from seq0 obtain x n where xX: "x \<in> X" and "(x, seq 0) \<in> Induce R ^^ n" by auto
  then obtain pre
    where 0: "pre 0 = x"
      and 1: "\<And>i. i < n \<Longrightarrow> (pre i, pre (Suc i)) \<in> Induce R"
      and 2: "pre n = seq 0" by (metis relpow_seq)
  from chain obtain cp P'
    where P'P: "P' \<subseteq> P"
      and tang: "recurring P' (shift seq cp)"
      and 3: "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce {}" by (elim cooperation_chainE, auto)
  show "?r \<Longrightarrow> False"
  proof (elim cooperation_SN_onE)
    let ?seq = "\<lambda>i. if i < n then pre i else seq (i-n)"
    show "cooperation_chain R P ?seq"
    proof(rule cooperation_chainI[OF P'P])
      from tang show "recurring P' (shift ?seq (n+cp))" by auto
      fix i assume i: "i < n + cp"
      show "(?seq i, ?seq (Suc i)) \<in> Induce R"
      proof (cases "Suc i" "n" rule: linorder_cases)
        case less with 1 show ?thesis by auto
      next
        case equal with 1 show ?thesis by (auto simp: 2[symmetric])
      next
        case greater
        from greater have [simp]: "Suc (i - n) = Suc i - n" by auto
        from greater i have "i - n < cp" by auto
        from greater 3[OF this] show ?thesis by auto
      qed
    qed
    show "?seq 0 \<in> X" using 0 xX 2 by auto
  qed
next
  fix seq
  assume 0: "seq 0 \<in> X" and chain: "cooperation_chain R P seq"
  from chain obtain cp P'
    where 1: "\<And>i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R"
      and P'P: "P' \<subseteq> P"
      and tang: "recurring P' (shift seq cp)"
    by (elim cooperation_chainE, auto)
  show "?l \<Longrightarrow> False"
  proof(elim cooperation_SN_onE)
    have "n \<le> cp \<Longrightarrow> (seq 0, seq n) \<in> Induce R ^^ n" for n using 1 by(induct n, auto)
    then have "(seq 0, seq cp) \<in> Induces R" using relpow_imp_rtrancl by blast
    then have "seq cp \<in> Induces R `` X" using 0 by auto
    then show "shift seq cp 0 \<in> ..." by auto
    from tang show "cooperation_chain {} P (shift seq cp)"
      using cooperation_chainI[OF P'P, of "shift seq cp" 0 "{}"] by auto
  qed
qed

lemma cooperation_SN_on_as_not_recurrent_on:
  "cooperation_SN_on R P X \<longleftrightarrow> (\<forall> P' \<subseteq> P. \<not> recurrent_on P' (Induces R `` X))" (is "_ = ?r")
proof-
  have "cooperation_SN_on {} P (Induces R `` X) \<longleftrightarrow> ?r" (is "?l \<longleftrightarrow> _")
  proof
    assume SN: ?l
    show ?r
    proof (intro allI impI notI, elim recurrent_onE)
      fix P' seq
      assume P'P: "P'\<subseteq> P" and 0: "seq 0 \<in> Induces R `` X" and tang: "recurring P' seq"
      from SN 0 show False
      proof(elim cooperation_SN_onE)
        from tang show "cooperation_chain {} P seq" by (intro cooperation_chainI[OF P'P], auto)
      qed
    qed
  next
    assume NR: ?r show ?l
    proof
      fix seq
      assume 0: "seq 0 \<in> (Induce R)\<^sup>* `` X" and chain: "cooperation_chain {} P seq"
      from chain obtain P' cp
        where P'P: "P' \<subseteq> P"
          and tang: "recurring P' (shift seq cp)"
          and chain: "\<And>i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce {}" by (elim cooperation_chainE, auto)
      from chain have "cp = 0" by auto
      with tang have "recurring P' seq" by auto
      with 0 P'P NR show False by auto
    qed
  qed
  then show ?thesis unfolding cooperation_SN_on_image by auto
qed

lemma cooperation_SN_on_as_SN_on_traverse:
  "cooperation_SN_on R P X \<longleftrightarrow> (\<forall>P' \<subseteq> P. P' \<noteq> {} \<longrightarrow> SN_on (traverse P') (Induces R `` X))"
  unfolding cooperation_SN_on_as_not_recurrent_on not_recurrent_on_iff_SN_on_traverse by auto

theorem SN_on_as_cooperation_SN_on:
  assumes fin: "finite R"
  shows "SN_on (Induce R) X \<longleftrightarrow> cooperation_SN_on R R X" (is "?r \<longleftrightarrow> ?l")
proof(rule iffI)
  assume l: ?l show ?r
  proof(rule ccontr)
    assume "\<not>?thesis"
    from not_SN_on_imp_recurrent_on[OF fin this]
    have "\<not> cooperation_SN_on R R X" by (auto simp: cooperation_SN_on_as_not_recurrent_on)
    with l show False by auto
  qed
next
  assume r: ?r show ?l
  proof (rule ccontr)
    assume "\<not>?thesis"
    then obtain seq
      where 0: "seq 0 \<in> X" and "cooperation_chain R R seq" by auto
    then obtain R' cp
      where R'R: "R' \<subseteq> R" and pre: "\<forall>i < cp. (seq i, seq (Suc i)) \<in> Induce R"
        and post: "recurring R' (shift seq cp)" by auto
    have "chain (Induce R) seq"
    proof(intro allI)
      fix i
      show "step seq i \<in> Induce R"
      proof (cases "i < cp")
        case True then show ?thesis using pre by auto
      next
        case False then have "(i - cp) + cp = i" by auto
        moreover
        have "chain (Induce R) (shift seq cp)"
        proof(rule chain_mono)
          from recurring_imp_chain[OF post] show "chain (Induce R') (shift seq cp)" by auto
          from R'R show "Induce R' \<subseteq> Induce R" by auto
        qed
        then have "step (shift seq cp) (i-cp) \<in> Induce R" by auto
        ultimately show ?thesis by auto
      qed
    qed
    with r 0 show False by blast
  qed
qed

lemma cooperation_chain_subset_1:
  assumes sub: "R' \<subseteq> R" and chain: "cooperation_chain R' P seq"
  shows "cooperation_chain R P seq"
proof-
  from chain obtain cp \<tau>s
    where 1: "\<tau>s \<subseteq> P" "recurring \<tau>s (shift seq cp)"
      and *: "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R'" by auto
  { fix i assume "i < cp"
    with * have "(seq i, seq (Suc i)) \<in> Induce R'" by auto
    with UN_mono[OF sub, of induce induce] * have "(seq i, seq (Suc i)) \<in> Induce R" by auto
  }
  with 1 show ?thesis by (intro cooperation_chainI)
qed

lemma cooperation_chain_subset_2:
  assumes sub: "P' \<subseteq> P" and chain: "cooperation_chain R P' seq"
  shows "cooperation_chain R P seq"
proof-
  from chain obtain cp \<tau>s
    where 1: "\<tau>s \<subseteq> P'"
      and *: "recurring \<tau>s (shift seq cp)" "\<And> i. i < cp \<Longrightarrow> (seq i, seq (Suc i)) \<in> Induce R" by auto
  from 1 sub have "\<tau>s \<subseteq> P" by auto
  with * show ?thesis by (intro cooperation_chainI)
qed

lemma cooperation_SN_on_subset_1:
  assumes sub: "R' \<subseteq> R" and SN: "cooperation_SN_on R P X"
  shows "cooperation_SN_on R' P X"
  using cooperation_chain_subset_1[OF sub, of P] SN
  by(intro cooperation_SN_onI, elim cooperation_SN_onE, auto)

lemma cooperation_SN_on_subset_2:
  assumes sub: "P' \<subseteq> P" and SN: "cooperation_SN_on R P X"
  shows "cooperation_SN_on R P' X"
  using cooperation_chain_subset_2[OF sub, of R] SN
  by(intro cooperation_SN_onI, elim cooperation_SN_onE, auto)

lemma cooperation_SN_on_subset_3:
  assumes sub: "X' \<subseteq> X" and SN: "cooperation_SN_on R P X"
  shows "cooperation_SN_on R P X'" 
  using assms unfolding cooperation_SN_on_def by auto

lemma cooperation_SN_on_subset:
  assumes 1: "R' \<subseteq> R" and 2: "P' \<subseteq> P" and 3: "X' \<subseteq> X" and SN: "cooperation_SN_on R P X"
  shows "cooperation_SN_on R' P' X'"
  by (rule cooperation_SN_on_subset_1[OF 1 cooperation_SN_on_subset_2[OF 2 cooperation_SN_on_subset_3[OF 3 SN]]])

context
  fixes R S
  assumes push: "\<And>r. r \<in> R \<Longrightarrow> S O induce r \<subseteq> induce r O S\<^sup>*"
begin

interpretation I': indexed_rewriting "\<lambda>r. induce r O S\<^sup>*".

lemma traversed_push:
  assumes "I'.traversed R seq' i"
  shows "\<exists>seq. seq 0 = seq' 0 \<and> traversed R seq i \<and> (seq i, seq' i) \<in> S\<^sup>*" (is "?goal R")
proof-
  have "I'.traversed P seq' i \<Longrightarrow> P \<subseteq> R \<Longrightarrow> ?goal P" for P
  proof(induct rule: I'.traversed.induct)
    case (base seq') show ?case by (auto intro: traversed.intros)
  next
    case (step P seq' i r)
    then obtain seq
      where 0: "seq 0 = seq' 0"
        and 1: "traversed P seq i"
        and 2: "(seq i, seq' i) \<in> S\<^sup>*" by auto
    from step have rR: "r \<in> R" by auto
    from 2 step have "(seq i, seq' (Suc i)) \<in> S\<^sup>* O induce r O S\<^sup>*" by auto
    also have "... \<subseteq> induce r O S\<^sup>* O S\<^sup>*" using rtrancl_O_push[OF push[OF rR]] by fast
    also have "... \<subseteq> induce r O S\<^sup>*" by auto
    finally obtain s where **: "(seq i, s) \<in> induce r" "(s, seq' (Suc i)) \<in> S\<^sup>*" by auto
    let ?seq = "\<lambda>j. if j \<le> i then seq j else s"
    from 0 traversed_restrict[OF _ 1, of ?seq] **
    show ?case by (intro exI[of _ ?seq], auto intro: traversed.intros)
  qed
  from this[of R] assms show ?thesis by auto
qed


lemma traverse_push2: "I'.traverse R \<subseteq> traverse R O S\<^sup>*" (is "?L \<subseteq> ?R")
proof(cases "R = {}")
  case True
  then show ?thesis by auto
next
  case False show ?thesis
  proof
    fix s t assume "(s,t) \<in> ?L"
    then obtain seq' i
      where 0: "seq' 0 = s"
        and 1: "I'.traversed R seq' i"
        and 2: "seq' i = t" by auto
    from traversed_push[OF 1] obtain seq
      where "seq 0 = seq' 0" "traversed R seq i" and 4: "(seq i, seq' i) \<in> S\<^sup>*" by auto
    with 0 have "(s,seq i) \<in> traverse R" by (auto intro: mem_traverseI)
    with 2 4 show "(s,t) \<in> ?R" by auto
  qed
qed

lemma traverse_push: "S\<^sup>* O traverse R \<subseteq> traverse R O S\<^sup>*" (is "?L \<subseteq> ?R")
proof(cases "R = {}")
  case True then show ?thesis by auto
next
  case False show ?thesis
  proof
    fix s t assume "(s,t) \<in> ?L"
    then obtain u where su: "(s,u) \<in> S\<^sup>*" and ut: "(u,t) \<in> traverse R" by auto
    note ut
    also have "traverse R \<subseteq> I'.traverse R" by (rule traverse_mono, auto)
    finally have"(u,t)\<in> I'.traverse R".
    from this obtain seq' i
      where 0: "seq' 0 = u"
        and 1: "I'.traversed R seq' i"
        and 2: "seq' i = t" by auto
    have "I'.traversed P seq' i \<Longrightarrow> P \<subseteq> R \<Longrightarrow> seq' 0 = u \<Longrightarrow>
      (s, seq' i) \<in> {(seq 0, seq i) | seq i. traversed P seq i} O S\<^sup>*" for P
    proof(induct rule: I'.traversed.induct)
      case (base seq') with su show ?case
        by (auto intro!: relcompI[of _ "s"] exI[of _ "\<lambda>_. s"] traversed.intros)
    next
      case (step P seq' i r)
      then have rR: "r \<in> R"
        and *: "(s, seq' i) \<in> {(seq 0, seq i) | seq i. traversed P seq i} O S\<^sup>*" by auto
      then obtain v
        where sv: "(s, v) \<in> {(seq 0, seq i) | seq i. traversed P seq i}"
          and vs'i: "(v, seq' i) \<in> S\<^sup>*" by auto
      then obtain seq i'
        where s: "s = seq 0" and vsi': "v = seq i'" and tang: "traversed P seq i'" by auto
      from vs'i step have "(v, seq' (Suc i)) \<in> S\<^sup>* O induce r O S\<^sup>*" by auto
      also have "... \<subseteq> induce r O S\<^sup>* O S\<^sup>*" using rtrancl_O_push[OF push, OF rR] by force
      also have "... \<subseteq> induce r O S\<^sup>*" by auto
      finally have "(v,seq' (Suc i)) \<in> ...".
      then obtain w where vw: "(v,w) \<in> induce r" and wS: "(w, seq' (Suc i)) \<in> S\<^sup>*" by auto
      let ?seq = "\<lambda>j. if j \<le> i' then seq j else w"
      have "traversed (insert r P) ?seq (Suc i')"
        apply(rule traversed.intros)
         apply(rule traversed_restrict[of _ seq])
        using tang vs'i vsi' vw by auto
      with s wS show ?case
        apply (intro relcompI[of _ w])
        by (auto intro!: exI[of _ ?seq] exI[of _ "Suc i'"])
    qed
    from 0 this[OF 1] 2 show "(s,t) \<in> ?R" by (auto intro: mem_traverseI)
  qed
qed

end



end

context
  fixes P P' R :: "'a set" and induce induce' :: "'a \<Rightarrow> ('b \<times> 'b) set"
begin

interpretation I: indexed_rewriting induce.
interpretation I': indexed_rewriting induce'.

context
  assumes simulation_P: "\<And>r. r \<in> P \<Longrightarrow> \<exists> ps. ps \<noteq> {} \<and> ps \<subseteq> P' \<and> induce r \<subseteq> I'.traverse ps"
    and simulation_R: "\<And> r. r \<in> R \<Longrightarrow> induce r = induce' r" 
begin

qualified lemma Induce_R_eq: "I.Induce R = I'.Induce R" 
  using simulation_R by auto

qualified definition r_to_ps :: "'a \<Rightarrow> 'a set" where 
  "r_to_ps r = (SOME ps. ps \<noteq> {} \<and> ps \<subseteq> P' \<and> induce r \<subseteq> I'.traverse ps)"

lemma r_to_ps: assumes "r \<in> P" shows 
  "r_to_ps r \<subseteq> P'" 
  "r_to_ps r \<noteq> {}" 
  "induce r \<subseteq> I'.traverse (r_to_ps r)"
proof -
  let ?P = "\<lambda> ps. ps \<noteq> {} \<and> ps \<subseteq> P' \<and> induce r \<subseteq> I'.traverse ps" 
  from simulation_P[OF assms] obtain ps where "?P ps" by auto
  from someI[of ?P ps, OF this, folded r_to_ps_def] have "?P (r_to_ps r)" by auto
  then show "r_to_ps r \<subseteq> P'" "r_to_ps r \<noteq> {}" "induce r \<subseteq> I'.traverse (r_to_ps r)" by auto
qed

lemma r_to_ps_traverse: assumes "Q \<subseteq> P" 
  shows "I.traverse Q \<subseteq> I'.traverse (\<Union> (r_to_ps ` Q))" 
proof 
  fix s t
  assume "(s,t) \<in> I.traverse Q" 
  from this[unfolded I.traverse_def]
  obtain seq i where st: "s = seq 0" "t = seq i" and tr: "I.traversed Q seq i" by auto
  from tr assms have "(seq 0, seq i) \<in> I'.traverse (\<Union> (r_to_ps ` Q))"
  proof (induct rule: I.traversed.induct)
    case (step Q seq i r)
    from step(2,4) have IH: "(seq 0, seq i) \<in> I'.traverse (\<Union>(r_to_ps ` Q))" by auto
    from step(4) have "r \<in> P" by auto
    note r_to_ps = r_to_ps[OF this]
    from step(3) r_to_ps(3) have "(seq i, seq (Suc i)) \<in> I'.traverse (r_to_ps r)" by auto
    from I'.traverse_union[OF IH this] show ?case by (simp add: Un_commute Union_image_insert)
  qed auto
  with st show "(s,t) \<in> I'.traverse (\<Union> (r_to_ps ` Q))" by simp
qed

lemma cooperation_SN_on_trancl_image: assumes "I'.cooperation_SN_on R P' X"
  shows "I.cooperation_SN_on R P X"
  unfolding I.cooperation_SN_on_as_SN_on_traverse
proof (intro impI allI)
  fix Q
  assume Q: "Q \<subseteq> P" "Q \<noteq> {}" 
  define Q' where "Q' = \<Union> (r_to_ps ` Q)"
  have QP': "Q' \<subseteq> P'" using r_to_ps Q unfolding Q'_def by blast+
  have Q': "Q' \<noteq> {}" using r_to_ps Q unfolding Q'_def by fast
  from r_to_ps_traverse[OF Q(1), folded Q'_def] have sub: "I.traverse Q \<subseteq> I'.traverse Q'" by auto
  from assms[unfolded I'.cooperation_SN_on_as_SN_on_traverse, rule_format, OF QP' Q']
  have "SN_on (I'.traverse Q') ((I'.Induce R)\<^sup>* `` X)" by auto
  from SN_on_subset1[OF this sub]
  show "SN_on (I.traverse Q) ((I.Induce R)\<^sup>* `` X)" unfolding Induce_R_eq .
qed

end
end


context
  fixes P R :: "'a1 set" and P' R' :: "'a2 set" and induce :: "'a1 \<Rightarrow> ('b1 \<times> 'b1) set"
    and induce' :: "'a2 \<Rightarrow> ('b2 \<times> 'b2) set" 
    and I :: "'b1 set" and I' :: "'b2 set" 
begin

interpretation I: indexed_rewriting induce.
interpretation I': indexed_rewriting induce'.

lemma cooperation_SN_on_simulation: assumes init: "B ` I \<subseteq> I'"
  and stepP: "\<And> a b1 b2. a \<in> P \<Longrightarrow> (b1,b2) \<in> induce a \<Longrightarrow> {b1,b2} \<subseteq> (I.Induce (R \<union> P))^* `` I \<Longrightarrow> 
    A a \<in> P' \<and> (B b1, B b2) \<in> induce' (A a)" 
  and stepR: "\<And> a b1 b2. a \<in> R \<Longrightarrow> (b1,b2) \<in> induce a \<Longrightarrow> {b1,b2} \<subseteq> (I.Induce (R \<union> P))^* `` I \<Longrightarrow> 
    A a \<in> R' \<and> (B b1, B b2) \<in> induce' (A a)" 
  and SN: "I'.cooperation_SN_on R' P' I'" 
shows "I.cooperation_SN_on R P I" 
proof
  fix b
  assume I: "b 0 \<in> I" and b: "I.cooperation_chain R P b" 
  let ?reach = "(I.Induce (R \<union> P))^* `` I" 
  from I.cooperation_chainE[OF b] obtain cp PP where PP: "PP \<subseteq> P" and rec: "I.recurring PP (shift b cp)" 
    and R: "\<And>i. i < cp \<Longrightarrow> (b i, b (Suc i)) \<in> I.Induce R" by metis
  define b' where "b' = shift b cp" 
  let ?b = "\<lambda> i. B (b i)" 
  let ?b' = "\<lambda> i. B (b' i)"  
  have b': "?b' = shift (\<lambda>i. B (b i)) cp" unfolding b'_def by simp
  have reach_step: "i \<le> cp \<Longrightarrow> b i \<in> ?reach \<and> (i \<noteq> 0 \<longrightarrow> (?b (i - 1), ?b i) \<in> I'.Induce R')" for i
  proof (induct i)
    case (Suc i)
    then have i: "i < cp" "i \<le> cp" by auto
    from R[OF i(1)] have "(b i, b (Suc i)) \<in> I.Induce (R \<union> P)" by simp
    with Suc(1)[OF i(2)] have bsi: "b (Suc i) \<in> ?reach" by (metis rtrancl_image_advance)
    from R[OF i(1)] obtain a where "a \<in> R" and "(b i, b (Suc i)) \<in> induce a" by auto
    from stepR[OF this] Suc(1)[OF i(2)] bsi have "A a \<in> R'" "(?b i, ?b (Suc i)) \<in> induce' (A a)" 
      by auto
    then have "(?b i, ?b (Suc i)) \<in> I'.Induce R'" by auto
    with bsi show ?case by auto
  qed (auto simp: I)
  have R: "i < cp \<Longrightarrow> (?b i, ?b (Suc i)) \<in> I'.Induce R'" for i using reach_step[of "Suc i"] by auto
  have b'0: "b' 0 \<in> ?reach" using reach_step[of cp] unfolding b'_def by simp
  note rec = rec[folded b'_def]
  have chain: "I'.cooperation_chain R' P' ?b" 
  proof (rule I'.cooperation_chainI[of "A ` PP" _ ?b cp, OF _ _ R, folded b'])
    from I.recurring_imp_chain[OF rec] have steps: "\<And> i. (b' i, b' (Suc i)) \<in> I.Induce (R \<union> P)" using PP by auto
    have reach: "b' i \<in> ?reach" for i 
    proof (induct i)
      case (Suc i)
      from Suc steps[of i] show ?case by (metis rtrancl_image_advance)
    qed (rule b'0)
    have reach: "{b' i, b' (Suc i)} \<subseteq> ?reach" for i using reach by auto
    {
      fix i
      from I.recurringD[OF rec, of i] obtain j where "j > 0" and trav: "I.traversed PP (shift b' i) j" by auto
      define b where "b = (shift b' i)" 
      have "b j \<in> ?reach" for j using reach[of "j + i"] unfolding b_def by auto
      then have "{b j, b (Suc j)} \<subseteq> ?reach" for j by auto
      note stepP = stepP[OF _ _ this]
      let ?b = "\<lambda> i. B (b i)" 
      from trav[folded b_def] PP stepP have "A ` PP \<subseteq> P' \<and> I'.traversed (A ` PP) ?b j"
      proof (induct rule: I.traversed.induct)
        case (step PP b i a)
        from step have a: "a \<in> P" by auto
        from step(5)[OF a step(3)] have stepP: "A a \<in> P' \<and> (B (b i), B (b (Suc i))) \<in> induce' (A a)" .
        from step have "PP \<subseteq> P" by auto
        from step(2)[OF this step(5)] have IH: "A ` PP \<subseteq> P' \<and> I'.traversed (A ` PP) (\<lambda>i. B (b i)) i" .
        show ?case using stepP IH by (auto intro: I'.traversed.step)
      qed auto        
      with \<open>j > 0\<close>
      have "A ` PP \<subseteq> P' \<and> (\<exists>j>0. I'.traversed (A ` PP) (shift ?b' i) j)" unfolding b_def by auto
    } note main = this
    from main show "A ` PP \<subseteq> P'" by auto
    from main show "I'.recurring (A ` PP) ?b'" unfolding I'.recurring_def by auto
  qed
  show False
    by (rule I'.cooperation_SN_onE[OF SN _ chain], insert I init, auto)
qed
end

end
