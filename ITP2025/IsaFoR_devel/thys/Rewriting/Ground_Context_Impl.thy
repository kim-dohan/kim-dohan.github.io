(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Ground_Context_Impl
imports
  First_Order_Rewriting.Term_Impl
  Ground_Context
  First_Order_Terms.Unification_String
  Auxx.Name
  First_Order_Terms.Option_Monad
begin

no_notation Subterm_and_Context.Hole ("\<box>")
notation Ground_Context.GCHole ("\<box>")
notation Ground_Context.equiv_class ("[_]")

derive compare_order gctxt

instantiation gctxt :: (showl, type) showl
begin

fun showsl_gctxt where
  "showsl_gctxt GCHole = showsl (STR ''_'')" |
  "showsl_gctxt (GCFun f ts) =
     showsl f \<circ> showsl_list_gen id (STR '''') (STR ''('') (STR '', '') (STR '')'') (map showsl_gctxt ts)"
definition "showsl_list (xs :: ('a,'b)gctxt list) = default_showsl_list showsl xs"
instance ..
end


subsection \<open>Implementing Ground Context Matching\<close>
context begin

(* avoid sequential mode to reduce number of simp rules, induction cases, ...*)
function
  merge_lists :: "('f, 'v) gctxt list \<Rightarrow> ('f, 'v) gctxt list \<Rightarrow> ('f, 'v) gctxt list option"
where
  "merge_lists [] []  = Some []"
| "merge_lists (\<box>#Cs) (D#Ds) = do { Es \<leftarrow> merge_lists Cs Ds; Some (D # Es) }"
| "merge_lists (C#Cs) (\<box>#Ds) = do { Es \<leftarrow> merge_lists Cs Ds; Some (C # Es) }"
| "merge_lists (GCFun f ss # Cs) (GCFun f ts # Ds) = do {
    us \<leftarrow> merge_lists ss ts;
    Es \<leftarrow> merge_lists Cs Ds;
    Some (GCFun f us # Es)
  }"
| "f \<noteq> g \<Longrightarrow> merge_lists (GCFun f ss # Cs) (GCFun g ts # Ds) = None"
| "merge_lists [] (D#Ds) = None"
| "merge_lists (C#Cs) [] = None"
proof (clarsimp split: prod.splits)
  fix P and xs ys :: "('f,'v)gctxt list"
  assume 1: "xs = [] \<and> ys = [] \<Longrightarrow> P"
    and 2: "\<And>Cs D Ds. xs = \<box>#Cs \<and> ys = D#Ds \<Longrightarrow> P"
    and 3: "\<And>C Cs Ds. xs = C#Cs \<and> ys = \<box>#Ds \<Longrightarrow> P"
    and 4: "\<And>f ss Cs ts Ds. xs = GCFun f ss # Cs \<and> ys = GCFun f ts # Ds \<Longrightarrow> P"
    and 5: "\<And>f g ss Cs ts Ds. \<lbrakk>f \<noteq> g; xs = GCFun f ss # Cs \<and> ys = GCFun g ts # Ds\<rbrakk> \<Longrightarrow> P"
    and 6: "\<And>D Ds. xs = [] \<and> ys = D#Ds \<Longrightarrow> P"
    and 7: "\<And>C Cs. xs = C#Cs \<and> ys = [] \<Longrightarrow> P"
  show P
  proof (cases xs)
    case Nil then show ?thesis using 1 6 by (cases ys) (blast)+
  next
    case (Cons z zs) show ?thesis
    proof (cases ys)
      case Nil then show ?thesis using Cons 7 by blast
    next
      note Cons' = Cons
      case (Cons u us) show P
      proof (cases z)
        case GCHole with Cons Cons' 2 show ?thesis by blast
      next
        case (GCFun f ss) show ?thesis
        proof (cases u)
          case GCHole with Cons Cons' 3 show ?thesis by blast
        next
          note GCFun' = GCFun
          case (GCFun g ts)
          from 4[of f ss zs ts us] and 5[of f g ss zs ts us]
            show ?thesis unfolding Cons Cons' GCFun GCFun' by (cases "f = g") simp_all
        qed
      qed
    qed
  qed
qed force+
termination by lexicographic_order

declare merge_lists.simps[code del]

(* code generation does not handle conditional equations, for simplification
they are, however, convenient *)
lemma merge_lists_code_simps[code]:
  "merge_lists [] [] = Some []"
  "merge_lists (\<box>#Cs) (D#Ds) = do { Es \<leftarrow> merge_lists Cs Ds; Some (D # Es) }"
  "merge_lists (C#Cs) (\<box>#Ds) = do { Es \<leftarrow> merge_lists Cs Ds; Some (C # Es) }"
  "merge_lists (GCFun f ss # Cs) (GCFun g ts # Ds) = do {
    guard (f = g);
    us \<leftarrow> merge_lists ss ts;
    Es \<leftarrow> merge_lists Cs Ds;
    Some (GCFun f us # Es)
  }"
  "merge_lists [] (D#Ds) = None"
  "merge_lists (C#Cs) [] = None"
  by (simp_all add: guard_def)

lemma merge_lists_length:
  assumes "merge_lists Cs Ds = Some Es"
  shows "length Cs = length Ds"
  using assms by (induct Cs Ds arbitrary: Es rule: merge_lists.induct) force+

lemma merge_lists_length':
  assumes "merge_lists Cs Ds = Some Es"
  shows "length Cs = length Es"
  using assms by (induct Cs Ds arbitrary: Es rule: merge_lists.induct) (auto split: bind_splits)

lemma merge_lists_GCHole[simp]:
  "merge_lists (\<box>#Cs) (D#Ds) = Some Es
    \<longleftrightarrow> (\<exists>Es'. Es = D#Es' \<and> merge_lists Cs Ds = Some Es')"
  "merge_lists (C#Cs) (\<box>#Ds) = Some Es
    \<longleftrightarrow> (\<exists>Es'. Es = C#Es' \<and> merge_lists Cs Ds = Some Es')"
  "merge_lists (GCFun f ss#Cs) (GCFun g ts#Ds) = Some Es
    \<longleftrightarrow> f = g \<and> (\<exists>us. merge_lists ss ts = Some us
     \<and> (\<exists>Es'. Es = GCFun f us # Es' \<and> merge_lists Cs Ds = Some Es'))" 
    apply (force split: bind_splits)
   apply (force split: bind_splits)
  apply (cases "f = g")
   apply (auto split: bind_splits)
  done

lemma merge_lists_ident[simp]: "merge_lists Cs Cs = Some Cs"
proof (induct "size_list size Cs" arbitrary: Cs rule: nat_less_induct)
  case 1
  note IH = 1[rule_format]
  show ?case
  proof (cases Cs)
    case Nil then show ?thesis by simp
  next
    case (Cons D Ds)
    show ?thesis
    proof (cases D)
      case GCHole show ?thesis using IH by (force simp: GCHole Cons)
    next
      case (GCFun f Es)
      have "size_list size Es < size_list size Cs" by (simp add: Cons GCFun)
      from IH[OF this] have Es: "merge_lists Es Es = Some Es" by simp
      have "size_list size Ds < size_list size Cs" by (simp add: Cons GCFun)
      from IH[OF this] have "merge_lists Ds Ds = Some Ds" by simp
      with Es show ?thesis by (simp add: Cons GCFun)
    qed
  qed
qed

lemma merge_lists_sound:
  assumes "merge_lists Cs Ds = Some Es" and "i < length Cs"
  shows "[Cs ! i] \<inter> [Ds ! i] = [Es ! i]"
using assms
proof (induct Cs Ds arbitrary: i Es rule: merge_lists.induct)
  case (2 Cs D Ds i Es)
  from 2(2) obtain Es' where Es: "Es = D#Es'" and "merge_lists Cs Ds = Some Es'" by (auto split: bind_splits)
  from 2(1)[OF this(2)] have IH: "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Es'!i]" by simp
  show ?case unfolding Es using 2(3) and IH by (cases i) simp_all
next
  case (3 C Cs Ds i Es)
  from 3(2) obtain Es' where Es: "Es = C#Es'" and "merge_lists Cs Ds = Some Es'" by (auto split: bind_splits)
  from 3(1)[OF this(2)] have IH: "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Es'!i]" by simp
  show ?case unfolding Es using 3(3) and IH by (cases i) simp_all
next
  case (4 f ss Cs ts Ds i Es)
  from 4(3) obtain us and Es'
    where us: "merge_lists ss ts = Some us" and Es: "Es = GCFun f us # Es'"
    and "merge_lists Cs Ds = Some Es'" by (auto split: bind_splits)
  from 4(2)[OF us this(3)]
    have IH: "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Es'!i]" by simp
  from 4(1)[simplified, OF us] have args: "\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i]" by simp
  then have eq: "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us]"
    by (simp add: merge_lists_length[OF us, symmetric] merge_lists_length'[OF us, symmetric])
       blast
  show ?case unfolding Es using 4(4) and IH and eq by (cases i) simp_all
qed simp_all

lemma merge_lists_bind_None[simp]:
  "merge_lists Cs Ds \<bind> f = None
    \<longleftrightarrow> merge_lists Cs Ds = None \<or> (\<exists>Es. merge_lists Cs Ds = Some Es \<and> f Es = None)"
  by (cases "merge_lists Cs Ds") simp_all

lemma merge_lists_None:
  assumes "merge_lists Cs Ds = None"
  shows "length Cs \<noteq> length Ds \<or> (\<exists>i<length Cs. [Cs!i] \<inter> [Ds!i] = {})"
using assms
proof (induct Cs Ds rule: merge_lists.induct)
  case (4 f ss Cs ts Ds)
  show ?case
  proof (cases "merge_lists ss ts")
    case None
    with 4(1) have "length ss \<noteq> length ts \<or> (\<exists>i<length ss. [ss!i] \<inter> [ts!i] = {})" by simp
    then show ?thesis by (rule disjE) (force+)
  next
    case (Some us)
    with 4(2,3) have "length Cs \<noteq> length Ds \<or> (\<exists>i<length Cs. [Cs!i] \<inter> [Ds!i] \<subseteq> {})" by force
    then show ?thesis by force
  qed
qed force+

lemma equiv_class_Int_GCFun_length:
  "[GCFun f ss] \<inter> [GCFun f ts] \<noteq> {} \<Longrightarrow> length ss = length ts" by auto

lemma equiv_class_Int:
  assumes "\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i]"
    and "length ss = length ts"
    and "length ss = length us"
  shows "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us]" (is "?S \<inter> ?T = ?U")
  using assms by fastforce

lemma equiv_class_Int_conv':
  assumes "[GCFun f ss] \<inter> [GCFun f ts] \<noteq> {}"
  shows "\<exists>us. merge_lists ss ts = Some us \<and> [GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us]"
proof (cases "merge_lists ss ts")
  case None
  from merge_lists_None[OF this] and equiv_class_Int_GCFun_length[OF assms]
    have "\<exists>i<length ss. [ss!i] \<inter> [ts!i] = {}" by blast
  with assms have False by auto
  then show ?thesis by simp
next
  case (Some us)
  from merge_lists_sound[OF this]
    have "\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i]" by simp
  from equiv_class_Int[OF this merge_lists_length[OF Some] merge_lists_length'[OF Some]]
    show ?thesis by (simp add: Some)
qed

lemma equiv_class_Int':
  assumes "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us]"
  shows "length ss = length ts \<and> length ss = length us
    \<and> (\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i])"
proof -
  from equiv_class_nonempty[of "GCFun f us"] and assms
    have ne: "[GCFun f ss] \<inter> [GCFun f ts] \<noteq> {}" by auto
  from assms equiv_class_Int_conv'[OF ne] obtain vs
    where Some: "merge_lists ss ts = Some vs" and "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f vs]"
    by auto
  with assms have vs: "vs = us"
    using equiv_class_eq_eq_conv[of "GCFun f us" "GCFun f vs"] by simp
  from merge_lists_sound[OF Some] and merge_lists_length[OF Some]
    and merge_lists_length'[OF Some] show ?thesis unfolding vs by simp
qed

lemma equiv_class_Int_conv[simp]:
  "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us] \<longleftrightarrow>
    length ss = length ts \<and> length ss = length us \<and> (\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i])"
  using equiv_class_Int[of ss ts us] and equiv_class_Int'[of f ss ts us] by blast

lemma merge_lists_complete:
  assumes "length Cs = length Ds" and "length Cs = length Es"
    and "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Es!i]"
  shows "merge_lists Cs Ds = Some Es"
using assms
proof (induct Cs Ds arbitrary: Es rule: merge_lists.induct)
  case (2 Cs D Ds)
  show ?case
  proof (cases Es)
    case Nil with 2 show ?thesis by simp
  next
    case (Cons F Fs)
    have "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Fs!i]"
    proof (intro allI impI)
      fix i assume "i < length Cs"
      then have "Suc i < length (\<box>#Cs)" by simp
      from 2(4)[THEN spec, THEN mp, OF this]
        show "[Cs!i] \<inter> [Ds!i] = [Fs!i]" by (simp add: Cons)
    qed
    with 2 have "merge_lists Cs Ds = Some Fs" by (simp add: Cons)
    moreover have "D = F"
    proof -
      from 2(4)[THEN spec, THEN mp, of 0] have "[\<box>] \<inter> [D] = [F]" by (simp add: Cons)
      then show ?thesis by (simp add: equiv_class_eq_eq_conv)
    qed
    ultimately show ?thesis by (simp add: Cons)
  qed
next 
  case (3 C Cs Ds Es)
  show ?case
  proof (cases Es)
    case Nil with 3 show ?thesis by simp
  next
    case (Cons F Fs)
    have "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Fs!i]"
    proof (intro allI impI)
      fix i assume "i < length Cs"
      then have "Suc i < length (C#Cs)" by simp
      from 3(4)[THEN spec, THEN mp, OF this]
        show "[Cs!i] \<inter> [Ds!i] = [Fs!i]" by (simp add: Cons)
     qed
    with 3 have "merge_lists Cs Ds = Some Fs" unfolding Cons by simp
    moreover have "C = F"
    proof -
      from 3(4)[THEN spec, THEN mp, of 0] have "[C] \<inter> [\<box>] = [F]" by (simp add: Cons)
      then show ?thesis by (simp add: equiv_class_eq_eq_conv)
    qed
    ultimately show ?thesis by (simp add: Cons)
  qed
next
  case (4 f ss Cs ts Ds Es)
  show ?case
  proof (cases Es)
    case Nil with 4 show ?thesis by simp
  next
    case (Cons F Fs)
    from 4 have len1: "length Cs = length Ds" by simp
    from 4 have len2: "length Cs = length Fs" by (simp add: Cons)
    have IH: "\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Fs!i]"
    proof (intro allI impI)
      fix i assume "i < length Cs"
      then have "Suc i < length (GCFun f ss # Cs)" by simp
      from 4(5)[THEN spec, THEN mp, OF this]
        show "[Cs!i] \<inter> [Ds!i] = [Fs!i]" by (simp add: Cons)
    qed
    from 4(5)[THEN spec, THEN mp, of 0]
      have eq_F: "[GCFun f ss] \<inter> [GCFun f ts] = [F]" by (simp add: Cons)
    with equiv_class_nonempty[of F] obtain us where Some: "merge_lists ss ts = Some us"
      and eq_GCFun: "[GCFun f ss] \<inter> [GCFun f ts] = [GCFun f us]"
      using equiv_class_Int_conv'[of f ss ts] by auto
    then have "length ss = length ts" and "length ss = length us"
      and "\<forall>i<length ss. [ss!i] \<inter> [ts!i] = [us!i]" unfolding equiv_class_Int_conv by auto
    from eq_F and eq_GCFun have F: "F = GCFun f us" using equiv_class_eq_eq_conv by fast
    from 4(2)[OF Some len1 len2 IH] show ?thesis by (simp add: Cons Some F)
  qed
next
  case (5 f g ss Cs ts Ds Es)
  from \<open>f \<noteq> g\<close> have "[GCFun f ss] \<inter> [GCFun g ts] = {}" by auto
  with 5(4)[THEN spec, THEN mp, of 0] have "[Es!0] = {}" by simp
  with equiv_class_nonempty[of "Es!0"] show ?case by force
qed simp_all

lemma merge_lists_Some_equiv_class_conv:
  "merge_lists Cs Ds = Some Es \<longleftrightarrow>
    length Cs = length Ds \<and> length Cs = length Es \<and> (\<forall>i<length Cs. [Cs!i] \<inter> [Ds!i] = [Es!i])"
  using merge_lists_sound[of Cs Ds Es]
    and merge_lists_length[of Cs Ds Es]
    and merge_lists_length'[of Cs Ds Es]
    and merge_lists_complete[of Cs Ds]
    by blast

qualified fun merge :: "('f, 'v) gctxt \<Rightarrow> ('f, 'v) gctxt \<Rightarrow> ('f, 'v) gctxt option" where
  "merge C D = do {
    Es \<leftarrow> merge_lists [C] [D];
    Some (Es!0)
  }"

lemma merge_ident[simp]: "merge C C = Some C" by simp

lemma merge_None:
  assumes "merge C D = None"
  shows "[C] \<inter> [D] = {}"
  using assms and merge_lists_None[of "C#[]" "D#[]"] by simp

lemma merge_sound:
  assumes "merge C D = Some E"
  shows "[C] \<inter> [D] = [E]"
  using assms and merge_lists_sound[of "C#[]" "D#[]"] by (auto split: bind_splits)

lemma merge_complete:
  assumes "[C] \<inter> [D] = [E]" shows "merge C D = Some E"
  using merge_lists_Some_equiv_class_conv[symmetric, of "C#[]" "D#[]" "E#[]"]
    and assms
    by simp

lemma merge_equiv_class_Some_conv[simp]:
  "merge C D = Some E \<longleftrightarrow> [C] \<inter> [D] = [E]" (is "?lhs \<longleftrightarrow> ?rhs")
  using merge_sound and merge_complete by blast

lemma merge_equiv_class_None_conv[simp]:
  "merge C D = None \<longleftrightarrow> [C] \<inter> [D] = {}" (is "?lhs \<longleftrightarrow> ?rhs")
proof
  assume ?lhs then show ?rhs by (rule merge_None)
next
  assume ?rhs
  then show ?lhs
  proof (cases "merge C D")
    case (Some E)
    then have "[C] \<inter> [D] = [E]" unfolding merge_equiv_class_Some_conv .
    moreover from equiv_class_nonempty[of E] have "[E] \<noteq> {}" by auto
    ultimately show ?thesis using \<open>?rhs\<close> by simp
  next
    case None then show ?thesis by simp
  qed
qed 

function
  match_list :: "(('f, 'v) gctxt \<times> ('f, 'v) term) list \<Rightarrow> (('f, 'v) gctxt \<times> 'v) list option"
where
  "match_list [] = Some []"
| "match_list ((\<box>, t)#ps) = match_list ps"
| "match_list ((GCFun f ss, Fun f ts)#ps) = do {
    ps' \<leftarrow> zip_option ss ts;
    match_list (ps' @ ps)
  }"
| "match_list ((GCFun f ss, Var x)#ps) = do {
    ps' \<leftarrow> match_list ps;
    Some ((GCFun f ss, x) # ps')
  }"
| "f \<noteq> g \<Longrightarrow> match_list ((GCFun f ss, Fun g ts)#ps) = None"
proof -
  fix P xs
  assume 1: "xs = [] \<Longrightarrow> P"
    and 2: "\<And>t ps. xs = (\<box>, t) # ps \<Longrightarrow> P"
    and 3: "\<And>f ss ts ps. xs = (GCFun f ss, Fun f ts) # ps \<Longrightarrow> P"
    and 4: "\<And>f ss y ps. xs = (GCFun f ss, Var y) # ps \<Longrightarrow> P"
    and 5: "\<And>f g ss ts ps. \<lbrakk>f \<noteq> g; xs = (GCFun f ss, Fun g ts) # ps\<rbrakk> \<Longrightarrow> P"
  show P
  proof (cases xs)
    case Nil then show ?thesis using 1 by blast
  next
    case (Cons z zs)
    show ?thesis
    proof (cases z)
      case (Pair C t)
      show ?thesis
      proof (cases C)
        case GCHole with Pair Cons 2 show ?thesis by blast
      next
        case (GCFun f ss)
        show ?thesis
        proof (cases t)
          case (Var y) with Cons Pair GCFun 4 show ?thesis by blast
        next
          case (Fun g ts) with Cons Pair GCFun 3 5 show ?thesis by (cases "f = g") blast+
        qed
      qed
    qed
  qed
qed force+
termination
proof 
  fix f :: 'f and hs :: "('f, 'v) gctxt list" and g :: 'f
    and ss :: "('f, 'v) term list" and ps res
  assume "zip_option hs ss = Some res"
  then have "length hs = length ss" and "res = zip hs ss" by auto
  then have lt: "size_list (size \<circ> snd) res < Suc (Suc (size_list size ss))"
    by (auto simp: size_list_map[symmetric])
  show "(res @ ps, (GCFun f hs, Fun g ss) # ps) \<in> measures [\<lambda>l. size_list (size \<circ> snd) l, length]"
    by (rule measures_less, insert lt, auto simp: o_def)
qed (auto simp: o_def)

declare match_list.simps[code del]

lemma match_list_code_simps[code]:
  "match_list [] = Some []"
  "match_list ((\<box>, t)#ps) = match_list ps"
  "match_list ((GCFun f ss, Fun g ts)#ps) = do {
    guard (f = g);
    ps' \<leftarrow> zip_option ss ts;
    match_list (ps' @ ps)
  }"
  "match_list ((GCFun f ss, Var x)#ps) = do {
    ps' \<leftarrow> match_list ps;
    Some ((GCFun f ss, x) # ps')
  }"
  by (simp_all add: guard_def)

lemma match_list_sound:
  assumes "match_list ps = Some ps'"
  shows "(\<forall>(C,t)\<in>set ps. t \<cdot> \<sigma> \<in> [C]) \<longleftrightarrow> (\<forall>(C,x)\<in>set ps'. Var x \<cdot> \<sigma> \<in> [C])"
    (is "?P ps \<sigma> = ?Q ps' \<sigma>")
using assms
proof (induct ps arbitrary: ps' rule: match_list.induct)
  case (3 f ss ts ps)
  then obtain us where zip: "zip_option ss ts = Some us" and "match_list (us @ ps) = Some ps'"
    by (cases "zip_option ss ts") auto
  from 3(1)[OF this] have "?P (us @ ps) \<sigma> = ?Q ps' \<sigma>" .
  moreover have "?P us \<sigma> = ?P ((GCFun f ss, Fun f ts)#[]) \<sigma>"
    using zip unfolding all_set_conv_all_nth by force
  ultimately show ?case by auto
next
  case (4 f ss x ps)
  then obtain ps'' where "match_list ps = Some ps''" and ps': "ps' = ((GCFun f ss, x) # ps'')"
    by (cases "match_list ps") auto
  from 4(1)[OF this(1)] show ?case unfolding ps' by auto
qed simp_all

fun
  gcsubst_apply_term ::
    "('f, 'v) term \<Rightarrow> ('v \<Rightarrow> ('f, 'v) gctxt) \<Rightarrow> ('f, 'v) gctxt" (infixl "\<cdot>gc" 60)
where
  "Var x \<cdot>gc gcs = gcs x"
| "Fun f ts \<cdot>gc gcs = GCFun f (map (\<lambda>t. t \<cdot>gc gcs) ts)"

lemma equiv_class_GCFun_subset:
  assumes "length ss = length ts"
    and "\<forall>i<length ss. [ss!i] \<subseteq> [ts!i]"
  shows "[GCFun f ss] \<subseteq> [GCFun f ts]"
  using assms by auto

lemma equiv_class_GCFun_length:
  assumes "[GCFun f ss] \<subseteq> [GCFun f ts]"
  shows "length ss = length ts"
  using assms and equiv_class_nonempty[of "GCFun f ss"]
  by auto

lemma equiv_class_GCFun_fun:
  assumes "[GCFun f ss] \<subseteq> [GCFun g ts]"
  shows "f = g"
  using assms and equiv_class_nonempty[of "GCFun f ss"]
  by auto

lemma equiv_class_GCFunE':
  assumes "[GCFun f ss] \<subseteq> [GCFun f ts]" and "i < length ss"
  shows "[ss!i] \<subseteq> [ts!i]"
proof -
  from equiv_class_GCFun_length[OF assms(1)] have len: "length ts = length ss" by simp
  let ?S = "\<lambda>ss. {us. length us = length ss \<and> (\<forall>i<length ss. us!i \<in> [ss!i])}"
  from assms have subset: "?S ss \<subseteq> ?S ts" by (auto simp: len)
  from Ex_list_of_length_P[of "length ss" "\<lambda>x i. x \<in> [ss!i]"]
    obtain us where us_len: "length us = length ss" and us: "\<forall>i<length ss. us!i \<in> [ss!i]"
    using equiv_class_nonempty by force
  then have "us \<in> ?S ss" by simp
  then have "us \<in> ?S ts" using subset unfolding len by auto
  show ?thesis
  proof
    fix t assume "t \<in> [ss!i]"
    let ?us = "us[i:=t]"
    show "t \<in> [ts!i]"
    proof (rule ccontr)
      assume "t \<notin> [ts!i]"
      have "\<forall>i<length ss. ?us!i \<in> [ss!i]"
      proof (intro allI impI)
        fix j assume "j < length ss" then show "?us!j \<in> [ss!j]"
          using \<open>t \<in> [ss!i]\<close> by (cases "i = j") (auto simp: us us_len assms)
      qed
      then have "?us \<in> ?S ss" using us_len by simp
      moreover from \<open>t \<notin> [ts!i]\<close> have "?us \<notin> ?S ts" using assms(2) by (force simp: us_len len)
      ultimately have "\<not> ?S ss \<subseteq> ?S ts" by blast
      with subset show False by (contradiction)
    qed
  qed
qed

lemma equiv_class_GCFun_subset_args_conv:
  "[GCFun f ss] \<subseteq> [GCFun g ts]
    \<longleftrightarrow> f = g \<and> length ss = length ts \<and> (\<forall>i<length ss. [ss!i] \<subseteq> [ts!i])"
  using equiv_class_GCFun_length[of f ss]
    and equiv_class_GCFun_fun[of f ss g ts]
    and equiv_class_GCFun_subset[of ss ts f]
    and equiv_class_GCFunE'[of f ss ts]
  by blast

lemma UNIV_subset_GCFun [simp]:
  shows "UNIV \<subseteq> [GCFun f ts] = False"
  by auto

lemma equiv_class_GCFun_subset_args_conv_comp:
  "[s] \<subseteq> [u] \<longleftrightarrow> (case u of \<box> \<Rightarrow> True |
     GCFun g ts \<Rightarrow> (case s of \<box> \<Rightarrow> False | GCFun f ss \<Rightarrow>
         f = g \<and> length ss = length ts \<and> (\<forall>i<length ss. [ss!i] \<subseteq> [ts!i])))"
  by (auto simp del: equiv_class.simps(2) simp add: equiv_class_GCFun_subset_args_conv split: gctxt.splits)

lemma match_list_sound_subset:
  assumes "match_list ps = Some ps'"
  shows "(\<forall>(C, t)\<in>set ps. [t \<cdot>gc \<sigma>] \<subseteq> [C]) \<longleftrightarrow> (\<forall>(C, x)\<in>set ps'. [\<sigma> x] \<subseteq> [C])"
    (is "?P ps \<sigma> = ?Q ps' \<sigma>")
using assms
proof (induct ps arbitrary: ps' rule: match_list.induct)
  case (3 f ss ts ps)
  then obtain us where zip: "zip_option ss ts = Some us" and "match_list (us @ ps) = Some ps'"
    by (force split: bind_splits)
  from 3(1)[OF this] have P: "?P (us @ ps) \<sigma> = ?Q ps' \<sigma>" .
  have IH: "?P us \<sigma> = ?P ((GCFun f ss, Fun f ts)#[]) \<sigma>"
  proof (intro iffI ballI2)
    fix C t assume "\<forall>(C, t)\<in>set us. [t \<cdot>gc \<sigma>] \<subseteq> [C]" 
      and "(C, t) \<in> set [(GCFun f ss, Fun f ts)]"
    then show "[t \<cdot>gc \<sigma>] \<subseteq> [C]" using zip by (force simp: all_set_conv_all_nth)
  next
    let ?ts = "map (\<lambda>t. t \<cdot>gc \<sigma>) ts"
    fix C t assume "\<forall>(C, t)\<in>set [(GCFun f ss, Fun f ts)]. [t \<cdot>gc \<sigma>] \<subseteq> [C]"
      and us: "(C, t) \<in> set us"
    then have "[GCFun f ?ts] \<subseteq> [GCFun f ss]" by simp
    from this[unfolded equiv_class_GCFun_subset_args_conv]
      have "length ?ts = length ss" and subset: "\<forall>i<length ss. [?ts!i] \<subseteq> [ss!i]" by auto
    from \<open>(C, t) \<in> set us\<close> obtain i where "i < length us" and "us!i = (C, t)"
      unfolding in_set_conv_nth by auto
    with zip and nth_zip[of i ss ts] have "ss!i = C" and "ts!i = t" by force+
    then show "[t \<cdot>gc \<sigma>] \<subseteq> [C]"
      using subset and \<open>i < length us\<close> and \<open>length ?ts = length ss\<close> zip by force
  qed
  from P show ?case by (force simp: ball_Un IH)
next
  case (4 f ss x ps)
  then obtain ps'' where "match_list ps = Some ps''" and ps': "ps' = ((GCFun f ss, x) # ps'')"
    by (cases "match_list ps") auto
  from 4(1)[OF this(1)] show ?case unfolding ps' by auto
qed simp_all

lemma match_list_complete:
  assumes "match_list ps = None"
  shows "\<forall>\<sigma>. \<exists>(C, t)\<in>set ps. t \<cdot> \<sigma> \<notin> [C]"
    (is "\<forall>\<sigma>. ?P ps \<sigma>")
using assms
proof (induct ps rule: match_list.induct)
  case (3 f ss ts ps)
  then have "zip_option ss ts = None
    \<or> (\<exists>us. zip_option ss ts = Some us \<and> match_list (us @ ps) = None)"
    by (cases "zip_option ss ts") auto
  then show ?case
  proof
    assume "zip_option ss ts = None"
    then have "length ss \<noteq> length ts" by simp then show ?case by simp
  next
    assume "\<exists>us. zip_option ss ts = Some us \<and> match_list (us @ ps) = None"
    then obtain us
      where zip: "zip_option ss ts = Some us"
      and "match_list (us @ ps) = None" by auto
    from 3(1)[OF this] have IH: "\<forall>\<sigma>. ?P (us @ ps) \<sigma>" .
    from zip have us: "us = zip ss ts" and len: "length ss = length ts" by auto
    show ?case
    proof
      fix \<sigma>
      from IH obtain C t where "(C, t) \<in> set (us @ ps)" and t: "t \<cdot> \<sigma> \<notin> [C]" by force+
      then have "(C, t) \<in> set us \<or> (C, t) \<in> set ps" by auto
      then show "?P ((GCFun f ss, Fun f ts)#ps) \<sigma>"
        by (rule disjE) (force simp: us in_set_conv_nth t len)+
    qed
  qed
qed force+

private function
  merge_var ::
    "'v \<Rightarrow> ('f, 'v) gctxt \<Rightarrow> (('f, 'v) gctxt \<times> 'v) list
    \<Rightarrow> ((('f, 'v) gctxt \<times> 'v) \<times> (('f, 'v) gctxt \<times> 'v) list) option"
where
  "merge_var x C [] = Some ((C, x), [])"
| "merge_var x C ((D, x)#ps) = do {
    E \<leftarrow> merge C D;
    merge_var x E ps
  }"
| "x \<noteq> y \<Longrightarrow> merge_var x C ((D, y)#ps) = do {
    (Cx, ps') \<leftarrow> merge_var x C ps;
    Some (Cx, (D, y) # ps')
  }"
proof -
  fix P x
  assume 1: "\<And>xa C. x = (xa, C, []) \<Longrightarrow> P"
    and 2: "\<And>xa C D ps. x = (xa, C, (D, xa) # ps) \<Longrightarrow> P"
    and 3: "\<And>xa y C D ps. \<lbrakk>xa \<noteq> y; x = (xa, C, (D, y) # ps)\<rbrakk> \<Longrightarrow> P"
  show P
  proof (cases x)
    case (fields y C ps)
    show ?thesis
    proof (cases ps)
      case Nil then show ?thesis using fields 1 by fast
    next
      case (Cons q qs)
      show ?thesis
      proof (cases q)
        case (Pair D z)
        then show ?thesis using fields Cons 2 3 by (cases "y = z") fast+
      qed
    qed
  qed
qed fast+
termination by lexicographic_order

declare merge_var.simps[code del]

lemma merge_var_code_simps[code]:
  "merge_var x C [] = Some ((C, x), [])"
  "merge_var x C ((D, y)#ps) = (if x = y then do {
    E \<leftarrow> merge C D;
    merge_var x E ps
  } else do {
    (b, ps') \<leftarrow> merge_var x C ps;
    Some (b, (D, y) # ps')
  })"
  by simp_all

lemma merge_var_complete:
  assumes "merge_var x C ps = None"
  shows "\<forall>\<sigma>. \<exists>(C, x)\<in>set ((C, x)#ps). \<sigma> x \<notin> [C]"
using assms
proof (induct x C ps rule: merge_var.induct)
  case (2 x C D ps)
  then have "merge C D = None \<or> (\<exists>E. merge C D = Some E \<and> merge_var x E ps = None)" by (cases "merge C D") auto
  then show ?case
  proof
    assume "merge C D = None"
    from merge_None[OF this] have "[C] \<inter> [D] = {}" .
    then show ?case by force
  next
    assume "\<exists>E. merge C D = Some E \<and> merge_var x E ps = None"
    then obtain E where "merge C D = Some E" and "merge_var x E ps = None" by auto
    from 2(1)[OF this] and merge_sound[OF this(1)] show ?case by force
  qed
qed force+

lemma merge_var_length [simp]:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "length ps \<ge> length ps'"
  using assms by (induct x C ps arbitrary: Cx ps' rule: merge_var.induct) (force split: bind_splits)+

lemma merge_var_pair:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "snd Cx = x"
  using assms by (induct x C ps arbitrary: Cx ps' rule: merge_var.induct) (force split: bind_splits)+

lemma merge_var_var:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "x \<notin> snd ` set ps'"
  using assms by (induct x C ps arbitrary: Cx ps' rule: merge_var.induct) (force split: bind_splits)+

lemma merge_var_equiv_class_subset:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "[fst Cx] \<subseteq> [C]"
using assms
proof (induct x C ps arbitrary: Cx ps' rule: merge_var.induct)
  case (2 x C D ps Cx ps')
  then obtain E
    where "merge C D = Some E" and "merge_var x E ps = Some (Cx, ps')"
    by (cases "merge C D") (force split: bind_splits)+
  from 2(1)[OF this] and merge_sound[OF this(1)] show ?case by force
qed (force split: bind_splits)+

lemma merge_var_sound:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "(\<forall>(D, y)\<in>set ((C, x)#ps). \<sigma> y \<in> [D]) = (\<forall>(D, y)\<in>set (Cx#ps'). \<sigma> y \<in> [D])"
    (is "?P ((C, x)#ps) = ?P (Cx#ps')")
using assms
proof (induct x C ps arbitrary: Cx ps' rule: merge_var.induct)
  case (2 x C D ps Cx)
  then obtain E where merge: "merge C D = Some E" and "merge_var x E ps = Some (Cx, ps')"
    by (auto split: bind_splits)
  from 2(1)[OF this] have IH: "?P ((E, x)#ps) = ?P (Cx#ps')" by force
  moreover have "\<sigma> x \<in> [C] \<and> \<sigma> x \<in> [D] \<longleftrightarrow> \<sigma> x \<in> [E]"
    unfolding merge_sound[OF merge, symmetric] Int_iff ..
  ultimately show ?case by force
next
  case (3 x y C D ps Cx)
  then obtain ps'' where "merge_var x C ps = Some (Cx, ps'')"
    and ps': "ps' = (D, y) # ps''" by (cases "merge_var x C ps") auto
  from 3(2)[OF this(1)] show ?case unfolding ps' by force
qed simp

lemma merge_var_sound_subset:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "(\<forall>(D, y)\<in>set ((C, x)#ps). [\<sigma> y] \<subseteq> [D]) = (\<forall>(D, y)\<in>set (Cx#ps'). [\<sigma> y] \<subseteq> [D])"
    (is "?P ((C, x)#ps) = ?P (Cx#ps')")
using assms
proof (induct x C ps arbitrary: Cx ps' rule: merge_var.induct)
  case (2 x C D ps Cx)
  then obtain E where merge: "merge C D = Some E" and "merge_var x E ps = Some (Cx, ps')"
    by (auto split: bind_splits)
  from 2(1)[OF this] have IH: "?P ((E, x)#ps) = ?P (Cx#ps')" by force
  moreover have "[\<sigma> x] \<subseteq> [C] \<and> [\<sigma> x] \<subseteq> [D] \<longleftrightarrow> [\<sigma> x] \<subseteq> [E]"
    unfolding merge_sound[OF merge, symmetric] by simp
  ultimately show ?case by auto
next
  case (3 x y C D ps Cx)
  then obtain ps'' where "merge_var x C ps = Some (Cx, ps'')"
    and ps': "ps' = (D, y) # ps''" by (force split: bind_splits)
  from 3(2)[OF this(1)] show ?case unfolding ps' by force
qed simp

fun merge_all :: "(('f, 'v) gctxt \<times> 'v) list \<Rightarrow> (('f, 'v) gctxt \<times> 'v) list option" where
  "merge_all [] = Some []"
| "merge_all ((C, x)#ps) = do {
    (Cx, ps') \<leftarrow> merge_var x C ps;
    ps'' \<leftarrow> merge_all ps';
    Some (Cx # ps'')
  }"

fun gcsubst :: "(('f, 'v) gctxt \<times> 'v) list \<Rightarrow> 'v \<Rightarrow> ('f, 'v) gctxt" where
  "gcsubst [] = (\<lambda>_. \<box>)"
| "gcsubst ((C, x)#xs) = (\<lambda>y. if x = y then C else gcsubst xs y)"

lemma gcsubst_simps[simp]:
  "gcsubst [] x = \<box>"
  "gcsubst ((C, x) # xs) x = C"
  "x \<noteq> y \<Longrightarrow> gcsubst ((C, x)#xs) y = gcsubst xs y"
  by simp_all

declare gcsubst.simps[simp del]

lemma merge_all_complete:
  assumes "merge_all ps = None"
  shows "\<forall>\<sigma>. \<exists>(C, x)\<in>set ps. \<sigma> x \<notin> [C]"
using assms
proof (induct ps rule: merge_all.induct)
  case 1 then show ?case by simp
next
  case (2 C x ps)
  then have "merge_var x C ps = None \<or>
    (\<exists>Cx ps'. merge_var x C ps = Some (Cx, ps') \<and> merge_all ps' = None)"
    by (cases "merge_var x C ps") force+
  then show ?case
  proof
    assume "merge_var x C ps = None" then show ?thesis by (rule merge_var_complete)
  next
    assume "\<exists>Cx ps'. merge_var x C ps = Some (Cx, ps') \<and> merge_all ps' = None"
    with 2(1) and merge_var_sound[of x C ps] show ?thesis by fastforce
  qed
qed

lemma merge_var_vars:
  assumes "merge_var x C ps = Some (Cx, ps')"
  shows "snd ` set ((C, x)#ps) = snd ` set (Cx # ps')"
using assms
proof (induct x C ps arbitrary: Cx ps' rule: merge_var.induct)
  case 1 then show ?case by simp
next
  case (2 x C D ps Cx ps')
  then obtain E where "merge C D = Some E" and mv: "merge_var x E ps = Some (Cx, ps')" by (force split: bind_splits)
  from 2(1)[OF this] and merge_var_pair[OF mv] show ?case by simp
next
  case (3 x y C D ps Cx ps')
  then obtain ps'' where "merge_var x C ps = Some (Cx, ps'')"
    and ps': "ps' = (D, y) # ps''" by (force split: bind_splits)
  from 3(2)[OF this(1)] show ?case unfolding ps' by auto
qed
 
lemma merge_all_vars:
  assumes "merge_all ps = Some gcs"
  shows "snd ` set gcs = snd ` set ps"
using assms
proof (induct ps arbitrary: gcs rule: merge_all.induct)
  case (2 C x ps gcs)
  then obtain Cx ps' ps'' where mv: "merge_var x C ps = Some (Cx, ps')"
    and "merge_all ps' = Some ps''"
    and gcs: "gcs = Cx # ps''" by (auto split: bind_splits)
   from 2(1)[OF this(1) refl this(2)] merge_var_vars[OF mv] show ?case unfolding gcs by simp
qed simp

lemma merge_all_sound:
  assumes "merge_all ps = Some gcs"
  shows "\<forall>(C, x)\<in>set ps. [gcsubst gcs x] \<subseteq> [C]"
using assms
proof (induct ps arbitrary: gcs rule: merge_all.induct)
  case 1 then show ?case by simp
next
  case (2 C x ps)
  from 2(2) obtain Cx ps' ps'' where mv: "merge_var x C ps = Some (Cx, ps')"
    and ma: "merge_all ps' = Some ps''"
    and gcs: "gcs = Cx # ps''" by (auto split: bind_splits)
  from 2(1)[OF mv refl ma] have IH: "\<forall>(C, x)\<in>set ps'. [gcsubst ps'' x] \<subseteq> [C]" .
  moreover have gcsubst: "\<forall>(C, x)\<in>set ps'. gcsubst ps'' x = gcsubst (Cx#ps'') x"
  proof (rule ballI2)
    fix D y assume "(D, y) \<in> set ps'"
    with merge_var_var[OF mv] have "y \<noteq> x" by force
    then show "gcsubst ps'' y = gcsubst (Cx # ps'') y"
      using merge_var_pair[OF mv] by (cases Cx) simp
  qed
  moreover have "[gcsubst (Cx#ps') x] \<subseteq> [fst Cx]"
    using merge_var_pair[OF mv] by (cases Cx) simp_all
  ultimately show ?case unfolding gcs unfolding merge_var_sound_subset[OF mv]
    by force
qed

fun match :: "('f, 'v) gctxt \<times> ('f, 'v) term \<Rightarrow> (('f, 'v) gctxt \<times> 'v) list option" where
  "match (C, t) = do {
    ps \<leftarrow> match_list [(C, t)];
    merge_all ps
  }"

lemma match_sound:
  assumes "match (C, t) = Some gcs"
  shows "[t \<cdot>gc gcsubst gcs] \<subseteq> [C]"
proof -
  from assms obtain ps where "match_list [(C, t)] = Some ps" and "merge_all ps = Some gcs"
    by (force split: bind_splits)
  from merge_all_sound[OF this(2), unfolded match_list_sound_subset[OF this(1), symmetric]]
  show ?thesis by simp
qed

lemma match_complete:
  assumes "match (C, t) = None"
  shows "\<forall>\<sigma>. t \<cdot> \<sigma> \<notin> [C]"
proof -
  from assms have "match_list [(C, t)] = None \<or> (\<exists>ps. match_list [(C, t)] = Some ps \<and>
    merge_all ps = None)" by (cases "match_list [(C, t)]") auto
  then show ?thesis
  proof
    assume "match_list [(C, t)] = None"
    from match_list_complete[OF this] show ?thesis by simp
  next
    assume "\<exists>ps. match_list [(C, t)] = Some ps \<and> merge_all ps = None"
    then obtain ps where match: "match_list [(C, t)] = Some ps" and "merge_all ps = None" by auto
    from merge_all_complete[OF this(2)]
      show ?thesis using match_list_sound[OF match, symmetric, simplified] by force
  qed
qed

fun term_of :: "('f, 'v) gctxt \<Rightarrow> ('f, 'v) term" where
  "term_of \<box> = Var undefined"
| "term_of (GCFun f Cs) = Fun f (map term_of Cs)"

fun gctxt_of :: "('f, 'v) term \<Rightarrow> ('f, 'v) gctxt" where
  "gctxt_of (Var x) = \<box>"
| "gctxt_of (Fun f ts) = GCFun f (map gctxt_of ts)"

lemma term_of_ident[simp]: "term_of C \<in> [C]"
  by (induct C) simp_all

lemma gctxt_of_ident[simp]: "t \<in> [gctxt_of t]"
  by (induct t) simp_all

lemma gctxt_of_term_of_ident[simp]: "gctxt_of (term_of C) = C"
  by (induct C, simp)
  (insert map_nth_eq_conv[symmetric, of _ _ "\<lambda>x. gctxt_of (term_of x)"],
    simp add: o_def, force)

lemma term_of_gctxt_of_ident [simp]:
  "term_of (gctxt_of t) = map_vars_term (\<lambda>_. undefined) t"
  by (induct t) simp_all

lemma in_equiv_class_gctxt_of_subset:
  assumes "t \<in> [C]" shows "[gctxt_of t] \<subseteq> [C]"
using assms
proof (induct t arbitrary: C)
  case (Var x) then show ?case by (cases C) auto
next
  case (Fun f ts)
  show ?case
  proof (cases C)
    case (GCFun g Cs)
    from Fun(2)[unfolded this]
      have f: "f = g" and len: "length ts = length Cs"
      and all: "\<forall>i<length ts. ts!i \<in> [Cs!i]" by auto
    with Fun(1) and len have IH: "\<forall>i<length ts. [gctxt_of (ts!i)] \<subseteq> [Cs!i]"
      by simp
    then show ?thesis unfolding GCFun using len
      using equiv_class_GCFun_subset[of Cs "map gctxt_of ts" f]
      by (force simp: f)
  qed simp
qed

lemma in_equiv_class_gctxt_of_subset_conv:
  "t \<in> [C] \<longleftrightarrow> [gctxt_of t] \<subseteq> [C]"
  using in_equiv_class_gctxt_of_subset[of t C] by auto

lemma equiv_class_subset_imp_in:
  assumes "[t \<cdot>gc \<sigma>] \<subseteq> [C]" shows "t \<cdot> (term_of \<circ> \<sigma>) \<in> [C]"
using assms
proof (induct t arbitrary: C)
  case (Fun f ts)
  let ?ts = "map (\<lambda>t. t \<cdot>gc \<sigma>) ts"
  show ?case
  proof (cases C)
    case (GCFun g Cs)
    from Fun(1) have IH': "\<forall>i<length ts. [ts!i \<cdot>gc \<sigma>] \<subseteq> [Cs!i]
      \<longrightarrow> ts!i \<cdot> (term_of \<circ> \<sigma>) \<in> [Cs!i]" by fastforce
    from Fun(2) have f: "f = g" and len: "length ?ts = length Cs"
      and all: "\<forall>i<length ?ts. [?ts!i] \<subseteq> [Cs!i]"
      unfolding GCFun gcsubst_apply_term.simps
        equiv_class_GCFun_subset_args_conv by blast+
    from all IH' have "\<forall>i<length ts. ts!i \<cdot> (term_of \<circ> \<sigma>) \<in> [Cs!i]"
      unfolding length_map by fastforce
    moreover have "length (map (\<lambda>t. t \<cdot> (term_of \<circ> \<sigma>)) ts) = length Cs"
      using len by simp
    ultimately show ?thesis by (simp add: GCFun o_def f)
  qed simp
qed force

lemma equiv_class_in_imp_subset:
  assumes "t \<cdot> \<sigma> \<in> [C]" shows "[t \<cdot>gc (gctxt_of \<circ> \<sigma>)] \<subseteq> [C]"
using assms
proof (induct t arbitrary: C)
  case (Var x) then show ?case by (simp add: in_equiv_class_gctxt_of_subset)
next
  case (Fun f ts) then show ?case by (cases C) force+
qed

lemma equiv_class_in_subset_conv:
  "(\<exists>\<sigma>. [t \<cdot>gc \<sigma>] \<subseteq> [C]) \<longleftrightarrow> (\<exists>\<sigma>. t \<cdot> \<sigma> \<in> [C])"
  using equiv_class_subset_imp_in equiv_class_in_imp_subset by blast

lemma match_impl[code]:
  "Ground_Context.match C t \<longleftrightarrow> match (C, t) \<noteq> None"
  using match_complete[of C t]
    and match_sound[of C t]
    unfolding Ground_Context.match_def
    by (cases "match (C, t)") (force simp: equiv_class_in_subset_conv[symmetric])+

lemma match_sound_in:
  assumes "match (C, t) = Some \<sigma>"
  shows "t \<cdot> (term_of \<circ> gcsubst \<sigma>) \<in> [C]"
  using equiv_class_subset_imp_in[OF match_sound[OF assms]] .

context 
  fixes iv :: "nat \<Rightarrow> 'v"
begin
fun
  gctxts_to_terms_intern :: "nat \<Rightarrow> ('f, 'v) gctxt list \<Rightarrow> nat \<times> ('f, 'v) term list" where
  "gctxts_to_terms_intern i (GCFun f ts # Cs) = (let
    (i1,res1) = gctxts_to_terms_intern i ts;
    (i2,res2) = gctxts_to_terms_intern i1 Cs
     in (i2, (Fun f res1 # res2)))"
| "gctxts_to_terms_intern i (GCHole # Cs) = (
    let (i',res) = gctxts_to_terms_intern (i+1) Cs
     in (i',Var (iv i) # res))"
| "gctxts_to_terms_intern i [] = (i, [])"


lemma gctxts_to_terms_intern_vars:
  fixes Cs :: "('f, 'v) gctxt list"
  assumes "gctxts_to_terms_intern i Cs = (j, ss)"
  shows "i \<le> j \<and> (\<forall> s \<in> set ss. vars_term s \<subseteq> {iv k | k. i \<le> k \<and> k < j})"
using assms
proof (induct i Cs arbitrary: j ss rule: gctxts_to_terms_intern.induct)
  case (1 i f ts Cs j ss)
  let ?call1 = "gctxts_to_terms_intern i ts"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  let ?call2 = "gctxts_to_terms_intern i1 Cs"
  obtain i2 res2 where call2: "?call2 = (i2,res2)" by force
  note IH = 1(1)[OF call1] 1(2)[OF call1[symmetric] refl call2]
  from 1(3) call1 call2 have j: "j = i2" and ss: "ss = Fun f res1 # res2" by auto
  show ?case unfolding j ss using IH by force
next
  case (2 i Cs j ss)
  let ?call1 = "gctxts_to_terms_intern (i+1) Cs"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  note IH = 2(1)[OF call1]
  from 2(2) call1 have j: "j = i1" and ss: "ss = Var (iv i) # res1" by auto
  show ?case unfolding j ss using IH by force
qed simp

lemma gctxts_to_terms_intern_sound:
  fixes Cs :: "('f, 'v) gctxt list"
  assumes "gctxts_to_terms_intern i Cs = (j, ss)"
  shows "length ss = length Cs \<and> (\<forall> k < length Cs. ss ! k \<cdot> \<sigma> \<in> [Cs ! k])"
using assms
proof (induct i Cs arbitrary: j ss rule: gctxts_to_terms_intern.induct)
  case (1 i f ts Cs j ss)
  let ?call1 = "gctxts_to_terms_intern i ts"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  let ?call2 = "gctxts_to_terms_intern i1 Cs"
  obtain i2 res2 where call2: "?call2 = (i2,res2)" by force
  note IH = 1(1)[OF call1] 1(2)[OF call1[symmetric] refl call2]
  from 1(3) call1 call2 have j: "j = i2" and ss: "ss = Fun f res1 # res2" by auto
  show ?case unfolding j ss using IH by (simp add: all_Suc_conv)
next
  case (2 i Cs j ss)
  let ?call1 = "gctxts_to_terms_intern (i+1) Cs"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  note IH = 2(1)[OF call1]
  from 2(2) call1 have j: "j = i1" and ss: "ss = Var (iv i) # res1" by auto
  show ?case unfolding j ss using IH by (simp add: all_Suc_conv)
qed simp
  

lemma gctxts_to_terms_intern_complete:
  assumes inj: "inj iv"
  assumes res: "gctxts_to_terms_intern i Cs = (j, ss)" "\<And> k. k < length Cs \<Longrightarrow> reprs k \<in> [Cs ! k]"
  shows "\<exists> \<sigma>. \<forall> k < length Cs. reprs k = ss ! k \<cdot> \<sigma>"
  using res
proof (induct i Cs arbitrary: j ss reprs rule: gctxts_to_terms_intern.induct)
  case (1 i f ts Cs j ss reprs)
  let ?call1 = "gctxts_to_terms_intern i ts"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  from gctxts_to_terms_intern_sound[OF this] have len1: "length res1 = length ts" by simp
  let ?call2 = "gctxts_to_terms_intern i1 Cs"
  obtain i2 res2 where call2: "?call2 = (i2,res2)" by force
  from gctxts_to_terms_intern_sound[OF this] have len2: "length res2 = length Cs" by simp
  note IH = 1(1)[OF call1] 1(2)[OF call1[symmetric] refl call2]
  from 1(3) call1 call2 have j: "j = i2" and ss: "ss = Fun f res1 # res2" by auto
  {
    from 1(4)[of 0] have "reprs 0 \<in> [GCFun f ts]" by simp
    then obtain rs where rep: "reprs 0 = Fun f rs" and len: "length rs = length ts" and rec: "\<And> k. k < length ts \<Longrightarrow> rs ! k \<in> [ts ! k]" by auto
    let ?rep1 = "\<lambda> k. rs ! k"
    from IH(1)[of ?rep1, OF rec] obtain \<sigma> where id: "\<And> k. k < length ts \<Longrightarrow> rs ! k = res1 ! k \<cdot> \<sigma>" by blast
    have rs: "rs = map (\<lambda> t. t \<cdot> \<sigma>) res1"
      by (rule nth_equalityI, insert len len1 id, auto)
    with rep have rep: "\<exists> \<sigma>. reprs 0 = Fun f res1 \<cdot> \<sigma>" by auto
  } 
  then obtain \<sigma>1 where \<sigma>1: "reprs 0 = Fun f res1 \<cdot> \<sigma>1" by blast
  let ?rep2 = "shift reprs 1"
  have "\<exists>\<sigma>. \<forall>k<length Cs. ?rep2 k = res2 ! k \<cdot> \<sigma>"
  proof (rule IH(2))
    fix k
    assume "k < length Cs"
    then show "?rep2 k \<in> [Cs ! k]" using 1(4)[of "Suc k"] by simp
  qed
  then obtain \<sigma>2 where \<sigma>2: "\<And> k. k < length Cs \<Longrightarrow> ?rep2 k = res2 ! k \<cdot> \<sigma>2" by blast
  define \<sigma> where \<sigma>: "\<sigma> \<equiv> \<lambda> x. if the_inv iv x < i1 then \<sigma>1 x else \<sigma>2 x"
  have \<sigma>1: "reprs 0 = Fun f res1 \<cdot> \<sigma>" unfolding \<sigma>1 
  proof (rule term_subst_eq)
    fix x
    assume "x \<in> vars_term (Fun f res1)"
    with gctxts_to_terms_intern_vars[OF call1] 
    obtain k where x: "x = iv k" and k: "i \<le> k \<and> k < i1" by auto
    from the_inv_f_f[OF inj, of k, folded x] k show "\<sigma>1 x = \<sigma> x" unfolding \<sigma> by simp
  qed
  {
    fix k
    assume k: "k < length Cs"
    have "?rep2 k = res2 ! k \<cdot> \<sigma>" unfolding \<sigma>2[OF k]
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term (res2 ! k)"
      with gctxts_to_terms_intern_vars[OF call2, unfolded set_conv_nth len2] k
      obtain k where x: "x = iv k" and k: "i1 \<le> k \<and> k < i2" by auto
      from the_inv_f_f[OF inj, of k, folded x] k show "\<sigma>2 x = \<sigma> x" unfolding \<sigma> by simp
    qed
  } note \<sigma>2 = this
  show ?case unfolding j ss using \<sigma>1 \<sigma>2 
    by (intro exI[of _ \<sigma>], simp add: all_Suc_conv)
next
  case (2 i Cs j ss reprs)
  let ?call1 = "gctxts_to_terms_intern (i+1) Cs"
  obtain i1 res1 where call1: "?call1 = (i1,res1)" by force
  from gctxts_to_terms_intern_sound[OF this] have len1: "length res1 = length Cs" by simp
  note IH = 2(1)[OF call1]
  from 2(2) call1 have j: "j = i1" and ss: "ss = Var (iv i) # res1" by auto
  let ?rep2 = "shift reprs 1"
  have "\<exists>\<sigma>. \<forall>k<length Cs. ?rep2 k = res1 ! k \<cdot> \<sigma>"
  proof (rule IH(1))
    fix k
    assume "k < length Cs"
    then show "?rep2 k \<in> [Cs ! k]" using 2(3)[of "Suc k"] by simp
  qed
  then obtain \<sigma>2 where \<sigma>2: "\<And> k. k < length Cs \<Longrightarrow> ?rep2 k = res1 ! k \<cdot> \<sigma>2" by blast
  define \<sigma> where \<sigma>: "\<sigma> \<equiv> \<lambda> x. if x = iv i then reprs 0 else \<sigma>2 x"
  have \<sigma>1: "reprs 0 = Var (iv i) \<cdot> \<sigma>" unfolding \<sigma> by simp
  {
    fix k
    assume k: "k < length Cs"
    have "?rep2 k = res1 ! k \<cdot> \<sigma>" unfolding \<sigma>2[OF k]
    proof (rule term_subst_eq)
      fix x
      assume "x \<in> vars_term (res1 ! k)"
      with gctxts_to_terms_intern_vars[OF call1, unfolded set_conv_nth len1] k
      obtain k where x: "x = iv k" and k: "i + 1 \<le> k \<and> k < i1" by auto
      from the_inv_f_f[OF inj, of k, folded x] the_inv_f_f[OF inj, of i] k show "\<sigma>2 x = \<sigma> x" unfolding \<sigma> by (cases "x = iv i", auto)
    qed
  } note \<sigma>2 = this
  show ?case unfolding j ss using \<sigma>1 \<sigma>2 
    by (intro exI[of _ \<sigma>], simp add: all_Suc_conv)
qed simp
end

definition gc_matcher :: "('f,string)gctxt \<Rightarrow> ('f,string)term \<Rightarrow> ('f,string)subst option" where
  "gc_matcher C l \<equiv> 
     map_option fst 
     (mgu_vd_string l (hd (snd (gctxts_to_terms_intern (\<lambda> i. Cons (CHR ''x'') (show i)) 0 [C]))))"


lemma gc_matcher_complete: assumes match: "l \<cdot> \<sigma> \<in> [C]"
  shows "\<exists> \<mu> \<delta>. gc_matcher C l = Some \<mu> \<and> \<sigma> = \<mu> \<circ>\<^sub>s \<delta>"
proof -
  let ?iv = "\<lambda> i. Cons (CHR ''x'') (show (i :: nat))"
  obtain ts i where call: "gctxts_to_terms_intern ?iv 0 [C] = (i,ts)" by force
  from gctxts_to_terms_intern_sound[OF call] obtain t where ts: "ts = [t]" by (cases ts, auto)
  from inj_show_nat have "inj ?iv" unfolding inj_on_def by auto
  from gctxts_to_terms_intern_complete[OF this call[unfolded ts], of "\<lambda> _. l \<cdot> \<sigma>"] match
  obtain \<sigma>' where unif: "l \<cdot> \<sigma> = t \<cdot> \<sigma>'" by auto
  from mgu_vd_string_complete[OF unif]
  obtain \<mu>1 \<mu>2 \<delta> where "mgu_vd_string l t = Some (\<mu>1, \<mu>2)" and 
    "\<sigma> = \<mu>1 \<circ>\<^sub>s \<delta>" by blast
  then show ?thesis unfolding gc_matcher_def call ts by auto
qed

lemma gc_matcher_sound: assumes match: "gc_matcher C l = Some \<mu>"
  shows "l \<cdot> \<mu> \<cdot> \<sigma> \<in> [C]"
proof -
  let ?iv = "\<lambda> i. Cons (CHR ''x'') (show (i :: nat))"
  obtain ts i where call: "gctxts_to_terms_intern ?iv 0 [C] = (i,ts)" by force
  from gctxts_to_terms_intern_sound[OF call] obtain t where 
    ts: "ts = [t]" and mem: "\<And> \<sigma>. t \<cdot> \<sigma> \<in> [C]" by (cases ts, auto)
  note match = match[unfolded gc_matcher_def call ts]
  from match
  obtain p where mgu: "mgu_vd_string l t = Some p" by auto
  obtain \<mu>1 \<mu>2 where p: "p = (\<mu>1, \<mu>2)" by force
  from match mgu p have mu: "\<mu> = \<mu>1" by simp
  from mgu_vd_string_sound[OF mgu[unfolded p]] have id: "l \<cdot> \<mu>1 = t \<cdot> \<mu>2" .
  then have "l \<cdot> \<mu> \<cdot> \<sigma> = t \<cdot> (\<mu>2 \<circ>\<^sub>s \<sigma>)" unfolding mu by simp
  from mem[of "\<mu>2 \<circ>\<^sub>s \<sigma>", folded this] show ?thesis .
qed
end
hide_const gctxts_to_terms_intern
declare merge.simps[simp del]

no_notation Ground_Context.GCHole ("\<box>")
no_notation Ground_Context.equiv_class ("[_]")
notation Subterm_and_Context.Hole ("\<box>")

end

