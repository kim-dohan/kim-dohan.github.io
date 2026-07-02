theory Lexicographic_Orders
imports 
  Quasi_Order
begin


subsection \<open>Products\<close>

locale lexcomp =
  1: ord less_eq1 less1 + 2: ord less_eq2 less2
  for less_eq1 :: "'a \<Rightarrow> 'a \<Rightarrow> bool" (infix "\<le>\<^sub>1" 50)
  and less1  (infix "<\<^sub>1" 50)
  and less_eq2 :: "'b \<Rightarrow> 'b \<Rightarrow> bool" (infix "\<le>\<^sub>2" 50)
  and less2 (infix "<\<^sub>2" 50)
begin

definition less_eq where "less_eq x y \<equiv> fst x <\<^sub>1 fst y \<or> fst x \<le>\<^sub>1 fst y \<and> snd x \<le>\<^sub>2 snd y"
notation less_eq (infix "\<le>\<^sub>1\<^sub>2" 50)
definition less where "less x y \<equiv> fst x <\<^sub>1 fst y \<or> fst x \<le>\<^sub>1 fst y \<and> snd x <\<^sub>2 snd y"
notation less (infix "<\<^sub>1\<^sub>2" 50)

sublocale ord less_eq less.

lemma less_eq_simp: "less_eq (x1,x2) (y1,y2) \<longleftrightarrow> x1 <\<^sub>1 y1 \<or> x1 \<le>\<^sub>1 y1 \<and> x2 \<le>\<^sub>2 y2" by (simp add: less_eq_def)
lemma less_simp: "less (x1,x2) (y1,y2) \<longleftrightarrow> x1 <\<^sub>1 y1 \<or> x1 \<le>\<^sub>1 y1 \<and> x2 <\<^sub>2 y2" by (simp add: less_def)

lemma less_eq_cases[elim, consumes 1, case_names fst snd]:
  assumes "less_eq x y" and "fst x <\<^sub>1 fst y \<Longrightarrow> P" and "fst x \<le>\<^sub>1 fst y \<Longrightarrow> snd x \<le>\<^sub>2 snd y \<Longrightarrow> P"
  shows P
  using assms by (cases x; cases y, auto simp: less_eq_simp)

lemma less_cases[elim, consumes 1, case_names fst snd]:
  assumes "less x y" and "fst x <\<^sub>1 fst y \<Longrightarrow> P" and "fst x \<le>\<^sub>1 fst y \<Longrightarrow> snd x <\<^sub>2 snd y \<Longrightarrow> P"
  shows P
  using assms by (cases x; cases y, auto simp: less_simp)

end

locale lexcomp_quasi_order = lexcomp + 1: quasi_order less_eq1 less1 + 2: quasi_order less_eq2 less2
begin

sublocale quasi_order less_eq less
proof
  fix x y z :: "'a \<times> 'b"
  { assume "fst x <\<^sub>1 fst y" also assume "fst y <\<^sub>1 fst z" finally have "fst x <\<^sub>1 fst z". } note 1 = this
  { assume "fst x <\<^sub>1 fst y" also assume "fst y \<le>\<^sub>1 fst z" finally have "fst x <\<^sub>1 fst z". } note 2 = this
  { assume "fst x \<le>\<^sub>1 fst y" also assume "fst y <\<^sub>1 fst z" finally have "fst x <\<^sub>1 fst z". } note 3 = this
  { assume "fst x \<le>\<^sub>1 fst y" also assume "fst y \<le>\<^sub>1 fst z" finally have "fst x \<le>\<^sub>1 fst z". } note 4 = this
  { assume "snd x \<le>\<^sub>2 snd y" also assume "snd y \<le>\<^sub>2 snd z" finally have "snd x \<le>\<^sub>2 snd z". } note 5 = this
  { assume "snd x <\<^sub>2 snd y" also assume "snd y \<le>\<^sub>2 snd z" finally have "snd x <\<^sub>2 snd z". } note 6 = this
  { assume "snd x \<le>\<^sub>2 snd y" also assume "snd y <\<^sub>2 snd z" finally have "snd x <\<^sub>2 snd z". } note 7 = this
  note [simp] = less_simp less_eq_simp 
  show "x \<le>\<^sub>1\<^sub>2 x" by (cases x,auto)
  from 1 2 3 4 5 show "x \<le>\<^sub>1\<^sub>2 y \<Longrightarrow> y \<le>\<^sub>1\<^sub>2 z \<Longrightarrow> x \<le>\<^sub>1\<^sub>2 z" by (cases x, cases y, cases z, auto)
  from 1 2 3 4 6 show "x <\<^sub>1\<^sub>2 y \<Longrightarrow> y \<le>\<^sub>1\<^sub>2 z \<Longrightarrow> x <\<^sub>1\<^sub>2 z" by (cases x, cases y, cases z, auto)
  from 1 2 3 4 7 show "x \<le>\<^sub>1\<^sub>2 y \<Longrightarrow> y <\<^sub>1\<^sub>2 z \<Longrightarrow> x <\<^sub>1\<^sub>2 z" by (cases x, cases y, cases z, auto)
  from "1.less_imp_le" "2.less_imp_le" show "x <\<^sub>1\<^sub>2 y \<Longrightarrow> x \<le>\<^sub>1\<^sub>2 y" by (cases x, cases y, auto)
qed

end


locale lexcomp_wf_order = lexcomp + 1: wf_order less_eq1 less1 + 2: wf_order less_eq2 less2
begin

sublocale lexcomp_quasi_order..

sublocale wf_order less_eq less
proof
  fix P :: "'a \<times> 'b \<Rightarrow> bool" and z :: "'a \<times> 'b"
  assume P: "\<And>x. (\<And>y. y <\<^sub>1\<^sub>2 x \<Longrightarrow> P y) \<Longrightarrow> P x"
  show "P z"
  proof (induct z)
    case (Pair a b)
    show "P (a, b)"
    proof (induct a arbitrary: b rule: "1.less_induct")
      case (less a\<^sub>1) note a\<^sub>1 = this
      have "a' \<le>\<^sub>1 a\<^sub>1 \<Longrightarrow> P (a', b)" for a'
      proof (induct b arbitrary: a' rule: "2.less_induct")
        case (less b\<^sub>1) note b\<^sub>1 = this
        show "P (a', b\<^sub>1)"
        proof (rule P)
          fix p assume p: "p <\<^sub>1\<^sub>2 (a', b\<^sub>1)"
          show "P p"
          proof (cases "fst p <\<^sub>1 a'")
            case True
            with b\<^sub>1(2) "1.less_le_trans" have "fst p <\<^sub>1 a\<^sub>1" by auto
            from a\<^sub>1[OF this] have "P (fst p, snd p)".
            then show ?thesis by simp
          next
            case False
            with p have 1: "fst p \<le>\<^sub>1 a'" and 2: "snd p <\<^sub>2 b\<^sub>1" by auto
            note 1 also note b\<^sub>1(2) finally have "fst p \<le>\<^sub>1 a\<^sub>1".
            from b\<^sub>1(1)[OF 2 this] have "P (fst p, snd p)".
            with 1 show ?thesis by simp
          qed
        qed
      qed
      then show "P (a\<^sub>1,b)" by auto
    qed
  qed
qed

lemma less_induct2[case_names less]:
  assumes "\<And>x1 x2. (\<And>y1 y2. (y1,y2) <\<^sub>1\<^sub>2 (x1,x2) \<Longrightarrow> thesis y1 y2) \<Longrightarrow> thesis x1 x2"
  shows "thesis z1 z2"
proof-
  note less_induct
  from assms have "(\<And>y1 y2. (y1,y2) <\<^sub>1\<^sub>2 x \<Longrightarrow> thesis y1 y2) \<Longrightarrow> thesis (fst x) (snd x)" for x by (cases x, auto)
  with less_induct[of "\<lambda>(z1, z2). thesis z1 z2" "(z1,z2)",simplified] show ?thesis by auto
qed

end


subsection \<open>Lexicographic composition of a list of order pairs\<close>

fun lex_less_eq
where "lex_less_eq [(le,l)] [x] [y] \<longleftrightarrow> le x y"
    | "lex_less_eq ((le,l)#ord#ords) (x#x'#xs) (y#y'#ys) \<longleftrightarrow> lexcomp.less_eq le l (lex_less_eq (ord#ords)) (x,x'#xs) (y,y'#ys)"
    | "lex_less_eq _ xs ys \<longleftrightarrow> xs = ys"

fun lex_less
where "lex_less [(le,l)] [x] [y] \<longleftrightarrow> l x y"
    | "lex_less ((le,l)#ord#ords) (x#x'#xs) (y#y'#ys) \<longleftrightarrow> lexcomp.less le l (lex_less (ord#ords)) (x,x'#xs) (y,y'#ys)"
    | "lex_less _ _ _ \<longleftrightarrow> False"

locale ord_list = fixes ords :: "(('a \<Rightarrow> 'a \<Rightarrow> bool) \<times> ('a \<Rightarrow> 'a \<Rightarrow> bool)) list"
begin
abbreviation(input) less_eq where "less_eq \<equiv> lex_less_eq ords"
abbreviation(input) less where "less \<equiv> lex_less ords"
sublocale ord less_eq less.
end

locale quasi_order_list = ord_list +
  assumes quasi_order_list: "\<And>le l. (le,l) \<in> set ords \<Longrightarrow> class.quasi_order le l"
begin

sublocale quasi_order less_eq less
proof(insert quasi_order_list, induct ords)
  case Nil
  then show ?case by (unfold_locales, auto)
next
  case 1: (Cons a ords)
  show ?case
  proof(cases a)
    case [simp]: (Pair le l)
    from 1 interpret 1: quasi_order le l by auto
    note [dest] = "1.order_trans" "1.less_trans" "1.le_less_trans" "1.less_le_trans"
    let ?le = "lex_less_eq (a # ords)"
    let ?l = "lex_less (a # ords)"
    show ?thesis
    proof (cases ords)
      case [simp]: Nil
      show ?thesis
      proof (unfold_locales)
        fix x y z
        show "?le x x" by (cases x rule: list_3_cases, auto)
        show "?le x y \<Longrightarrow> ?le y z \<Longrightarrow> ?le x z"
         and "?l x y \<Longrightarrow> ?le y z \<Longrightarrow> ?l x z"
         and "?le x y \<Longrightarrow> ?l y z \<Longrightarrow> ?l x z"
          by (atomize(full), (cases x rule:list_3_cases; cases y rule:list_3_cases; cases z rule:list_3_cases), auto)
        show "?l x y \<Longrightarrow> ?le x y" by (cases x rule: list_3_cases; cases y rule: list_3_cases, auto simp: "1.less_imp_le")
      qed
    next
      case [simp]: (Cons b ords)
      from 1 interpret IH: lexcomp_quasi_order le l "lex_less_eq (b#ords)" "lex_less (b#ords)" by (unfold lexcomp_quasi_order_def, auto)
      note [dest] = IH.order_trans IH.less_trans IH.le_less_trans IH.less_le_trans
      show ?thesis
      proof (unfold_locales)
        fix x y z
        show "?le x x" by (cases x rule: list_3_cases, auto)
        show "?le x y \<Longrightarrow> ?le y z \<Longrightarrow> ?le x z"
         and "?l x y \<Longrightarrow> ?le y z \<Longrightarrow> ?l x z"
         and "?le x y \<Longrightarrow> ?l y z \<Longrightarrow> ?l x z"
          by (atomize(full), (cases x rule:list_3_cases; cases y rule:list_3_cases; cases z rule:list_3_cases), auto)
        show "?l x y \<Longrightarrow> ?le x y" by (cases x rule: list_3_cases; cases y rule: list_3_cases, auto simp: "IH.less_imp_le")
      qed
    qed
  qed
qed

end

locale wf_order_list = ord_list +
  assumes wf_order_list: "\<And>le l. (le,l) \<in> set ords \<Longrightarrow> class.wf_order le l"
begin

sublocale quasi_order_list ords using wf_order_list by (auto simp: quasi_order_list_def class.wf_order_def)

sublocale wf_order less_eq less
proof(insert wf_order_list, induct ords)
  case Nil
  then show ?case by (unfold_locales, auto)
next
  case IH: (Cons a ords)
  show ?case
  proof(cases a)
    case a[simp]: (Pair le l)
    from IH interpret q: quasi_order_list "a#ords" by (auto simp: quasi_order_list_def class.wf_order_def)
    from IH interpret step: lexcomp_wf_order le l "lex_less_eq (ords)" "lex_less (ords)" by (auto simp: lexcomp_wf_order_def)
    show ?thesis
    proof (unfold_locales)
      fix P xs
      assume scheme: "\<And>x. (\<And>y. lex_less (a # ords) y x \<Longrightarrow> P y) \<Longrightarrow> P x"
      show "P xs"
      proof (cases ords)
        case ords: Nil
        show ?thesis
        proof (cases xs rule: list_3_cases)
          case xs: (1 x)
          show ?thesis
          proof (unfold xs, induct x rule: "step.1.less_induct")
            case IH1: (less x)
            show ?case
            proof(rule scheme, unfold ords)
              from IH1 show "lex_less [a] ys [x] \<Longrightarrow> P ys" for ys by (cases ys rule: list_3_cases, auto)
            qed
          qed
        next
          case Nil show ?thesis by (rule scheme, auto simp: ords Nil)
        next
          case 2 show ?thesis by (rule scheme, auto simp: ords 2)
        qed
      next
        case [simp]: (Cons b ords')
        show ?thesis
        proof (cases xs)
          case Nil show ?thesis by (rule scheme, auto simp: Nil)
        next
          case xs: (Cons x xs')
          show ?thesis
          proof (cases xs')
            case [simp]: Nil
            show ?thesis
            proof (rule scheme)
              show "lex_less (a # ords) y xs \<Longrightarrow> P y" for y by (cases y rule: list_3_cases, auto simp: xs)
            qed
          next
            case xs': (Cons x' xs'')
            from IH interpret step2: lexcomp_wf_order le l "lex_less_eq (b#ords')" "lex_less (b#ords')" by (auto simp: lexcomp_wf_order_def)
            show ?thesis
            proof(unfold xs, insert xs', induct x xs' arbitrary: x' xs'' rule: step.less_induct2)
              case (less x xs')
              show ?case
              proof (rule scheme)
                from less show "lex_less (a # ords) ys (x # xs') \<Longrightarrow> P ys" for ys by (cases ys rule: list_3_cases, auto)
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

end


end
