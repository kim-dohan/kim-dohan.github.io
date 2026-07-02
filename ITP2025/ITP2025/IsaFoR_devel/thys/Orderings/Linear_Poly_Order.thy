(*
Author:  Alexander Krauss <krauss@in.tum.de> (2009)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Linear_Poly_Order
imports
  Term_Order_Extension
  Linear_Polynomial
  First_Order_Rewriting.Term_Impl
  Auxx.Name
  Auxx.Map_Choice
begin

text \<open>we first head for polynomial interpretations\<close>

type_synonym ('f, 'a) lpoly_inter = "'f \<times> nat \<Rightarrow> ('a \<times> 'a list)"
type_synonym ('f, 'a) lpoly_interL = "(('f \<times> nat) \<times> ('a \<times> 'a list)) list"

context
  fixes R :: "('a, 'b) lpoly_order_semiring_scheme" (structure)
begin
(* default interpretation f/n \<rightarrow> default \<oplus> x_1 \<oplus> ... \<oplus> x_n *)
definition to_lpoly_inter :: "('f :: compare_order, 'a) lpoly_interL \<Rightarrow> ('f, 'a) lpoly_inter" where
  "to_lpoly_inter I = fun_of_map_fun (ceta_map_of I) (\<lambda> fn. (default R,replicate (snd fn) \<one>))"

definition create_af :: "('f :: compare_order, 'a) lpoly_interL \<Rightarrow> 'f af" where
  "create_af I \<equiv> fun_of_map_fun' (ceta_map_of I) (\<lambda> (f,n) . {0 ..< n}) (\<lambda> (c,coeffs). 
  set ([ i . (c,i) <- zip coeffs [0 ..< length coeffs], c \<noteq> \<zero>]))"

definition create_mono_af :: "('f :: compare_order, 'a) lpoly_interL \<Rightarrow> 'f af" where
  "create_mono_af I \<equiv> if psm then fun_of_map_fun' (ceta_map_of I) (\<lambda> (f,n) . {0 ..< n}) 
  (\<lambda> (c,coeffs). set ([ i . c \<succeq> \<zero>, (c',i) <- zip coeffs [0 ..< length coeffs], c' = \<one> \<or> check_mono c'])) else empty_af"
end

context 
  fixes R :: "('a, 'b) ordered_semiring_scheme" (structure)
begin
fun
  eval_termI :: "('f, 'a) lpoly_inter \<Rightarrow> ('v, 'a) p_ass \<Rightarrow> ('f, 'v) term \<Rightarrow> 'a" 
where
  "eval_termI pi \<alpha> (Var x) = \<alpha> x"
| "eval_termI pi \<alpha> (Fun f ts) =
    (let (a, as) = pi (f, length ts) in
    Max \<zero> (a \<oplus> (list_sum R (map (\<lambda> at. fst at \<otimes> (eval_termI pi \<alpha> (snd at))) (zip as ts)))))"

context
  notes [[function_internals, inductive_internals]]
begin
fun PleftI :: "('f, 'a) lpoly_inter \<Rightarrow> ('f, 'v) term \<Rightarrow> ('v, 'a) l_poly"
where
  "PleftI pi (Var x) = (LPoly \<zero> [(x, \<one>)] )"
| "PleftI pi (Fun f ts) = (
    let (c, as) = pi (f, length ts) in
    (case (sum_lpoly R (LPoly c []) (list_sum_lpoly R (map (\<lambda> at .
      (mul_lpoly R (fst at)  (PleftI pi (snd at)))) (zip as ts)))) :: ('v, 'a) l_poly of
      LPoly d [] \<Rightarrow> LPoly (Max \<zero> d) []
    | p \<Rightarrow> p))"

fun PrightI :: "('f, 'a) lpoly_inter \<Rightarrow> ('f, 'v) term \<Rightarrow> ('v, 'a) l_poly"
where
  "PrightI pi (Var x) = (LPoly \<zero> [(x, \<one>)] )"
| "PrightI pi (Fun f ts) = (
    let (c, as) = pi (f, length ts) in
    (case (sum_lpoly R (LPoly c []) (list_sum_lpoly R (map (\<lambda> at .
      (mul_lpoly R (fst at) (PrightI pi (snd at)))) (zip as ts)))) :: ('v, 'a) l_poly of
      LPoly d vp \<Rightarrow> LPoly (Max \<zero> d) vp))"
end

definition coeffs_of_constraint :: "('f, 'a) lpoly_inter \<Rightarrow> ('f, 'v) rule \<Rightarrow> ('a \<times> 'a) list"
where
  "coeffs_of_constraint pi st =
    [(a, b). a \<leftarrow> coeffs_of_lpoly R (PleftI pi (fst st)),
             b \<leftarrow> coeffs_of_lpoly R (PrightI pi (snd st))]"

end

context 
  fixes R :: "('a :: showl, 'b) lpoly_order_semiring_scheme" (structure)
begin
fun
  check_polo_ns
where
  "check_polo_ns pi (s, t) = do {
    let left = PleftI R pi s;
    let right = PrightI R pi t;
    check_lpoly_ns R left right
      <+? (\<lambda>e. showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' >= '') \<circ> showsl t \<circ> showsl_nl \<circ> e)
  }"

fun
  check_polo_s
where
  "check_polo_s pi (s, t) = do {
    let left = PleftI R pi s;
    let right = PrightI R pi t;
    check_lpoly_s R left right
      <+? (\<lambda>e. showsl (STR ''could not ensure '') \<circ> showsl s \<circ> showsl (STR '' > '') \<circ> showsl t \<circ> showsl_nl \<circ> e)
  }"

definition
  check_poly_mono_npsm :: "('f \<times> nat) list \<Rightarrow> ('f :: showl, 'a) lpoly_interL \<Rightarrow> showsl check"
where
  "check_poly_mono_npsm F pi = check_allm (\<lambda>((f, n), (c, cs)). do {
    check (n = Suc 0 \<longrightarrow> c = \<zero>) (showsl (STR ''constant part '') \<circ> showsl c \<circ> showsl (STR '' must be 0\<newline>''));
    check (n = length cs) (showsl (STR ''the arity is not the same as the number of arguments\<newline>''));
    check (n \<le> Suc 0) (showsl (STR ''symbol has arity larger than 1\<newline>''))
  } <+? (\<lambda>s. showsl (STR ''problem with monotonicity due to interpretation of '') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl_nl \<circ> s)
  ) pi >>
  check_subseteq F (map fst pi)
    <+? (\<lambda> fn. showsl (STR ''unknown interpretation for '') \<circ> showsl fn \<circ> showsl_nl)"

lemma check_poly_mono_npsm_mono: assumes "isOK(check_poly_mono_npsm F pi)" and "set G \<subseteq> set F" 
  shows "isOK(check_poly_mono_npsm G pi)" 
  using assms unfolding check_poly_mono_npsm_def by auto

definition
  check_poly_mono :: "('f :: showl, 'a) lpoly_interL \<Rightarrow> showsl check"
where
  "check_poly_mono = check_allm (\<lambda>((f, n), (c, cs)). do {
    check (c \<succeq> \<zero>)
      (showsl (STR ''constant part '') \<circ> showsl c \<circ> showsl (STR '' must be at least '') \<circ> showsl \<zero> \<circ> showsl_nl);
    check (n \<le> length cs) (showsl (STR ''the last argument is ignored\<newline>''));
    check_allm (\<lambda>d. check (check_mono d)
      (showsl (STR ''coefficient '') \<circ> showsl d \<circ> showsl (STR '' is not allowed\<newline>''))) cs
  } <+? (\<lambda>s. showsl (STR ''problem with monotonicity due to interpretation of '') 
       \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl_nl \<circ> s)
  )"

fun
  check_lpoly_coeffs :: "('f :: showl, 'a) lpoly_interL \<Rightarrow> showsl check"
where
  "check_lpoly_coeffs I =
    check_allm (\<lambda>((f, n), (c, cs)). do {
      check (c \<in> carrier R)
        (showsl (STR ''constant part '') \<circ> showsl c \<circ> showsl (STR '' is not well-formed\<newline>''));
      check (length cs \<le> n) 
        (showsl (STR ''number of coefficients exceeds arity of symbol '') \<circ> showsl f);
      check (arc_pos c \<or> Bex (set cs) arc_pos)
        (showsl (STR ''could not find positive entry which is required for arctic interpretations\<newline>''));
      check_allm (\<lambda>a. check (a \<succeq> \<zero> \<and> a \<in> carrier R)
        (showsl (STR ''coefficient '') \<circ> showsl a \<circ> showsl (STR '' is not allowed\<newline>''))) cs
  } <+?  (\<lambda>s. showsl (STR ''problem with interpretation of '') \<circ> showsl f \<circ> showsl (STR ''/'') \<circ> showsl n \<circ> showsl_nl \<circ> s)
  ) I"

end

context lpoly_order
begin
declare poly_simps[simp] poly_order_simps[simp]

abbreviation
  eval_term ::
    "('f, 'a) lpoly_inter \<Rightarrow> ('v, 'a) p_ass \<Rightarrow> ('f, 'v) term \<Rightarrow> 'a" ("_\<guillemotleft>_,_>>" [1000, 0, 0] 50)
where
  "eval_term \<equiv> eval_termI R"

abbreviation wf_lpoly_inter :: "('f, 'a) lpoly_inter \<Rightarrow> bool"
where
  "wf_lpoly_inter pi \<equiv>
    (\<forall> fn. fst (pi fn) \<in> carrier R \<and> (\<forall> a. a \<in> set (snd (pi fn)) \<longrightarrow> a \<in> carrier R \<and> a \<succeq> \<zero>)) \<and>
    (\<forall> fn. arc_pos (fst (pi fn)) \<or> (\<exists> a \<in> set (take (snd fn) (snd (pi fn))). arc_pos a))"

end

locale linear_poly_order =
  lpoly_order R for R :: "('a :: showl) lpoly_order_semiring" (structure) +
  fixes pi :: "('f :: {showl, compare_order}, 'a) lpoly_inter"
  assumes wf_pi: "wf_lpoly_inter pi"
begin

lemma wf_terms [simp]:
  assumes wf_ass: "wf_ass R \<alpha>"
  shows "(pi\<guillemotleft>\<alpha>, t>>) \<in> carrier R"
proof (induct t)
  case (Var x)
  from wf_ass have "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
  then show ?case by auto
next
  case (Fun f ts)
  show ?case
  proof (cases "pi (f,length ts)")
    case (Pair a as)
    have "list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts)) \<in> carrier R" (is "?ls \<in> _")
    proof (rule wf_list_sum, rule)
      fix p
      assume "p \<in> set (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts))" (is "p \<in> set (map _ ?zip)")
      from this obtain a' t where p: "p = a' \<otimes> (pi\<guillemotleft>\<alpha>,t>>)" and ab: "(a',t) \<in> set ?zip" by auto
      from ab have a': "a' \<in> set as" and t: "t \<in> set ts" using set_zip_leftD[where x = a' and y = t] set_zip_rightD[where y = t and x = a'] by auto
      from a' Pair have "a' \<in> set (snd (pi (f,length ts)))" by auto
      with Fun wf_pi have "a' \<in> carrier R" by auto
      with Fun t p show "p \<in> carrier R" by auto
    qed
    from wf_pi have "fst (pi (f,length ts)) \<in> carrier R" by auto
    with Pair \<open>?ls \<in> carrier R\<close> have "(a \<oplus> ?ls) \<in> carrier R" by auto
    then show ?thesis using Pair by (auto simp: wf_max0)
  qed
qed

lemma pos_term [simp]:
  assumes wf_ass: "wf_ass R \<alpha>"
    and pos_ass: "pos_ass \<alpha>"
  shows "(pi\<guillemotleft>\<alpha>, t>>) \<succeq> \<zero>"
proof (induct t)
  case (Var x)
  from wf_ass pos_ass have "\<alpha> x \<in> carrier R \<and> \<alpha> x \<succeq> \<zero>" unfolding wf_ass_def pos_ass_def by auto
  then show ?case by auto
next
  case (Fun f ts)
  show ?case
  proof (cases "pi (f,length ts)")
    case (Pair a as)
    have "list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts)) \<in> carrier R" (is "?ls \<in> _")
    proof (rule wf_list_sum, rule)
      fix p
      assume "p \<in> set (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts))" (is "p \<in> set (map _ ?zip)")
      from this obtain a' t where p: "p = a' \<otimes> (pi\<guillemotleft>\<alpha>,t>>)" and ab: "(a',t) \<in> set ?zip" by auto
      from ab have a': "a' \<in> set as" and t: "t \<in> set ts" using set_zip_leftD[where x = a' and y = t] set_zip_rightD[where y = t and x = a'] by auto
      from a' Pair have "a' \<in> set (snd (pi (f,length ts)))" by auto
      with Fun wf_pi have "a' \<in> carrier R" by auto
      with Fun t p wf_ass wf_pi show "p \<in> carrier R" by auto
    qed
    from wf_pi have "fst (pi (f,length ts)) \<in> carrier R" by auto
    with Pair \<open>?ls \<in> carrier R\<close> have "a \<oplus> ?ls \<in> carrier R" by auto
    then show ?thesis using Pair by (auto simp: wf_max0 max_ge)
  qed
qed

definition apos_ass :: "('v, 'a) p_ass \<Rightarrow> bool"
where
  "apos_ass \<alpha> \<longleftrightarrow> (\<forall> x. arc_pos (\<alpha> x))"

lemma apos_term [simp]:
  assumes wf_ass: "wf_ass R \<alpha>"
    and apos_ass: "apos_ass \<alpha>"
  shows "arc_pos (pi\<guillemotleft>\<alpha>, t>>)"
proof (induct t)
  case (Var x)
  from apos_ass show ?case unfolding apos_ass_def by auto
next
  case (Fun f ts)
  show ?case
  proof (cases "pi (f,length ts)")
    case (Pair a as)
    have wf_args: "set (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts)) \<subseteq> carrier R"
    proof 
      fix p
      assume "p \<in> set (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts))" (is "p \<in> set (map _ ?zip)")
      from this obtain a' t where p: "p = a' \<otimes> (pi\<guillemotleft>\<alpha>,t>>)" and ab: "(a',t) \<in> set ?zip" by auto
      from ab have a': "a' \<in> set as" and t: "t \<in> set ts" using set_zip_leftD[where x = a' and y = t] set_zip_rightD[where y = t and x = a'] by auto
      from a' Pair have "a' \<in> set (snd (pi (f,length ts)))" by auto
      with Fun wf_pi have "a' \<in> carrier R" by auto
      with Fun t p wf_ass wf_pi show "p \<in> carrier R" by auto
    qed
    have "list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip as ts)) \<in> carrier R" (is "?ls \<in> _")
      by (rule wf_list_sum, rule wf_args)
    from wf_pi have "fst (pi (f,length ts)) \<in> carrier R" by auto
    with Pair have wf_a: "a \<in> carrier R" by auto
    with wf_pi have "arc_pos (fst (pi (f,length ts))) \<or> (\<exists> a \<in> set (take (length ts) (snd (pi (f,length ts)))). arc_pos a)" (is "?ac \<or> ?aa") by auto
    then show ?thesis
    proof
      assume "?ac"
      then have "arc_pos (a \<oplus> ?ls)" and "(a \<oplus> ?ls) \<in> carrier R" using Pair \<open>?ls \<in> carrier R\<close> wf_a arc_pos_plus by auto
      then show ?thesis using Pair by auto
    next
      assume ?aa
      from this obtain c where c: "c \<in> set (take (length ts) as) \<and> arc_pos c" using Pair by auto
      from wf_pi have "(\<forall> b \<in> set (snd (pi (f,length ts))). b \<in> carrier R)" by auto
      with Pair have wf_as: "\<forall> b \<in> set as. b \<in> carrier R" by auto
      from Pair Fun have rec: "\<forall> t \<in> set ts. arc_pos (pi\<guillemotleft>\<alpha>,t>>)" by auto
      from c wf_as rec wf_args have aa: "arc_pos ?ls"
      proof (induct ts arbitrary: as)
        case (Cons t ts) note oCons = this
        show ?case
        proof (cases as)
          case Nil
          with Cons show ?thesis by auto
        next
          case (Cons b bs)
          let ?prod = "b \<otimes> (pi\<guillemotleft>\<alpha>,t>>)"
          have wf: "(pi\<guillemotleft>\<alpha>,t>>) \<in> carrier R \<and> b \<in> carrier R \<and> ?prod \<in> carrier R" using wf_ass Cons oCons by auto
          then have wf_p: "?prod \<in> carrier R" by auto
          show ?thesis
          proof (cases "b = c")
            case True
            show ?thesis 
              by (simp add: Cons, rule arc_pos_plus[OF arc_pos_mult wf_p], simp add: True c, insert wf Cons oCons, auto)
          next
            case False
            with Cons oCons have "c \<in> set (take (length ts) bs)" by auto
            with Cons oCons have ap: "arc_pos (list_sum R (map (\<lambda> at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip bs ts)))" (is "arc_pos ?ls") by auto
            with Cons oCons have "?ls \<in> carrier R" by auto
            show ?thesis 
              by (simp add: Cons, simp only: a_comm[OF \<open>?prod \<in> carrier R\<close> \<open>?ls \<in> carrier R\<close>], rule arc_pos_plus[OF ap], insert Cons oCons wf, auto) 
          qed
        qed
      qed simp
      have "a \<oplus> ?ls = ?ls \<oplus> a" using wf_a \<open>?ls \<in> carrier R\<close> by (rule a_comm)
      then have "arc_pos (a \<oplus> ?ls)" and "a \<oplus> ?ls \<in> carrier R" using aa \<open>?ls \<in> carrier R\<close> wf_a arc_pos_plus by auto
      then show ?thesis using Pair by auto
    qed
  qed
qed

definition inter_s :: "('f, 'v) trs"
where
  "inter_s = {(s, t). (\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow>  (pi\<guillemotleft>\<alpha>, s>>) \<succ> (pi\<guillemotleft>\<alpha>, t>>))}"

definition inter_ns :: "('f, 'v) trs"
where
  "inter_ns = {(s, t). (\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>, s>>) \<succeq> (pi\<guillemotleft>\<alpha>, t>>))}"

definition default_ass :: "('v, 'a) p_ass"
where
  "default_ass = (\<lambda> x. default R)"

lemma wf_pos_apos_default_ass [simp]:
  "wf_ass R default_ass \<and> pos_ass default_ass \<and> apos_ass default_ass"
  unfolding wf_ass_def pos_ass_def apos_ass_def default_ass_def
  by auto

lemma interpr_subst:
  assumes wf_ass: "wf_ass R \<alpha>"
  shows "(pi\<guillemotleft>\<alpha>, t \<cdot> \<sigma>>>) = (pi\<guillemotleft>(\<lambda> x. (pi\<guillemotleft>\<alpha>, \<sigma> x>>)),t>>)"
proof -
  have "(pi\<guillemotleft>\<alpha>, t \<cdot> \<sigma>>>) = (pi\<guillemotleft>(\<lambda> x. (pi\<guillemotleft>\<alpha>, \<sigma> x>>)),t>>)" (is "_ = (pi\<guillemotleft>?B, t>>)")
  proof (induct t)
    case (Fun f ss)
    let ?ts = "map (\<lambda> s. s \<cdot> \<sigma>) ss"
    have wf_assB: "wf_ass R ?B" unfolding wf_ass_def using wf_ass wf_pi by auto
    have map: "(map (eval_term pi \<alpha>) (?ts))
      = (map (eval_term pi ?B) ss)" using Fun by (induct ss, auto)
    let ?i = "pi (f, length ss)"
    show ?case
    proof (cases "?i")
      case (Pair c cs)
      from wf_pi have "\<forall> d \<in> set (snd ?i). d \<in> carrier R" by auto
      with Pair have wf_i: "\<forall> d \<in> set cs. d \<in> carrier R" by auto
      from wf_i map have "map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip cs (map (\<lambda>t. t \<cdot> \<sigma>) ss)) =
        map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<lambda>x. (pi\<guillemotleft>\<alpha>, \<sigma> x>>),snd at>>)) (zip cs ss)"
      proof (induct cs arbitrary: ss)
        case (Cons c cs) note oCons = this
        then show ?case
        proof (cases ss, simp)
          case (Cons s sss)
          with oCons show ?thesis by auto
        qed
      qed simp
      with Pair show ?thesis by auto
    qed
  qed auto
  then show ?thesis by simp
qed
end


context linear_poly_order
begin

lemma wf_list_sum_lpoly:
  assumes "\<forall> p \<in> set ps. wf_lpoly R p"
  shows "wf_lpoly R (list_sum_lpoly R ps)"
  using wf_list_sum_lpoly[of ps] assms by auto

lemma pos_list_sum_lpoly:
  assumes "\<forall> p \<in> set ps. wf_lpoly R p"
    and  "\<forall> p \<in> set ps. pos_coeffs p"
  shows "pos_coeffs (list_sum_lpoly R ps)"
using assms
proof (induct ps)
  case Nil then show ?case by (simp add: pos_coeffs_def pos_pvars_def)
next
  case (Cons p ps)
  show ?case 
    by (simp only: list_prod.simps monoid.simps, rule pos_sum_lpoly, auto simp: Cons, rule wf_list_sum_lpoly, auto simp: Cons)
qed

lemma list_sum_lpoly_sound:
  assumes wf_ps: "\<forall> p \<in> set ps. wf_lpoly R p"
    and wf_ass: "wf_ass R \<alpha>"
  shows "eval_lpoly \<alpha> (list_sum_lpoly R ps) = list_sum R (map (eval_lpoly \<alpha>) ps)"
using wf_ps
proof (induct ps)
  case (Cons p ps)
  have "eval_lpoly \<alpha> (list_sum_lpoly R (p # ps)) = eval_lpoly \<alpha> (sum_lpoly R p (list_sum_lpoly R ps))" by auto
  also have "\<dots> = eval_lpoly \<alpha> p \<oplus> eval_lpoly \<alpha> (list_sum_lpoly R ps)"
    by (rule sum_poly_sound, rule wf_ass, simp add: Cons, rule wf_list_sum_lpoly, auto simp: Cons)
  also have "\<dots> = eval_lpoly \<alpha> p \<oplus> list_sum R (map (eval_lpoly \<alpha>) ps)" using Cons by auto
  finally show ?case by (auto simp: Cons wf_ass)
qed simp

abbreviation Pleft :: "('f, 'v) term \<Rightarrow> ('v, 'a) l_poly"
where "Pleft \<equiv> PleftI R pi"

abbreviation Pright :: "('f, 'v) term \<Rightarrow> ('v, 'a) l_poly"
where "Pright \<equiv> PrightI R pi"

lemma Pleft_both:
  assumes wf_ass: "wf_ass R \<alpha>"
    and pos_ass: "pos_ass \<alpha>"
  shows "((pi\<guillemotleft>\<alpha>,t>>) \<succeq> eval_lpoly \<alpha> (Pleft t)) \<and> wf_lpoly R (Pleft t)"
proof (induct t)
  case (Var x)
  from wf_ass[unfolded wf_ass_def] have wfx: "\<alpha> x \<in> carrier R" by auto
  then have "?case = (\<alpha> x \<succeq> \<alpha> x)" by (auto simp: wf_pvars_def)
  also have "\<dots>" using wfx by auto
  finally show ?case .
next
  case (Fun f ts)
  let ?I = "\<lambda> s. pi\<guillemotleft>\<alpha>,s>>"
  let ?E = "\<lambda> p. eval_lpoly \<alpha> p"
  show ?case
  proof (cases "pi (f,length ts)")
    case (Pair c cs)
    from wf_pi have "fst (pi (f,length ts)) \<in> carrier R \<and> (\<forall> c \<in> set (snd (pi (f,length ts))). c \<in> carrier R \<and> c \<succeq> \<zero>)" by auto
    with Pair have wf_c: "c \<in> carrier R" and wf_cs: "\<forall> c \<in> set cs. c \<in> carrier R" and pos_cs: "\<forall> c \<in> set cs. c \<succeq> \<zero>" by auto
    let ?plist = "map (\<lambda> at. mul_lpoly R (fst at) (Pleft (snd at))) (zip cs ts)"
    have wf_ps: "\<forall> p \<in> set ?plist. wf_lpoly R p"
    proof
      fix p
      assume "p \<in> set ?plist"
      from this obtain a t where p: "p = mul_lpoly R a (Pleft t)" and at: "(a,t) \<in> set (zip cs ts)" by auto
      from at have a: "a \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = a and y = t] set_zip_rightD[where x = a and y = t] by auto
      show "wf_lpoly R p" by (simp only: p, rule wf_mul_lpoly, auto simp: wf_cs a t Fun)
    qed
    have wf_sum: "wf_lpoly R (list_sum_lpoly R ?plist)"
      by (rule wf_list_sum_lpoly, rule wf_ps)
    have "(list_sum R (map (\<lambda> at. fst at \<otimes> (?I (snd at))) (zip cs ts))) \<succeq> list_sum R (map ?E ?plist)" (is "list_sum R ?vlist \<succeq> _")
    proof (simp only: o_def map_map, rule list_sum_mono)
      fix ct
      assume mem: "ct \<in> set (zip cs ts)"
      from this obtain c t where ct: "ct = (c,t)" by force
      from ct mem have c: "c \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = c and y = t] set_zip_rightD[where x = c and y = t] by auto
      have "((c \<otimes> (?I t)) \<succeq> ?E (mul_lpoly R c (Pleft t))) \<and> (c \<otimes> ?I t) \<in> carrier R \<and> (?E (mul_lpoly R c (Pleft t))) \<in> carrier R"
      proof (rule conjI)
        have id: "?E (mul_lpoly R c (Pleft t)) = c \<otimes> (?E (Pleft t))" by (rule mul_poly_sound, auto simp: c wf_cs Fun t wf_ass)
        show "c \<otimes> (?I t) \<succeq> ?E (mul_lpoly R c (Pleft t))"
          by (simp only: id, rule times_right_mono, auto simp: c wf_cs pos_cs t Fun wf_ass)
        show "(c \<otimes> (?I t)) \<in> carrier R \<and> (?E (mul_lpoly R c (Pleft t))) \<in> carrier R"
          by (rule conjI, rule m_closed, auto simp: c wf_cs wf_ass, rule wf_eval_lpoly, auto simp: wf_ass t Fun, rule wf_mul_lpoly, auto simp: c wf_cs t Fun)
      qed
      with ct show " (fst ct \<otimes> (pi\<guillemotleft>\<alpha>,snd ct>>) \<succeq> eval_lpoly \<alpha> (mul_lpoly R (fst ct) (Pleft (snd ct)))) \<and> (fst ct \<otimes> (pi\<guillemotleft>\<alpha>,snd ct>>)) \<in> carrier R \<and> (eval_lpoly \<alpha> (mul_lpoly R (fst ct) (Pleft (snd ct)))) \<in> carrier R" by simp
    qed
    also have  "\<dots> = ?E (list_sum_lpoly R ?plist)" by (rule list_sum_lpoly_sound[symmetric], rule wf_ps, rule wf_ass)
    finally have part1: "list_sum R ?vlist \<succeq> ?E (list_sum_lpoly R ?plist)" .
    have wf_csump: "wf_lpoly R (sum_lpoly R (c_lpoly c) (list_sum_lpoly R ?plist))" (is "wf_lpoly R ?csump")
      by (rule wf_sum_lpoly, auto simp: wf_c wf_pvars_def, rule wf_sum)
    from Pair Fun have id: "Pleft (Fun f ts) = (case ?csump of LPoly d [] \<Rightarrow> LPoly (Max \<zero> d) [] | p \<Rightarrow> p)" by auto
    from wf_csump have wf_final: "wf_lpoly R (Pleft (Fun f ts))" by (simp only: id, cases ?csump, cases "get_nc_lpoly ?csump", auto simp: wf_pvars_def)
    have "?E ?csump = ?E (c_lpoly c) \<oplus> ?E (list_sum_lpoly R ?plist)" by (rule sum_poly_sound, auto simp: wf_ass wf_c wf_pvars_def wf_sum)
    also have "\<dots> = c \<oplus> ?E (list_sum_lpoly R ?plist)" by (simp add: wf_c)
    finally have idr: "?E ?csump = c \<oplus> ?E (list_sum_lpoly R ?plist)" .
    have wf_suml: "list_sum R ?vlist \<in> carrier R"
    proof (rule wf_list_sum, rule)
      fix v
      assume "v \<in> set ?vlist"
      from this obtain c t where v: "v = c \<otimes> (?I t)" and ct: "(c,t) \<in> set (zip cs ts)" by auto
      from ct have c: "c \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = c and y = t] set_zip_rightD[where x = c and y = t] by auto
      show "v \<in> carrier R" by (simp only: v, insert wf_cs c wf_ass, auto)
    qed
    have ge_csum: "c \<oplus> list_sum R ?vlist \<succeq> ?E ?csump"
      by (simp only: idr, rule plus_right_mono, rule part1, rule wf_c, rule wf_suml,
      rule wf_eval_lpoly, rule wf_ass, rule wf_sum)
    have wf_csuml: "c \<oplus> list_sum R ?vlist \<in> carrier R" using wf_suml wf_c by auto
    from Pair have left: "?I (Fun f ts) = Max \<zero> ( c \<oplus> list_sum R ?vlist)" by auto
    have "\<dots> \<succeq> Max \<zero> ( ?E ?csump)"
      by (rule max_mono, rule ge_csum, rule wf_csuml, rule wf_eval_lpoly, rule wf_ass, rule wf_csump, auto)
    then have part2: "?I (Fun f ts) \<succeq> Max \<zero> ( ?E ?csump)" by (simp only: left)
    have part3: "Max \<zero> ( ?E ?csump) \<succeq> ?E (Pleft (Fun f ts))"
      using wf_csump by (simp only: id, cases ?csump, cases "get_nc_lpoly ?csump", auto simp: max_ge_right wf_ass)
    have ge_final: "?I (Fun f ts) \<succeq> ?E (Pleft (Fun f ts))"
      by (rule geq_trans, rule part2, rule part3, rule wf_terms, rule wf_ass, rule wf_max0,
        rule wf_eval_lpoly, rule wf_ass, rule wf_csump, rule wf_eval_lpoly, rule wf_ass, rule wf_final)
    from wf_final ge_final show ?thesis by auto
  qed
qed


lemma Pleft_sound:   assumes wf_ass: "wf_ass R \<alpha>"
  and pos_ass: "pos_ass \<alpha>"
  shows "(pi\<guillemotleft>\<alpha>,t>>) \<succeq> eval_lpoly \<alpha> (Pleft t)"
  using Pleft_both assms by auto

lemma wf_Pleft[simp]: "wf_lpoly R (Pleft t)"
  using Pleft_both[where \<alpha> = zero_ass] by auto

lemma pos_eval_pvars: assumes wf_ass: "wf_ass R \<alpha>"
  and pos_ass: "pos_ass \<alpha>"
  and wf_vas: "wf_pvars R vas"
  and pos_vas: "pos_pvars vas"
  shows "eval_pvars \<alpha> vas \<succeq> \<zero>"
using wf_vas pos_vas
proof (induct vas)
  case (Cons xa vas)
  show ?case
  proof (cases xa)
    case (Pair x a)
    from pos_ass wf_ass have pos_x: "\<alpha> x \<succeq> \<zero>" and wf_x: "\<alpha> x \<in> carrier R" unfolding pos_ass_def wf_ass_def by auto
    from Pair Cons have pos_a: "a \<succeq> \<zero>" and wf_a: "a \<in> carrier R" unfolding wf_pvars_def pos_pvars_def by auto
    have "a \<otimes> \<alpha> x \<succeq> \<zero> \<otimes> \<zero>" by (rule geq_trans[where y = "a \<otimes> \<zero>"], rule times_right_mono, auto simp: wf_a pos_a wf_x pos_x)
    then have pos_ax: "a \<otimes> \<alpha> x \<succeq> \<zero>" by auto
    have wf_ax: "a \<otimes> \<alpha> x \<in> carrier R" by (auto simp: wf_x wf_a)
    from Cons have pos_rec: "eval_pvars \<alpha> vas \<succeq> \<zero>" unfolding wf_pvars_def pos_pvars_def by auto
    from Cons have "wf_pvars R vas" unfolding wf_pvars_def by auto
    with Cons have wf_rec: "eval_pvars \<alpha> vas \<in> carrier R" using wf_ass by auto
    have "a \<otimes> \<alpha> x \<oplus> eval_pvars \<alpha> vas \<succeq> \<zero> \<oplus> \<zero>" by (rule plus_left_right_mono, auto simp: pos_ax wf_ax pos_rec wf_rec)
    then show ?thesis by (simp add: Pair)
  qed
qed simp


lemma Pright_both:  assumes wf_ass: "wf_ass R \<alpha>"
  and pos_ass: "pos_ass \<alpha>"
  shows "(eval_lpoly \<alpha> (Pright t) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)) \<and> wf_lpoly R (Pright t) \<and> pos_coeffs (Pright t)"
proof (induct t)
  case (Var x)
  from wf_ass[unfolded wf_ass_def] have wfx: "\<alpha> x \<in> carrier R" by auto
  then have "?case = (\<alpha> x \<succeq> \<alpha> x)" by (auto simp: wf_pvars_def pos_coeffs_def pos_pvars_def)
  also have "\<dots>" using wfx by auto
  finally show ?case .
next
  case (Fun f ts)
  let ?I = "\<lambda> s. pi\<guillemotleft>\<alpha>,s>>"
  let ?E = "\<lambda> p. eval_lpoly \<alpha> p"
  show ?case
  proof (cases "pi (f,length ts)")
    case (Pair c cs)
    from wf_pi have "fst (pi (f,length ts)) \<in> carrier R \<and> (\<forall> c \<in> set (snd (pi (f,length ts))). c \<in> carrier R \<and> c \<succeq> \<zero>)" by auto
    with Pair have wf_c: "c \<in> carrier R" and wf_cs: "\<forall> c \<in> set cs. c \<in> carrier R" and pos_cs: "\<forall> c \<in> set cs. c \<succeq> \<zero>" by auto
    let ?plist = "map (\<lambda> at. mul_lpoly R (fst at) (Pright (snd at))) (zip cs ts)"
    have wf_ps: "\<forall> p \<in> set ?plist. wf_lpoly R p"
    proof
      fix p
      assume "p \<in> set ?plist"
      from this obtain a t where p: "p = mul_lpoly R a (Pright t)" and at: "(a,t) \<in> set (zip cs ts)" by auto
      from at have a: "a \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = a and y = t] set_zip_rightD[where x = a and y = t] by auto
      show "wf_lpoly R p" by (simp only: p, rule wf_mul_lpoly, auto simp: wf_cs a t Fun)
    qed
    have wf_sum: "wf_lpoly R (list_sum_lpoly R ?plist)"
      by (rule wf_list_sum_lpoly, rule wf_ps)
    have pos_ps: "\<forall> p \<in> set ?plist. pos_coeffs p"
    proof
      fix p
      assume "p \<in> set ?plist"
      from this obtain a t where p: "p = mul_lpoly R a (Pright t)" and at: "(a,t) \<in> set (zip cs ts)" by auto
      from at have a: "a \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = a and y = t] set_zip_rightD[where x = a and y = t] by auto
      show "pos_coeffs p" by (simp only: p, rule pos_mul_lpoly, auto simp: a pos_cs wf_cs t Fun)
    qed
    have pos_sum: "pos_coeffs (list_sum_lpoly R ?plist)"
      by (rule pos_list_sum_lpoly, rule wf_ps, rule pos_ps)
    have id1: "?E (list_sum_lpoly R ?plist) = list_sum R (map ?E ?plist)" by (rule list_sum_lpoly_sound, rule wf_ps, rule wf_ass)
    have "\<dots> \<succeq> (list_sum R (map (\<lambda> at. fst at \<otimes> (?I (snd at))) (zip cs ts)))" (is "_ \<succeq> (list_sum R ?vlist)")
    proof (simp only: o_def map_map, rule list_sum_mono)
      fix ct
      assume mem: "ct \<in> set (zip cs ts)"
      from this obtain c t where ct: "ct = (c,t)" by force
      from ct mem have c: "c \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = c and y = t] set_zip_rightD[where x = c and y = t] by auto
      have "(?E (mul_lpoly R c (Pright t)) \<succeq> (c \<otimes> (?I t))) \<and> c \<otimes> ?I t \<in> carrier R \<and>  ?E (mul_lpoly R c (Pright t)) \<in> carrier R"
      proof (rule conjI)
        have id: "?E (mul_lpoly R c (Pright t)) = c \<otimes> (?E (Pright t))" by (rule mul_poly_sound, auto simp: c wf_cs Fun t wf_ass)
        show "?E (mul_lpoly R c (Pright t)) \<succeq> c \<otimes> (?I t)"
          by (simp only: id, rule times_right_mono[OF _ _ _ wf_eval_lpoly], auto simp: c wf_cs Fun[OF t]  pos_cs  wf_ass)
            next
        show "c \<otimes> (?I t) \<in> carrier R \<and> ?E (mul_lpoly R c (Pright t)) \<in> carrier R"
          by (rule conjI[OF m_closed wf_eval_lpoly[OF _ wf_mul_lpoly]], auto simp: c wf_cs wf_ass Fun[OF t])
      qed
      with ct show " (eval_lpoly \<alpha> (mul_lpoly R (fst ct) (Pright (snd ct))) \<succeq> fst ct \<otimes> (pi\<guillemotleft>\<alpha>,snd ct>>)) \<and> eval_lpoly \<alpha> (mul_lpoly R (fst ct) (Pright (snd ct))) \<in> carrier R \<and> fst ct \<otimes> (pi\<guillemotleft>\<alpha>,snd ct>>) \<in> carrier R" by simp
    qed
    then have part1: "?E (list_sum_lpoly R ?plist) \<succeq> list_sum R ?vlist" by (simp only: id1)
    have wf_csump: "wf_lpoly R (sum_lpoly R (c_lpoly c) (list_sum_lpoly R ?plist))" (is "wf_lpoly R ?csump")
      by (rule wf_sum_lpoly[OF _ wf_sum], auto simp: wf_c wf_pvars_def)
    have pos_csump: "pos_coeffs ?csump"
      by (rule pos_sum_lpoly, auto simp: wf_sum wf_c pos_sum, auto simp: wf_c wf_pvars_def pos_coeffs_def pos_pvars_def)
    from Pair Fun have id: "Pright (Fun f ts) = (case ?csump of LPoly d nc \<Rightarrow> LPoly (Max \<zero> d) nc)" by auto
    from wf_csump have wf_final: "wf_lpoly R (Pright (Fun f ts))" by (simp only: id, cases ?csump, auto simp: wf_pvars_def wf_max0)
    from pos_csump have pos_final: "pos_coeffs (Pright (Fun f ts))" unfolding pos_coeffs_def by (simp only: id, cases ?csump, auto)
    have "?E ?csump = ?E (c_lpoly c) \<oplus> ?E (list_sum_lpoly R ?plist)" by (rule sum_poly_sound, auto simp: wf_ass wf_c wf_pvars_def wf_sum)
    also have "\<dots> = c \<oplus> ?E (list_sum_lpoly R ?plist)" by (simp add: wf_c)
    finally have idr: "?E ?csump = c \<oplus> ?E (list_sum_lpoly R ?plist)" .
    have wf_sumr: "list_sum R ?vlist \<in> carrier R"
    proof (rule wf_list_sum, rule)
      fix v
      assume "v \<in> set ?vlist"
      from this obtain c t where v: "v = c \<otimes> (?I t)" and ct: "(c,t) \<in> set (zip cs ts)" by auto
      from ct have c: "c \<in> set cs" and t: "t \<in> set ts" using set_zip_leftD[where x = c and y = t] set_zip_rightD[where x = c and y = t] by auto
      show "v \<in> carrier R" by (simp only: v, rule m_closed, auto simp: wf_cs c wf_ass)
    qed
    have ge_csum: "?E ?csump \<succeq> c \<oplus> list_sum R ?vlist"
      by (simp only: idr, rule plus_right_mono, rule part1, rule wf_c,
      rule wf_eval_lpoly, rule wf_ass, rule wf_sum, rule wf_sumr)
    have wf_csuml: "c \<oplus> list_sum R ?vlist \<in> carrier R" using wf_sumr wf_c by auto
    from Pair have right: "?I (Fun f ts) = Max \<zero> ( c \<oplus> list_sum R ?vlist)" by auto
    have "Max \<zero> ( ?E ?csump) \<succeq> \<dots>"
      by (rule max_mono, rule ge_csum, rule wf_eval_lpoly, rule wf_ass, rule wf_csump, rule wf_csuml, auto)
    then have part2: "Max \<zero> ( ?E ?csump) \<succeq> ?I (Fun f ts)" by (simp only: right)
    have part3: "?E (Pright (Fun f ts)) \<succeq> Max \<zero> (?E ?csump)"
    proof (cases ?csump)
      case (LPoly d nc)
      have wf_nc: "wf_pvars R nc" using wf_csump LPoly by (simp only: id, auto)
      have wf_enc: "eval_pvars \<alpha> nc \<in> carrier R" using wf_csump LPoly by (simp only: id, auto simp: wf_ass)
      have wf_d: "d \<in> carrier R" using wf_csump LPoly by (simp only: id, auto)
      have pos_nc: "pos_pvars nc" using pos_csump LPoly unfolding pos_coeffs_def by (simp only: id, auto)
      have nc_pos: "eval_pvars \<alpha> nc \<succeq> \<zero>" by (rule pos_eval_pvars, auto simp: wf_ass pos_ass pos_nc wf_nc)
      have md_pos: "Max \<zero> d \<succeq> \<zero>" by (rule max_ge, insert wf_d, auto)
      have "Max \<zero> d \<oplus> eval_pvars \<alpha> nc \<succeq> \<zero> \<oplus> \<zero>" (is "?pr \<succeq> _") by (rule plus_left_right_mono, rule md_pos, rule nc_pos, auto simp: wf_enc wf_d wf_max0)
      then have "?pr \<succeq> \<zero>" by simp
      then have max_id: "Max \<zero> ?pr = ?pr" by (rule max0_id_pos, auto simp: wf_enc wf_d wf_max0)
      have "?pr \<succeq> Max \<zero> (d \<oplus> eval_pvars \<alpha> nc)"
      proof (rule geq_trans[where ?y = "Max \<zero> (?pr)"], simp only: max_id, rule geq_refl)
        show "Max \<zero> ?pr \<succeq> Max \<zero> (d \<oplus> eval_pvars \<alpha> nc)"
          by (rule max_mono[OF plus_left_mono[OF max_ge_right]], auto simp: wf_d wf_max0 wf_enc)
      qed (auto simp: wf_d wf_max0 wf_enc)
      then show ?thesis by (simp only: id, simp only: LPoly, simp)
    qed
    have ge_final: "?E (Pright (Fun f ts)) \<succeq> ?I (Fun f ts)"
      by (rule geq_trans, rule part3, rule part2, rule wf_eval_lpoly, rule wf_ass, rule wf_final, rule wf_max0,
      rule wf_eval_lpoly, rule wf_ass, rule wf_csump, rule wf_terms, rule wf_ass)
    from wf_final ge_final pos_final show ?thesis by auto
  qed
qed

lemma Pright_sound:
  assumes wf_ass: "wf_ass R \<alpha>"
    and pos_ass: "pos_ass \<alpha>"
  shows "eval_lpoly \<alpha> (Pright t) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)"
  using Pright_both assms by auto

lemma wf_Pright[simp]:
  "wf_lpoly R (Pright t)"
  using Pright_both[where \<alpha> = zero_ass] by auto

end

(* create an arity that is not used *)
definition create_arity :: "('f, 'a) lpoly_interL \<Rightarrow> nat" where
  "create_arity fcns = Suc (max_list (map (snd o fst) fcns))"

lemma replicate_prop:
  assumes "x \<in> P"
  shows "set (replicate n x) \<subseteq> P"
  using assms by (induct n) simp_all

lemma replicate_prop_elem:
  assumes "P x"
  shows "y \<in> set (replicate n x) \<Longrightarrow> P y"
  using assms by (induct n) auto

context lpoly_order
begin

lemma create_arity_sound:
  assumes m: "m \<ge> create_arity I"
  shows "to_lpoly_inter R I (f, m) = (default R, replicate m \<one>)" (is "?I (f, m) = _")
proof (cases "map_of I (f, m)")
  case None then show ?thesis by (auto simp: to_lpoly_inter_def)
next
  case (Some val)
  then have one: "((f,m),val) \<in> set I" by (rule map_of_SomeD)
  then have "m \<in> set (map (snd o fst) I)" unfolding o_def by force
  from max_list[OF this] m show ?thesis unfolding create_arity_def by auto
qed
end

context linear_poly_order
begin
lemma default_interpretation_subterm_inter_ns: 
  assumes pi: "pi (f, n) = (default R, replicate n \<one>)"
  and n: "n = length ts"
  and t: "(t :: ('f,'v)term) \<in> set ts"
  shows "(Fun f ts, t) \<in> inter_ns"
  unfolding inter_ns_def
proof (clarify)
  fix \<alpha> :: "('v,'a)p_ass"
  assume wf_ass: "wf_ass R \<alpha>" and pos_ass: "pos_ass \<alpha>" and "apos_ass \<alpha>"
  let ?C = "\<lambda> c. c \<in> carrier R"
  define c where "c = default R"
  note wf[simp] = wf_terms[OF wf_ass]
  note pos[simp] = pos_term[OF wf_ass pos_ass]
  have c0: "c \<succeq> \<zero>" "?C c" unfolding c_def by auto
  have id: "map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip (replicate (length ts) \<one>) ts) = 
    map (\<lambda> t. pi\<guillemotleft>\<alpha>,t>>) ts"
    by (rule nth_equalityI, auto simp: l_one[OF wf])
  let ?e = "Max \<zero> (c \<oplus> list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip (replicate (length ts) \<one>) ts))) \<succ>
    (pi\<guillemotleft>\<alpha>,t>>)"
  show "(pi\<guillemotleft>\<alpha>,Fun f ts>>) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)"
    unfolding eval_termI.simps pi[unfolded n] split Let_def c_def[symmetric] id
    using c0 t
  proof (induct ts arbitrary: c t)
    case (Cons t ts c s)
    note c = Cons(3)
    let ?sum' = "\<lambda> ts. list_sum R (map (eval_term pi \<alpha>) ts)"
    let ?sum = "?sum' ts"
    have Csum: "\<And> ts. ?C (?sum' ts)" by auto
    then have id: "c \<oplus> ((pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum) =
      c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum" using c wf[of t] by algebra
    from plus_left_right_mono[OF Cons(2) pos[of t] c] c
    have ge: "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<succeq> \<zero>" "?C (c \<oplus> (pi\<guillemotleft>\<alpha>,t>>))" by auto
    show ?case
    proof (cases "s = t")
      case False
      then have s: "s \<in> set ts" using Cons by auto
      from Cons(1)[OF ge s]
      show ?thesis by (simp add: id)
    next
      case True
      have "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum \<succeq> c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> \<zero>"
      proof (rule plus_right_mono, induct ts)
        case (Cons t ts)
        from plus_left_right_mono[OF pos[of t] Cons wf _ Csum]
        show ?case by simp
      qed (insert c, auto)
      with c have ge1: "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum \<succeq> c \<oplus> (pi\<guillemotleft>\<alpha>,t>>)" by simp
      from geq_trans[OF this ge(1)] Csum c have "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum \<succeq> \<zero>" by auto
      from max0_id_pos[OF this] Csum c have id2: "Max \<zero> (c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum) = c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum" by auto
      show ?thesis unfolding True
      proof (simp add: id id2)
        have "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<succeq> \<zero> \<oplus> (pi\<guillemotleft>\<alpha>,t>>)"
          by (rule plus_left_mono[OF geq_trans[OF Cons(2)]], insert c, auto)        
        then show "c \<oplus> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> ?sum \<succeq> (pi\<guillemotleft>\<alpha>,t>>)"
          by (intro geq_trans[OF ge1], insert c Csum, auto)
      qed
    qed
  qed simp
qed


lemma list_sum_append: assumes xs: "set xs \<subseteq> carrier R"
  and ys: "set ys \<subseteq> carrier R"
shows "list_sum R (xs @ ys) = list_sum R xs \<oplus> list_sum R ys" 
  using xs
proof (induct xs)
  case Nil
  thus ?case using wf_list_sum[OF ys] by auto
next
  case (Cons x xs)
  have "list_sum R ((x # xs) @ ys) = x \<oplus> list_sum R (xs @ ys)" using Cons(2) ys by simp
  also have "\<dots> = x \<oplus> (list_sum R xs \<oplus> list_sum R ys)" using Cons ys by auto
  also have "\<dots> = (x \<oplus> list_sum R xs) \<oplus> list_sum R ys" using wf_list_sum[OF ys] wf_list_sum[of xs] Cons(2) 
    by (intro a_assoc[symmetric], auto) 
  finally show ?case by auto  
qed 

lemma inter_ns_ce_compat:
  assumes pi: "pi = to_lpoly_inter R I" (is "_ = ?pi")
  shows "ce_compatible inter_ns"
proof (unfold ce_compatible_def, rule exI[of _ "create_arity I"], intro allI impI, rule subsetI, unfold ce_trs.simps)
  fix m c x
  let ?n = "create_arity I"
  assume m: "?n \<le> m"
  let ?m = "Suc (Suc m)"
  from m have "?m \<ge> ?n" by auto
  then have inter: "pi (c, ?m) = (default R, replicate ?m \<one>)" by (simp only: pi, rule create_arity_sound)
  assume "x \<in> {(Fun c (t # s # replicate m (Var undefined)), t)| t s. True} \<union>
              {(Fun c (t # s # replicate m (Var undefined)), s)| t s. True}" (is "_ \<in> ?tc \<union> ?sc")
  then obtain t s u where x: "x = (Fun c (t # s # replicate m (Var undefined)), u)" 
    and u: "u = t \<or> u = s" by auto
  show "x \<in> inter_ns" unfolding x
    by (rule default_interpretation_subterm_inter_ns[OF inter], insert u, auto)
qed

lemma inter_s_subset_inter_ns: "inter_s \<subseteq> inter_ns"
  unfolding inter_s_def inter_ns_def using gt_imp_ge wf_terms by auto

lemma create_af_sound:
  assumes not: "i \<notin> create_af R I fn"
  shows "length (snd (to_lpoly_inter R I fn)) \<le> i \<or> (snd (to_lpoly_inter R I fn)) ! i = \<zero>"
  (is "?len \<or> ?zero")
proof -
  obtain f n where fn: "fn = (f,n)" by force
  note not = not[unfolded create_af_def fn]
  show ?thesis
  proof (cases "map_of I (f,n)")
    case (Some cc)
    obtain c coeffs where cc: "cc = (c,coeffs)" by force
    note look = Some[unfolded cc]
    from not look Some have 
      i: "i \<notin> set ([ i . (c,i) <- zip coeffs [0 ..< length coeffs], c \<noteq> \<zero>])" (is "_ \<notin> ?set")  by auto
    have "length coeffs \<le> i \<or> coeffs ! i = \<zero>"
    proof (rule ccontr)
      assume "\<not> ?thesis"
      then have ii: "i < length coeffs" and c: "coeffs ! i \<noteq> \<zero>" by auto
      then have "i \<in> ?set" by (force simp: set_zip)
      with i show False by blast
    qed
    then show ?thesis unfolding fn by (simp add: look to_lpoly_inter_def)
  next
    case None
    with not have i: "i \<ge> n" by auto
    then show ?thesis unfolding fn
      by (auto simp: to_lpoly_inter_def None)
  qed
qed

lemma inter_ns_af_compat:
  assumes pi: "pi = to_lpoly_inter R I" (is "_ = ?pi")
  shows "af_compatible (create_af R I) inter_ns"
proof (unfold af_compatible_def, intro allI)
  fix f :: 'f and bef and s t :: "('f,'v)term" and aft
  obtain v :: 'v where True by simp
  let ?st = "Fun f (bef @ s # aft)"
  let ?tt = "Fun f (bef @ t # aft)"
  let ?pair = "(?st, ?tt)"
  let ?n = "Suc (length bef + length aft)"
  let ?i = "length bef"
  show "?i \<in> create_af R I (f, ?n) \<or> ?pair \<in> inter_ns"
  proof (cases "?i \<in> create_af R I (f, ?n)")
    case False
    then have "length (snd (?pi (f,?n))) \<le> ?i \<or> snd (?pi (f, ?n)) ! ?i = \<zero>" by (rule create_af_sound)
    with pi have pi3: "length (snd (pi (f,?n))) \<le> ?i \<or> snd (pi (f,?n)) ! ?i = \<zero>" by simp
    obtain c cs where pi2: "pi (f, ?n) = (c,cs)" by force
    with pi3 have short_0: "length cs \<le> ?i \<or> cs ! ?i = \<zero>" by auto
    have "\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<longrightarrow> ((pi\<guillemotleft>\<alpha>,?st>>) \<succeq> (pi\<guillemotleft>\<alpha>,?tt>>))" (is "\<forall> \<alpha>. ?wfpos \<alpha> \<longrightarrow> ?rel \<alpha>")
    proof
      fix \<alpha>
      show "?wfpos \<alpha> \<longrightarrow> ?rel \<alpha>"
      proof
        assume wfpos: "?wfpos \<alpha>"
        then have wf_ass: "wf_ass R \<alpha>" ..
        let ?in = "\<lambda> t :: ('f,'v) term. (pi\<guillemotleft>\<alpha>,t>>)"
        let ?inter = "\<lambda> s bef cs. list_sum R (map (\<lambda> at. fst at \<otimes> (?in (snd at))) (zip cs (bef @ s # aft)))"
        let ?intre = "\<lambda> aft cs. list_sum R (map (\<lambda> at. fst at \<otimes> (?in (snd at))) (zip cs aft))"
        have int_s: "?in ?st = Max \<zero> (c \<oplus> ?inter s bef cs)" by (auto simp: pi2)
        have int_t: "?in ?tt = Max \<zero> (c \<oplus> ?inter t bef cs)" by (auto simp: pi2)
        from short_0 have "?inter s bef cs = ?inter t bef cs"
        proof (induct cs arbitrary: bef)
          case (Cons c cs) note oCons = this
          show ?case
          proof (cases bef)
            case Nil
            with Cons show ?thesis by (simp add: wf_ass)
          next
            case (Cons b befs)
            with oCons have "length cs \<le> length befs \<or> cs ! length befs = \<zero>" by auto
            with Cons oCons show ?thesis by auto
          qed
        qed auto
        with int_s int_t have eq: "?in ?st = ?in ?tt" by auto
        show "?rel \<alpha>" by (simp only: eq, rule geq_refl, rule wf_terms, auto simp: wf_ass)
      qed
    qed
    then have "?pair \<in> inter_ns" unfolding inter_ns_def by auto
    then show ?thesis ..
  qed simp
qed
end

context lpoly_order
begin

abbreviation pi_of where "pi_of \<equiv> to_lpoly_inter R"

lemma check_poly_mono_npsm_sound:
  assumes ok: "isOK(check_poly_mono_npsm R F I)"
  shows "\<forall> fn \<in> set F \<union> set (map fst I). snd fn \<le> Suc 0 \<and> (snd fn = Suc 0 \<longrightarrow> fst (pi_of I fn) = \<zero> \<and> length (snd (pi_of I fn)) = Suc 0)" (is "\<forall> fn \<in> set F \<union> set (map fst I). ?P fn")
proof
  fix fn
  assume fn: "fn \<in> set F \<union> set (map fst I)"
  note ok = ok[unfolded check_poly_mono_npsm_def, simplified]
  from ok[THEN conjunct2] fn obtain ccs where mem: "(fn,ccs) \<in> set I" by auto
  obtain f n where fn: "fn = (f,n)" by force
  from ok[THEN conjunct1, rule_format, OF mem]
  have le_1: "snd fn \<le> Suc 0" unfolding fn by (cases ccs, auto)
  show "?P fn"
  proof (rule conjI[OF le_1], intro impI)
    assume eq_1: "snd fn = Suc 0"
    have "\<exists> ccs. map_of I fn = Some ccs"
    proof (cases "map_of I fn")
      case None
      from None[unfolded map_of_eq_None_iff[of I fn]] mem show ?thesis by force
    qed auto
    then obtain c cs where look: "map_of I fn = Some (c,cs)" by force
    from map_of_SomeD[OF look] have mem: "(fn, (c,cs)) \<in> set I" .
    have pi: "pi_of I fn = (c,cs)" unfolding to_lpoly_inter_def look ceta_map_of fun_of_map_fun.simps Let_def by simp
    note ok = ok[THEN conjunct1, rule_format, OF mem, unfolded fn split, simplified]
    from ok eq_1
    show "fst (pi_of I fn) = \<zero> \<and> length (snd (pi_of I fn)) = Suc 0"
      unfolding pi unfolding fn by simp
  qed
qed
end

context mono_linear_poly_order_carrier
begin

lemma plus_gt_right_mono: "\<lbrakk>y \<succ> z; x \<in> carrier R; y \<in> carrier R; z \<in> carrier R\<rbrakk> \<Longrightarrow> x \<oplus> y \<succ> x \<oplus> z"
  by (simp add: a_comm[where x = x], rule plus_gt_left_mono, auto simp: plus_single_mono)


lemma check_poly_mono_sound:
  assumes "isOK (check_poly_mono R I)"
  shows "\<forall> f n. (fst (pi_of I (f,n)) \<succeq> \<zero>) \<and> (length (snd (pi_of I (f, n))) \<ge> n \<and> (\<forall> c \<in> set (snd (pi_of I (f, n))). check_mono c \<or> c = \<one>))" (is "\<forall> f n. ?prop f n")
proof (intro allI)
  fix f n
  note to_lpoly_inter_def[simp]
  show "?prop f n"
  proof (cases "map_of I (f, n)")
    case None
    then have id: "pi_of I (f,n) = (default R, replicate n \<one>)" by auto
    show ?thesis
      by (simp only: id, rule conjI, simp, rule conjI, simp, simp)
  next
    case (Some ccs)
    from this obtain c cs where map_of: "map_of I (f, n) = Some (c,cs)" by force
    then have "((f,n),(c,cs)) \<in> set I" by (rule map_of_SomeD)
    with assms[unfolded check_poly_mono_def] map_of show "?prop f n" by auto
  qed
qed
end

context lpoly_order
begin
definition check_poly_strict_mono where
  "check_poly_strict_mono p i \<equiv> fst p \<succeq> \<zero> \<and> i < length (snd p) \<and> (let c = snd p ! i in check_mono c \<or> c = \<one>)"
end

locale pre_mono_linear_poly_order = linear_poly_order R pi + mono_linear_poly_order_carrier 
  for pi :: "('f :: {showl, compare_order}, 'a :: showl) lpoly_inter"
begin

lemma default_interpretation_subterm_inter_s: 
  assumes pi: "pi (f, n) = (default R, replicate n \<one>)"
    and n: "n = length ts"
    and t: "(t :: ('f,'v)term) \<in> set ts"
  shows "(Fun f ts, t) \<in> inter_s"
  unfolding inter_s_def
proof (clarify)
  fix \<alpha> :: "('v,'a)p_ass"
  assume wf_ass: "wf_ass R \<alpha>" and pos_ass: "pos_ass \<alpha>" and "apos_ass \<alpha>"
  let ?C = "\<lambda> c. c \<in> carrier R"
  define c where "c = default R"
  note wf[simp] = wf_terms[OF wf_ass]
  note pos[simp] = pos_term[OF wf_ass pos_ass]
  have c0: "c \<succeq> \<zero>" "?C c" unfolding c_def by auto
  have id: "map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip (replicate (length ts) \<one>) ts) = 
    map (\<lambda> t. pi\<guillemotleft>\<alpha>,t>>) ts"
    by (rule nth_equalityI, auto simp: l_one[OF wf])
  let ?e = "Max \<zero> (c \<oplus> list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip (replicate (length ts) \<one>) ts))) \<succ>
    (pi\<guillemotleft>\<alpha>,t>>)"
  from split_list[OF t] obtain bef aft where ts: "ts = bef @ [t] @ aft" by auto
  have "list_sum R (map (eval_term pi \<alpha>) ts) = list_sum R (map (eval_term pi \<alpha>) bef @ [pi\<guillemotleft>\<alpha>,t>>] @ map (eval_term pi \<alpha>) aft)"
    unfolding ts by auto
  also have "\<dots> = list_sum R (map (eval_term pi \<alpha>) bef) \<oplus> ((pi\<guillemotleft>\<alpha>,t>>) \<oplus> list_sum R (map (eval_term pi \<alpha>) aft))" 
    by (subst list_sum_append, force, force, subst list_sum_append, auto)
  finally have id2: "list_sum R (map (eval_term pi \<alpha>) ts) = 
    list_sum R (map (eval_term pi \<alpha>) bef) \<oplus> ((pi\<guillemotleft>\<alpha>,t>>) \<oplus> list_sum R (map (eval_term pi \<alpha>) aft))" (is "?list = _") .
  have "\<dots> \<succeq> \<zero> \<oplus> ((pi\<guillemotleft>\<alpha>,t>>) \<oplus> list_sum R (map (eval_term pi \<alpha>) aft))" (is "_ \<succeq> ?r")
    by (rule plus_left_mono[OF pos_list_sum], force+)
  also have "?r = (pi\<guillemotleft>\<alpha>,t>>) \<oplus> list_sum R (map (eval_term pi \<alpha>) aft)" 
    by (rule l_zero, force)
  finally have one: "?list \<succeq> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> list_sum R (map (eval_term pi \<alpha>) aft)" (is "_ \<succeq> ?r") unfolding id2 .
  have "?r \<succeq> (pi\<guillemotleft>\<alpha>,t>>) \<oplus> \<zero>" 
    by (rule plus_right_mono[OF pos_list_sum], force+)
  hence two: "?r \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" by auto
  from geq_trans[OF one two] have list: "?list \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" by force 
  have cg0: "c \<succ> \<zero>" unfolding c_def by (rule default_gt_zero)
  have "c \<oplus> ?list \<succ> \<zero> \<oplus> ?list" 
    by (rule plus_gt_left_mono[OF cg0 plus_single_mono], insert c0, auto)
  also have "\<zero> \<oplus> ?list = ?list" by (rule l_zero, force)
  finally have gt: "c \<oplus> ?list \<succ> ?list" .
  have gt: "c \<oplus> ?list \<succ> (pi\<guillemotleft>\<alpha>,t>>)" 
    by (rule compat2[OF gt list], insert c0, force+)
  have id3: "Max \<zero> (c \<oplus> ?list) = c \<oplus> ?list" 
    by (rule max0_id_pos, rule geq_trans[OF gt_imp_ge[OF gt]], insert c0, force+)
  show "(pi\<guillemotleft>\<alpha>,Fun f ts>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>)"
    unfolding eval_termI.simps pi[unfolded n] split Let_def c_def[symmetric] id id3 by (rule gt)
qed


lemma check_poly_strict_mono: assumes 
  mono: "check_poly_strict_mono (pi (f,Suc (length bef + length aft))) (length bef)"
  and st: "(s,t) \<in> (inter_s :: ('f,'v)trs)" (is "_ \<in> ?inter_s")
  shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_s"
proof -
  let ?st = "Fun f (bef @ s # aft)"
  let ?tt = "Fun f (bef @ t # aft)"
  let ?pair = "(?st, ?tt)"
  let ?n = "Suc (length bef + length aft)"
  let ?i = "length bef"
  obtain c cs where ccs: "pi (f,?n) = (c,cs)" by force
  from mono[unfolded this check_poly_strict_mono_def Let_def, simplified]
  have c: "c \<succeq> \<zero>" and mono: "?i < length cs \<and> (check_mono (cs ! ?i) \<or> cs ! ?i = \<one>)" by auto
  from wf_pi have "fst (pi (f,?n)) \<in> carrier R" and "\<forall> d \<in> set (snd (pi (f,?n))). d \<in> carrier R \<and> d \<succeq> \<zero>" by auto
  with ccs have wf_c: "c \<in> carrier R" and wf_cs: "\<forall> d \<in> set cs. d \<in> carrier R \<and> d \<succeq> \<zero>" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ?inter_s"
    unfolding inter_s_def
  proof (clarify)
    fix \<alpha> :: "('v,'a)p_ass"
    assume wf_ass: "wf_ass R \<alpha>" and pos_ass: "pos_ass \<alpha>" and apos_ass: "apos_ass \<alpha>"
    let ?in = "\<lambda> t :: ('f,'v) term. (pi\<guillemotleft>\<alpha>,t>>)"
    let ?inter = "\<lambda> s bef cs. list_sum R (map (\<lambda> at. fst at \<otimes> (?in (snd at))) (zip cs (bef @ s # aft)))"
    have int_s: "?in ?st = Max \<zero> (c \<oplus> ?inter s bef cs)" by (auto simp: ccs)
    have int_t: "?in ?tt = Max \<zero> (c \<oplus> ?inter t bef cs)" by (auto simp: ccs)
    from mono wf_cs have main: "?inter s bef cs \<succ> ?inter t bef cs"
    proof (induct cs arbitrary: bef)
      case (Cons c cs) note oCons = this
      then have wf_c: "c \<in> carrier R" and c_0: "c \<succeq> \<zero>" by auto
      {
        fix aft and a :: 'a and b :: "('f,'v)term"
        assume "(a,b) \<in> set (zip cs aft)"
        then have "a \<in> set cs" by (rule set_zip_leftD)
        with Cons have "a \<in> carrier R" by auto
        then have "a \<otimes> ?in b \<in> carrier R" using wf_ass by auto
      } note wf_zip = this
      then have wf_rec: "\<And> aft. list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip cs aft)) \<in> carrier R"
        by (intro wf_list_sum, auto)
      show ?case
      proof (cases bef)
        case Nil
        from st have st: "?in s \<succ> ?in t" unfolding inter_s_def using wf_ass pos_ass apos_ass by auto
        from Cons Nil have "check_mono c \<or> c = \<one>" by auto
        then have cst: "c \<otimes> ?in s \<succ> c \<otimes> ?in t"
        proof
          assume "c = \<one>"
          with st show ?thesis by (simp add: wf_ass)
        next
          assume "check_mono c"
          then show ?thesis
            by (rule check_mono[OF _ st], auto simp: wf_ass wf_c c_0)
        qed
        show ?thesis
          by (simp add: Nil Cons, rule plus_gt_left_mono2, rule cst, 
          auto simp: Cons wf_ass plus_single_mono wf_zip geq_refl[OF wf_rec])
      next
        case (Cons b befs)
        with oCons have "Suc (length befs) \<le> length cs" by auto
        with Cons oCons have rec: "?inter s befs cs \<succ> ?inter t befs cs" by auto
        show ?thesis by (simp add: Cons oCons, rule plus_gt_right_mono[OF rec, simplified, OF _ wf_rec wf_rec],  
          auto simp: wf_c wf_ass)
      qed
    qed auto
    have wf_inter: "\<And> t. ?inter t bef cs \<in> carrier R"
    proof (rule wf_list_sum, auto)
      fix t a b
      assume "(a,b) \<in> set (zip cs (bef @ t # aft))"
      then have "a \<in> set cs" by (rule set_zip_leftD)
      with wf_cs wf_ass show "(a \<otimes> (?in b)) \<in> carrier R" by auto
    qed
    have wf_cint: "\<And> t. c \<oplus> ?inter t bef cs \<in> carrier R"
      by (rule a_closed, rule wf_c, rule wf_inter)
    have pos_inter: "\<And> t. (?inter t bef cs) \<succeq> \<zero>"
    proof (rule pos_list_sum, simp, clarify, simp)
      fix t a b
      assume "(a,b) \<in> set (zip cs (bef @ t # aft))"
      then have "a \<in> set cs" by (rule set_zip_leftD)
      then have pos_a: "a \<succeq> \<zero>" and wf_a: "a \<in> carrier R" using wf_cs  by auto
      show "a \<otimes> (?in b) \<in> carrier R \<and> (a \<otimes> (?in b) \<succeq> \<zero>)"
      proof (rule conjI, auto simp: wf_ass wf_a)
        have int: "(a \<otimes> (?in b) \<succeq> a \<otimes> \<zero>)"
          by (rule times_right_mono, rule pos_a, rule pos_term, auto simp: wf_a wf_ass pos_ass)
        show "(a \<otimes> (?in b)) \<succeq> \<zero>" by (rule geq_trans[where y = "a \<otimes> \<zero>"], rule int, auto simp: wf_a wf_ass)
      qed
    qed
    have "\<And> t. c \<oplus> (?inter t bef cs) \<succeq> \<zero> \<oplus> \<zero>"
      by (rule plus_left_right_mono[OF _ pos_inter wf_c _ wf_inter], auto simp: c)
    then have pos_cint: "\<And> t. c \<oplus> (?inter t bef cs) \<succeq> \<zero>" by auto
    have id_cint: "\<And> t. Max \<zero> (c \<oplus> (?inter t bef cs)) = c \<oplus> (?inter t bef cs)"
      by (rule max0_id_pos, rule pos_cint, rule wf_cint)
    {
      fix t aft and a :: 'a and b :: "('f,'v)term"
      assume "(a,b) \<in> set (zip cs (bef @ t # aft))"
      then have "a \<in> set cs" by (rule set_zip_leftD)
      with wf_cs have "a \<in> carrier R" by auto
      then have "a \<otimes> ?in b \<in> carrier R" using wf_ass by auto
    }
    then have wf_rec: "\<And> t aft. list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip cs (bef @ t # aft))) \<in> carrier R"
      by (intro wf_list_sum, auto)
    show "?in ?st \<succ> ?in ?tt" by (simp only: int_s int_t id_cint, rule plus_gt_right_mono, rule main, rule wf_c, (rule wf_rec)+)
  qed
qed

lemma create_mono_af:
  assumes pi: "pi = to_lpoly_inter R I" (is "_ = ?pi")
  shows "af_monotone (create_mono_af R I) inter_s"
proof (rule af_monotoneI[OF check_poly_strict_mono])
  fix f and bef aft :: "('f,'v)term list"
  note d = check_poly_strict_mono_def Let_def to_lpoly_inter_def create_mono_af_def
  let ?n = "Suc (length bef + length aft)"
  let ?i = "length bef"
  obtain n where n: "?n = n" and i: "?i < n" by auto
  assume mono: "?i \<in> create_mono_af R I (f, ?n)"
  show "check_poly_strict_mono (pi (f, ?n)) ?i"
  proof (cases "map_of I (f,?n)")
    case None
    then have "pi (f, ?n) = ((default R, replicate n \<one>))" 
      unfolding pi d n by simp
    then show ?thesis unfolding d using i by simp
  next
    case (Some p)
    then have pi: "pi (f,?n) = p" unfolding pi d by auto
    obtain c cs where p: "p = (c,cs)" by force
    from mono[unfolded d] Some
    obtain c' where "c \<succeq> \<zero>" and "c' = \<one> \<or> check_mono c'" and 
      "(c',length bef) \<in> set (zip cs [0..<length cs])"
      by (auto split: if_splits simp: empty_af_def pi p)
    with i show ?thesis unfolding pi p d
      by (auto simp: set_zip)
  qed
qed
end


locale mono_linear_poly_order = pre_mono_linear_poly_order +
  assumes pi_mono: "\<forall> f n. (fst (pi (f, n)) \<succeq> \<zero>) \<and> (length (snd (pi (f, n))) \<ge> n \<and> (\<forall> c \<in> set (snd (pi (f, n))). check_mono c \<or> c = \<one>))"
begin

lemma inter_s_ce_compat: assumes pi: "pi = to_lpoly_inter R I" (is "_ = ?pi")
  shows "ce_compatible inter_s"
unfolding inter_s_def ce_compatible_def
proof (rule exI[of _ "create_arity I"], intro allI impI, rule subsetI, unfold ce_trs.simps)
  fix m c x
  let ?n = "create_arity I"
  assume m: "?n \<le> m"
  let ?m = "Suc (Suc m)"
  from m have "?m \<ge> ?n" by auto
  then have inter: "pi (c, ?m) = (default R, replicate ?m \<one>)" by (simp only: pi, rule create_arity_sound)
  let ?sum = "\<lambda> \<alpha>. list_sum R (replicate m (\<one> \<otimes> \<alpha> undefined))"
  {
    fix \<alpha>
    assume alpha: "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha>"
    let ?sum' = "list_sum R (replicate m (\<alpha> undefined))"
    have id: "?sum \<alpha> = ?sum'"
      by (subst l_one, insert alpha, auto simp: wf_ass_def)
    have wf_sum: "?sum \<alpha> \<in> carrier R" unfolding id
      by (rule wf_list_sum, rule replicate_prop, insert alpha, auto simp: wf_ass_def)
    have pos_sum: "?sum \<alpha> \<succeq> \<zero>" unfolding id
      by (rule pos_list_sum, insert alpha, auto simp: wf_ass_def pos_ass_def)
    from wf_sum pos_sum have "\<exists> d. ?sum \<alpha> = d \<and> d \<in> carrier R \<and> d \<succeq> \<zero>" by force
  } note sum = this
  fix x
  assume "x \<in> {(Fun c (t # s # replicate m (Var undefined)), t) | t s. True} \<union>
              {(Fun c (t # s # replicate m (Var undefined)), s) | t s. True}" (is "_ \<in> ?tc \<union> ?sc")
  then show "x \<in> {(s,t). \<forall>\<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>)}"
  proof
    assume "x \<in> ?tc"
    then obtain t s where id: "x = (Fun c (t # s # replicate m (Var undefined)), t)" (is "x = (?l, _)") by auto
    have "\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,?l>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>)"
    proof (intro allI)
      fix \<alpha>
      show "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,?l>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>)" (is "?wf_pos \<longrightarrow> ?goal")
      proof
        assume wf_pos_ass: ?wf_pos
        let ?term = "((default R \<oplus> (pi\<guillemotleft>\<alpha>,t>>)) \<oplus> (pi\<guillemotleft>\<alpha>,s>>)) \<oplus> ?sum \<alpha>"
        from sum[OF wf_pos_ass] obtain d where id: "?sum \<alpha> = d" and d: "d \<in> carrier R" "d \<succeq> \<zero>" by auto
        have max: "Max \<zero> ?term = ?term" unfolding id
          by (rule max0_id_pos, auto simp: wf_pos_ass d, (rule sum_pos)+, auto simp: wf_pos_ass d)
        have "Max \<zero> ?term \<succ> ((\<zero> \<oplus> (pi\<guillemotleft>\<alpha>,t>>)) \<oplus> \<zero>) \<oplus> \<zero>" unfolding max unfolding id
          by ((rule plus_gt_left_mono2)+, auto simp: wf_pos_ass d plus_single_mono default_gt_zero)
        then have "Max \<zero> ?term \<succ> (pi\<guillemotleft>\<alpha>,t>>)" by (auto simp: wf_pos_ass)
        with wf_pos_ass show ?goal using inter
          by (auto simp: d wf_max0 a_assoc id)
      qed
    qed
    then show ?thesis using id by simp
  next
    assume "x \<in> ?sc"
    then obtain t s where id: "x = (Fun c (t # s # replicate m (Var undefined)), s)" (is "x = (?l, _)") by auto
    have "\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,?l>>) \<succ> (pi\<guillemotleft>\<alpha>,s>>)"
    proof (intro allI)
      fix \<alpha>
      show "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,?l>>) \<succ> (pi\<guillemotleft>\<alpha>,s>>)" (is "?wf_pos \<longrightarrow> ?goal")
      proof
        assume wf_pos_ass: ?wf_pos
        let ?term = "((default R \<oplus> (pi\<guillemotleft>\<alpha>,t>>)) \<oplus> (pi\<guillemotleft>\<alpha>,s>>)) \<oplus> ?sum \<alpha>"
        from sum[OF wf_pos_ass] obtain d where id: "?sum \<alpha> = d" and d: "d \<in> carrier R" "d \<succeq> \<zero>" by auto
        have max: "Max \<zero> ?term = ?term" unfolding id
          by (rule max0_id_pos, auto simp: wf_pos_ass d, (rule sum_pos)+, auto simp: wf_pos_ass d)
        have "Max \<zero> ?term \<succ> ((\<zero> \<oplus> \<zero>) \<oplus> (pi\<guillemotleft>\<alpha>,s>>)) \<oplus> \<zero>" unfolding max unfolding id
          by ((rule plus_gt_left_mono2)+, auto simp: wf_pos_ass d plus_single_mono default_gt_zero)
        then have "Max \<zero> ?term \<succ> (pi\<guillemotleft>\<alpha>,s>>)" by (auto simp: wf_pos_ass)
        with wf_pos_ass show ?goal using inter
          by (auto simp: d wf_max0 a_assoc id)
      qed
    qed
    then show ?thesis using id by simp
  qed
qed

lemma inter_s_mono:
  shows "ctxt.closed inter_s"
proof (rule one_imp_ctxt_closed[OF check_poly_strict_mono])
  fix f bef s t aft
  show "check_poly_strict_mono (pi (f, Suc (length bef + length aft))) (length bef)"
    unfolding check_poly_strict_mono_def Let_def 
    using pi_mono[rule_format, of f "Suc (length bef + length aft)"]
    by auto
qed
end

context linear_poly_order
begin
lemmas compat_orig = compat
end

sublocale linear_poly_order \<subseteq> redtriple_order inter_s inter_ns inter_ns
proof
  show "SN inter_s"
  proof
    fix f
    assume steps: "(\<forall> i. (f i, f (Suc i)) \<in> inter_s)"
    let ?b = default_ass
    have "\<forall> i. ((pi\<guillemotleft>?b,f i>>) \<succ> (pi\<guillemotleft>?b, f (Suc i)>>)) \<and> (arc_pos (pi\<guillemotleft>?b, f (Suc i)>>))"
    proof
      fix i
      from steps have "(f i, f (Suc i)) \<in> inter_s" ..
      then have dec: "(pi\<guillemotleft>?b, f i>>) \<succ>  (pi\<guillemotleft>?b, f (Suc i)>>)" (is ?dec) unfolding inter_s_def
        by auto
      show "?dec \<and> arc_pos (pi\<guillemotleft>?b, f (Suc i)>>)" by (rule conjI, rule dec, rule apos_term, auto)
    qed
    from this obtain g
      where nSN: "\<forall> i. ((g i) :: 'a) \<succ> (g (Suc i)) \<and> g i \<in> carrier R \<and> g (Suc i) \<in> carrier R
      \<and>  g (Suc i) \<succeq> \<zero> \<and> arc_pos (g (Suc i))" by fastforce
    with SN show False by (auto simp: SN_defs)
  qed
next
  show "inter_ns O inter_s \<subseteq> inter_s"
  proof (clarify)
    fix s t u :: "('f,'v)term"
    assume st: "(s,t) \<in> inter_ns" and tu: "(t,u) \<in> inter_s"
    show "(s,u) \<in> inter_s" unfolding inter_s_def
    proof(rule, unfold split, clarify)
      fix \<alpha> :: "'v \<Rightarrow> 'a"
      assume wf: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
      show "(pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,u>>)"
        by (rule compat, insert st tu wf, unfold inter_s_def inter_ns_def, auto intro: wf_terms)
    qed
  qed
next
  show "inter_s O inter_ns \<subseteq> inter_s"
  proof (clarify)
    fix s t u :: "('f,'v)term"
    assume st: "(s,t) \<in> inter_s" and tu: "(t,u) \<in> inter_ns"
    show "(s,u) \<in> inter_s" unfolding inter_s_def
    proof(rule, unfold split, clarify)
      fix \<alpha> :: "'v \<Rightarrow> 'a"
      assume wf: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
      show "(pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,u>>)"
        by (rule compat2, insert st tu wf, unfold inter_s_def inter_ns_def, auto intro: wf_terms)
    qed
  qed
next
  show "ctxt.closed inter_ns" unfolding inter_ns_def
  proof (rule one_imp_ctxt_closed)
    fix f :: 'f
      and bef :: "('f,'v) term list"
      and s :: "('f,'v) term"
      and t :: "('f,'v) term"
      and aft :: "('f,'v) term list"
    let ?P = "{(s,t). \<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,s>>) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)}"
    assume "(s, t) \<in> ?P"
    then have st: "\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>, s>>) \<succeq> (pi\<guillemotleft>\<alpha>, t>>)" by (simp)
    let ?inter = "pi (f, (Suc (length bef + length aft)))"
    show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> ?P"
    proof (cases "?inter")
      case (Pair c list)
      have "\<forall> \<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>, Fun f (bef @ s # aft)>>) \<succeq> (pi\<guillemotleft>\<alpha>,Fun f (bef @ t # aft)>>)" (is "\<forall> \<alpha>. ?ass \<alpha> \<longrightarrow> ?ge \<alpha>")
      proof
        fix \<alpha>
        show "?ass \<alpha> \<longrightarrow> ?ge \<alpha>"
        proof
          assume "?ass \<alpha>"
          then have wf_ass: "wf_ass R \<alpha>" and pos_ass: "pos_ass \<alpha>" and apos_ass: "apos_ass \<alpha>" by auto
          with st have sta: "(pi\<guillemotleft>\<alpha>,s>>) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" by auto
          from wf_pi have "fst ?inter \<in> carrier R \<and> (\<forall> a. a \<in> set (snd ?inter) \<longrightarrow> a \<in> carrier R \<and> a \<succeq> \<zero>)"  by auto
          with Pair have wf_c: "c \<in> carrier R" and wf_list: "\<forall> a \<in> set list. a \<in> carrier R" and pos_list: "\<forall> a \<in> set list. a \<succeq> \<zero>" by auto
          let ?expr = "\<lambda> list rest.  list_sum R (map (\<lambda>at. fst at \<otimes> (pi\<guillemotleft>\<alpha>,snd at>>)) (zip list rest))"
          from wf_list pos_list have main: "(?expr list (bef @ s # aft) \<succeq> ?expr list (bef @ t # aft)) \<and> (?expr list (bef @ s # aft)) \<in> carrier R \<and> (?expr list (bef @ t # aft)) \<in> carrier R"
          proof (induct list arbitrary:bef)
            case (Cons a as) note oCons = this
            then have wf_a: "a \<in> carrier R" and pos_a: "a \<succeq> \<zero>" and wf_as: "\<forall> a \<in> set as. a \<in> carrier R" and pos_as: "\<forall> a \<in> set as. a \<succeq> \<zero>" by auto
            then show ?case
            proof (cases bef)
              case Nil
              {
                fix aas aaft
                assume "(aas,aaft) \<in> set (zip as aft)"
                then have "aas \<in> set as" using set_zip_leftD[where x = aas and y = aaft] by auto
                with wf_as have wfaas: "aas \<in> carrier R" by auto
                then have "(aas \<otimes> (pi\<guillemotleft>\<alpha>,aaft>>)) \<in> carrier R" by (auto simp: wf_ass wfaas)
              }
              then have wf_as_aft: "?expr as aft \<in> carrier R"
                by (intro wf_list_sum, auto)
              show ?thesis
                by (rule conjI, simp add: Nil, rule plus_left_mono, rule times_right_mono,
                  auto simp: wf_a pos_a wf_ass Nil wf_as_aft sta)
            next
              case (Cons u us)
              with oCons wf_as pos_as have wf_rec: "?expr as (us @ s # aft) \<in> carrier R \<and> ?expr as (us @ t # aft) \<in> carrier R" by auto
              show ?thesis
                by (simp add: Cons, rule conjI, rule plus_right_mono, auto simp: Cons oCons wf_ass wf_as pos_as)
            qed
          qed simp
          show "?ge \<alpha>" by (simp add: Pair, rule max_mono, rule plus_right_mono, auto simp: main wf_c)
        qed
      qed
      then show ?thesis by auto
    qed
  qed
next
  show "subst.closed inter_s"
  proof (unfold subst.closed_def inter_s_def, rule subsetI)
    fix st_sig :: "('f,'v)term \<times> ('f,'v)term"
    assume st_sig: "st_sig \<in> subst.closure {(s,t). \<forall>\<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>) }" (is "_ \<in> subst.closure ?P")
    then show "st_sig \<in> ?P"
    proof (cases st_sig)
      case (Pair s_sig t_sig)
      with st_sig have "(s_sig, t_sig) \<in> subst.closure ?P" by simp
      then have "(s_sig, t_sig) \<in> ?P"
      proof induct
        case (subst s t \<sigma>)
        { fix \<alpha>
          have "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>, s \<cdot> \<sigma>>>) \<succ> (pi\<guillemotleft>\<alpha>, t \<cdot> \<sigma>>>)" (is "?wf \<and> ?ps \<longrightarrow> ?go")
          proof -
            {
              assume ?wf and ?ps
              have wf_assB: "wf_ass R (\<lambda>x. pi\<guillemotleft>\<alpha>,\<sigma> x>>)" (is "wf_ass R ?bet") unfolding wf_ass_def using \<open>?wf\<close>  by auto
              have pos_assB: "pos_ass ?bet" unfolding pos_ass_def using \<open>?ps\<close> \<open>?wf\<close>  by auto
              have apos_assB: "apos_ass ?bet" unfolding apos_ass_def using \<open>?ps\<close> \<open>?wf\<close> by auto
              with Pair subst Cons wf_assB pos_assB have "(pi\<guillemotleft>?bet,s>>) \<succ> (pi\<guillemotleft>?bet,t>>)" by force
              with \<open>?wf\<close> have "?go" by (simp add: interpr_subst)
            }
            then show ?thesis by blast
          qed }
        then show ?case by simp
      qed
      with Pair show ?thesis by simp
    qed
  qed
next
  show "subst.closed inter_ns"
  proof (unfold subst.closed_def inter_ns_def, rule subsetI)
    fix st_sig :: "('f,'v)term \<times> ('f,'v)term"
    assume st_sig: "st_sig \<in> subst.closure {(s,t). \<forall>\<alpha>. wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>,s>>) \<succeq> (pi\<guillemotleft>\<alpha>,t>>) }" (is "_ \<in> subst.closure ?P")
    then show "st_sig \<in> ?P"
    proof (cases st_sig)
      case (Pair s_sig t_sig)
      with st_sig have "(s_sig, t_sig) \<in> subst.closure ?P" by simp
      then have "(s_sig, t_sig) \<in> ?P"
      proof induct
        case (subst s t \<sigma>)
        { fix \<alpha>
          have "wf_ass R \<alpha> \<and> pos_ass \<alpha> \<and> apos_ass \<alpha> \<longrightarrow> (pi\<guillemotleft>\<alpha>, s \<cdot> \<sigma>>>) \<succeq> (pi\<guillemotleft>\<alpha>, t \<cdot> \<sigma>>>)" (is "?wf \<and> ?ps \<longrightarrow> ?go")
          proof -
            {
              assume ?wf and ?ps
              have wf_assB: "wf_ass R (\<lambda>x. pi\<guillemotleft>\<alpha>, \<sigma> x>>)" (is "wf_ass R ?bet") unfolding wf_ass_def using \<open>?wf\<close>  by auto
              have pos_assB: "pos_ass ?bet" unfolding pos_ass_def using \<open>?ps\<close> \<open>?wf\<close>  by auto
              have apos_assB: "apos_ass ?bet" unfolding apos_ass_def using \<open>?ps\<close> \<open>?wf\<close> by auto
              with Cons subst Pair wf_assB pos_assB have "(pi\<guillemotleft>?bet,s>>) \<succeq> (pi\<guillemotleft>?bet,t>>)" by force
              with \<open>?wf\<close> have "?go" by (simp add: interpr_subst)
            }
            then show ?thesis by blast
          qed }
        then show ?case by simp
      qed
      with Pair show ?thesis by simp
    qed
  qed
next
  show "trans inter_ns" unfolding trans_def
  proof (clarify)
    fix s t u :: "('f,'v)term"
    assume st: "(s,t) \<in> inter_ns" and tu: "(t,u) \<in> inter_ns"
    show "(s,u) \<in> inter_ns" unfolding inter_ns_def
    proof(rule, unfold split, clarify)
      fix \<alpha> :: "'v \<Rightarrow> 'a"
      assume wf: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
      show "(pi\<guillemotleft>\<alpha>,s>>) \<succeq> (pi\<guillemotleft>\<alpha>,u>>)"
        by (rule geq_trans, insert st tu wf, unfold inter_ns_def, auto intro: wf_terms)
    qed
  qed
next
  show "trans inter_s" unfolding trans_def
  proof (clarify)
    fix s t u :: "('f,'v)term"
    assume st: "(s,t) \<in> inter_s" and tu: "(t,u) \<in> inter_s"
    show "(s,u) \<in> inter_s" unfolding inter_s_def
    proof(rule, unfold split, clarify)
      fix \<alpha> :: "'v \<Rightarrow> 'a"
      assume wf: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
      show "(pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,u>>)"
        by (rule gt_trans, insert st tu wf, unfold inter_s_def, auto intro: wf_terms)
    qed
  qed
next
  show "refl inter_ns"
    unfolding inter_ns_def refl_on_def using geq_refl by (auto intro: wf_terms)
  show "inter_s \<subseteq> inter_ns" by (rule inter_s_subset_inter_ns)
qed

context linear_poly_order
begin

lemma eval_term_subst_eq: "\<lbrakk>\<And> x. x \<in> vars_term t \<Longrightarrow> \<alpha> x = \<beta> x\<rbrakk> \<Longrightarrow> (pi\<guillemotleft>\<alpha>,t>>) = (pi\<guillemotleft>\<beta>,t>>)"
proof (induction t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ts)
  {
    fix t x
    assume t: "t \<in> set ts" and x: "x \<in> vars_term t"
    with Fun.prems[of x] have "\<alpha> x = \<beta> x" by auto
  } note id = this
  {
    fix t
    assume t: "t \<in> set ts"
    from Fun.IH[OF t id[OF t]]
    have "(pi\<guillemotleft>\<alpha>,t>>) = (pi\<guillemotleft>\<beta>,t>>)" .
  } note IH = this
  obtain d ds where pi: "pi (f,length ts) = (d,ds)" by force
  show ?case unfolding eval_termI.simps Let_def pi split
  proof (rule arg_cong[where f = "\<lambda> a. Max \<zero> (d \<oplus> list_sum R a)"],
    rule map_cong[OF refl])
    fix x
    assume "x \<in> set (zip ds ts)"
    from zip_snd[OF this] have "snd x \<in> set ts" .
    from IH[OF this]
    show "fst x \<otimes> (pi\<guillemotleft>\<alpha>,snd x>>) = fst x \<otimes> (pi\<guillemotleft>\<beta>,snd x>>)" by simp
  qed
qed
end

locale npsm_mono_linear_poly_order = linear_poly_order +
  fixes F :: "'b sig"
  assumes F_unary: "\<And> fn. fn \<in> F \<Longrightarrow> snd fn \<le> Suc 0"
      and pi_mono: "\<And> fn. fn \<in> F \<Longrightarrow> snd fn = Suc 0 \<Longrightarrow> fst (pi fn) = \<zero> \<and> length (snd (pi fn)) = Suc 0"
      and mode: "\<not> psm"
begin

lemma inter_s_F_mono:
  fixes s :: "('b,'v)term"
  assumes st: "(s,t) \<in> inter_s"
  and F: "(f,Suc (length bef + length aft)) \<in> F"
  shows "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_s"
proof -
  let ?f = "(f,Suc 0)"
  from F_unary[OF F] have empty: "bef = []" "aft = []" by auto
  from F empty have "?f \<in> F" by auto
  from pi_mono[OF this] have pi: "fst (pi ?f) = \<zero>" "length (snd (pi ?f)) = Suc 0" by auto
  let ?st' = "Fun f (bef @ s # aft)"
  let ?tt' = "Fun f (bef @ t # aft)"
  let ?pair' = "(?st', ?tt')"
  let ?s = "Fun f [s]"
  let ?t = "Fun f [t]"
  let ?pair = "(?s, ?t)"
  have pair: "?pair' = ?pair" unfolding empty by simp
  obtain c cs where ccs: "pi ?f = (c,cs)" by force
  with pi obtain c where pi: "pi ?f = (\<zero>,[c])" by (cases "snd (pi ?f)", auto)
  from wf_pi[THEN conjunct1] have "\<forall> d \<in> set (snd (pi ?f)). d \<in> carrier R \<and> d \<succeq> \<zero>" by auto
  with pi have wf_c: "c \<in> carrier R" and c_0: "c \<succeq> \<zero>" by auto
  from wf_pi[THEN conjunct2] have "arc_pos (fst (pi ?f)) \<or> (\<exists> a \<in> set (take (snd ?f) (snd (pi ?f))). arc_pos a)" by auto
  show "(Fun f (bef @ s # aft), Fun f (bef @ t # aft)) \<in> inter_s"
    unfolding inter_s_def pair
  proof (clarify)
    fix \<alpha> :: "('v,'a)p_ass"
    assume wf_ass: "wf_ass R \<alpha>" and pos_ass: "pos_ass \<alpha>" and apos_ass: "apos_ass \<alpha>"
    let ?in = "\<lambda> t :: ('b,'v) term. (pi\<guillemotleft>\<alpha>,t>>)"
    let ?inter = "\<lambda> s. c \<otimes> ?in s"
    from st[unfolded inter_s_def] wf_ass pos_ass apos_ass have gt: "?in s \<succ> ?in t"
      by simp
    from times_gt_right_mono[OF gt mode _ _ wf_c]
    have gt: "?inter s \<succ> ?inter t" using wf_ass by simp
    from wf_c wf_ass have wf_s: "?inter s \<in> carrier R" by simp
    from wf_c wf_ass have wf_t: "?inter t \<in> carrier R" by simp
    note max0 = max0_npsm_id[OF mode]
    have int_s: "?in ?s = ?inter s" using max0 wf_s by (simp add: pi)
    have int_t: "?in ?t = ?inter t" using max0 wf_t by (simp add: pi)
    show "?in ?s \<succ> ?in ?t" unfolding int_s int_t by (rule gt)
  qed
qed

lemma rel_subterm_terminating:
  fixes Rs Rw :: "('b, 'v) trs"
  assumes F: "funas_trs Rs \<subseteq> F" "funas_trs Rw \<subseteq> F"
  and orient: "Rs \<subseteq> inter_s" "Rw \<subseteq> inter_ns"
  and ST: "ST \<subseteq> {(Fun f ts, t) | f ts t. t \<in> set ts \<and> (f,length ts) \<notin> F}" 
  shows "SN_rel (rstep (Rs \<union> ST)) (rstep (Rw \<union> ST))"
proof (rule sig_mono_imp_SN_rel_subterm[OF inter_s_F_mono F_unary orient _ F ST])
  fix l r
  assume "(l,r) \<in> inter_ns \<inter> Rw"
  with F have ns: "(l,r) \<in> inter_ns" and Fl: "funas_term l \<subseteq> F"
    and Fr: "funas_term r \<subseteq> F" unfolding funas_trs_def funas_rule_def [abs_def] by force+
  show "vars_term r \<subseteq> vars_term l"
  proof (rule ccontr)
    assume "\<not> ?thesis"
    then obtain x where xr: "x \<in> vars_term r" and xl: "x \<notin> vars_term l" by auto
    from Fr xr have "\<exists> c. c \<in> carrier R \<and> arc_pos c \<and> (\<forall> \<alpha>. wf_ass R \<alpha> \<longrightarrow> pi\<guillemotleft>\<alpha>,r>> = c \<otimes> \<alpha> x)"
    proof (induction r)
      case (Var y)
      from Var.prems have xy: "x = y" by simp
      show ?case using wf_terms[of _ "Var y"]
        by (intro exI[of _ \<one>], unfold xy, auto simp: arc_pos_one)
    next
      case (Fun f ss)
      from Fun.prems(1) have "(f,length ss) \<in> F" by simp
      with F_unary[OF this] Fun.prems(2) obtain s where ss: "ss = [s]"
        and F: "(f,Suc 0) \<in> F"
        by (cases ss, auto)
      with Fun.prems have "funas_term s \<subseteq> F" "x \<in> vars_term s" by auto
      from Fun.IH[OF _ this, unfolded ss] obtain c where c: "c \<in> carrier R"
        and ac: "arc_pos c"
        and eval: "\<And> \<alpha>. wf_ass R \<alpha> \<Longrightarrow> (pi\<guillemotleft>\<alpha>,s>>) = c \<otimes> \<alpha> x" by auto
      obtain d ds where "pi (f,Suc 0) = (d,ds)" by force
      with pi_mono[OF F] obtain d where pi: "pi (f, length [s]) = (\<zero>,[d])" by (cases ds, auto)
      from wf_pi[THEN conjunct1, rule_format, of "(f,Suc 0)"] pi
      have d: "d \<in> carrier R" by auto
      from wf_pi[THEN conjunct2, rule_format, of "(f,Suc 0)"] pi
        arc_pos_zero[OF mode] have ad: "arc_pos d" by auto
      show ?case unfolding ss
      proof (rule exI[of _ "d \<otimes> c"], intro conjI allI impI)
        show "d \<otimes> c \<in> carrier R" using d c by simp
        show "arc_pos (d \<otimes> c)" using ad ac d c by simp
      next
        fix \<alpha> :: "('v,'a)p_ass"
        assume wf: "wf_ass R \<alpha>"
        then have x: "\<alpha> x \<in> carrier R" unfolding wf_ass_def by auto
        have "(pi\<guillemotleft>\<alpha>,Fun f [s]>>) = Max \<zero> (\<zero> \<oplus> (d \<otimes> (c \<otimes> \<alpha> x) \<oplus> \<zero>))"
          unfolding eval_termI.simps Let_def pi split
          using eval[OF wf] by simp
        also have "... = d \<otimes> (c \<otimes> \<alpha> x)"
          using max0_npsm_id[OF mode]  d c x by simp
        also have "\<dots> = (d \<otimes> c) \<otimes> \<alpha> x" using d c x by algebra
        finally show "(pi\<guillemotleft>\<alpha>,Fun f [s]>>) = (d \<otimes> c) \<otimes> \<alpha> x" .
      qed
    qed
    then obtain c where c: "c \<in> carrier R" and ac: "arc_pos c" and
      evalr: "\<And> \<alpha>. wf_ass R \<alpha> \<Longrightarrow> (pi\<guillemotleft>\<alpha>,r>>) = c \<otimes> \<alpha> x"
      by auto
    let ?d = "default_ass :: ('v,'a)p_ass"
    from wf_pos_apos_default_ass
    have wd: "wf_ass R ?d" and pd: "pos_ass ?d" and ad: "apos_ass ?d" by auto
    from not_all_ge[OF mode wf_terms[OF wd] c ac, of l] obtain e where
      we: "e \<in> carrier R" and pe: "e \<succeq> \<zero>" and ae: "arc_pos e"
      and nge: "\<not> (pi\<guillemotleft>?d,l>>) \<succeq> c \<otimes> e" by blast
    let ?e = "\<lambda> y. if y = x then e else ?d y"
    from wd we have wae: "wf_ass R ?e" unfolding wf_ass_def by auto
    from pd pe have pae: "pos_ass ?e" unfolding pos_ass_def by auto
    from ad ae have aae: "apos_ass ?e" unfolding apos_ass_def by auto
    have id: "(pi\<guillemotleft>?d,l>>) = (pi\<guillemotleft>?e,l>>)"
      by (rule eval_term_subst_eq, insert xl, auto)
    have "... \<succeq> (pi\<guillemotleft>?e,r>>)" using  ns[unfolded inter_ns_def] wae pae aae by auto
    also have "... = c \<otimes> e" unfolding evalr[OF wae] by simp
    finally have "(pi\<guillemotleft>?d,l>>) \<succeq> c \<otimes> e" unfolding id .
    with nge show False by blast
  qed
qed
end

(* show that several functions are invariant under updates *)
lemma pow_update[simp]: "x [^]\<^bsub>(C \<lparr>gt := a, bound := b\<rparr>)\<^esub> (n :: nat) = x [^]\<^bsub>C\<^esub> n"
  unfolding nat_pow_def by auto

lemma to_lpoly_inter_update[simp]: 
  "to_lpoly_inter (C \<lparr>gt := a, bound := b\<rparr>) I = to_lpoly_inter C I"
  unfolding to_lpoly_inter_def by auto

lemma create_af_update[simp]: "create_af (C \<lparr>gt := a, bound := b\<rparr>) I = create_af C I"
  unfolding create_af_def by auto

lemma create_mono_af_update[simp]: "create_mono_af (C \<lparr>gt := a, bound := b\<rparr>) I = create_mono_af C I"
  unfolding create_mono_af_def by auto

(* and now systematically extend (raw) definitions *)
lemma add_var_update[simp]: "add_var (R\<lparr> gt := gt, bound := bnd \<rparr>) = add_var R"
proof (intro ext, goal_cases)
  case (1 x a xs)
  show ?case
    by (induct x a xs rule: add_var.induct, auto)
qed

lemma wf_pvars_update[simp]: "wf_pvars (R\<lparr> gt := gt, bound := bnd \<rparr>) = wf_pvars R"
  by (rule ext, simp add: wf_pvars_def)

lemma wf_lpoly_update[simp]: "wf_lpoly (R\<lparr> gt := gt, bound := bnd \<rparr>) = wf_lpoly R"
proof (intro ext, goal_cases)
  case (1 x)
  show ?case by (cases x, auto)
qed

lemma list_prod_update[simp]: "list_prod (R\<lparr> gt := gt, bound := bnd \<rparr>) = list_prod R"
proof (intro ext, goal_cases)
  case (1 xs)
  show ?case by (induct xs rule: list_prod.induct, auto)
qed

lemma sum_pvars_update[simp]: "sum_pvars (R\<lparr> gt := gt, bound := bnd \<rparr>) = sum_pvars R"
proof (intro ext, goal_cases)
  case (1 x xs)
  show ?case by (induct x xs rule: sum_pvars.induct, auto)
qed

lemma sum_lpoly_update[simp]: "sum_lpoly (R\<lparr> gt := gt, bound := bnd \<rparr>) = sum_lpoly R"
proof (intro ext, goal_cases)
  case (1 x xs)
  show ?case by (induct x xs rule: sum_lpoly.induct, auto)
qed

lemma mul_pvars_update[simp]: "mul_pvars (R\<lparr> gt := gt, bound := bnd \<rparr>) = mul_pvars R"
proof (intro ext, goal_cases)
  case (1 x xs)
  show ?case by (induct x xs rule: mul_pvars.induct, auto simp: Let_def)
qed

lemma mul_lpoly_update[simp]: "mul_lpoly (R\<lparr> gt := gt, bound := bnd \<rparr>) = mul_lpoly R"
proof (intro ext, goal_cases)
  case (1 x xs)
  show ?case by (induct x xs rule: mul_lpoly.induct, auto)
qed

lemma update_manual: 
  "Max\<^bsub>R\<lparr>gt := gt, bound := bnd\<rparr>\<^esub> = Max\<^bsub>R\<^esub>"
  "\<zero>\<^bsub>R\<lparr>gt := gt, bound := bnd\<rparr>\<^esub> = \<zero>\<^bsub>R\<^esub>" by auto

lemma Pleft_update[simp]: "PleftI (R\<lparr> gt := gt, bound := bnd \<rparr>) = PleftI R" 
  unfolding PleftI_def PleftI_sumC_def PleftI_graph_def by (simp, unfold update_manual, simp)

lemma Pright_update[simp]: "PrightI (R\<lparr> gt := gt, bound := bnd \<rparr>) = PrightI R" 
  unfolding PrightI_def PrightI_sumC_def PrightI_graph_def by (simp, unfold update_manual, simp)

context linear_poly_order
begin

lemma wf_elem_coeff_left:
  assumes "a \<in> set (coeffs_of_lpoly R (Pleft t))"
  shows "a \<in> carrier R"
proof -
  have "wf_ass R default_ass" and "pos_ass default_ass" by auto
  from Pleft_both[OF this] have "wf_lpoly R (Pleft t)" ..
  from wf_lpoly_coeff[OF this] show ?thesis using assms by auto
qed

lemma wf_elem_coeff_right: assumes "a \<in> set (coeffs_of_lpoly R (Pright t))" shows "a \<in> carrier R"
proof -
  have "wf_ass R default_ass" and "pos_ass default_ass" by auto
  from Pright_both[OF this] have "wf_lpoly R (Pright t)" by auto
  from wf_lpoly_coeff[OF this] show ?thesis using assms by auto
qed

lemma check_polo_ns: fixes st :: "('f,'v :: showl)rule"
  assumes ok: "isOK(check_polo_ns (R \<lparr> gt := gt, bound := bnd \<rparr>) pi st)"
  shows "st \<in> inter_ns"
proof -
  let ?R = "R \<lparr> gt := gt, bound := bnd \<rparr>"
  obtain s t where st: "st = (s,t)" by force
  from ok st have "isOK(check_lpoly_ns ?R (Pleft s) (Pright t))" by simp
  from check_lpoly_ns_sound[OF this wf_Pleft wf_Pright] have poly: "(Pleft s, Pright t) \<in> poly_ns" .
  show ?thesis unfolding st inter_ns_def
  proof (simp, intro allI impI, elim conjE)
    fix \<alpha> :: "'v \<Rightarrow> 'a"
    assume [simp]: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
    have ge1: "(pi\<guillemotleft>\<alpha>,s>>) \<succeq> eval_lpoly \<alpha> (Pleft s)" by (rule Pleft_sound, auto)
    have mid: "\<dots> \<succeq> eval_lpoly \<alpha> (Pright t)" using poly unfolding poly_ns_def by auto
    have ge2: "\<dots> \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" by (rule Pright_sound, auto)
    show "(pi\<guillemotleft>\<alpha>,s>>) \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" 
      by (rule geq_trans[OF ge1 geq_trans[OF mid ge2]], auto)
  qed
qed

lemma check_polo_s:
  fixes st :: "('f,'v :: showl)rule"
  assumes ok: "isOK(check_polo_s (R \<lparr> gt := gt, bound := bnd \<rparr>) pi st)"
  and gt: "\<And> a b. (a,b) \<in> set (coeffs_of_constraint (R \<lparr> gt := gt, bound := bnd \<rparr>) pi st) 
  \<Longrightarrow> a \<in> carrier R \<Longrightarrow> b \<in> carrier R \<Longrightarrow> gt a b \<Longrightarrow> a \<succ> b"
  shows "st \<in> inter_s"
proof -
  let ?R = "R \<lparr> gt := gt, bound := bnd \<rparr>"
  obtain s t where st: "st = (s,t)" by force
  from ok st have ok: "isOK(check_lpoly_s ?R (Pleft s) (Pright t))" by simp
  have poly: "(Pleft s, Pright t) \<in> poly_s" 
    by (rule check_lpoly_s_sound[OF ok wf_Pleft wf_Pright gt],
      auto simp: coeffs_of_constraint_def st)
  show ?thesis unfolding st inter_s_def
  proof (simp, intro allI impI, elim conjE)
    fix \<alpha> :: "'v \<Rightarrow> 'a"
    assume [simp]: "wf_ass R \<alpha>" "pos_ass \<alpha>" "apos_ass \<alpha>"
    have ge1: "(pi\<guillemotleft>\<alpha>,s>>) \<succeq> eval_lpoly \<alpha> (Pleft s)" by (rule Pleft_sound, auto)
    have mid: "\<dots> \<succ> eval_lpoly \<alpha> (Pright t)" using poly unfolding poly_s_def by auto
    have ge2: "\<dots> \<succeq> (pi\<guillemotleft>\<alpha>,t>>)" by (rule Pright_sound, auto)
    show "(pi\<guillemotleft>\<alpha>,s>>) \<succ> (pi\<guillemotleft>\<alpha>,t>>)" 
      by (rule compat_orig[OF ge1 compat2[OF mid ge2]], auto)
  qed
qed
end

context lpoly_order
begin
definition bound_entry :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a list \<Rightarrow> bool"
  where "bound_entry bcoeff bconst \<equiv> \<lambda> (a,as). bconst \<succeq> a \<and> (\<forall> a \<in> set as. bcoeff \<succeq> a \<or> \<one> \<succeq> a)"

definition bound_entry_strict :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<times> 'a list \<Rightarrow> bool"
  where "bound_entry_strict bcoeff bconst \<equiv> \<lambda> (a,as). bconst \<succeq> a \<and> (\<forall> a \<in> set as. bcoeff \<succeq> a)"

lemma pow_ge_zero[intro]: assumes a: "a \<succeq> \<zero>"
  and wf: "a \<in> carrier R"
  shows "a [^] (n :: nat) \<succeq> \<zero>"
proof (induct n)
  case (Suc n)
  have "a [^] (Suc n) \<succeq> \<zero> \<otimes> a" unfolding nat_pow_Suc
    by (rule times_left_mono[OF a Suc], insert wf, auto)
  then show ?case using wf by auto
qed auto

lemma pow_commute_left: assumes wf[simp]: "a \<in> carrier R"
  shows "a [^] (n :: nat) \<otimes> a = a \<otimes> a [^] n"
proof (induct n)
  case (Suc n)
  have "a [^] (Suc n) \<otimes> a = (a \<otimes> a [^] n) \<otimes> a"
    unfolding nat_pow_Suc unfolding Suc ..
  also have "... = a \<otimes> (a [^] n \<otimes> a)" using wf nat_pow_closed[OF wf] by algebra
  finally show ?case by simp
qed simp

lemma pow_ge_1: assumes 1: "\<one> \<succeq> a"
  and 0: "a \<succeq> \<zero>"
  and wf: "a \<in> carrier R"
  shows "\<one> \<succeq> a [^] (n :: nat)"
proof (induct n)
  case (Suc n)
  have "(\<one> \<succeq> (a [^] (Suc n))) = ((\<one> \<otimes> \<one>) \<succeq> (a [^] n \<otimes> a))" by simp
  also have "..."
    by (rule geq_trans[OF times_right_mono[OF one_geq_zero 1] times_left_mono[OF 0 Suc]], insert wf, auto)
  then show ?case by simp
qed simp

lemma list_sum_append[simp]: assumes as: "set as \<subseteq> carrier R"
  and bs: "set bs \<subseteq> carrier R"
  shows "list_sum R (as @ bs) = list_sum R as \<oplus> list_sum R bs"
  using as 
proof (induct as)
  case Nil
  with wf_list_sum[OF bs] show ?case by auto
next
  case (Cons a as)
  then have IH: "list_sum R (as @ bs) = list_sum R as \<oplus> list_sum R bs" 
    and wf: "a \<in> carrier R" "set as \<subseteq> carrier R"
    by auto
  show ?case using IH wf_list_sum[OF wf(2)] wf(1) wf_list_sum[OF bs]
    by (simp, algebra)
qed
end


context linear_poly_order
begin

lemma bound_eval_term_main_0:
  assumes bF: "\<And> fn. fn \<in> F \<Longrightarrow> bound_entry_strict \<zero> bcv (pi fn)"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and t: "funas_term (t :: ('f,'v)term) \<subseteq> F"
  shows "bcv \<succeq> (pi\<guillemotleft>zero_ass,t>>)"
proof (cases t)
  case (Var x)
  then show ?thesis using bcv by (auto simp: zero_ass_def)
next
  case (Fun f ts)
  let ?e = "\<lambda> t. pi\<guillemotleft>zero_ass,t>>"
  let ?n = "length ts"
  obtain a as where pi: "pi (f, ?n) = (a,as)" by force
  let ?map = "map (\<lambda> at. fst at \<otimes> ?e (snd at)) (zip as ts)"
  let ?map' = "map (\<lambda> at. \<zero>) (zip as ts)"
  let ?nn = "length (zip as ts)"
  note wf = wf_pi[THEN conjunct1, rule_format, of "(f, ?n)", unfolded pi fst_conv snd_conv]
  from wf have wfa: "a \<in> carrier R" and wfas: "\<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R"
    and as0: "\<And> a. a \<in> set as \<Longrightarrow> a \<succeq> \<zero>" by auto
  from Fun t have "(f,?n) \<in> F" by auto
  from bF[OF this, unfolded pi bound_entry_strict_def split]
  have b_a: "bcv \<succeq> a" and b_as: "\<And> a. a \<in> set as \<Longrightarrow> \<zero> \<succeq> a" by auto
  have "\<zero> = list_sum R ?map'"
    by (induct "zip as ts", auto)
  also have "list_sum R ?map' \<succeq> list_sum R ?map"
  proof (rule list_sum_mono)
    fix at
    assume mem: "at \<in> set (zip as ts)"
    then obtain a t where at: "at = (a,t)" by force
    from set_zip_leftD[OF mem[unfolded at]] have a: "a \<in> set as" .
    have et0: "?e t \<succeq> \<zero>" and etC: "?e t \<in> carrier R" by auto
    from times_left_mono[OF et0 b_as[OF a] _ wfas[OF a] etC] etC wfas[OF a]
    show "\<zero> \<succeq> fst at \<otimes> ?e (snd at) \<and> \<zero> \<in> carrier R \<and> fst at \<otimes> ?e (snd at) \<in> carrier R"
      unfolding at by auto
  qed
  finally have map0: "\<zero> \<succeq> list_sum R ?map" .
  have wfmap: "list_sum R ?map \<in> carrier R"
    by (rule wf_list_sum, insert wfas, auto dest: set_zip_leftD)
  have "?e t = Max \<zero> (a \<oplus> list_sum R ?map)"
    unfolding Fun by (simp add: pi)
  also have "Max \<zero> (a \<oplus> \<zero>) \<succeq> \<dots>" 
    by (rule max_mono, rule plus_right_mono[OF map0], insert wfa wfmap, auto)
  also have "a \<oplus> \<zero> = a" using wfa by simp
  finally have ge2: "Max \<zero> a \<succeq> ?e t" .
  have "bcv \<succeq> Max \<zero> a" using b_a bcv wfbcv wfa
    by (metis max_mono max0_id_pos zero_closed)
  from geq_trans[OF this ge2 wfbcv] wfa
  show ?thesis by auto
qed  

lemma bound_eval_term_main:
  assumes bF: "\<And> fn. fn \<in> F \<Longrightarrow> bound_entry bc bcv (pi fn)"
  and bc: "bc \<succeq> \<zero>"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and wfbc: "bc \<in> carrier R"
  and t: "funas_term (t :: ('f,'v)term) \<subseteq> F"
  shows "\<exists> bs. length bs \<le> term_size t \<and> (\<forall> b \<in> set bs. b \<in> carrier R 
    \<and> (\<exists> n < term_size t. b = bc [^] n \<otimes> bcv)) \<and> (list_sum R bs \<succeq> (pi\<guillemotleft>zero_ass,t>>))"
  using t
proof (induct t)
  case (Var x)
  show ?case
    by (rule exI[of _ Nil], auto simp: zero_ass_def)
next
  case (Fun f ts)
  let ?e = "\<lambda> t. pi\<guillemotleft>zero_ass,t>>"
  let ?n = "length ts"
  obtain a as where pi: "pi (f, ?n) = (a,as)" by force
  let ?map = "map (\<lambda> at. fst at \<otimes> ?e (snd at)) (zip as ts)"
  let ?nn = "length (zip as ts)"
  note wf = wf_pi[THEN conjunct1, rule_format, of "(f, ?n)", unfolded pi fst_conv snd_conv]
  from wf have wfa: "a \<in> carrier R" and wfas: "\<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R"
    and as0: "\<And> a. a \<in> set as \<Longrightarrow> a \<succeq> \<zero>" by auto
  from Fun(2) have "(f,?n) \<in> F" by auto
  from bF[OF this, unfolded pi bound_entry_def split]
  have b_a: "bcv \<succeq> a" and b_as: "\<And> a. a \<in> set as \<Longrightarrow> (bc \<succeq> a) \<or> (\<one> \<succeq> a)" by auto
  obtain Pow where Pow: "Pow = (\<lambda> b (t :: ('f,'v)term). (\<exists> n < term_size t. b = bc [^] n \<otimes> bcv))" by auto
  let ?P = "\<lambda> bs i. length bs \<le> term_size (ts ! i) \<and> (\<forall> b \<in> set bs. Pow b (Fun f ts)) \<and> (\<forall> b \<in> set bs. b \<in> carrier R) \<and> (list_sum R bs \<succeq> ?map ! i)"
  {
    fix i
    assume i: "i < ?nn"
    then have ias: "i < length as" and its: "i < ?n" by auto
    from ias have asi: "as ! i \<in> set as" by auto
    from its have tsi: "ts ! i \<in> set ts" by auto
    from Fun(2) tsi have "funas_term (ts ! i) \<subseteq> F" by auto
    note IH = Fun(1)[OF tsi this]
    from as0[OF asi] have asi0: "as ! i \<succeq> \<zero>" .
    from b_as[OF asi] have b_asi: "(bc \<succeq> as ! i) \<or> (\<one> \<succeq> as ! i)" .
    from wfas[OF asi] have wfasi: "as ! i \<in> carrier R" .
    from i have id: "?map ! i = (as ! i \<otimes> ?e (ts ! i))" by auto
    have wf_map: "?map ! i \<in> carrier R" unfolding id using wfasi by auto
    from IH obtain bs where len: "length bs \<le> term_size (ts ! i)"
      and bs: "\<And> b. b \<in> set bs \<Longrightarrow> Pow b (ts ! i)"
      and wf_bs: "\<And> b. b \<in> set bs \<Longrightarrow> b \<in> carrier R"
      and ge2: "list_sum R bs \<succeq> ?e (ts ! i)" unfolding Pow by auto
    let ?bs = "map ((\<otimes>) bc) bs"
    have lsum: "list_sum R ?bs = bc \<otimes> list_sum R bs" using wf_bs
    proof (induct bs)
      case (Cons b bs)
      then have wfb: "b \<in> carrier R" and wfbs: "\<And> b. b \<in> set bs \<Longrightarrow> b \<in> carrier R" and
        IH: "list_sum R (map ((\<otimes>) bc) bs) = bc \<otimes> (list_sum R bs)" by auto
      show ?case unfolding list.map list_prod.simps
        unfolding IH monoid.simps 
        by (rule r_distr[symmetric], insert wfb wfbc wfbs, auto)
    qed (auto simp: wfbc)
    {
      fix bbc
      assume "bbc \<in> set ?bs"
      then obtain b where bbc: "bbc = bc \<otimes> b" and b: "b \<in> set bs" by auto
      then have "bbc \<in> carrier R" using wfbc wf_bs by auto
    } note wf_bs2 = this
    have size_tsi: "term_size (ts ! i) < term_size (Fun f ts)"
      by (rule supt_term_size, insert tsi, auto)
    {
      fix bbc
      assume "bbc \<in> set ?bs"
      then obtain b where bbc: "bbc = bc \<otimes> b" and b: "b \<in> set bs" by auto
      from bs[OF b] obtain n where b: "b = bc [^] n \<otimes> bcv" and n: "n < term_size (ts ! i)" unfolding Pow by auto
      have bbc: "bbc = bc [^] (Suc n) \<otimes> bcv" unfolding bbc b nat_pow_Suc pow_commute_left[OF wfbc]
        by (rule m_assoc[symmetric], insert wfbc wfbcv, auto)
      from size_tsi n have "Suc n < term_size (Fun f ts)" by auto
      with bbc have "\<exists> n < term_size (Fun f ts). bbc = bc [^] n \<otimes> bcv" by blast
      then have "Pow bbc (Fun f ts)" unfolding Pow .
    } note bs2 = this
    from b_asi have "\<exists> bs2. ?P bs2 i"
    proof
      assume b_asi: "bc \<succeq> as ! i"
      have ge: "(bc \<otimes> ?e (ts ! i)) \<succeq> ?map ! i" unfolding id
        by (rule times_left_mono[OF _ b_asi wfbc wfasi], auto)
      have ge2: "list_sum R ?bs \<succeq> (bc \<otimes> (?e (ts ! i)))" unfolding lsum
        by (rule times_right_mono[OF bc ge2 wfbc wf_list_sum], insert wf_bs wfbcv, auto)
      have ge: "list_sum R ?bs \<succeq> ?map ! i"
        by (rule geq_trans[OF ge2 ge wf_list_sum _ wf_map], insert wf_bs2 wfbc, auto)
      show "\<exists> bs2. ?P bs2 i"
        by (rule exI[of _ ?bs], unfold length_map, insert len ge bs2 wf_bs2, blast)
    next
      assume asi: "\<one> \<succeq> as ! i"
      show "\<exists> bs2. ?P bs2 i"
      proof (rule exI[of _ bs], rule conjI[OF len conjI[OF ballI conjI[OF ballI[OF wf_bs]]]])
        fix b
        assume "b \<in> set bs"
        from bs[OF this, unfolded Pow] obtain n where n: "n < term_size (ts ! i)" and b: "b = bc [^] n \<otimes> bcv"
          by auto
        with size_tsi have "n < term_size (Fun f ts)" by auto
        with b show "Pow b (Fun f ts)" unfolding Pow by blast
      next
        have "(\<one> \<otimes> ?e (ts ! i)) \<succeq> ?map ! i" unfolding id
          by (rule times_left_mono[OF _ asi _ wfasi], auto)
        then have ge: "?e (ts ! i) \<succeq> ?map ! i" by simp
        show "list_sum R bs \<succeq> ?map ! i"
          by (rule geq_trans[OF ge2 ge wf_list_sum _ wf_map], insert wf_bs, auto)
      qed
    qed
    note this \<open>?map ! i \<in> carrier R\<close>
  }
  then have bsi: "\<forall> i. \<exists> bs. i < ?nn \<longrightarrow> ?P bs i" and wfmi: "\<And> i. i < ?nn \<Longrightarrow> ?map ! i \<in> carrier R"
    by blast+
  from choice[OF bsi] obtain bs where bs: "\<And> i. i < ?nn \<Longrightarrow> ?P (bs i) i" by auto
  let ?bs' = "concat (map bs [0 ..< ?nn])"
  let ?bs = "bcv # ?bs'"
  have "length ?bs' \<le> sum_list (map term_size ts)" unfolding length_concat
    unfolding map_map o_def
    using bs[THEN conjunct1]
  proof (induct ts arbitrary: as bs)
    case (Cons t ts aas bs)
    note oCons = this
    show ?case
    proof (cases aas)
      case (Cons a as)
      note oCons = oCons[unfolded Cons]
      note IH = oCons(1)[of as "\<lambda> i. bs (Suc i)"]
      note pre = oCons(2)
      from pre[of "0 :: nat"] have le: "length (bs 0) \<le> term_size t" by auto
      {
        fix i
        assume i: "i < length (zip as ts)"
        then have i: "Suc i < length (zip (a # as) (t # ts))" by simp
        from pre[OF this] have "length (bs (Suc i)) \<le> term_size (ts ! i)" by auto
      }
      from IH[OF this] have
        le2: " (\<Sum>x\<leftarrow>[0..<length (zip as ts)]. length (bs (Suc x))) \<le> sum_list (map term_size ts)"
        by simp
      have "(\<Sum>x\<leftarrow>[0..<length (zip aas (t # ts))]. length (bs x)) =
        (\<Sum>x\<leftarrow>[0..< Suc (length (zip as ts))]. length (bs x))"
        unfolding Cons by simp
      also have "... = length (bs 0) + (\<Sum>x\<leftarrow>[0..< length (zip as ts)]. length (bs (Suc x)))"
        unfolding map_upt_Suc by simp
      also have "... \<le> term_size t + sum_list (map term_size ts)" using le le2 by auto
      finally
      show ?thesis by simp
    qed auto
  qed auto
  then have len: "length ?bs \<le> term_size (Fun f ts)" by auto
  {
    fix b
    assume "b \<in> set ?bs"
    then have "b = bcv \<or> b \<in> set ?bs'" by auto
    then have "b \<in> carrier R \<and> Pow b (Fun f ts) \<and> (b \<succeq> \<zero>)"
    proof
      assume b: "b = bcv"
      show ?thesis
        unfolding b Pow
        by (rule conjI[OF wfbcv], rule conjI, rule exI[of _ "0 :: nat"], insert wfbcv bcv, auto)
    next
      assume "b \<in> set ?bs'"
      then obtain i where i: "i < ?nn" and b: "b \<in> set (bs i)" by auto
      from i have ias: "i < length as" by auto
      then have asi: "as ! i \<in> set as" by auto
      from bs[OF i] b have "Pow b (Fun f ts)" by auto
      from this[unfolded Pow] obtain n where bpow: "b = bc [^] (n :: nat) \<otimes> bcv" by auto
      have "b \<succeq> \<zero> \<otimes> bcv" unfolding bpow
        by (rule times_left_mono[OF bcv pow_ge_zero], insert wfbc wfbcv bc, auto)
      then have "b \<succeq> \<zero>" using wfbcv by auto
      with bs[OF i] b show ?thesis by auto
    qed
  } note bs_wf_pow = this
  show ?case
  proof (rule exI[of _ ?bs], intro conjI, rule len, intro ballI)
    fix b
    assume "b \<in> set ?bs"
    from bs_wf_pow[OF this]
    show "b \<in> carrier R \<and> (\<exists> n < term_size (Fun f ts). b = bc [^] n \<otimes> bcv)"
      unfolding Pow by simp
  next
    have wf_bs: "list_sum R ?bs \<in> carrier R"
      using bs_wf_pow by auto
    let ?sum = "a \<oplus> list_sum R ?map"
    have e: "?e (Fun f ts) = Max \<zero> ?sum" unfolding eval_termI.simps Let_def pi split ..
    {
      fix p
      assume "p \<in> set ?map"
      from this[unfolded set_map set_zip]
      obtain i where i: "i < length as" and p: "p = (as ! i \<otimes> ?e (ts ! i))" by auto
      from i have asi: "as ! i \<in> set as" by auto
      from wfas[OF asi] have "p \<in> carrier R" unfolding p by auto
    } note wf_prods = this
    then have wf_sum: "list_sum R ?map \<in> carrier R" by auto
    with wfa have wf_asum: "?sum \<in> carrier R" by auto
    have "list_sum R ?bs = Max \<zero> (list_sum R ?bs)"
      by (rule max0_id_pos[symmetric, OF pos_list_sum wf_bs], insert bs_wf_pow, auto)
    also have "... \<succeq> ?e (Fun f ts)" unfolding e
    proof (rule max_mono[OF _ wf_bs wf_asum])
      have wf_bs': "list_sum R ?bs' \<in> carrier R" using bs_wf_pow by auto
      have id: "list_sum R ?bs = bcv \<oplus> list_sum R ?bs'" by simp
      have ge1: "... \<succeq> a \<oplus> list_sum R ?bs'"
        by (rule plus_left_mono[OF b_a wfbcv wfa wf_bs'])
      have ge2: "... \<succeq> ?sum"
      proof (rule plus_right_mono[OF _ wfa wf_bs' wf_sum])
        obtain z where z: "z = zip as ts" by auto
        obtain f where f: "f = (\<lambda> (at :: 'a \<times> ('f,'v)term). fst at \<otimes> ?e (snd at))" by auto
        from wf_prods have "\<And> p. p \<in> set (map f z) \<Longrightarrow> p \<in> carrier R"
          unfolding f z .
        then show "list_sum R ?bs' \<succeq> list_sum R ?map" using bs[THEN conjunct2, THEN conjunct2] unfolding z[symmetric] f[symmetric]
        proof (induct z arbitrary: bs)
          case (Cons a z bs)
          note IH = Cons(1)[of "\<lambda> i. bs (Suc i)"]
          note wfaz = Cons(2)
          then have wfa: "f a \<in> carrier R" and wfz: "\<And> p. p \<in> set (map f z) \<Longrightarrow> p \<in> carrier R" by auto
          note bs = Cons(3)
          {
            fix i
            assume "i < length z"
            then have "Suc i < length (a # z)" by auto
            from bs[OF this]
            have "(\<forall> a \<in> set (bs (Suc i)). a \<in> carrier R) \<and> (list_sum R (bs (Suc i)) \<succeq> map f z ! i)" by auto
          } note bsz = this
          let ?cc = "concat (map (\<lambda> i. bs (Suc i)) [0 ..< length z])"
          from IH[OF wfz bsz] have ge2: "list_sum R ?cc \<succeq> list_sum R (map f z)" .
          from bs[of "0 :: nat"] have wfbs0: "\<And> a. a \<in> set (bs 0) \<Longrightarrow> a \<in> carrier R"
            and ge1: "list_sum R (bs 0) \<succeq> f a" by auto
          let ?start = "list_sum R (concat (map bs [0..<length (a # z)]))"
          have "list_sum R (concat (map bs [0..<length (a # z)]))
            = list_sum R (concat (map bs [0..< Suc (length z)]))" by simp
          also have "... = list_sum R (bs 0 @ ?cc)"
            unfolding map_upt_Suc by auto
          also have "... = list_sum R (bs 0) \<oplus> list_sum R ?cc"
            by (rule list_sum_append, insert wfbs0 bsz, auto)
          finally have id: "?start = list_sum R (bs 0) \<oplus> list_sum R ?cc" "list_sum R (map f (a # z)) = f a \<oplus> list_sum R (map f z)" by auto
          show ?case unfolding id
            by (rule plus_left_right_mono[OF ge1 ge2], insert wfbs0 wfa wfz bsz, auto)
        qed simp
      qed
      show "list_sum R ?bs \<succeq> ?sum" unfolding id
        by (rule geq_trans[OF ge1 ge2 _ _ wf_asum], insert wfa wfbcv bs_wf_pow, auto)
    qed auto
    finally
    show "list_sum R ?bs \<succeq> ?e (Fun f ts)" .
  qed
qed
end

locale complexity_linear_poly_order = linear_poly_order + complexity_linear_poly_order_carrier
begin

lemma bound_eval_term_derivational_0:
  assumes bF: "\<And> fn. fn \<in> set F \<Longrightarrow> bound_entry_strict \<zero> bcv (pi fn)"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and deriv: "t \<in> terms_of (Derivational_Complexity F)"
  shows "bound R bcv \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
  by (rule bound_mono[OF bound_eval_term_main_0[OF bF bcv], of "set F"],
  insert deriv wfbcv, auto)

lemma bound_eval_term_derivational:
  assumes bF: "\<And> fn. fn \<in> set F \<Longrightarrow> bound_entry bc bcv (pi fn)"
  and bc: "bc \<succeq> \<zero>"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and wfbc: "bc \<in> carrier R"
  and mono: "\<And> n m. n \<le> m \<Longrightarrow> g n \<le> g m"
  and bG: "\<And> n. bound R (bc [^] n \<otimes> bcv) \<le> g n"
  and deriv: "t \<in> terms_of_nat (Derivational_Complexity F) N"
  shows "g N * N \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  from deriv have t: "funas_term t \<subseteq> set F" and N: "term_size t \<le> N" by auto
  from bound_eval_term_main[OF bF bc bcv wfbcv wfbc t]
  obtain bs where len: "length bs \<le> term_size t"
    and bs: "\<And> b. b \<in> set bs \<Longrightarrow> b \<in> carrier R \<and> (\<exists> n < term_size t. b = bc [^] n \<otimes> bcv)"
    and ge: "list_sum R bs \<succeq> (pi\<guillemotleft>zero_ass,t>>)"
    by auto
  {
    fix b
    assume "b \<in> set bs"
    from bs[OF this] obtain n where wf: "b \<in> carrier R" and n: "n < term_size t" and b: "b = bc [^] n \<otimes> bcv"
      by auto
    from bG[of n] have ge: "g n \<ge> bound R b" unfolding b .
    from n N have "n \<le> N" by auto
    from mono[OF this] ge wf have "g N \<ge> bound R b" "b \<in> carrier R" by auto
  } note bs = this
  then have "bound R (list_sum R bs) \<le> g N * length bs"
  proof (induct bs)
    case (Cons b bs)
    from Cons have ge1: "g N \<ge> bound R b" by auto
    from Cons have ge2: "g N * length bs \<ge> bound R (list_sum R bs)" by auto
    have id: "bound R (list_sum R (b # bs)) \<le> bound R b + bound R (list_sum R bs)" 
      unfolding list_prod.simps monoid.simps
      by (rule bound_plus, insert Cons, auto)
    also have "... \<le> g N + g N * length bs" using ge1 ge2 by arith
    finally show ?case by simp
  qed simp
  also have "... \<le> g N * size N"
    using len N by auto
  finally have "bound R (list_sum R bs) \<le> g N * N" by simp
  from order_trans[OF bound_mono[OF ge] this]
  show ?thesis using bs by auto
qed

lemma bound_eval_term_runtime_0:
  assumes bF: "\<And> fn. fn \<in> set C \<Longrightarrow> bound_entry_strict \<zero> bcv (pi fn)"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and bD: "\<And> fn. fn \<in> set D \<Longrightarrow> bound_entry_strict bd bdv (pi fn)"
  and bn: "\<And> fn. fn \<in> set D \<Longrightarrow> snd fn \<le> bn"
  and bd: "bd \<succeq> \<zero>"
  and bdv: "bdv \<succeq> \<zero>"
  and wfbdv: "bdv \<in> carrier R"
  and wfbd: "bd \<in> carrier R"
  and rt: "t \<in> terms_of (Runtime_Complexity C D)"
  shows "bound R bdv + bn * bound R (bd \<otimes> bcv) \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  let ?e = "\<lambda> t. (pi\<guillemotleft>zero_ass,t>>)"
  from rt obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  let ?n = "length ts"
  from rt t have fD: "(f,length ts) \<in> set D" and ti: "\<And> t. t \<in> set ts \<Longrightarrow> funas_term t \<subseteq> set C"
    by (auto simp: funas_args_term_def)
  from bound_eval_term_main_0[OF bF bcv wfbcv ti] have ti: "\<And> t. t \<in> set ts \<Longrightarrow> bcv \<succeq> ?e t" by auto
  obtain a as where pi: "pi (f, ?n) = (a,as)" by force
  let ?map = "map (\<lambda> at. fst at \<otimes> ?e (snd at)) (zip as ts)"
  let ?nn = "length (zip as ts)"
  note wf = wf_pi[THEN conjunct1, rule_format, of "(f, ?n)", unfolded pi fst_conv snd_conv]
  from wf have wfa: "a \<in> carrier R" and wfas: "\<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R"
    and as0: "\<And> a. a \<in> set as \<Longrightarrow> a \<succeq> \<zero>" by auto
  from bD[OF fD, unfolded pi bound_entry_strict_def split]
  have b_a: "bdv \<succeq> a" and b_as: "\<And> a. a \<in> set as \<Longrightarrow> bd \<succeq> a" by auto
  define prods where "prods = ?map"
  {
    fix p
    assume p: "p \<in> set prods"
    from this[unfolded prods_def set_map]
    obtain at where mem: "at \<in> set (zip as ts)" and p: "p = fst at \<otimes> ?e (snd at)" by auto
    obtain a t where at: "at = (a,t)" by force
    from set_zip_leftD[OF mem[unfolded at]] have a: "a \<in> set as" .
    from set_zip_rightD[OF mem[unfolded at]] have t: "t \<in> set ts" .
    have et0: "?e t \<succeq> \<zero>" and etC: "?e t \<in> carrier R" by auto
    from times_left_mono[OF et0 b_as[OF a] wfbd wfas[OF a] etC]
    have ge1: "bd \<otimes> ?e t \<succeq> a \<otimes> ?e t" .
    from pos_term[of zero_ass t] have "?e t \<succeq> \<zero>" by auto
    from times_right_mono[OF as0[OF a] this _ etC] wfas[OF a] have a0: "a \<otimes> ?e t \<succeq> \<zero>" by auto
    from times_right_mono[OF bd ti[OF t] wfbd wfbcv etC] have "bd \<otimes> bcv \<succeq> bd \<otimes> ?e t" .
    from bound_mono[OF geq_trans[OF this ge1]] wfbd wfbcv etC wfas[OF a] as0[OF a] a0      
    have "bound R p \<le> bound R (bd \<otimes> bcv)"
      "p \<in> carrier R"
      "p \<succeq> \<zero>" unfolding p at by auto
  } note bound_prods = this
  from bn[OF fD] have bn: "length prods \<le> bn" unfolding prods_def by simp
  have "bound R (?e t) = bound R (Max \<zero> (a \<oplus> list_sum R prods))"
    unfolding t using pi by (simp add: prods_def)
  also have "... \<le> bound R (Max \<zero> (bdv \<oplus> list_sum R prods))"
    by (rule bound_mono[OF max_mono[OF plus_left_mono[OF b_a]]], insert wfa wfbdv bound_prods, auto simp: wf_max0)
  also have "Max \<zero> (bdv \<oplus> list_sum R prods) = bdv \<oplus> list_sum R prods"
  proof (rule max0_id_pos)
    have "bdv \<oplus> list_sum R prods \<succeq> \<zero> \<oplus> \<zero>"
      by (rule geq_trans[OF plus_right_mono[OF pos_list_sum] plus_left_mono[OF bdv]], insert wfa wfbdv bound_prods, auto)
    then show "bdv \<oplus> list_sum R prods \<succeq> \<zero>" by simp
  qed (insert bound_prods wfbdv, auto)
  also have "bound R (bdv \<oplus> list_sum R prods) \<le> bound R bdv + bound R (list_sum R prods)"
    by (rule bound_plus, insert bound_prods wfbdv, auto)
  also have "bound R (list_sum R prods) \<le> bn * bound R (bd \<otimes> bcv)" using bn bound_prods(1-2)
  proof (induct prods arbitrary: bn)
    case (Cons p ps sbn)
    from Cons(2) obtain bn where sbn: "sbn = Suc bn" and len: "length ps \<le> bn" by (cases sbn, auto)
    from Cons(1)[OF len Cons(3-4)] have 
      IH: "bound R (list_sum R ps) \<le> bn * bound R (bd \<otimes> bcv)" by auto
    have "bound R (list_sum R (p # ps)) \<le> bound R p + bound R (list_sum R ps)" using Cons(3-4)
      by (auto intro: bound_plus)
    also have "\<dots> \<le> bound R p + bn * bound R (bd \<otimes> bcv)" using IH by simp
    also have "bound R p \<le> bound R (bd \<otimes> bcv)"
      by (rule Cons(3), auto)
    finally show ?case unfolding sbn by auto
  qed simp
  finally show "bound R (?e t) \<le> bound R bdv + bn * bound R (bd \<otimes> bcv)" by auto
qed

lemma bound_eval_term_runtime:
  assumes bC: "\<And> fn. fn \<in> set C \<Longrightarrow> bound_entry bc bcv (pi fn)"
  and bc: "bc \<succeq> \<zero>"
  and bcv: "bcv \<succeq> \<zero>"
  and wfbcv: "bcv \<in> carrier R"
  and wfbc: "bc \<in> carrier R"
  and bD: "\<And> fn. fn \<in> set D \<Longrightarrow> bound_entry_strict bd bdv (pi fn)"
  and bn: "\<And> fn. fn \<in> set D \<Longrightarrow> snd fn \<le> bn"
  and bd: "bd \<succeq> \<zero>"
  and bdv: "bdv \<succeq> \<zero>"
  and wfbdv: "bdv \<in> carrier R"
  and wfbd: "bd \<in> carrier R"
  and mono: "\<And> n m. n \<le> m \<Longrightarrow> g n \<le> g m"
  and bG: "\<And> n. bound R (bd \<otimes> (bc [^] n \<otimes> bcv)) \<le> g n"
  and deriv: "t \<in> terms_of_nat (Runtime_Complexity C D) N"
  shows "bound R bdv + g N * N * bn \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  from deriv[simplified] obtain f ts where t: "t = Fun f ts" and f: "(f,length ts) \<in> set D" and
    ts: "\<And> ti. ti \<in> set ts \<Longrightarrow> funas_term ti \<subseteq> set C" and size: "term_size t \<le> N"
    by (cases t) (auto simp: funas_args_term_def)
  obtain a as where pi: "pi (f,length ts) = (a,as)" by force
  from bn[OF f] have bn: "length ts \<le> bn" by simp
  from bD[OF f] have ge_a: "bdv \<succeq> a" and ge_as: "\<And> a . a \<in> set as \<Longrightarrow> bd \<succeq> a"
    unfolding pi bound_entry_strict_def by auto
  from wf_pi[THEN conjunct1, rule_format, of "(f,length ts)", unfolded pi]
  have wfa: "a \<in> carrier R" and wfas: "\<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R" and as0: "\<And> a. a \<in> set as \<Longrightarrow> a \<succeq> \<zero>" by auto
  let ?eval = "\<lambda> t. (pi\<guillemotleft>zero_ass,t>>)"
  let ?p = "\<lambda> at. fst at \<otimes> ?eval (snd at)"
  let ?map = "map ?p (zip as ts)"
  obtain prods where prods: "prods = ?map" by auto
  {
    fix p
    assume "p \<in> set prods"
    from this[unfolded prods set_conv_nth] obtain i where ias: "i < length as" and its: "i < length ts"
      and p: "p = ?map ! i" by auto
    let ?asi = "as ! i"
    let ?tsi = "ts ! i"
    from p ias its have p: "p = (?asi \<otimes> ?eval ?tsi)" by auto
    from ias have asi: "?asi \<in> set as" by auto
    from wfas[OF this] as0[OF this] ge_as[OF this] have wfasi: "?asi \<in> carrier R" and asi0: "?asi \<succeq> \<zero>"
      and bd_ge: "bd \<succeq> as ! i" .
    from its have tsi: "?tsi \<in> set ts" by auto
    from ts[OF tsi] have tsiC: "funas_term ?tsi \<subseteq> set C" .
    from tsi have "t \<rhd> ?tsi" unfolding t by auto
    from supt_term_size[OF this] size have size: "term_size ?tsi \<le> N" by simp
    from bound_eval_term_main[OF bC bc bcv wfbcv wfbc tsiC]
    obtain bs where len: "length bs \<le> term_size ?tsi"
      and bs: "\<And> b. b \<in> set bs \<Longrightarrow> b \<in> carrier R \<and> (\<exists> n < term_size ?tsi. b = bc [^] n \<otimes> bcv)"
      and ge: "list_sum R bs \<succeq> ?eval ?tsi"
      by auto
    have bd_p: "bd \<otimes> list_sum R bs \<succeq> p" unfolding p
      by (rule geq_trans[OF times_left_mono[OF geq_trans[OF ge pos_term] bd_ge wfbd wfasi] times_right_mono[OF asi0 ge]], insert bs wfasi wfbd, auto)
    from bs have gn_bd: "g N * length bs \<ge> bound R (bd \<otimes> list_sum R bs)"
    proof (induct bs)
      case (Cons b bs)
      from Cons(2)[of b] obtain n where n: "n < term_size ?tsi" and b: "b = bc [^] n \<otimes> bcv" by auto
      from n size have n: "n \<le> N" by auto
      from Cons(2) have wf: "b \<in> carrier R" "set bs \<subseteq> carrier R" by auto
      have "bound R (bd \<otimes> list_sum R (b # bs)) = bound R (bd \<otimes> b \<oplus> bd \<otimes> list_sum R bs)"
        by (rule arg_cong[of _ _ "bound R"], simp, insert wf wfbd wf_list_sum[OF wf(2)], algebra)
      also have "... \<le> bound R (bd \<otimes> b) + bound R (bd \<otimes> list_sum R bs)"
        by (rule bound_plus, insert Cons(2) wfbd, auto)
      also have "... \<le> bound R (bd \<otimes> b) + g N * length bs"
        using Cons by auto
      also have "bound R (bd \<otimes> b) \<le> g n" unfolding b by (rule bG)
      also have "... \<le> g N"
        by (rule mono[OF n])
      finally show ?case by simp
    qed (simp add: wfbd)
    from le_trans[OF bound_mono[OF bd_p] gn_bd]
    have "bound R p \<le> g N * length bs" using bs wfbd wfasi unfolding p by auto
    also have "... \<le> g N * N"
      using le_trans[OF len size]  by auto
    finally have main: "bound R p \<le> g N * N" "p \<in> carrier R" unfolding p using wfasi by auto
    have "p \<succeq> \<zero> \<otimes> \<zero>" unfolding p
      by (rule geq_trans[OF times_left_mono[OF pos_term asi0]], insert wfasi, auto)
    then have "p \<succeq> \<zero>" by simp
    note main this
  } note bound_prods = this
  have "bound R (?eval t) = bound R (Max \<zero> (a \<oplus> list_sum R prods))"
    unfolding t using pi by (simp add: Let_def prods)
  also have "... \<le> bound R (Max \<zero> ( bdv \<oplus> list_sum R prods))"
    by (rule bound_mono[OF max_mono[OF plus_left_mono[OF ge_a]]], insert wfa wfbdv bound_prods, auto simp: wf_max0)
  also have "Max \<zero> (bdv \<oplus> list_sum R prods) = bdv \<oplus> list_sum R prods"
  proof (rule max0_id_pos)
    have "bdv \<oplus> list_sum R prods \<succeq> \<zero> \<oplus> \<zero>"
      by (rule geq_trans[OF plus_right_mono[OF pos_list_sum] plus_left_mono[OF bdv]], insert wfa wfbdv bound_prods, auto)
    then show "bdv \<oplus> list_sum R prods \<succeq> \<zero>" by simp
  qed (insert bound_prods wfbdv, auto)
  also have "bound R (bdv \<oplus> list_sum R prods) \<le> bound R bdv + bound R (list_sum R prods)"
    by (rule bound_plus, insert bound_prods wfbdv, auto)
  also have "bound R (list_sum R prods) \<le> g N * N * length (prods)"
    using bound_prods(1) bound_prods(2)
  proof (induct prods)
    case (Cons p prods)
    have "bound R (list_sum R (p # prods)) \<le> bound R p + bound R (list_sum R prods)"
      unfolding list_prod.simps monoid.simps
      by (rule bound_plus, insert Cons(3), auto)
    also have "bound R (list_sum R prods) \<le> g N * N * length prods"
      using Cons by auto
    also have "bound R p \<le> g N * N" using Cons(2)[of p] by auto
    finally show ?case by simp
  qed simp
  also have "... \<le> g N * N * bn"
  proof -
    from prods bn have "length prods \<le> bn" by simp
    then show ?thesis by simp
  qed
  finally show "bound R (?eval t) \<le> bound R bdv + g N * N * bn" by auto
qed
end

context ordered_semiring
begin

lemma poly_c_max_list:
  assumes init: "init \<in> carrier R"
  shows "\<lbrakk> \<And> a. a \<in> set as \<Longrightarrow> a \<in> carrier R\<rbrakk> \<Longrightarrow>
  (foldr Max as init)  \<in> carrier R \<and> (foldr Max as init) \<succeq> init \<and> (\<forall> a \<in> set as. (foldr Max as init) \<succeq> a)"
proof (induct as)
  case (Cons a as)
  let ?w = "\<lambda> a. a \<in> carrier R"
  from Cons(2) have a: "?w a" and as: "\<And> a. a \<in> set as \<Longrightarrow> ?w a" by auto
  let ?mf = "foldr Max as init"
  let ?mm = "Max a ?mf"
  note IH = Cons(1)[OF as]
  from IH have mf: "?w ?mf" and ge_init: "?mf \<succeq> init" and ge_as: "\<And> a. a \<in> set as \<Longrightarrow> ?mf \<succeq> a" by auto
  from wf_max[OF a mf] have mm: "?w ?mm" .
  from max_ge[OF a mf] have mm_a: "?mm \<succeq> a" .
  from max_ge_right[OF a mf] have mm_mf: "?mm \<succeq> ?mf" .
  note mm_mf = geq_trans[OF mm_mf _ mm mf]
  from mm_mf[OF ge_init init] have mm_init: "?mm \<succeq> init" .
  from mm_mf[OF ge_as as] have mm_as: "\<And> a. a \<in> set as \<Longrightarrow> ?mm \<succeq> a" .
  from mm mm_init mm_as mm_a
  show ?case by simp
qed (simp add: init)
end

context
  fixes R :: "('a,'b)ordered_semiring_scheme" (structure)
begin

definition poly_c_max_inter_bcoeff :: "('f \<times> nat)list \<Rightarrow> ('f,'a)lpoly_inter \<Rightarrow> 'a"
  where "poly_c_max_inter_bcoeff F pi = foldr Max (concat (map (\<lambda> fn. filter (\<lambda> b. \<not> (\<one> \<succeq> b)) (snd (pi fn))) F)) \<zero>"

definition poly_c_max_inter_bcoeff_strict :: "('f \<times> nat)list \<Rightarrow> ('f,'a)lpoly_inter \<Rightarrow> 'a"
  where "poly_c_max_inter_bcoeff_strict F pi = foldr Max (concat (map (\<lambda> fn. snd (pi fn)) F)) \<zero>"

definition poly_c_max_inter_bconst :: "('f \<times> nat)list \<Rightarrow> ('f,'a)lpoly_inter \<Rightarrow> 'a"
  where "poly_c_max_inter_bconst F pi = foldr Max (map (\<lambda> fn. fst (pi fn)) F) \<zero>"

end

context linear_poly_order
begin

lemma poly_c_max_inter_bcoeff:
  "poly_c_max_inter_bcoeff R F pi \<in> carrier R \<and> poly_c_max_inter_bcoeff R F pi \<succeq> \<zero> \<and>
  (\<forall> a \<in> set (concat (map (\<lambda> fn. filter (\<lambda> b. \<not> (\<one> \<succeq> b)) (snd (pi fn))) F)). poly_c_max_inter_bcoeff R F pi \<succeq> a)"
  unfolding poly_c_max_inter_bcoeff_def
  by (rule poly_c_max_list[OF zero_closed], insert wf_pi, auto)

lemma poly_c_max_inter_bcoeff_strict:
  "poly_c_max_inter_bcoeff_strict R F pi \<in> carrier R \<and> poly_c_max_inter_bcoeff_strict R F pi \<succeq> \<zero> \<and>
  (\<forall> a \<in> set (concat (map (\<lambda> fn. snd (pi fn)) F)). poly_c_max_inter_bcoeff_strict R F pi \<succeq> a)"
  unfolding poly_c_max_inter_bcoeff_strict_def
  by (rule poly_c_max_list[OF zero_closed], insert wf_pi, auto)

lemma poly_c_max_inter_bconst:
  "poly_c_max_inter_bconst R F pi \<in> carrier R \<and> poly_c_max_inter_bconst R F pi \<succeq> \<zero> \<and>
  (\<forall> a \<in> set (map (\<lambda> fn. fst (pi fn)) F). poly_c_max_inter_bconst R F pi \<succeq> a)"
  unfolding poly_c_max_inter_bconst_def
  by (rule poly_c_max_list[OF zero_closed], insert wf_pi, auto)
end

context complexity_linear_poly_order
begin

lemma bound_eval_term_max_derivational:
  assumes mono: "\<And> n m. n \<le> m \<Longrightarrow> g n \<le> g m"
  and bG: "\<And> n. bound R ( poly_c_max_inter_bcoeff R F pi [^] n \<otimes> (poly_c_max_inter_bconst R F pi)) \<le> g n"
  and t: "t \<in> terms_of_nat (Derivational_Complexity F) N"
  shows "g N * N \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  let ?bc = "poly_c_max_inter_bcoeff R F pi"
  let ?bcv = "poly_c_max_inter_bconst R F pi"
  let ?c = "concat (map (\<lambda> fn. filter (\<lambda> b. \<not> (\<one> \<succeq> b)) (snd (pi fn))) F)"
  let ?cv = "map (\<lambda> fn. fst (pi fn)) F"
  have bc: "?bc \<in> carrier R \<and> ?bc \<succeq> \<zero> \<and> (\<forall> a \<in> set ?c. ?bc \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff)
  have bcv: "?bcv \<in> carrier R \<and> ?bcv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?cv. ?bcv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  {
    fix fn
    assume fn: "fn \<in> set F"
    obtain a as where pi: "pi fn = (a,as)" by force
    have "bound_entry ?bc ?bcv (pi fn)"
      unfolding bound_entry_def pi split
      using fn bcv bc pi by force+
  } note bound_entry = this
  show ?thesis
    by (rule bound_eval_term_derivational[OF bound_entry _ _ _ _ mono bG t], insert bc bcv, auto)
qed

lemma bound_eval_term_max_derivational_0:
  assumes c0: "poly_c_max_inter_bcoeff_strict R F pi = \<zero>"
  shows "\<exists> c. \<forall> t. t \<in> terms_of (Derivational_Complexity F) \<longrightarrow> c \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  let ?bc = "poly_c_max_inter_bcoeff_strict R F pi"
  let ?bcv = "poly_c_max_inter_bconst R F pi"
  let ?c = "concat (map (\<lambda> fn. (snd (pi fn))) F)"
  let ?cv = "map (\<lambda> fn. fst (pi fn)) F"
  have bc: "?bc \<in> carrier R \<and> ?bc \<succeq> \<zero> \<and> (\<forall> a \<in> set ?c. ?bc \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff_strict)
  have bcv: "?bcv \<in> carrier R \<and> ?bcv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?cv. ?bcv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  show ?thesis
    by (intro exI impI allI, rule bound_eval_term_derivational_0[of F ?bcv],
      insert bc bcv c0, auto simp: bound_entry_strict_def)
qed

lemma bound_eval_term_max_runtime_0:
  assumes c0: "poly_c_max_inter_bcoeff_strict R C pi = \<zero>"
  shows "\<exists> c. \<forall> t. t \<in> terms_of (Runtime_Complexity C D) \<longrightarrow> c \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  let ?bc = "poly_c_max_inter_bcoeff_strict R C pi"
  let ?bcv = "poly_c_max_inter_bconst R C pi"
  let ?c = "concat (map (\<lambda> fn. (snd (pi fn))) C)"
  let ?cv = "map (\<lambda> fn. fst (pi fn)) C"
  let ?bd = "poly_c_max_inter_bcoeff_strict R D pi"
  let ?bdv = "poly_c_max_inter_bconst R D pi"
  let ?d = "concat (map (\<lambda> fn. snd (pi fn)) D)"
  let ?dv = "map (\<lambda> fn. fst (pi fn)) D"
  let ?bn = "max_list (map snd D)"
  have bd: "?bd \<in> carrier R \<and> ?bd \<succeq> \<zero> \<and> (\<forall> a \<in> set ?d. ?bd \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff_strict)
  have bdv: "?bdv \<in> carrier R \<and> ?bdv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?dv. ?bdv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  have bc: "?bc \<in> carrier R \<and> ?bc \<succeq> \<zero> \<and> (\<forall> a \<in> set ?c. ?bc \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff_strict)
  have bcv: "?bcv \<in> carrier R \<and> ?bcv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?cv. ?bcv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  show ?thesis
    by (intro exI impI allI, rule bound_eval_term_runtime_0[of C ?bcv D ?bd ?bdv ?bn],
    insert bc bcv c0 bd bdv, auto simp: bound_entry_strict_def max_list)
qed

lemma bound_eval_term_max_runtime:
  assumes mono: "\<And> n m. n \<le> m \<Longrightarrow> g n \<le> g m"
  and bG: "\<And> n. bound R (poly_c_max_inter_bcoeff_strict R D pi \<otimes> (poly_c_max_inter_bcoeff R C pi [^] n \<otimes> (poly_c_max_inter_bconst R C pi))) \<le> g n"
  and t: "t \<in> terms_of_nat (Runtime_Complexity C D) N"
  shows "bound R (poly_c_max_inter_bconst R D pi) + g N * N * max_list (map snd D) \<ge> bound R (pi\<guillemotleft>zero_ass,t>>)"
proof -
  let ?bc = "poly_c_max_inter_bcoeff R C pi"
  let ?bcv = "poly_c_max_inter_bconst R C pi"
  let ?bd = "poly_c_max_inter_bcoeff_strict R D pi"
  let ?bdv = "poly_c_max_inter_bconst R D pi"
  let ?c = "concat (map (\<lambda> fn. filter (\<lambda> b. \<not> (\<one> \<succeq> b)) (snd (pi fn))) C)"
  let ?d = "concat (map (\<lambda> fn. snd (pi fn)) D)"
  let ?cv = "map (\<lambda> fn. fst (pi fn)) C"
  let ?dv = "map (\<lambda> fn. fst (pi fn)) D"
  have bc: "?bc \<in> carrier R \<and> ?bc \<succeq> \<zero> \<and> (\<forall> a \<in> set ?c. ?bc \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff)
  have bcv: "?bcv \<in> carrier R \<and> ?bcv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?cv. ?bcv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  have bd: "?bd \<in> carrier R \<and> ?bd \<succeq> \<zero> \<and> (\<forall> a \<in> set ?d. ?bd \<succeq> a)"
    by (rule poly_c_max_inter_bcoeff_strict)
  have bdv: "?bdv \<in> carrier R \<and> ?bdv \<succeq> \<zero> \<and> (\<forall> a \<in> set ?dv. ?bdv \<succeq> a)"
    by (rule poly_c_max_inter_bconst)
  {
    fix fn
    assume fn: "fn \<in> set C"
    obtain a as where pi: "pi fn = (a,as)" by force
    have "bound_entry ?bc ?bcv (pi fn)"
      unfolding bound_entry_def pi split
      using fn bcv bc pi by force+
  } note bound_entry = this
  {
    fix fn
    assume fn: "fn \<in> set D"
    obtain a as where pi: "pi fn = (a,as)" by force
    have "bound_entry_strict ?bd ?bdv (pi fn)"
      unfolding bound_entry_strict_def pi split
      using fn bdv bd pi by force+
  } note bound_entry_strict = this
  let ?bn = "max_list (map snd D)"
  {
    fix fn
    assume fn: "fn \<in> set D"
    then have "snd fn \<in> set (map snd D)" by simp
    from max_list[OF this] have "snd fn \<le> ?bn" .
  } note bn = this
  show ?thesis
    by (rule bound_eval_term_runtime[OF bound_entry _ _ _ _ bound_entry_strict _ _ _ _ _ mono bG t],
      insert bc bcv bd bdv bn, auto)
qed
end

context 
  fixes R :: "('a, 'b) lpoly_order_semiring_scheme" (structure)
begin

fun convert_lpoly_complexity  :: "('f, 'a)lpoly_inter \<Rightarrow> ('f, 'v) complexity_measure \<Rightarrow> complexity_class \<Rightarrow> showsl check" where
   "convert_lpoly_complexity pi cm (Comp_Poly deg) = (let
        F = (case cm of Derivational_Complexity F \<Rightarrow> F | Runtime_Complexity C D \<Rightarrow> C);
        bc = poly_c_max_inter_bcoeff R F pi;
        bc' = poly_c_max_inter_bcoeff_strict R F pi
      in do {
        check (deg > 0 \<or> bc' = \<zero>) 
          (showsl (STR ''constant complexity not fully supported for linear (poly/matrix)-interpretations''));
        check_complexity R bc (deg - 1)        
      })"
end

locale linear_poly_order_impl =
  fixes C :: "'a :: showl lpoly_order_semiring" (structure)
    and check_inter :: "showsl check"
  assumes carrier: "\<And> as. isOK(check_inter) \<Longrightarrow> \<exists> gt bnd. lpoly_order (C \<lparr>gt := gt, bound := bnd\<rparr>) \<and>
       (\<forall> (a,b) \<in> set as. a \<in> carrier C \<longrightarrow> b \<in> carrier C \<longrightarrow> a \<succ> b \<longrightarrow> gt a b) \<and>
       (psm \<longrightarrow>  
         complexity_linear_poly_order_carrier (C \<lparr>gt := gt, bound := bnd\<rparr>))" 
begin 

(* TODO: check whether we can change the position of C and C \<lparr> gt := gt, bound := bnd \<rparr> *)
lemma linear_poly_order:
  fixes I :: "('f :: {showl, compare_order}, 'a) lpoly_interL"
  defines [simp]: "II \<equiv> to_lpoly_inter C I :: ('f, 'a) lpoly_inter"
  assumes check_coeffs: "isOK (check_lpoly_coeffs C I)"
    and check_inter: "isOK (check_inter)"
  shows "\<exists> (S :: ('f, 'v :: showl) trs) NS. ce_af_redtriple_order S NS NS (create_af C I) \<and>
    (\<forall> st \<in> set sts. isOK (check_polo_s C II st) \<longrightarrow> st \<in> S) \<and>
    (\<forall> st \<in> set sts. isOK (check_polo_ns C II st) \<longrightarrow> st \<in> NS) \<and>
    (not_subterm_rel_info NS (Some (map fst I))) \<and>
    (psm \<longrightarrow> (cpx_ce_af_redtriple_order S NS NS (create_af C I) (create_mono_af C I) (\<lambda> cm cc. isOK(convert_lpoly_complexity C II cm cc))) \<and>
      not_subterm_rel_info S (Some (map fst I)) \<and>
      (isOK (check_poly_mono C I) \<longrightarrow>
        mono_ce_af_redtriple_order S NS NS (create_af C I))) \<and>
    (\<not> psm \<and> isOK (check_poly_mono_npsm C (funas_trs_list sts) I) \<longrightarrow>
      mono_ce_af_redtriple_order S NS NS (create_af C I))"
proof -
  let ?as = "[ab. st \<leftarrow> sts, ab \<leftarrow> coeffs_of_constraint C II st]"
  from carrier[OF check_inter, of ?as]
  obtain gt bnd where carrier:
    "lpoly_order (C \<lparr>gt := gt, bound := bnd\<rparr>)"
    and gt: "\<forall> (a,b) \<in> set ?as. a \<in> carrier C \<longrightarrow> b \<in> carrier C \<longrightarrow> a \<succ> b \<longrightarrow> gt a b"
    and mono: "psm \<longrightarrow> complexity_linear_poly_order_carrier (C \<lparr>gt := gt, bound := bnd\<rparr>)" by auto
  let ?C = "C \<lparr>gt := gt, bound := bnd\<rparr>"
  let ?I = "to_lpoly_inter C I"
  let ?II = "to_lpoly_inter ?C I"
  let ?pi = "create_af ?C I"
  let ?mono_af = "create_mono_af ?C I"
  let ?zero = "\<zero>\<^bsub>?C\<^esub>"
  let ?one = "\<one>\<^bsub>?C\<^esub>"
  let ?arcpos = "arc_pos \<^bsub>?C\<^esub>"
  let ?carrier = "carrier ?C"
  let ?ge = "(\<succeq>\<^bsub>?C\<^esub>)"
  interpret lpoly_order ?C by fact
  have C: 
    "?carrier = carrier C"
    "?arcpos = arc_pos" 
    "?ge = (\<succeq>)"
    "?zero = \<zero>"
    "?one = \<one>"
    "create_af C I = ?pi"
    "create_mono_af C I = ?mono_af"
    by auto
  interpret linear_poly_order ?C ?II
  proof
    note [simp] = to_lpoly_inter_def 
    show "wf_lpoly_inter ?II"
    proof (rule conjI, intro allI, unfold C)
      fix fn
      let ?goal = "\<lambda>fn. fst (?II fn) \<in> carrier C \<and> (\<forall>a. a \<in> set (snd (?II fn)) \<longrightarrow> a \<in> carrier C \<and> (a \<succeq> \<zero>))"
      show "?goal fn"
      proof (cases "map_of I fn")
        case None
        then have repl: "?II fn = (default C, replicate (snd fn) \<one>)" by auto
        have "\<forall> x \<in> set (replicate (snd fn) \<one>). x = \<one>" by (induct "snd fn", auto)
        with repl wf_default one_closed one_geq_zero show "?goal fn" by auto
      next
        case (Some aas)
        then have aas: "II fn = aas" by auto
        from Some have "(fn ,aas) \<in> set I" by (rule map_of_SomeD)
        with check_coeffs have "(fst aas) \<in> carrier C \<and> (\<forall> a \<in> set (snd aas). a \<in> carrier C \<and> a \<succeq> \<zero>)"
          by (cases fn, cases aas, auto)
        with aas show "?goal fn" by auto
      qed
    next
      let ?goal2 = "\<lambda> fn. arc_pos (fst (?II fn)) \<or>
        (\<exists>a\<in>set (take (snd fn) (snd (?II fn))). arc_pos a)"
      show "\<forall> fn. ?goal2 fn"
      proof (intro impI allI)
        fix fn
        show "?goal2 fn"
        proof (cases "map_of I fn")
          case None
          then have "?II fn = (default C, replicate (snd fn) \<one>)" by auto
          then show "?goal2 fn" using arc_pos_one arc_pos_default by auto
        next
          case (Some aas)
          then have aas: "?II fn = aas" by auto
          from Some have "(fn, aas) \<in> set I" by (rule map_of_SomeD)
          with check_coeffs have "arc_pos (fst aas) \<or> Bex  (set (take (snd fn) (snd aas))) arc_pos" by (cases fn, cases aas, auto)
          with aas show "?goal2 fn" by auto
        qed
      qed
    qed
  qed
  let ?inter_s = "inter_s :: ('f,'v)trs"
  let ?inter_ns = "inter_ns :: ('f,'v)trs"
  have ws: "not_subterm_rel_info ?inter_ns (Some (map fst I))" 
    unfolding not_subterm_rel_info.simps
  proof (intro allI impI conjI; clarify, intro simple_arg_posI)
    fix f n i and ts :: "('f,'v)term list"
    assume 
      nmem: "(f, n) \<notin> set (map fst I)" 
      and n: "length ts = n"
      and i: "i < n"
    from map_of_eq_None_iff[of I "(f,n)"] nmem
    have "map_of I (f, n) = None" by auto
    then have default: "?II (f,n) = (default C, replicate n \<one>)" by (simp add: to_lpoly_inter_def)
    show "(Fun f ts, ts ! i) \<in> ?inter_ns"
      by (rule default_interpretation_subterm_inter_ns, insert default n i, auto)
  qed
  interpret ce_af_redtriple_order ?inter_s ?inter_ns ?inter_ns ?pi
  proof
    show "ce_compatible inter_ns" 
      by (rule inter_ns_ce_compat, simp)
    show "af_compatible ?pi inter_ns" 
      by (rule inter_ns_af_compat[OF refl])
  qed
  have order: "ce_af_redtriple_order ?inter_s inter_ns inter_ns ?pi" ..
  {
    fix st
    assume st: "st \<in> set sts" and ok: "isOK(check_polo_s C ?I st)"
    have "st \<in> inter_s" 
    proof (rule check_polo_s[of "bound C" "(\<succ>)"], simp add: ok, simp)
      fix a b
      assume mem: "(a,b) \<in> set (coeffs_of_constraint C ?I st)" and ab: "a \<succ> b"
        and a: "a \<in> carrier C" and b: "b \<in> carrier C"
      show "gt a b"
        by (rule gt[rule_format, of "(a,b)", unfolded split, rule_format, OF _ a b ab],
          insert mem st, auto)
    qed
  } note S = this 
  {
    fix st
    assume st: "st \<in> set sts" and ok: "isOK(check_polo_ns C ?I st)"
    have "st \<in> inter_ns" 
      by (rule check_polo_ns[of "bound C" "(\<succ>)"], insert ok, auto)
  } note NS = this
  let ?amono = "\<not> psm \<and> isOK(check_poly_mono_npsm C (funas_trs_list sts) I)"
  show ?thesis
  proof (cases ?amono)
    case False
    then have id: "?amono = False" by simp
    show ?thesis unfolding id C
    proof (intro exI conjI allI ballI,
        rule order,
        (intro impI, rule S, auto)[1],
        (intro impI, rule NS, auto)[1],
        rule ws,
          intro impI, intro conjI)
      assume psm
      from mono \<open>psm\<close> have "complexity_linear_poly_order_carrier ?C" 
        by auto
      interpret complexity_linear_poly_order_carrier ?C by fact
      interpret complexity_linear_poly_order ?C ?II ..
      show "isOK(check_poly_mono C I) \<longrightarrow>
        mono_ce_af_redtriple_order ?inter_s inter_ns inter_ns ?pi"
      proof
        assume ok: "isOK(check_poly_mono C I)"
        interpret mono_linear_poly_order ?C ?II
          by (unfold_locales, rule check_poly_mono_sound,
            insert ok, auto simp: check_poly_mono_def)
        show "mono_ce_af_redtriple_order ?inter_s inter_ns inter_ns ?pi" 
          by (unfold_locales, rule inter_s_mono, rule inter_s_ce_compat[OF refl])
      qed
      let ?conv' = "convert_lpoly_complexity C II  :: ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> showsl check"  
      let ?conv = "convert_lpoly_complexity ?C ?II :: ('f,'v)complexity_measure \<Rightarrow> complexity_class \<Rightarrow> showsl check"  
      show "cpx_ce_af_redtriple_order ?inter_s inter_ns inter_ns ?pi ?mono_af (\<lambda> cm cc. isOK(?conv' cm cc))"
      proof
        fix cm cc
        assume ok: "isOK(?conv' cm cc)"
        obtain deg where cc_deg: "cc = Comp_Poly deg" by (cases cc, auto)
        have "?conv' cm cc = ?conv cm cc" 
          by (auto simp: poly_c_max_inter_bcoeff_def poly_c_max_inter_bcoeff_strict_def Let_def cc_deg)
        with ok have conv: "isOK(?conv cm cc)" by simp
        let ?bcF = "\<lambda> F. poly_c_max_inter_bcoeff ?C F ?II"
        let ?smone = "\<lambda> F. if (\<one> \<succeq> (?bcF F)) then succeed else check_complexity C (?bcF F) deg"
        let ?d1 = "deg - 1"
        from conv cc_deg obtain F D where choice: "cm = Derivational_Complexity F \<or> cm = Runtime_Complexity F D"
          and cc: "isOK(check_complexity ?C (?bcF F) ?d1)" 
          by (auto split: complexity_measure.splits)
        let ?F = "get_signature_of_cm cm"
        let ?bc = "?bcF F"
        let ?bcv = "poly_c_max_inter_bconst ?C F ?II"
        let ?bd = "poly_c_max_inter_bcoeff_strict ?C D ?II"
        let ?bc' = "poly_c_max_inter_bcoeff_strict ?C F ?II"
        from conv cc_deg choice have deg: "?bc' = \<zero> \<or> Suc ?d1 = deg" by auto
        from poly_c_max_inter_bcoeff[of F] have wfbc: "?bc \<in> carrier ?C" and gebc: "?bc \<succeq>\<^bsub>?C\<^esub> \<zero>\<^bsub>?C\<^esub>" by auto
        from poly_c_max_inter_bcoeff_strict[of D] have wfbd: "?bd \<in> carrier ?C" and gebd: "?bd \<succeq>\<^bsub>?C\<^esub> \<zero>\<^bsub>?C\<^esub>" by auto
        from poly_c_max_inter_bconst[of F] have wfbcv: "?bcv \<in> carrier ?C" and gebcv: "?bcv \<succeq>\<^bsub>?C\<^esub> \<zero>\<^bsub>?C\<^esub>" by auto
        from arc_pos_True have apos: "apos_ass zero_ass" unfolding apos_ass_def by simp
        let ?eval = "\<lambda> t :: ('f,'v)term. eval_term ?II zero_ass t"
        let ?S = "{(a,b). a \<in> carrier ?C \<and> b \<in> carrier ?C \<and> b \<succeq> \<zero> \<and> arc_pos b \<and> gt a b}"
        {
          fix s t
          assume "(s,t) \<in> ?inter_s"
          from this[unfolded inter_s_def] 
          have "\<And> \<alpha>. wf_ass ?C \<alpha> \<Longrightarrow> pos_ass \<alpha> \<Longrightarrow> apos_ass \<alpha> \<Longrightarrow> gt (eval_term II \<alpha> s) (eval_term II \<alpha> t)"
            by auto
          from this[OF wf_zero_ass pos_zero_ass apos]
          have gt: "gt (?eval s) (?eval t)" by auto
          from pos_term[OF wf_zero_ass pos_zero_ass] have ge: "(?eval t) \<succeq> \<zero>" by auto
          from apos_term[OF wf_zero_ass apos] have apos: "arc_pos (?eval t)" by auto
          from ge gt apos wf_terms[OF wf_zero_ass]  have "(?eval s,?eval t) \<in> ?S" by (auto simp: Let_def)
        } note image = this
        {
          fix bd
          assume wfbd: "bd \<in> carrier ?C" and gebd: "bd \<succeq>\<^bsub>?C\<^esub> \<zero>\<^bsub>?C\<^esub>"
          have "\<exists> g. g \<in> O_of (Comp_Poly (deg - 1)) \<and> (\<forall> n. bound ?C (bd \<otimes>\<^bsub>?C\<^esub> ( (?bc [^]\<^bsub>?C\<^esub> n) \<otimes>\<^bsub>?C\<^esub> ?bcv)) \<le> g n)"
            by (rule complexity_cond[OF wfbc wfbcv wfbd gebc gebcv gebd cc])
        } note get_g = this
        from choice
        have "\<exists> c d g. g \<in> complexity_of (Comp_Poly ?d1) \<and> (\<forall> n t. t \<in> terms_of_nat cm n \<longrightarrow> bound ?C (?eval t) \<le> c + g n * n * d)"
        proof
          assume cm: "cm = Derivational_Complexity F"
          from get_g[OF one_closed one_geq_zero] obtain g where g: "g \<in> O_of (Comp_Poly ?d1)"
            and bnd2: "\<And> n. bound ?C (\<one> \<otimes> (?bc [^] n \<otimes> ?bcv)) \<le> g n" by auto          
          from g[unfolded O_of_def] obtain gg where gg: "gg \<in> complexity_of (Comp_Poly ?d1)" and ggg: "\<And> n. g n \<le> gg n" by auto
          {
            fix n :: nat
            have "?bc [^] n \<otimes>\<^bsub>?C\<^esub> ?bcv =  \<one> \<otimes> (?bc [^] n \<otimes> ?bcv)"
              using l_one[OF m_closed[OF nat_pow_closed[OF wfbc] wfbcv]] by simp
            moreover from le_trans[OF bnd2[of n] ggg] have "bound ?C (\<one> \<otimes> (?bc [^] n \<otimes> ?bcv)) \<le> gg n" by auto
            ultimately have "bound ?C (?bc [^]\<^bsub>?C\<^esub> n \<otimes>\<^bsub>?C\<^esub> ?bcv) \<le> gg n" by auto
          } note bnd2 = this
          from complexity_poly_mono[OF gg] have gg_mono: "\<And> n m. n \<le> m \<Longrightarrow> gg n \<le> gg m" .          
          from bound_eval_term_max_derivational[of gg, OF gg_mono bnd2]
          have bound2: "\<And> t N. t \<in> terms_of_nat cm N \<Longrightarrow> bound ?C (?eval t) \<le> gg N * N"
            unfolding cm by auto
          show ?thesis
            by (rule exI[of _ 0], rule exI[of _ 1], rule exI, rule conjI[OF gg], insert bound2, auto)
        next
          assume cm: "cm = Runtime_Complexity F D"
          from get_g[OF wfbd gebd] obtain g where g: "g \<in> O_of (Comp_Poly ?d1)"
            and bnd2: "\<And> n. bound ?C (?bd \<otimes> (?bc [^] n \<otimes> ?bcv)) \<le> g n" by auto
          from g[unfolded O_of_def] obtain gg where gg: "gg \<in> complexity_of (Comp_Poly ?d1)" and ggg: "\<And> n. g n \<le> gg n" by auto
          from le_trans[OF bnd2 ggg] have bnd2: "\<And> n. bound ?C (?bd \<otimes>\<^bsub>?C\<^esub> (?bc [^]\<^bsub>?C\<^esub> n \<otimes>\<^bsub>?C\<^esub> ?bcv)) \<le> gg n" by auto
          from complexity_poly_mono[OF gg] have gg_mono: "\<And> n m. n \<le> m \<Longrightarrow> gg n \<le> gg m" .
          let ?bn = "max_list (map snd D)"
          let ?bdv = "poly_c_max_inter_bconst ?C D ?II"
          from bound_eval_term_max_runtime[of gg, OF gg_mono bnd2]
          have bound2: "\<And> t N. t \<in> terms_of_nat cm N \<Longrightarrow> bound ?C (?eval t) \<le> bound ?C ?bdv + gg N * N * ?bn"
            unfolding cm by auto
          show ?thesis
            by (rule exI[of _ "bound ?C ?bdv"], rule exI[of _ ?bn], rule exI, rule conjI[OF gg], insert bound2, auto)
        qed
        then obtain c d g where g: "g \<in> complexity_of (Comp_Poly ?d1)"
          and bound2: "\<And> n t. t \<in> terms_of_nat cm n \<Longrightarrow> bound ?C (?eval t) \<le> c + g n * n * d" by blast
        from g[simplified] obtain c' e where g: "g = (\<lambda> n. c' * n ^ ?d1 + e)" by auto
        obtain c'' where c'': "c'' = c' * d + e * d" by auto
        let ?h = "(\<lambda> n. c'' * n ^ Suc ?d1 + c)"
        obtain h where h: "h = ?h" by auto
        {
          fix n :: nat
          {
            assume n: "1 \<le> n"
            have le: "(e * d) * (n * 1) \<le> (e * d) * (n * n ^ ?d1)"
              by (rule mult_left_mono[OF mult_left_mono[OF one_le_power[OF n]]], auto)
            have "c + g n * n * d = c + (c' * d) * (n ^ Suc ?d1) + (e * d * n)" unfolding g
              by (simp add: field_simps)
            also have "... \<le> h n" unfolding h c'' using le by (simp add: field_simps)
            finally have "c + g n * n * d \<le> h n" .
          } note le = this
          have "c + g n * n * d \<le> h n" using le unfolding h g c'' by (cases n, auto simp: field_simps)
        }
        from le_trans[OF bound2 this] have bound2: "\<And> t n . t \<in> terms_of_nat cm n \<Longrightarrow> bound ?C (?eval t) \<le> h n" .
        (* handle bc = 0 case *)
        from deg have "\<exists> c d. \<forall> t n. t \<in> terms_of_nat cm n \<longrightarrow> bound ?C (?eval t) \<le> c * n ^ deg + d"
        proof
          assume deg: "Suc ?d1 = deg"
          show ?thesis using bound2 unfolding h deg by blast
        next
          assume "?bc' = \<zero>"
          then have 0: "?bc' = ?zero" by simp 
          have "\<exists> c. \<forall> t. t \<in> terms_of cm \<longrightarrow> bound ?C (?eval t) \<le> c"
            using choice
          proof 
            assume "cm = Derivational_Complexity F"
            with bound_eval_term_max_derivational_0[OF 0]
            show ?thesis by blast
          next
            assume "cm = Runtime_Complexity F D"
            with bound_eval_term_max_runtime_0[OF 0]
            show ?thesis by blast
          qed
          then obtain c where bnd: "\<And> t n. t \<in> terms_of_nat cm n \<Longrightarrow> bound ?C (?eval t) \<le> c"
            unfolding terms_of by auto
          show ?thesis
            by (rule exI[of _ 0], rule exI[of _ c], insert bnd, auto)
        qed
        then obtain c d where bound2: "\<And> t n. t \<in> terms_of_nat cm n \<Longrightarrow> bound ?C (?eval t) \<le> c * n ^ deg + d" by auto
        let ?h = "\<lambda> n. c * n ^ deg + d"
        have one: "\<And> t n. \<lbrakk>t \<in> terms_of_nat cm n\<rbrakk>
          \<Longrightarrow> deriv_bound ?inter_s t (?h n)"
          by (rule deriv_bound_image[of _ ?eval, OF deriv_bound_mono[OF bound2 bound]], insert image, auto)
        show deriv_bound: "deriv_bound_measure_class ?inter_s cm cc" unfolding cc
          unfolding deriv_bound_measure_class_def cc_deg
          by (rule deriv_bound_rel_class_polyI[of _ _ c _ d], insert one, auto)
      next
        show "af_monotone ?mono_af ?inter_s"
          by (rule pre_mono_linear_poly_order.create_mono_af[OF _ refl], unfold_locales)
      qed
      show "not_subterm_rel_info ?inter_s (Some (map fst I))" 
        unfolding not_subterm_rel_info.simps
      proof (intro allI impI conjI; clarify, intro simple_arg_posI)
        fix f n i and ts :: "('f,'v)term list"
        assume 
          nmem: "(f, n) \<notin> set (map fst I)" 
          and n: "length ts = n"
          and i: "i < n"
        from map_of_eq_None_iff[of I "(f,n)"] nmem
        have "map_of I (f, n) = None" by auto
        then have default: "?II (f,n) = (default C, replicate n \<one>)" by (simp add: to_lpoly_inter_def)
        show "(Fun f ts, ts ! i) \<in> ?inter_s" 
          by (rule pre_mono_linear_poly_order.default_interpretation_subterm_inter_s, unfold_locales,
            insert default n i, auto)
      qed
    qed simp
  next
    case True
    then have npsm: "isOK(check_poly_mono_npsm C (funas_trs_list sts) I)" and nmono: "\<not> psm" by auto
    from npsm have npsm: "isOK(check_poly_mono_npsm ?C (funas_trs_list sts) I)" 
      unfolding check_poly_mono_npsm_def by auto
    let ?F = "funas_trs (set sts)"
    interpret npsm_mono_linear_poly_order ?C ?II ?F
      by (unfold_locales, insert check_poly_mono_npsm_sound[OF npsm] nmono, auto)
    let ?x = "Var undefined :: ('f,'v)term" 
    define R_ws where "R_ws = ({(Fun f [?x], ?x) | f. (f,1) \<notin> fst ` set I \<and> (f,1) \<in> ?F} :: ('f,'v)trs)" 
    have R_ws: "R_ws \<subseteq> ?inter_ns" unfolding R_ws_def
    proof (clarify)
      fix f
      assume "(f,1) \<notin> fst ` set I"        
      with ws[unfolded not_subterm_rel_info.simps simple_arg_pos_def, rule_format, of "(f,1)" 0 "[?x]"]
      show "(Fun f [?x], ?x) \<in> ?inter_ns" by auto
    qed
    have R_wsF: "funas_trs R_ws \<subseteq> ?F" unfolding R_ws_def funas_trs_def 
      by (auto simp: funas_rule_def)
    obtain R where R: "R = set (filter (\<lambda> st. isOK(check_polo_s C II st)) sts)" by auto
    obtain Rw where Rw: "Rw = R_ws \<union> set (filter (\<lambda> st. isOK(check_polo_ns C II st)) sts)" by auto
    from S R have RS: "R \<subseteq> inter_s" by auto
    from NS Rw R_ws have RwNS: "Rw \<subseteq> inter_ns" by auto
    from R Rw R_wsF have F: "funas_trs R \<subseteq> ?F" "funas_trs Rw \<subseteq> ?F" unfolding funas_trs_def by auto
    let ?Ce = "\<Union>(ce_trs ` UNIV) :: ('f,'v)trs"
    let ?ST = "{(Fun f ts, t) |f ts t. t \<in> set ts \<and> (f, length ts) \<notin> ?F}"
    let ?R = "rstep (R \<union> ?ST)"
    let ?Rw = "rstep (Rw \<union> ?ST)"
    from rel_subterm_terminating[OF F RS RwNS subset_refl] have
      SN_rel: "SN_rel (?R) (?Rw)" .
    let ?S = "(relto (?R) (?Rw))^+"
    let ?NS = "(?R \<union> ?Rw)^*"
    interpret mono_ce_af_redtriple_order ?S ?NS ?NS ?pi
    proof (rule ce_SN_rel_imp_redtriple[OF SN_rel])
      fix f and n :: nat
      show "?pi (f, n) = {0 ..< n}"
      proof (cases "map_of I (f, n)")
        case None
        then show ?thesis unfolding create_af_def by auto
      next
        case (Some ccs)
        then obtain c cs where look: "map_of I (f, n) = Some (c,cs)" by force
        from map_of_SomeD[OF look] have mem: "((f,n),(c,cs)) \<in> set I" by auto
        with check_coeffs have apos: "arc_pos c \<or> Bex (set (take n cs)) arc_pos" 
          and len: "length cs \<le> n" by auto
        from mem have "(f,n) \<in> set (map fst I)" by force
        with check_poly_mono_npsm_sound[OF npsm]
        have mono: "n \<le> Suc 0" "n = Suc 0 \<Longrightarrow> fst (?II (f,n)) = \<zero> \<and> length (snd (?II (f,n))) = Suc 0" by force+
        from look have II: "?II (f,n) = (c,cs)" unfolding to_lpoly_inter_def by auto
        note mono = mono[unfolded II fst_conv snd_conv]
        show ?thesis
        proof (cases n)
          case (Suc n')
          with mono have n: "n = Suc 0" by auto
          from mono(2)[OF this] obtain d where c: "c = \<zero>" and cs: "cs = [d]" by (cases cs, auto)
          from apos[unfolded c n cs] arc_pos_zero[OF mode]
          have ad: "arc_pos d" by auto
          with arc_pos_zero[OF mode] have d: "d \<noteq> \<zero>" by auto
          show ?thesis unfolding create_af_def look cs Let_def ceta_map_of fun_of_map_fun'.simps 
            using d n by auto
        next
          case 0
          then show ?thesis unfolding create_af_def look ceta_map_of fun_of_map_fun'.simps
            using len by auto
        qed
      qed
    qed (insert F_unary, force simp: ce_trs.simps)
    show ?thesis unfolding C
    proof (rule exI[of _ ?S], rule exI[of _ ?NS], intro conjI impI ballI)
      show "ce_af_redtriple_order ?S ?NS ?NS ?pi" ..
    next
      fix st
      assume "st \<in> set sts" and "isOK(check_polo_s C II st)"
      then have "st \<in> ?R" unfolding R by (cases st rule: prod.exhaust) (auto)
      also have "?R \<subseteq> ?S" unfolding relto_trancl_conv by regexp
      finally show "st \<in> ?S" .
    next
      fix st
      assume "st \<in> set sts" and "isOK(check_polo_ns C II st)"
      then have "st \<in> ?Rw" unfolding Rw by (cases st rule: prod.exhaust) (auto)
      also have "?Rw \<subseteq> ?NS" by regexp
      finally show "st \<in> ?NS" .
    next
      show "mono_ce_af_redtriple_order ?S ?NS ?NS ?pi" ..
      show "mono_ce_af_redtriple_order ?S ?NS ?NS ?pi" ..
      show "not_subterm_rel_info ?NS (Some (map fst I))" unfolding not_subterm_rel_info.simps
      proof (intro allI impI)
        fix fn i
        assume nmem: "fn \<notin> set (map fst I)"
        then obtain f n where f: "fn = (f,n)" by force
        show "simple_arg_pos ?NS fn i" unfolding f
        proof (rule simple_arg_posI)
          fix ts :: "('f,'v)term list"
          assume len: "length ts = n" and i: "i < n"
          then have t: "ts ! i \<in> set ts" by auto
          let ?f = "(f,length ts)"
          have "(Fun f ts, ts ! i) \<in> ?Rw"
          proof (cases "?f \<in> ?F")
            case False
            then show ?thesis using t by auto
          next
            case True
            from F_unary[OF this] t have ts: "length ts = 1" by (cases ts, auto)
            with i[folded len] obtain t where ts: "ts = [t]" and i: "i = 0" by (cases ts, auto)
            with True f len nmem have rule: "\<And> R. (Fun f [?x], ?x) \<in> Rw \<union> R" 
              unfolding Rw R_ws_def by auto
            show ?thesis unfolding ts i
              by (rule rstepI[OF rule, of _ Hole "\<lambda> _. t"], auto)
          qed
          then show "(Fun f ts, ts ! i) \<in> ?NS" by regexp
        qed
      qed
    qed (insert nmono, auto)
  qed
qed
end

context
  fixes C :: "('a :: showl)lpoly_order_semiring" (structure)
begin

definition create_lpoly_repr :: "('f::{compare_order,showl},'a::showl)lpoly_interL \<Rightarrow> showsl"
where "create_lpoly_repr I = (let pi = to_lpoly_inter C I in  (
  showsl (STR ''polynomial interpretation over '') \<circ> description C \<circ> showsl_nl \<circ> (showsl_sep (\<lambda>(f,n).
    let t = Fun f (map Var (fresh_strings_list ''x_'' 1 [] n)) in (
      showsl (STR ''Pol('') \<circ> showsl t \<circ> showsl (STR '') = '') \<circ>
      showsl_lpoly C (PleftI C pi t)
    )) showsl_nl (remdups (map fst I)))))"

definition create_poly_rel_impl :: "showsl check \<Rightarrow> ('f :: {showl,compare_order}, 'a :: showl)lpoly_interL \<Rightarrow> ('f,'v :: showl)rel_impl"
where "create_poly_rel_impl cI I = (let pi = to_lpoly_inter C I; ns = check_polo_ns C pi in
    \<lparr>rel_impl.valid = do {cI; check_lpoly_coeffs C I},
     standard = succeed,
     desc = create_lpoly_repr I,
     s = check_polo_s C pi,
     ns = ns, nst = ns,
     af = create_af C I,
     top_af = create_af C I,
     SN = succeed,
     subst_s = succeed,
     ce_compat = succeed,
     co_rewr = succeed,
     top_mono = succeed,
     top_refl = succeed,
     mono_af = create_mono_af C I,
     mono = (\<lambda> sig. if psm then check_poly_mono C I else check_poly_mono_npsm C sig I),
     not_wst = Some (map fst I), 
     not_sst = if psm then Some (map fst I) else None, 
     cpx = (if psm then convert_lpoly_complexity C pi else no_complexity_check) \<rparr>)"

lemma create_poly_rel_impl:
  assumes "linear_poly_order_impl C check_inter"
  shows "rel_impl (create_poly_rel_impl check_inter I :: ('f :: {compare_order,showl},'v :: showl)rel_impl)"
  unfolding rel_impl_def
proof (intro impI allI, goal_cases)
  case (1 U)
  let ?c = "create_poly_rel_impl check_inter I :: ('f,'v)rel_impl"
  let ?pi = "rel_impl.af ?c :: 'f af"
  let ?mono_af = "rel_impl.mono_af ?c :: 'f af"
  note valid = 1(1)
  from valid have carrier_valid: "isOK (check_inter)" 
    and polo_valid: "isOK(check_lpoly_coeffs C I)" 
    and top_af: "rel_impl.top_af ?c = ?pi" unfolding create_poly_rel_impl_def by (auto simp: Let_def)
  let ?I = "to_lpoly_inter C I :: ('f,'a)lpoly_inter"
  let ?cpx = "rel_impl.cpx ?c"
  let ?cpx' = "\<lambda> cm cc. isOK(rel_impl.cpx ?c cm cc)"
  interpret linear_poly_order_impl C check_inter by fact
  from linear_poly_order[of I U, OF polo_valid carrier_valid] obtain S NS cpx where order: "ce_af_redtriple_order S NS NS ?pi"
    and S: "(\<forall> st \<in> set U. isOK(check_polo_s C ?I st) \<longrightarrow> st \<in> S)"
    and NS: "(\<forall> st \<in> set U. isOK(check_polo_ns C ?I st) \<longrightarrow> st \<in> NS)"
    and cpx: "psm \<Longrightarrow> cpx_ce_af_redtriple_order S NS NS ?pi ?mono_af (\<lambda> cm cc. isOK(convert_lpoly_complexity C ?I cm cc))"
    and ws: "not_subterm_rel_info NS (Some (map fst I))" 
    and sst: "psm \<Longrightarrow> not_subterm_rel_info S (Some (map fst I))" 
    and mono: "psm \<Longrightarrow> isOK(check_poly_mono C I) \<Longrightarrow> mono_ce_af_redtriple_order S NS NS ?pi"
    and nmono: "\<not> psm \<Longrightarrow> isOK(check_poly_mono_npsm C (funas_trs_list U) I) \<Longrightarrow> mono_ce_af_redtriple_order S NS NS ?pi" 
    unfolding create_poly_rel_impl_def Let_def rel_impl.simps by blast
  interpret ce_af_redtriple_order S NS NS ?pi by fact
  have order: "cpx_ce_af_redtriple_order S NS NS ?pi ?mono_af ?cpx'"
  proof (cases psm)
    case True
    show ?thesis using cpx[OF True] True
      unfolding create_poly_rel_impl_def Let_def by simp
  next
    case False
    then have id: "?cpx = no_complexity_check" "?mono_af = empty_af" unfolding create_poly_rel_impl_def Let_def 
      by (auto simp: create_mono_af_def)
    show ?thesis unfolding id 
      by (unfold_locales, force simp: no_complexity_check_def, rule empty_af)
  qed
  let ?ws = "rel_impl.not_wst ?c"
  let ?sst = "rel_impl.not_sst ?c"
  have ws: "not_subterm_rel_info NS ?ws" using ws
    by (auto simp: create_poly_rel_impl_def Let_def)
  have sst: "not_subterm_rel_info S ?sst" using sst
    by (cases psm, auto simp: create_poly_rel_impl_def Let_def)
  show ?case unfolding top_af
  proof (rule exI[of _ S], intro exI[of _ NS] conjI impI allI 
      ws sst SN compat_S_NS compat_NS_S af_compat subst_S subst_NS ctxt_NS S_imp_NS NS_ce_compat 
      trans_NS refl_NS top_mono_same trans_S)
    show "irrefl S" using SN irrefl_on_def by fastforce
    from co_rewrite_irrefl[OF this compat_NS_S] show "NS \<inter> S^-1 = {}" .    
    interpret cpx_ce_af_redtriple_order S NS NS ?pi ?mono_af ?cpx' by fact
    show "af_monotone ?mono_af S" by (rule \<mu>)
    show "isOK (rel_impl.cpx (local.create_poly_rel_impl check_inter I) cm cc) \<Longrightarrow> deriv_bound_measure_class S cm cc" for cm cc
      by (rule cpx_class)
    {
      fix sig
      assume "isOK (rel_impl.mono ?c sig)" and sub: "funas_trs (set U) \<subseteq> set sig" 
      hence ok: "isOK (rel_impl.mono ?c (funas_trs_list U))" using check_poly_mono_npsm_mono[of C sig _ "funas_trs_list U"] 
        by (auto simp: create_poly_rel_impl_def Let_def)
      note ok = ok[unfolded create_poly_rel_impl_def Let_def, simplified]
      have "mono_ce_af_redtriple_order S NS NS ?pi"
      proof (cases psm)
        case True
        with ok have "isOK (check_poly_mono C I)" by simp
        from mono[OF True this] show ?thesis .
      next
        case False
        with ok have "isOK(check_poly_mono_npsm C (funas_trs_list U) I)"
          by simp
        from nmono[OF False this] show ?thesis .
      qed
      then interpret mono_ce_af_redtriple_order S NS NS ?pi .
      show "ctxt.closed S" by (rule ctxt_S)
      show "ce_compatible S" by (rule S_ce_compat)
    }
  qed (insert S NS, auto simp: create_poly_rel_impl_def Let_def)
qed
end

context lpoly_order
begin
declare poly_simps[simp del] poly_order_simps[simp del]
end

no_notation arcpos ("arc'_pos\<index>")

end
