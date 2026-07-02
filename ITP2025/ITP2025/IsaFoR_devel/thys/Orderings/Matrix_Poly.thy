(*
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2015)
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Matrix_Poly
imports 
  "Abstract-Rewriting.SN_Order_Carrier"
  Jordan_Normal_Form.Matrix_Complexity
  Show.Show_Instances
  Linear_Poly_Order
  Jordan_Normal_Form_Complexity_Approximation
  Poly_Order
  Jordan_Normal_Form.Shows_Literal_Matrix
begin

subsection \<open>Standard linear polynomial interpretations\<close>

text \<open>We can take standard linear polynomials using +, *, ... from type class
as carrier operations.\<close>

definition class_complexity :: "'a :: ordered_semiring_1 \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "class_complexity a deg = (check (a \<le> 1) (showsl (STR ''value is larger than 1'')))"

definition
  class_lpoly_order ::
    "'a :: ordered_semiring_1 \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      'a lpoly_order_semiring"
where
  "class_lpoly_order def cmon gtt = class_ordered_semiring (TYPE('a)) gtt \<lparr> 
    plus_single_mono = True,
    default = def,
    arcpos = (\<lambda> _. True),
    checkmono = cmon,
    bound = (\<lambda> _. 0), \<comment> \<open>does not matter, will be overwritten\<close>
    check_complexity = class_complexity,
    description = showsl (STR ''polynomial interpretation'')
  \<rparr>"

(* TODO: show is required here, since weak_complexity_linear_poly_order_carrier in AFP requires show *)
lemma class_lpoly_order:
  fixes d :: "'a :: {showl, show, large_real_ordered_semiring_1}"
    and check_carrier :: "showsl check"
  assumes check_carrier: "isOK check_carrier \<Longrightarrow> weak_complexity_linear_poly_order_carrier weak_gt d cmon"
  shows "linear_poly_order_impl (class_lpoly_order d cmon (weak_gt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)) (check_carrier)"
proof
  note class_mono = times_left_mono times_right_mono
  fix I :: "('f, 'a) lpoly_interL" and as :: "('a \<times> 'a) list"
  assume check: "isOK check_carrier"
  interpret weak_complexity_linear_poly_order_carrier weak_gt d cmon by (rule check_carrier[OF check])
  let ?as = "filter (\<lambda> (a, b). weak_gt a b) as :: ('a \<times> 'a) list"
  have "\<forall> m1 m2. (m1, m2) \<in> set ?as \<longrightarrow> weak_gt m1 m2" by auto
  from weak_gt_mono[of ?as, OF this] obtain gt bnd
    where mono: "mono_matrix_carrier gt d bnd cmon" and
     weak_gt: "\<And> m1 m2. (m1, m2) \<in> set ?as \<Longrightarrow> gt m1 m2" by auto 
  interpret mono_matrix_carrier gt d bnd cmon by fact
  let ?gt = gt
  let ?bnd = bnd
  let ?mono = cmon
  note d = class_lpoly_order_def class_ordered_semiring_def class_semiring_def
  let ?D = "class_lpoly_order d cmon weak_gt"
  let ?C = "?D\<lparr>gt := ?gt, bound := ?bnd\<rparr>"
  from class_ordered_semiring[of "\<lparr>
     plus_single_mono = True,
     default = d,
     arcpos = (\<lambda> _. True),
     checkmono = ?mono,
     bound = ?bnd,
     check_complexity = class_complexity,
     description = _\<rparr>"]
  interpret ordered_semiring ?C 
    unfolding d by simp
  interpret lpoly_order ?C
    by (unfold_locales, unfold d, auto intro: 
      SN default_ge_zero plus_gt_left_mono plus_gt_both_mono) 
  have lpoly_order: "lpoly_order ?C" ..
  show "\<exists>gta bnd.
               lpoly_order (?D\<lparr>gt := gta, bound := bnd\<rparr>) \<and>
               (\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> gta a b) \<and>
               (psm\<^bsub>?D\<^esub> \<longrightarrow> complexity_linear_poly_order_carrier (?D\<lparr>gt := gta, bound := bnd\<rparr>))"
  proof (intro exI conjI impI, rule lpoly_order)
    show "\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> ?gt a b" using weak_gt unfolding d by auto
    {
      fix bc bcv bd :: 'a and deg
      assume bc0: "bc \<ge> 0" and bcv0: "bcv \<ge> 0" and bd0: "bd \<ge> 0"
        and comp: "isOK(class_complexity bc deg)"
      from comp[unfolded class_complexity_def]
      have bc1: "bc \<le> 1" by (auto split: if_splits)
      let ?b = "bnd (bcv * bd)"
      let ?g = "\<lambda> _ :: nat. ?b"
      have mono: "\<And> g. g \<in> O_of (Comp_Poly 0) \<Longrightarrow> g \<in> O_of (Comp_Poly deg)"
        using O_of_poly_mono_deg[of 0 deg] by auto
      have "\<exists>g. g \<in> O_of (Comp_Poly deg) \<and>
           (\<forall>n. bnd (bcv * (bd * bc [^]\<^bsub>?C\<^esub> n)) \<le> g n)"      
      proof (intro exI[of _ ?g] conjI allI, rule mono, rule O_of_polyI[of _ 0 _ ?b], simp)
        fix n :: nat
        have id: "bc [^]\<^bsub>?C\<^esub> n = bc ^ n"
          by (induct n, unfold nat_pow_0 nat_pow_Suc, auto simp: field_simps d)
        have "\<dots> \<le> 1"
        proof (induct n)
          case 0
          show ?case by (simp add: ge_refl)
        next
          case (Suc n)
          from ge_trans[OF class_mono(2)[OF one_ge_zero bc1] class_mono(1)[OF bc0 Suc]]
          show ?case by (simp add: field_simps)
        qed
        from class_mono(2)[OF _ this, of "bcv * bd"]
        have "bcv * (bd * bc ^ n) \<le> bcv * bd" using bcv0 bd0 by (auto simp: field_simps)
        from bound_mono[OF this]
        show "bnd (bcv * (bd * bc [^]\<^bsub>?C\<^esub> n)) \<le> ?b" unfolding id .
      qed
    } note main = this
    show "complexity_linear_poly_order_carrier ?C"
      by (unfold_locales, insert main, unfold d, auto simp: field_simps intro: bound_mono bound_plus default_gt_zero bound mono)
  qed
qed

subsection \<open>Arctic linear polynomial interpretations\<close>

text \<open>We can take arctic operations from type class as carrier operations.\<close>

definition class_arc_complexity :: "'a \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "class_arc_complexity a deg = error (showsl (STR ''complexity for arctic semirings not supported''))"

definition
  class_arc_lpoly_order ::
    "'a :: ordered_semiring_1 \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      'a lpoly_order_semiring"
where
  "class_arc_lpoly_order def apos gtt = class_ordered_semiring (TYPE('a)) gtt \<lparr> 
    plus_single_mono = False,
    default = def,
    arcpos = apos,
    checkmono = (\<lambda> _. False),
    bound = (\<lambda> _. 0), 
    check_complexity = class_arc_complexity,
    description = showsl_lit (STR ''polynomial interpretation over arctic semiring'')
  \<rparr>"

lemma class_arc_lpoly_order:
  fixes d :: "'a :: {showl, ordered_semiring_1}"
  assumes "weak_SN_both_mono_ordered_semiring_1 weak_gt d arc_pos"
  shows "linear_poly_order_impl (class_arc_lpoly_order d arc_pos (weak_gt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)) check_carrier"
proof
  fix I :: "('f, 'a) lpoly_interL" and as :: "('a \<times> 'a) list"
  interpret weak_SN_both_mono_ordered_semiring_1 weak_gt d arc_pos by fact
  let ?as = "filter (\<lambda> (a, b). weak_gt a b) as :: ('a \<times> 'a) list"
  have "\<forall> m1 m2. (m1, m2) \<in> set ?as \<longrightarrow> weak_gt m1 m2" by auto
  from weak_gt_both_mono[of ?as, OF this] obtain gt
    where mono: "SN_both_mono_ordered_semiring_1 d gt arc_pos" and
     weak_gt: "\<And> m1 m2. (m1, m2) \<in> set ?as \<Longrightarrow> gt m1 m2" by auto 
  interpret SN_both_mono_ordered_semiring_1 d gt arc_pos by fact
  note [simp] = gt_imp_ge[OF zero_leastI]
  let ?gt = gt
  let ?bnd = "\<lambda> _ :: 'a. 0"
  let ?mono = "\<lambda> _. False"
  note d = class_arc_lpoly_order_def class_ordered_semiring_def class_semiring_def
  let ?D = "class_arc_lpoly_order d arc_pos weak_gt"
  let ?C = "?D\<lparr>gt := ?gt, bound := ?bnd\<rparr>"
  from class_ordered_semiring[of "\<lparr>
     plus_single_mono = False,
     default = d,
     arcpos = arc_pos,
     checkmono = ?mono,
     bound = ?bnd,
     check_complexity = class_arc_complexity,
     description = _\<rparr>"]
  interpret ordered_semiring ?C 
    unfolding d by simp
  interpret lpoly_order ?C
    by (unfold_locales, unfold d, insert SN not_all_ge, auto simp: arc_pos_zero max0_id intro: 
      default_ge_zero plus_gt_both_mono arc_pos_one arc_pos_default
      arc_pos_plus arc_pos_mult not_all_ge zero_leastI zero_leastII zero_leastIII
      times_gt_left_mono times_gt_right_mono) 
  have lpoly_order: "lpoly_order ?C" ..
  show "\<exists>gta bnd.
               lpoly_order (?D\<lparr>gt := gta, bound := bnd\<rparr>) \<and>
               (\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> gta a b) \<and>
               (psm\<^bsub>?D\<^esub> \<longrightarrow> complexity_linear_poly_order_carrier (?D\<lparr>gt := gta, bound := bnd\<rparr>))"
  proof (intro exI conjI impI, rule lpoly_order)
    show "\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> ?gt a b" using weak_gt unfolding d by auto
  qed (auto simp: d)
qed

subsection \<open>Matrix interpretations\<close>

text \<open>We can take standard matrix operations as carrier operations.\<close>

definition mat_complexity :: "nat \<Rightarrow> 'a :: large_real_ordered_semiring_1 mat \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "mat_complexity n M d \<equiv> mat_estimate_complexity_jb (Suc d) M"

definition
  mat_lpoly_order ::
    "nat \<Rightarrow> nat \<Rightarrow> 'a :: large_real_ordered_semiring_1 \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow>
      ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      ('a mat) lpoly_order_semiring"
where
  "mat_lpoly_order n sd def cmon gtt = mat_ordered_semiring n sd gtt \<lparr> 
    plus_single_mono = True,
    default = mat_default def n,
    arcpos = (\<lambda> _. True),
    checkmono = mat_mono cmon sd,
    bound = (\<lambda> _. 0), \<comment> \<open>does not matter, will be overwritten\<close>
    check_complexity = mat_complexity n,
    description = showsl_lit (STR ''matrix interpretation'')
  \<rparr>"                   

definition check_dimensions :: "nat \<Rightarrow> nat \<Rightarrow> showsl check \<Rightarrow> showsl check"
where
  "check_dimensions n sd c = do {
    c;
    check (sd \<le> n \<and> sd > 0)
      (showsl (STR ''strict dimension must be at least 1 and less than total dimension''))
  }"


lemma mat_lpoly_order:
  fixes d :: "'a :: {showl, show, large_real_ordered_semiring_1}"
    and check_carrier :: "showsl check"
  assumes check_carrier: "isOK (check_carrier) \<Longrightarrow> weak_complexity_linear_poly_order_carrier weak_gt d cmon"
  shows "linear_poly_order_impl (mat_lpoly_order n sd d cmon (weak_gt :: 'a \<Rightarrow> 'a \<Rightarrow> bool)) (check_dimensions n sd check_carrier)"
proof
  fix I :: "('f, 'a mat) lpoly_interL" and as :: "('a mat \<times> 'a mat) list"
  assume check: "isOK (check_dimensions n sd check_carrier)"
  note check = check[unfolded check_dimensions_def, simplified]
  from check have sd_n: "sd \<le> n" and sd_pos: "sd > 0" and check: "isOK(check_carrier)" by auto
  interpret weak_complexity_linear_poly_order_carrier weak_gt d cmon by (rule check_carrier[OF check])
  let ?as = "filter (\<lambda> (a,b). weak_mat_gt sd a b) as :: ('a mat \<times> 'a mat) list"
  have "\<And>m1 m2.
      m1 \<in> carrier_mat n n \<Longrightarrow> m2 \<in> carrier_mat n n \<Longrightarrow> (m1, m2) \<in> set ?as \<Longrightarrow>
      weak_mat_gt sd m1 m2" by auto
  from weak_mat_gt_mono[OF sd_n, of ?as, OF this] obtain gt bnd
    where mono: "mono_matrix_carrier gt d bnd cmon" and
     weak_gt: "\<And> m1 m2. m1 \<in> carrier_mat n n \<Longrightarrow> m2 \<in> carrier_mat n n \<Longrightarrow> (m1, m2) \<in> set ?as \<Longrightarrow>
              mat_gt gt sd m1 m2" by blast
  interpret mono_matrix_carrier gt d bnd cmon by fact
  let ?gt = "mat_gt gt sd"
  let ?bnd = "\<lambda> m :: 'a mat. bnd (sum_mat m)"
  let ?mono = "mat_mono cmon sd"
  note d = mat_lpoly_order_def mat_ordered_semiring_def ring_mat_def
  let ?D = "mat_lpoly_order n sd d cmon weak_gt"
  let ?C = "?D\<lparr>gt := ?gt, bound := ?bnd\<rparr>"
  from mat_ordered_semiring[OF sd_n, of "\<lparr>
     plus_single_mono = True,
     default = default\<^sub>m d n,
     arcpos = (\<lambda> _. True),
     checkmono = ?mono,
     bound = ?bnd,
     check_complexity = mat_complexity n,
     description = _\<rparr>"]
  interpret ordered_semiring ?C 
    unfolding d by simp
  interpret lpoly_order ?C
    by (unfold_locales, unfold d, insert mat_gt_SN[OF sd_n], 
      auto intro: mat_default_ge_0
      mat_plus_gt_left_mono[OF sd_n]
      mat_gt_ge_mono[OF sd_n])  
  have lpoly_order: "lpoly_order ?C" ..
  show "\<exists>gta bnd.
               lpoly_order (?D\<lparr>gt := gta, bound := bnd\<rparr>) \<and>
               (\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> gta a b) \<and>
               (psm\<^bsub>?D\<^esub> \<longrightarrow> complexity_linear_poly_order_carrier (?D\<lparr>gt := gta, bound := bnd\<rparr>))"
  proof (intro exI conjI impI, rule lpoly_order)
    show "\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> ?gt a b" using weak_gt unfolding d by auto
  next
    {
      fix bc bcv bd :: "'a mat" and deg
      assume bc: "bc \<in> carrier_mat n n" and bcv: "bcv \<in> carrier_mat n n" and bd: "bd \<in> carrier_mat n n"
        and bc0: "bc \<ge>\<^sub>m 0\<^sub>m n n" and bcv0: "bcv \<ge>\<^sub>m 0\<^sub>m n n" and bd0: "bd \<ge>\<^sub>m 0\<^sub>m n n"
        and comp: "isOK(mat_complexity n bc deg)"
      let ?b = "\<lambda> nn. bnd (sum_mat (bd * ((bc ^\<^sub>m nn) * bcv)))"
      from comp[unfolded mat_complexity_def]
      have ok: "isOK(mat_estimate_complexity_jb (Suc deg) bc)" by auto
      from mat_estimate_complexity_jb_sum_mat_prod[OF ok bc bd bcv refl] obtain c where
        bnd: "\<And> k. k > 0 \<Longrightarrow> sum_mat (bd * (bc ^\<^sub>m k * bcv)) \<le> c * of_nat k ^ deg" by auto
      {
        fix k
        assume "k > (0 :: nat)"
        from bound_mono[OF bnd[OF this]] have "?b k \<le> bnd (c * of_nat k ^ deg)" by auto
        also have "\<dots> \<le> bnd c * of_nat k ^ deg"
          by (rule bound_pow_of_nat)
        finally have "?b k \<le> bnd c * of_nat k ^ deg" .
      }
      then obtain c where main: "\<And> k. k > 0 \<Longrightarrow> ?b k \<le> c * k ^ deg" by auto
      let ?gp = "\<lambda> nn. c * nn ^ deg"
      let ?g = "\<lambda> nn. ?gp nn + ?b 0"
      {
        fix n
        have "?b n \<le> ?g n"
        proof (cases n)
          case (Suc m)
          then have "n > 0" by simp
          from main[OF this] show ?thesis by simp
        qed auto
      }
      then have main: "\<forall> nn. ?b nn \<le> ?g nn" by auto
      have deg: "?g \<in> O_of (Comp_Poly deg)" 
        by (rule O_of_polyI[of _ c _ "?b 0"], simp)
      have "\<exists>g. g \<in> O_of (Comp_Poly deg) \<and>
           (\<forall>na. bnd (sum_mat (bd * (bc [^]\<^bsub>?C\<^esub> na * bcv))) \<le> g na)"
        by (intro exI conjI, rule deg, insert main,
        unfold pow_mat_ring_pow[OF bc, of _ ?C], 
        unfold d nat_pow_def, auto)
    } note main1 = this
    {
      fix m :: "'a mat"
      let ?m = "\<lambda> x. (x :: 'a mat) \<in> carrier_mat n n"
      let ?R = "{(x,y). ?m x \<and> ?m y \<and> y \<ge>\<^sub>m 0\<^sub>m n n \<and> mat_gt gt sd x y}"
      let ?f = "\<lambda> m. sum_mat m"
      let ?fR = "{(x,y). y \<ge> 0 \<and> gt x y}"
      {
        fix x y
        assume "(x,y) \<in> ?R"
        then have x: "?m x" and y: "?m y" and ge: "y \<ge>\<^sub>m 0\<^sub>m n n" and gt: "mat_gt gt sd x y" by auto
        from sum_mat_mono_gt[OF sd_n x y gt] sum_mat_mono[OF y _ ge]        
        have "(?f x, ?f y) \<in> ?fR" by simp
      } note step = this
      have "deriv_bound ?R m (?bnd m)" 
        by (rule deriv_bound_image[of _ sum_mat, OF bound], insert step, auto)
    } note main2 = this
    show "complexity_linear_poly_order_carrier ?C"
      by (unfold_locales, insert main1 main2, unfold d, auto simp: sum_mat_add
        intro: 
        mat_default_gt_mat0[OF sd_pos sd_n] mat_mono[OF sd_n] 
        bound_plus bound_mono[OF sum_mat_mono])    
  qed
qed


subsection \<open>Arctic matrix interpretations\<close>

text \<open>We can take arctic matrix operations as carrier operations.\<close>

definition mat_arc_complexity :: "'a \<Rightarrow> nat \<Rightarrow> showsl check"
where
  "mat_arc_complexity m deg = error (showsl_lit (STR ''complexity for arctic matrices not supported''))"

definition
  mat_arc_lpoly_order ::
    "nat \<Rightarrow> 'a :: ordered_semiring_1 \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> ('a :: ordered_semiring_1 \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow>
      ('a mat) lpoly_order_semiring"
where
  "mat_arc_lpoly_order n def apos gtt = mat_both_ordered_semiring n gtt \<lparr>
    plus_single_mono = False,
    default = mat_default def n,
    arcpos = mat_arc_posI apos,
    checkmono = (\<lambda> _. False),
    bound = (\<lambda> _. 0),
    check_complexity = mat_arc_complexity,
    description = showsl_lit (STR ''arctic matrix interpretation'')
  \<rparr>"

definition "check_arc_dimension n = check (n > 0) (showsl_lit (STR ''dimension must be at least 1''))"

lemma mat_arc_lpoly_order:
  fixes default :: "'a :: {showl, show, ordered_semiring_1}"
  assumes "weak_SN_both_mono_ordered_semiring_1 weak_gt default arc_pos"
  shows "linear_poly_order_impl (mat_arc_lpoly_order n default arc_pos weak_gt) (check_arc_dimension n)"
proof
  fix as :: "('a mat \<times> 'a mat) list"
  assume check: "isOK (check_arc_dimension n)"
  note check = check[unfolded check_arc_dimension_def, simplified]
  from check have n_pos: "n > 0" by simp
  interpret weak_SN_both_mono_ordered_semiring_1 weak_gt default arc_pos by fact
  let ?as = "filter (\<lambda> (A,B). A \<in> carrier_mat n n \<and> B \<in> carrier_mat n n \<and> weak_mat_gt_arc A B) as"
  have AB': "set ?as \<subseteq> carrier_mat n n \<times> carrier_mat n n" by auto
  have "\<forall>(A,B) \<in> set ?as. weak_mat_gt_arc A B" by auto
  from weak_mat_gt_both_mono[OF AB']
  obtain gt
    where mono: "SN_both_mono_ordered_semiring_1 default gt arc_pos"
    and weak_gt: "\<forall>(A,B) \<in> set ?as. mat_comp_all gt A B" by auto
  interpret SN_both_mono_ordered_semiring_1 default gt arc_pos by fact
  let ?gt = "mat_comp_all gt"
  let ?bnd = "\<lambda> m. 0"
  note d = mat_arc_lpoly_order_def  
    mat_both_ordered_semiring_def ring_mat_def lpoly_order_semiring.simps
    partial_object.simps ordered_semiring.simps
  let ?D = "mat_arc_lpoly_order n default arc_pos weak_gt"
  let ?C = "?D\<lparr>gt := ?gt, bound := ?bnd\<rparr>"
  from mat_both_ordered_semiring[OF n_pos, of "\<lparr>
     plus_single_mono = False,
     default = mat_default default n,
     arcpos = mat_arc_pos,
     checkmono = (\<lambda> _. False),
     bound = ?bnd,
     check_complexity = mat_arc_complexity,
     description = _\<rparr>"]
  interpret ordered_semiring ?C 
    unfolding d by (simp add: mat_ordered_semiring_def ring_mat_def)
  {
    fix m :: "'a mat"
    assume m: "m \<in> carrier_mat n n"
    note mat_max_id[OF mat0_leastIII[OF this] this zero_carrier_mat]
  } note mat_max[simp] = this
  interpret lpoly_order ?C
    by (unfold_locales, unfold d, 
    auto simp: mat_arc_pos_zero[OF n_pos] mat_max_0_id
    intro: mat_gt_arc_plus_mono mat_gt_arc_mult_left_mono
    mat_gt_arc_mult_right_mono mat0_leastI mat0_leastII
    SN_subset[OF mat_gt_arc_SN[OF n_pos]] mat_default_ge_0
    mat_arc_pos_plus[OF n_pos] mat_arc_pos_mult[OF n_pos]
    mat_arc_pos_mat_default[OF n_pos] mat_arc_pos_one[OF n_pos]
    mat_not_all_ge[OF n_pos])
  have lpoly_order: "lpoly_order ?C" ..
  show "\<exists>gta bnd.
               lpoly_order (?D\<lparr>gt := gta, bound := bnd\<rparr>) \<and>
               (\<forall>(a, b)\<in>set as. a \<in> carrier ?D \<longrightarrow> b \<in> carrier ?D \<longrightarrow>
                   a \<succ>\<^bsub>?D\<^esub> b \<longrightarrow> gta a b) \<and>
               (psm\<^bsub>?D\<^esub> \<longrightarrow> complexity_linear_poly_order_carrier (?D\<lparr>gt := gta, bound := bnd\<rparr>))"
    apply (intro exI conjI impI ballI2)
    apply (rule lpoly_order)
    unfolding d using weak_gt by auto
qed

abbreviation int_mat_rel_impl where
  "int_mat_rel_impl n sd \<equiv>
    create_poly_rel_impl (mat_lpoly_order n sd 1 int_mono (\<lambda>x y. y < x))
      (check_dimensions n sd succeed)"

abbreviation int_rel_impl where
  "int_rel_impl \<equiv> 
    create_poly_rel_impl (class_lpoly_order 1 int_mono (\<lambda>x y. y < x))
      succeed"

lemma int_mat_rel_impl:
  "rel_impl (int_mat_rel_impl n sd I)"
  by (rule create_poly_rel_impl[OF mat_lpoly_order[OF int_weak_complexity]])

lemma int_rel_impl:
  "rel_impl (int_rel_impl I)"
  by (rule create_poly_rel_impl[OF class_lpoly_order[OF int_weak_complexity]])

\<comment> \<open>TODO: show required, since show required via mono_matrix_carrier in AFP\<close>
lemma delta_cpx_poly_order_carrier:
  fixes d :: "'a :: {show, large_real_ordered_semiring_1, floor_ceiling}"
  assumes d: "d > 0"
  shows "cpx_poly_order_carrier d (delta_gt d) (1 \<le> d) False (delta_bound d)"
proof -
  let ?nat = "delta_bound d"
  from delta_complexity[OF d] have "mono_matrix_carrier (delta_gt d) d ?nat delta_mono" by simp
  interpret mono_matrix_carrier "delta_gt d" d ?nat delta_mono by fact
  from delta_poly[OF d] have "poly_order_carrier d (delta_gt d) (1 \<le> d) False" by simp
  interpret poly_order_carrier d "delta_gt d" "1 \<le> d" False by fact
  show ?thesis ..
qed

lemma delta_non_inf_poly_order_carrier:
  fixes d :: "'a :: {show, large_real_ordered_semiring_1, floor_ceiling}"
  assumes d: "d > 0"
  shows "non_inf_poly_order_carrier d (delta_gt d) (1 \<le> d) False"
proof -
  interpret cpx_poly_order_carrier d "delta_gt d" "1 \<le> d" False "delta_bound d"
    by (rule delta_cpx_poly_order_carrier[OF d])
  show ?thesis
    by (unfold_locales, insert non_inf_delta_gt[OF d], auto simp: mult_right_mono_neg delta_gt_def)
qed

definition "check_def_pos d = check (d > 0) (showsl_lit (STR ''default value must be positive''))"

lemma delta_weak_complexity:
  assumes d0: "isOK(check_def_pos def)" 
  shows "weak_complexity_linear_poly_order_carrier (>) def delta_mono"
  by (rule delta_weak_complexity_carrier, insert d0, auto simp: check_def_pos_def)

abbreviation delta_mat_rel_impl where
  "delta_mat_rel_impl n sd d \<equiv> 
    create_poly_rel_impl (mat_lpoly_order n sd d delta_mono (>))
      (check_dimensions n sd (check_def_pos d))"

abbreviation delta_rel_impl where
  "delta_rel_impl d \<equiv> 
    create_poly_rel_impl (class_lpoly_order d delta_mono (>))
      (check_def_pos d)"

abbreviation delta_nl_rel_impl where
  "delta_nl_rel_impl d \<equiv> 
    create_nlpoly_rel_impl (check_def_pos d) d (delta_gt d) (1 \<le> d) False"

abbreviation delta_non_inf_order where
  "delta_non_inf_order d s \<equiv>
    create_nlpoly_non_inf_order (check_def_pos d) d (delta_gt d) (1 \<le> d) False s"

context
  fixes d :: "'a :: {floor_ceiling,large_real_ordered_semiring_1,show,showl}"
begin

lemma delta_non_inf_order: "generic_non_inf_order_impl (delta_non_inf_order d s)"
  by (rule non_inf_poly_order_carrier_to_generic_non_inf_order[OF delta_non_inf_poly_order_carrier],
    simp add: check_def_pos_def)
end

section \<open>The arctic integers and rationals can be used as carrier\<close>

(* TODO: move *)
instantiation arctic :: showl
begin
fun showsl_arctic where
  "showsl_arctic MinInfty = showsl_lit (STR ''-infinity'')"
| "showsl_arctic (Num_arc i) = showsl i" 
definition "showsl_list (xs :: arctic list) = default_showsl_list showsl xs"
instance ..
end

instantiation arctic_delta :: (showl) showl
begin
fun showsl_arctic_delta where
  "showsl_arctic_delta MinInfty_delta = showsl_lit (STR ''-infinity'')"
| "showsl_arctic_delta (Num_arc_delta x) = showsl x" 
definition "showsl_list (xs :: 'a arctic_delta list) = default_showsl_list showsl xs"
instance ..
end

abbreviation arctic_mat_rel_impl where
  "arctic_mat_rel_impl n \<equiv> 
    create_poly_rel_impl (mat_arc_lpoly_order n 1 pos_arctic (>))
      (check_arc_dimension n)"

abbreviation arctic_delta_mat_rel_impl where
  "arctic_delta_mat_rel_impl n \<equiv> 
    create_poly_rel_impl (mat_arc_lpoly_order n 1 pos_arctic_delta weak_gt_arctic_delta)
      (check_arc_dimension n) :: (_,'a :: {floor_ceiling,showl,show} arctic_delta mat)lpoly_interL \<Rightarrow> (_, _) rel_impl"

abbreviation arctic_rel_impl where
  "arctic_rel_impl \<equiv> 
    create_poly_rel_impl (class_arc_lpoly_order 1 pos_arctic (>))
      succeed"

abbreviation arctic_delta_rel_impl where
  "arctic_delta_rel_impl \<equiv> 
    create_poly_rel_impl (class_arc_lpoly_order 1 pos_arctic_delta weak_gt_arctic_delta)
      succeed"

end
