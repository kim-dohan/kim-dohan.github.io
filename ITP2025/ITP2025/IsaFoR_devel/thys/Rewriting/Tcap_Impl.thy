(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Tcap_Impl
imports
  Tcap
  Ground_Context_Impl
  First_Order_Rewriting.Trs_Impl
begin

no_notation Subterm_and_Context.Hole ("\<box>")
notation GCHole ("\<box>")
notation Ground_Context.equiv_class ("[_]")

section \<open>tcap\<close>

(* an executable version of tcap *)
fun tcapI :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt" where
  "tcapI _ (Var _) = \<box>"
| "tcapI R (Fun f ts) = (
    let h = GCFun f (map (tcapI R) ts) in
    if \<exists>r\<in>set R. Ground_Context.match h (fst r)
      then \<box>
      else h)"

(* and a version for the reversed TRS *)
fun tcapR :: "('f, 'v) rules \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt" where
  "tcapR _ (Var _) = \<box>"
| "tcapR R (Fun f ts) = (
    let h = GCFun f (map (tcapR R) ts) in
    if \<exists>r\<in>set R. Ground_Context.match h (snd r)
      then \<box>
      else h)"


(* and a version with rule maps *)
fun tcapRM2 :: "('f \<times> nat \<Rightarrow> ('f, 'v) rules) \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) gctxt" where
  "tcapRM2 _ (Var _) = \<box>"
| "tcapRM2 rm (Fun f ts) = (
    let h = GCFun f (map (tcapRM2 rm) ts); n = length ts in
    if \<exists>r\<in>set (rm (f, n)). Ground_Context.match h (fst r)
      then \<box>
      else h)"

lemma tcapRM2_sound:
  fixes t :: "('f, 'v) term"
  assumes noLeftVars: "\<And>lr. lr \<in> set R \<Longrightarrow> is_Fun (fst lr)"
    and rm: "\<And>f n. set (rm (f, n)) = {(l, r). (l, r) \<in> set R \<and> root l = Some (f, n)}"
  shows "tcapRM2 rm t = tcap (set R) t"
proof (induct t)
  case (Fun f ts)
  let ?hArgs = "(map (tcap (set R)) ts) :: ('f, 'v) gctxt list"
  let ?hIArgs = "(map (tcapRM2 rm) ts) :: ('f, 'v) gctxt list "
  let ?h = "GCFun f ?hArgs"
  let ?hI = "GCFun f ?hIArgs"
  from Fun have heq: "?hI = ?h" by simp
  then have hArgsEq: "?hIArgs = ?hArgs" by simp
  let ?EQ = "\<lambda>(h1::('f, 'v) gctxt) (h2::('f, 'v) gctxt) n.
    (\<exists>r\<in>set R. Ground_Context.match h1 (fst r)) = (\<exists>r\<in>set (rm (f, n)). Ground_Context.match h2 (fst r))"
  have "\<And>h1 h2. h1 = h2 \<Longrightarrow> ?EQ (GCFun f h1) (GCFun f h2) (length h2)"
  proof -
    fix h1 h2 :: "('f, 'v) gctxt list"
    assume h12: "h1 = h2"
    let ?mat = "\<lambda>r. Ground_Context.match (GCFun f h2) (fst r)"
    have "(\<exists>r\<in>set (rm (f, length h2)). ?mat r) = (\<exists>r\<in>set (rm (f, length h2)). ?mat r)" by simp
    also have "\<dots> = (\<exists>r\<in>set R. ?mat r)"
    proof
      assume "\<exists>r\<in>set (rm (f, length h2)). ?mat r"
      from this obtain r where "r \<in> set (rm (f, length h2)) \<and> ?mat r" by auto
      with rm have "r \<in> set R \<and> ?mat r" by auto
      then show "\<exists>r\<in>set R. ?mat r" by auto
    next
      assume "\<exists>r\<in>set R. ?mat r"
      from this obtain r where A: "r \<in> set R \<and> ?mat r" by auto
      with noLeftVars[of r] obtain g ts' rhs where B: "r = (Fun g ts', rhs)" by (cases r, cases "fst r", auto)
      from A B have "f = g \<and> length ts' = length h2" by (cases "f=g", auto simp: Ground_Context.match_def)
      with A B rm have "(Fun f ts', rhs) \<in> set (rm (f, length h2)) \<and> ?mat (Fun f ts', rhs)" by simp
      then show "\<exists>r\<in>set (rm (f, length h2)). ?mat r" by blast
    qed
    then show "?EQ (GCFun f h1) (GCFun f h2) (length h2)" by (simp add: h12)
  qed
  from this[OF hArgsEq[symmetric]] have a: "?EQ ?h ?hI (length ts)" by auto
  then show ?case by (force simp: Let_def heq)
qed simp

definition
  tcapRM :: "bool \<Rightarrow> (('f \<times> nat) \<Rightarrow> ('f, 'v) rules) \<Rightarrow> ('f, 'v) term  \<Rightarrow> ('f, 'v) gctxt"
where
  "tcapRM nlv rm = (if nlv then tcapRM2 rm else (\<lambda>t. \<box>))"

lemma tcapRM: 
  assumes nlv: "nlv = (\<forall>lr\<in>set R. is_Fun (fst lr))"
    and rm: "\<And>f n. set (rm (f, n)) = {(l, r). (l, r) \<in> set R \<and> root l = Some (f, n)}"
  shows "tcapRM nlv rm = tcap (set R)"
proof
  fix t
  show "tcapRM nlv rm t = tcap (set R) t"
  proof (cases nlv)    
    case True
    then have "tcapRM nlv rm t = tcapRM2 rm t" by (auto simp: tcapRM_def)
    also have "... = tcap (set R) t"
      by (rule tcapRM2_sound, insert True[unfolded nlv] rm, auto)      
    finally show ?thesis .
  next
    case False
    then have "tcapRM nlv rm t = \<box>" by (auto simp: tcapRM_def)
    also have "... = tcap (set R) t"
      by (rule tcap_lhs_var[symmetric], insert False[unfolded nlv], auto)
    finally show ?thesis .
  qed  
qed


lemma tcapI_sound[simp]:
  fixes R :: "('f,'v) rule list"   
  shows "tcapI R = tcap (set R)"
proof 
  fix t
  show "tcapI R t = tcap (set R) t"
  proof (induct t)
    case (Var x) then show ?case by simp
  next
    case (Fun f ts)
    let ?h = "GCFun f (map (tcap (set R)) ts) :: ('f,'v) gctxt"
    let ?hI = "GCFun f (map (tcapI R) ts) :: ('f,'v) gctxt"
    from Fun have heq: "?hI = ?h" by simp
    let ?EQ = "\<lambda>(h1 :: ('f,'v) gctxt) (h2 :: ('f,'v) gctxt) . ((\<exists> r \<in> set R. Ground_Context.match h1 (fst r)) = (Bex (set R) (\<lambda> r. Ground_Context.match h2 (fst r)) ))"
    have "!! h1 h2 . h1 = h2 \<Longrightarrow> ?EQ h1 h2 "
    proof -
      fix h1 h2 :: "('f,'v)gctxt" 
      show "h1 = h2 \<Longrightarrow> ?EQ h1 h2" by (induct R, auto)
    qed
    then have "?h = ?hI \<Longrightarrow> ?EQ ?h ?hI" .
    with heq have a: "?EQ ?h ?hI" by simp
    show ?case using if_weak_cong[OF a, where x = "GCHole" and y = "GCFun f (map (tcap (set R)) ts)",symmetric] unfolding tcapI.simps tcap.simps Let_def heq by force
  qed
qed

lemma tcapR_sound[simp]:   fixes R :: "('f,'v) rule list"
  shows "tcapR R = tcap ((set R)^-1)"
proof 
  fix t
  let ?swap = "\<lambda> lr. (snd lr, fst lr)"
  have id: "set (map ?swap R) = (set R)^-1" by (induct R, auto)
  have "tcapR R t = tcapI (map ?swap R) t"
  proof (induct t)
    case (Fun f ss)
    from Fun have id: "map (tcapR R) ss = map (tcapI (map ?swap R)) ss" by auto
    show ?case by (simp add: Let_def id)
  qed simp
  also have "... = tcap ((set R)^-1) t" unfolding tcapI_sound id ..
  finally show "tcapR R t = tcap ((set R)^-1) t" .
qed

abbreviation
  tcap_below_impl :: "('f, 'v) rules \<Rightarrow> 'f \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) gctxt"
where
  "tcap_below_impl R f ts \<equiv> GCFun f (map (tcapI R) ts)"

fun match_tcap_below_impl :: "('f, 'v) term \<Rightarrow> ('f, 'v) rules \<Rightarrow> ('f, 'v) term \<Rightarrow> bool"
where
  "match_tcap_below_impl l R (Fun f ts) = Ground_Context.match (tcap_below_impl R f ts) l"
| "match_tcap_below_impl l R (Var x) = False"

lemma match_tcap_below_impl [simp]:
  "match_tcap_below_impl l R = match_tcap_below l (set R)"
by (intro ext, case_tac x, auto)

lemma gctxts_unifiable_code [code]:
  "Ground_Context.unifiable s t \<longleftrightarrow> Ground_Context_Impl.merge s t \<noteq> None"
by (auto simp: Ground_Context.unifiable_def)

no_notation Ground_Context.GCHole ("\<box>")
no_notation Ground_Context.equiv_class ("[_]")
notation Subterm_and_Context.Hole ("\<box>")

end
