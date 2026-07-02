(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Semantic_Labeling
imports 
  TRS.Q_Restricted_Rewriting
  TRS.DP_Transformation
begin

type_synonym  ('v, 'c) assign = "'v \<Rightarrow> 'c"
type_synonym  ('f, 'c) inter = "'f \<Rightarrow> 'c list \<Rightarrow> 'c"
type_synonym  ('f, 'l) labels = "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> bool" 
type_synonym  ('f, 'c, 'l) label = "'f \<Rightarrow> 'c list \<Rightarrow> 'l"
type_synonym  ('f, 'l, 'lf) lcompose = "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'lf"
type_synonym  ('lf, 'f, 'l) ldecompose = "'lf \<Rightarrow> ('f \<times> 'l)"

fun eval_lab :: "('f,'c)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'l,'lf)lcompose \<Rightarrow> ('v,'c)assign \<Rightarrow> ('f,'v)term \<Rightarrow> ('c \<times> ('lf,'v)term)" 
where "eval_lab I L LC \<alpha> (Var x) = (\<alpha> x, Var x)"
  |   "eval_lab I L LC \<alpha> (Fun f ts) = 
     (let clts = map (eval_lab I L LC \<alpha>) ts;
          cs = map fst clts;
          c = I f cs;
          lts = map snd clts in     
     (c, Fun (LC f (length ts) (L f cs)) lts))"

fun lab_root :: "('f,'c)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'l,'lf)lcompose \<Rightarrow> ('v,'c)assign \<Rightarrow> ('f,'v)term \<Rightarrow> ('lf,'v)term" 
where "lab_root I L L' LC \<alpha> (Fun f ts) = 
     (let clts = map (eval_lab I L LC \<alpha>) ts;
          cs = map fst clts;
          lts = map snd clts in     
     (Fun (LC f (length ts) (L' f cs)) lts))"
  | "lab_root _ _ _ _ _ (Var x) = (Var x)"

fun lab_root_all :: "('f,'c)inter \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'c,'l)label \<Rightarrow> ('f,'l,'lf)lcompose \<Rightarrow> ('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('v,'c)assign \<Rightarrow> ('f,'v)term \<Rightarrow> ('lf,'v)terms" 
where "lab_root_all I L L' LC lge \<alpha> (Fun f ts) = 
     (let clts = map (eval_lab I L LC \<alpha>) ts;
          cs = map fst clts;
          lts = map snd clts;
          l   = L' f cs in     
     {(Fun (LC f (length ts) ls) lts) | ls. lge f (length ts) l ls})"
  | "lab_root_all _ _ _ _ _ _ (Var x) = {(Var x)}"

abbreviation eval where "eval I L LC \<alpha> t \<equiv> fst (eval_lab I L LC \<alpha> t)"
abbreviation lab where "lab I L LC \<alpha> t \<equiv> snd (eval_lab I L LC \<alpha> t)"
definition wf_assign where "wf_assign C \<alpha> \<equiv> \<forall> x. \<alpha> x \<in> C"
definition lab_rule where "lab_rule I L LC C lr \<equiv> {(lab I L LC \<alpha> (fst lr), lab I L LC \<alpha> (snd lr)) | \<alpha> . wf_assign C \<alpha>}"
definition lab_lhs where "lab_lhs I L LC C l \<equiv> {lab I L LC \<alpha> l | \<alpha> . wf_assign C \<alpha>}"
definition lab_root_rule where "lab_root_rule I L L' LC C lr \<equiv> {(lab_root I L L' LC \<alpha> (fst lr), lab_root I L L' LC \<alpha> (snd lr)) | \<alpha> . wf_assign C \<alpha>}"
definition lab_root_all_rule where "lab_root_all_rule I L L' LC lge C rule \<equiv> {(lab_root I L L' LC \<alpha> (fst rule), lr) | \<alpha> lr. wf_assign C \<alpha> \<and> lr \<in> lab_root_all I L L' LC lge \<alpha> (snd rule)}"
abbreviation lab_trs where "lab_trs I L LC C R \<equiv> \<Union>(lab_rule I L LC C ` R)"
abbreviation lab_lhss where "lab_lhss I L LC C Q \<equiv> \<Union>(lab_lhs I L LC C ` Q)"
abbreviation lab_lhss_all where "lab_lhss_all LD Q \<equiv> { lt. map_funs_term (\<lambda> fl. fst (LD fl)) lt \<in> Q}"
abbreviation lab_root_trs where "lab_root_trs I L L' LC C R \<equiv> \<Union>(lab_root_rule I L L' LC C ` R)"
abbreviation lab_root_all_trs where "lab_root_all_trs I L L' LC lge C R \<equiv> \<Union>(lab_root_all_rule I L L' LC lge C ` R)"
definition wf_inter where "wf_inter I C \<equiv> \<forall> f cs. set cs \<subseteq> C \<longrightarrow> I f cs \<in> C"
definition wf_label where "wf_label L LS C \<equiv> \<forall> f cs. set cs \<subseteq> C \<longrightarrow> LS f (length cs) (L f cs)"
abbreviation qmodel_rule where "qmodel_rule I L LC C cge l r \<equiv> \<forall> \<alpha>. wf_assign C \<alpha> \<longrightarrow> cge (eval I L LC \<alpha> l) (eval I L LC \<alpha> r)"
definition qmodel where "qmodel I L LC C cge R \<equiv> \<forall> (l,r) \<in> R. qmodel_rule I L LC C cge l r"
definition cge_wm: "cge_wm I C cge \<equiv> \<forall> f bef c d aft. (set ([c,d] @ bef @ aft) \<subseteq> C \<and> cge c d \<longrightarrow> cge (I f (bef @ c # aft)) (I f (bef @ d # aft)))"
definition lge_wm: "lge_wm I L C cge lge \<equiv> \<forall> f bef c d aft. (set ([c,d] @ bef @ aft) \<subseteq> C \<and> cge c d \<longrightarrow> lge f (Suc (length bef + length aft)) (L f (bef @ c # aft)) (L f (bef @ d # aft)))"



definition
  decr_of_ord :: "('f \<Rightarrow> nat \<Rightarrow> 'l rel) \<Rightarrow> ('f,'l,'lf)lcompose \<Rightarrow> ('f,'l)labels \<Rightarrow> ('lf, 'v) trs"
where
  "decr_of_ord gr LC LS \<equiv> {(Fun (LC f (length ts) l) ts, Fun (LC f (length ts) l') ts) | f l l' ts. LS f (length ts) l \<and> LS f (length ts) l' \<and> (l,l') \<in> gr f (length ts)}"

definition lge_to_lgr :: "('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('f,'l)labels \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool" 
  where "lge_to_lgr lge LS f n \<equiv> let LSfn = LS f n; lgefn = lge f n in (\<lambda> l l'. l \<noteq> l' \<and> LSfn l \<and> LSfn l' \<and> lgefn l l')"
definition lge_to_lgr_rel :: "('f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool) \<Rightarrow> ('f,'l)labels \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'l rel"
  where "lge_to_lgr_rel lge LS f n \<equiv> {(l,l')| l l'. lge_to_lgr lge LS f n l l'}"

locale sl_interpr = 
  fixes C :: "'c set"
  and  c :: "'c"
  and  I :: "('f,'c)inter"
  and  cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and  lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and  L :: "('f,'c,'l)label"
  and  LC :: "('f,'l,'lf)lcompose"
  and  LD :: "('lf,'f,'l)ldecompose"
  and  LS :: "('f,'l)labels" 
  assumes c: "c \<in> C"
  and wf_I: "wf_inter I C" 
  and wf_L: "wf_label L LS C" 
  and wm_cge: "cge_wm I C cge"
  and wm_lge: "lge_wm I L C cge lge"
  and gr_SN: "\<And> f n. SN (lge_to_lgr_rel lge LS f n)"
  and LD_LC: "\<And> f n l. LD (LC f n l) = (f,l)"
  and lge_trans: "\<And> f n x y z. \<lbrakk>lge f n x y; lge f n y z\<rbrakk> \<Longrightarrow> lge f n x z"

locale sl_interpr_root = sl_interpr C c I cge lge L LC LD LS
  for C c I cge lge L and LC :: "('f,'l,'lf)lcompose" and LD LS +
  fixes 
       L' :: "('f,'c,'l)label"
  and  LS' :: "('f,'l)labels" 
  assumes
      wf_L': "wf_label L' LS' C" 
  and wm_lge': "lge_wm I L' C cge lge"
  and lge_refl: "\<And> f n x. LS' f n x \<Longrightarrow> lge f n x x"
  and gr'_SN: "\<And> f n. SN (lge_to_lgr_rel lge (\<lambda> f n x. LS f n x \<or> LS' f n x) f n)"


context sl_interpr
begin
abbreviation gr where "gr \<equiv> lge_to_lgr_rel lge LS"
abbreviation Eval where "Eval \<equiv> eval I L LC"
abbreviation Lab where "Lab \<equiv> lab I L LC"
abbreviation Lab_trs :: "('f,'v)trs \<Rightarrow> ('lf,'v)trs" where "Lab_trs \<equiv> lab_trs I L LC C"
abbreviation Lab_lhss :: "('f,'v)terms \<Rightarrow> ('lf,'v)terms" where "Lab_lhss \<equiv> lab_lhss I L LC C"
abbreviation Lab_lhss_all :: "('f,'v)terms \<Rightarrow> ('lf,'v)terms" where "Lab_lhss_all \<equiv> lab_lhss_all LD"
abbreviation wf_ass where "wf_ass \<equiv> wf_assign C"
definition subst_ass where "subst_ass \<alpha> \<sigma> \<equiv> \<lambda> x. Eval \<alpha> (\<sigma> x)"
definition lab_subst where "lab_subst \<alpha> \<sigma> \<equiv> (\<lambda>x. Lab \<alpha> (\<sigma> x))"
abbreviation Decr :: "('lf,'v)trs" where "Decr \<equiv> decr_of_ord gr LC LS"
definition default_ass where "default_ass x = c"
abbreviation LAB where "LAB t \<equiv> Lab default_ass t"
abbreviation UNLAB where "UNLAB fl \<equiv> fst (LD fl)"
end

context sl_interpr_root
begin
abbreviation LS_both where "LS_both \<equiv> (\<lambda> f n x. LS f n x \<or> LS' f n x)"
abbreviation gr_root where "gr_root \<equiv> lge_to_lgr_rel lge LS'"
abbreviation gr_both where "gr_both \<equiv> lge_to_lgr_rel lge LS_both"
abbreviation Lab_root where "Lab_root \<equiv> lab_root I L L' LC"
abbreviation Lab_root_all where "Lab_root_all \<equiv> lab_root_all I L L' LC lge"
abbreviation Lab_root_trs :: "('f,'v)trs \<Rightarrow> ('lf,'v)trs" where "Lab_root_trs \<equiv> lab_root_trs I L L' LC C"
abbreviation Lab_root_all_trs :: "('f,'v)trs \<Rightarrow> ('lf,'v)trs" where "Lab_root_all_trs \<equiv> lab_root_all_trs I L L' LC lge C"
abbreviation Decr_root :: "('lf,'v)trs" where "Decr_root \<equiv> decr_of_ord gr_root LC LS'"
abbreviation Decr_both :: "('lf,'v)trs" where "Decr_both \<equiv> decr_of_ord gr_both LC LS_both"
abbreviation LAB_root where "LAB_root t \<equiv> Lab_root default_ass t"
end

context sl_interpr
begin

lemma Decr_SN_generic: assumes grSN: "\<And> f n. SN (lge_to_lgr_rel lge LSg f n)"
  shows "SN (rstep (decr_of_ord (lge_to_lgr_rel lge LSg) LC LSg))" (is "SN (rstep ?Decr)")
proof -
  let ?gr = "lge_to_lgr_rel lge LSg"
  let ?id = "id :: 'lf \<Rightarrow> 'lf"
  let ?nfs = "False"
  let ?m = "False"
  show ?thesis 
  proof(rule ccontr)
    assume nSN: "\<not> ?thesis"
    then have nSN: "\<not> SN (qrstep ?nfs {} ?Decr)" by auto
    have wf_trs: "wf_trs ?Decr" unfolding decr_of_ord_def wf_trs_def by auto
    then have wf_trs: "wf_qtrs ?nfs {} ?Decr" unfolding wf_qtrs_def wwf_qtrs_def wf_trs_def by auto
    from not_SN_imp_ichain[OF this nSN]
    obtain s t \<sigma> where ichain: "ichain (initial_dpp ?id ?nfs ?m {} ?Decr) s t \<sigma>" by blast
    note ichain = ichain[unfolded initial_dpp.simps applicable_rules_empty]
    have DP: "DP ?id ?Decr \<subseteq> {(Fun ((LC f (length ts) l)) ts, Fun ((LC f (length ts) l')) ts) | f l l' (ts :: ('lf,'a)term list). (l,l') \<in> ?gr f (length ts)}" (is "_ \<subseteq> ?DP")
    proof -
      {
        fix f l l' ts h and us :: "('lf,'a) term list"
        assume gr: "(l,l') \<in> ?gr f (length ts)" and right: "Fun (LC f (length ts) l') ts \<unrhd> Fun h us" and left: "\<not> (Fun (LC f (length ts) l) ts \<rhd> Fun h us)"
        let ?n = "length ts"
        have "(sharp_term id (Fun (LC f ?n l) ts), sharp_term id (Fun h us)) \<in> ?DP" 
        proof (cases "Fun h us = Fun (LC f ?n l') ts")
          case True
          with gr show ?thesis by auto
        next
          case False
          with right have "Fun (LC f ?n l') ts \<rhd> Fun h us" by auto
          then have "Fun (LC f ?n l) ts \<rhd> Fun h us"
          proof (cases, (auto)[1])          
            case (subt s)
            then show ?thesis ..
          qed
          with left show ?thesis by blast
        qed
      }
      then show ?thesis unfolding DP_on_def decr_of_ord_def by blast
    qed
    from ichain DP have DP: "\<And> i. (s i, t i) \<in> ?DP" by (simp add: ichain.simps) blast
    obtain l where l: "l = (\<lambda> t :: ('lf,'a)term. case t of Fun lf _ \<Rightarrow> snd (LD lf))" by auto
    obtain n where n: "n = (\<lambda> i. num_args (s i))" by auto
    obtain f where f: "f = (\<lambda> i. case (s i) of Fun lf _ \<Rightarrow> fst (LD lf))" by auto
    {
      fix i :: nat
      from DP[of i] obtain fi li li' usi where si: "s i = Fun ((LC fi (length usi) li')) usi" and ti: "t i = Fun ((LC fi (length usi) li)) usi" by blast
      let ?n = "length usi"
      from DP[of i] obtain f' ll l' where "LC fi (length usi) li' = LC f' (length usi) l' \<and> LC fi (length usi) li = LC f' (length usi) ll \<and> (l', ll) \<in> ?gr f' (length usi)" unfolding si ti by auto
      then have id: "LD (LC fi (length usi) li') = LD (LC f' (length usi) l') \<and> LD (LC fi (length usi) li) = LD (LC f' (length usi) ll)" and gr: "(l', ll) \<in> ?gr f' (length usi)" by auto
      from id[unfolded LD_LC] gr have labels: "(li',li) \<in> ?gr fi ?n"  by simp
      have lti: "l (t i) = li" unfolding l ti using LD_LC by simp
      have lsi: "l (s i) = li'" unfolding l si using LD_LC by simp
      from ichain have "(t i \<cdot> \<sigma> i, s (Suc i) \<cdot> (\<sigma> (Suc i))) \<in> (rstep ?Decr)^*" by (simp add: ichain.simps)
      then have steps: "(Fun ((LC fi ?n li)) (map (\<lambda> u. u \<cdot> \<sigma> i) usi), s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (rstep ?Decr)^*" unfolding ti by simp
      have nvar: "\<forall> lr \<in> ?Decr. \<forall> x. fst lr \<noteq> Var x" unfolding decr_of_ord_def map_funs_trs.simps by auto
      obtain t where t: "s (Suc i) \<cdot> \<sigma> (Suc i) = t" by auto
      obtain ts where ts: "map (\<lambda> u. u \<cdot> \<sigma> i) usi = ts" and lts: "length usi = length ts" by auto
      from steps have "\<exists> ssi li'. s (Suc i) \<cdot> \<sigma> (Suc i) = Fun ((LC fi ?n li')) ssi \<and> length ssi = ?n \<and> (li,li') \<in> (?gr fi ?n)^*" 
        unfolding t ts lts 
      proof (induct)
        case base
        show ?case by auto
      next
        case (step u s)
        from step(3) obtain vs li' where u: "u = Fun (LC fi (length ts) li') vs" and len: "length vs = length ts" and li': "(li,li') \<in> (?gr fi (length ts))^*" by auto
        from step(2) obtain C l r \<sigma> where ul: "u = C\<langle>l \<cdot> \<sigma>\<rangle>" and sr: "s = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> ?Decr" by auto
        show ?case
        proof (cases C)
          case (More g bef D aft)
          let ?ts = "(bef @ D\<langle>r\<cdot>\<sigma>\<rangle> # aft)"
          from u[unfolded ul] len have "s = Fun (LC fi (length ts) li') ?ts" and "length ?ts = length ts" unfolding sr More by auto
          with li' show ?thesis by auto
        next
          case Hole
          then have ul: "u = l \<cdot> \<sigma>" and sr: "s = r \<cdot> \<sigma>" using ul sr by auto
          from lr[unfolded decr_of_ord_def] obtain f l1 l2 ls where l: "l = Fun (LC f (length ls) l1) ls" and r: "r = Fun (LC f (length ls) l2) ls" and l1l2: "(l1,l2) \<in> ?gr f (length ls)"
            by auto
          from ul[unfolded u l] len have len: "length ls = length ts" and f: "LC fi (length ts) li' = LC f (length ts) l1" (is "?l = ?l1") by auto
          then have "LD ?l = LD ?l1" by auto
          from this[unfolded LD_LC] have f: "f = fi" and l1: "l1 = li'" by auto           
          from li' l1l2[unfolded len f l1] have "(li,l2) \<in> (?gr fi (length ts))^*" by auto
          with sr[unfolded r f len] len show ?thesis by auto
        qed
      qed
      then obtain ssi li'' where "s (Suc i) \<cdot> \<sigma> (Suc i) = Fun ((LC fi ?n li'')) ssi" and "length ssi = ?n" and li'': "(li,li'') \<in> (?gr fi ?n)^*" by auto
      with DP[of "Suc i"] obtain ssi where ssi: "s (Suc i) = Fun ((LC fi ?n li'')) ssi" and len: "length ssi = ?n" by auto
      have lssi: "l (s (Suc i)) = li''" unfolding l ssi using LD_LC by simp
      from labels li'' have "(l (s i), l (s (Suc i))) \<in> (?gr (f i) (n i))^+" and "n (Suc i) = n i" and "f (Suc i) = f i" unfolding lsi lssi lti n f
        unfolding si ssi by (auto simp: len LD_LC)
    } note main = this
    {
      fix i
      have "n i = n 0 \<and> f i = f 0"
        by (induct i, auto simp: main)
      with main(1)[of i] have "(l (s i), l (s (Suc i))) \<in> (?gr (f 0) (n 0))^+" by simp
    }
    with SN_imp_SN_trancl[OF grSN[of "f 0" "n 0"]] show False unfolding SN_defs by force
  qed
qed

lemma Decr_SN: "SN (rstep Decr)"
  by (rule Decr_SN_generic, rule gr_SN)

lemma wf_default_ass: "wf_ass default_ass" 
  unfolding default_ass_def wf_assign_def using c by auto

lemma eval_subst[simp] :
  "Eval \<alpha> (t \<cdot> \<sigma>) = Eval (subst_ass \<alpha> \<sigma>) t"
proof (induct t, simp add: subst_ass_def)
  case (Fun f ts)
  let ?beta = "subst_ass \<alpha> \<sigma>"
  have evalInd: "map (\<lambda> x. Eval \<alpha> (x \<cdot> \<sigma>)) ts = map (Eval ?beta) ts" using Fun  by auto
  have "Eval \<alpha> (Fun f ts \<cdot> \<sigma>) = Eval \<alpha> (Fun f (map (\<lambda> t. t \<cdot> \<sigma>) ts))" by simp
  also have "\<dots> = Eval ?beta (Fun f ts)" by (simp add: Let_def o_def evalInd)
  finally show ?case .
qed

lemma lab_subst[simp] :
  "Lab \<alpha> (t \<cdot> \<sigma>) = Lab (subst_ass \<alpha> \<sigma>) t \<cdot> lab_subst \<alpha> \<sigma>"
  by (induct t, simp add: lab_subst_def, simp add: Let_def o_def)
end

context sl_interpr_root
begin

lemma Decr_both: "Decr \<union> Decr_root \<subseteq> Decr_both"
proof -
  {
    fix l r f n
    assume "(l,r) \<in> gr f n"
    then have "(l,r) \<in> gr_both f n" unfolding lge_to_lgr_rel_def lge_to_lgr_def
      by (auto simp: Let_def)
  } note subset = this
  {
    fix l r f n
    assume "(l,r) \<in> gr_root f n"
    then have "(l,r) \<in> gr_both f n" unfolding lge_to_lgr_rel_def lge_to_lgr_def
      by (auto simp: Let_def)
  } note subset_root = this
  show "Decr \<union> Decr_root \<subseteq> Decr_both" (is "?DD \<subseteq> _")   
  proof 
    fix s t
    assume "(s,t) \<in> ?DD"    
    then show "(s,t) \<in> Decr_both"
    proof
      assume "(s,t) \<in> Decr"
      then show ?thesis unfolding decr_of_ord_def using subset by blast
    next
      assume "(s,t) \<in> Decr_root"
      then show ?thesis unfolding decr_of_ord_def using subset_root by blast
    qed
  qed
qed

lemma Decr_SN_both: "SN (rstep Decr_both)"
  by (rule Decr_SN_generic[OF gr'_SN] )

lemma Decr_SN_both_2: "SN (rstep (Decr \<union> Decr_root))"
  by (rule SN_subset[OF Decr_SN_both rstep_mono[OF Decr_both]])

lemma lab_root_subst[simp]:    
  "is_Fun t \<Longrightarrow> Lab_root \<alpha> (t \<cdot> \<sigma>) = Lab_root (subst_ass \<alpha> \<sigma>) t \<cdot> lab_subst \<alpha> \<sigma>"
  by (cases t, auto simp add: o_def)
end

context sl_interpr
begin
lemma wf_term[simp]: assumes "wf_ass \<alpha>"
  shows "Eval \<alpha> t \<in> C"
proof (induct t)
  case (Var x)
  with assms show ?case by (auto simp: wf_assign_def)
next
  case (Fun f ts)
  let ?cs = "map (Eval \<alpha>) ts"
  let ?c = "I f ?cs"
  from Fun have "set ?cs \<subseteq> C" by auto
  with wf_I have "?c \<in> C" unfolding wf_inter_def by (best)
  then show ?case by (simp add: Let_def o_def)
qed

lemma wf_ass_subst_ass[simp]: assumes "wf_ass \<alpha>"
  shows "wf_ass (subst_ass \<alpha> \<sigma>)"
using assms unfolding subst_ass_def by (simp add: wf_assign_def)

lemma quasi_sem_rewrite: assumes step: "(s,t) \<in> qrstep nfs Q R"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  shows "cge (Eval \<alpha> s) (Eval \<alpha> t)"
using step
proof
  fix l r C' \<sigma> assume in_R: "(l, r) \<in> R" and s: "s = C'\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C'\<langle>r\<cdot>\<sigma>\<rangle>"
  let ?beta = "subst_ass \<alpha> \<sigma>"
  have wfbeta: "wf_ass ?beta" using wfass by auto
  have "Eval \<alpha> (l\<cdot>\<sigma>) = Eval ?beta l" by simp
  also have "cge \<dots> (Eval ?beta r)" using in_R wfbeta qmodel by (auto simp: qmodel_def)
  also have "\<dots> = Eval \<alpha> (r\<cdot>\<sigma>)" by simp
  finally have root: "cge (Eval \<alpha> (l\<cdot>\<sigma>)) (Eval \<alpha> (r\<cdot>\<sigma>))" .
  have "Eval \<alpha> s = Eval \<alpha> (C'\<langle>l\<cdot>\<sigma>\<rangle>)" by (simp add: s)
  also have "cge \<dots> (Eval \<alpha> (C'\<langle>r\<cdot>\<sigma>\<rangle>))" 
  proof (induct C', simp add: root[simplified])
    case (More f bef D aft)
    show ?case
    proof (simp add: Let_def, rule wm_cge[unfolded cge_wm, THEN spec, THEN spec, THEN spec, THEN spec, THEN spec, THEN mp], 
      rule conjI[OF _ More], rule subsetI)
      fix x 
      assume "x \<in> set ([Eval \<alpha> D\<langle>l \<cdot> \<sigma>\<rangle>, Eval \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>] @ map (fst \<circ> eval_lab I L LC \<alpha>) bef @ map (fst \<circ> eval_lab I L LC \<alpha>) aft)"
      then have "x \<in> { Eval \<alpha> u | u. True}" by auto            
      with wf_term[OF wfass] show "x \<in> C" by blast
    qed
  qed
  also have "\<dots> = Eval \<alpha> t" by (simp add: t)
  finally show ?thesis .
qed

lemma UNLAB_lab: "map_funs_term UNLAB (Lab \<alpha> t) = t"
proof (induct t)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  then show ?case 
    unfolding eval_lab.simps Let_def snd_conv term.simps
      LD_LC fst_conv
    by (induct ts, auto)
qed

lemma Lab_lhss_subset: "Lab_lhss Q \<subseteq> Lab_lhss_all Q"
proof 
  fix t
  assume "t \<in> Lab_lhss Q"
  then obtain \<alpha> q where q: "q \<in> Q" and "wf_assign C \<alpha>" and t: "t = Lab \<alpha> q" 
    by (force simp: lab_lhs_def)
  show "t \<in> Lab_lhss_all Q" unfolding t using q  
    by (auto simp: UNLAB_lab)
qed  

lemma gr_irreflexive: "(l,l) \<notin> gr f n"
  using SN_on_irrefl[OF gr_SN[of f n]] by blast

lemma lab_nf: 
  assumes nf: "s \<in> NF_terms Q"
  shows "Lab \<alpha> s \<in> NF_terms (Lab_lhss_all Q)"
proof(rule, rule) 
  fix t
  assume "(Lab \<alpha> s, t) \<in> rstep (Id_on (Lab_lhss_all Q))"
  from rstep_imp_map_rstep[OF this, of UNLAB, unfolded UNLAB_lab]
  have step: "(s, map_funs_term UNLAB t) \<in> rstep (map_funs_trs UNLAB (Id_on (Lab_lhss_all Q)))" (is "?p \<in> rstep ?Q") .
  have subset: "?Q \<subseteq> Id_on Q"
  proof -
    {
      fix l r
      assume "(l,r) \<in> ?Q"
      then obtain q where "q \<in> Lab_lhss_all Q" and "l = map_funs_term UNLAB q" and "r = map_funs_term UNLAB q"
        by (force simp: map_funs_trs.simps)
      then have "(l,r) \<in> Id_on Q" by auto
    }
    then show ?thesis by auto
  qed
  from rstep_mono[OF subset] step
  have "(s, map_funs_term UNLAB t) \<in> rstep (Id_on Q)" by auto
  with nf show False
    by auto
qed

lemma vars_term_lab[simp]: "vars_term (Lab \<alpha> t) = vars_term t"
  by (induct t, auto simp: Let_def)

lemma lab_nf_subst: assumes "NF_subst nfs (l,r) \<sigma> Q"
  shows "NF_subst nfs (Lab \<alpha> l, Lab \<beta> r) (lab_subst \<gamma> \<sigma>) (Lab_lhss_all Q)"
proof
  let ?l = "Lab \<alpha> l" 
  let ?r = "Lab \<beta> r"
  let ?\<sigma> = "lab_subst \<gamma> \<sigma>"
  fix x 
  assume nfs and "x \<in> vars_term ?l \<or> x \<in> vars_term ?r"
  then have x: "x \<in> vars_rule (l,r)" by (auto simp: vars_rule_def)
  show "?\<sigma> x \<in> NF_terms (Lab_lhss_all Q)" unfolding lab_subst_def
    by (rule lab_nf, insert assms[unfolded NF_subst_def] \<open>nfs\<close> x, auto)
qed

lemma lab_rqrstep: assumes step: "(s,t) \<in> rqrstep nfs Q R"
  and wfass: "wf_ass \<alpha>"
  shows "(Lab \<alpha> s, Lab \<alpha> t) \<in> rqrstep nfs (Lab_lhss_all Q) (Lab_trs R)"
  using step
proof 
  fix l r \<sigma>
  assume rule: "(l,r) \<in> R" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>"
    and nfs: "NF_subst nfs (l,r) \<sigma> Q"
    and NF: "\<forall>u\<lhd>l \<cdot> \<sigma>. u \<in> NF_terms Q" 
  let ?beta = "subst_ass \<alpha> \<sigma>"
  let ?delt = "lab_subst \<alpha> \<sigma>"
  let ?Q = "Lab_lhss_all Q"
  have wfbeta: "wf_ass ?beta" using wfass by auto
  from rule wfbeta
  have mem: "(Lab ?beta l, Lab ?beta r) \<in> (Lab_trs R)" by (simp add: lab_rule_def, force)
  have id: "Lab ?beta l \<cdot> ?delt = Lab \<alpha> (l \<cdot> \<sigma>)" by simp
  note conv = NF_rstep_supt_args_conv
  show ?thesis unfolding s t
  proof (rule rqrstepI[OF _ mem lab_subst lab_subst lab_nf_subst[OF nfs]])
    show "\<forall> u \<lhd> Lab ?beta l \<cdot> ?delt. u \<in> NF_terms ?Q" unfolding id conv
    proof
      fix u
      assume u: "u \<in> set (args (Lab \<alpha> (l \<cdot> \<sigma>)))"
      then obtain f ls where ls: "l \<cdot> \<sigma> = Fun f ls" by (cases "l \<cdot> \<sigma>", auto)
      from u ls obtain v where u: "u = Lab \<alpha> v" and v: "v \<in> set ls"
        by (auto simp: Let_def)
      from NF[unfolded conv ls] v have "v \<in> NF_terms Q" by auto
      from lab_nf[OF this]      
      show "u \<in> NF_terms ?Q" unfolding u .
    qed
  qed
qed


fun lge_term :: "('lf,'v)term \<Rightarrow> ('lf,'v)term \<Rightarrow> bool"
  where "lge_term (Var x) (Var y) = (x = y)"
     |  "lge_term (Fun f ts) (Fun g ss) = (length ts = length ss \<and> (\<forall> i < length ss. lge_term (ts ! i) (ss ! i))
                          \<and> (\<exists> h lf lg. f = LC h (length ss) lf \<and> g = LC h (length ss) lg \<and> (lf = lg \<or> Ball {lf,lg} (LS h (length ss)) \<and> lge h (length ss) lf lg)))"
     |  "lge_term _ _ = False"

lemma lge_term_decr:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and ge: "lge_term u (Lab \<alpha> s)"
  and NF: "\<forall> t \<lhd> s. t \<in> NF_terms Q"
  shows "(u,Lab \<alpha> s) \<in> (qrstep nfs (Lab_lhss_all Q) D)^*" (is "_ \<in> ?D^*")
  using ge NF
proof (induct s arbitrary: u)
  case (Var x)
  then show ?case by (cases u, auto)
next
  case (Fun f ss)
  let ?Q = "Lab_lhss_all Q"
  from Fun(2) obtain g us where u: "u = Fun g us" by (cases u, auto simp: Let_def)
  note Fun = Fun[unfolded u]
  have id: "Lab \<alpha> (Fun f ss) = Fun (LC f (length ss) (L f (map (Eval \<alpha>) ss))) (map (Lab \<alpha>) ss)"
    (is "_ = Fun ?g ?ss")
    by (simp add: Let_def o_def)
  from Fun(2)[unfolded id] obtain h lg1 lg2 where len: "length ss = length us" and g: "g = LC h (length ss) lg1" and h: "?g = LC h (length ss) lg2" and disj: "lg1 = lg2 \<or> Ball {lg1,lg2} (LS h (length ss)) \<and> lge h (length ss) lg1 lg2" by auto
  from h have "LD ?g = LD (LC h (length ss) lg2)" by simp
  from this[unfolded LD_LC] have h: "h = f" and lg2: "L f (map (Eval \<alpha>) ss) = lg2" by auto
  {
    fix i
    assume i: "i < length ss"
    from i have mem: "ss ! i \<in> set ss" by auto
    from i Fun(2)[unfolded id] have ge: "lge_term (us ! i) (Lab \<alpha> (ss ! i))" by auto
    have NF1: "\<forall> t \<lhd> ss ! i. t \<in> NF_terms Q" using mem Fun(3) by auto    
    from Fun(3)[unfolded NF_rstep_supt_args_conv] mem have "ss ! i \<in> NF_terms Q" by simp
    from lab_nf[OF this] have NF2: "Lab \<alpha> (ss ! i) \<in> NF_terms ?Q" .
    from Fun(1)[OF mem ge NF1] have "(us ! i, Lab \<alpha> (ss ! i)) \<in> ?D^*" by auto
    note this and NF2
  } note args = this
  have one: "(Fun g us, Fun g ?ss) \<in> ?D^*" 
    by (rule args_qrsteps_imp_qrsteps, insert len args(1), auto)
  from disj[unfolded h] have "lg1 = lg2 \<or> Ball {lg1, lg2} (LS f (length ss)) \<and> lge f (length ss) lg1 lg2 \<and> lg1 \<noteq> lg2"
    (is "_ \<or> ?two") by blast
  then show ?case
  proof
    assume eq: "lg1 = lg2"
    show ?case using one unfolding u g eq id h lg2 .
  next
    assume ?two
    then have "(lg1,lg2) \<in> gr f (length ss)" 
      unfolding lge_to_lgr_rel_def lge_to_lgr_def Let_def h by auto
    then have mem: "(Fun g ?ss, Fun ?g ?ss) \<in> Decr" using \<open>?two\<close> unfolding g lg2 decr_of_ord_def h  by auto
    with D have mem: "(Fun g ?ss, Fun ?g ?ss) \<in> (subst.closure D \<inter> Decr)^*" by auto
    then have "(Fun g ?ss, Fun ?g ?ss) \<in> ?D^* \<inter> { (Fun h1 ?ss, Fun h2 ?ss) | h1 h2. True }" 
    proof (induct)
      case base then show ?case by auto
    next
      case (step y z)
      from step(3)
      obtain gg where y: "y = Fun gg ?ss" by auto
      note step = step[unfolded y]
      from step(3) have steps: "(Fun g ?ss, Fun gg ?ss) \<in> ?D^*" by auto
      from step(2)[unfolded decr_of_ord_def] obtain ggg where z: "z = Fun ggg ?ss" by auto
      from step(2) have "(Fun gg ?ss, z) \<in> subst.closure D" by auto
      then obtain l r \<sigma> where lr: "(l,r) \<in> D" and id: "l \<cdot> \<sigma> = Fun gg ?ss" "z = r \<cdot> \<sigma>"
        by (auto elim: subst.closure.cases)
      have D: "?D = qrstep False (Lab_lhss_all Q) D" 
        by (rule wwf_qtrs_imp_nfs_False_switch[OF wf_trs_imp_wwf_qtrs[OF wf]]) auto
      have "(Fun gg ?ss, z) \<in> ?D" unfolding D
      proof (rule qrstepI[OF _ lr, of \<sigma> _ _ \<box>])
        show "\<forall>u\<lhd> l \<cdot> \<sigma>. u \<in> NF_terms (Lab_lhss_all Q)"
          unfolding id NF_rstep_supt_args_conv set_conv_nth using args(2) by auto
      qed (auto simp: id)
      with steps have steps: "(Fun g ?ss, z) \<in> ?D^*" by auto
      then show ?case unfolding z by auto
    qed
    with one show ?case unfolding id u by auto
  qed
qed

lemma lge_term_refl: "lge_term (Lab \<alpha> t) (Lab \<alpha> t)"
proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts)
  show ?case 
    by (unfold lge_term.simps eval_lab.simps map_map o_def snd_conv Let_def length_map, intro conjI,
    simp, simp add: Fun,
    intro exI conjI, rule refl, rule refl, simp)
qed

lemma quasi_lab_rewrite:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> qrstep nfs Q R"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  and ge: "lge_term u (Lab \<alpha> s)"
  shows "\<exists> v s'. (u,s') \<in> (qrstep nfs (Lab_lhss_all Q) D)^* \<and> (s',v) \<in> qrstep nfs (Lab_lhss_all Q) (Lab_trs R) \<and> lge_term v (Lab \<alpha> t)"
using step ge
proof (induct)
  case (IH C' \<sigma> l r)
  let ?Q = "Lab_lhss_all Q"
  let ?De = "qrstep nfs ?Q D"
  let ?R = "qrstep nfs ?Q (Lab_trs R)"
  from IH(4)
  show "\<exists> v s'. (u, s') \<in> ?De^* \<and> (s',v) \<in> ?R \<and> lge_term v (Lab \<alpha> C'\<langle>r \<cdot> \<sigma>\<rangle>)"
  proof (induct C' arbitrary: u)
    case (Hole u)
    from rqrstepI[OF IH(1) IH(2) refl refl IH(3)]
    have step: "(l \<cdot> \<sigma>, r \<cdot> \<sigma>) \<in> rqrstep nfs Q R" .
    from lab_rqrstep[OF this wfass] have "(Lab \<alpha> (l \<cdot> \<sigma>), Lab \<alpha> (r \<cdot> \<sigma>)) \<in> rqrstep nfs ?Q (Lab_trs R)" .
    then have step: "(Lab \<alpha> (l \<cdot> \<sigma>), Lab \<alpha> (r \<cdot> \<sigma>)) \<in> ?R" unfolding qrstep_iff_rqrstep_or_nrqrstep by auto
    have steps: "(u,Lab \<alpha> (l \<cdot> \<sigma>)) \<in> ?De^*"
      by (rule lge_term_decr[OF D wf], insert Hole IH(1), auto) 
    show ?case 
      by (rule exI[of _ "Lab \<alpha> (r \<cdot> \<sigma>)"], rule exI[of _ "Lab \<alpha> (l \<cdot> \<sigma>)"], intro conjI, rule steps, rule step,
      unfold intp_actxt.simps, rule lge_term_refl)
  next
    case (More f ss D ts u)
    let ?n = "Suc (length ss + length ts)"
    let ?ll = "L f (map (Eval \<alpha>) (ss @ D\<langle>l \<cdot> \<sigma>\<rangle> # ts))"
    let ?lr = "L f (map (Eval \<alpha>) (ss @ D\<langle>r \<cdot> \<sigma>\<rangle> # ts))"
    let ?D = "More (LC f ?n ?ll) (map (Lab \<alpha>) ss) \<box> (map (Lab \<alpha>) ts)"
    let ?E = "More (LC f ?n ?lr) (map (Lab \<alpha>) ss) \<box> (map (Lab \<alpha>) ts)"
    from IH(2) have "(D\<langle>l \<cdot> \<sigma>\<rangle>, D\<langle>r \<cdot> \<sigma>\<rangle>) \<in> qrstep False {} R" using ctxt.closure.intros by auto
    then have cge: "cge (Eval \<alpha> D\<langle>l \<cdot> \<sigma>\<rangle>) (Eval \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>)" using qmodel wfass by (rule quasi_sem_rewrite)
    let ?l = "?D\<langle>Lab \<alpha> D\<langle>l \<cdot> \<sigma>\<rangle>\<rangle>"
    let ?r = "?E\<langle>Lab \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>\<rangle>"
    have id: "Lab \<alpha> (More f ss D ts)\<langle>l \<cdot> \<sigma>\<rangle> = ?l" "Lab \<alpha> (More f ss D ts)\<langle>r \<cdot> \<sigma>\<rangle> = ?r"
      by (auto simp: Let_def o_def)
    {
      fix c
      assume "c \<in> set ([Eval \<alpha> D\<langle>l \<cdot> \<sigma>\<rangle>, Eval \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>] @ map (Eval \<alpha>) ss @ map (Eval \<alpha>) ts)"
      then have "c \<in> { Eval \<alpha> u | u. True}" by auto            
      with wf_term[OF wfass] have "c \<in> C" by blast
    } note inC = this
    have lge: "lge f ?n ?ll ?lr" 
      by (simp, rule wm_lge[unfolded lge_wm, THEN spec, THEN spec[of _ "map (Eval \<alpha>) ss"], THEN spec, THEN spec, 
        THEN spec[of _ "map (Eval \<alpha>) ts"], THEN mp, simplified length_map], rule conjI[OF _ cge], rule subsetI, rule inC, simp)
    from More(2) id have ge: "lge_term u (?D\<langle>Lab \<alpha> D\<langle> l \<cdot> \<sigma>\<rangle>\<rangle>)" by simp
    then obtain g us where u: "u = Fun g us" and len: "length us = ?n" by (cases u, auto)
    let ?m = "length ss"
    from ge[unfolded u, simplified]    
    obtain h lg1 lg2 where ge: "\<forall> i < ?n. lge_term (us ! i) (map (Lab \<alpha>) (ss @ D\<langle>l\<cdot>\<sigma>\<rangle> # ts) ! i)" and g: "g = LC h ?n lg1" and h: "LC f ?n ?ll = LC h ?n lg2" and disj: "lg1 = lg2 \<or> Ball {lg1,lg2} (LS h ?n) \<and> lge h ?n lg1 lg2" by auto
    from h have "LD (LC f ?n ?ll) = LD (LC h ?n lg2)" by simp 
    from this[unfolded LD_LC] have h: "h = f" and lg2: "?ll = lg2" by auto
    from ge[THEN spec[of _ "length ss"]] have "lge_term (us ! ?m) (Lab \<alpha> D\<langle>l\<cdot>\<sigma>\<rangle>)" by (auto simp: nth_append)
    from More(1)[OF this] obtain v s' where steps: "(us ! ?m, s') \<in> ?De^*" and step: "(s',v) \<in> ?R" and lge2: "lge_term v (Lab \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>)" by auto
    let ?list = "\<lambda> u. (take ?m us @ u # drop (Suc ?m) us)"
    let ?C = "\<lambda> u. Fun g (?list u)"
    have steps: "(?C (us ! ?m), ?C s') \<in> ?De^*"
      by (rule ctxt_closed_one[OF _ steps], blast)
    have "?m < length us" using len by simp
    from id_take_nth_drop[OF this] have "?C (us ! ?m) = Fun g us" by simp
    with steps have steps: "(Fun g us, ?C s') \<in> ?De^*" by simp
    have step: "(?C s',?C v) \<in> ?R" 
      by (rule ctxt_closed_one[OF _ step], blast)
    show ?case 
    proof (intro exI conjI, unfold u, rule steps, rule step, unfold id(2))
      let ?lisl = "?list v"
      let ?lisr = "map (Lab \<alpha>) ss @ Lab \<alpha> D\<langle>r\<cdot>\<sigma>\<rangle> # map (Lab \<alpha>) ts"
      from len have leng: "length ?lisr = ?n" by simp
      show "lge_term (Fun g (take ?m us @ v # drop (Suc ?m) us)) ?r"
        unfolding intp_actxt.simps lge_term.simps
      proof (intro conjI, simp add: len)
        let ?p = "\<lambda> i. lge_term (?lisl ! i) (?lisr ! i)"
        show "\<forall> i < length ?lisr. ?p i"
        proof (intro allI impI)
          fix i
          assume i: "i < length ?lisr"
          with len have i': "i < length us" by auto
          show "?p i"
          proof (cases "i < ?m")
            case True
            with ge[THEN spec[of _ i]]
            show "?p i"
              by (auto simp: i' nth_append)
          next
            case False note oFalse = this
            show "?p i"
            proof (cases "i = ?m")
              case True
              with i' lge2 show ?thesis 
                by (auto simp: i' nth_append)
            next
              case False
              from oFalse have "i = i - ?m + ?m" by simp
              then obtain j where "i = j + ?m" by simp
              with False obtain j where id: "i = ?m + Suc j" by (cases j, auto)
              from i id have j: "j < length ts" by auto
              from j len have min: "min (length us) ?m = ?m" by simp
              show "?p i"
                using ge[THEN spec[of _ i]] i i' unfolding len[symmetric]
                by (auto simp: id nth_append min)
            qed
          qed
        qed
      next
        obtain n where n: "?n = n" by auto
        obtain ll where ll: "?ll = ll" by auto
        obtain lr where lr: "?lr = lr" by auto
        have "LS f ?n ?ll" 
          by (simp, rule wf_L[unfolded wf_label_def, THEN spec, THEN spec[of _ "map (Eval \<alpha>) (ss @ D\<langle>l \<cdot> \<sigma>\<rangle> # ts)"], THEN mp, simplified], auto simp: inC)
        then have llLS: "LS f n ll" using ll n by auto
        have "LS f ?n ?lr" 
          by (simp, rule wf_L[unfolded wf_label_def, THEN spec, THEN spec[of _ "map (Eval \<alpha>) (ss @ D\<langle>r \<cdot> \<sigma>\<rangle> # ts)"], THEN mp, simplified], auto simp: inC)  
        then have lrLS: "LS f n lr" using lr n by auto        
        show "\<exists> h lf lg. 
          g = LC h (length ?lisr) lf \<and>
          LC f ?n ?lr = LC h (length ?lisr) lg \<and>
          (lf = lg \<or> Ball {lf,lg} (LS h (length ?lisr)) \<and> lge h (length ?lisr) lf lg)"
          unfolding leng n g h 
        proof (intro exI conjI, rule refl, rule refl, insert disj[unfolded lg2[symmetric]] lge, unfold leng n h ll lr)
          assume one: "lg1 = ll \<or> Ball {lg1,ll} (LS f n) \<and> lge f n lg1 ll" 
            and two: "lge f n ll lr"
          from one 
          show "lg1 = lr \<or> Ball {lg1,lr} (LS f n) \<and> lge f n lg1 lr"
          proof 
            assume "lg1 = ll"
            with two llLS lrLS show ?thesis by auto
          next
            assume "Ball {lg1,ll} (LS f n) \<and> lge f n lg1 ll"
            with lge_trans[OF _ two, of lg1] lrLS show ?thesis by auto
          qed
        qed
      qed
    qed
  qed
qed

lemma quasi_lab_rewrites:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> (qrstep nfs Q R)^*"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  and ge: "lge_term u (Lab \<alpha> s)"
  shows "\<exists> v. (u,v) \<in> (qrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> D))^* \<and> lge_term v (Lab \<alpha> t)"
using step 
proof (induct)
  case base
  show ?case
    by (rule exI[of _ u], rule conjI[OF _ ge], auto)
next
  case (step t w)
  let ?Q = "(Lab_lhss_all Q)"
  let ?R = "qrstep nfs ?Q (Lab_trs R \<union> D)"
  from step(3) obtain v where steps: "(u,v) \<in> ?R^*" and lge: "lge_term v (Lab \<alpha> t)" by auto
  from quasi_lab_rewrite[OF D wf step(2) qmodel wfass lge] obtain x y where 
    more_steps: "(v,x) \<in> (qrstep nfs ?Q D)^*" "(x,y) \<in> qrstep nfs ?Q (Lab_trs R)" and ge: "lge_term y (Lab \<alpha> w)"
    by auto
  from steps more_steps have steps: "(u,y) \<in> ?R^* O (qrstep nfs ?Q D)^* O qrstep nfs ?Q (Lab_trs R)" by auto
  have steps: "(u,y) \<in> ?R^*" 
    by (rule set_mp[OF _ steps], unfold qrstep_union, regexp)
  with ge show ?case by auto
qed

lemma quasi_lab_relstep:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> rel_qrstep (nfs,Q,R,S)"
  and qmodel_R: "qmodel I L LC C cge R"
  and qmodel_S: "qmodel I L LC C cge S"
  and wfass: "wf_ass \<alpha>"
  and ge: "lge_term x (Lab \<alpha> s)"
  shows "\<exists> v. (x,v) \<in> rel_qrstep (nfs,Lab_lhss_all Q,Lab_trs R, Lab_trs S \<union> D) \<and> lge_term v (Lab \<alpha> t)"
proof -
  let ?Q = "Lab_lhss_all Q"
  let ?R = "Lab_trs R"
  let ?D = "D"
  let ?S = "Lab_trs S"
  from step
  obtain u v where steps: "(s,u) \<in> (qrstep nfs Q S)^*" "(u,v) \<in> qrstep nfs Q R" "(v,t) \<in> (qrstep nfs Q S)^*"
    by auto
  from quasi_lab_rewrites[OF D wf steps(1) qmodel_S wfass ge]
  obtain u1 where step1: "(x,u1) \<in> (qrstep nfs ?Q (?S \<union> ?D))^*" and ge: "lge_term u1 (Lab \<alpha> u)"
    by auto
  from quasi_lab_rewrite[OF D wf steps(2) qmodel_R wfass ge]
  obtain v1 v2 where step2: "(u1,v1) \<in> (qrstep nfs ?Q ?D)^*" "(v1,v2) \<in> qrstep nfs ?Q ?R" and ge: "lge_term v2 (Lab \<alpha> v)"
    by auto
  from quasi_lab_rewrites[OF D wf steps(3) qmodel_S wfass ge]
  obtain t1 where step3: "(v2,t1) \<in> (qrstep nfs ?Q (?S \<union> ?D))^*" and ge: "lge_term t1 (Lab \<alpha> t)" 
    by auto
  from step1 step2 step3
  have step: "(x,t1) \<in> (qrstep nfs ?Q (?S \<union> ?D))^* O (qrstep nfs ?Q ?D)^* O qrstep nfs ?Q ?R O (qrstep nfs ?Q (?S \<union> ?D))^*" by auto
  have "(x,t1) \<in> rel_qrstep (nfs, ?Q,?R, ?S \<union> ?D)"
    by (rule set_mp[OF _ step], unfold qrstep_union split, regexp)
  with ge show ?thesis by auto
qed
end

context 
begin
qualified fun aux where 
  "aux R 0 z = z"
| "aux R (Suc n) z = (SOME lt. R (aux R n z,lt,Suc n))"
end

context sl_interpr
begin

lemma quasi_rel_SN_lab_imp_rel_SN:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and LQ: "NF_terms LQ \<supseteq> NF_terms (Lab_lhss_all Q)"
  and SN: "SN_qrel (nfs, LQ,Lab_trs R,Lab_trs S \<union> D)" 
  and qmodel_R: "qmodel I L LC C cge R"
  and qmodel_S: "qmodel I L LC C cge S"
  shows "SN_qrel (nfs,Q,R,S)"
  unfolding SN_qrel_def split_conv SN_rel_defs
proof 
  fix f 
  assume "\<forall> i. (f i, f (Suc i)) \<in> relto (qrstep nfs Q R) (qrstep nfs Q S)"
  then have steps: "\<And> i. (f i, f (Suc i)) \<in> rel_qrstep (nfs,Q,R,S)" by auto
  let ?R = "rel_qrstep (nfs,Lab_lhss_all Q, Lab_trs R, Lab_trs S \<union> D)"
  obtain g where g: "g = (\<lambda>i. Semantic_Labeling.aux (\<lambda> (r,lt,n). (r,lt) \<in> ?R \<and> lge_term lt (LAB (f n))) i (LAB (f 0)))" by auto
  note main = someI_ex[OF quasi_lab_relstep[OF D wf steps qmodel_R qmodel_S wf_default_ass]]
  {
    fix i
    have "(g i, g (Suc i)) \<in> ?R \<and> lge_term (g i) (LAB (f i))" (is "?p i")
    proof (induct i)
      case 0
      from main[of _ 0, OF _ _ lge_term_refl]
      show "?p 0" by (auto simp: lge_term_refl g)
    next
      case (Suc i)
      then have ge: "lge_term (g i) (LAB (f i))" by auto
      from main[OF _ _ ge]
      have ge: "lge_term (g (Suc i)) (LAB (f (Suc i)))" by (auto simp: g)
      from main[OF _ _ ge] ge
      show ?case by (auto simp: g)
    qed
    then have "(g i, g (Suc i)) \<in> ?R" by simp    
  } note steps = this
  from steps have "\<not> SN ?R" unfolding SN_defs by auto
  with SN_subset[OF _ rel_qrstep_mono[OF subset_refl subset_refl LQ]] SN[unfolded SN_qrel_def SN_rel_defs]
  show False by auto
qed


abbreviation F_all :: "'lf sig"
  where "F_all \<equiv> {(LC f n l,n) | l f n. LS f n l}"

lemma wf_lab: assumes wf: "wf_ass \<alpha>"
  shows "funas_term (Lab \<alpha> t) \<subseteq> F_all"
proof (induct t)
  case (Var x)
  then show ?case by auto
next
  case (Fun f ts)
  let ?n = "length ts"
  have C: "set (map (Eval \<alpha>) ts) \<subseteq> C"
    using wf_term[OF wf] by auto
  have L: "LS f ?n (L f (map (Eval \<alpha>) ts))"
    using wf_L[unfolded wf_label_def, THEN spec, THEN spec, THEN mp[OF _ C]] by auto
  show ?case unfolding eval_lab.simps Let_def o_def snd_conv map_map
    using L Fun by force
qed

end

lemma lab_trs_union: "lab_trs I L LC cge (R \<union> S) = lab_trs I L LC cge R \<union> lab_trs I L LC cge S" by auto


context sl_interpr_root
begin

fun lge_term_root :: "('lf,'v)term \<Rightarrow> ('lf,'v)term \<Rightarrow> bool"
  where "lge_term_root (Fun f ts) (Fun g ss) = (length ts = length ss \<and> (\<forall> i < length ss. lge_term (ts ! i) (ss ! i))
                          \<and> (\<exists> h lf lg. f = LC h (length ss) lf \<and> g = LC h (length ss) lg \<and> (lf = lg \<or> Ball {lf,lg} (LS' h (length ss)) \<and> lge h (length ss) lf lg)))"
 |  "lge_term_root (Var x) (Var y) = (x = y)"
 |  "lge_term_root _ _ = False"


lemma lge_term_root_refl: "lge_term_root (Lab_root \<alpha> t) (Lab_root \<alpha> t)"
proof (induct t)
  case (Var x) then show ?case by simp
next
  case (Fun f ts)
  show ?case 
    by (unfold lge_term_root.simps lab_root.simps map_map o_def snd_conv Let_def length_map, intro conjI,
    simp, simp add: lge_term_refl, 
    intro exI conjI, rule refl, rule refl, simp)
qed

lemma quasi_lab_root_rewrite: 
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> nrqrstep nfs Q R"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  and ge: "lge_term_root u (Lab_root \<alpha> s)"
  shows "\<exists> v s'. (u,s') \<in> (nrqrstep nfs (Lab_lhss_all Q) D)^* \<and> (s',v) \<in> nrqrstep nfs (Lab_lhss_all Q) (Lab_trs R) \<and> lge_term_root v (Lab_root \<alpha> t)"
proof -  
  let ?Q = "Lab_lhss_all Q"
  let ?De = "qrstep nfs ?Q D" 
  let ?nDe = "nrqrstep nfs ?Q D" 
  let ?R = "qrstep nfs ?Q (Lab_trs R)"
  let ?nR = "nrqrstep nfs ?Q (Lab_trs R)"
  from step[unfolded nrqrstep_def] 
  obtain C' l r \<sigma> where lr: "(l,r) \<in> R" and "C' \<noteq> \<box>" and s: "s = C'\<langle>l \<cdot> \<sigma>\<rangle>" and t: "t = C'\<langle>r \<cdot> \<sigma>\<rangle>" and 
  NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms Q" and nfs: "NF_subst nfs (l,r) \<sigma> Q" by auto
  then obtain f D bef aft where C': "C' = More f bef D aft" by (cases C', auto)
  let ?si = "D\<langle>l\<cdot>\<sigma>\<rangle>" 
  let ?ti = "D\<langle>r\<cdot>\<sigma>\<rangle>"
  let ?C = "\<lambda> t. Fun f (bef @ t # aft)"
  from lr NF nfs have step: "(?si, ?ti) \<in> qrstep nfs Q R" by auto
  from quasi_sem_rewrite[OF step qmodel wfass]
  have cge: "cge (Eval \<alpha> ?si) (Eval \<alpha> ?ti)" .
  let ?n = "Suc (length bef + length aft)"
  let ?m = "length bef"
  let ?ls = "\<lambda> t. map (Lab \<alpha>) bef @ Lab \<alpha> t # map (Lab \<alpha>) aft"
  let ?lsi = "?ls ?si"
  let ?lti = "?ls ?ti"
  let ?L' = "L' f (map (Eval \<alpha>) (bef @ D\<langle>l \<cdot> \<sigma>\<rangle> # aft))"
  let ?L'' = "L' f (map (Eval \<alpha>) (bef @ D\<langle>r \<cdot> \<sigma>\<rangle> # aft))"
  from C' s t have s: "s = ?C ?si" and t: "t = ?C ?ti" by auto
  from ge[unfolded s] obtain g us where u: "u = Fun g us" by (cases u, auto)
  from ge[unfolded s u lab_root.simps Let_def lge_term_root.simps map_map o_def]
  obtain h lf lg where len: "length us = ?n" and args: "\<And> i. i < ?n \<Longrightarrow> lge_term (us ! i) (?lsi ! i)"
    and g: "g = LC h ?n lf" and id: "LC f ?n ?L' = LC h ?n lg" and disj: "lf = lg \<or> Ball {lf,lg} (LS' h ?n) \<and> lge h ?n lf lg"
    by auto
  from id have "LD (LC f ?n ?L') = LD (LC h ?n lg)" by auto
  from this[unfolded LD_LC] have h: "h = f" and lg: "lg = ?L'" by auto
  from args[of ?m] have lge_term: "lge_term (us ! ?m) (Lab \<alpha> ?si)" by (auto simp: nth_append)
  from quasi_lab_rewrite[OF D wf step qmodel wfass lge_term] obtain v s' 
    where steps: "(us ! ?m, s') \<in> ?De^*" and step: "(s',v) \<in> ?R" and ge: "lge_term v (Lab \<alpha> D\<langle>r \<cdot> \<sigma>\<rangle>)" by auto
  let ?lis = "\<lambda> t. (take ?m us @ t # drop (Suc ?m) us)"
  let ?D = "\<lambda> f t. Fun f (?lis t)"
  have us: "take ?m us @ us ! ?m # drop (Suc ?m) us = us" (is "?us = us")
    by (rule id_take_nth_drop[symmetric], insert len, auto)
  then have gus: "Fun g us = Fun g ?us" by simp
  from len have m: "?m < length us" by auto
  have gus: "Fun g us = Fun g (?lis (us ! ?m))" using id_take_nth_drop[OF m]
    by simp
  show ?thesis
  proof (rule exI[of _ "?D g v"], rule exI[of _ "?D g s'"], unfold u, intro conjI)
    show "(?D g s', ?D g v) \<in> ?nR"
      by (rule qrstep_imp_ctxt_nrqrstep[OF step])
  next
    show "(Fun g us, ?D g s') \<in> ?nDe^*"
      unfolding gus
      by (rule qrsteps_imp_ctxt_nrqrsteps[OF steps])
  next
    let ?lt = "map (Lab \<alpha>) (bef @ D\<langle>r \<cdot> \<sigma>\<rangle> # aft)"
    have ex: "\<exists> h lf lg. g = LC h ?n lf \<and> LC f ?n ?L'' = LC h ?n lg \<and> (lf = lg \<or> Ball {lf,lg} (LS' h ?n) \<and> lge h ?n lf lg)"
    proof (intro exI conjI, unfold g h, rule refl, rule refl)
      {
        fix c
        assume "c \<in> set ([Eval \<alpha> ?si, Eval \<alpha> ?ti] @ map (Eval \<alpha>) bef @ map (Eval \<alpha>) aft)"
        then have "c \<in> { Eval \<alpha> u | u. True}" by auto            
        with wf_term[OF wfass] have "c \<in> C" by blast
      } note inC = this  
      have lge: "lge f ?n ?L' ?L''"
        by (simp, rule wm_lge'[unfolded lge_wm, THEN spec, THEN spec[of _ "map (Eval \<alpha>) bef"], THEN spec, THEN spec, 
          THEN spec[of _ "map (Eval \<alpha>) aft"], THEN mp, simplified length_map], rule conjI[OF _ cge], rule subsetI, rule inC, simp)
      have L': "LS' f ?n ?L'" 
        by (simp, rule wf_L'[unfolded wf_label_def, THEN spec, THEN spec[of _ "map (Eval \<alpha>) (bef @ ?si # aft)"], THEN mp, simplified], auto simp: inC)
      have L'': "LS' f ?n ?L''" 
        by (simp, rule wf_L'[unfolded wf_label_def, THEN spec, THEN spec[of _ "map (Eval \<alpha>) (bef @ ?ti # aft)"], THEN mp, simplified], auto simp: inC)
      show "lf = ?L'' \<or> Ball {lf, ?L''} (LS' f ?n) \<and> lge f ?n lf ?L''"
        using disj
      proof
        assume "lf = lg" 
        with lg lge L' L'' show ?thesis by auto
      next
        assume "Ball {lf,lg} (LS' h ?n) \<and> lge h ?n lf lg"
        then have lf: "LS' f ?n lf" and ge2: "lge f ?n lf lg" unfolding h by auto
        from lge_trans[OF ge2[unfolded lg] lge] L'' lf
        show ?thesis by blast
      qed
    qed      
    show "lge_term_root (?D g v) (Lab_root \<alpha> t)"
      unfolding t lab_root.simps Let_def map_map o_def lge_term_root.simps
    proof (intro conjI, simp add: len, intro allI impI)
      fix i      
      assume i: "i < length ?lt"
      show "lge_term (?lis v ! i) (?lt ! i)"
      proof (cases "i = ?m")
        case True
        then have id: "?lis v ! i = v" "?lt ! i = Lab \<alpha> D\<langle>r\<cdot>\<sigma>\<rangle>" by (auto simp: len nth_append)
        show ?thesis unfolding id by (rule ge)
      next
        case False
        have id: "?lis v ! i = us ! i"          
          by (rule nth_append_take_drop_is_nth_conv, insert False i len, auto)
        obtain j where j: "j =  i - ?m - 1" by auto
        have "i > ?m \<Longrightarrow> i - ?m = Suc j" unfolding j by auto
        then have id2: "?lt ! i = ?lsi ! i" using False by (cases "i > ?m", auto simp: nth_append)        
        from args[of i] i len have "lge_term (us ! i) (?lsi ! i)" by auto
        then show ?thesis unfolding id id2 .
      qed      
    qed (insert ex, auto)
  qed
qed

lemma quasi_lab_root_rewrites: 
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> (nrqrstep nfs Q R)^*"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  and ge: "lge_term_root u (Lab_root \<alpha> s)"
  shows "\<exists> v . (u,v) \<in> (nrqrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> D))^* \<and> lge_term_root v (Lab_root \<alpha> t)"
using step 
proof (induct)
  case base
  show ?case
    by (rule exI[of _ u], rule conjI[OF _ ge], auto)
next
  case (step t w)
  let ?Q = "(Lab_lhss_all Q)"
  let ?R = "qrstep nfs ?Q (Lab_trs R \<union> D)"
  let ?nR = "nrqrstep nfs ?Q (Lab_trs R \<union> D)"
  from step(3) obtain v where steps: "(u,v) \<in> ?nR^*" and lge: "lge_term_root v (Lab_root \<alpha> t)" by auto
  from quasi_lab_root_rewrite[OF D wf step(2) qmodel wfass lge] obtain x y where 
    more_steps: "(v,x) \<in> (nrqrstep nfs ?Q D)^*" "(x,y) \<in> nrqrstep nfs ?Q (Lab_trs R)" and ge: "lge_term_root y (Lab_root \<alpha> w)"
    by auto
  from steps more_steps have steps: "(u,y) \<in> ?nR^* O (nrqrstep nfs ?Q D)^* O nrqrstep nfs ?Q (Lab_trs R)" by auto
  have steps: "(u,y) \<in> ?nR^*" 
    by (rule set_mp[OF _ steps], unfold nrqrstep_union, regexp)
  with ge show ?case by auto
qed


lemma lge_term_root_decr:
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and ge: "lge_term_root u (Lab_root \<alpha> s)"
  and NF: "s \<in> NF_terms Q" (* it would suffice that arguments of S are in NF, but this is the more common case *)
  shows "(u,Lab_root \<alpha> s) \<in> (nrqrstep nfs (Lab_lhss_all Q) D)^* O Decr_root^=" (is "_ \<in> ?D^* O _")
proof (cases s)
  case (Var x)
  then show ?thesis using ge by (cases u, auto)
next
  case (Fun f ss)  
  let ?Q = "Lab_lhss_all Q"
  let ?D' = "qrstep nfs ?Q D"
  from ge Fun obtain g us where u: "u = Fun g us" by (cases u, auto simp: Let_def)
  note ge = ge[unfolded u lab_root.simps Let_def map_map o_def]
  have id: "Lab_root \<alpha> s = Fun (LC f (length ss) (L' f (map (Eval \<alpha>) ss))) (map (Lab \<alpha>) ss)"
    (is "_ = Fun ?g ?ss")
    by (simp add: Fun Let_def o_def)
  note ge = ge[unfolded id]
  from ge obtain h lg1 lg2 where len: "length ss = length us" and g: "g = LC h (length ss) lg1" and h: "?g = LC h (length ss) lg2" and disj: "lg1 = lg2 \<or> Ball {lg1,lg2} (LS' h (length ss)) \<and> lge h (length ss) lg1 lg2" by auto
  from h have "LD ?g = LD (LC h (length ss) lg2)" by simp
  from this[unfolded LD_LC] have h: "h = f" and lg2: "L' f (map (Eval \<alpha>) ss) = lg2" by auto
  {
    fix i
    assume i: "i < length ss"
    from i have mem: "ss ! i \<in> set ss" by auto
    from i ge have ge: "lge_term (us ! i) (Lab \<alpha> (ss ! i))" by auto
    have NF1: "\<forall> t \<lhd> ss ! i. t \<in> NF_terms Q"
    proof (intro impI allI)
      fix t
      assume "ss ! i \<rhd> t" 
      with mem have "t \<lhd> s" unfolding Fun by auto
      with NF_imp_subt_NF[OF NF]
      show "t \<in> NF_terms Q" by auto
    qed
    from lge_term_decr[OF D wf ge NF1] i
    have "(us ! i, ?ss ! i) \<in> ?D'^*" by auto
  } note args = this
  have one: "(Fun g us, Fun g ?ss) \<in> ?D^*" 
    by (rule args_steps_imp_steps_gen[OF _ _ args],
    rule qrsteps_imp_ctxt_nrqrsteps, insert len, auto)
  from disj[unfolded h] have "lg1 = lg2 \<or> Ball {lg1, lg2} (LS' f (length ss)) \<and> lge f (length ss) lg1 lg2 \<and> lg1 \<noteq> lg2"
    (is "_ \<or> ?two") by blast
  then show ?thesis
  proof
    assume eq: "lg1 = lg2"
    show ?thesis using one unfolding u g eq id h lg2 by auto
  next
    assume ?two
    then have "(lg1,lg2) \<in> gr_root f (length ss)" 
      unfolding lge_to_lgr_rel_def lge_to_lgr_def Let_def h by auto
    then have mem: "(Fun g ?ss, Fun ?g ?ss) \<in> Decr_root" using \<open>?two\<close> unfolding g lg2 decr_of_ord_def h  by auto
    with one show ?thesis unfolding id u by auto
  qed
qed

lemma quasi_lab_root_rewrites_qnf: 
  assumes D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and step: "(s,t) \<in> (nrqrstep nfs Q R)^*"
  and qmodel: "qmodel I L LC C cge R"
  and wfass: "wf_ass \<alpha>"
  and NF: "t \<in> NF_terms Q"
  shows "(Lab_root \<alpha> s, Lab_root \<alpha> t) \<in> (nrqrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> D))^* O Decr_root^="
proof - 
  let ?Q = "Lab_lhss_all Q"
  let ?D = "nrqrstep nfs ?Q D"
  let ?RD = "nrqrstep nfs ?Q (Lab_trs R \<union> D)"
  from quasi_lab_root_rewrites[OF D wf step qmodel wfass lge_term_root_refl]
  obtain v where steps: "(Lab_root \<alpha> s, v) \<in> ?RD^*" and ge: "lge_term_root v (Lab_root \<alpha> t)" by auto
  from lge_term_root_decr[OF D wf ge NF]
  have "(v,Lab_root \<alpha> t) \<in> ?D^* O Decr_root^=" .
  with steps have steps: "(Lab_root \<alpha> s, Lab_root \<alpha> t) \<in> ?RD^* O ?D^* O Decr_root^=" by auto
  show ?thesis
    by (rule set_mp[OF _ steps], unfold nrqrstep_union, regexp)
qed


lemma nrqrstep_Decr_root: "(nrqrstep nfs Q R O Decr_root^=) = (Decr_root^= O nrqrstep nfs Q R)" (is "(?N O ?D^=) = _")
proof -
  obtain D where D: "?D^= = D" by auto
  obtain N where N: "?N = N" by auto
  {
    fix s t
    assume "(s,t) \<in> ?N O ?D^="
    then obtain u where su: "(s,u) \<in> ?N" and ut: "(u,t) \<in> ?D^=" by auto
    have "(s,t) \<in> ?D^= O ?N"
    proof (cases "u = t")
      case True
      with su show ?thesis by auto
    next
      case False
      with ut have ut: "(u,t) \<in> ?D" by auto
      from su show ?thesis
      proof
        fix l r C \<sigma>
        assume nf: "\<forall> u \<lhd> l\<cdot>\<sigma>. u \<in> NF_terms Q" and lr: "(l,r) \<in> R"
          and C: "C \<noteq> \<box>" and s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and u: "u = C\<langle>r\<cdot>\<sigma>\<rangle>"
          and nfs: "NF_subst nfs (l,r) \<sigma> Q"
        from C obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
        let ?args = "\<lambda> t. bef @ D\<langle>t\<rangle> # aft"
        let ?n = "\<lambda> t. length (?args t)"
        let ?ts = "?args (r \<cdot> \<sigma>)"
        let ?ss = "?args (l \<cdot> \<sigma>)"
        let ?nts = "?n (r \<cdot> \<sigma>)"
        from ut[unfolded decr_of_ord_def]
        obtain g l1 l2 ts where u2: "u = Fun (LC g (length ts) l1) ts" and
          t: "t = Fun (LC g (length ts) l2) ts" and
          l1: "LS' g (length ts) l1" and
          l2: "LS' g (length ts) l2" and
          gr: "(l1,l2) \<in> gr_root g (length ts)" 
          by blast
        let ?f1 = "LC g (length ts) l1" 
        let ?f2 = "LC g (length ts) l2"
        from u u2 C have f: "f = ?f1" and ts: "ts = ?ts" by auto
        let ?u = "Fun ?f2 ?ss"
        have "(s,?u) \<in> ?D" unfolding s C f decr_of_ord_def  
          using l1 l2 gr 
          unfolding ts by auto
        moreover have "(?u,t) \<in> ?N"
          unfolding t ts
        proof (rule nrqrstepI[OF nf lr _ _ _ nfs])
          have "More ?f2 bef D aft \<noteq> \<box>" by simp
        qed auto
        ultimately show ?thesis by auto
      qed
    qed
  }
  moreover
  {
    fix s t
    assume "(s,t) \<in> ?D^= O ?N"
    then obtain u where su: "(s,u) \<in> ?D^=" and ut: "(u,t) \<in> ?N" by auto
    have "(s,t) \<in> ?N O ?D^="
    proof (cases "s = u")
      case True
      with ut show ?thesis by auto
    next
      case False
      with su have su: "(s,u) \<in> ?D" by auto
      from ut show ?thesis
      proof
        fix l r C \<sigma>
        assume nf: "\<forall> u \<lhd> l\<cdot>\<sigma>. u \<in> NF_terms Q" and lr: "(l,r) \<in> R"
          and C: "C \<noteq> \<box>" and u: "u = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>"
          and nfs: "NF_subst nfs (l,r) \<sigma> Q"
        from C obtain f bef D aft where C: "C = More f bef D aft" by (cases C, auto)
        let ?args = "\<lambda> t. bef @ D\<langle>t\<rangle> # aft"
        let ?n = "\<lambda> t. length (?args t)"
        let ?ts = "?args (l \<cdot> \<sigma>)"
        let ?ss = "?args (r \<cdot> \<sigma>)"
        let ?nts = "?n (r \<cdot> \<sigma>)"
        from su[unfolded decr_of_ord_def]
        obtain g l1 l2 ts where u2: "u = Fun (LC g (length ts) l2) ts" and
          s: "s = Fun (LC g (length ts) l1) ts" and
          l1: "LS' g (length ts) l1" and
          l2: "LS' g (length ts) l2" and
          gr: "(l1,l2) \<in> gr_root g (length ts)" 
          by blast
        let ?f1 = "LC g (length ts) l1" 
        let ?f2 = "LC g (length ts) l2"
        from u u2 C have f: "f = ?f2" and ts: "ts = ?ts" by auto
        let ?u = "Fun ?f1 ?ss"
        have "(?u,t) \<in> ?D" unfolding t C f decr_of_ord_def  
          using l1 l2 gr 
          unfolding ts by auto
        moreover have "(s,?u) \<in> ?N"
          unfolding s ts
        proof (rule nrqrstepI[OF nf lr _ _ _ nfs])
          have "More ?f1 bef D aft \<noteq> \<box>" by simp
        qed auto
        ultimately show ?thesis by auto
      qed
    qed
  }
  ultimately show ?thesis unfolding D N by blast
qed        

lemma nrqrsteps_Decr_root:
  "((nrqrstep nfs Q R)^* O Decr_root^=) = (Decr_root^= O (nrqrstep nfs Q R)^*)" (is "(?N^* O ?D) = _")
proof -
  {
    fix n
    have "(?N^^n O ?D) = (?D O ?N^^n)"
    proof (induct n)
      case 0
      show ?case by simp
    next
      case (Suc n)
      have "?N^^(Suc n) O ?D = ?N^^n O ?N O ?D"
        by auto
      also have "... = (?N^^n O ?D) O ?N" unfolding nrqrstep_Decr_root
        by blast
      also have "... = ?D O (?N^^n O ?N)" unfolding Suc by blast
      finally show ?case by auto
    qed
  } note n = this
  then show ?thesis unfolding rtrancl_is_UN_relpow by (auto simp: relcomp.simps, blast+)
qed

lemma quasi_lab_root_steps_qnf: 
  assumes nvar: "\<forall>(l,r) \<in> (R \<union> S). is_Fun l"
  and ndef: "\<not> defined (applicable_rules Q (R \<union> S)) (the (root s))"
  and D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and steps: "(s,t) \<in> (qrstep nfs Q (R \<union> S))^*"
  and qmodel_R: "qmodel I L LC C cge R"
  and qmodel_S: "qmodel I L LC C cge S"
  and nf: "t \<in> NF_terms Q"
  and wfass: "wf_ass \<alpha>"
  shows "(Lab_root \<alpha> s,Lab_root \<alpha> t) \<in> Decr_root^= O
  (qrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> Lab_trs S \<union> D))^*"
  (is "?st \<in> _")
proof -
  let ?Q = "Lab_lhss_all Q"
  let ?R = "Lab_trs R"
  let ?RS = "Lab_trs R \<union> Lab_trs S"
  let ?D = "D"
  let ?QD = "nrqrstep nfs ?Q D"
  let ?All = "nrqrstep nfs ?Q (?RS \<union> D)"
  let ?Lab = "Lab_root \<alpha>"
  from qrsteps_imp_nrqrsteps[OF nvar ndef steps]
  have st: "(s,t) \<in> (nrqrstep nfs Q (R \<union> S))^*" .
  from qmodel_R qmodel_S have qmodel: "qmodel I L LC C cge (R \<union> S)" 
    unfolding qmodel_def by  auto
  from quasi_lab_root_rewrites[OF D wf st qmodel wfass lge_term_root_refl]
  obtain t' where st: "(?Lab s, t') \<in> ?All^*"
    and t': "lge_term_root t' (?Lab t)" unfolding lab_trs_union by auto
  from lge_term_root_decr[OF D wf t' nf]
  have tt: "(t', ?Lab t) \<in> ?QD^* O Decr_root^=" by auto
  from st tt
  have st: "?st \<in> ?All^* O ?QD^* O Decr_root^=" by blast
  have st: "?st \<in> ?All^* O Decr_root^="
    by (rule set_mp[OF _ st], unfold nrqrstep_union, regexp)
  from this[simplified nrqrsteps_Decr_root O_assoc[symmetric]]
  have st: "?st \<in> Decr_root^= O ?All^*" 
    by (simp add: O_assoc)
  have "?All \<subseteq> qrstep nfs ?Q (?RS \<union> D)"
    unfolding qrstep_iff_rqrstep_or_nrqrstep  by auto
  from rtrancl_mono[OF this] st
  show ?thesis by blast
qed

    
lemma quasi_lab_root_relto_qnf: 
  assumes nvar: "\<forall>(l,r) \<in> (R \<union> S). is_Fun l"
  and ndef: "\<not> defined (applicable_rules Q (R \<union> S)) (the (root s))"
  and D: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and steps: "(s,t) \<in> (qrstep nfs Q (R \<union> S))^* O qrstep nfs Q R O (qrstep nfs Q (R \<union> S))^*"
  and qmodel_R: "qmodel I L LC C cge R"
  and qmodel_S: "qmodel I L LC C cge S"
  and nf: "t \<in> NF_terms Q"
  and wfass: "wf_ass \<alpha>"
  shows "(Lab_root \<alpha> s,Lab_root \<alpha> t) \<in> Decr_root^= O
  (qrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> Lab_trs S \<union> D))^* O 
  (qrstep nfs (Lab_lhss_all Q) (Lab_trs R)) O 
  (qrstep nfs (Lab_lhss_all Q) (Lab_trs R \<union> Lab_trs S \<union> D))^*"
  (is "?st \<in> _")
proof -
  let ?Q = "Lab_lhss_all Q"
  let ?R = "Lab_trs R"
  let ?RS = "Lab_trs R \<union> Lab_trs S"
  let ?D = "D"
  let ?QD = "nrqrstep nfs ?Q D"
  let ?QR = "nrqrstep nfs ?Q ?R"
  let ?All = "nrqrstep nfs ?Q (?RS \<union> D)"
  let ?Lab = "Lab_root \<alpha>"
  from steps
  obtain u v where steps: "(s,u) \<in> (qrstep nfs Q (R \<union> S))^*" "(u,v) \<in> qrstep nfs Q R" "(v,t) \<in> (qrstep nfs Q (R \<union> S))^*"
    by auto
  from qrsteps_imp_nrqrsteps[OF nvar ndef steps(1)]
  have su: "(s,u) \<in> (nrqrstep nfs Q (R \<union> S))^*" .
  note ndef = ndef[unfolded nrqrsteps_num_args[OF su] nrqrsteps_preserve_root[OF su]]  
  have uv: "(u,v) \<in> nrqrstep nfs Q R"
    by (rule qrstep_imp_nrqrstep[OF _ _ steps(2)], insert nvar ndef, auto simp: applicable_rules_union defined_def)
  note ndef = ndef[unfolded nrqrstep_num_args[OF uv] nrqrstep_preserves_root[OF uv]]
  from qrsteps_imp_nrqrsteps[OF nvar ndef steps(3)]
  have vt: "(v,t) \<in> (nrqrstep nfs Q (R \<union> S))^*" .
  from qmodel_R qmodel_S have qmodel: "qmodel I L LC C cge (R \<union> S)" 
    unfolding qmodel_def by  auto
  note rewrs = quasi_lab_root_rewrites[OF D wf _ qmodel wfass]
  from rewrs[OF _ _ su lge_term_root_refl]
  obtain u' where su: "(?Lab s, u') \<in> ?All^*"
    and u': "lge_term_root u' (?Lab u)" unfolding lab_trs_union by auto
  from quasi_lab_root_rewrite[OF D wf uv qmodel_R wfass u']
  obtain u'' v' where uu: "(u',u'') \<in> ?QD^*" and
    uv: "(u'',v') \<in> ?QR"
    and v': "lge_term_root v' (?Lab v)" by auto
  from rewrs[OF _ _ vt v'] obtain t' where
    vt: "(v',t') \<in> ?All^*" and
    t': "lge_term_root t' (?Lab t)" by auto
  from lge_term_root_decr[OF D wf t' nf]
  have tt: "(t', ?Lab t) \<in> ?QD^* O Decr_root^=" by auto
  from su uu uv vt tt
  have st: "?st \<in> ?All^* O ?QD^* O ?QR O ?All^* O ?QD^* O Decr_root^=" by blast
  have st: "?st \<in> ?All^* O ?QR O ?All^* O Decr_root^="
    by (rule set_mp[OF _ st], unfold nrqrstep_union, regexp)
  from this[simplified nrqrsteps_Decr_root nrqrstep_Decr_root O_assoc[symmetric]]
  have st: "?st \<in> Decr_root^= O ?All^* O ?QR O ?All^*" 
    by (simp add: O_assoc)
  then have "?st \<in> Decr_root^= O (relto (?QR) (?All))" .
  then show ?thesis
    using relto_mono[of ?QR "qrstep nfs ?Q ?R" ?All "qrstep nfs ?Q (?RS \<union> D)"]
    unfolding qrstep_iff_rqrstep_or_nrqrstep by blast
qed  

lemma UNLAB_lab_root: "map_funs_term UNLAB (Lab_root \<alpha> t) = t"
proof (cases t)
  case (Var x) then show ?thesis by auto
next
  case (Fun f ts)
  show ?thesis unfolding Fun lab_root.simps Let_def term.simps map_map o_def
      LD_LC fst_conv using UNLAB_lab[of \<alpha>] 
    by (induct ts, auto)
qed


lemma quasi_lab_root_all_merge: 
  assumes steps: "(Lab_root \<alpha> (t \<cdot> \<sigma>),v) \<in> Decr_root^= O Rel"
  and tv: "is_Fun t"
  and st: "(s,t) \<in> P"
  and wfass: "wf_ass \<alpha>"
  shows "\<exists> lt. (Lab_root (subst_ass \<alpha> \<sigma>) s,lt) \<in> Lab_root_all_trs P \<and>
              (lt \<cdot> lab_subst \<alpha> \<sigma>, v) \<in> Rel \<and> map_funs_term UNLAB (lt \<cdot> lab_subst \<alpha> \<sigma>) = t \<cdot> \<sigma>
              \<and> \<Union>(funas_term ` set (args (lt \<cdot> lab_subst \<alpha> \<sigma>))) \<subseteq> F_all
              \<and> map_funs_term UNLAB lt = t"
proof -
  let ?L = "Lab_root \<alpha>"
  let ?a = "subst_ass \<alpha> \<sigma>"
  let ?\<sigma> = "lab_subst \<alpha> \<sigma>"
  let ?L' = "Lab_root ?a"
  let ?D = "Decr_root^="
  let ?P = "Lab_root_all_trs P"
  let ?m = "map_funs_term UNLAB"
  let ?w = "\<lambda>t. \<Union>(funas_term ` set (args t)) \<subseteq> F_all"
  from steps obtain lu where tu: "(?L (t \<cdot> \<sigma>), lu) \<in> ?D" and uv: "(lu,v) \<in> Rel" by auto
  from tv obtain f ts where t: "t = Fun f ts" by force
  then obtain tss where tsig: "t \<cdot> \<sigma> = Fun f tss" and tss: "tss = map (\<lambda> t. t \<cdot> \<sigma>) ts" by auto
  let ?ls = "?L' s"
  let ?cs = "map (Eval \<alpha>) tss"
  let ?cs' = "map (Eval ?a) ts"
  let ?ltss = "map (Lab \<alpha>) tss"
  let ?n = "length tss"
  let ?f = "LC f ?n (L' f ?cs)"
  let ?lts = "Fun ?f ?ltss"
  have ltsig: "?L (t \<cdot> \<sigma>) = ?lts" unfolding tsig by (auto simp: o_def)
  have ltsig': "?L (t \<cdot> \<sigma>) = ?L' t \<cdot> ?\<sigma>" unfolding lab_root_subst[OF tv] ..
  have wfa: "wf_ass ?a" by (rule wf_ass_subst_ass[OF wfass])
  have cs': "set ?cs' \<subseteq> C"
    using wf_term[OF wfa] by auto
  have L': "LS' f (length ts) (L' f ?cs')"
    by (rule wf_L'[unfolded wf_label_def, THEN spec[of _ f], THEN spec[of _ ?cs'], THEN mp, unfolded length_map], rule cs')
  have wftss:"\<And> t. t \<in> set (map (Lab \<alpha>) tss) \<Longrightarrow> funas_term t \<subseteq> F_all"
    using wf_lab[OF wfass] by force
  show ?thesis
  proof (cases "?L (t \<cdot> \<sigma>) = lu")
    assume id: "?L (t \<cdot> \<sigma>) = lu"
    have rel: "(?L' t \<cdot> ?\<sigma>,v) \<in> Rel"
      using uv unfolding ltsig'[symmetric] id by auto
    have P: "(?L' s, ?L' t) \<in> ?P"
    proof(rule, rule, rule refl, rule st, unfold lab_root_all_rule_def, rule,
      intro exI conjI, unfold fst_conv snd_conv, rule refl, rule wfa)
      show "?L' t \<in> Lab_root_all ?a t"
        unfolding t 
        by (simp add: o_def, intro exI conjI, rule refl, rule lge_refl, rule L')
    qed
    show "\<exists> lt. (?L' s, lt) \<in> ?P \<and> (lt \<cdot> ?\<sigma>,v) \<in> Rel \<and> ?m (lt \<cdot> ?\<sigma>) = t \<cdot> \<sigma> \<and> ?w (lt \<cdot> ?\<sigma>) \<and> ?m lt = t" 
      by (intro exI conjI, rule P, rule rel, 
        unfold ltsig'[symmetric], rule UNLAB_lab_root, 
        unfold ltsig, insert wftss, force, rule UNLAB_lab_root)
  next
    assume "?L (t \<cdot> \<sigma>) \<noteq> lu"    
    with tu have "(?L (t \<cdot> \<sigma>), lu) \<in> Decr_root" by simp
    from this[unfolded ltsig decr_of_ord_def]
    obtain g l l' 
      where f: "?f = LC g (length ?ltss) l" and lu: "lu = Fun (LC g (length ?ltss) l') ?ltss" and inLS: "LS' g (length ?ltss) l" "LS' g (length ?ltss) l'" 
      and gr: "(l,l') \<in> gr_root g (length ?ltss)" by auto
    from arg_cong[OF f, of LD, unfolded LD_LC]
    have gf: "g = f" and l: "l = L' f ?cs" by auto
    have L't: "?L' t = Fun ?f (map (Lab ?a) ts)" unfolding t lab_root.simps Let_def map_map o_def tss by simp
    note L't =  L't[unfolded f gf tss length_map]
    then have L't: "?L' t = Fun (LC f (length ts) l) (map (Lab ?a) ts)"
      unfolding l tss .
    let ?t = "Fun (LC f (length ts) l') (map (Lab ?a) ts)"
    have tu: "?t \<cdot> ?\<sigma> = lu" unfolding lu tss gf by auto
    show "\<exists> lt. (?L' s, lt) \<in> ?P \<and> (lt \<cdot> ?\<sigma>,v) \<in> Rel \<and> ?m (lt \<cdot> ?\<sigma>) = t \<cdot> \<sigma> \<and> ?w (lt \<cdot> ?\<sigma>) \<and> ?m lt = t" 
    proof (rule exI[of _ ?t], intro conjI)
      show "(?t \<cdot> ?\<sigma>,v) \<in> Rel" unfolding tu by (rule uv)
    next
      show "(?L' s, ?t) \<in> ?P"
      proof (rule, rule, rule refl, rule st,
          unfold lab_root_all_rule_def, rule,
      intro exI conjI, unfold fst_conv snd_conv, rule refl, rule wfa)
        show "?t \<in> Lab_root_all ?a t"
          unfolding t lab_root_all.simps Let_def
        proof (rule, intro exI conjI, unfold map_map o_def, rule refl)
          have id: "L' f ?cs' = l" unfolding l tss map_map o_def by auto
          show "lge f (length ts) (L' f ?cs') l'" unfolding id
            using gr[unfolded gf tss length_map] 
            unfolding lge_to_lgr_rel_def lge_to_lgr_def Let_def by auto
        qed
      qed
    next
      show "?w (?t \<cdot> ?\<sigma>)" 
        unfolding tu lu using wftss by force
    next
      show "?m (?t \<cdot> ?\<sigma>) = t \<cdot> \<sigma>"
        unfolding tu lu term.simps map_map t tss LD_LC gf fst_conv o_def UNLAB_lab
        by auto
    next
      show "?m ?t  = t "
        unfolding tu lu term.simps map_map t tss LD_LC gf fst_conv o_def UNLAB_lab
        by auto
    qed 
  qed
qed


lemma lab_nf_root: 
  assumes nf: "s \<in> NF_terms Q"
  shows "Lab_root \<alpha> s \<in> NF_terms (Lab_lhss_all Q)"
proof(rule, rule) 
  fix t
  assume "(Lab_root \<alpha> s, t) \<in> rstep (Id_on (Lab_lhss_all Q))"
  from rstep_imp_map_rstep[OF this, of UNLAB, unfolded UNLAB_lab_root]
  have step: "(s, map_funs_term UNLAB t) \<in> rstep (map_funs_trs UNLAB (Id_on (Lab_lhss_all Q)))" (is "?p \<in> rstep ?Q") .
  have subset: "?Q \<subseteq> Id_on Q"
  proof -
    {
      fix l r
      assume "(l,r) \<in> ?Q"
      then obtain q where "q \<in> Lab_lhss_all Q" and "l = map_funs_term UNLAB q" and "r = map_funs_term UNLAB q"
        by (force simp: map_funs_trs.simps)
      then have "(l,r) \<in> Id_on Q" by auto
    }
    then show ?thesis by auto
  qed
  from rstep_mono[OF subset] step
  have "(s, map_funs_term UNLAB t) \<in> rstep (Id_on Q)" by auto
  with nf show False
    by auto
qed
end

text \<open>towards minimality\<close>

context sl_interpr
begin

lemma lab_subst_inj: assumes inj: "\<And> f. inj (L f)"
  and x: "x \<in> vars_term t"
  and nv: "is_Fun t"
  and diff: "\<alpha> x \<noteq> \<alpha>' x"
  shows "Lab \<alpha> t \<cdot> \<sigma> \<noteq> Lab \<alpha>' t \<cdot> \<sigma>'"
  using nv x
proof (induct t)
  case (Var y) 
  then show ?case by auto
next
  case (Fun f ts) note oFun = this
  from Fun(3) obtain t where t: "t \<in> set ts" and x: "x \<in> vars_term t"    
    by auto
  from t obtain i where i: "i < length ts" and ti: "ts ! i = t" 
    unfolding set_conv_nth by auto
  from id_take_nth_drop[OF i] ti have ts: "Fun f ts = Fun f (take i ts @ t # drop (Suc i) ts)"
    by auto  
  show ?case
  proof (cases t)
    case (Fun g ss)
    then have "is_Fun t" by auto
    from oFun(1)[OF t this x]
    show ?thesis unfolding ts
      by (auto simp: Let_def)
  next
    case (Var y)
    with x have t: "t = Var x" by auto
    from i have i: "min (length ts) i = i" 
      "Suc (i + (length ts - Suc i)) = length ts" by auto
    show ?thesis 
    proof (rule ccontr)
      assume eq: "\<not> ?thesis"
      let ?n = "length ts"
      let ?bef = "take i ts"
      let ?aft = "drop (Suc i) ts"
      from eq have "LC f ?n (L f (map (Eval \<alpha>) ?bef @ \<alpha> x # map (Eval \<alpha>) ?aft)) =
             LC f ?n (L f (map (Eval \<alpha>') ?bef @ \<alpha>' x # map (Eval \<alpha>') ?aft))" 
        (is "LC f ?n ?l = LC f ?n ?r")
        by (auto simp: ts t Let_def o_def i)
      then have "LD (LC f ?n ?l) = LD (LC f ?n ?r)" by auto
      from this[unfolded LD_LC] have eq: "?l = ?r" by simp
      with inj[unfolded inj_on_def, THEN bspec, THEN bspec, THEN mp[OF _ eq]] have "\<alpha> x = \<alpha>' x" by auto
      with diff show False by auto
    qed
  qed
qed    

fun eval_lab_ctxt :: "('v,'c)assign \<Rightarrow> 'c \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('c \<times> ('lf,'v)ctxt)" 
where "eval_lab_ctxt \<alpha> d Hole = (d, Hole)"
  |   "eval_lab_ctxt \<alpha> d (More f bef C' aft) = 
     (let clbef = map (eval_lab I L LC \<alpha>) bef;
          claft = map (eval_lab I L LC \<alpha>) aft;
          cl = eval_lab_ctxt \<alpha> d C';
          cs = map fst (clbef) @ fst cl # map fst claft;
          c = I f cs;
          lbef = map snd clbef;
          laft = map snd claft in
     (c, More (LC f (Suc (length bef + length aft)) (L f cs)) lbef (snd cl) laft))"

lemma eval_ctxt: "Eval \<alpha> (D\<langle>t\<rangle>) = fst (eval_lab_ctxt \<alpha> (Eval \<alpha> t) D)"
  by (induct D, auto simp: Let_def) 

lemma lab_ctxt: "Lab \<alpha> (D\<langle>t\<rangle>) = (snd (eval_lab_ctxt \<alpha> (Eval \<alpha> t) D))\<langle>Lab \<alpha> t\<rangle>"
  by (induct D, auto simp: Let_def o_def eval_ctxt) 

lemma lab_UNLAB:
  assumes t: "Lab \<alpha> t = u"
  shows "Lab \<alpha> (map_funs_term UNLAB u) = u"
proof -
  from t have "Lab \<alpha> (map_funs_term UNLAB (Lab \<alpha> t)) = Lab \<alpha> (map_funs_term UNLAB u)"
    by simp
  from this[unfolded UNLAB_lab, unfolded t] show ?thesis ..
qed
      
lemma lab_ctxt_split: 
  assumes  "Lab \<alpha> t = D\<langle>u\<rangle>"
  shows "Lab \<alpha> (map_funs_term UNLAB u) = u \<and> snd (eval_lab_ctxt \<alpha> (Eval \<alpha> (map_funs_term UNLAB u)) (map_funs_ctxt UNLAB D)) = D"
  using assms
proof (induct D arbitrary: t)
  case Hole
  then have "Lab \<alpha> t = u" by simp
  from lab_UNLAB[OF this]
  show ?case by simp
next
  case (More f bef D aft)
  from More(2) obtain g ts where t: "t = Fun g ts" by (cases t, auto)
  note More = More[unfolded t]
  from More(2)
  have f: "f = LC g (length ts) (L g (map (Eval \<alpha>) ts))"
    and ts: "map (Lab \<alpha>) ts = bef @ D\<langle>u\<rangle> # aft" (is "?ts = ?bua")
    by (auto simp: Let_def o_def)
  from arg_cong[OF ts,of length] 
  have len: "length ts = Suc (length bef + length aft)" by auto
  note ts' = ts[unfolded list_eq_iff_nth_eq, THEN conjunct2, THEN spec, THEN mp, unfolded length_map]
  let ?m = "length bef"
  from len have m: "?m < length ts" by auto
  from arg_cong[OF ts, of "\<lambda> x. x ! ?m"] m 
  have tu: "Lab \<alpha> (ts ! ?m) = D\<langle>u\<rangle>" by auto  
  from More(1)[OF this] have one: "Lab \<alpha> (map_funs_term UNLAB u) = u"
    and two: "snd (eval_lab_ctxt \<alpha> (Eval \<alpha> (map_funs_term UNLAB u)) (map_funs_ctxt UNLAB D)) = D" by auto
  let ?map = "map (\<lambda> x. Lab \<alpha> (map_funs_term UNLAB x))"
  have bef: "?map bef = bef"
  proof (rule nth_equalityI, simp, unfold length_map)
    fix i
    assume i: "i < ?m"
    with len have i': "i < length ts" by auto
    have "?map bef ! i = Lab \<alpha> (map_funs_term UNLAB (bef ! i))" using i by auto
    also have "... = bef ! i"
    proof (rule lab_UNLAB)
      show "Lab \<alpha> (ts ! i) = bef ! i"
        using ts'[OF i'] i' i 
        by (auto simp: nth_append)
    qed
    finally show "?map bef ! i = bef ! i" .
  qed
  have aft: "?map aft = aft"
  proof (rule nth_equalityI, simp, unfold length_map)
    fix i
    assume i: "i < length aft"
    let ?i = "Suc (?m + i)"
    from i len have i': "?i < length ts" by auto
    have "?map aft ! i = Lab \<alpha> (map_funs_term UNLAB (aft ! i))" using i by auto
    also have "... = aft ! i"
    proof (rule lab_UNLAB)
      show "Lab \<alpha> (ts ! ?i) = aft ! i"
        using ts'[OF i'] i' i 
        by (auto simp: nth_append)
    qed
    finally show "?map aft ! i = aft ! i" .
  qed
  show ?case
  proof (rule conjI[OF one], simp add: Let_def o_def two bef aft)
    let ?n = "Suc (?m + length aft)"
    let ?ma = "map (\<lambda> x. Eval \<alpha> (map_funs_term UNLAB x))"
    let ?ctxt = "eval_lab_ctxt \<alpha> (Eval \<alpha> (map_funs_term UNLAB u)) (map_funs_ctxt UNLAB D)"
    let ?cs = "?ma bef @ fst ?ctxt # ?ma aft"
    have ld_f: "LD f = (UNLAB f, snd (LD f))" by simp
    with arg_cong[OF f, of LD, unfolded LD_LC] have
      g: "UNLAB f = g" and Lg: "L g (map (Eval \<alpha>) ts) = snd (LD f)" by auto
    show "LC (UNLAB f) ?n (L (UNLAB f) ?cs) = f" unfolding g 
      unfolding f len
    proof (rule arg_cong[where f = "LC g ?n"], rule arg_cong[where f = "L g"])
      {
        fix i
        assume i: "i < ?n"
        then have i': "i < length (bef @ D\<langle>u\<rangle> # aft)" by simp
        from ts have ts': "map (Eval \<alpha>) (map (map_funs_term UNLAB) ?ts) ! i
          = map (Eval \<alpha>) (map (map_funs_term UNLAB) ?bua) ! i" (is "?l = ?r") by simp        from i have "map (Eval \<alpha>) ts ! i = ?l" using len
          by (simp add: UNLAB_lab)
        also have "... = Eval \<alpha> (map_funs_term UNLAB (?bua ! i))" unfolding ts'
          unfolding map_map
          unfolding nth_map[OF i'] by (simp add: o_def)        
        also have "... = ?cs ! i"
        proof (cases "i < ?m")
          case True
          then show ?thesis 
            by (auto simp: nth_append)
        next
          case False
          show ?thesis
          proof (cases "i - ?m")
            case (Suc j)
            with i have "j < length aft" by auto
            with Suc show ?thesis using False
              by (auto simp: nth_append)
          next
            case 0
            with False have i: "i = ?m" by simp
            show ?thesis unfolding i
              by (simp add: nth_append eval_ctxt)
          qed
        qed
        finally 
        have "?cs ! i = map (Eval \<alpha>) ts ! i" by simp
      } note main = this
      show "?cs = map (Eval \<alpha>) ts" 
        by (rule nth_equalityI, insert main len, auto)
    qed
  qed
qed


lemma lab_nf_rev: 
  assumes nf: "Lab \<alpha> s \<in> NF_terms (Lab_lhss Q)" and wf: "wf_ass \<alpha>"
  shows "s \<in> NF_terms Q"
  unfolding NF_ctxt_subst 
proof(rule,rule)
  assume "\<exists> C q \<sigma>. s = C\<langle>q \<cdot> \<sigma>\<rangle> \<and> q \<in> Q"
  then obtain C q \<sigma> where s: "s = C\<langle>q\<cdot>\<sigma>\<rangle>" and q: "q \<in> Q" by auto 
  let ?\<sigma> = "lab_subst \<alpha> \<sigma>"
  let ?q = "Lab (subst_ass \<alpha> \<sigma>) q"
  let ?Q = "Lab_lhss Q"
  obtain D where D: "Lab \<alpha> s = D\<langle>?q\<cdot>?\<sigma>\<rangle>" unfolding s
    unfolding lab_ctxt by auto
  have q: "?q \<in> ?Q" 
    by (auto simp: lab_lhs_def, rule bexI[OF _ q], rule exI[of _ "subst_ass \<alpha> \<sigma>"], auto simp: wf)
  have "Lab \<alpha> s \<notin> NF_terms ?Q"
    unfolding D NF_ctxt_subst
    using q by auto
  then show False using nf by auto
qed
end

lemma eval_lab_independent:
  fixes t::"('f,'v)term" and I::"('f,'c)inter"
  assumes "\<forall>x\<in>vars_term t. \<alpha> x = \<beta> x"
  shows "eval_lab I L LC \<alpha> t = eval_lab I L LC \<beta> t"
using assms
proof (induct t, simp)
  case (Fun f ts)
  then have map: "map (eval_lab I L LC \<alpha>) ts = map (eval_lab I L LC \<beta>) ts" by auto
  then show ?case by (auto simp: Let_def map)
qed

lemma lab_root_independent:
  fixes t::"('f,'v)term" and I::"('f,'c)inter"
  assumes vars: "\<forall>x\<in>vars_term t. \<alpha> x = \<beta> x"
  shows "lab_root I L L' LC \<alpha> t = lab_root I L L' LC \<beta> t"
proof (cases t, simp)
  case (Fun f ts)
  from vars[unfolded Fun] have vars: "\<And> t . t \<in> set ts \<Longrightarrow> (\<forall> x \<in> vars_term t. \<alpha> x = \<beta> x)" by auto
  from eval_lab_independent[OF vars]
  have map: "map (eval_lab I L LC \<alpha>) ts = map (eval_lab I L LC \<beta>) ts" by auto
  show ?thesis unfolding Fun by (auto simp: Let_def map)
qed


context sl_interpr
begin

lemma inj_step: assumes inj: "\<And> f. inj (L f)"
  and step: "(Lab \<alpha> t,u) \<in> qrstep nfs (Lab_lhss Q) (Lab_trs R)"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
  and SN: "\<not> SN_on (qrstep nfs Q R) {t} \<Longrightarrow> wwf_qtrs Q R"
  and model: "qmodel I L LC C cge R"
  and cge: "cge = (=)"
  and wf: "wf_ass \<alpha>"
  shows "\<exists> s. (t,s) \<in> qrstep nfs Q R \<and> u = Lab \<alpha> s"
proof -
  from wwf_qtrs_imp_nfs_False_switch[OF wwf] have switch: "qrstep nfs Q R = qrstep False Q R" by blast
  from step obtain C \<sigma> ll lr where id: "Lab \<alpha> t = C\<langle>ll\<cdot>\<sigma>\<rangle>" "u = C\<langle>lr\<cdot>\<sigma>\<rangle>" and llr: "(ll,lr) \<in> Lab_trs R" and NF: "\<forall> u \<lhd> ll \<cdot> \<sigma>. u \<in> NF_terms (Lab_lhss Q)" by (induct, auto)
  from llr obtain l r \<beta> where lr: "(l,r) \<in> R" and llr: "ll = Lab \<beta> l" "lr = Lab \<beta> r" and beta: "wf_ass \<beta>" by (force simp: lab_rule_def)  
  note id1 = lab_ctxt_split[OF id(1), unfolded llr]
  let ?C = "snd (eval_lab_ctxt \<alpha> (Eval \<alpha> (map_funs_term UNLAB (Lab \<beta> l \<cdot> \<sigma>))) (map_funs_ctxt UNLAB C))"
  let ?\<sigma> = "map_funs_subst UNLAB \<sigma>"
  have nf: "\<forall> u \<lhd> l \<cdot> ?\<sigma>. u \<in> NF_terms Q" 
  proof (intro allI impI)
    fix u
    assume u: "l \<cdot> ?\<sigma> \<rhd> u"
    then obtain D where D: "D \<noteq> \<box>" and u: "l \<cdot> ?\<sigma> = D\<langle>u\<rangle>" by (rule supt_ctxtE)
    show "u \<in> NF_terms Q"        
    proof (rule lab_nf_rev, rule NF[THEN spec, THEN mp], unfold llr)        
      let ?D = "snd (eval_lab_ctxt \<alpha> (Eval \<alpha> u) D)"
      show "Lab \<beta> l \<cdot> \<sigma> \<rhd> Lab \<alpha> u"
      proof (rule ctxt_supt)
        have "Lab \<beta> l \<cdot> \<sigma> = Lab \<alpha> (l \<cdot> ?\<sigma>)"
          using id1 by (auto simp: UNLAB_lab)
        also have "... = Lab \<alpha> (D\<langle>u\<rangle>)" unfolding u ..
        also have "... = ?D\<langle>Lab \<alpha> u\<rangle>" (is "_ = ?r") unfolding lab_ctxt ..
        finally show "Lab \<beta> l \<cdot> \<sigma> = ?r" .
      next
        from D show "?D \<noteq> \<box>" by (cases D, auto simp: Let_def)
      qed
    next
      show "wf_ass \<alpha>" by (rule wf)
    qed
  qed  
  have "(map_funs_term UNLAB (Lab \<alpha> t), map_funs_term UNLAB u) \<in> qrstep nfs Q R" unfolding switch
  proof (rule qrstepI[OF _ lr], unfold id llr map_funs_term_ctxt_distrib map_funs_subst_distrib UNLAB_lab)
    show "(map_funs_ctxt UNLAB C)\<langle>l \<cdot> ?\<sigma>\<rangle> = (map_funs_ctxt UNLAB C)\<langle>l \<cdot> ?\<sigma>\<rangle>" ..
  next
    show "\<forall>u\<lhd>l \<cdot> map_funs_subst UNLAB \<sigma>. u \<in> NF_terms Q" by (rule nf)
  qed auto
  then have step: "(t, map_funs_term UNLAB u) \<in> qrstep nfs Q R" unfolding UNLAB_lab .
  have wwf: "wwf_rule Q (l,r)"
  proof (cases "wwf_qtrs Q R")
    case True
    with lr show ?thesis unfolding wwf_qtrs_def wwf_rule_def by auto
  next
    case False
    from False SN have "SN_on (qrstep nfs Q R) {t}" by auto
    then have SN: "SN_on (qrstep False Q R) {t}" unfolding switch by auto
    show ?thesis
      by (rule SN_on_imp_wwf_rule[OF SN _ lr nf, unfolded arg_cong[OF id(1), of "map_funs_term UNLAB", unfolded UNLAB_lab]], unfold llr, auto simp: UNLAB_lab)
  qed
  show ?thesis
  proof (intro exI conjI, rule step, unfold id llr)    
    show "C\<langle>Lab \<beta> r \<cdot> \<sigma>\<rangle> = Lab \<alpha> (map_funs_term UNLAB C\<langle>Lab \<beta> r \<cdot> \<sigma>\<rangle>)"
    proof -
      let ?D = "snd (eval_lab_ctxt \<alpha> (Eval \<alpha> (map_funs_term UNLAB (Lab \<beta> r \<cdot> \<sigma>))) (map_funs_ctxt UNLAB C))"
      from model[unfolded qmodel_def, THEN bspec[OF _ lr], unfolded split cge]
      have eval: "\<And> \<alpha>. wf_ass \<alpha> \<Longrightarrow> Eval \<alpha> l = Eval \<alpha> r" by simp
      have CD: "?C = ?D"        
        by (rule arg_cong[where f = "\<lambda>x. snd (eval_lab_ctxt \<alpha> x (map_funs_ctxt UNLAB C))"], unfold map_funs_subst_distrib eval_subst UNLAB_lab, rule eval, simp add: wf)
      have "Lab \<alpha> (map_funs_term UNLAB C\<langle>Lab \<beta> r \<cdot> \<sigma>\<rangle>) = Lab \<alpha> ((map_funs_ctxt UNLAB C) \<langle>r \<cdot> ?\<sigma>\<rangle>)" 
        unfolding map_funs_term_ctxt_distrib map_funs_subst_distrib UNLAB_lab by simp
      also have "... = ?D\<langle>Lab \<alpha> (r \<cdot> ?\<sigma>)\<rangle>" unfolding lab_ctxt 
        unfolding map_funs_subst_distrib UNLAB_lab ..
      also have "... = ?C\<langle>Lab \<alpha> (r \<cdot> ?\<sigma>)\<rangle>" unfolding CD ..
      also have "... = C\<langle>Lab \<alpha> (r \<cdot> ?\<sigma>)\<rangle>" using id1 by simp
      also have "... = C\<langle>Lab \<beta> r \<cdot> \<sigma>\<rangle>" 
        unfolding ctxt_eq lab_subst
      proof -
        let ?\<alpha> = "subst_ass \<alpha> ?\<sigma>"
        let ?\<tau> = "lab_subst \<alpha> ?\<sigma>"        
        from id1 have idl: "Lab ?\<alpha> l \<cdot> ?\<tau> = Lab \<beta> l \<cdot> \<sigma>" 
          by (simp add: UNLAB_lab)
        from wwf[unfolded wwf_rule_def, THEN mp[OF _ only_applicable_rules[OF nf]]]
        have nvar: "is_Fun l" and rl: "vars_term r \<subseteq> vars_term l" by auto
        {
          fix x
          assume x: "x \<in> vars_term l"
          have "?\<alpha> x = \<beta> x"
            using lab_subst_inj[OF inj x nvar, of ?\<alpha> \<beta> ?\<tau> \<sigma>] idl
            by auto
        } note alpha_beta = this
        then have abl: "\<forall> x \<in> vars_term l. ?\<alpha> x = \<beta> x" by auto
        then have abr: "\<forall> x \<in> vars_term r. ?\<alpha> x = \<beta> x" using rl by auto
        from eval_lab_independent[OF abl, of I L LC] 
        have l: "Lab ?\<alpha> l = Lab \<beta> l" by simp 
        from eval_lab_independent[OF abr, of I L LC] 
        have r: "Lab ?\<alpha> r = Lab \<beta> r" by simp 
        show "Lab ?\<alpha> r \<cdot> ?\<tau> = Lab \<beta> r \<cdot> \<sigma>" unfolding r
          by (rule vars_term_subset_subst_eq [OF _ idl [unfolded l]], unfold vars_term_lab, 
            rule rl)
      qed        
      finally show ?thesis by simp
    qed
  qed
qed

lemma SN_inj:
  assumes inj: "\<And> f. inj (L f)"
   and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
   and SN: "SN_on (qrstep nfs Q R) {t}"
   and model: "qmodel I L LC C cge R"
   and cge: "cge = (=)"
   and wf: "wf_ass \<alpha>"
   and LQ: "NF_terms (Lab_lhss Q) \<supseteq> NF_terms LQ"
  shows "SN_on (qrstep nfs LQ (Lab_trs R)) {Lab \<alpha> t}" 
proof -
  let ?QR = "qrstep nfs (Lab_lhss Q) (Lab_trs R)"
  {
    fix f
    assume f0: "f 0 = Lab \<alpha> t" and "\<forall> i. (f i, f (Suc i)) \<in> ?QR"
    then have steps: "\<And> i. (f i, f (Suc i)) \<in> ?QR" by auto
    note main =  inj_step[OF inj _ wwf _ model cge wf]
    obtain g where g: "g = (\<lambda> n. Semantic_Labeling.aux (\<lambda> (pt,t,i). ((pt,t) \<in> qrstep nfs Q R \<and> f i = Lab \<alpha> t)) n t)" by auto
    {
      fix i
      have "(i > 0 \<longrightarrow> (g (i - 1), g i) \<in> qrstep nfs Q R) \<and> Lab \<alpha> (g i) = f i \<and> SN_on (qrstep nfs Q R) {g i}"
      proof (induct i)
        case 0 
        show ?case by (auto simp: f0 g SN)
      next
        case (Suc i)
        then have id: "f i = Lab \<alpha> (g i)" and SN: "SN_on (qrstep nfs Q R) {g i}" by auto
        from someI_ex[OF main[OF steps[of i, unfolded id] ]] SN
        have gsi: "(g i, g (Suc i)) \<in> qrstep nfs Q R" and fsi: "f (Suc i) = Lab \<alpha> (g (Suc i))"
          unfolding g aux.simps by auto
        from step_preserves_SN_on[OF gsi SN] gsi fsi 
        show ?case by auto
      qed
      then have "i > 0 \<longrightarrow> (g (i - 1), g i) \<in> qrstep nfs Q R" by simp
    }
    then have "\<And> i. (g i, g (Suc i)) \<in> qrstep nfs Q R" by force
    then have "\<not> SN_on (qrstep nfs Q R) {g 0}" by auto
    with SN have False unfolding g by auto
  }
  then have SN: "SN_on ?QR {Lab \<alpha> t}" unfolding SN_on_def by blast
  show ?thesis
    by (rule SN_on_subset1[OF SN qrstep_mono[OF _ LQ]], auto)
qed
end


context sl_interpr
begin
definition Lab_all_trs :: "('f,'v)trs \<Rightarrow> ('lf,'v)trs"
  where "Lab_all_trs R \<equiv> {(l,r) | l r. funas_term r \<subseteq> F_all \<and> (map_funs_term UNLAB l, map_funs_term UNLAB r) \<in> R}"

definition Lab_lhss_more :: "('f,'v)terms \<Rightarrow> ('lf,'v)terms"
  where "Lab_lhss_more Q \<equiv> { l. funas_term l \<subseteq> F_all \<and> map_funs_term UNLAB l \<in> Q}"

lemma Lab_lhss_more: "Lab_lhss Q \<subseteq> Lab_lhss_more Q" "Lab_lhss_more Q \<subseteq> Lab_lhss_all Q"
proof -
  show "Lab_lhss Q \<subseteq> Lab_lhss_more Q" 
  proof
    fix x 
    assume "x \<in> Lab_lhss Q"
    then obtain q where q: "q \<in> Q" and x: "x \<in> lab_lhs I L LC C q" by auto
    then obtain a where x: "x = Lab a q" and a: "wf_ass a" unfolding lab_lhs_def by auto
    show "x \<in> Lab_lhss_more Q" unfolding x Lab_lhss_more_def using wf_lab[OF a, of q] UNLAB_lab[of a q] q by auto
  qed
next
  show "Lab_lhss_more Q \<subseteq> Lab_lhss_all Q" unfolding Lab_lhss_more_def by auto
qed

lemma NF_unlab: assumes NF: "s \<in> NF_terms LQ"
  and wf: "funas_term s \<subseteq> F_all"
  and LQ: "NF_terms (Lab_lhss_more Q) \<supseteq> NF_terms LQ"
  and Q: "\<And> q. q \<in> Q \<Longrightarrow> linear_term q"
  shows "map_funs_term UNLAB s \<in> NF_terms Q"
proof -
  let ?m = "map_funs_term UNLAB"
  let ?LQ = "Lab_lhss_more Q"
  from LQ NF have NF: "s \<in> NF_terms ?LQ" by auto
  show ?thesis
  proof (rule ccontr)
    assume "?m s \<notin> NF_terms Q"
    then show False
    proof (rule not_NF_termsE)
      fix q C \<sigma>
      assume q: "q \<in> Q" and m: "?m s = C\<langle>q \<cdot> \<sigma>\<rangle>"
      from Q[OF q] have lin: "linear_term q" by auto
      from map_funs_term_ctxt_decomp[OF m] obtain D u where C: "C = map_funs_ctxt UNLAB D"
        and q\<sigma>: "?m u = q \<cdot> \<sigma>" and s: "s = D\<langle>u\<rangle>" by auto
      from map_funs_subst_split[OF q\<sigma> lin]
      obtain t \<tau> where u: "u = t \<cdot> \<tau>" and qt: "q = ?m t" and vars: "\<And> x. x \<in> vars_term q \<Longrightarrow> ?m (\<tau> x) = \<sigma> x" by auto
      note NF = NF[unfolded s u]
      note wf = wf[unfolded s u]
      from wf q qt
      have "t \<in> ?LQ" unfolding funas_term_ctxt_apply funas_term_subst unfolding Lab_lhss_more_def by auto
      with NF show False by auto
    qed
  qed
qed

lemma wf_Lab_all_trs: assumes "(l,r) \<in> Lab_all_trs R"
  shows "funas_term r \<subseteq> F_all"
  using assms
  unfolding Lab_all_trs_def by auto


lemma wf_Decr: 
  assumes wf: "funas_term lt \<subseteq> F_all"
  and     d: "(lt,ls) \<in> qrstep nfs Q Decr"
  shows "funas_term ls \<subseteq> F_all"
  using d
proof 
  fix C \<sigma> l r 
  assume d: "(l,r) \<in> Decr" and lt: "lt = C\<langle>l\<cdot>\<sigma>\<rangle>" and ls: "ls = C\<langle>r \<cdot> \<sigma>\<rangle>"
  from d[unfolded decr_of_ord_def] obtain f l1 l2 ts where 
    l: "l = Fun (LC f (length ts) l1) ts" and r: "r = Fun (LC f (length ts) l2) ts"
    and l2: "LS f (length ts) l2" by auto
  then have vars: "vars_term l = vars_term r" by auto
  show ?thesis using wf unfolding ls lt unfolding funas_term_ctxt_apply funas_term_subst vars
    unfolding l r using l2 by auto
qed

lemma wf_Decr_args: 
  assumes wf: "\<Union>(funas_term ` set (args lt)) \<subseteq> F_all"
  and     d: "(lt,ls) \<in> qrstep nfs Q Decr"
  shows "\<Union>(funas_term ` set (args ls)) \<subseteq> F_all"
  using d
proof 
  fix C \<sigma> l r 
  assume d: "(l,r) \<in> Decr" and lt: "lt = C\<langle>l\<cdot>\<sigma>\<rangle>" and ls: "ls = C\<langle>r \<cdot> \<sigma>\<rangle>"
    and NF: "\<forall> u \<lhd> l\<cdot>\<sigma>. u \<in> NF_terms Q"
  from d[unfolded decr_of_ord_def] obtain f l1 l2 ts where 
    l: "l = Fun (LC f (length ts) l1) ts" and r: "r = Fun (LC f (length ts) l2) ts"
    and l2: "LS f (length ts) l2" by auto
  then have vars: "vars_term l = vars_term r" by auto
  show "\<Union>(funas_term ` set (args ls)) \<subseteq> F_all"
  proof (cases C)
    case Hole
    show ?thesis using wf unfolding ls lt Hole l r by auto
  next
    case (More g bef D aft)
    from wf have "funas_term (D\<langle>l\<cdot>\<sigma>\<rangle>) \<subseteq> F_all" unfolding lt  More by auto
    then have "funas_term (D\<langle>r\<cdot>\<sigma>\<rangle>) \<subseteq> F_all" unfolding funas_term_ctxt_apply funas_term_subst  vars
      unfolding l r  using l2 by auto
    then show ?thesis using wf unfolding ls lt More by auto
  qed
qed
  
lemma step_imp_UNLAB_step: assumes LR: "LR \<subseteq> Lab_all_trs R"
  and lin: "\<And> q. q \<in> Q \<Longrightarrow> linear_term q"
  and wfs:  "\<Union>(funas_term ` set (args s)) \<subseteq> F_all"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
  and SN: "\<not> SN_on (qrstep nfs Q R) {map_funs_term UNLAB s} \<Longrightarrow> wwf_qtrs Q R"
  and LQ: "NF_terms (Lab_lhss_more Q) \<supseteq> NF_terms LQ"
  and step: "(s,t) \<in> qrstep nfs LQ LR"
  shows "(map_funs_term UNLAB s, map_funs_term UNLAB t) \<in> qrstep nfs Q R \<and> \<Union>(funas_term ` set (args t)) \<subseteq> F_all \<and> (funas_term s \<subseteq> F_all \<longrightarrow> funas_term t \<subseteq> F_all)"
proof -
  from wwf_qtrs_imp_nfs_False_switch[OF wf] have switch: "qrstep nfs Q R = qrstep False Q R" by blast
  let ?Q = "Lab_lhss_more Q"
  let ?m = "map_funs_term UNLAB"
  from qrstep_mono[OF LR LQ] step 
  have "(s,t) \<in> qrstep nfs ?Q (Lab_all_trs R)" by auto
  from this[unfolded qrstep_rule_conv[where R = "Lab_all_trs R"]]
  obtain l r where lr: "(l,r) \<in> Lab_all_trs R" and step: "(s,t) \<in> qrstep nfs ?Q {(l,r)}" by auto
  from step obtain C \<sigma> where s: "s = C\<langle>l\<cdot>\<sigma>\<rangle>" and t: "t = C\<langle>r\<cdot>\<sigma>\<rangle>" and NF: "\<forall> u \<lhd> l \<cdot> \<sigma>. u \<in> NF_terms ?Q" 
    and nfs: "NF_subst nfs (l,r) \<sigma> ?Q" by auto
  have mlr: "(?m l, ?m r) \<in> R" "(?m l, ?m r) \<in> {(?m l, ?m r)}" using lr[unfolded Lab_all_trs_def] by auto
  have mnf: "\<forall>u\<lhd>map_funs_term UNLAB l \<cdot> map_funs_subst UNLAB \<sigma>. u \<in> NF_terms Q" unfolding map_funs_subst_distrib[symmetric]
  proof (intro allI impI)
    fix u
    assume "?m (l \<cdot> \<sigma>) \<rhd> u"
    then show "u \<in> NF_terms Q"
    proof
      fix D
      assume D: "D \<noteq> \<box>" and mls: "?m (l \<cdot> \<sigma>) = D\<langle>u\<rangle>"
      from map_funs_term_ctxt_decomp[OF mls] obtain E v where DE: "D = map_funs_ctxt UNLAB E"
        and u: "u = ?m v" and l\<sigma>: "l \<cdot> \<sigma> = E\<langle>v\<rangle>" by auto
      from D DE have E: "E \<noteq> \<box>" by (cases E, auto)
      obtain CE where CE: "CE = C \<circ>\<^sub>c E" by auto
      have sCEv: "s = CE\<langle>v\<rangle>" unfolding CE s l\<sigma> by auto
      obtain f bef E' aft where CE: "CE = More f bef E' aft" 
        using E unfolding CE by (cases C, cases E, auto)
      have "E'\<langle>v\<rangle> \<in> set (args s)" unfolding sCEv CE by auto
      then have "funas_term (E'\<langle>v\<rangle>) \<subseteq> F_all" using wfs by blast
      then have vwf: "funas_term v \<subseteq> F_all" by auto
      show "u \<in> NF_terms Q"
        unfolding u
      proof (rule NF_unlab[OF _ vwf subset_refl lin])
        show "v \<in> NF_terms ?Q"
          using NF[unfolded l\<sigma>] E by auto
      qed
    qed
  qed
  have ustep: "(?m s, ?m t) \<in> qrstep False Q ({(?m l, ?m r)})" unfolding s t map_funs_term_ctxt_distrib map_funs_subst_distrib
    by (rule qrstepI[OF mnf mlr(2) refl refl], simp)
  have "wf_rule (?m l, ?m r)"
  proof (cases "SN_on (qrstep nfs Q R) {?m s}")
    case True
    from SN_on_imp_qrstep_wf_rules[OF SN_on_subset1[OF True[unfolded switch] qrstep_mono] ustep]
    have "(?m s, ?m t) \<in> qrstep False Q (wf_rules {(?m l, ?m r)})" 
      using mlr by auto
    then have "wf_rules {(?m l, ?m r)} \<noteq> {}" by auto
    then show "wf_rule (?m l, ?m r)" unfolding wf_rules_def by auto
  next
    case False
    from SN[OF this] have "wwf_qtrs Q R" by auto
    from this[unfolded wwf_qtrs_wwf_rules] mlr(1) have "wwf_rule Q (?m l,?m r)" by auto
    moreover have "applicable_rule Q (?m l, ?m r)"
      by (rule only_applicable_rules[OF mnf])
    ultimately show ?thesis unfolding wwf_rule_def wf_rule_def by blast
  qed
  then have vars: "vars_term r \<subseteq> vars_term l" and nvar: "is_Fun l"
    unfolding wf_rule_def snd_conv fst_conv using vars_term_map_funs_term
    by auto
  {
    assume wfs: "funas_term s \<subseteq> F_all"
    have wf: "funas_term t \<subseteq> F_all"
      by (rule qrstep_preserves_funas_terms[OF wf_Lab_all_trs[OF lr] wfs step vars])
  } note wfst = this
  from nvar obtain f ls where l: "l = Fun f ls" by (cases l, auto)
  have wfr:  "funas_term r \<subseteq> F_all" using lr LR unfolding Lab_all_trs_def by auto
  {
    fix x
    assume "x \<in> vars_term r"
    with vars have x: "x \<in> vars_term l" by auto
    have "funas_term (\<sigma> x) \<subseteq> F_all"
    proof (cases C)
      case (More f bef D aft)
      from s[unfolded More] have "D\<langle>l\<cdot>\<sigma>\<rangle> \<in> set (args s)" by auto
      with wfs have "funas_term (D\<langle>l\<cdot>\<sigma>\<rangle>) \<subseteq> F_all" by blast
      then show ?thesis using x unfolding funas_term_ctxt_apply funas_term_subst by force
    next
      case Hole
      from x obtain l' where l': "l' \<in> set ls" and x: "x \<in> vars_term l'" unfolding l by auto
      from s[unfolded Hole] l l' have "l' \<cdot> \<sigma> \<in> set (args s)" by auto
      then have "funas_term (l' \<cdot> \<sigma>) \<subseteq> F_all" using wfs by auto
      with x show ?thesis unfolding funas_term_subst by auto
    qed
  }
  with wfr 
  have wfr\<sigma>: "funas_term (r \<cdot> \<sigma>) \<subseteq> F_all"
    unfolding funas_term_subst by blast
  have wft: "\<Union>(funas_term ` set (args t)) \<subseteq> F_all"
  proof (cases C)
    case Hole
    show ?thesis unfolding t Hole using wfr\<sigma> funas_term_args by force
  next
    case (More f bef D aft)
    {
      fix u
      assume "u \<in> set (args (More f bef D aft)\<langle>r \<cdot> \<sigma>\<rangle>)"
      then have "u \<in> set bef \<union> set aft \<or> u = D\<langle>r\<cdot>\<sigma>\<rangle>" by auto
      then have "funas_term u \<subseteq> F_all"
      proof
        assume u: "u = D\<langle>r \<cdot> \<sigma>\<rangle>"
        from wfs[unfolded s More] have "funas_term (D\<langle>l\<cdot>\<sigma>\<rangle>) \<subseteq> F_all" by auto
        then show ?thesis using wfr\<sigma> unfolding u  by auto
      next
        assume "u \<in> set bef \<union> set aft"
        with wfs[unfolded s More] show ?thesis by auto
      qed
    }
    then show ?thesis unfolding t More by blast
  qed
  have "(?m s, ?m t) \<in> qrstep False Q R"
    using set_mp[OF qrstep_mono[OF _ subset_refl] ustep, of R] mlr(1) by auto
  with wft wfst show ?thesis unfolding switch by auto
qed

lemma Decr_UNLAB: "map_funs_trs UNLAB Decr \<subseteq> Id"
  unfolding map_funs_trs.simps decr_of_ord_def using LD_LC by auto

lemma map_funs_term_Decr:
  assumes step: "(s,t) \<in> qrstep nfs Q Decr"
  shows "map_funs_term UNLAB s = map_funs_term UNLAB t"
proof -
  from qrstep_imp_map_rstep[OF step, of UNLAB]
    rstep_mono[OF Decr_UNLAB] rstep_id 
  show ?thesis by auto
qed


lemma SN_on_UNLAB_imp_SN_on: assumes LR: "LR \<subseteq> Lab_all_trs R"
  and lin: "\<And> q. q \<in> Q \<Longrightarrow> linear_term q"
  and wfs:  "\<Union>(funas_term ` set (args s)) \<subseteq> F_all"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
  and SN: "SN_on (qrstep nfs Q R) {map_funs_term UNLAB s}"
  and LQ: "NF_terms (Lab_lhss_more Q) \<supseteq> NF_terms LQ"
  shows "SN_on (qrstep nfs LQ (LR \<union> Decr)) {s}"
proof
  fix f
  assume f: "f 0 \<in> {s}" and steps: "\<forall> i. (f i, f (Suc i)) \<in> qrstep nfs LQ (LR \<union> Decr)"
  let ?r = "qrstep nfs Q R"
  let ?B = "qrstep nfs LQ LR \<union> qrstep nfs LQ Decr"
  let ?R = "qrstep nfs LQ LR"
  let ?D = "qrstep nfs LQ Decr"
  let ?m = "\<lambda>i. map_funs_term UNLAB (f i)"
  let ?w = "\<lambda>t. \<Union>(funas_term ` set (args t)) \<subseteq> F_all"
  let ?SN = "\<lambda>x. SN_on ?r {x}"
  let ?f = "\<lambda> i. (f i, f (Suc i))"
  from steps have steps: "\<And> i. ?f i \<in> ?B" unfolding qrstep_union by auto
  show False
  proof (cases "\<forall> i. (\<exists> j \<ge> i. ?f j \<in> ?R)")
    case False
    then obtain i where n: "\<And> j. j \<ge> i \<Longrightarrow> ?f j \<notin> ?R" by auto
    obtain g where g: "g = (\<lambda> j. f (j + i))" by auto
    {
      fix j
      have "(g j, g (Suc j)) \<in> ?D" using steps[of "j + i"] n[of "j + i"] 
        unfolding g by auto
    }
    then have "\<not> SN ?D" unfolding SN_defs by blast    
    with SN_subset[OF Decr_SN, of "qrstep nfs LQ Decr"] show False by auto
  next
    case True
    let ?p = "\<lambda> i. ?f i \<in> ?R"
    {
      fix i
      have "?w (f i) \<and> ?SN (?m i) \<and> (i > 0 \<longrightarrow> ((?p (i - 1) \<longrightarrow> (?m (i - 1), ?m i) \<in> ?r)) \<and> (\<not> ?p (i - 1) \<longrightarrow> ?m i = ?m (i - 1)))"
      proof (induct i)
        case 0
        show ?case unfolding singletonD[OF f] using wfs SN by auto
      next
        case (Suc i)
        then have wf: "?w (f i)" and SN: "?SN (?m i)" by auto
        show ?case
        proof (cases "?p i")
          case True
          from step_imp_UNLAB_step[OF LR lin wf wwf _ LQ True]
          show ?thesis using step_preserves_SN_on[OF _ SN] True SN by auto
        next
          case False
          with steps[of i] have step: "?f i \<in> ?D" by auto
          from wf_Decr_args[OF wf step] have wf: "?w (f (Suc i))" by auto
          from map_funs_term_Decr[OF step] have "?m i = ?m (Suc i)" .
          then show ?thesis using wf SN False by auto
        qed
      qed
    } note main = this
    {
      fix i
      assume "?p i"
      with main[of "Suc i"] have "(?m i, ?m (Suc i)) \<in> ?r" by simp
    } note p = this
    {
      fix i
      assume "\<not> ?p i"
      with main[of "Suc i"] have "?m (Suc i) = ?m i" by simp
    } note np = this
    obtain p where p': "p = ?p" by auto
    from p p' have p: "\<And> i. p i \<Longrightarrow> (?m i, ?m (Suc i)) \<in> ?r" by auto
    from np p' have np: "\<And> i. \<not> p i \<Longrightarrow> ?m (Suc i) = ?m i" by auto
    interpret infinitely_many p unfolding p'
      by (unfold_locales, unfold INFM_nat_le, rule True)
    obtain g where g: "g = (\<lambda> i. ?m (index i))" by auto
    {
      fix i
      from p[OF index_p, of i]
      have "(g i, ?m (Suc (index i))) \<in> ?r" unfolding g by auto
      also have "?m (Suc (index i)) = g (Suc i)"
      proof -
        let ?i = "Suc (index i)"
        {
          fix k
          assume "?i + k \<le> index (Suc i)"
          then have "?m (?i + k) = ?m ?i"
          proof (induct k)
            case 0 then show ?case by simp
          next
            case (Suc k)
            with np[OF index_not_p_between[of i "?i + k"]]
            show ?case by auto
          qed
        } note eq = this
        let ?k = "index (Suc i) - ?i"
        from index_ordered[of i] have "?i \<le> index (Suc i)" by auto
        then have id: "?i + ?k = index (Suc i)" by auto
        then have "?i + ?k \<le> index (Suc i)" by auto
        from eq[OF this] show ?thesis unfolding id g ..
      qed
      finally have "(g i, g (Suc i)) \<in> ?r" .
    }
    then have "\<not> SN_on ?r {g 0}" unfolding SN_defs by auto
    with main[of "index 0"] show False unfolding g by auto
  qed
qed
end

    

context sl_interpr_root
begin

lemma SN_inj_root: assumes inj: "\<And> f. inj (L f)"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q R"
  and SN: "SN_on (qrstep nfs Q R) {t}"
  and ndef: "\<not> defined (applicable_rules Q R) (the (root t))"
  and model: "qmodel I L LC C cge R"
  and cge: "cge = (=)"
  and wf: "wf_ass \<alpha>"
  and LQ: "NF_terms (Lab_lhss Q) \<supseteq> NF_terms LQ"
  and nvar: "\<And> l r. (l,r) \<in> R \<Longrightarrow> is_Fun l"
  shows "SN_on (qrstep nfs LQ (Lab_trs R)) {Lab_root \<alpha> t}" 
proof (rule SN_on_subset1[OF _ qrstep_mono[OF subset_refl LQ]])
  from nvar have nvar: "\<forall> (l,r) \<in> R. is_Fun l" by auto
  {
    fix l r
    assume lr: "(l,r) \<in> Lab_trs R" and v: "is_Var l"
    from lr obtain ll rr where "(l,r) \<in> lab_rule I L LC C (ll,rr)" 
      and llrr: "(ll,rr) \<in> R" by auto
    then obtain \<alpha> where l: "l = Lab \<alpha> ll" unfolding lab_rule_def by auto
    from nvar llrr v have False unfolding l by (cases ll, auto simp: Let_def)
  }
  then have nvarL: "\<forall> (l,r) \<in> Lab_trs R. is_Fun l" by auto  
  let ?LQ = "Lab_lhss Q"
  let ?QR = "qrstep nfs ?LQ (Lab_trs R)"
  show "SN_on ?QR {Lab_root \<alpha> t}"
  proof (cases t)
    case (Var x)
    show ?thesis
    proof
      fix f
      assume z: "f 0 \<in> {Lab_root \<alpha> t}" and steps: "\<forall> i. (f i, f (Suc i)) \<in> ?QR"
      from steps[THEN spec[of _ 0]] singletonD[OF z] Var have "(Var x, f (Suc 0)) \<in> ?QR" by simp      
      then show False
      proof 
        fix D \<sigma> l r
        assume lr: "(l,r) \<in> Lab_trs R" and "Var x = D\<langle>l\<cdot>\<sigma>\<rangle>"
        then obtain y where l: "l = Var y" by (cases D, simp, cases l, auto)
        from nvarL l lr show False by force
      qed
    qed
  next
    case (Fun f ts)
    show ?thesis unfolding Fun lab_root.simps Let_def
    proof (rule SN_args_imp_SN[OF _ nvarL], unfold map_map o_def)
      fix lt
      assume "lt \<in> set (map (Lab \<alpha>) ts)"
      then obtain t where t: "t \<in> set ts" and lt: "lt = Lab \<alpha> t" by auto
      show "SN_on ?QR {lt}" unfolding lt
        by (rule SN_inj[OF inj wwf SN_imp_SN_arg_gen[OF ctxt_closed_qrstep SN[unfolded Fun] t] model cge wf subset_refl])
    next
      let ?n = "length ts"
      let ?f = "LC f ?n (L' f (map (Eval \<alpha>) ts))"
      let ?m = "length (map (Lab \<alpha>) ts)"
      let ?U = "applicable_rules ?LQ (Lab_trs R)"
      let ?d = "defined ?U (?f,?m)"
      show "\<not> ?d"
      proof
        assume "?d"
        from this[unfolded defined_def] 
        obtain l r where lr: "(l,r) \<in> ?U" and l: "root l = Some (?f, ?n)" by auto
        then obtain ls where l: "l = Fun ?f ls" and ls: "length ls = ?n" by (cases l, auto)
        from lr[unfolded applicable_rules_def] have lr: "(l,r) \<in> Lab_trs R"
          and u: "applicable_rule ?LQ (l,r)" by auto
        from u[unfolded applicable_rule_def] have 
          NF: "\<And> s. l \<rhd> s \<Longrightarrow> s \<in> NF_terms (Lab_lhss Q)" by auto
        from lr obtain ll rr where "(l,r) \<in> lab_rule I L LC C (ll,rr)" 
          and llrr: "(ll,rr) \<in> R" by auto
        then obtain \<alpha> where l': "l = Lab \<alpha> ll" and r: "r = Lab \<alpha> rr"
          and wf_a: "wf_ass \<alpha>"
          unfolding lab_rule_def by auto
        have u: "applicable_rule Q (ll,rr)" 
          unfolding applicable_rule_def fst_conv 
        proof (intro allI impI)
          fix s
          assume supt: "ll \<rhd> s"
          show "s \<in> NF_terms Q"
          proof (rule lab_nf_rev[OF _ wf_a])
            from supt obtain D where llD: "ll = D\<langle>s\<rangle>" and D: "D \<noteq> \<box>" by auto
            show "Lab \<alpha> s \<in> NF_terms (Lab_lhss Q)"
              by (rule NF[unfolded l' llD lab_ctxt, OF nectxt_imp_supt_ctxt],
              insert D, cases D, auto simp: Let_def)
          qed
        qed
        with llrr have u: "(ll,rr) \<in> applicable_rules Q R" 
          unfolding applicable_rules_def by auto
        from ndef[unfolded Fun] have ndef: "\<not> defined (applicable_rules Q R) (f, ?n)" by auto
        from l[unfolded l'] obtain g lls where ll: "ll = Fun g lls" by (cases ll, auto simp: Let_def)
        let ?g = "LC g (length lls) (L g (map (Eval \<alpha>) lls))"
        from l[unfolded l' ll] have gf: "?g = ?f" and lls: "length lls = length ls" 
          by (auto simp: Let_def o_def)
        from arg_cong[OF gf, of LD, unfolded LD_LC] have gf: "g = f" by auto
        have "defined (applicable_rules Q R) (g, length lls)"
          unfolding defined_def using u unfolding ll by auto
        with ndef show False unfolding gf lls ls ..
      qed
    qed
  qed
qed
end

context sl_interpr
begin

lemma model_rewrite: 
  fixes R :: "('f,'v)trs"
  assumes model: "qmodel I L LC C cge R"
  and decr: "Decr = ({} :: ('lf,'v)trs)" (is "?D = {}")
  and step: "(s,t) \<in> qrstep nfs Q R"
  and LQ: "NF_terms LQ \<supseteq> NF_terms (Lab_lhss_all Q)"
  shows "(LAB s, LAB t) \<in> qrstep nfs LQ (Lab_trs R)"
proof -
  from quasi_lab_rewrite[OF _ _ step model wf_default_ass lge_term_refl, of ?D,
  unfolded qrstep_empty_r decr wf_trs_def]
  obtain v where step: "(LAB s, v) \<in> qrstep nfs (Lab_lhss_all Q) (Lab_trs R)" and lge: "lge_term v (LAB t)" by auto
  {
    fix s t  :: "('lf,'v)term"
    assume "lge_term s t"
    then have "s = t"
    proof (induct s arbitrary: t)
      case (Var x)
      then show ?case by (cases t, auto)
    next
      case (Fun f ss t)
      from Fun(2) obtain g ts where t: "t = Fun g ts" by (cases t, auto simp: Let_def)
      note Fun = Fun[unfolded t]
      have ssts: "ss = ts" 
        by (rule nth_equalityI, insert Fun, auto)
      from Fun(2)[simplified]
      obtain h lf lg where f: "f = LC h (length ts) lf" and
        g: "g = LC h (length ts) lg" and
        disj: "lf = lg \<or> Ball {lf,lg} (LS h (length ts)) \<and> lge h (length ts) lf lg" (is "?id \<or> ?cond") by auto
      from disj have "?id \<or> lf \<noteq> lg \<and> ?cond" by blast
      then have fg: "f = g"
      proof
        assume "lf = lg"
        then show ?thesis unfolding f g by auto
      next
        assume cond: "lf \<noteq> lg \<and> ?cond"
        then have "(lf,lg) \<in> gr h (length ts)" 
          unfolding lge_to_lgr_rel_def lge_to_lgr_def
          by (auto simp: Let_def)
        with cond decr show ?thesis unfolding decr_of_ord_def by auto 
      qed
      show ?case unfolding t fg ssts ..
    qed
  }
  from step[unfolded this[OF lge]]
    qrstep_mono[OF subset_refl LQ]
  show ?thesis by blast
qed
end

hide_const Semantic_Labeling.aux


locale sl_interpr_same = sl_interpr C c I cge lge L LC LD LS 
  for 
  C :: "'c set"
  and  c :: "'c"
  and  I :: "('f,'c)inter"
  and  cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and  lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and  L :: "('f,'c,'l)label"
  and  LC :: "('f,'l,'f)lcompose"
  and  LD :: "('f,'f,'l)ldecompose"
  and  LS :: "('f,'l)labels" 
begin


lemma sl_model_finite: fixes R :: "('f,'v)trs"
  assumes inj: "\<And> f. inj (L f)"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q (R \<union> Rw)"
  and model_R: "qmodel I L LC C cge R"
  and model_Rw: "qmodel I L LC C cge Rw"
  and cge: "cge = (=)"
  and decr: "Decr = ({} :: ('f,'v)trs)"
  and LQ1: "NF_terms (Lab_lhss Q) \<supseteq> NF_terms LQ"
  and LQ2: "NF_terms LQ \<supseteq> NF_terms (Lab_lhss_all Q)"
  and fin: "finite_dpp (nfs,m,Lab_trs P, Lab_trs Pw, LQ, Lab_trs R, Lab_trs Rw)"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  let ?P = "Lab_trs P"
  let ?Pw = "Lab_trs Pw"
  let ?R = "Lab_trs R"
  let ?Rw = "Lab_trs Rw"
  let ?Q = "LQ"
  let ?subst_closure' = "rqrstep nfs ?Q"
  let ?subst_closure = "rqrstep nfs Q"
  let ?M = "{(s, t). m \<longrightarrow> SN_on (qrstep nfs ?Q (?R \<union> ?Rw)) {t}}"
  let ?N = "{(s,t). s \<in> NF_terms ?Q}"
  let ?P' = "?subst_closure' ?P \<inter> ?N \<inter> ?M"
  let ?Pw' = "?subst_closure' ?Pw \<inter> ?N \<inter> ?M"
  let ?R'  ="qrstep nfs ?Q ?R"
  let ?Rw'  ="qrstep nfs ?Q ?Rw"
  let ?A = "?P' \<union> ?Pw' \<union> ?R' \<union> ?Rw'"
  note NF_anti = LQ2
  show ?thesis 
  proof (rule finite_dpp_map_min[OF fin, where I = "\<lambda> _. True"])
    fix t
    assume SN: "m \<longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t}"
    show "m \<longrightarrow> SN_on (qrstep nfs ?Q (?R \<union> ?Rw)) {LAB t}"
    proof
      assume m
      with SN have SN: "SN_on (qrstep nfs Q (R \<union> Rw)) {t}" by blast
      show "SN_on (qrstep nfs ?Q (?R \<union> ?Rw)) {LAB t}"
        unfolding lab_trs_union[symmetric]
        by (rule SN_inj[OF inj wwf SN _ cge wf_default_ass LQ1], 
          insert model_R model_Rw, auto simp: qmodel_def)
    qed
  next
    fix s t
    assume "(s,t) \<in> qrstep nfs Q Rw"
    from model_rewrite[OF model_Rw decr this LQ2]
    show "(LAB s, LAB t)
      \<in> ?A^* \<and> True" by auto 
  next
    fix s t 
    assume "(s,t) \<in> qrstep nfs Q R"
    from model_rewrite[OF model_R decr this LQ2]
    show "(LAB s, LAB t) \<in> ?A^* O (?P' \<union> ?R') O ?A^* \<and> True"
      by auto
  next
    fix s t
    assume "(s,t) \<in> ?subst_closure P \<inter> {(s,t). s \<in> NF_terms Q}" and SN: "m \<longrightarrow> SN_on (qrstep nfs ?Q (?R \<union> ?Rw)) {LAB t}"
    then have step: "(s,t) \<in> ?subst_closure P" and nf: "s \<in> NF_terms Q" by auto
    from lab_nf[OF nf] have "LAB s \<in> NF_terms (Lab_lhss_all Q)" by auto
    with NF_anti
    have N: "(LAB s, LAB t) \<in> ?N" by auto
    from lab_rqrstep[OF step wf_default_ass] rqrstep_mono[OF subset_refl NF_anti]
    have "(LAB s, LAB t) \<in> rqrstep nfs LQ (Lab_trs P)" by blast
    with N SN show "(LAB s, LAB t) \<in> ?A^* O ?P' O ?A^* \<and> True" by auto
  next
    fix s t 
    assume "(s,t) \<in> ?subst_closure Pw \<inter> {(s,t). s \<in> NF_terms Q}" and SN: "m \<longrightarrow> SN_on (qrstep nfs ?Q (?R \<union> ?Rw)) {LAB t}"
    then have step: "(s,t) \<in> ?subst_closure Pw" and nf: "s \<in> NF_terms Q" by auto
    from lab_nf[OF nf] have "LAB s \<in> NF_terms (Lab_lhss_all Q)" by auto
    with NF_anti
    have N: "(LAB s, LAB t) \<in> ?N" by auto
    from lab_rqrstep[OF step wf_default_ass] rqrstep_mono[OF subset_refl NF_anti]
    have "(LAB s, LAB t) \<in> rqrstep nfs LQ (Lab_trs Pw)" by blast
    with N SN show "(LAB s, LAB t) \<in> ?A^* O (?P' \<union> ?Pw') O ?A^* \<and> True" by auto
  qed
qed
end  

locale sl_interpr_root_same = sl_interpr_root C c I cge lge L LC LD LS L' LS'
  for  C :: "'c set"
  and  c :: "'c"
  and  I :: "('f,'c)inter"
  and  cge :: "'c \<Rightarrow> 'c \<Rightarrow> bool"
  and  lge :: "'f \<Rightarrow> nat \<Rightarrow> 'l \<Rightarrow> 'l \<Rightarrow> bool"
  and  L :: "('f,'c,'l)label"
  and  LC :: "('f,'l,'f)lcompose"
  and  LD :: "('f,'f,'l)ldecompose"
  and  LS :: "('f,'l)labels" 
  and  L' :: "('f,'c,'l)label"
  and  LS' :: "('f,'l)labels" 
begin

lemma sl_model_root_finite: fixes R :: "('f,'v)trs"
  assumes inj: "\<And> f. inj (L f)"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q (R \<union> Rw)"
  and model_R: "qmodel I L LC C cge R"
  and model_Rw: "qmodel I L LC C cge Rw"
  and cge: "cge = (=)"
  and decr: "Decr = ({} :: ('f,'v)trs)"
  and decr_root: "Decr_root = ({} :: ('f,'v)trs)"
  and LQ1: "NF_terms (Lab_lhss Q) \<supseteq> NF_terms LQ"
  and LQ2: "NF_terms LQ \<supseteq> NF_terms (Lab_lhss_all Q)"
  and nvarP: "\<forall> (s,t) \<in> P \<union> Pw. is_Fun s \<and> is_Fun t"
  and ndefP: "\<forall> (s,t) \<in> P \<union> Pw. \<not> defined (applicable_rules Q (R \<union> Rw)) (the (root t))"
  and nvar: "\<forall> (s,t) \<in> R \<union> Rw. is_Fun s"
  and fin: "finite_dpp (nfs,m,Lab_root_trs P, Lab_root_trs Pw, LQ, Lab_trs R, Lab_trs Rw)"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  let ?E = "{} :: ('f,'v)trs"
  from decr have decr: "Decr \<subseteq> (subst.closure ?E \<inter> Decr)^+" by auto
  from decr_root have decr_root: "\<And> D :: ('f,'v)trs. Decr_root^= O D = D" by auto
  let ?P = "Lab_root_trs P"
  let ?Pw = "Lab_root_trs Pw"  
  let ?R = "Lab_trs R"
  let ?Rw = "Lab_trs Rw"
  let ?Q = "LQ"
  let ?R'  ="qrstep nfs ?Q ?R"
  let ?Rw'  ="qrstep nfs ?Q (?R \<union> ?Rw)"
  let ?dpp = "(nfs,m,P,Pw,Q,R,Rw)"
  note mono2 = qrstep_mono[OF _ LQ2]
  have wftrs: "wf_trs {}" unfolding wf_trs_def by auto
  show ?thesis 
      unfolding finite_dpp_def
    proof (clarify)
      fix s t \<sigma>
      assume "min_ichain ?dpp s t \<sigma>"
      then have ichain: "ichain ?dpp s t \<sigma>" and SN: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}" by (auto simp: minimal_cond_def)
      let ?steps = "\<lambda> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))^* O qrstep nfs Q R O (qrstep nfs Q (R \<union> Rw))^*"
      from ichain[unfolded ichain.simps]
      have PPw: "\<And> i. (s i, t i) \<in> P \<union> Pw"
        and steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))^*"
        and NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
        and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q" 
        and inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. ?steps i)"
        by auto 
      let ?l = "LAB_root"
      let ?ts = "\<lambda> i. ?l (t i \<cdot> \<sigma> i)"
      let ?ss = "\<lambda> i. ?l (s i \<cdot> \<sigma> i)"
      let ?a = "subst_ass default_ass"
      let ?t = "\<lambda> i. Lab_root (?a (\<sigma> i)) (t i)"
      let ?s = "\<lambda> i. Lab_root (?a (\<sigma> i)) (s i)"
      let ?\<sigma> = "\<lambda> i. lab_subst default_ass (\<sigma> i)"
      let ?p = "\<lambda> i. (?t i \<cdot> ?\<sigma> i, ?s (Suc i) \<cdot> ?\<sigma> (Suc i))"
      from model_R model_Rw have model: "qmodel I L LC C cge (R \<union> Rw)"
        unfolding qmodel_def by auto
      {
        fix i
        note wf_ass_subst_ass[OF wf_default_ass, of "\<sigma> i"]
      } note wf_ass = this
      {
        fix i
        from nvarP PPw[of i] have nvarPi: "is_Fun (t i)" "is_Fun (s i)" by auto
        from nvarP PPw[of "Suc i"] have nvarPsi: "is_Fun (s (Suc i))" by auto
        have tsi: "?t i \<cdot> ?\<sigma> i = ?ts i" unfolding lab_root_subst[OF nvarPi(1)] ..
        have ssi: "?s i \<cdot> ?\<sigma> i = ?ss i" unfolding lab_root_subst[OF nvarPi(2)] ..
        have sssi: "?s (Suc i) \<cdot> ?\<sigma> (Suc i) = ?ss (Suc i)" unfolding lab_root_subst[OF nvarPsi] ..
        from nvarPi obtain f ts where ti: "t i = Fun f ts" by force
        from nvarPi obtain g ss where si: "s i = Fun g ss" by force
        from ndefP PPw[of i] have ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (f, length ts)" using ti by force
        from ndef have ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root (t i \<cdot> \<sigma> i)))" unfolding ti by auto
        from wf_ass[of i] PPw[of i] have PPw: "(?s i, ?t i) \<in> ?P \<union> ?Pw" by (force simp: lab_root_rule_def)
        have steps: "?p i \<in>
          ?Rw'^*" unfolding tsi sssi
          by (rule set_mp[OF _ quasi_lab_root_steps_qnf[OF nvar ndef decr wftrs steps[of i] model_R model_Rw NF wf_default_ass, unfolded decr_root]],
          rule rtrancl_mono[OF mono2], auto)
        from set_mp[OF LQ2 lab_nf_root[OF NF[of i], of default_ass]]
        have NF: "?s i \<cdot> ?\<sigma> i \<in> NF_terms ?Q" unfolding ssi .
        from SN_inj_root[OF inj wwf SN[of i] ndef model cge wf_default_ass LQ1 ]
        have SN: "m \<Longrightarrow> SN_on ?Rw' {?t i \<cdot> ?\<sigma> i}" unfolding lab_trs_union tsi using nvar by auto
        let ?aa = "?a (\<sigma> i)"
        from lab_nf_subst[OF nfs[of i]] 
        have "NF_subst nfs (Lab ?aa (s i), Lab ?aa (t i)) (?\<sigma> i) (Lab_lhss_all Q)" .
        then have "NF_subst nfs (?s i, ?t i) (?\<sigma> i) (Lab_lhss_all Q)"
          unfolding NF_subst_def ti si vars_rule_def by (auto simp: Let_def)
        with LQ2 
        have nfs: "NF_subst nfs (?s i, ?t i) (?\<sigma> i) LQ" unfolding NF_subst_def by auto
        note PPw steps NF SN tsi sssi ndef nfs
      }
      note main = this
      from main(4) have min: "m \<Longrightarrow> minimal_cond nfs ?Q (?R \<union> ?Rw) ?s ?t ?\<sigma>"
        unfolding minimal_cond_def by auto
      let ?dpp = "(nfs,m,?P,?Pw,?Q,?R,?Rw)"
      have ichain: "ichain ?dpp ?s ?t ?\<sigma>"
        unfolding ichain.simps
      proof (intro conjI allI)
        fix i
        show "(?s i, ?t i) \<in> ?P \<union> ?Pw" using main(1) by auto
        show "?s i \<cdot> ?\<sigma> i \<in> NF_terms ?Q" using main(3) by auto
        show "?p i \<in> ?Rw'^*" using main(2) by auto
        show "NF_subst nfs (?s i, ?t i) (?\<sigma> i) LQ" using main(8) .
        let ?lsteps = "\<lambda> i. ?p i \<in> ?Rw'^* O ?R' O ?Rw'^*"
        show "(INFM i. (?s i, ?t i) \<in> ?P) \<or> (INFM i. ?lsteps i)"
          unfolding INFM_disj_distrib[symmetric]
          unfolding INFM_nat_le
        proof (intro allI)
          fix n
          from inf[unfolded INFM_disj_distrib[symmetric], unfolded INFM_nat_le]
          obtain m where m: "m \<ge> n" and disj: "(s m, t m) \<in> P \<or> ?steps m" by blast
          show "\<exists> m \<ge> n. (?s m, ?t m) \<in> ?P \<or> ?lsteps m"
          proof (intro exI conjI, rule m)
            from disj show "(?s m, ?t m) \<in> ?P \<or> ?lsteps m"
            proof
              assume "(s m, t m) \<in> P"
              then show ?thesis
                using wf_ass[of m]  by (force simp: lab_root_rule_def)
            next
              assume "?steps m"
              from set_mp[OF relto_mono[OF mono2[OF subset_refl] mono2[OF subset_refl]] 
                 quasi_lab_root_relto_qnf[OF nvar main(7) decr wftrs this model_R model_Rw NF wf_default_ass, unfolded decr_root]]
              show ?thesis
                unfolding main(5) main(6)
                by simp
            qed
          qed
        qed
      qed
      with min have "min_ichain ?dpp ?s ?t ?\<sigma>" by simp
      with fin show False unfolding finite_dpp_def by auto
    qed
qed

lemma sl_qmodel_root_finite: fixes R D :: "('f,'v)trs"
  assumes model_R: "qmodel I L LC C cge R"
  and model_Rw: "qmodel I L LC C cge Rw"
  and D1: "Decr \<subseteq> (subst.closure D \<inter> Decr)^+"
  and wf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wf_trs D"
  and wwf: "nfs \<Longrightarrow> Q \<noteq> {} \<Longrightarrow> wwf_qtrs Q (R \<union> Rw)"
  and D2: "D \<subseteq> Decr"
  and LQ1: "NF_terms (Lab_lhss_more Q) \<supseteq> NF_terms LQ"
  and LQ2: "NF_terms LQ \<supseteq> NF_terms (Lab_lhss_all Q)"
  and Q: "\<And>q. q \<in> Q \<Longrightarrow> linear_term q"
  and LR: "Lab_trs R \<subseteq> LR"
  and LRw: "Lab_trs Rw \<subseteq> LR \<union> LRw"
  and LRRw: "LR \<union> LRw \<subseteq> Lab_all_trs (R \<union> Rw)"
  and nvarP: "\<forall> (s,t) \<in> P \<union> Pw. is_Fun s \<and> is_Fun t"
  and ndefP: "\<forall> (s,t) \<in> P \<union> Pw. \<not> defined (applicable_rules Q (R \<union> Rw)) (the (root t))"
  and nvar: "\<forall> (l,r) \<in> R \<union> Rw. is_Fun l" 
  and fin: "finite_dpp (nfs,m,Lab_root_all_trs P, Lab_root_all_trs Pw, LQ, LR, LRw \<union> D)"
  shows "finite_dpp (nfs,m,P,Pw,Q,R,Rw)"
proof -
  let ?r = "qrstep nfs Q R"
  let ?rw = "qrstep nfs Q (R \<union> Rw)"
  let ?rws = "?rw^*"
  let ?rrw = "?rws O ?r O ?rws"
  let ?D = "Decr_root :: ('f,'v)trs"
  let ?P = "Lab_root_all_trs P"
  let ?Pw = "Lab_root_all_trs Pw"  
  let ?R = "Lab_trs R"
  let ?Rw = "Lab_trs Rw"
  let ?Q = "LQ"
  let ?R'  ="qrstep nfs ?Q ?R"
  let ?Rw'  ="qrstep nfs ?Q (?R \<union> ?Rw \<union> D)"
  let ?Rws = "?Rw'^*"
  let ?RRw = "?Rws O ?R' O ?Rws"
  let ?dpp = "(nfs,m,P,Pw,Q,R,Rw)"
  note mono2 = qrstep_mono[OF subset_refl LQ2]
  show ?thesis 
      unfolding finite_dpp_def
    proof (clarify)
      fix s t \<sigma>
      assume "min_ichain ?dpp s t \<sigma>"
      then have ichain: "ichain ?dpp s t \<sigma>" and SN: "\<And> i. m \<Longrightarrow> SN_on (qrstep nfs Q (R \<union> Rw)) {t i \<cdot> \<sigma> i}" by (auto simp: minimal_cond_def)
      let ?steps = "\<lambda> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))^* O qrstep nfs Q R O (qrstep nfs Q (R \<union> Rw))^*"
      from ichain[unfolded ichain.simps]
      have PPw: "\<And> i. (s i, t i) \<in> P \<union> Pw"
        and steps: "\<And> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i)) \<in> (qrstep nfs Q (R \<union> Rw))^*"
        and NF: "\<And> i. s i \<cdot> \<sigma> i \<in> NF_terms Q"
        and nfs: "\<And> i. NF_subst nfs (s i, t i) (\<sigma> i) Q"
        and inf: "(INFM i. (s i, t i) \<in> P) \<or> (INFM i. ?steps i)"
        by auto 
      let ?l = "LAB_root"
      let ?ts = "\<lambda> i. ?l (t i \<cdot> \<sigma> i)"
      let ?ss = "\<lambda> i. ?l (s i \<cdot> \<sigma> i)"
      let ?a = "subst_ass default_ass"
      let ?s = "\<lambda> i. Lab_root (?a (\<sigma> i)) (s i)"
      let ?\<sigma> = "\<lambda> i. lab_subst default_ass (\<sigma> i)"
      let ?p' = "\<lambda> i. (t i \<cdot> \<sigma> i, s (Suc i) \<cdot> \<sigma> (Suc i))"
      let ?p = "\<lambda> i. (?l (t i \<cdot> \<sigma> i), ?l (s (Suc i) \<cdot> \<sigma> (Suc i)))"
      let ?Pc = "\<lambda> i. if (s i,t i) \<in> P then ?P else ?Pw"
      let ?pc = "\<lambda> i. if (s i,t i) \<in> P then P else Pw"
      let ?Rc = "\<lambda> i. if ?p' i \<in> ?rrw then ?RRw else ?Rws"
      let ?w = "\<lambda> t. \<Union>(funas_term ` set (args t)) \<subseteq> F_all"
      let ?m = "map_funs_term UNLAB"
      let ?mu = "\<lambda> i u. ?m (u \<cdot> ?\<sigma> i) = t i \<cdot> \<sigma> i" 
      let ?muu = "\<lambda> i u. ?m (u ) = t i" 
      have rrws: "?RRw \<subseteq> ?Rws" unfolding qrstep_union by regexp
      let ?prop = "\<lambda> i P R lt. (?s i,lt) \<in> P \<and> (lt \<cdot> ?\<sigma> i,
        ?s (Suc i) \<cdot> ?\<sigma> (Suc i)) \<in> R \<and> ?mu i lt \<and> ?w (lt \<cdot> ?\<sigma> i) \<and> ?muu i lt"
      let ?t' = "\<lambda> i. SOME lt. ?prop i (?Pc i) (?Rc i) lt"
      obtain t' where t': "t' = ?t'" by auto           
      let ?p'' = "\<lambda> i. (t' i \<cdot> ?\<sigma> i, ?s (Suc i) \<cdot> ?\<sigma> (Suc i))"
      from model_R model_Rw have model: "qmodel I L LC C cge (R \<union> Rw)"
        unfolding qmodel_def by auto
      {
        fix i
        note wf_ass_subst_ass[OF wf_default_ass, of "\<sigma> i"]
      } note wf_ass = this
      {
        fix i 
        from nvarP PPw[of i] have nvarPi: "is_Fun (t i)" "is_Fun (s i)" by auto
        from nvarP PPw[of "Suc i"] have nvarPsi: "is_Fun (s (Suc i))" by auto
        have ssi: "?s i \<cdot> ?\<sigma> i = ?ss i" unfolding lab_root_subst[OF nvarPi(2)] ..
        have sssi: "?ss (Suc i) = ?s (Suc i) \<cdot> ?\<sigma> (Suc i)" unfolding lab_root_subst[OF nvarPsi] ..
        from nvarPi obtain f ts where ti: "t i = Fun f ts" by force
        from nvarPi obtain g ss where si: "s i = Fun g ss" by force
        from ndefP PPw[of i] have ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (f, length ts)" using ti by force
        from ndef have ndef: "\<not> defined (applicable_rules Q (R \<union> Rw)) (the (root (t i \<cdot> \<sigma> i)))" unfolding ti by auto
        have steps: "?p i \<in> ?D^= O ?Rc i"
        proof (cases "?p' i \<in> ?rrw")
          case False
          then have id: "?Rc i = ?Rws" by simp
          show ?thesis unfolding id
            by (rule set_mp[OF _ quasi_lab_root_steps_qnf[OF nvar ndef D1 wf steps[of i] model_R model_Rw NF wf_default_ass]], insert rtrancl_mono[OF mono2], auto)
        next
          case True
          then have id: "?Rc i = ?RRw" by auto
          from quasi_lab_root_relto_qnf[OF nvar ndef D1 wf True model_R model_Rw NF wf_default_ass]
            obtain v where "(?ts i, v) \<in> Decr_root^=" and "(v, ?ss (Suc i)) \<in> relto (qrstep nfs (Lab_lhss_all Q) ?R ) (qrstep nfs (Lab_lhss_all Q) (?R \<union> ?Rw \<union> D))"
            by auto
          with set_mp[OF relto_mono[OF mono2 mono2], of "(v, ?ss (Suc i))" nfs "?R \<union> ?Rw \<union> D" nfs ?R]
            show ?thesis unfolding id by blast
        qed
        have pc: "(s i, t i) \<in> ?pc i" using PPw[of i] by auto
        note steps = quasi_lab_root_all_merge[OF steps nvarPi(1) pc wf_default_ass]
        have pc: "Lab_root_all_trs (?pc i) = ?Pc i" by simp
        note steps = steps[unfolded pc sssi]
        from someI_ex[OF steps] 
        have t': "?prop i (?Pc i) (?Rc i) (t' i)" unfolding t' .
        from set_mp[OF LQ2 lab_nf_root[OF NF[of i], of default_ass]]
        have NF: "?s i \<cdot> ?\<sigma> i \<in> NF_terms ?Q" unfolding ssi .
        obtain lu u where lu: "lu = t' i \<cdot> ?\<sigma> i" and u: "u = t i \<cdot> \<sigma> i" by auto
        with t' SN[of i] have wf: "?w lu" and mu: "u = ?m lu" and SN: "m \<Longrightarrow> SN_on ?rw {?m lu}" by auto
        from SN_on_UNLAB_imp_SN_on[OF LRRw Q wf wwf SN LQ1] 
        have SN: "m \<Longrightarrow> SN_on (qrstep nfs LQ (LR \<union> LRw \<union> Decr)) {lu}" .
        have SN: "m \<Longrightarrow> SN_on (qrstep nfs LQ (LR \<union> LRw \<union> D)) {lu}"
          by (rule SN_on_subset1[OF SN qrstep_mono], insert D2, auto) 
        let ?aa = "?a (\<sigma> i)"
        from t' have tim: "t i = map_funs_term UNLAB (t' i)" by simp
        have varsti: "vars_term (t' i) = vars_term (t i)" unfolding tim by simp
        from lab_nf_subst[OF nfs[of i]] have "NF_subst nfs (Lab ?aa (s i), Lab ?aa (t i)) (?\<sigma> i) (Lab_lhss_all Q)" .
        then have "NF_subst nfs (Lab ?aa (s i), Lab ?aa (t i)) (?\<sigma> i) LQ" 
          using LQ2 unfolding NF_subst_def by auto
        then have nfs: "NF_subst nfs (?s i, t' i) (?\<sigma> i) LQ" using varsti
          unfolding si ti NF_subst_def vars_rule_def by (auto simp: Let_def)
        note t' NF SN[unfolded lu] nfs
      }
      note main = this
      have id: "?R \<union> (?Rw \<union> D) = ?R \<union> ?Rw \<union> D" by auto
      let ?dpp = "(nfs,m,?P,?Pw,?Q,?R,?Rw \<union> D)"
      have ichain: "ichain ?dpp ?s t' ?\<sigma>"
        unfolding ichain.simps id
      proof (intro conjI allI)
        fix i
        show "(?s i, t' i) \<in> ?P \<union> ?Pw"
          using main(1)[of i] by (cases "(s i, t i) \<in> P", auto)
        show "?s i \<cdot> ?\<sigma> i \<in> NF_terms ?Q" using main(2) by auto
        show "?p'' i \<in> ?Rws" using main(1)[of i] rrws
          by (cases "?p' i \<in> ?rrw", auto)
        show "NF_subst nfs (?s i, t' i) (?\<sigma> i) LQ" using main[of i] by simp
        let ?lsteps = "\<lambda> i. ?p'' i \<in> ?RRw"
        show "(INFM i. (?s i, t' i) \<in> ?P) \<or> (INFM i. ?lsteps i)"
          unfolding INFM_disj_distrib[symmetric]
          unfolding INFM_nat_le
        proof (intro allI)
          fix n
          from inf[unfolded INFM_disj_distrib[symmetric], unfolded INFM_nat_le]
          obtain m where m: "m \<ge> n" and disj: "(s m, t m) \<in> P \<or> ?p' m \<in> ?rrw" by blast
          show "\<exists> m \<ge> n. (?s m, t' m) \<in> ?P \<or> ?lsteps m"
          proof (intro exI conjI, rule m)
            from disj show "(?s m, t' m) \<in> ?P \<or> ?lsteps m"
            proof
              assume "(s m, t m) \<in> P"
              then show ?thesis using main(1)[of m] by auto
            next
              assume "?p' m \<in> ?rrw"
              then show ?thesis using main(1)[of m] by auto
            qed
          qed
        qed
      qed
      let ?dpp = "(nfs,m,?P,?Pw, ?Q, LR, LRw \<union> D)"
      have ichain: "ichain ?dpp ?s t' ?\<sigma>" 
        by (rule ichain_mono[OF ichain _ _ _ LR], insert LRw LR, auto)      
      from main(3) have min_cond: "m \<Longrightarrow> minimal_cond nfs ?Q (LR \<union> (LRw \<union> D)) ?s t' ?\<sigma>"
        unfolding minimal_cond_def Un_assoc ..
      from ichain min_cond have "min_ichain ?dpp ?s t' ?\<sigma>" by simp
      with fin show False unfolding finite_dpp_def by auto
    qed
qed
end  

sublocale sl_interpr_root_same \<subseteq> sl_interpr_same ..

end
