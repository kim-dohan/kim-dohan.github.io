(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Uncurry
imports
  TRS.DP_Transformation
  TRS.QDP_Framework
  TRS.Tcap
  Auxx.Name
begin

function
  unapp :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> (('f, 'v) term \<times> (('f, 'v) term) list)"
where
  "unapp a (Var x) = (Var x, [])"
| "unapp a (Fun f ss) =
    (if f = a \<and> length ss = 2
      then (case unapp a (ss ! 0) of (r, ts) \<Rightarrow> (r, ts @ [ss ! 1]))
      else (Fun f ss, []))"
  by pat_completeness auto

termination
proof
  fix a :: 'a  and f :: 'a and ss :: "('a,'b)term list"
  assume "f = a \<and> length ss = 2"
  then obtain s ts where "ss = s # ts" by (cases ss, auto)
  then show  "((a, ss ! 0), a, Fun f ss) \<in> measure (\<lambda> (x,y). size y)" by auto
qed simp

fun apply_args :: "'f \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f, 'v) term" where
  "apply_args a t [] = t"
| "apply_args a t (s # ss) = apply_args a (Fun a [t, s]) ss"

fun apply_args_as_ctxt :: "'f \<Rightarrow> ('f, 'v) term list \<Rightarrow> ('f,'v)ctxt" where
  "apply_args_as_ctxt a [] = \<box>"
| "apply_args_as_ctxt a (s # ss) = apply_args_as_ctxt a ss \<circ>\<^sub>c (More a [] \<box> [s])"

lemma apply_args_as_ctxt: "apply_args a t ss = (apply_args_as_ctxt a ss)\<langle>t\<rangle>"
  by (induct ss arbitrary: t, auto)

declare apply_args_as_ctxt.simps[simp del]

lemma apply_args_last: "apply_args a t (ss @ [s]) = Fun a [apply_args a t ss, s]"
  by (induct ss arbitrary: t, auto)

lemma apply_args_append: "apply_args a t (ss @ ts) = apply_args a (apply_args a t ss) ts"
  by (induct ss arbitrary: t, auto)

lemma apply_args_subst: "(apply_args a t ts) \<cdot> \<sigma> = apply_args a (t \<cdot> \<sigma>) (map (\<lambda> s. s \<cdot> \<sigma>) ts)"
  by (induct ts rule: List.rev_induct, auto simp: apply_args_last)

lemma apply_args_rsteps:
  assumes t: "(t, s) \<in> (rstep R)^*"
    and len: "length ts = length ss"
    and ts: "\<And>i. i < length ts \<Longrightarrow> (ts ! i, ss ! i) \<in> (rstep R)^*"
  shows "(apply_args a t ts, apply_args a s ss) \<in> (rstep R)^*"
using len ts t
proof (induct ts arbitrary: ss t s)
  case Nil
  then show ?case by auto
next
  case (Cons v ts)
  from Cons(2) obtain w ws where ss: "ss = w # ws" and len: "length ts = length ws" by (cases ss, auto)
  note Cons = Cons[unfolded ss]
  from Cons(3)[of 0] have step: "(v,w) \<in> (rstep R)^*" by simp
  { 
    fix i
    assume "i < length ts"
    then have "(ts ! i, ws ! i) \<in> (rstep R)^*"
      using Cons(3)[of "Suc i"] by auto
  } note steps = this
  have step: "(Fun a [t,v], Fun a [s,w]) \<in> (rstep R)^*"
  proof (rule args_rsteps_imp_rsteps, simp)
    show "\<forall> i < length [t,v]. ([t,v] ! i, [s,w] ! i) \<in> (rstep R)^*"
    proof(simp, intro allI impI)
      fix i
      assume "i < Suc (Suc 0)"
      then have "i = 0 \<or> i = 1" by arith
      then show "([t,v] ! i, [s,w] ! i) \<in> (rstep R)^*"
        using Cons(4) step by force
    qed
  qed    
  show ?case
    by (unfold ss, simp, rule Cons(1)[OF len steps step])
qed


lemma apply_args_root_rel:
  assumes ctxt: "ctxt.closed R"
    and step: "(t,s) \<in> R"
  shows "(apply_args a t ts, apply_args a s ts) \<in> R"
  unfolding apply_args_as_ctxt 
  using ctxt
  unfolding ctxt.closed_def using step by auto

lemma apply_args_root_trancl:
  assumes ctxt: "ctxt.closed R"
    and steps: "(t,s) \<in> R^+"
  shows "(apply_args a t ts, apply_args a s ts) \<in>  R^+"
  by (rule apply_args_root_rel[OF _ steps], insert ctxt, blast)

lemma obtain_length2: "length xs = 2 \<Longrightarrow> (\<And> x y. xs = [x,y] \<Longrightarrow> P) \<Longrightarrow> P"
  by (cases xs, simp, cases "tl xs", simp, cases "tl (tl xs)", auto)

lemma obtain_length2_conj: "Q \<and> length xs = 2 \<Longrightarrow> (\<And> x y. xs = [x,y] \<Longrightarrow> P) \<Longrightarrow> P"
  using obtain_length2 by auto



lemma unapp_apply_app: assumes unapps: "unapp a s = (r,ts)"
  shows "unapp a (Fun a [s,t]) = (r,ts @ [t])"
  by (simp add: unapps)

lemma unapp_apply_args: assumes "unapp a t = (r,ss)"
  shows "t = apply_args a r ss"
using assms
proof (induct t arbitrary: ss)
  case (Var y)
  then show ?case by auto
next
  case (Fun f ts)
  show ?case
  proof (cases "f = a \<and> length ts = 2")
    case False
    then show ?thesis using Fun(2) by auto
  next
    case True
    obtain s t where ts: "ts = [s,t]" by (rule obtain_length2_conj[OF True]) 
    obtain rr sss where us: "unapp a s = (rr,sss)" by (cases "unapp a s", auto)
    from Fun(2) have "unapp a (Fun f ts) = (rr, sss @ [t])"      
      by (simp add: True ts us)
    with Fun(2) have r: "r = rr" and ss: "ss = (sss @ [t])" by auto
    show ?thesis 
      unfolding ts r ss Fun(1)[unfolded ts r, OF _ us, simplified] apply_args_last
      using True by simp
  qed
qed



lemma unapp_apply_non_app: assumes napp: "\<And> t1 t2. t \<noteq> Fun a [t1,t2]"
  shows "unapp a (apply_args a t ss) = (t, ss)"
proof (induct ss rule: List.rev_induct)
  case Nil with napp show ?case 
  proof (cases t, simp)
    case (Fun f ts)
    show ?thesis 
    proof (cases "f = a \<and> length ts = 2")
      case False with Fun show ?thesis by auto
    next
      case True
      from obtain_length2_conj[OF True] Fun napp show ?thesis by auto
    qed
  qed
next
  case (snoc s ss)
  show ?case using snoc
    by (unfold apply_args_last, simp)
qed


lemma unapp_root: "unapp a t = (r,ss) \<Longrightarrow> r \<noteq> Fun a [u,v]"
proof (induct t arbitrary: ss)
  case (Var x) then show ?case by auto
next
  case (Fun f ts)
  show ?case  
  proof (cases "f = a \<and> length ts = 2")
    case False
    then show ?thesis using Fun by auto
  next
    case True
    obtain t1 t2 where ts: "ts = [t1,t2]" by (rule obtain_length2_conj[OF True])
    obtain rr sss where unapp2: "unapp a t1 = (rr,sss)" by (cases "unapp a t1", auto)
    with True Fun ts have "unapp a (Fun f ts) = (rr,sss @ [t2])" by auto
    with Fun have r: "r = rr" and ss: "ss = sss @ [t2]" by auto
    from Fun(1)[unfolded ts r, OF _ unapp2]
    show ?thesis unfolding r by auto
  qed
qed

lemma unapp_root_fun: assumes "unapp a t = (Fun f ss,ts)"
  shows "\<not> (f = a \<and> length ss = 2)"
proof 
  assume ass: "f = a \<and> length ss = 2"
  obtain x y where "ss = [x,y]" by (rule obtain_length2_conj[OF ass])
  with unapp_root[OF assms] ass show False by auto
qed

lemma unapp_apply_var: "unapp a (apply_args a (Var x) ss) = (Var x,ss)"
  by (rule unapp_apply_non_app, simp)

lemma unapp_apply_fun: assumes nonapp: "\<not> (f = a \<and> length ts = 2)" 
  shows "unapp a (apply_args a (Fun f ts) ss) = (Fun f ts,ss)"
proof (rule unapp_apply_non_app)
  fix t1 t2
  show "Fun f ts \<noteq> Fun a [t1,t2]"
  proof
    assume "Fun f ts = Fun a [t1,t2]"
    then have "f = a \<and> length ts = 2" by simp
    with nonapp show False .. 
  qed
qed

    

lemma unapp_size_root: assumes "unapp a t = (r,ts)"
  shows "size r \<le> size t"
using assms
proof (induct t arbitrary: ts )
  case (Var x) then show ?case by simp
next
  case (Fun f ss)
  show ?case 
  proof (cases "f = a \<and> length ss = 2")
    case False
    with Fun show ?thesis by auto
  next
    case True
    obtain u v where ss: "ss = [u,v]" by (rule obtain_length2_conj[OF True])
    obtain rr sss where unapp: "unapp a u = (rr,sss)" by (cases "unapp a u", auto)
    from Fun(2) have "unapp a (Fun f ss) = (rr, sss @ [v])"
      by (simp add: True unapp ss)
    with Fun(2) have r: "r = rr" and ts: "ts = sss @ [v]" by auto
    from Fun(1)[unfolded r ss, OF _ unapp, simplified] have "size r \<le> size u" 
      unfolding r by simp
    then show ?thesis unfolding ss by simp
  qed
qed


lemma unapp_size_arg: assumes "unapp a t = (r,ts)" and "s \<in> set ts"
  shows "size s < size t"
using assms
proof (induct t arbitrary: ts )
  case (Var x) then show ?case by simp
next
  case (Fun f ss)
  show ?case 
  proof (cases "f = a \<and> length ss = 2")
    case False
    with Fun show ?thesis by auto
  next
    case True
    obtain u v where ss: "ss = [u,v]" by (rule obtain_length2_conj[OF True])
    obtain rr sss where unapp: "unapp a u = (rr,sss)" by (cases "unapp a u", auto)
    from Fun(2) have "unapp a (Fun f ss) = (rr, sss @ [v])"
      by (simp add: True unapp ss)
    with Fun(2) have r: "r = rr" and ts: "ts = sss @ [v]" by auto
    from Fun(1)[unfolded r ss, OF _ unapp, simplified] have rec: "s \<in> set sss \<Longrightarrow> size s < size u"
      by simp
    from Fun(3)[unfolded ts] have "s \<in> set sss \<or> s = v" by auto
    then show ?thesis
    proof
      assume "s \<in> set sss"
      from rec[OF this] show ?thesis unfolding ss by simp
    next
      assume "s = v" then show ?thesis unfolding ss by simp
    qed
  qed
qed

lemma unapp_size_intro1: assumes "(x, ys) = unapp a t" and "x = Fun f xs" and mem: "y \<in> set (xs @ ys)"
       shows "size y < size t"
proof - 
  from assms have unapp: "unapp a t = (Fun f xs, ys)" by auto
  from mem have "y \<in> set xs \<or> y \<in> set ys" by auto
  then show ?thesis
  proof
    assume "y \<in> set xs"
    then have "size y < size (Fun f xs)" by (auto simp: size_simps)
    with unapp_size_root[OF unapp] 
    show ?thesis by simp
  next
    assume "y \<in> set ys"
    from unapp_size_arg[OF unapp this]
    show ?thesis by simp
  qed
qed


declare unapp_size_intro1[intro]

fun hvf_term :: "'f \<Rightarrow> ('f,'v)term \<Rightarrow> bool"        
where "hvf_term a t = (case unapp a t of 
            (Var _, ts) \<Rightarrow> ts = []
          | (Fun f us, ts) \<Rightarrow> Ball (set (us @ ts)) (hvf_term a))
      "


lemma applicative_term_induct[case_names Var Fun]:
  assumes var_IH: "\<And> x ts. (\<And> t. t \<in> set ts \<Longrightarrow> P t) \<Longrightarrow> P (apply_args a (Var x) ts)"
    and   fun_IH: "\<And> f ss ts. \<lbrakk>\<And> t. t \<in> set ts \<Longrightarrow> P t; \<And> s. s \<in> set ss \<Longrightarrow> P s; \<not> (f = a \<and> length ss = 2)\<rbrakk> \<Longrightarrow>
                P (apply_args a (Fun f ss) ts)"
  shows "P t"
proof (induct rule: wf_induct[of _ P, OF wf_measures])
  fix t
  assume "\<forall> s. (s,t) \<in> measures [size] \<longrightarrow> P s"
  then have ind: "\<And> s. size s < size t \<Longrightarrow> P s" by auto
  obtain r ts where unapp: "unapp a t = (r,ts)" by (cases "unapp a t", auto)
  from ind[OF unapp_size_arg[OF unapp]] have indt: "\<And> t. t \<in> set ts \<Longrightarrow> P t" by auto
  from unapp_apply_args[OF unapp] have t: "t = apply_args a r ts" .
  show "P t" unfolding t
  proof (cases r)
    case (Var x)
    show "P (apply_args a r ts)"
      unfolding Var
      by (rule var_IH, rule indt)
  next
    case (Fun f ss)
    note unapp = unapp[unfolded Fun]
    have napp: "\<not> (f = a \<and> length ss = 2)"
      by (rule unapp_root_fun[OF unapp])
    from unapp_size_root[OF unapp] have s1: "size (Fun f ss) \<le> size t" .
    {
      fix s
      assume "s \<in> set ss"
      then have "size s < size (Fun f ss)" by (auto simp: size_simps)
      from this s1 have "size s < size t" by simp
      note ind[OF this]
    } note inds = this
    from fun_IH[OF indt inds napp]
    show "P (apply_args a r ts)" unfolding Fun .
  qed
qed



lemma hvf_term_induct[consumes 1,case_names Var Fun]: assumes app: "hvf_term a t"
  and ind_var: "\<And> x. P (Var x)"
  and fun_IH: "\<And> f ss ts. ((\<And> t. t \<in> set ts \<Longrightarrow> P t) \<Longrightarrow> (\<And> s. s \<in> set ss \<Longrightarrow> P s) \<Longrightarrow> (\<And> t. t \<in> set ts \<Longrightarrow> hvf_term a t) \<Longrightarrow> 
               (\<And> s. s \<in> set ss \<Longrightarrow> hvf_term a s) \<Longrightarrow> \<not> (f = a \<and> length ss = 2) \<Longrightarrow>
                P (apply_args a (Fun f ss) ts))"
  shows "P t"
proof -
  have "hvf_term a t \<longrightarrow> P t" (is "?P t")
  proof (induct rule: wf_induct[of _ ?P, OF wf_measures])
    fix t
    assume "\<forall> s. (s,t) \<in> measures [size] \<longrightarrow> ?P s"
    then have ind: "\<And> s. \<lbrakk>hvf_term a s; size s < size t\<rbrakk> \<Longrightarrow> P s" by auto
    obtain r ts where unapp: "unapp a t = (r,ts)" by (cases "unapp a t", auto)
    from unapp_apply_args[OF unapp] have t: "t = apply_args a r ts" .
    show "?P t" unfolding t
    proof
      assume hvf: "hvf_term a (apply_args a r ts)"
      note unapp = unapp[unfolded t]
      show "P (apply_args a r ts)"
      proof (cases r)
        case (Var x)
        show "P (apply_args a r ts)"
        proof (cases ts)
          case Nil then show ?thesis unfolding Var using ind_var by auto
        next
          case (Cons t tts)
          from hvf[simplified, simplified unapp, unfolded Var Cons] 
          show ?thesis by auto
        qed
      next
        case (Fun f ss)
        note unapp = unapp[unfolded Fun]
        note hvf = hvf[unfolded Fun]
        note ind = ind[unfolded t Fun]
        from hvf have hvfs: "\<And> s. s \<in> set ss \<Longrightarrow> hvf_term a s" by (auto simp: unapp)
        from hvf have hvft: "\<And> t. t \<in> set ts \<Longrightarrow> hvf_term a t" by (auto simp: unapp)
        from ind[OF hvft unapp_size_arg[OF unapp]] have indt: "\<And> t. t \<in> set ts \<Longrightarrow> P t" . 
        {
          fix s
          assume s: "s \<in> set ss"
          then have "size s < size (Fun f ss)" by (auto simp: size_simps)
          with unapp_size_root[OF unapp]
          have "size s < size (apply_args a (Fun f ss) ts)" by simp
          note ind[OF hvfs[OF s] this]
        } note inds = this
        have napp: "\<not> (f = a \<and> length ss = 2)"
          by (rule unapp_root_fun[OF unapp])        
        show ?thesis unfolding Fun
          by (rule fun_IH[OF indt inds hvft hvfs napp])
      qed
    qed
  qed
  with app show ?thesis by simp
qed

(* store for each original symbol f/n a non-empty list of symbols
   [f0,f1,..,f_aa] *)
type_synonym 'f sig_map = "'f \<Rightarrow> nat \<Rightarrow> 'f list"

definition get_symbol :: "'f sig_map \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'f"
  where "get_symbol sm f n i \<equiv> sm f n ! i"

definition aarity :: "'f sig_map \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> nat"
  where "aarity sm f n \<equiv> length (sm f n) - 1"

lemma unapp_size_intro2: assumes "(x, ys) = unapp a t" and "x = Fun f xs" and mem: "y \<in> set xs"
       shows "size y < size t"
  using assms unapp_size_intro1  by auto

lemma unapp_size_intro3: assumes "(x, ys) = unapp a t" and mem: "y \<in> set ys"
       shows "size y < size t"
  using unapp_size_arg[OF assms(1)[symmetric] assms(2)] .

declare unapp_size_intro2[intro]
declare unapp_size_intro3[intro]


fun uncurry_term :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term"
where "uncurry_term a sm t = (case unapp a t of
           (Var x,ts) \<Rightarrow> apply_args a (Var x) (map (uncurry_term a sm) ts)
         | (Fun f ss,ts) \<Rightarrow> (
          let n = length ss;
              uss = map (uncurry_term a sm) ss;
              uts = map (uncurry_term a sm) ts;
              aa  = aarity sm f n;
              m   = min (length ts) aa;
              fm  = get_symbol sm f n m
            in apply_args a (Fun fm (uss @ take m uts)) (drop m uts)))"

declare uncurry_term.simps[simp del]

abbreviation uncurry_subst where
"uncurry_subst a sm \<sigma> \<equiv> (\<lambda>x. uncurry_term a sm (\<sigma> x))"

lemma uncurry_apply_args_fun: assumes "\<not> (f = a \<and> length ss = 2)"
  shows "uncurry_term a sm (apply_args a (Fun f ss) ts) = 
  apply_args a (Fun (get_symbol sm f (length ss) (min (length ts) (aarity sm f (length ss)))) (map (uncurry_term a sm) ss @ take (min (length ts) (aarity sm f (length ss))) (map (uncurry_term a sm) ts))) (drop (min (length ts) (aarity sm f (length ss))) (map (uncurry_term a sm) ts))"
  by (unfold uncurry_term.simps[where t =  "apply_args a (Fun f ss) ts"] unapp_apply_fun[OF assms], simp add: Let_def)

lemma uncurry_apply_args_var: 
  "uncurry_term a sm (apply_args a (Var x) ts) = 
  apply_args a (Var x) (map (uncurry_term a sm) ts)"
  by (unfold uncurry_term.simps[where t =  "apply_args a (Var x) ts"] unapp_apply_var, simp)

lemma uncurry_subst_hvf: "hvf_term a t \<Longrightarrow> 
  uncurry_term a sm (t \<cdot> \<sigma>) =  uncurry_term a sm t \<cdot> uncurry_subst a sm \<sigma>"
proof (induct t rule: hvf_term_induct)
  case (Var x)
  then show ?case by (simp add: uncurry_term.simps)
next
  case (Fun f ss ts)
  show ?case (is "?l = ?r")
  proof -
    from Fun(5) have nappsig: "\<not> (f = a \<and> length (map (\<lambda> s. s \<cdot> \<sigma>) ss) = 2)" by simp 
    from Fun(2) have indss:  "(map (\<lambda>x. uncurry_term a sm (x \<cdot> \<sigma>)) ss) = (map (\<lambda> x. uncurry_term a sm x \<cdot> uncurry_subst a sm \<sigma>) ss)"
      by auto
    from Fun(1) have indts:  "(map (\<lambda>x. uncurry_term a sm (x \<cdot> \<sigma>)) ts) = (map (\<lambda> x. uncurry_term a sm x \<cdot> uncurry_subst a sm \<sigma>) ts)"
      by auto
    show ?thesis
      by (unfold uncurry_apply_args_fun[OF Fun(5)] apply_args_subst, simp, unfold uncurry_apply_args_fun[OF nappsig], 
        simp add: o_def indss indts take_map drop_map)
  qed
qed


definition generate_var :: "nat \<Rightarrow> string"
where "generate_var i \<equiv> (CHR ''x'') # show i"

lemma inj_generate_var: "inj generate_var" 
  unfolding inj_on_def generate_var_def using inj_show_nat[unfolded inj_on_def] by auto

definition generate_f_xs :: "'f \<Rightarrow> nat \<Rightarrow> ('f,string)term"
where "generate_f_xs f n \<equiv> Fun f (map (\<lambda> i. Var (generate_var i)) [0 ..< n])"

definition uncurry_of_sig :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,string)trs"
where "uncurry_of_sig a sm \<equiv> {(Fun a [generate_f_xs (get_symbol sm f n i) (n + i), Var (generate_var (n + i))],generate_f_xs (get_symbol sm f n (Suc i)) (n + Suc i)) | f n i. i < aarity sm f n}"

lemma apply_arg_uncurry_of_sig:
  assumes n: "n < aarity sm f m"
  and len: "length ts = m + n"
  shows "(Fun a [Fun (get_symbol sm f m n) ts, t], Fun (get_symbol sm f m (Suc n)) (ts @ [t])) \<in> subst.closure (uncurry_of_sig a sm)" (is "(?l, ?r) \<in> subst.closure ?U") 
proof -
  let ?ll = "Fun a [generate_f_xs (get_symbol sm f m n) (m + n), Var (generate_var (m + n))]"
  let ?rr = "generate_f_xs (get_symbol sm f m (Suc n)) (m + Suc n)"
  let ?sigma = "(\<lambda>x. (ts @ [t]) ! (the_inv generate_var) x)"
  show ?thesis
  proof (rule subst.closureI2)
    show "(?ll, ?rr) \<in> uncurry_of_sig a sm" unfolding uncurry_of_sig_def using n by blast
  next
    show "?l = ?ll \<cdot> ?sigma"
      unfolding  generate_f_xs_def 
      by (simp add: o_def the_inv_f_f[OF inj_generate_var], unfold len[symmetric], simp, rule nth_equalityI, auto simp: nth_append)
  next
    show "?r = ?rr \<cdot> ?sigma"
      unfolding  generate_f_xs_def 
      by  (simp add: o_def the_inv_f_f[OF inj_generate_var], unfold len[symmetric], simp, rule nth_equalityI, auto simp: nth_append)
  qed
qed

lemma apply_args_uncurry_of_sig: assumes xs: "length ts = m + n"
  and aarity: "n + length us \<le> aarity sm f m"
  shows "(apply_args a (Fun (get_symbol sm f m n) ts) us, Fun (get_symbol sm f m (n + length us)) (ts @ us)) 
  \<in> (rstep (uncurry_of_sig a sm))^*" (is "_ \<in> ?U^*")
using xs aarity
proof (induct us arbitrary: ts n)
  case Nil
  then show ?case by auto
next
  case (Cons u us)
  from Cons(2) Cons(3) have n: "n < aarity sm f m"  by auto
  have step: "(Fun a [Fun (get_symbol sm f m n) ts, u], Fun (get_symbol sm f m (Suc n)) (ts @ [u])) \<in> ?U" (is "(Fun a [?l,_], ?r) \<in> _")
    using apply_arg_uncurry_of_sig[OF n Cons(2)] unfolding rstep_eq_closure
    using ctxt.subset_closure by auto
  have step: "(apply_args a ?l (u # us), apply_args a ?r us) \<in> ?U"
    by (simp, rule apply_args_root_rel[OF ctxt_closed_rstep step])
  have id1: "ts @ u # us = (ts @ [u]) @ us" by auto
  have id2: "n + length (u # us) = Suc n + length us" by auto
  show ?case
    by (rule converse_rtrancl_into_rtrancl[OF step], unfold id1 id2, rule Cons(1), insert Cons(2) Cons(3), auto)
qed


lemma apply_args_uncurry: 
  "(apply_args a (uncurry_term a sm t) (map (uncurry_term a sm) ts), uncurry_term a sm (apply_args a t ts)) 
  \<in> (rstep (uncurry_of_sig a sm))^*" 
  (is "(_,?u (apply_args a t ts)) \<in> ?U")
proof (induct t rule: applicative_term_induct[where a = a])
  case (Var x us)
  show ?case
    by (unfold apply_args_append[symmetric] uncurry_apply_args_var, simp)
next
  case (Fun f ss us)
  obtain u where u: "?u = u" by auto
  obtain aa where aa: "aarity sm f (length ss) = aa" by auto
  obtain m where m: "min (length us + length ts) aa = m" by auto
  obtain n where n: "min (length us) aa = n" by auto
  obtain xs where xs: "map u ss @ take n (map u us) = xs" by simp
  from m n have nm: "n \<le> m" and nu: "n - length us = 0" by auto
  then have "m = n + (m - n)" by auto
  with m obtain m where m: "min (length us + length ts) aa = n + m" by auto
  obtain ys where ys: "drop (n + m - length us) ts = ys" by auto
  then have ys': "drop (n + m - length us) (map u ts) = map u ys" by (auto simp: drop_map)
  obtain zs where zs: "take (n + m - length us) ts = zs" by auto
  have ts: "ts = zs @ ys" unfolding ys[symmetric] zs[symmetric] by force
  have id1: "map u ss @ take n (map u us) @ take m (drop n (map u us) @ map u ts) = 
    xs @ take m (drop n (map u us) @ map u ts)" unfolding xs[symmetric] by simp
  have "map u ts = map u zs @ map u ys" unfolding ts
    by simp
  also have "\<dots> = map u (take (n + m - length us) ts) @ map u ys" unfolding zs ..
  finally have id2: "map u ts = map u (take (n + m - length us) ts) @ map u ys" by simp
  obtain g where g: "get_symbol sm f (length ss) = g" by auto
  show ?case
  proof (unfold apply_args_append[symmetric] uncurry_apply_args_fun[OF Fun(3)], simp add: u aa m n g take_map[symmetric] drop_append[symmetric]
      del: take_append, unfold take_add[of n m] take_append[of n], simp add: xs nu id1 ys' del: take_append map_append,
      unfold arg_cong[OF id2, of "\<lambda> t. apply_args a (Fun (g n) xs) (drop n (map u us) @ t)"],
      simp add: take_map[symmetric] del: take_append
    )
    show "(apply_args a (Fun (g n) xs)
      (drop n (map u us) @ take (n + m - length us) (map u ts) @ map u ys),
     apply_args a
      (Fun (g (n + m)) (xs @ take m (drop n (map u us) @ map u ts)))
      (drop (n + m) (map u us) @ map u ys))
    \<in> ?U" (is "(?l,?r) \<in> _")
    proof (cases "n = length us")
      case False
      with n have n: "n = aa" by simp
      with m have m: "m = 0" by auto
      from m nu have "?l = apply_args a (Fun (g n) xs)
         (drop n (map u us) @ map u ys)" by simp
      also have "\<dots> = ?r" using m by simp
      finally show ?thesis by simp
    next
      case True
      from True have l: "?l = apply_args a (apply_args a (Fun (g n) xs) (take m (map u ts))) (map u ys)" by (auto simp: apply_args_append)
      from True have r: "?r = apply_args a (Fun (g (n+m)) (xs @ take m (map u ts))) (map u ys)" by simp
      show ?thesis unfolding l r 
      proof (rule apply_args_rsteps)
        have len1: "length xs = length ss + n" unfolding xs[symmetric] using True by simp
        from m  have "m \<le> length ts" and "n + m \<le> aa"  unfolding True[symmetric] by auto
        then have len2: "n + length (take m (map u ts)) \<le> aarity sm f (length ss)" 
          and m: "n + m = n + length (take m (map u ts))" unfolding aa by auto
        show "(apply_args a (Fun (g n) xs) (take m (map u ts)), Fun (g (n+m)) (xs @ take m (map u ts))) \<in> ?U"
          unfolding g[symmetric] m
          by (rule apply_args_uncurry_of_sig[OF len1 len2])
      qed auto
    qed
  qed
qed
    


lemma uncurry_subst:
  fixes \<sigma> :: "('f, string) subst"
  shows "(uncurry_term a sm t \<cdot> uncurry_subst a sm \<sigma>, uncurry_term a sm (t \<cdot> \<sigma>)) \<in> (rstep (uncurry_of_sig a sm))^*" (is "(?u t \<cdot> ?us,_) \<in> ?U")
proof -
  let ?m = "map (\<lambda>x. ?u x \<cdot> ?us)"
  let ?n = "map (\<lambda>x. ?u (x \<cdot> \<sigma>))"
  let ?k = "\<lambda> ts. map ?u (map (\<lambda> x. x \<cdot> \<sigma>) ts)"
  show ?thesis
  proof (induct t rule: applicative_term_induct[where a = a])
    case (Fun f ss ts)
    from Fun(3) have napp: "\<not> (f = a \<and> length (map (\<lambda>t. t \<cdot> \<sigma>) ss) = 2)" by simp
    obtain g where g: " (get_symbol sm f (length ss)
      (min (length ts) (aarity sm f (length ss)))) = g" by auto
    obtain m where m: " (min (length ts) (aarity sm f (length ss))) = m" by auto
    show ?case
    proof (simp add: apply_args_subst, unfold uncurry_apply_args_fun[OF Fun(3)] uncurry_apply_args_fun[OF napp], simp add: o_def g, simp add: m,
        simp add: apply_args_subst, simp add: o_def, rule apply_args_rsteps, rule args_rsteps_imp_rsteps, simp_all, simp add: take_map o_def,
        intro allI impI)
      fix i
      assume "i < length ts - m"
      then show "(?u (ts ! (m+i)) \<cdot> ?us, ?u (ts ! (m+i) \<cdot> \<sigma>)) \<in> ?U" using Fun(1) by auto
    next
      fix i
      assume i: "i < length ss + min (length ts) m"
      show "((?m ss @ ?m (take m ts)) ! i, (?n ss @ ?n (take m ts)) ! i) \<in> ?U"
      proof (cases "i < length ss")
        case True
        then show ?thesis using Fun(2) by (auto simp: nth_append)
      next
        case False
        then have "i - length ss < min (length ts) m" using i by auto
        then have "i - length ss < length (take m ts)" by auto
        then show ?thesis using False Fun(1) by (auto simp: nth_append)
      qed
    qed
  next
    case (Var x ts)
    show ?case 
    proof (unfold apply_args_subst uncurry_apply_args_var, simp add: o_def, rule rtrancl_trans, rule apply_args_rsteps[OF rtrancl_refl])
      show "length (?m ts) = length (?k ts)" by simp
    next
      fix i
      assume "i < length (?m ts)"
      with Var show "(?m ts ! i, ?k ts ! i) \<in> ?U" by auto
    qed (rule apply_args_uncurry)
  qed
qed



definition uncurry_trs :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs"
where "uncurry_trs a sm R \<equiv> (\<lambda>(l,r). (uncurry_term a sm l, uncurry_term a sm r)) ` R"



fun unapp_ctxt :: "'f \<Rightarrow> ('f,'v)ctxt \<Rightarrow> (('f,'v)ctxt \<times> (('f,'v)term)list)"
where "unapp_ctxt a Hole = (Hole,[])"
   |  "unapp_ctxt a (More f bef C aft) = (if f = a \<and> bef = [] \<and> length aft = 1 then 
               (case unapp_ctxt a C of (r,ts) \<Rightarrow> (r,ts @ aft)) else (More f bef C aft, []))"


fun apply_args_ctxt :: "'f \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)term list \<Rightarrow> ('f,'v)ctxt"
where "apply_args_ctxt a C [] = C"
    | "apply_args_ctxt a C (s # ss) = apply_args_ctxt a (More a [] C [s]) ss"

lemma apply_args_ctxt_last: "apply_args_ctxt a C (ss @ [s]) = More a [] (apply_args_ctxt a C ss) [s]"
  by (induct ss arbitrary: C, auto)

lemma unapp_apply_args_ctxt: assumes "unapp_ctxt a C = (D,ss)"
  shows "C = apply_args_ctxt a D ss"
using assms
proof (induct C arbitrary: ss)
  case Hole
  then show ?case by auto
next
  case (More f bef E aft)
  show ?case
  proof (cases "f = a \<and> bef = [] \<and> length aft = 1")
    case False
    then show ?thesis using More(2) by auto
  next
    case True
    then obtain t where aft: "aft = [t]" by (cases aft, auto)
    obtain DD sss where us: "unapp_ctxt a E = (DD,sss)" by (cases "unapp_ctxt a E", auto)
    from More(2) have "unapp_ctxt a (More f bef E aft) = (DD, sss @ [t])"      
      by (simp add: True aft us)
    with More(2) have D: "D = DD" and ss: "ss = (sss @ [t])" by auto
    show ?thesis 
      unfolding aft D ss  More(1)[unfolded aft True D, OF us] apply_args_ctxt_last
      using True by simp
  qed
qed


lemma unapp_ctxt_root: "unapp_ctxt a C = (D,ss) \<Longrightarrow> D \<noteq> More a [] E [v]"
proof (induct C arbitrary: ss)
  case Hole then show ?case by auto
next
  case (More f bef F aft)
  show ?case  
  proof (cases "f = a \<and> bef = [] \<and> length aft = 1")
    case False
    then show ?thesis using More by auto
  next
    case True
    then obtain t where aft: "aft = [t]" by (cases aft, auto)
    obtain G sss where unapp2: "unapp_ctxt a F = (G,sss)" by (cases "unapp_ctxt a F", auto)
    with True More aft have "unapp_ctxt a (More f bef F aft) = (G,sss @ [t])" by auto
    with More have D: "D = G" and ss: "ss = sss @ [t]" by auto
    from More(1)[unfolded aft D, OF unapp2]
    show ?thesis unfolding D by auto
  qed
qed

fun size_ctxt :: "('f,'v)ctxt \<Rightarrow> nat" where
  "size_ctxt Hole = 0"
| "size_ctxt (More f as c bs) =
     size_list size as + size_list size bs +
  size_ctxt c + Suc 0" 



lemma unapp_ctxt_size_root: assumes "unapp_ctxt a C = (D,ts)"
  shows "size_ctxt D \<le> size_ctxt C"
using assms
proof (induct C arbitrary: ts )
  case Hole then show ?case by simp
next
  case (More f bef C aft)
  show ?case 
  proof (cases "f = a \<and> bef = [] \<and> length aft = 1")
    case False
    with More show ?thesis by auto
  next
    case True
    then obtain u where aft: "aft = [u]" by (cases aft, auto)
    obtain DD sss where unapp: "unapp_ctxt a C = (DD,sss)" by (cases "unapp_ctxt a C", auto)
    from More(2) have "unapp_ctxt a (More f bef C aft) = (DD, sss @ [u])"
      by (simp add: True unapp aft)
    with More(2) have D: "D = DD" and ts: "ts = sss @ [u]" by auto
    from More(1)[unfolded D aft, OF unapp, simplified] 
    show ?thesis unfolding D by auto 
  qed
qed

lemma apply_args_ctxt_insert: "(apply_args_ctxt a C ss)\<langle>t\<rangle> = apply_args a (C\<langle>t\<rangle>) ss"
  by (induct ss arbitrary: C, auto)


lemma apply_args_arg_rsteps:
  assumes ctxt: "ctxt.closed R"
    and steps: "(u,v) \<in> R"
  shows "(apply_args a t (bef @ u # aft), apply_args a t (bef @ v # aft)) \<in> R"
proof -
  show ?thesis
  proof (induct bef arbitrary: t)
    case Nil
    show ?case by (simp, 
      rule apply_args_root_rel[OF ctxt], insert steps ctxt_closed_one[OF ctxt, of _ _ a "[t]"], auto)
  next
    case (Cons b bef t)
    show ?case
      by (simp, rule Cons)
  qed
qed

definition aarity_term :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)term \<Rightarrow> nat option"
where "aarity_term a sm t \<equiv> case (unapp a t) of (Fun f ss,ts) \<Rightarrow> Some (aarity sm f (length ss) - (length ts)) | (Var _,_) \<Rightarrow> None"

lemma aarity_term_subst: assumes "aarity_term a sm t = Some i"
  shows "aarity_term a sm (t \<cdot> \<sigma>) = Some i"
proof -
  obtain r ts where unapp: "unapp a t = (r,ts)" by (cases "unapp a t", auto)
  show ?thesis 
  proof (cases r)
    case (Var x)
    with assms unapp show ?thesis unfolding aarity_term_def by auto
  next
    case (Fun f ss)
    note unapp = unapp[unfolded Fun]
    from unapp_root_fun[OF unapp]
    have napp: "\<And> g. \<not> (f = a \<and> length (map g ss) = 2)" by auto          
    show ?thesis unfolding aarity_term_def unapp_apply_args[OF unapp] apply_args_subst 
      by (simp add: unapp_apply_fun[OF napp], insert unapp assms, unfold aarity_term_def, simp)
  qed
qed
    
  
lemma uncurry_aarity: assumes "aarity_term a sm t \<in> {Some 0, None}"
  shows "uncurry_term a sm (apply_args a t ts) = apply_args a (uncurry_term a sm t) (map (uncurry_term a sm) ts)"
using assms
proof (induct t rule: applicative_term_induct[where a = a])
  case (Var x ss)
  show ?case unfolding uncurry_apply_args_var apply_args_append[symmetric] by auto
next
  case (Fun f ss us)
  obtain aa where aa: "aarity sm f (length ss) = aa" by auto
  from unapp_apply_fun[OF Fun(3), of us] Fun(4)[unfolded aarity_term_def] 
  have "aa - length us = 0" by (auto simp: aa)
  then have id1: "min (length us + length ts) aa = min (length us) aa" by auto 
  show ?case unfolding apply_args_append[symmetric] uncurry_apply_args_fun[OF Fun(3)]
    by (simp add: aa id1)
qed

lemma size_apply_args_ctxt: "size_ctxt (apply_args_ctxt a C ss) = size_ctxt C + size_list size ss + length ss"
  by (induct ss arbitrary: C, auto)

definition eta_closed :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool"
where "eta_closed a sm R R' \<equiv> \<forall> l r aa. (l,r) \<in> R \<longrightarrow> aarity_term a sm l = Some aa \<longrightarrow> aa > 0 \<longrightarrow> (\<exists> ll rr y. instance_rule (l,r) (ll,rr) \<and> y \<notin> vars_rule (ll,rr) \<and> (Fun a [ll,Var y], Fun a [rr,Var y]) \<in> R')"

lemma uncurry_step:
  assumes hvfR: "\<And> l r. (l,r) \<in> R \<Longrightarrow> hvf_term a l"
    and eta: "eta_closed a sm R R"
    and trs: "\<And> x r. (Var x,r) \<notin> R"
    (* new condition in comparison to paper. E.g. x \<rightarrow> f x, then f x \<rightarrow> f f x,
    but f(x) \<rightarrow> f(f) x" does not hold for U(R) = x \<rightarrow> f(x) *)
    and step: "(s,t) \<in> rstep R"
  shows "(uncurry_term a sm s, uncurry_term a sm t) \<in> rel_qrstep (nfs,{},uncurry_trs a sm R, uncurry_of_sig a sm)" (is "_ \<in> rel_qrstep (_,_,?R,?S)")
proof -
  let ?u = "uncurry_term a sm"
  let ?size = size_ctxt
  from step show ?thesis unfolding qrstep_rstep_conv split
  proof (induct)
    case (IH C \<sigma> l r)
    from IH show ?case (is "_ \<in> ?U")
    proof (induct C arbitrary: l r \<sigma> rule: wf_induct[OF wf_measures[of "[?size]"]])
      case (1 C)
      have ctxtU: "ctxt.closed ?U" by blast
      let ?us = "uncurry_subst a sm \<sigma>"
      let ?tCs = "\<lambda> t C s. C\<langle>t \<cdot> s\<rangle>"
      let ?tCsig = "\<lambda> t C. C\<langle>t \<cdot> \<sigma>\<rangle>"
      let ?lC = "?tCsig l"
      let ?rC = "?tCsig r"
      note lr = 1(2)
      from lr hvfR have hvfl: "hvf_term a l"by auto
      from 1(1) have ind_gen: "\<And> l r D s. (l,r) \<in> R \<Longrightarrow>  ?size D < ?size C \<Longrightarrow> (?u (?tCs l D s), ?u (?tCs r D s)) \<in> ?U" by auto
      note ind = ind_gen[OF lr, of _ \<sigma>]
      obtain D ss where unapp: "unapp_ctxt a C = (D,ss)" by (cases "unapp_ctxt a C", auto)
      from unapp_ctxt_root[OF unapp] have napp: "\<And> E t. D \<noteq> More a [] E [t]" .
      from unapp_apply_args_ctxt[OF unapp] have C: "C = apply_args_ctxt a D ss" (is "_ = ?C") by auto
      from unapp_ctxt_size_root[OF unapp] have size: "?size D \<le> ?size C" by auto
      show ?case 
      proof (cases D)
        case (More f bef E aft)
        obtain u v where u: "?tCsig l E = u" and v: "?tCsig r E = v" by auto
        show ?thesis unfolding C More apply_args_ctxt_insert
        proof (simp add: u v)
          from size More have "?size E < ?size C" by auto
          note ind = ind[OF this]
          note steps = ind[unfolded u v]
          show "(?u (apply_args a (Fun f (bef @ u # aft)) ss),
                 ?u (apply_args a (Fun f (bef @ v # aft)) ss)) \<in> ?U"
          proof (cases "f = a \<and> length bef + length aft = 1")
            case False
            then have napp: "\<And> x. \<not> (f = a \<and> length (bef @ x # aft) = 2)" by auto
            obtain g where g: "(get_symbol sm f (Suc (length bef + length aft))
             (min (length ss) (aarity sm f (Suc (length bef + length aft))))) = g" by auto
            obtain bbef where bbef: "map ?u bef = bbef" by auto
            obtain aaft where aaft: "map (uncurry_term a sm) aft @ take (min (length ss) (aarity sm f (Suc (length bef + length aft))))
                 (map (uncurry_term a sm) ss) = aaft" by auto
            show ?thesis 
              unfolding uncurry_apply_args_fun[OF napp] 
              by (simp, rule apply_args_root_rel[OF ctxtU], rule ctxt_closed_one[OF ctxtU steps])
          next
            case True
            show ?thesis
            proof (cases bef)
              case (Cons b bbef)
              with True have f: "f = a" and bef: "bef = [b]" and aft: "aft = []" by auto
              show ?thesis unfolding f bef aft
              proof (simp)
                show "(?u (apply_args a (Fun a [b,u]) ss), ?u (apply_args a (Fun a [b,v]) ss)) \<in> ?U"
                proof (cases "aarity_term a sm b \<in> {Some 0, None}")
                  case True
                  note ua = uncurry_aarity[OF True]                  
                  show ?thesis unfolding apply_args.simps(2)[symmetric]
                    unfolding ua[of "u # ss"]  ua[of "v # ss"]
                    using  apply_args_arg_rsteps[OF ctxtU steps, of a "?u b" "[]" "map ?u ss"] by auto
                next
                  case False
                  obtain r ts where unapp: "unapp a b = (r,ts)" by (cases "unapp a b", auto)              
                  from unapp_apply_args[OF unapp] have b: "b = apply_args a r ts" by auto
                  from False obtain g us where Fun: "r = Fun g us" unfolding b by (cases r, auto simp: aarity_term_def unapp_apply_var)
                  obtain h where h: "h = get_symbol sm g (length us) (min (Suc (length ts + length ss)) (aarity sm g (length us)))" by auto
                  obtain n where n: "n = min (length (ts @ t # ss)) (aarity sm g (length us))" by auto
                  obtain uus where uus: "uus = map (uncurry_term a sm) us" by auto
                  obtain uts where uts: "uts = map (uncurry_term a sm) ts" by auto
                  obtain uss where uss: "uss = map (uncurry_term a sm) ss" by auto
                  let ?t = "\<lambda> t. apply_args a (Fun h (uus @ take n  (uts @ ?u t # uss)))  (drop n (uts @ ?u t # uss))" 
                  have napp: "\<not> (g = a \<and> length us = 2)"
                  proof
                    assume ass: "g = a \<and> length us = 2"
                    from obtain_length2_conj[OF this] obtain y z where "us = [y,z]" by blast
                    with unapp_root[OF unapp, unfolded Fun] ass show False by auto
                  qed                  
                  {
                    fix t
                    have "?u (apply_args a (Fun a [b,t]) ss) = ?u (apply_args a (Fun a [apply_args a (Fun g us) ts,t]) ss)"
                      unfolding f bef aft b Fun by simp
                    also have "\<dots> = ?u (apply_args a (Fun g us) (ts @ t # ss))" unfolding apply_args_last[symmetric] apply_args_append[symmetric]
                      by simp
                    also have "\<dots> = ?t t"
                      unfolding uncurry_apply_args_fun[OF napp] by (simp add: h n uus uts uss)
                    finally have "?u (apply_args a (Fun a [b,t]) ss) = ?t t" .
                  } note id = this
                  show ?thesis 
                    unfolding id
                  proof (cases "n \<le> length uts")
                    case False
                    then have n: "n - length uts > 0 \<and> n = length uts + (n - length uts)" by auto
                    then obtain k where n: "n = length uts + Suc k" by (cases "n - length uts", auto)
                    {
                      fix t
                      have "?t t = apply_args a (Fun h (uus @ uts @ uncurry_term a sm t # take k uss)) (drop k uss)" unfolding n 
                        by (simp)
                    } note id = this
                    show "(?t u, ?t v) \<in> ?U" unfolding id
                      by (rule apply_args_root_rel[OF ctxtU], insert ctxt_closed_one[OF ctxtU steps, of h "uus @ uts"], auto) 
                  next
                    case True
                    {
                      fix t
                      have "?t t = apply_args a (Fun h (uus @ take n uts)) (drop n uts @ uncurry_term a sm t # uss)" using True by simp
                    } note id = this
                    show "(?t u, ?t v) \<in> ?U" unfolding id                    
                      by (rule apply_args_arg_rsteps[OF ctxtU steps])
                  qed
                qed
              qed
            next
              case Nil
              with True obtain t where f: "f = a" and aft: "aft = [t]" by (cases aft, auto)
              then show ?thesis using napp[unfolded More, of E t] unfolding f True aft Nil by simp
            qed
          qed
        qed
      next
        case Hole
        then show ?thesis unfolding C Hole apply_args_ctxt_insert
        proof (simp)
          show "(?u (apply_args a (l \<cdot> \<sigma>) ss), ?u (apply_args a (r \<cdot> \<sigma>) ss)) \<in> ?U"
          proof (cases ss)
            case Nil
            have "(?u (l \<cdot> \<sigma>), ?u r \<cdot> ?us) \<in> rstep ?R"
            proof (intro rstepI)
              show "(?u l, ?u r) \<in> ?R" unfolding uncurry_trs_def using lr by auto
            next
              show "?u (l \<cdot> \<sigma>) = \<box>\<langle>?u l \<cdot> ?us\<rangle>" by (simp add: uncurry_subst_hvf[OF hvfl])
            next
              show "?u r \<cdot> ?us = \<box>\<langle>?u r \<cdot> ?us\<rangle>" by simp
            qed 
            moreover have "(?u r \<cdot> ?us, ?u (r \<cdot> \<sigma>)) \<in> (rstep ?S)^*"
              by (rule set_mp[OF rtrancl_mono[OF rstep_mono] uncurry_subst]) simp
            ultimately show ?thesis unfolding Nil by auto
          next
            case (Cons s sss)
            have rsig: "(apply_args a (?u r \<cdot> ?us) (map ?u ss), ?u (apply_args a (r \<cdot> \<sigma>) ss)) \<in> (rstep ?S)^*"
            proof (rule set_mp[OF rtrancl_mono[OF rstep_mono[of "uncurry_of_sig a sm"]]], simp, rule rtrancl_trans)
              show "(apply_args a (?u r \<cdot> ?us) (map ?u ss), apply_args a (?u (r \<cdot> \<sigma>)) (map ?u ss)) \<in> (rstep (uncurry_of_sig a sm))^*"
                by (rule apply_args_rsteps[OF uncurry_subst], auto)
            next
              show "(apply_args a (?u (r \<cdot> \<sigma>)) (map ?u ss), ?u (apply_args a (r \<cdot> \<sigma>) ss)) \<in> (rstep (uncurry_of_sig a sm))^*"
                by (rule apply_args_uncurry)
            qed            
            show ?thesis
            proof (cases "aarity_term a sm (l \<cdot> \<sigma>) \<in> {Some 0, None}")
              case True
              have "?u (apply_args a (l \<cdot> \<sigma>) ss) = apply_args a (?u (l \<cdot> \<sigma>)) (map ?u ss)"
                by (rule uncurry_aarity[OF True])
              also have "\<dots> = apply_args a (?u l \<cdot> ?us) (map ?u ss)"
                unfolding uncurry_subst_hvf[OF hvfl] ..
              finally have lsig: "?u (apply_args a (l \<cdot> \<sigma>) ss) = apply_args a (?u l \<cdot> ?us) (map ?u ss)" .
              have lrsig: "(apply_args a (?u l \<cdot> ?us) (map ?u ss), apply_args a (?u r \<cdot> ?us) (map ?u ss)) \<in> rstep ?R"
                by (rule apply_args_root_rel[OF ctxt_closed_rstep], rule rstepI[where C = \<box>], unfold uncurry_trs_def, insert lr, auto)
              show ?thesis 
                unfolding lsig using lrsig rsig by auto
            next
              case False
              show ?thesis 
              proof (cases "aarity_term a sm l")
                case (Some aa)
                from aarity_term_subst[OF Some, of "\<sigma>"] False
                have "aa > 0" by auto
                from eta[unfolded eta_closed_def] lr Some this obtain ll rr y where inst: "instance_rule (l,r) (ll,rr)" and newRule: "(Fun a [ll,Var y], Fun a [rr,Var y]) \<in> R" and y: "y \<notin> vars_rule (ll,rr)" by blast+
                from inst[unfolded instance_rule_def] obtain \<delta> where l: "l = ll \<cdot> \<delta>" and r: "r = rr \<cdot> \<delta>" by auto
                let ?C = "apply_args_ctxt a \<box> sss" 
                let ?sig = "subst_extend (\<delta> \<circ>\<^sub>s \<sigma>) (zip [y] [s])"
                have "?size ?C < ?size C" unfolding C Hole Cons by (simp add: size_apply_args_ctxt)
                note ind = ind_gen[OF newRule this, of ?sig]
                {
                  fix t :: "('a,string)term"
                  assume y: "y \<notin> vars_term t"
                  then have "t \<cdot> ?sig = t \<cdot> (\<delta> \<circ>\<^sub>s \<sigma>)" 
                    using subst_extend_id[of "UNIV - {y}" "[y]" t "\<delta> \<circ>\<^sub>s \<sigma>" "[s]"] by auto
                  then have "?C\<langle>Fun a [t, Var y] \<cdot> ?sig\<rangle> = apply_args a (t \<cdot> (\<delta> \<circ>\<^sub>s \<sigma>)) ss"
                    unfolding Cons
                    by (simp add: apply_args_ctxt_insert)
                } note id = this
                from y have ly: "y \<notin> vars_term ll" and ry: "y \<notin> vars_term rr" unfolding vars_rule_def by auto
                from ind[unfolded id[OF ly] id[OF ry]]
                show ?thesis unfolding l r by auto
              next
                case None
                then obtain x vs where unappl: "unapp a l = (Var x,vs)" 
                  unfolding aarity_term_def by (cases "unapp a l", cases "fst (unapp a l)", auto)
                with hvfl have l: "l = Var x"
                proof (induct l rule: hvf_term_induct)
                  case (Fun g xs ys)
                  from Fun(6) unapp_apply_fun[OF Fun(5)] show ?case by auto
                qed simp
                show ?thesis using trs lr[unfolded l]  by blast
              qed
            qed
          qed
        qed
      qed
    qed
  qed
qed

lemma uncurry_trs_union: "uncurry_trs a sm (R \<union> R') = uncurry_trs a sm R \<union> uncurry_trs a sm R'" unfolding uncurry_trs_def by auto

(* to see why trsw is required, consider 
   R = {f f x \<rightarrow> f x} and Rw = {x \<rightarrow> f x}. Then R/Rw is not terminating
   whereas the uncurried version is (taking f \<rightarrow> [f/0,f/1,f/2]))
*)
lemma uncurrying_sound: assumes 
       hvfR: "\<And> l r. (l,r) \<in> R_eta \<Longrightarrow> hvf_term a l"
  and hvfRw: "\<And> l r. (l,r) \<in> Rw_eta \<Longrightarrow> hvf_term a l"
  and eta2: "R \<subseteq> R_eta"
  and eta1: "eta_closed a sm R_eta R_eta"
  and eta2w: "Rw \<subseteq> R_eta \<union> Rw_eta"
  and eta1w: "eta_closed a sm (R_eta \<union> Rw_eta) (R_eta \<union> Rw_eta)"
  and trsw: "\<And> x r. (Var x,r) \<notin> Rw_eta" 
  and SN: "SN_qrel (nfs,{}, uncurry_trs a sm R_eta, uncurry_trs a sm Rw_eta \<union> uncurry_of_sig a sm)" (is "SN_qrel (_,_,?UR,?URw \<union> ?US)")
  shows "SN_qrel (nfs,Q,R,Rw)"
proof -
  let ?u = "uncurry_term a sm"
  let ?QR = "qrstep nfs {} ?UR"
  let ?QS = "qrstep nfs {} (?URw \<union> ?US)"
  let ?A = "(?QR \<union> ?QS)^*"
  {
    assume "\<exists> x r. (Var x, r) \<in> R_eta"
    then obtain x r where xr: "(Var x, r) \<in> R_eta" by auto
    then have "(?u (Var x), ?u r) \<in> ?UR" unfolding uncurry_trs_def by auto
    then have "(Var x, ?u r) \<in> ?UR" unfolding uncurry_term.simps[of _ _ "Var x"] by auto
    from lhs_var_imp_rstep_not_SN[OF this] have nSN: "\<not> (SN (rstep ?UR))" .
    from SN have SN: "SN (relto (rstep ?UR) (rstep (?URw \<union> ?US)))"
      unfolding SN_qrel_def SN_rel_defs by auto
    have "SN (rstep ?UR)" by (rule SN_subset[OF SN], auto)
    with nSN have False ..
  }
  then have varR: "\<And> x r. (Var x,r) \<notin> R_eta" by auto
  show ?thesis
  proof (rule SN_qrel_map[OF SN])
    fix s t
    assume "(s,t) \<in> qrstep nfs Q R"
    with qrstep_mono[OF eta2, of Q "{}"]
    have "(s,t) \<in> rstep R_eta" by auto
    from uncurry_step[OF hvfR eta1 varR this]
    have step: "(?u s, ?u t) \<in> relto (rstep ?UR) (rstep ?US)" by auto
    show "(?u s, ?u t) \<in> ?A O ?QR O ?A" 
      by (rule set_mp[OF _ step], unfold qrstep_union qrstep_rstep_conv, regexp)
  next
    fix s t
    assume "(s,t) \<in> qrstep nfs Q Rw"
    with qrstep_mono[OF eta2w, of Q "{}"]
    have "(s,t) \<in> rstep (R_eta \<union> Rw_eta)" by auto
    from uncurry_step[OF _ eta1w _ this]
    have step: "(?u s, ?u t) \<in> relto (rstep (?UR \<union> ?URw)) (rstep ?US)" using hvfR hvfRw trsw varR
      unfolding uncurry_trs_union rstep_union qrstep_rstep_conv split by blast
    show "(?u s, ?u t) \<in> ?A" 
      by (rule set_mp[OF _ step], unfold rstep_union qrstep_rstep_conv, regexp)
  qed
qed



definition only_eta :: "('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool"
where "only_eta E R_eta \<equiv> \<forall> l r. (l,r) \<in> E \<longrightarrow> (\<exists> a t l' r'. (l',r') \<in> R_eta \<and> instance_rule (l,r) (Fun a [l',t], Fun a [r',t]))"


lemma only_eta: assumes eta: "only_eta E (E \<union> R)" shows "rstep E \<subseteq> rstep R"
proof(rule rstep_subset[OF ctxt_closed_rstep subst_closed_rstep], rule)
  fix l r
  assume "(l,r) \<in> E"
  then show "(l,r) \<in> rstep R"
  proof (induct l arbitrary: r rule: wf_induct[OF wf_measures[of "[size]"]])
    case (1 l r)
    show ?case
    proof (cases "(l,r) \<in> R")
      case True
      then show ?thesis by (rule rstep_rule)
    next
      case False
      show ?thesis 
      proof (cases l)
        case (Var x)
        with eta 1(2) have "(l,r) \<in> R" unfolding only_eta_def instance_rule_def by force
        then show ?thesis using False by simp
      next
        case (Fun f ss)
        from False 1(2)
        obtain a t l' r' where l'r': "(l',r') \<in> E \<union> R" and inst: "instance_rule (l,r) (Fun a [l', t], Fun a [r',t])"
          using eta[unfolded only_eta_def] by blast+
        from inst[unfolded instance_rule_def] obtain \<sigma> where l: "l = Fun a [l',t] \<cdot> \<sigma>" and r: "r = Fun a [r',t] \<cdot> \<sigma>" by auto
        then have "size l' < size l" using size_subst[of l' \<sigma>] by simp
        with 1(1)[THEN spec, of l', THEN mp] l'r' have "(l',r') \<in> rstep R" by auto 
        from rstep_subst[OF rstep_ctxt[OF this,of "More a [] \<box> [t]"],of \<sigma>] show ?thesis unfolding l r
          by simp
      qed
    qed
  qed
qed

lemma only_eta_subset:
  assumes eta: "only_eta E (E \<union> R)"
  shows "rstep R = rstep (E \<union> R)"
  using rstep_mono only_eta[OF eta] unfolding rstep_union
  by auto

definition inj_sig_map :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> bool"
  where "inj_sig_map a m sm \<equiv> inj_on (\<lambda> (f,n,i). (get_symbol sm f n i, n + i * (m - 1))) {(f,n,i). i \<le> aarity sm f n} \<and> sm a m = [a]"

lemma inj_sig_map: assumes inj: "inj_sig_map a m sm" and i: "i < aarity sm f n" and m: "n + (Suc i) * (m - 1) = m"
  shows "get_symbol sm f n (Suc i) \<noteq> a" 
proof -
  from inj[unfolded inj_sig_map_def, THEN conjunct1, unfolded inj_on_def get_symbol_def, THEN bspec[of _ _ "(a,m,0)"], THEN bspec[of _ _ "(f,n,Suc i)"]] 
    m i
  show ?thesis by (simp add: get_symbol_def inj[unfolded inj_sig_map_def])
qed

lemma inj_sig_map_a: assumes inj: "inj_sig_map a m sm"
  shows "get_symbol sm a m 0 = a"
  using inj[unfolded inj_sig_map_def]
  unfolding get_symbol_def by auto

definition inverse_sig_map :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> 'f \<Rightarrow> nat \<Rightarrow> 'f \<times> nat \<times> nat"
  where "inverse_sig_map a m sm f m' \<equiv> THE (g,n,i). get_symbol sm g n i = f \<and> n + i * (m - 1) = m' \<and> i \<le> aarity sm g n"

lemma inverse_sig_map_gen: assumes inj: "inj_sig_map a m sm" and i: "i \<le> aarity sm f n" shows "inverse_sig_map a m sm (get_symbol sm f n i) (n+i * (m - 1)) = (f,n,i)" 
  unfolding inverse_sig_map_def
proof (rule, simp add: i, clarify)
  fix ff nn ii
  assume "get_symbol sm ff nn ii = get_symbol sm f n i" and "nn + ii * (m - 1) = n + i * (m - 1)" and "ii \<le> aarity sm ff nn"
  with i inj[unfolded inj_sig_map_def inj_on_def, THEN conjunct1, THEN bspec[of _ _ "(f,n,i)"], THEN bspec[of _ _ "(ff,nn,ii)"]]
  show "ff = f \<and> (nn,ii) = (n,i)" by auto
qed

lemma inverse_sig_map: assumes inj: "inj_sig_map a 2 sm" and i: "i \<le> aarity sm f n" shows "inverse_sig_map a 2 sm (get_symbol sm f n i) (n+i) = (f,n,i)"
  using inverse_sig_map_gen[OF inj i] by simp


lemma inverse_sig_map_a: assumes inj: "inj_sig_map a m sm" shows  "inverse_sig_map a m sm a m = (a,m,0)" 
proof -
  from inj[unfolded inj_sig_map_def, THEN conjunct2] 
  have "inverse_sig_map a m sm a m = inverse_sig_map a m sm (get_symbol sm a m 0) (m + 0 * (m - 1))" unfolding get_symbol_def by (auto)
  also have "\<dots> = (a,m,0)" by (rule inverse_sig_map_gen[OF inj], simp)
  finally show ?thesis . 
qed

fun curry :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)term \<Rightarrow> ('f,'v)term"
where "curry a _ (Var x) = (Var x)"
  |   "curry a sm (Fun f ts) = (let (f,n,i) = inverse_sig_map a 2 sm f (length ts);
                                    ss = map (curry a sm) ts
                                 in apply_args a (Fun f (take n ss)) (drop n ss))"

fun curry_subst :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)subst \<Rightarrow> ('f,'v)subst"
where "curry_subst a sm (sig) = (\<lambda>x. curry a sm (sig x))"

lemma curry_subst: "curry a sm (t \<cdot> \<sigma>) = curry a sm t \<cdot> curry_subst a sm \<sigma>"
proof (induct t)
  case (Var x)
  then show ?case by simp
next
  case (Fun f ss)
  then have id: "map (\<lambda>x. curry a sm (x \<cdot> \<sigma>)) ss = map (\<lambda> x. curry a sm x \<cdot> curry_subst a sm \<sigma>) ss" by auto
  show ?case by (cases "inverse_sig_map a 2 sm f (length ss)", auto simp: o_def Let_def apply_args_subst take_map[symmetric] drop_map[symmetric] id)
qed

fun curry_ctxt :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)ctxt \<Rightarrow> ('f,'v)ctxt"
where "curry_ctxt a _ \<box> = \<box>"
  |   "curry_ctxt a sm (More f bef C aft) = (let (g,n,i) = inverse_sig_map a 2 sm f (Suc (length bef + length aft));
                                    cbef = map (curry a sm) bef;
                                    caft = map (curry a sm) aft;   
                                    D = curry_ctxt a sm C;
                                    m = n - Suc (length bef)                                   
                                 in (if length bef < n then apply_args_ctxt a (More g cbef D (take m caft)) (drop m caft)
                                                       else apply_args_ctxt a (More a [apply_args a (Fun g (take n cbef)) (drop n cbef)] D []) caft))"

lemma curry_ctxt: "curry a sm (C \<langle> t \<rangle> ) = (curry_ctxt a sm C) \<langle> curry a sm t \<rangle> "
proof (induct C)
  case Hole
  then show ?case by simp
next
  case (More f bef C aft)
  show ?case
  proof (cases "inverse_sig_map a 2 sm f (Suc (length bef + length aft))")
    case (fields g n i)
    {
      assume "length bef < n"
      then have "n - length bef = Suc (n - Suc (length bef))" by arith
    } note helper = this
    show ?thesis
      by (simp add: fields Let_def More apply_args_ctxt_insert take_map[symmetric] drop_map[symmetric], auto simp: apply_args_append helper)
  qed
qed


definition curry_trs :: "'f \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs"
where "curry_trs a sm R = {(curry a sm l, curry a sm r) | l r. (l,r) \<in> R}"


lemma curry_rstep: 
  assumes step: "(s,t) \<in> rstep R"
  shows "(curry a sm s, curry a sm t) \<in> rstep (curry_trs a sm R)"
using step
proof (induct)
  case (IH C \<sigma> l r)
  show "(curry a sm C\<langle>l \<cdot> \<sigma>\<rangle>,curry a sm C\<langle>r \<cdot> \<sigma>\<rangle>) \<in> rstep (curry_trs a sm R)"
    unfolding curry_ctxt curry_subst  
    by (rule rstep_ctxt, rule rstep_subst, rule rstep_rule, unfold curry_trs_def, insert IH, auto)
qed

lemma curry_apply_args: assumes inj: "inj_sig_map a 2 sm"
  shows "curry a sm (apply_args a t ts) = apply_args a (curry a sm t) (map (curry a sm) ts)"
proof (induct ts rule: List.rev_induct)
  case Nil then show ?case by simp
next
  case (snoc s ss)
  have two: "Suc (Suc 0) = 2" by simp
  show ?case
    by (simp add: apply_args_last snoc[symmetric] inverse_sig_map_a[OF inj] two)
qed

lemma curry_uncurry: assumes inj: "inj_sig_map a 2 sm"
  shows "curry a sm (uncurry_term a sm t) = t"
proof -
  let ?c = "curry a sm"
  let ?u = "uncurry_term a sm"
  show ?thesis
  proof (induct t rule: applicative_term_induct[where a = a])
    case (Var x ts)
    have "?c (?u (apply_args a (Var x) ts)) = ?c (apply_args a (Var x) (map ?u ts))" 
      unfolding uncurry_apply_args_var ..
    also have "\<dots> = apply_args a (Var x) (map ?c (map ?u ts))"
      unfolding curry_apply_args[OF inj] by simp
    also have "\<dots> = apply_args a (Var x) ts"
      by (rule arg_cong[where f = "apply_args a (Var x)"], insert Var, induct ts, auto)
    finally show ?case . 
  next
    case (Fun f ss ts)
    let ?n = "min (length ts) (aarity sm f (length ss))"
    let ?f = "get_symbol sm f (length ss) ?n"
    from Fun(1) have id_ts: "map (curry a sm) (map (uncurry_term a sm) ts) = ts" by (induct ts, auto)
    from Fun(2) have id_ss: "map (curry a sm) (map (uncurry_term a sm) ss) = ss" by (induct ss, auto)
    from Fun(3) have napp: "(f,length ss) \<noteq> (a,2)" by simp
    have inv: "inverse_sig_map a 2 sm ?f (length ss + ?n) = (f,length ss,?n)" 
      by (rule inverse_sig_map[OF inj], simp)
    have "?c (?u (apply_args a (Fun f ss) ts)) = apply_args a (?c (Fun ?f (map ?u ss @ take ?n (map ?u ts)))) (drop ?n ts)" 
      unfolding uncurry_apply_args_fun[OF Fun(3)]
      unfolding curry_apply_args[OF inj]
      unfolding drop_map[symmetric]
      unfolding id_ts ..
    also have "\<dots> = apply_args a (apply_args a (Fun f ss) (take ?n ts)) (drop ?n ts)" 
      using id_ts id_ss by (simp add: o_def take_map[symmetric] inv)
    also have "\<dots> = apply_args a (Fun f ss) ts" 
      unfolding apply_args_append[symmetric] by simp
    finally show ?case . 
  qed
qed

lemma curry_uncurry_trs: assumes "inj_sig_map a 2 sm"
  shows "curry_trs a sm (uncurry_trs a sm R) = R"
proof (rule set_eqI, clarify)
  fix l r
  let ?c = "curry a sm"
  let ?u = "uncurry_term a sm"
  let ?cu = "\<lambda> t. ?c (?u t)"
  let ?CU = "curry_trs a sm (uncurry_trs a sm R)"
  note curry_uncurry = curry_uncurry[OF assms]
  show "((l,r) \<in> ?CU) = ((l,r) \<in> R)"
  proof
    assume "(l,r) \<in> R"
    then have "(?cu l,?cu r) \<in> ?CU"
      unfolding curry_trs_def uncurry_trs_def by force
    then show "(l,r) \<in> ?CU" unfolding curry_uncurry .
  next
    assume "(l,r) \<in> ?CU"
    then obtain ll rr where lr: "(ll,rr) \<in> R" and l: "l = ?cu ll" and r: "r = ?cu rr"
      unfolding curry_trs_def uncurry_trs_def by force
    from lr show "(l,r) \<in> R" unfolding l r curry_uncurry .
  qed
qed


lemma curry_trs_uncurry_of_sig: assumes inj: "inj_sig_map a 2 sm"
  shows "curry_trs a sm (uncurry_of_sig a sm) \<subseteq> Id" 
proof (clarify)
  fix cl cr
  assume clcr: "(cl,cr) \<in> curry_trs a sm (uncurry_of_sig a sm)"
  let ?c = "curry a sm"
  from clcr obtain l r where lr: "(l,r) \<in> uncurry_of_sig a sm" and cl: "cl = ?c l" and cr: "cr = ?c r"
    unfolding curry_trs_def by auto
  then obtain f n i where 
    l: "l = Fun a [generate_f_xs (get_symbol sm f n i) (n + i), Var (generate_var (n+i))]"
    and r: "r = generate_f_xs (get_symbol sm f n (Suc i)) (n + Suc i)"
    and i: "i < aarity sm f n"
    unfolding uncurry_of_sig_def by auto
  then have i: "i \<le> aarity sm f n" and si: "Suc i \<le> aarity sm f n" by auto
  note invi = inverse_sig_map[OF inj i]
  note invsi = inverse_sig_map[OF inj si, simplified]
  have id: "Fun a [?c (generate_f_xs (get_symbol sm f n i) (n + i)), Var (generate_var (n+i))] = ?c (generate_f_xs (get_symbol sm f n (Suc i)) (n + Suc i))" 
    unfolding generate_f_xs_def
    by (simp add: o_def invi invsi Let_def apply_args_last)
  have two: "Suc (Suc 0) = 2" by simp
  show "cl = cr" unfolding cl cr l r  
    by (simp add: inverse_sig_map_a[OF inj] two id)
qed
  
  
lemma curry_rstep_uncurry_of_sig: assumes inj: "inj_sig_map a 2 sm"
  and step: "(s,t) \<in> rstep (uncurry_of_sig a sm)"
  shows "curry a sm s = curry a sm t"
proof -
  from rstep_mono[OF curry_trs_uncurry_of_sig[OF inj], unfolded rstep_id] curry_rstep[OF step]
  show ?thesis by auto
qed

lemma uncurry_of_sig_SN: assumes inj: "inj_sig_map a 2 sm"
  shows "SN (rstep (uncurry_of_sig a sm))" (is "SN (rstep ?R)")
proof(rule ccontr)
  assume nSN: "\<not> ?thesis"
  have wf: "wf_trs ?R"
  proof -
    { 
      fix l r
      assume lr: "(l,r) \<in> ?R"
      have "vars_term r \<subseteq> vars_term l"
      proof -
        from lr[unfolded uncurry_of_sig_def]
        obtain f n i where l: "l = Fun a [generate_f_xs (get_symbol sm f n i) (n+ i), Var (generate_var (n+ i))]" and r: "r = generate_f_xs (get_symbol sm f n (Suc i)) (n + Suc i)"
          by auto
        {
          fix f i
          have "vars_term (generate_f_xs f i) = generate_var ` {0 ..< i}"
            unfolding generate_f_xs_def by auto
        } note vars_gen = this
        have id: "{0..<Suc (n+i)} = insert (n+i) {0..<(n+i)}" by auto
        show ?thesis unfolding l r 
          by (simp add: vars_gen id)
      qed
    }
    then show ?thesis
      unfolding wf_trs_def uncurry_of_sig_def by auto
  qed
  {
    fix f n
    have "defined ?R (f,n) \<Longrightarrow> ((f,n) = (a,2))"
      unfolding defined_def uncurry_of_sig_def
      by (auto)
  } note defined = this
  from not_SN_imp_ichain_rstep[OF wf nSN]
  obtain s t \<sigma> where "ichain (nfs, m, DP id ?R,{},{},{},?R) s t \<sigma>" by blast
  then obtain s t where "(s,t) \<in> DP id ?R" by (auto simp: ichain.simps)
  from this[unfolded DP_on_def] 
  obtain l r h us
    where lr: "(l,r) \<in> ?R" and u: "r \<unrhd> Fun h us" and d: "defined ?R (h, length us)"  by auto
  from defined[OF d] have h: "h = a" and us: "length us = 2" by auto
  from lr[unfolded uncurry_of_sig_def]
  obtain f n i where i: "i < aarity sm f n" and r: "r = generate_f_xs (get_symbol sm f n (Suc i)) (n + Suc i)" (is "_ = ?r") by auto
  from u[unfolded r generate_f_xs_def] have "?r = Fun h us" 
  proof (cases)
    case refl
    then show ?thesis unfolding generate_f_xs_def by auto
  next
    case (subt u)
    then obtain x where "u = Var x" by auto
    from subt(2)[unfolded this] have False by cases
    then show ?thesis by simp
  qed
  from this[unfolded h] have get: "get_symbol sm f n (Suc i) = a" and 2: "n + Suc i = 2" unfolding generate_f_xs_def us[symmetric] by auto
  from inj_sig_map[OF inj i] 2 get 
  show False by simp 
qed

lemma uncurry_preserves_SN:
  assumes inj: "inj_sig_map a 2 sm"
    and SN: "SN_on (rstep R) {t}"
    and curry: "t = curry a sm s"
  shows "SN_on (rstep (uncurry_trs a sm R \<union> uncurry_of_sig a sm)) {s}"
    (is "SN_on (rstep (?U \<union> ?S)) _")
proof 
  fix f
  assume f0: "f 0 \<in> {s}" and fsteps: "\<forall> i. (f i, f (Suc i)) \<in> rstep (?U \<union> ?S)"
  obtain g where g: "g = (\<lambda> i. curry a sm (f i))" by auto
  let ?C = "curry_trs a sm"
  from singletonD[OF f0] curry have t: "t = g 0" unfolding g by auto
  { 
    fix i
    from curry_rstep[OF fsteps[THEN spec, of i], of a sm]
    have "(g i, g (Suc i)) \<in> rstep (?C (?U \<union> ?S))" unfolding g .
    then have "(g i, g (Suc i)) \<in> rstep (?C ?U \<union> ?C ?S)" unfolding curry_trs_def by force
    then have "(g i, g (Suc i)) \<in> rstep R \<union> rstep (?C ?S)" unfolding curry_uncurry_trs[OF inj] rstep_union .
    then have "(g i, g (Suc i)) \<in> rstep R \<union> Id" 
      using rstep_mono[OF curry_trs_uncurry_of_sig[OF inj], unfolded rstep_id] by auto
  } note gsteps = this
  then have "\<forall> i. (g i, g (Suc i)) \<in> Id \<union> rstep R" by auto
  from non_strict_ending[OF this _, simplified, OF SN[unfolded t]]
  obtain j where j: "\<And> i. i \<ge> j \<Longrightarrow> (g i, g (Suc i)) \<notin> rstep R" by auto
  obtain h where h: "h = (\<lambda> i. f (i + j))" by auto
  {
    fix i
    from fsteps have step: "(h i, h (Suc i)) \<in> rstep ?U \<union> rstep ?S" unfolding h rstep_union by auto
    have "(h i, h (Suc i)) \<in> rstep ?S"      
    proof (rule ccontr)
      assume "(h i, h (Suc i)) \<notin> rstep ?S"
      with step have "(h i, h (Suc i)) \<in> rstep ?U" by auto
      from curry_rstep[OF this, of a sm, unfolded curry_uncurry_trs[OF inj]]
      have "(g (i+j), g (Suc (i+j))) \<in> rstep R" unfolding g h by simp
      with j[of "i + j"] show False by simp
    qed
  }
  then have "\<not> SN (rstep ?S)" by auto
  with uncurry_of_sig_SN[OF inj]
  show False by simp
qed

lemma uncurrying_for_nonterm: assumes inj: "inj_sig_map a 2 sm"
  and eta: "only_eta E (E \<union> R)"
  and nSN: "\<not> SN (rstep (uncurry_trs a sm (E \<union> R) \<union> uncurry_of_sig a sm))" (is "\<not> SN ?U")
  shows "\<not> SN (rstep R)"
proof -
  from nSN obtain s where "\<not> SN_on ?U {s}" unfolding SN_defs by blast
  with uncurry_preserves_SN[OF inj _ refl]
  have "\<not> SN (rstep (E \<union> R))" unfolding SN_defs by blast
  with only_eta_subset[OF eta] show ?thesis by simp
qed

lemma uncurrying_sound_dp: assumes hvfPR: "\<And> l r. (l,r) \<in> R_eta \<union> Rw_eta \<union> P \<union> Pw \<Longrightarrow> hvf_term a l"
  and eta1: "eta_closed a sm R_eta R_eta"
  and eta1w: "eta_closed a sm (R_eta \<union> Rw_eta) (R_eta \<union> Rw_eta)"
  and eta2: "R \<subseteq> R_eta"
  and eta2w: "R_eta \<union> Rw_eta = Ew \<union> (R \<union> Rw)"
  and eta3w: "only_eta Ew (R_eta \<union> Rw_eta)"
  and nvar: "\<And> l r. (l,r) \<in> R \<union> Rw \<Longrightarrow> is_Fun l"
  and inj: "inj_sig_map a 2 sm"
  and finite: "finite_dpp (nfs,m,uncurry_trs a sm P,uncurry_trs a sm Pw, {},uncurry_trs a sm R_eta,uncurry_trs a sm Rw_eta \<union> uncurry_of_sig a sm)" (is "finite_dpp (_,_,_,_,_,_,_ \<union> ?S)")
  shows "finite_dpp (nfs,m,P,Pw,{},R,Rw)"
proof -
  let ?qrstep = "qrstep nfs"
  from only_eta_subset[OF eta3w[unfolded eta2w]] rstep_mono[OF eta2] eta2w have R: "rstep R \<subseteq> rstep R_eta" and
    RRw: "?qrstep {} (R \<union> Rw) = rstep (R_eta \<union> Rw_eta)" by auto
  {
    fix x r
    {
      assume "(Var x, r) \<in> R_eta \<union> Rw_eta"
      then have "(Var x, r) \<in> rstep (R_eta \<union> Rw_eta)" by auto
      with RRw have varx:  "(Var x, r) \<in> rstep (R \<union> Rw)" by auto    
      obtain C \<sigma> l r where lr: "(l,r) \<in> R \<union> Rw" and varx: "Var x = C\<langle>l \<cdot> \<sigma>\<rangle>" 
        by (rule rstepE[OF varx], auto)
      from varx obtain y where "l = Var y" by (cases C, cases l, auto)
      from nvar[OF lr[unfolded this]] have False by simp
    }
    then have "(Var x,r) \<notin> R_eta \<union> Rw_eta" by auto
  } note var = this
  let ?u = "uncurry_term a sm"
  let ?us = "uncurry_subst a sm"
  let ?U = "uncurry_trs a sm"
  let ?RRw = "?U (R_eta \<union> Rw_eta)"
  let ?All = "?U R_eta \<union> (?U Rw_eta \<union> ?S)"
  let ?Q = "{}"
  let ?min = "\<lambda> t. SN_on (?qrstep ?Q ?All) {t}"
  let ?mmin = "\<lambda> t. m \<longrightarrow> ?min t"
  let ?subst_closure = "rqrstep nfs {}"
  let ?Ms = "{(s,t). ?mmin t}"
  let ?N = "{(s,t). s \<in> NF_terms ?Q}"
  let ?P = "?subst_closure P \<inter> ?N"
  let ?Pw = "?subst_closure Pw \<inter> ?N"
  let ?UP = "(?subst_closure (?U P) \<inter> ?N) \<inter> ?Ms"
  let ?UPw = "(?subst_closure (?U Pw) \<inter> ?N) \<inter> ?Ms"
  let ?UR = "?qrstep ?Q (?U R_eta)"
  let ?URw = "?qrstep ?Q (?U Rw_eta)"
  let ?URwU = "?qrstep ?Q (?U Rw_eta \<union> ?S)"
  let ?A = "?UP \<union> ?UPw \<union> ?UR \<union> ?URwU"
  have all: "?RRw \<union> ?S = ?All" unfolding uncurry_trs_union by auto
  {
    fix s t P'
    assume step: "(s,t) \<in> ?subst_closure P' \<inter> ?N" and SN: "m \<longrightarrow> SN_on (?qrstep {} (R \<union> Rw)) {t}"
      and P': "P' \<subseteq> P \<union> Pw" 
    then have "(s,t) \<in> ?subst_closure P'" by auto
    from rqrstepE[OF this] obtain l r \<sigma> where lr: "(l,r) \<in> P'" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" by auto
    from P' hvfPR lr have "hvf_term a l" by blast
    from uncurry_subst_hvf[OF this, of sm \<sigma>]
    have us: "?u s = ?u l \<cdot> ?us \<sigma>" unfolding s  by auto
    from lr have ulr: "(?u l, ?u r) \<in> ?U P'" unfolding uncurry_trs_def by auto
    then have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> ?subst_closure (?U P')" unfolding us by (auto simp: rrstep_def')
    {
      assume m
      with SN have SN: "SN_on (?qrstep {} (R \<union> Rw)) {t}" by auto
      have "?min (?u r \<cdot> ?us \<sigma>)"
        unfolding all[symmetric] 
        unfolding qrstep_rstep_conv
          by (rule uncurry_preserves_SN[OF inj SN[unfolded RRw]], unfold t curry_subst curry_uncurry[OF inj], rule term_subst_eq, simp add: curry_uncurry[OF inj])
    }
    with step have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> (?subst_closure (?U P') \<inter> ?N) \<inter> ?Ms" by auto
    have steps: "(?u r \<cdot> ?us \<sigma>, ?u t) \<in> ?A^*"
      unfolding t 
      by (rule set_mp[OF _ uncurry_subst], unfold qrstep_rstep_conv rstep_union, regexp)
    from step steps 
    have "(?u s, ?u t) \<in> ((?subst_closure (?U P') \<inter> ?N) \<inter> ?Ms) O ?A^*" by auto
  } note P' = this
  show ?thesis
  proof (rule finite_dpp_map_min[OF finite, where I = "\<lambda> _. True"])
    fix t
    assume SN: "m \<longrightarrow> SN_on (?qrstep {} (R \<union> Rw)) {t}"
    show "m \<longrightarrow> SN_on (?qrstep {} (?U R_eta \<union> (?U Rw_eta \<union> ?S))) {?u t}"
    proof 
      assume m
      with SN have SN: "SN_on (?qrstep {} (R \<union> Rw)) {t}" by simp
      show "SN_on (?qrstep {} (?U R_eta \<union> (?U Rw_eta \<union> ?S))) {?u t}"
        unfolding qrstep_rstep_conv all[symmetric] 
        by (rule uncurry_preserves_SN[OF inj SN[unfolded RRw]], unfold curry_uncurry[OF inj], simp)
    qed
  next
    fix s t 
    assume step: "(s,t) \<in> ?qrstep ?Q Rw" 
    then have step: "(s,t) \<in> ?qrstep {} (R \<union> Rw)" by auto
    have step: "(?u s, ?u t) \<in> rel_qrstep (nfs,{},?U (R_eta \<union> Rw_eta), ?S)" 
      by (rule uncurry_step[OF _ eta1w var step[unfolded RRw]], insert hvfPR, blast)
    have "(?u s, ?u t) \<in> ?A^*"
      by (rule set_mp[OF _ step], unfold uncurry_trs_union qrstep_union split, regexp)
    then show "(?u s, ?u t) \<in> ?A^* \<and> True" by simp
  next
    fix s t 
    assume step: "(s,t) \<in> ?qrstep ?Q R" 
    then have step: "(s,t) \<in> rstep R_eta" using eta2 by auto
    have step: "(?u s, ?u t) \<in> rel_qrstep (nfs,{},?U R_eta, ?S)" 
      by (rule uncurry_step[OF _ eta1 _ step], insert var hvfPR, blast+)
    have "(?u s, ?u t) \<in> ?A^* O (?UP \<union> ?UR) O ?A^*"
      by (rule set_mp[OF _ step], unfold uncurry_trs_union qrstep_union split, regexp)
    then show "(?u s, ?u t) \<in> ?A^* O (?UP \<union> ?UR) O ?A^* \<and> True" by simp
  next
    fix s t 
    assume step: "(s,t) \<in> ?P" and SN: "m \<longrightarrow> SN_on (?qrstep {} (R \<union> Rw)) {t}"
    have "(?u s, ?u t) \<in> ?UP O ?A^*"
      by (rule P'[OF step SN], auto)
    then show "(?u s, ?u t) \<in> ?A^* O ?UP O ?A^* \<and> True" by auto
  next
    fix s t
    assume step: "(s,t) \<in> ?Pw" and SN: "m \<longrightarrow> SN_on (?qrstep {} (R \<union> Rw)) {t}"
    have "(?u s, ?u t) \<in> ?UPw O ?A^*" 
      by (rule P'[OF step SN], auto)
    then show "(?u s, ?u t) \<in> ?A^* O (?UP \<union> ?UPw) O ?A^* \<and> True" by auto
  qed
qed


section \<open>uncurrying of top symbols\<close>

abbreviation (input) get_default_sym :: "'f sig_map \<Rightarrow> 'f \<times> nat \<Rightarrow> 'f"
where
  "get_default_sym sm \<equiv> \<lambda>(f, n). get_symbol sm f n 0"

abbreviation map_sym :: "'f sig_map \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "map_sym sm \<equiv> map_funs_term_wa (get_default_sym sm)"

definition "get_inv_default_sym a m sm \<equiv> \<lambda>(f, n). fst (inverse_sig_map a m sm f n)"

lemma inj_sig_map_below:
  assumes inj: "inj_sig_map a m sm"
  shows "get_inv_default_sym a m sm (get_default_sym sm (f,n), n) = f"
  unfolding get_inv_default_sym_def
  using inverse_sig_map_gen[OF inj, of 0 f n, simplified]
  by auto

definition map_inv_sym :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term"
where
  "map_inv_sym a m sm \<equiv> map_funs_term_wa (get_inv_default_sym a m sm)"

lemma map_inv_sym:
  assumes inj: "inj_sig_map a m sm"
  shows "map_inv_sym a m sm (map_sym sm t) = t"
  by (unfold map_inv_sym_def map_funs_term_wa_compose, rule map_funs_term_wa_funas_term_id[OF subset_refl],
    insert inj_sig_map_below[OF inj], auto)

definition map_inv_trs :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "map_inv_trs a m sm \<equiv> map_funs_trs_wa (get_inv_default_sym a m sm)"

abbreviation uncurry_below_trs :: "'f sig_map \<Rightarrow> ('f, 'v) trs \<Rightarrow> ('f, 'v) trs"
where
  "uncurry_below_trs sm \<equiv> map_funs_trs_wa (get_default_sym sm)"  

lemma map_inv_trs:
  assumes inj: "inj_sig_map a m sm"
  shows "map_inv_trs a m sm (uncurry_below_trs sm R) = R"
  by (unfold map_inv_trs_def map_funs_trs_wa_compose, rule map_funs_trs_wa_funas_trs_id[OF subset_refl],
    insert inj_sig_map_below[OF inj], auto)

lemma map_sym_preserves_SN:
  assumes inj: "inj_sig_map a m sm"
    and SN: "SN_on (rstep R) {t}"
  shows "SN_on (rstep (uncurry_below_trs sm R)) {map_sym sm t}"
proof
  fix f
  assume f0: "f 0 \<in> {map_sym sm t}"
    and steps: "\<forall> i. (f i, f (Suc i)) \<in> rstep (uncurry_below_trs sm R)"
  obtain g where g: "g = (\<lambda> i. map_inv_sym a m sm (f i))" by auto
  let ?R = "map_inv_trs a m sm (uncurry_below_trs sm R)"
  {
    fix i
    from map_funs_trs_wa_rstep[OF steps[THEN spec, of i]]
    have "(g i, g (Suc i)) \<in> rstep ?R"
      unfolding g map_inv_sym_def map_inv_trs_def .
    then have "(g i, g (Suc i)) \<in> rstep R" 
      unfolding map_inv_trs[OF inj] .
  } note steps = this
  have "g 0 = t" unfolding g singletonD[OF f0] by (rule map_inv_sym[OF inj])
  with steps SN show False by auto
qed


fun uncurry_top :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f, 'v) term \<Rightarrow> ('f, 'v) term" where
  "uncurry_top a n sm (Fun f ts) = (let
      mt = map (map_sym sm);
      t = hd ts
    in if f = a \<and> length ts = n \<and> \<not> is_Var t \<and> (case the (root t) of (h, m) \<Rightarrow> aarity sm h m \<noteq> 0)
      then (case t of Fun g ss \<Rightarrow> Fun (get_symbol sm g (length ss) 1) (mt (ss @ tl ts)))
      else Fun (get_default_sym sm (f, length ts)) (mt ts))"
|  "uncurry_top a n sm (Var x) = Var x"

fun hvf_top :: "'f \<Rightarrow> nat \<Rightarrow> ('f, 'v) term \<Rightarrow> bool" where
  "hvf_top a n (Fun f ts) = (f = a \<and> length ts = n \<longrightarrow> \<not> (is_Var (hd ts)))"
| "hvf_top a n (Var _) = False"

abbreviation uncurry_top_subst where
  "uncurry_top_subst sm \<equiv> map_funs_subst_wa (get_default_sym sm)"

lemma uncurry_top_subst_hvf:
  assumes hvf: "hvf_top a (Suc n) t"
  shows "uncurry_top a (Suc n) sm (t \<cdot> \<sigma>) = uncurry_top a (Suc n) sm t \<cdot> uncurry_top_subst sm \<sigma>"
proof -
  from hvf obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  show ?thesis
  proof (cases "f = a \<and> length ts = Suc n")
    case True
    then obtain s tss where ts: "ts = s # tss" by (cases ts, auto)
    with hvf True show ?thesis unfolding t by (cases s, auto simp: Let_def)
  next
    case False
    then show ?thesis unfolding t by auto
  qed
qed

definition uncurry_of_top_sig :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f,string)trs"
where "uncurry_of_top_sig a m sm \<equiv> {(Fun a (generate_f_xs (get_symbol sm f n i) (n + i) # map (\<lambda> i. Var (generate_var i)) [n+i..<n+i+(m - 1)]),generate_f_xs (get_symbol sm f n (Suc i)) (n + i + (m - 1))) | f n i. i < aarity sm f n}"

lemma uncurry_top_sig: assumes a: "get_symbol sm a (Suc n) 0 = a"
  and ts: "length ts = n"               
  shows "(Fun a (map_sym sm s # map (map_sym sm) ts), uncurry_top a (Suc n) sm (Fun a (s # ts))) \<in> (rrstep (uncurry_of_top_sig a (Suc n) sm))^=" (is "(Fun a (?m s #_ ), ?u (Fun a _)) \<in> ?C")
proof (cases s)
  case (Var x)
  then show ?thesis by (simp add: a ts)
next
  case (Fun f ss)
  show ?thesis
  proof (cases "aarity sm f (length ss) = 0")
    case True
    then show ?thesis by (auto simp: Fun a ts)
  next
    case False
    let ?m = "length ss"
    let ?l = "Fun a (generate_f_xs (get_symbol sm f ?m 0) ?m # map (\<lambda>i. Var (generate_var i)) [?m..<?m + n])"
    let ?r = "generate_f_xs (get_symbol sm f ?m (Suc 0)) (?m + n)"
    let ?sig = "(\<lambda>i. map_sym sm ((ss @ ts) ! the_inv generate_var i))"
    have lr: "(?l,?r) \<in> uncurry_of_top_sig a (Suc n) sm"
      unfolding uncurry_of_top_sig_def
      by (rule, rule exI[of _ f], rule exI[of _ ?m], rule exI[of _ 0], insert False, simp)
    show ?thesis
      by  (simp add: Let_def ts Fun False, rule impI, rule disjI1, rule rrstepI[OF lr, of _ ?sig], simp_all add: o_def generate_f_xs_def
        the_inv_f_f[OF inj_generate_var] ts[symmetric], rule conjI, (rule nth_equalityI, simp, simp add: nth_append)+) 
  qed
qed


lemma uncurry_top_subst: assumes a: "get_symbol sm a (Suc n) 0 = a"
   shows "(uncurry_top a (Suc n) sm (Fun f ts) \<cdot> uncurry_top_subst sm \<sigma>, uncurry_top a (Suc n) sm (Fun f ts \<cdot> \<sigma>)) \<in> (rrstep (uncurry_of_top_sig a (Suc n) sm))^=" (is "_ \<in> ?C^=")
proof (cases "hvf_top a (Suc n) (Fun f ts)")
  case True
  from uncurry_top_subst_hvf[OF this] show ?thesis by auto
next
  case False
  let ?u = "uncurry_top a (Suc n) sm"
  let ?us = "uncurry_top_subst sm \<sigma>"
  let ?m = "map_sym sm"
  from False have f: "f = a" and l: "length ts = Suc n" and v: "is_Var (hd ts)" by auto
  from l obtain s tts where ts: "ts = s # tts" and n: "n = length tts" by (cases ts, auto)
  from v ts obtain x where ts: "ts = Var x # tts" by (cases s, auto)
  obtain s u where s: "\<sigma> x = s" by auto
  with a f ts have l: "?u (Fun f ts) \<cdot> ?us  = Fun a (?m s # map ?m (map (\<lambda> w. w \<cdot> \<sigma>) tts))" (is "_ = ?l")  
    and r: "Fun f ts \<cdot> \<sigma> = Fun a (s # map (\<lambda>w. w \<cdot> \<sigma>) tts)" (is "_ = ?r") unfolding n by (auto) 
  show ?thesis unfolding l r by (rule uncurry_top_sig[OF a], auto simp: n)
qed

definition uncurry_top_trs :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs"
where "uncurry_top_trs a n sm R \<equiv> (\<lambda>(l,r). (uncurry_top a n sm l, uncurry_top a n sm r)) ` R"


lemma uncurry_top_preserves_SN:
  assumes inj: "inj_sig_map a (Suc n) sm"
    and SN: "SN_on (rstep R) {t}"
  shows "SN_on (rstep (uncurry_below_trs sm R)) {uncurry_top a (Suc n) sm t}"
proof (cases "uncurry_top a (Suc n) sm t = map_sym sm t")
  case True
  with map_sym_preserves_SN[OF inj SN] show ?thesis by simp
next 
  case False
  let ?n = "Suc n"
  from inj_sig_map_a[OF inj] have a: "get_symbol sm a ?n 0 = a" .
  from False obtain f ts where t: "t = Fun f ts" by (cases t, auto)
  from False have "f = a \<and> length ts = ?n" unfolding t by (cases "f = a \<and> length ts = ?n", auto)
  with t obtain l rs where t: "t = Fun a (l # rs)" and n: "n = length rs" by (cases ts, auto)
  from False[unfolded t n, unfolded uncurry_top.simps, simplified Let_def, simplified]
  have cond: "is_Fun l \<and> 0 < aarity sm (fst (the (root l))) (num_args l)"
    by (cases "is_Fun l \<and> 0 < aarity sm (fst (the (root l))) (num_args l)", auto simp: a)
       (cases l, auto)
  from cond t obtain g ls where t: "t = Fun a (Fun g ls # rs)" and aa: "aarity sm g (length ls) > 0"
    by (cases l, auto)
  let ?U = "uncurry_below_trs sm R"
  note SN_pres = map_sym_preserves_SN[OF inj]
  have R: "\<forall>(l, r)\<in>?U. is_Fun l"
  proof (clarsimp)
    fix l r
    assume "(l, r) \<in> ?U" and "is_Var l"
    with left_var_imp_not_SN[of _ _ ?U] SN_pres[OF SN]
    show False by auto
  qed
  note SN = SN[unfolded t]
  let ?m = "map_sym sm"
  let ?g = "get_symbol sm g (length ls) (Suc 0)"
  have "SN_on (rstep ?U) {Fun ?g (map ?m (ls @ rs))}"
  proof (rule SN_args_imp_SN_rstep[OF _ R])
    fix s
    from SN_pres[OF SN_imp_SN_arg[OF SN]] have rs: "\<And> r. r \<in> set rs \<Longrightarrow> SN_on (rstep ?U) {?m r}" by simp
    {
      fix s
      assume "s \<in>  set (map ?m ls)"
      then obtain l where l: "l \<in> set ls" and s: "s = ?m l" by auto
      from SN_pres[OF SN_imp_SN_arg[OF SN_imp_SN_arg[OF SN, of "Fun g ls"] l]]
      have "SN_on (rstep ?U) {s}" unfolding s by auto
    } note ls = this
    assume "s \<in>  set (map ?m (ls @ rs))"
    with ls rs show "SN_on (rstep ?U) {s}"
      by auto
  next
    {
      assume "defined ?U (?g, length ls + length rs)"
      from this[unfolded defined_def] obtain ll rr where
      llrr: " (ll, rr) \<in> ?U" and  "root ll = Some (?g, length ls + length rs)" by auto
      then obtain lls where ll: "ll = Fun ?g lls" and lls: "length lls = length ls + length rs" by (cases ll, auto)
      from llrr obtain lll rrr where lllrrr: "(lll,rrr) \<in> R" and ll2: "ll = ?m lll" unfolding map_funs_trs_wa_def by auto
      from ll ll2 obtain h llls where lll3: "lll = Fun h llls" by (cases lll, auto)
      from ll2[unfolded ll lll3] lls have len: "length llls = length ls + length rs" and g: "?g = get_default_sym sm (h,length ls + length rs)" by auto
      from inverse_sig_map_gen[OF inj, of 0 h "length ls + length rs"] have 
        one: "inverse_sig_map a ?n sm ?g (length ls + length rs) = (h,length ls + length rs,0)" unfolding g by simp
      with aa inverse_sig_map_gen[OF inj, of "Suc 0" g "length ls"] have False by (auto simp: n)
    }
    then show "\<not> defined ?U (?g, length (map ?m (ls @ rs)))" by auto
  qed
  then show ?thesis using cond aa unfolding t n
    by (simp add: Let_def)
qed

lemma uncurry_top_subst_SN: assumes 
     inj: "inj_sig_map a (Suc n) sm"
  and ndef: "\<not> defined R (a,Suc n)"
  and SN: "SN_on (rstep R) {t \<cdot> \<sigma>}"
  shows "SN_on (rstep (uncurry_below_trs sm R)) {uncurry_top a (Suc n) sm t \<cdot> uncurry_top_subst sm \<sigma>}"
    (is "SN_on (rstep ?U) {?u t \<cdot> ?us}")
proof (cases t)
  case (Var x)
  then show ?thesis using map_sym_preserves_SN[OF inj SN] by auto
next
  case (Fun f ts)
  let ?n = "Suc n"
  show ?thesis
  proof (cases "hvf_top a ?n t")
    case True    
    show ?thesis unfolding uncurry_top_subst_hvf[OF True, symmetric]
      by (rule uncurry_top_preserves_SN[OF inj SN])
  next
    case False    
    let ?m = "map_sym sm"
    note a = inj_sig_map_a[OF inj]
    from False have f: "f = a" and l: "length ts = ?n" and v: "is_Var (hd ts)" unfolding Fun using a by auto
    then obtain s tts where ts: "ts = s # tts" and n: "n = length tts" by (cases ts, auto)
    from v ts obtain x where ts: "ts = Var x # tts" by (cases s, auto)
    obtain s u where s: "\<sigma> x = s" by auto
    with f ts have l: "?u (Fun f ts) \<cdot> ?us  = Fun a (?m s # map ?m (map (\<lambda> w. w \<cdot> \<sigma>) tts))" (is "_ = ?l") 
      and r: "Fun f ts \<cdot> \<sigma> = Fun a (s # map (\<lambda> w. w \<cdot> \<sigma>) tts)" (is "_ = ?r") by (auto simp: a[unfolded n])
    let ?args = "?m s # map ?m (map (\<lambda> w. w \<cdot> \<sigma>) tts)"
    show ?thesis unfolding Fun l
    proof (rule SN_args_imp_SN_rstep)
      {
        assume "defined ?U (a,Suc (length tts))"
        then obtain l r where lr: "(l,r) \<in> ?U"
          and "root l = Some (a, Suc (length tts))" unfolding defined_def by auto
        then obtain ls where l: "l = Fun a ls" and len: "length ls = Suc (length tts)" by (cases l, auto)
        from lr[unfolded map_funs_trs_wa_def]
        obtain ll rr where llrr: "(ll,rr) \<in> R" and l2: "l = map_sym sm ll" by auto
        from l2 len obtain g lls where ll: "ll = Fun g lls" and len2: "length lls = ?n" and "get_default_sym sm (g,?n) = a" unfolding n l by (cases ll, auto)
        with inverse_sig_map_a[OF inj] have "inverse_sig_map a ?n sm (get_default_sym sm (g, ?n)) ?n = (a,?n,0)" by simp
        with inverse_sig_map_gen[OF inj, of 0 g ?n] have g: "g = a" by auto
        from llrr[unfolded ll g] len2 have d: "defined R (a,?n)" unfolding defined_def by auto
        from ndef d have False by auto
      }
      then show "\<not> defined ?U (a, length ?args)" by auto
    next
      fix u
      assume "u \<in> set ?args"
      then have dis: "u = ?m s \<or> (\<exists> t \<in> set tts. u = ?m (t \<cdot> \<sigma>))" by auto
      note SN = map_sym_preserves_SN[OF inj SN_imp_SN_arg[OF SN[unfolded Fun ts, simplified]]]
      from dis show "SN_on (rstep ?U) {u}"
      proof
        assume u: "u = ?m s"
        show ?thesis unfolding u by (rule SN, simp add: s)
      next
        assume "\<exists> t \<in> set tts. u = ?m (t \<cdot> \<sigma>)"
        then obtain t where t: "t \<in> set tts" and u: "u = ?m (t \<cdot> \<sigma>)" by auto
        show ?thesis unfolding u by (rule SN, insert t, auto)
      qed
    next
      {
        fix l r
        assume "(l, r) \<in> ?U" and "is_Var l"
        then obtain x ll rr where "(ll,rr) \<in> R" and "Var x = ?m ll"  unfolding map_funs_trs_wa_def by auto
        then have "(Var x, rr) \<in> R" by (cases ll, auto)
        from left_var_imp_not_SN[OF this] SN have False by simp
      }
      then show "\<forall>(l, r)\<in>?U. is_Fun l" by auto
    qed
  qed
qed

definition eta_closed_top :: "'f \<Rightarrow> nat \<Rightarrow> 'f sig_map \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)trs \<Rightarrow> bool"
  where "eta_closed_top a n sm R P \<equiv> \<forall> f ls r. (Fun f ls,r) \<in> R \<longrightarrow> aarity sm f (length ls) \<noteq> 0 \<longrightarrow> (\<exists> ll rr ys. length ys = n - 1 \<and> distinct ys \<and> 
           set ys \<inter> vars_rule (ll,rr) = {} \<and> instance_rule (Fun f ls,r) (ll,rr) \<and>
           (Fun a (ll # map Var ys), Fun a (rr # map Var ys)) \<in> P)"

lemma uncurry_top_step:
  fixes P R P' RB :: "('f,string)trs" and a n sm m and INV
  defines UR: "UR \<equiv> uncurry_below_trs sm R"
  defines CSP: "CSP \<equiv> rrstep (uncurry_top_trs a (Suc n) sm P)"
  defines CSS: "CSS \<equiv>  rrstep (uncurry_of_top_sig a (Suc n) sm)"
  defines Ms: "Ms \<equiv> {(s,t). m \<longrightarrow> SN_on (rstep (uncurry_below_trs sm RB)) {t}}"
  defines IA: "IA \<equiv> \<lambda> t. \<not> defined RB (the (root t)) \<and> is_Fun t"
  defines IH: "IH \<equiv> \<lambda> t. the (root t) = (a, Suc n) \<and> tcap RB (hd (args t)) = GCHole"
  defines I: "I \<equiv> \<lambda> t. IA t \<and> (IH t \<longrightarrow> INV)" 
  assumes 
      inj: "inj_sig_map a (Suc n) sm"
  and ndefa: "\<not> defined RB (a,(Suc n))"
  and step: "(s,t) \<in> rstep R"
  and P: "\<forall> (l,r) \<in> P. hvf_top a (Suc n) l"
  and RB: "\<And> l r. (l,r) \<in> RB \<Longrightarrow> is_Fun l"
  and inv: "I s"
  and INV: "INV \<Longrightarrow> eta_closed_top a (Suc n) sm R P \<and> CSS \<subseteq> rrstep P'"
  and subset: "R \<subseteq> RB"
  and SN: "m \<Longrightarrow> SN_on (rstep RB) {s}"
  shows "(uncurry_top a (Suc n) sm s, uncurry_top a (Suc n) sm t) \<in> (CSP \<inter> Ms \<union> rstep UR) O ((rrstep P' \<inter> Ms)^=) \<and> I t"
  (is "(?u s,_) \<in> ?Rel \<and> _")
proof - 
  from inv[unfolded I IA]
  obtain f ss where s: "s = Fun f ss" and ndef: "\<not> defined RB (f,length ss)" by (cases s, auto)
  let ?n = "Suc n"
  let ?mini = "m"
  from inj_sig_map_a[OF inj] have a: "get_symbol sm a ?n 0 = a" .
  let ?UP = "uncurry_top_trs a ?n sm P"
  let ?UR = "uncurry_below_trs sm R"
  let ?URB = "uncurry_below_trs sm RB"
  let ?US = "uncurry_of_top_sig a ?n sm"
  let ?SN = "\<lambda>x. SN_on (rstep ?URB) {x}"
  let ?Ms = "{(s,t). m \<longrightarrow> SN_on (rstep ?URB) {t}}"
  let ?URM = "rstep ?UR \<inter> ?Ms"
  let ?CSP = "rrstep ?UP \<inter> ?Ms"
  let ?CSS = "rrstep P' \<inter> ?Ms"
  note SN_pres = map_sym_preserves_SN[OF inj SN]
  have RB: "\<forall> (l,r) \<in> RB. \<not> (is_Var l)" using RB by auto
  then have R: "\<forall> (l,r) \<in> R. \<not> (is_Var l)" using subset by auto
  from step have stepRB: "(s,t) \<in> rstep RB" using subset by auto
  note SN_suc = step_preserves_SN_on[OF _ uncurry_top_preserves_SN[OF inj SN]]
  note SN = step_preserves_SN_on[OF stepRB SN]
  {
    assume t: "(?u s, ?u t) \<in> rstep ?UR \<union> ?CSP"
    let ?p = "(?u s, ?u t)"
    have p: "?p \<in> ?URM \<union> ?CSP"
      using t  uncurry_top_preserves_SN[OF inj SN] by auto
    have "(?u s, ?u t) \<in> ?Rel"
      by (rule set_mp[OF _ p], unfold Ms UR CSP, auto)
  } note one_step = this
  from rstep_imp_nrrstep[OF _ _ R step] ndef
  have some_step: "(s, t) \<in> nrrstep R" using subset unfolding s defined_def  by auto
  from some_step[unfolded nrrstep_def'] obtain C l r \<sigma> where l: "s = C\<langle>l \<cdot> \<sigma>\<rangle>" and r: "t = C\<langle>r \<cdot> \<sigma>\<rangle>" and lr: "(l,r) \<in> R" and C: "C \<noteq> \<box>" by auto
  from lr R obtain g ls where lhs: "l = Fun g ls" by (cases l, auto)
  from C l obtain bef D aft where C: "C = More f bef D aft" unfolding s by (cases C, auto)
  from C l r have ss: "ss = bef @ D\<langle>l \<cdot> \<sigma>\<rangle> # aft" and t: "t = Fun f (bef @ D\<langle>r\<cdot>\<sigma>\<rangle> # aft)" unfolding s by auto
  from inv have IA: "IA t" unfolding I IA s t ss by auto
  let ?C = "map_funs_ctxt_wa (get_default_sym sm)"
  let ?m = "map_sym sm" 
  from lr have mlr: "(?m l, ?m r) \<in> ?UR" unfolding map_funs_trs_wa_def by auto
  from lr have "(D\<langle>l\<cdot>\<sigma>\<rangle>, D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep R" by auto
  from map_funs_trs_wa_rstep[OF this] have "(?m (D\<langle>l\<cdot>\<sigma>\<rangle>), ?m (D\<langle>r\<cdot>\<sigma>\<rangle>)) \<in> rstep ?UR" by simp
  then have step: "\<And> C. (C\<langle>?m (D\<langle>l\<cdot>\<sigma>\<rangle>)\<rangle>, C\<langle>?m (D\<langle>r\<cdot>\<sigma>\<rangle>)\<rangle>) \<in> rstep ?UR" by (rule rstep_ctxt)
  note no_trans_step = step[of "More (get_default_sym sm (f,Suc (length bef + length aft))) (map ?m bef) \<box> (map ?m aft)", simplified]
  from lr have "(l\<cdot>\<sigma>, r\<cdot>\<sigma>) \<in> rstep R" by auto
  from map_funs_trs_wa_rstep[OF this] have "(?m (l\<cdot>\<sigma>), ?m (r\<cdot>\<sigma>)) \<in> rstep ?UR" by simp
  then have small_step: "\<And> C. (C\<langle>?m (l\<cdot>\<sigma>)\<rangle>, C\<langle>?m (r\<cdot>\<sigma>)\<rangle>) \<in> rstep ?UR" by (rule rstep_ctxt)
  have It: "I t"
    unfolding I
  proof (rule conjI[OF IA], intro impI)
    assume invt: "IH t"
    have "IH s" 
    proof (cases bef)
      case (Cons b bbef)
      with invt show ?thesis
        unfolding l r IH C by auto
    next
      case Nil      
      {
        assume tcap: "tcap RB D\<langle>r\<cdot>\<sigma>\<rangle> = GCHole"
        from set_mp[OF subset lr] have "(D\<langle>l\<cdot>\<sigma>\<rangle>,D\<langle>r\<cdot>\<sigma>\<rangle>) \<in> rstep RB" by auto
        from tcap_rewrite[OF this] tcap
        have "tcap RB D\<langle>l\<cdot>\<sigma>\<rangle> = GCHole" 
          by (cases "tcap RB D\<langle>l\<cdot>\<sigma>\<rangle>", auto)          
      }
      with invt show ?thesis 
        unfolding l r IH C Nil by simp
    qed
    with inv[unfolded I]
    show INV by simp
  qed
  show ?thesis
  proof (cases "f = a \<and> Suc (length bef + length aft) = ?n")
    case False
    from False have False: "\<And> t c. (f = a \<and> length (bef @ t # aft) = ?n \<and> c) = False" by auto
    show ?thesis 
      by (rule conjI[OF _ It], rule one_step, rule UnI1, unfold s ss t uncurry_top.simps Let_def False, simp add: no_trans_step)
  next
    case True
    then have f: "f = a" by auto
    show ?thesis
    proof (cases bef)
      case (Cons b bbef)
      from Cons True have n: "Suc (length bbef + length aft) = n" by simp
      show ?thesis
      proof (cases "\<not> (is_Var b) \<and> aarity sm (fst (the (root b))) (num_args b) \<noteq> 0")
        case False
        show ?thesis
          by (rule conjI[OF _ It], rule one_step, rule UnI1, insert True no_trans_step, unfold s ss t f Cons, insert False, unfold uncurry_top.simps Let_def, cases b, auto)
      next
        case True
        then obtain h hs where b: "b = Fun h hs" and len: "0 < aarity sm h (length hs)" by (cases b, auto)
        show ?thesis 
          by (rule conjI[OF _ It],rule one_step, rule UnI1, unfold s ss t f Cons b, insert len step[of "More (get_symbol sm h (length hs) (Suc 0)) (map ?m hs @ map ?m bbef) \<box> (map ?m aft)"], unfold uncurry_top.simps Let_def, simp add: n)
      qed
    next
      case Nil
      with True have n: "n = length aft" by simp
      show ?thesis 
      proof (cases D)
        case (More g bef1 E aft1)
        show ?thesis
        proof (cases "aarity sm g (Suc (length bef1 + length aft1))")
          case 0
          show ?thesis
            by (rule conjI[OF _ It],rule one_step, rule UnI1, insert small_step[of "More a [] (More (get_symbol sm g (Suc (length bef1 + length aft1)) 0) (map ?m bef1) (?C E) (map ?m aft1)) (map ?m aft)"] 0, unfold s ss t f Nil More, simp add: a[unfolded n])
        next
          case (Suc n)
          show ?thesis
            by (rule conjI[OF _ It],rule one_step, rule UnI1, insert insert small_step[of "More (get_symbol sm g (Suc (length bef1 + length aft1)) (Suc 0)) (map ?m bef1) (?C E) (map ?m aft1 @ map ?m aft)"] Suc, unfold s ss t f Nil More, simp add: n)
        qed
      next
        case Hole
        from ndefa subset have ndefaR: "\<not> defined R (a, ?n)" unfolding defined_def by auto
        from lhs lr have "defined R (g,length ls)" unfolding defined_def by auto
        with ndefaR have "(g,length ls) \<noteq> (a,?n)" unfolding defined_def by auto
        then have napp: "(g = a \<and> length ls = ?n) = False" by simp
        have l: "Fun f ss = Fun a ((l \<cdot> \<sigma>) # aft)" and t: "t = Fun a ((r \<cdot> \<sigma>) # aft)" unfolding ss t f Nil Hole by auto          
        then have ss: "ss = (l \<cdot> \<sigma>) #  aft" by simp
        have "length ss = ?n" unfolding ss n by simp
        with inv f have eta: "tcap RB (l \<cdot> \<sigma>) \<noteq> GCHole \<or> INV" unfolding ss CSS I IH s by auto
        from lr subset have "(l,r) \<in> RB" by auto
        from eta tcap_lhs[OF this, of \<sigma>] have INV by auto
        from INV[OF this] have eta: "eta_closed_top a ?n sm R P" and P': "rrstep ?US \<subseteq> rrstep P'" unfolding CSS by auto 
        note an = a[unfolded n]
        note SN_pres = map_sym_preserves_SN[OF inj]
        note SNt = SN_pres[OF SN[unfolded t]]
        note SNut = uncurry_top_preserves_SN[OF inj SN]
        show ?thesis 
        proof (cases "aarity sm g (length ls)")
          case 0
          then have l: "?u (Fun f ss) = Fun a (?m (l \<cdot> \<sigma>) # map ?m aft)" unfolding l lhs
            by (simp add: an)
          let ?t = "Fun a (?m (r \<cdot> \<sigma>) # map ?m aft)"
          obtain tt where tt: "?t = tt" by auto
          from subset have URB: "?UR \<subseteq> ?URB" unfolding map_funs_trs_wa_def by auto
          from small_step[of "More a [] \<box> (map ?m aft)"]
          have urstep: "(?u s, ?t) \<in> rstep ?UR" unfolding l s by auto          
          from set_mp[OF rstep_mono[OF URB] this] have "(?u s, ?t) \<in> rstep ?URB" by simp
          from urstep SN_suc[OF this] have one: "(?u s, ?t) \<in> ?URM" by auto
          have "(?t, ?u t) \<in> (rrstep ?US)^="
            unfolding t by (rule uncurry_top_sig[OF a], simp add: n)
          with P' have two: "(?t, ?u t) \<in> (rrstep P')^=" by auto
          with SNut have two: "(?t, ?u t) \<in> ?CSS^=" by auto
          from one two have "(?u s, ?u t) \<in> ?URM O ?CSS^=" by auto
          then show ?thesis unfolding UR CSP Ms using It by auto
        next            
          case (Suc m)
          then have aa: "aarity sm g (length ls) \<noteq> 0" by simp
          from eta[unfolded eta_closed_top_def, THEN spec, THEN spec, THEN spec, THEN mp[OF _ lr[unfolded lhs]], THEN mp[OF _ aa]]
          obtain ll rr yy where yy1: "length yy = n" and yy2: "distinct yy" 
            and yy3: "set yy \<inter> vars_rule (ll,rr) = {}" and  inst: "instance_rule (l,r) (ll,rr)" and llrr: "(Fun a (ll # map Var yy), Fun a (rr # map Var yy)) \<in> P" unfolding lhs[symmetric] 
            by auto
          from P llrr have hvf: "hvf_top a ?n (Fun a (ll # map Var yy))" by auto
          from yy3 have yl: "set yy \<inter> vars_term ll = {}" and yr: "set yy \<inter> vars_term rr = {}" unfolding vars_rule_def by auto
          from inst[unfolded instance_rule_def] obtain \<delta> where ll: "l = ll \<cdot> \<delta>" and rr: "r = rr \<cdot> \<delta>" by auto
          obtain \<gamma> where gamma: "\<gamma> = \<delta> \<circ>\<^sub>s \<sigma>" by simp
          let ?sig = "subst_extend \<gamma> (zip yy aft)"
          obtain \<tau> where tau: "?sig = \<tau>" by auto
          {
            fix t :: "('f,string)term"
            assume y: "set yy \<inter> vars_term t = {}"              
            then have one: "t \<cdot> ?sig = t \<cdot> \<gamma>" 
              using subst_extend_id[of "UNIV - set yy" "yy" t \<gamma> "aft"] by auto
            from yy1 n have n: "length aft = length yy" by simp
            have two: "map ((subst_extend \<gamma> (zip yy aft))) yy = aft"
            proof (rule nth_equalityI, simp add: n, simp del: subst_extend.simps)
              fix i
              assume i: "i < length yy"
              from n set_zip[of yy aft] have zip: "set (zip yy aft) = {(yy ! i, aft ! i) | i. i < length yy}" by simp
              with i have yi: "(yy ! i, aft ! i) \<in> set (zip yy aft)" by auto
              show "(subst_extend \<gamma> (zip yy aft)) (yy ! i) = aft ! i"
              proof -
                show ?thesis 
                proof (cases "map_of (zip yy aft) (yy ! i)")
                  case None
                  from this[unfolded map_of_eq_None_iff] and yi show ?thesis by force
                next
                  case (Some ai)
                  from map_of_SomeD[OF Some] have "(yy ! i, ai) \<in> set (zip yy aft)" .
                  with zip obtain j where j: "j < length yy" and yij: "yy ! i = yy ! j" and ai: "ai = aft ! j" by auto
                  from nth_eq_iff_index_eq[OF yy2 i j] yij ai have "ai = aft ! i" by simp
                  then show ?thesis
                    by (simp add: Some)
                qed
              qed
            qed
            from one two have "Fun a (t # map Var yy) \<cdot> ?sig = Fun a ((t \<cdot> \<gamma>) # aft)"
              by (simp add: o_def)
          } note id = this
          let ?tau = "map_funs_subst_wa (\<lambda>(f, n). get_symbol sm f n 0) \<tau>"
          from id[OF yl] have l: "Fun f ss = Fun a (ll # map Var yy) \<cdot> ?sig" unfolding l ll gamma by auto
          from id[OF yr] have r: "t = Fun a (rr # map Var yy) \<cdot> ?sig" unfolding t rr gamma by auto            
          from llrr have llrr: "(?u (Fun a (ll # map Var yy)), ?u (Fun a (rr # map Var yy))) \<in> ?UP" 
            unfolding uncurry_top_trs_def by force
          have "(?u (Fun a (rr # map Var yy)) \<cdot> ?tau, ?u t) \<in> (rrstep ?US)^="
            unfolding r tau by (rule uncurry_top_subst[OF a])
          with SNut have two: "(?u (Fun a (rr # map Var yy)) \<cdot> ?tau, ?u t) \<in> (?CSS)^=" using P' by auto
          {
            assume m: ?mini
            have SN: "SN_on (rstep ?URB) {?u (Fun a (rr # map Var yy)) \<cdot> ?tau}"
              by (rule uncurry_top_subst_SN[OF inj ndefa], insert SN[unfolded r tau, OF m])
          } note SN = this
          have "(?u s, ?u (Fun a (rr # map Var yy)) \<cdot> ?tau) \<in> rrstep ?UP"
            unfolding s l tau uncurry_top_subst_hvf[OF hvf] 
            by (rule rrstepI, rule llrr, auto)
          with SN have one: "(?u s, ?u (Fun a (rr # map Var yy)) \<cdot> ?tau) \<in> ?CSP" by auto
          from one two have "(?u s, ?u t) \<in> ?CSP O ?CSS^=" by auto
          then show ?thesis unfolding UR CSP Ms CSS using It by auto
        qed
      qed
    qed
  qed
qed


lemma uncurrying_top_sound_dp:
  fixes P Pw :: "('f,string)trs"
  assumes hvflP: "\<And> l r. (l,r) \<in> P_eta \<union> Pw_eta  \<Longrightarrow> hvf_top a (Suc n) l \<and> is_Fun r"
  and P: "P \<subseteq> P_eta"
  and Pw: "Pw \<subseteq> Pw_eta"
  and P_eta: "\<forall> (l,r) \<in> P \<union> Pw. the (root r) = (a, Suc n) \<and> tcap (R \<union> Rw) (hd (args r)) = GCHole \<longrightarrow> eta_closed_top a (Suc n) sm R P_eta \<and> eta_closed_top a (Suc n) sm Rw Pw_eta \<and> rrstep (uncurry_of_top_sig a (Suc n) sm) \<subseteq> rrstep Pw'"
  and ndefa: "\<not> defined (R \<union> Rw) (a,Suc n)"
  and ndef: "\<And> s f ts. (s,Fun f ts) \<in> P \<union> Pw \<Longrightarrow> \<not> (defined (R \<union> Rw) (f,length ts))"
  and nvar: "\<And> l r. (l,r) \<in> R \<union> Rw \<Longrightarrow> is_Fun l"
  and inj: "inj_sig_map a (Suc n) sm"
  and finite: "finite_dpp (nfs,m,uncurry_top_trs a (Suc n) sm P_eta,uncurry_top_trs a (Suc n) sm Pw_eta \<union> Pw',{},uncurry_below_trs sm R,uncurry_below_trs sm Rw)" (is "finite_dpp (?P,?Pw,_,?R,?Rw)")
  shows "finite_dpp (nfs,m,P,Pw,{},R,Rw)"
proof - 
  let ?n = "Suc n"
  let ?u = "uncurry_top a ?n sm"
  let ?us = "uncurry_top_subst sm"
  let ?US = "uncurry_of_top_sig a (Suc n) sm"
  let ?map = "map_funs_trs_wa (\<lambda>(f, n). get_symbol sm f n 0)"
  let ?Q = "{}"
  let ?Q' = "{}"
  let ?R = "qrstep nfs ?Q R"
  let ?Rw = "qrstep nfs ?Q Rw" 
  let ?P = "rrstep P \<inter> {(s,t). s \<in> NF_terms ?Q}"
  let ?Pw = "rrstep Pw \<inter> {(s,t). s \<in> NF_terms ?Q}"
  let ?M = "\<lambda>x. SN_on (qrstep nfs ?Q (R \<union> Rw)) {x}"
  let ?M' = "\<lambda>x. SN_on (qrstep nfs ?Q' (?map R \<union> ?map Rw)) {x}"
  let ?Ms = "{(s,t). m \<longrightarrow> ?M' t}"
  let ?Ms' = "{(s,t). m \<longrightarrow> SN_on (rstep (?map (R \<union> Rw))) {t}}"
  let ?P' = "uncurry_top_trs a ?n sm P_eta"
  let ?Pwo' = "uncurry_top_trs a ?n sm Pw_eta"
  let ?Pw' = "uncurry_top_trs a ?n sm Pw_eta \<union> Pw'"
  let ?R' = "?map R"
  let ?Rw' = "?map Rw"
  let ?UR = "qrstep nfs ?Q' ?R'"
  let ?URw = "qrstep nfs ?Q' ?Rw'"
  let ?UP = "rrstep ?P' \<inter> {(s,t). s \<in> NF_terms ?Q'}"
  let ?UPw = "rrstep ?Pw' \<inter> {(s,t). s \<in> NF_terms ?Q'}"
  let ?A = "?UP \<inter> ?Ms \<union> ?UPw \<inter> ?Ms \<union> ?UR \<union> ?URw"
  let ?As = "?A^*"
  from inj_sig_map_a[OF inj] have a: "get_symbol sm a ?n 0 = a" by auto
  { 
    fix s t :: "('f,string)term" and \<sigma>
    assume M: "m \<longrightarrow> ?M (t \<cdot> \<sigma>)" and "is_Fun t" and ip: "(s,t) \<in> P \<union> Pw"
    then obtain f ts where t: "t = Fun f ts" by (cases t, auto)
    let ?p = "(?u t \<cdot> ?us \<sigma>, ?u (t \<cdot> \<sigma>))"
    have t_subst_pre: "?p \<in> (rrstep Pw')^=" 
    proof (cases "hvf_top a ?n t")
      case True
      show ?thesis unfolding uncurry_top_subst_hvf[OF True] by auto
    next
      case False
      then have p: "the (root t) = (a, ?n) \<and> tcap (R \<union> Rw) (hd (args t)) = GCHole" unfolding t
        by (cases "hd ts", auto)
      then have mem: "?p \<in> (rrstep ?US)^="
        using uncurry_top_subst[OF a, of f ts \<sigma>] unfolding t by auto
      from p P_eta[THEN bspec[OF _ ip]] have "rrstep ?US \<subseteq> rrstep Pw'" by auto
      with mem show ?thesis by auto
    qed
    from M have min: "m \<longrightarrow> SN_on (rstep (R \<union> Rw)) {t \<cdot> \<sigma>}" by auto
    from uncurry_top_preserves_SN[OF inj] min t_subst_pre 
    have "?p \<in> (rrstep Pw' \<inter> ?Ms)^=" unfolding map_funs_trs_wa_union[symmetric] by auto
    then have "?p \<in> ?A^=" unfolding rrstep_union by auto
    then have "?p \<in> ?A^*" by auto
  } note t_subst = this
  let ?IA = "\<lambda> t. \<not> defined (R \<union> Rw) (the (root t)) \<and> is_Fun t"
  let ?IH = "\<lambda> t. (the (root t)) = (a,?n) \<and> tcap (R \<union> Rw) (hd (args t)) = GCHole"
  let ?IC = "eta_closed_top a ?n sm Rw Pw_eta \<and> eta_closed_top a ?n sm R P_eta \<and> rrstep ?US \<subseteq> rrstep Pw'"
  let ?I = "\<lambda> t. ?IA t \<and> (?IH t \<longrightarrow> ?IC)"
  show ?thesis
  proof (rule finite_dpp_map_min[OF finite, where f = ?u and I = ?I and Q = "{}", unfolded rqrstep_rrstep_conv])
    fix t
    assume SN: "m \<longrightarrow> ?M t"
    {
      assume m
      with SN have "?M t" by blast
      from uncurry_top_preserves_SN[OF inj this[unfolded qrstep_rstep_conv]]
      have "?M' (?u t)" unfolding qrstep_rstep_conv map_funs_trs_wa_union rstep_union .
    }
    then show "m \<longrightarrow> ?M' (?u t)" ..
  next
    fix s t
    assume M: "m \<longrightarrow> ?M t" and "(s,t) \<in> ?P"
    then have "(s,t) \<in> rrstep P" by auto
    from this[unfolded rrstep_def'] obtain l r \<sigma> where iP: "(l,r) \<in> P" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" by auto
    with P have inP: "(l,r) \<in> P_eta" and inPPw: "(l,r) \<in> P_eta \<union> Pw_eta" and iPPw: "(l,r) \<in> P \<union> Pw" by auto
    from inP have P: "(?u l, ?u r) \<in> ?P'" unfolding uncurry_top_trs_def  by auto 
    from hvflP[OF inPPw] obtain f ts where r: "r = Fun f ts" and nvar: "is_Fun r" by (cases r, auto)
    from ndef[OF iPPw[unfolded r]] have ndef: "\<not> defined (R \<union> Rw) (f, length ts)" .
    from hvflP[OF inPPw] obtain g ss where l: "l = Fun g ss" by (cases l, auto)
    from hvflP[OF inPPw] l have hvf: "hvf_top a ?n (Fun g ss)" by auto
    have s_subst: "?u (l \<cdot> \<sigma>) = ?u l \<cdot> ?us \<sigma>"  unfolding l by (rule uncurry_top_subst_hvf[OF hvf])
    have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> rrstep ?P'" unfolding s s_subst using P by auto
    from M have "m \<longrightarrow> SN_on (rstep (R \<union> Rw)) {r \<cdot> \<sigma>}" unfolding t by simp
    from uncurry_top_subst_SN[OF inj ndefa] this have "m \<longrightarrow> ?M' (?u r \<cdot> ?us \<sigma>)"
      unfolding map_funs_trs_wa_union by auto
    with step have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> ?UP \<inter> ?Ms" by auto
    from t_subst[OF M[unfolded t] nvar iPPw] have "(?u r \<cdot> ?us \<sigma>, ?u t) \<in> ?As"  unfolding t .
    with step have step: "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms) O ?As" by auto
    have IA: "?IA t" unfolding t r using ndef by auto
    {
      assume "?IH t"
      from this[unfolded t r, simplified]
      have f: "f = a" and l: "length ts = ?n" and tcap: "tcap (R \<union> Rw) (hd (map (\<lambda> t. t \<cdot> \<sigma>) ts)) = GCHole"  by auto
      from l obtain s ss where ts: "ts = s # ss" and l: "length ss = n" by (cases ts, auto)
      from tcap have tcap: "tcap (R \<union> Rw) (s \<cdot> \<sigma>) = GCHole" unfolding ts by auto
      from tcap_instance_subset[of "R \<union> Rw" s \<sigma>] have tcap: "tcap (R \<union> Rw) s = GCHole" unfolding tcap
        by (cases "tcap (R \<union> Rw) s", auto)
      from P_eta[THEN bspec[OF _ iPPw], unfolded split t r f ts tcap[symmetric]]
      have "?IC" using l by auto
    } with IA have "?I t" by blast
    with step 
    show "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms) O ?As \<and> ?I t" ..
  next
    fix s t
    assume M: "m \<longrightarrow> ?M t" and "(s,t) \<in> ?Pw"
    then have "(s,t) \<in> rrstep Pw" by auto
    from this[unfolded rrstep_def'] obtain l r \<sigma> where iP: "(l,r) \<in> Pw" and s: "s = l \<cdot> \<sigma>" and t: "t = r \<cdot> \<sigma>" by auto
    with Pw have inP: "(l,r) \<in> Pw_eta" and inPPw: "(l,r) \<in> P_eta \<union> Pw_eta" and iPPw: "(l,r) \<in> P \<union> Pw" by auto
    from inP have P: "(?u l, ?u r) \<in> ?Pw'" unfolding uncurry_top_trs_def  by auto 
    from hvflP[OF inPPw] obtain f ts where r: "r = Fun f ts" and nvar: "is_Fun r" by (cases r, auto)
    from ndef[OF iPPw[unfolded r]] have ndef: "\<not> defined (R \<union> Rw) (f, length ts)" .
    from hvflP[OF inPPw] obtain g ss where l: "l = Fun g ss" by (cases l, auto)
    from hvflP[OF inPPw] l have hvf: "hvf_top a ?n (Fun g ss)" by auto
    have s_subst: "?u (l \<cdot> \<sigma>) = ?u l \<cdot> ?us \<sigma>"  unfolding l by (rule uncurry_top_subst_hvf[OF hvf])
    have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> rrstep ?Pw'" unfolding s s_subst using P by auto
    from M have "m \<longrightarrow> SN_on (rstep (R \<union> Rw)) {r \<cdot> \<sigma>}" unfolding t by simp
    from uncurry_top_subst_SN[OF inj ndefa] this have "m \<longrightarrow> ?M' (?u r \<cdot> ?us \<sigma>)"
      unfolding map_funs_trs_wa_union by simp
    with step have step: "(?u s, ?u r \<cdot> ?us \<sigma>) \<in> ?UP \<inter> ?Ms \<union> ?UPw \<inter> ?Ms" by auto
    from t_subst[OF M[unfolded t] nvar iPPw] have "(?u r \<cdot> ?us \<sigma>, ?u t) \<in> ?As"  unfolding t .
    with step have step: "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms \<union> ?UPw \<inter> ?Ms) O ?As" by auto
    have IA: "?IA t" unfolding t r using ndef by auto
    {
      assume "?IH t"
      from this[unfolded t r, simplified]
      have f: "f = a" and l: "length ts = ?n" and tcap: "tcap (R \<union> Rw) (hd (map (\<lambda> t. t \<cdot> \<sigma>) ts)) = GCHole"  by auto
      from l obtain s ss where ts: "ts = s # ss" and l: "length ss = n" by (cases ts, auto)
      from tcap have tcap: "tcap (R \<union> Rw) (s \<cdot> \<sigma>) = GCHole" unfolding ts by auto
      from tcap_instance_subset[of "R \<union> Rw" s \<sigma>] have tcap: "tcap (R \<union> Rw) s = GCHole" unfolding tcap
        by (cases "tcap (R \<union> Rw) s", auto)
      from P_eta[THEN bspec[OF _ iPPw], unfolded split t r f ts tcap[symmetric]]
      have "?IC" using l by auto
    } with IA have "?I t" by blast
    with step 
    show "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms \<union> ?UPw \<inter> ?Ms) O ?As \<and> ?I t" ..
  next
    fix s t
    assume I: "?I s" and Ms: "m \<longrightarrow> ?M s" and Mt: "m \<longrightarrow> ?M t" and step: "(s,t) \<in> ?Rw"
    from Ms have SN: "m \<Longrightarrow> SN_on (rstep (R \<union> Rw)) {s}" by simp
    from hvflP have hvfP: "\<forall> (l,r) \<in> Pw_eta. hvf_top a ?n l" by auto
    from step have step: "(s,t) \<in> rstep Rw" by auto
    have res: "(?u s, ?u t) \<in> (rrstep ?Pwo' \<inter> ?Ms' \<union> rstep ?Rw') O ((rrstep Pw' \<inter> ?Ms')^=) \<and> ?I t"
      by (rule uncurry_top_step[OF inj ndefa step hvfP nvar I _ _ SN], auto)
    have step: "(?u s, ?u t) \<in> (?UPw \<inter> ?Ms \<union> ?URw) O (?UPw \<inter> ?Ms)^=" 
      by (rule set_mp[OF _ res[THEN conjunct1]], unfold rrstep_union map_funs_trs_wa_union, auto)
    have step: "(?u s, ?u t) \<in> ?A O ?A^="
      by (rule set_mp[OF _ step], regexp)
    have step: "(?u s, ?u t) \<in> ?As"
      by (rule set_mp[OF _ step], regexp)
    from res[THEN conjunct2] have "?I t" .
    with step show "(?u s, ?u t) \<in> ?As \<and> ?I t" ..
  next
    fix s t
    assume I: "?I s" and Ms: "m \<longrightarrow> ?M s" and Mt: "m \<longrightarrow> ?M t" and step: "(s,t) \<in> ?R"
    from Ms have SN: "m \<Longrightarrow> SN_on (rstep (R \<union> Rw)) {s}" by simp
    from hvflP have hvfP: "\<forall> (l,r) \<in> P_eta. hvf_top a ?n l" by auto
    from step have step: "(s,t) \<in> rstep R" by auto
    have res: "(?u s, ?u t) \<in> (rrstep ?P' \<inter> ?Ms' \<union> rstep ?R') O ((rrstep Pw' \<inter> ?Ms')^=) \<and> ?I t"
      by (rule uncurry_top_step[OF inj ndefa step hvfP nvar I _ _ SN], auto)
    have step: "(?u s, ?u t) \<in> (?UP \<inter> ?Ms \<union> ?UR) O (?UPw \<inter> ?Ms)^=" 
      by (rule set_mp[OF _ res[THEN conjunct1]], unfold rrstep_union map_funs_trs_wa_union, auto)
    have step: "(?u s, ?u t) \<in> (?UP \<inter> ?Ms \<union> ?UR) O ?As^=" 
      by (rule set_mp[OF _ step], auto)
    have step: "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms \<union> ?UR) O ?As"
      by (rule set_mp[OF _ step], regexp)
    from res[THEN conjunct2] have "?I t" .
    with step show "(?u s, ?u t) \<in> ?As O (?UP \<inter> ?Ms \<union> ?UR) O ?As \<and> ?I t" ..
  qed 
qed

end
