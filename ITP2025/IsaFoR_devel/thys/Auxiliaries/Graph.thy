(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Graph
imports
  Certification_Monads.Check_Monad
  Show.Shows_Literal
begin

type_synonym 'a graph = "'a set \<times> ('a \<times> 'a) set"
type_synonym 'a ipath = "nat \<Rightarrow> 'a"

definition nodes :: "'a graph \<Rightarrow> 'a set"
where "nodes G = fst G"
  

definition
  path_nodes :: "'a ipath \<Rightarrow> 'a set"
where
  "path_nodes p = range p"

definition
  suffix :: "'a ipath \<Rightarrow> 'a ipath \<Rightarrow> bool" ("_ =\<dots> _" 50)
where
  "(p =\<dots> q) = (\<exists> n. \<forall> m. (p (m+n) = q m))"

lemma suffix_trans[trans]: assumes "p =\<dots> q" and "q =\<dots> r" shows "p =\<dots> r"
using assms proof (unfold suffix_def)
  assume "\<exists>n. \<forall>m. p (m + n) = q m" 
  from this obtain n1 where A: "\<forall> m. p (m + n1) = q m" ..
  assume "\<exists>n. \<forall>m. q (m + n) = r m"
  from this obtain n2 where B: "\<forall>m. q (m + n2) = r m" ..
  have " \<forall>m. p (m + (n2 + n1)) = (r m)" 
  proof 
    fix m
    have "m + (n2 + n1) = m + n2 + n1" (is "?x = ?y") by arith
    then have "p (m + (n2 + n1)) = p (m + n2 + n1)" using arg_cong[where x = ?x and y = ?y] by simp
    also from A have "\<dots> = q (m + n2) " ..
    also from B have "\<dots> = r m" ..
    finally show "p (m + (n2 + n1)) = r m" .
 qed
 then show  "\<exists>n. \<forall>m. p (m + n) = r m" ..
qed

(* start of automated check *)
context
  fixes ss :: "'a \<Rightarrow> showsl" (* printer of nodes *)
  and empty_index :: "'i"
  and candidates :: "'i \<Rightarrow> 'a \<Rightarrow> 'a list"  (* approximation of node *)
  and add_index :: "'a \<Rightarrow> 'i \<Rightarrow> 'i" (* check edge via approximation *)
  and index_set :: "'i \<Rightarrow> 'a set"
  and g :: "'a \<times> 'a \<Rightarrow> bool" (* graph *)
begin

definition check_no_edge :: "'a \<Rightarrow> 'a \<Rightarrow> showsl check" where
  "check_no_edge m n = (check (\<not> g (m, n)) (showsl_lit (STR ''edge from '') \<circ> ss m \<circ> showsl_lit (STR '' to '') \<circ> ss n))"

lemma check_no_edge[simp]: "isOK(check_no_edge m n) = (\<not> g (m,n))"
  unfolding check_no_edge_def by simp 

definition
  check_edges :: "'a list \<Rightarrow> 'a list \<Rightarrow> showsl check"
where
  "check_edges c d =
     check_allm (\<lambda>n. check_allm (check_no_edge n) d) c"

lemma check_edges_sound[simp]:
  "isOK (check_edges c d) = (\<forall>m\<in>set c. (\<forall>n \<in>set d. (\<not> g (m, n))))"
  unfolding check_edges_def by auto

fun check_no_back_edges :: "'i \<Rightarrow> 'a list list \<Rightarrow> showsl check"
where
  "check_no_back_edges i [] = succeed" |
  "check_no_back_edges i (as # Cs) = (check_allm (\<lambda> a. 
     check_allm (check_no_edge a) (candidates i a)) as 
    >> check_no_back_edges (foldr add_index as i) Cs)"

definition
  check_graph_decomp
    :: "(bool \<times> 'a list) list \<Rightarrow> showsl check"
where
  "check_graph_decomp rcs = do {
     check_no_back_edges empty_index (map snd rcs);
     check_allm (\<lambda>c. check_edges c c) (map snd (filter (\<lambda>rc. \<not> (fst rc)) rcs))
   }"

context 
  fixes P :: "'i \<Rightarrow> bool"
  assumes index_set[simp]: "index_set empty_index = {}"
    "index_set (add_index a i) = insert a (index_set i)"
  and P[simp]: "P empty_index" "P i \<Longrightarrow> P (add_index a i)"
  and candidates: "P i \<Longrightarrow> g (a,b) \<Longrightarrow> b \<in> index_set i \<Longrightarrow> b \<in> set (candidates i a)"  
begin

lemma insert_set_foldr[simp]: "index_set (foldr add_index as i) = set as \<union> index_set i"
  by (induct as arbitrary: i, auto)

lemma P_foldr[simp]: "P i \<Longrightarrow> P (foldr add_index as i)"
  by (induct as arbitrary: i, auto simp: P)

lemma check_no_back_edges: assumes "isOK(check_no_back_edges index cs)" "P index"
  shows "\<forall> j < length cs. \<forall> i < j. \<forall> n \<in> set (cs ! i). \<forall> m \<in> set (cs ! j). \<not> (g (m,n))"
proof (rule ccontr)
  assume "\<not> ?thesis"
  then obtain i j n m where j: "j < length cs" and i: "i < j" and n: "n \<in> set (cs ! i)"
  and m: "m \<in> set (cs ! j)" and "g (m,n)" by auto
  note candidates = candidates[OF _ \<open>g (m,n)\<close>]
  from j i have "i < length cs" by auto
  with assms have "\<exists> index. P index \<and> isOK(check_no_back_edges index (drop i cs))"
  proof (induct cs arbitrary: i index)
    case (Cons c cs i)
    then show ?case by (cases i, auto)
  qed simp
  then obtain index' where Pi: "P index'" and ok: "isOK(check_no_back_edges index' (drop i cs))" by auto
  have cs: "cs = take i cs @ cs ! i # drop (Suc i) cs" 
    using \<open>i < length cs\<close> id_take_nth_drop by blast
  from arg_cong[OF this, of "drop i"] \<open>i < length cs\<close> have drop: "drop i cs = cs ! i # drop (Suc i) cs"
    by auto
  define csr where "csr = drop (Suc i) cs"
  define index where "index = foldr add_index (cs ! i) index'"
  from n have n: "n \<in> index_set index" unfolding index_def by simp      
  from ok[unfolded drop]
  have ok: "isOK (check_no_back_edges index csr)" unfolding index_def csr_def
    by auto
  define k where "k = j - (i + Suc 0)"
  from i have jk: "j = i + Suc k" unfolding k_def by simp
  have csj: "cs ! j = drop (Suc i) cs ! k" and k: "k < length (drop (Suc i) cs)" 
    unfolding arg_cong[OF cs, of "\<lambda> cs. cs ! j"]
    unfolding jk using \<open>i < length cs\<close> 
    by (subst nth_drop, auto simp: cs[symmetric], insert j jk, auto)
  from k m have m: "m \<in> set (concat csr)" unfolding csr_def[symmetric] csj by auto
  from Pi have Pi: "P index" unfolding index_def by simp

  from ok m n Pi show False
  proof (induct csr arbitrary: index)
    case (Cons c csr index)
    note IH = Cons(1)
    note ok = Cons(2)
    note m = Cons(3)
    note n = Cons(4)
    note Pi = Cons(5)
    show ?case
    proof (cases "m \<in> set c")
      case False
      then have m: "m \<in> set (concat csr)" using m by auto
      from ok have ok: "isOK (local.check_no_back_edges (foldr add_index c index) csr)" by simp
      show False
        by (rule IH[OF ok m], insert n Pi, auto)
    next
      case True
      from candidates[OF Pi n] have "n \<in> set (candidates index m)" .
      with True ok[simplified] \<open>g (m,n)\<close> show False by simp
    qed
  qed simp
qed 

lemma check_graph_decomp_sound: 
  assumes check: "isOK (check_graph_decomp cs)"
  and path: "\<And> n. g (p n, p (Suc n))"
  and nodes: "path_nodes p \<subseteq> set (concat (map snd cs))" (is "?pn p cs")
  shows "\<exists> q C . p =\<dots> q \<and> C \<in> set (map snd (filter fst cs)) \<and> path_nodes q \<subseteq>  set C" 
proof -
  let ?cs = "map snd cs"
  let ?ncs = "map snd (filter (\<lambda> rc. \<not> (fst rc)) cs)"
  let ?inn = "\<lambda> c. (\<forall> n \<in> set c. \<forall> m \<in> set c. \<not> (g (m,n)))"
  note check = check[unfolded check_graph_decomp_def]
  from check have nr_sccs: "\<forall> c \<in> set ?ncs. ?inn c" (is "?in cs") by auto
  from check have back_e: "\<forall> j < length cs. \<forall> i < j. \<forall> n \<in> set (?cs ! i). \<forall> m \<in> set (?cs ! j). \<not> (g (m,n))" (is "?back cs")
    using check_no_back_edges by auto
  from path nr_sccs back_e nodes show ?thesis 
  proof (induct cs arbitrary: p)
    case Nil
    then show ?case unfolding path_nodes_def by auto
  next
    case (Cons rc cs)
    let ?cs = "map snd cs"
    let ?ncs = "map snd (filter (Not o fst) cs)"    
    {
      fix q
      assume "p =\<dots> q"
      from this[unfolded suffix_def] obtain n where q: "\<And> m. p (m + n) = q m" by auto        
      then have q: "\<And> m. q m = p (m + n)" by simp
      from Cons(2) have "\<And> n. g (q n, q (Suc n))" unfolding q by simp
    } note path_suffix = this
    show ?case
    proof (cases "\<exists> q. p =\<dots> q \<and> path_nodes q \<subseteq> set (concat ?cs)")
      case True
      from this obtain q where pq: "p =\<dots> q" and qnodes: "?pn q cs" by auto
      from Cons(4) have "?back cs" by force
      have "?in cs" 
      proof
        fix c
        assume "c \<in> set (map snd [r\<leftarrow>cs . \<not> fst r])"
        then have "c \<in> set (map snd [r\<leftarrow>rc # cs . \<not> fst r])" by auto
        with \<open>?in (rc # cs)\<close> show "?inn c" by auto 
      qed
      from path_suffix[OF pq] \<open>?pn q cs\<close> \<open>?in cs\<close> \<open>?back cs\<close> Cons 
      have "\<exists> r C. q =\<dots> r \<and> C \<in> set (map snd (filter fst cs)) \<and> path_nodes r \<subseteq> set C" by auto
      then obtain r C where qr: "q =\<dots> r" and C: "C \<in> set (map snd (filter fst cs))" 
        and r: "path_nodes r \<subseteq> set C" by force
      from pq qr have p_r: "p =\<dots> r" using suffix_trans by auto
      from C have "C \<in> set (map snd (filter fst (rc # cs)))" by auto
      with p_r r show ?thesis by blast
    next
      case False
      then have ends_not_in_cs: "\<forall> q. p =\<dots> q \<longrightarrow> (\<not> path_nodes q \<subseteq> set (concat ?cs))" by auto
      obtain r c where Pair: "rc = (r,c)" by force
      show ?thesis 
      proof (cases "\<exists> q. p =\<dots> q \<and> path_nodes q \<subseteq> set c")
        case True
        from this obtain q :: "'a ipath" where pq: "p =\<dots> q" and pnodes: "path_nodes q \<subseteq> set c" by auto
        have r
        proof (rule ccontr)
          assume "\<not> r"
          with Cons Pair have contra: "?inn c" by auto
          from path_suffix[OF pq]
            contra pnodes show False
            unfolding path_nodes_def by force
        qed
        with pq pnodes Pair show ?thesis  by auto
      next
        case False
        have "p =\<dots> p" unfolding suffix_def
        proof
          show "\<forall> m. p (m + 0) = p m" by auto
        qed
        with False have "\<not> path_nodes p \<subseteq> set c" by auto
        from this obtain i where i: "p i \<notin> set c" unfolding path_nodes_def by auto 
        obtain q where q: "\<forall> j. p (j + (Suc i)) = q j" by force
        then have pq: "p =\<dots> q" unfolding suffix_def ..
        with ends_not_in_cs have "\<not> path_nodes q \<subseteq> set (concat ?cs)" by auto
        from this obtain j where j: "q j \<notin> set (concat ?cs)" unfolding path_nodes_def by auto
        let ?k = "Suc (j + i)"
        from j q have k: "p ?k \<notin> set (concat ?cs)" by auto
        from i k Pair \<open>?pn p (rc # cs)\<close> have nearly: "p i \<in> set (concat ?cs) \<and> p ?k \<in> set c"
          unfolding path_nodes_def by (simp, blast)
        then have "\<exists> k. p k \<in> set (concat ?cs) \<and> p (Suc k) \<in> set c"
        proof (induct j arbitrary: i)
          case 0
          then show ?case by auto
        next
          case (Suc j)
          then show ?case 
          proof (cases "p (Suc i) \<in> set c")
            case True
            with Suc show ?thesis by auto
          next
            case False
            with \<open>?pn p (rc # cs)\<close> Pair have p: "p (Suc i) \<in> set (concat ?cs)" unfolding path_nodes_def by auto
            have su: "Suc (Suc j + i) = Suc (j + Suc i)" by auto
            with Suc p show ?thesis by (simp only: su, blast)  
          qed
        qed
        from this obtain l where contra: "p l \<in> set (concat ?cs) \<and> p (Suc l) \<in> set c" by auto
        from this obtain d where d: "p l \<in> set d \<and> d \<in> set ?cs" by auto
        from this obtain m where m: "m < length ?cs \<and> ?cs ! m = d" using set_conv_nth[where xs = ?cs] by force
        with \<open>?back (rc # cs)\<close> d contra  have "\<not> g (p l, p (Suc l))"
          unfolding Pair by force
        with Cons(2) show ?thesis by simp
      qed
    qed
  qed
qed
end
end
end
