(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Memories
imports
  Util
begin

datatype comparison = Less | Equal | More

(**
    A memory model is an element of type [('m,'a,'b)memory] where
    ['m] is the type of the memory, ['a] is the type of the keys
    and ['b] is the type of the values. A memory model is given by
    three functions:
    - [empty ()] returns an empty memory;
    - [lookup M k] tries to find the value [v] associated to [k]
      in the memory [M];
    - [store M (k,v)] stores the value [v] to the index [k] in the
      memory [M]
**)

record ('m,'a,'b)memory =
  empty  :: "unit \<Rightarrow> 'm"
  lookup :: "'m \<Rightarrow> 'a \<Rightarrow> 'b option"
  store  :: "'m \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'm"

definition singleton :: "('m,'a,'b)memory \<Rightarrow> ('a \<times> 'b) \<Rightarrow> 'm" where
  "singleton model =  memory.store model (memory.empty model ())"

(**
    A memory is valid with respect to a function [f] if, when queried,
    it only returns values that are images of the keys by [f].
    A satisfactory memory model is a memory model such that one can
    find a predicate [P] where:
    - If [P(M, f)] holds then all the queries on [M] return values
    that are image of the keys by [f]
    - For all [f], [P(empty (), f)] holds
    - [store] preserves the validity of [P]
**)

definition valid :: "('m,'a,'b)memory \<Rightarrow> 'm \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> bool" where
  "valid model M f \<equiv> (\<forall>a b. memory.lookup model M a = Some b \<longrightarrow> f a = b)"

definition satisfactory where
  "satisfactory P model \<equiv> (\<forall>f. P model (memory.empty model ()) f)
    \<and> (\<forall>f a M. P model M f \<longrightarrow> P model (memory.store model M (a, f a)) f)
    \<and> (\<forall>M f. P model M f \<longrightarrow> valid model M f)"

declare satisfactory_def[simp]

lemma singleton_valid:
  assumes "satisfactory P model"
  and "f k = v"
  shows "P model (singleton model (k, v)) f"
using assms unfolding singleton_def by auto

(**
    The first example of a satisfactory memory model is obviously
    the list of tuples: key \<times> value. Given that the structure is
    really simple, [valid] is a powerful enough validity predicate.
**)

fun lm_store_acc :: "('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) \<Rightarrow> ('k \<times> 'v) list \<Rightarrow> ('k \<times> 'v) list" where
 "lm_store_acc [] kv accu = kv # accu" |
 "lm_store_acc ((a,_) # rec) (k,v) accu = (
    case k = a of True \<Rightarrow> accu | False \<Rightarrow> lm_store_acc rec (k,v) accu)"

definition lm_store where "lm_store M kv = lm_store_acc M kv M"

lemma lm_store_acc_sound1:
  assumes "\<exists>b. (k, b) \<in> set M"
  shows "lm_store_acc M (k, v) rec = rec"
using assms proof (induct M)
case Nil then show ?case by simp
next
case (Cons afa M)
  obtain a fa where Hafa: "afa = (a, fa)" by (cases afa) auto
  with Cons show ?case by (cases "a = k") simp_all
qed

lemma lm_store_sound1:
  assumes "\<exists>b. (k, b) \<in> set M"
  shows "lm_store M (k, v) = M"
using assms lm_store_acc_sound1 by (simp add: lm_store_def)

lemma lm_store_acc_sound2:
  assumes "\<not> (\<exists>b. (k, b) \<in> set M)"
  shows "lm_store_acc M (k, v) rec = (k, v) # rec"
using assms proof (induct M)
case Nil then show ?case by simp
next
case (Cons afa M)
  obtain a fa where Hafa: "afa = (a, fa)" by (cases afa) auto
  with Cons show ?case by (cases "a = k") auto
qed

lemma lm_store_sound2:
  assumes "\<not> (\<exists>b. (k, b) \<in> set M)"
  shows "lm_store M (k, v) = (k,v) # M"
using assms lm_store_acc_sound2 by (simp add: lm_store_def)

definition lm :: "(('k \<times> 'v) list, 'k, 'v) memory" where
  "lm \<equiv> \<lparr> empty = (\<lambda>_. []), lookup = map_of, store = lm_store \<rparr>"

lemma satisfactory_lm: "satisfactory valid lm"
proof-
have lm_empty: "\<forall>f. valid lm (memory.empty lm ()) f" by (simp add: lm_def valid_def)
{
  fix f a M k v
  assume M_valid: "valid lm M f"
  and Hlkp: "memory.lookup lm (store lm M (a, f a)) k = Some v"
  have "f k = v"
  proof (cases "\<exists>b. (a, b) \<in> set M")
  case True
    from M_valid lm_store_sound1[OF this] Hlkp
     show ?thesis by (simp add: valid_def lm_def)
  next
  case False
    from M_valid lm_store_sound2[OF this] Hlkp
     show ?thesis by (cases "k = a") (simp_all add: valid_def lm_def)
  qed
}
then have lm_store: "\<forall>f a b M. valid lm M f \<longrightarrow> f a = b \<longrightarrow> valid lm (memory.store lm M (a,b)) f"
 by (auto simp: valid_def)
from lm_empty lm_store show ?thesis unfolding satisfactory_def by fast
qed

(**
    The second example arise when we consider functions [f] taking
    two variables. It is the curryfied counterpart of lm when key
    is actually a tuple.
**)

fun l2m_lookup :: "('k1 \<times> ('k2 \<times> 'v) list) list \<Rightarrow> ('k1 \<times> 'k2) \<Rightarrow> 'v option" where
  "l2m_lookup [] _ = None"
| "l2m_lookup ((a, kvs) # rec) (k1, k2) =
    (case k1 = a of
      True \<Rightarrow> map_of kvs k2
    | False \<Rightarrow> l2m_lookup rec (k1, k2))"

fun l2m_store :: "('k1 \<times> ('k2 \<times> 'v) list) list \<Rightarrow> (('k1 \<times> 'k2) \<times> 'v) \<Rightarrow> ('k1 \<times> ('k2 \<times> 'v) list) list" where
  "l2m_store [] ((k1, k2), v) = [ (k1, [(k2, v)]) ]" |
  "l2m_store ((a, kvs) # rec) ((k1, k2), v) =
   (case k1 = a of
      True  \<Rightarrow> (a, lm_store kvs (k2, v)) # rec
    | False \<Rightarrow> (a, kvs) # (l2m_store rec ((k1, k2), v)))"

definition l2m :: "(('k1 \<times> ('k2 \<times> 'v) list) list, 'k1 \<times> 'k2, 'v)memory" where
  "l2m \<equiv> \<lparr> empty = \<lambda>_. [], lookup = l2m_lookup, store = l2m_store \<rparr>"

definition l2m_valid :: "(('k1 \<times> ('k2 \<times> 'v) list) list, 'k1 \<times> 'k2, 'v)memory \<Rightarrow>
                         ('k1 \<times> ('k2 \<times> 'v) list) list \<Rightarrow> (('k1 \<times> 'k2) \<Rightarrow> 'v) \<Rightarrow> bool" where
  "l2m_valid _ M f \<equiv> \<forall> (k1, kvs) \<in> set M. \<forall> (k2, v) \<in> set kvs. f (k1, k2) = v"

lemma satisfactory_l2m: "satisfactory l2m_valid l2m"
proof-
have l2m_empty: "\<forall>f. l2m_valid l2m (memory.empty l2m ()) f" by (simp add: l2m_def l2m_valid_def)
{
  fix f k1 k2 M
  assume M_valid: "l2m_valid l2m M f"
  from M_valid have "l2m_valid l2m (memory.store l2m M ((k1, k2), f (k1, k2))) f"
  proof (induct M)
  case Nil then show ?case by (simp add: l2m_valid_def l2m_def)
  next
  case (Cons akvs rec)
    obtain a kvs where akvs: "akvs = (a, kvs)" by (cases akvs) auto
    show ?case
    proof (cases "k1 = a")
    case True note Hk1a = this
      show ?thesis
      proof (cases "\<exists>b. (k2, b) \<in> set kvs")
      case True
        from lm_store_sound1[OF this] Cons(2) akvs Hk1a
         show ?thesis by (simp add: l2m_valid_def l2m_def)
      next
      case False
        from lm_store_sound2[OF this] Cons(2) akvs Hk1a
         show ?thesis by (simp add: l2m_valid_def l2m_def)
      qed
    next
    case False
      with akvs have store_rew: "memory.store l2m (akvs # rec) ((k1, k2), f (k1, k2)) \<equiv>
        akvs # (memory.store l2m rec ((k1, k2), f (k1, k2)))" by (simp add: l2m_def)
      from Cons(2) have "l2m_valid l2m rec f" by (simp add: l2m_valid_def)
      from Cons(1)[OF this] Cons(2) False akvs store_rew
       show ?thesis by (simp add: l2m_valid_def)
    qed
  qed
}
then have l2m_store: "\<forall>f a M. l2m_valid l2m M f
   \<longrightarrow> l2m_valid l2m (memory.store l2m M (a, f a)) f" by fast
{
  fix M f k b
  assume l2m_valid: "l2m_valid l2m M f" and Hget: "memory.lookup l2m M k = Some b"
  obtain k1 k2 where kkk: "k = (k1, k2)" by (cases k) auto
  from l2m_valid Hget have "f k = b"
  proof (induct M)
  case Nil then show ?case by (simp add: l2m_def)
  next
  case (Cons akvs rec)
    obtain a kvs where akvs: "akvs = (a, kvs)" by (cases "akvs") auto
    show ?case
    proof (cases "k1 = a")
    case True
      with Cons(2) akvs kkk Cons(3) map_of_SomeD[of kvs k2 b]
       show ?thesis by (auto simp: l2m_valid_def l2m_def)
    next
    case False
      from Cons(2) have "l2m_valid l2m rec f" by (simp add: l2m_valid_def)
      from Cons(1)[OF this] Cons(3) False akvs kkk show ?thesis by (simp add: l2m_def)
    qed
  qed
}
then have l2m_valid: "\<forall>M f. l2m_valid l2m M f \<longrightarrow> valid l2m M f" by (auto simp: valid_def)
with l2m_empty l2m_store show ?thesis unfolding satisfactory_def by fast
qed

(**
    An approx_tree is a binary search tree whose nodes are labelled by
    approximations (elements of approx's codomain) and whose leaves
    contain memories to disambiguate between keys that have the same
    approximation.
    The main idea is to use an approximation that maps to a set where
    comparison is easy (e.g. Int32 or Int64 are good candidates).
**)

datatype ('a,'m)"approx_tree" =
    Leaf 'a 'm
  | Node 'a "('a,'m)approx_tree" "('a, 'm)approx_tree"

definition atm_empty :: "('m, 'k, 'v)memory \<Rightarrow> 'a \<Rightarrow> unit \<Rightarrow> ('a, 'm)approx_tree" where
  "atm_empty model def _ \<equiv> Leaf def (memory.empty model ())"

fun atm_store_rec :: "('m, 'k, 'v)memory \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comparison) \<Rightarrow>
  ('a,'m)approx_tree \<Rightarrow> 'a \<Rightarrow> ('k \<times> 'v) \<Rightarrow> ('a,'m)approx_tree" where
  "atm_store_rec model cmp (Leaf a1 M) a2 kv =
     (case cmp a1 a2 of
        Less  \<Rightarrow> Node a1 (Leaf a1 M) (Leaf a2 (singleton model kv))
      | Equal \<Rightarrow> Leaf a1 (memory.store model M kv)
      | More  \<Rightarrow> Node a2 (Leaf a2 (singleton model kv)) (Leaf a1 M))" |
  "atm_store_rec model cmp (Node a1 AT1 AT2) a2 kv =
     (case cmp a1 a2 of
        Less  \<Rightarrow> Node a1 AT1 (atm_store_rec model cmp AT2 a2 kv)
      | _     \<Rightarrow> Node a1 (atm_store_rec model cmp AT1 a2 kv) AT2)"

definition atm_store :: "('m, 'k, 'v)memory \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comparison) \<Rightarrow>
  ('a,'m)approx_tree \<Rightarrow> ('k \<times> 'v) \<Rightarrow> ('a, 'm)approx_tree" where
  "atm_store model approx cmp M kv \<equiv> atm_store_rec model cmp M (approx (fst kv)) kv"

fun atm_lookup_rec :: "('m, 'k, 'v)memory \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comparison) \<Rightarrow>
  ('a,'m)approx_tree \<Rightarrow> 'a \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "atm_lookup_rec model cmp (Leaf a1 M) a2 k =
     (case cmp a1 a2 of
        Equal \<Rightarrow> memory.lookup model M k
      | _     \<Rightarrow> None)" |
  "atm_lookup_rec model cmp (Node a1 AT1 AT2) a2 k =
     (case cmp a1 a2 of
        Less \<Rightarrow> atm_lookup_rec model cmp AT2 a2 k
      | _    \<Rightarrow> atm_lookup_rec model cmp AT1 a2 k)"

definition atm_lookup :: "('m, 'k, 'v)memory \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comparison) \<Rightarrow>
  ('a, 'm)approx_tree \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "atm_lookup model approx cmp M k \<equiv> atm_lookup_rec model cmp M (approx k) k"

definition atm :: "('m, 'k, 'v)memory \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> comparison) \<Rightarrow> 'a \<Rightarrow>
  (('a, 'm)approx_tree,'k,'v)memory"
  where "atm model approx cmp df \<equiv> \<lparr> empty = atm_empty model df,
  lookup = atm_lookup model approx cmp , store = atm_store model approx cmp \<rparr>"

fun atm_valid :: "('m, 'k, 'v)memory \<Rightarrow> (('m, 'k, 'v)memory \<Rightarrow> 'm \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> bool) \<Rightarrow>
  ('a, 'm) approx_tree \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> bool" where
  "atm_valid model model_P (Leaf a kvs) f = (model_P model kvs f)" |
  "atm_valid model model_P (Node a lst rst) f = (
   (atm_valid model model_P lst f) \<and> (atm_valid model model_P rst f))"

locale approximation_tree =
  fixes model :: "('m, 'k, 'v)memory"
  fixes model_P :: "('m, 'k, 'v)memory \<Rightarrow> 'm \<Rightarrow> ('k \<Rightarrow> 'v) \<Rightarrow> bool"
  fixes approx :: "'k \<Rightarrow> 'a"
  fixes comp :: "'a \<Rightarrow> 'a \<Rightarrow> comparison"
  fixes default :: "'a"
  assumes comp_eq: "\<forall> h i. (comp h i = Equal) = (h = i)"
  and comp_lt_gt: "\<forall> h i. (comp h i = Less) = (comp i h = More)"
  and model_satisfactory: "satisfactory model_P model"
begin

(**
    We now define the validity predicate on approximation trees. It is a bit
    complicated because it states that the tree is well-formed and that the
    values are correct.
**)

definition atm_inst where "atm_inst = atm model approx comp default"

lemma satisfactory_atm: "satisfactory (\<lambda>_. atm_valid model model_P) atm_inst"
proof-
from model_satisfactory[unfolded satisfactory_def]
 have atm_empty: "\<forall> f. atm_valid model model_P (memory.empty atm_inst ()) f"
 by (simp add: atm_inst_def atm_def atm_empty_def)
{
  fix M :: "('a, 'm)approx_tree" and f ak k
  assume M_valid: "atm_valid model model_P M f"
  then have "atm_valid model model_P (atm_store_rec model comp M ak (k, f k)) f"
  proof (induct M)
  case (Leaf a kvs)
    then show ?case
    proof (cases "comp a ak")
    case Equal note Haak = this
      then show ?thesis
       using Leaf model_satisfactory[unfolded satisfactory_def]
       by simp
    next
    case Less note Haak = this
      then show ?thesis
       using Leaf comp_eq comp_lt_gt[rule_format, of a ak]
       singleton_valid[OF model_satisfactory, of f k "f k"]
       by simp
    next
    case More note Haak = this
      then show ?thesis
       using Leaf comp_eq singleton_valid[OF model_satisfactory, of f k "f k"]
       by simp
    qed
  next
  case (Node a lst rst) then show ?case by (cases "comp a ak") auto
  qed
}
then have atm_store: "\<forall>f a M. atm_valid model model_P M f \<longrightarrow>
   atm_valid model model_P (memory.store atm_inst M (a, f a)) f"
 by (auto simp: atm_inst_def atm_def atm_store_def)
{
  fix M f ak k v
  assume "atm_valid model model_P M f"
  and "atm_lookup_rec model comp M ak k = Some v"
  then have "f k = v"
  proof (induct M)
  case (Leaf a kvs)
    show ?case
    proof (cases "comp a ak = Equal")
    case True
      with Leaf model_satisfactory[unfolded satisfactory_def valid_def]
       show ?thesis by auto
    next
    case False
      with Leaf(2) show ?thesis by (cases "comp a ak") auto
    qed
  next
  case (Node a lst rst) then show ?case by (cases "comp a ak") auto
  qed
}
then have atm_valid: "\<forall>f M. atm_valid model model_P M f \<longrightarrow> valid atm_inst M f"
 by (simp add: atm_inst_def atm_def valid_def atm_lookup_def)
from atm_empty atm_store atm_valid show ?thesis by simp
qed

end

(*hide constructors (e.g., More is already used for contexts)*)
hide_const (open) More Less Equal

end
