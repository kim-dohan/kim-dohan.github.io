text \<open>This theory shows that the axioms of the memory model in LLVM-Memory-Axioms are satisfiable, 
  by providing a concrete implementation.\<close>

theory Memory_Model_Impl
  imports LLVM_Memory_Axioms
begin


subsection \<open>Internal construction of memory model\<close>

text \<open>We use explicit invariants and also store implicit data, e.g., 
  the set of used addresses.\<close>

fun len_of :: "llvm_type \<Rightarrow> nat" where
  "len_of (IntType bits) = ((max 1 bits) + 7) div 8" \<comment> \<open>byte-wise alignment\<close>
| "len_of (PointerType ty) = 64" \<comment> \<open>arbitrary chosen value\<close>

lemma len_of[simp]: "len_of ty > 0" "int (len_of ty) > 0" "len_of ty \<noteq> 0" 
  by (cases ty, auto)+

type_synonym mem_internal = "int \<times> \<comment> \<open>next free adress\<close>
  int set \<times>   \<comment> \<open>reserved addresses\<close>
  (int \<times> int) set \<times> \<comment> \<open>reserved bounds\<close>
  (int \<Rightarrow> (int \<times> int) option) \<times> \<comment> \<open>bounds\<close>
  (int \<Rightarrow> stack_value option) \<comment> \<open>memory\<close>" 

definition addresses :: "int \<Rightarrow> int \<Rightarrow> int set" where
  "addresses lb ub = {lb ..< ub}" 

fun mem_invariant :: "mem_internal \<Rightarrow> bool" where
  "mem_invariant (c, A, Bs, B, f) = (
  c > 0 \<and> 
  (\<forall> a \<in> A. a < c) \<and> 
  (\<forall> lb ub. (lb,ub) \<in> Bs \<longrightarrow> lb < ub \<and> ub \<le> c \<and> addresses lb ub \<subseteq> A) \<and>
  (\<forall> a lb ub. B a = Some (lb,ub) \<longrightarrow> (lb,ub) \<in> Bs \<and> lb \<le> a \<and> a < ub) \<and>
  (\<forall> a. a \<notin> A \<longrightarrow> f a = None) \<and>
  True)" 

definition empty_mem_internal :: mem_internal where
  "empty_mem_internal = (1, {}, {}, \<lambda> _. None, \<lambda> _. None)" 

lemma empty_mem_internal[simp]: "mem_invariant (empty_mem_internal)"
  unfolding empty_mem_internal_def by auto


fun alloc_internal :: "mem_internal \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + (int \<times> int) \<times> mem_internal" where
  "alloc_internal (c, A, Bs, B, f) ty n = (if n \<le> 0 then Inl Undefined_Behaviour
      else let c' = c + int (len_of ty) * n 
        in Inr ((c, c'), 
          (c', A \<union> addresses c c', 
          Bs \<union> {(c,c')}, 
          \<lambda> a. if c \<le> a \<and> a < c' then Some (c,c') else B a, 
          f)))"

lemma alloc_internal: "mem_invariant m \<Longrightarrow> alloc_internal m ty n = Inr (b,m') \<Longrightarrow> mem_invariant m'"
proof (cases m, goal_cases)
  case (1 c A Bs B f)
  note m = 1(3)
  note assms = 1(1-2)[unfolded m, simplified]
  define c' where "c' = c + int (len_of ty) * n" 
  from assms have n: "n > 0" by (cases "n \<le> 0", auto)
  hence "(n \<le> 0) = False" by simp
  note assms = assms[unfolded this, folded c'_def, simplified]  
  hence m': "m' = (c', A \<union> addresses c c', insert (c, c') Bs, \<lambda>a. if c \<le> a \<and> a < c' then Some (c, c') else B a, f)" 
    by auto
  from n len_of[of ty] have "int (len_of ty) * n > 0" by auto
  with assms have c: "c' > 0" "c' > c" unfolding c'_def by linarith+
  have addr: "a \<in> addresses c c' \<Longrightarrow> a < c'" for a unfolding addresses_def by auto
  show ?thesis using assms(1) c unfolding m' by (auto, metis addr, force)
qed

lemma alloc_internal_ok: "0 < l \<Longrightarrow> isOK (alloc_internal m t l)" 
  by (cases m, auto) 

lemma alloc_internal_bounds1: "alloc_internal m t l = Inr ((lb, ub), m') \<Longrightarrow> ub - lb = int (len_of t) * l" 
  by (cases m, auto simp add: Let_def split: if_splits)

fun bounds_internal :: "mem_internal \<Rightarrow> int \<Rightarrow> (int \<times> int) option" where
  "bounds_internal (_, _, _, B, _) = B" 

lemma alloc_internal_bounds2: "alloc_internal m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<in> {lb..<ub} \<Longrightarrow> 
  bounds_internal m' a = Some (lb, ub)" 
  by (cases m, auto simp add: Let_def split: if_splits)


lemma alloc_internal_bounds3: "alloc_internal m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} 
  \<Longrightarrow> bounds_internal m' a = bounds_internal m a"
  by (cases m, auto simp add: Let_def split: if_splits)

lemma alloc_internal_bounds4: assumes "mem_invariant m"
  "alloc_internal m t n = Inr ((lb, ub), m')" 
  "a \<in> {lb..<ub}"
shows "bounds_internal m a = None" 
proof (cases m)
  case (fields c A Bs B f)
  note assms = assms[unfolded fields, simplified, unfolded Let_def]
  from assms have "(n \<le> 0) = False" by auto
  note assms = assms[unfolded this if_False, simplified]
  from assms have "c \<le> a" by simp
  {
    assume "bounds_internal m a \<noteq> None" 
    then obtain lb' ub' where "bounds_internal m a = Some (lb', ub')" by force
    with fields have "B a = Some (lb', ub')" by auto
    with assms have *: "(lb', ub') \<in> Bs" "a < ub'" by auto
    with assms have "ub' \<le> c" by auto
    with * have "a < c" by auto
    with \<open>c \<le> a\<close> have False by auto
  }
  thus ?thesis by blast
qed

fun store_internal :: "mem_internal \<Rightarrow> int \<Rightarrow> llvm_type \<Rightarrow> stack_value \<Rightarrow> stuck + mem_internal" where
  "store_internal (c, A, Bs, B, f) a ty v = (case B a
     of Some (lb, ub) \<Rightarrow> if lb \<le> a \<and> a + len_of ty \<le> ub then 
         Inr (c, A, Bs, B, f(a := Some v)) 
      else Inl Undefined_Behaviour
      | None \<Rightarrow> Inl Undefined_Behaviour)" 

lemma store_internal: "mem_invariant m \<Longrightarrow> store_internal m a ty v = Inr m' \<Longrightarrow> mem_invariant m'"
proof (goal_cases)
  case 1
  obtain c A Bs B f where m: "m = (c,A,Bs,B,f)" by (cases m, auto)
  from 1 m obtain lb ub where B: "B a = Some (lb, ub)" by (cases "B a", auto)
  note 1 = 1[unfolded m, simplified, unfolded B, simplified]
  from 1 have *: "(lb \<le> a \<and> a + int (len_of ty) \<le> ub) = True" by (auto split: if_splits)
  note 1 = 1[unfolded this, simplified]
  from 1 have m': "m' = (c, A, Bs, B, f(a \<mapsto> v))" by simp
  from * len_of[of ty] have "a \<in> addresses lb ub"
    unfolding addresses_def by (smt atLeastLessThan_iff)
  with 1(1) B have "a \<in> A" by force
  with 1(1) show ?case unfolding m' by auto
qed

fun load_internal :: "mem_internal \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + stack_value" where
  "load_internal (c, A, Bs, B, f) ty a = (case f a of None \<Rightarrow> Inl Undefined_Behaviour
    | Some v \<Rightarrow> Inr v)" 

lemma alloc_load_internal: "alloc_internal m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} \<Longrightarrow> load_internal m' t' a = load_internal m t' a"
  by (cases m, auto split: if_splits simp add: Let_def)

lemma store_load_internal1: "mem_invariant m \<Longrightarrow> store_internal m a t v = Inr m' \<Longrightarrow>
       a' + int (len_of t') \<le> a \<or> a + int (len_of t) \<le> a' \<Longrightarrow>
       load_internal m' t' a' = load_internal m t' a'" 
proof (cases m, goal_cases)
  case (1 c A Bs B f)
  note m = 1(4)
  note assms = 1(1-3)[unfolded m, simplified]
  from assms obtain lb ub where B: "B a = Some (lb, ub)"
    by (auto split: option.splits)
  note assms = assms[unfolded B, simplified]
  from assms have *: "(lb \<le> a \<and> a + int (len_of t) \<le> ub) = True" by (auto split: if_splits)
  note assms = assms[unfolded *, simplified]
  hence m': "m' = (c, A, Bs, B, f(a \<mapsto> v))" by auto
  show ?case unfolding m m' using B * assms(1,3) 
    by (cases "f a", auto)
qed
  

lemma store_load_internal2: "store_internal m a t v = Inr m' \<Longrightarrow> load_internal m' t a = Inr v" 
  by (cases m, auto split: if_splits option.splits)

lemma bounds_internal_store1: "mem_invariant m \<Longrightarrow> bounds_internal m a = Some (lb, ub) \<Longrightarrow>
       lb \<le> a \<Longrightarrow> a + int (len_of t) \<le> ub \<Longrightarrow> \<exists>m'. store_internal m a t v = Inr m'"
  by (cases m, auto)

lemma bounds_internal_store2: "store_internal m a t v = Inr m' \<Longrightarrow> bounds_internal m' = bounds_internal m"
  by (cases m, auto split: option.splits if_splits)

subsection \<open>Internal executable construction of memory model\<close>

text \<open>We still use explicit invariants, but now distinguish between the
  executable parts and those parts that are just extra informations.\<close>

type_synonym mem_explicit = "int \<times> \<comment> \<open>next free adress\<close>
  (int \<Rightarrow> (int \<times> int) option) \<times> \<comment> \<open>bounds\<close>
  (int \<Rightarrow> stack_value option) \<comment> \<open>memory\<close>" 
 
fun project_mem :: "mem_internal \<Rightarrow> mem_explicit" where
  "project_mem (c, A, Bs, B, f) = (c, B, f)" 

definition empty_mem_exp :: mem_explicit where
  "empty_mem_exp = (1, \<lambda> _. None, \<lambda> _. None)" 

lemma empty_mem_exp[simp]: 
  "empty_mem_exp = project_mem empty_mem_internal"
  unfolding empty_mem_exp_def empty_mem_internal_def by simp


fun alloc_exp :: "mem_explicit \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + (int \<times> int) \<times> mem_explicit" where
  "alloc_exp (c, B, f) ty n = (if n \<le> 0 then Inl Undefined_Behaviour
      else let c' = c + int (len_of ty) * n 
        in Inr ((c, c'), 
          (c',  
          \<lambda> a. if c \<le> a \<and> a < c' then Some (c,c') else B a, 
          f)))"

lemma alloc_exp[simp]: "alloc_exp (project_mem m) ty n = map_sum id (map_prod id project_mem) (alloc_internal m ty n)" 
  by (cases m, auto simp: Let_def)

fun store_exp :: "mem_explicit \<Rightarrow> int \<Rightarrow> llvm_type \<Rightarrow> stack_value \<Rightarrow> stuck + mem_explicit" where
  "store_exp (c, B, f) a ty v = (case B a
     of Some (lb, ub) \<Rightarrow> if lb \<le> a \<and> a + len_of ty \<le> ub then 
         Inr (c, B, f(a := Some v)) 
      else Inl Undefined_Behaviour
      | None \<Rightarrow> Inl Undefined_Behaviour)" 

lemma store_exp[simp]: "store_exp (project_mem m) a ty n = map_sum id project_mem (store_internal m a ty n)" 
  by (cases m, auto split: option.splits)

fun load_exp :: "mem_explicit \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + stack_value" where
  "load_exp (c, B, f) ty a = (case f a of None \<Rightarrow> Inl Undefined_Behaviour
    | Some v \<Rightarrow> Inr v)" 

lemma load_exp[simp]: "load_exp (project_mem m) ty l = load_internal m ty l" 
  by (cases m, auto split: option.splits)


fun bounds_exp :: "mem_explicit \<Rightarrow> int \<Rightarrow> (int \<times> int) option" where
  "bounds_exp (_, B, _) = B" 

lemma bounds_exp[simp]: "bounds_exp (project_mem m) = bounds_internal m" 
  by (cases m, auto)

declare alloc_internal.simps[simp del]
declare store_internal.simps[simp del]
declare load_internal.simps[simp del]
declare mem_invariant.simps[simp del]


subsection \<open>Dedicated type for memory where invariant is integrated.\<close>

typedef mem = "{ project_mem m | m. mem_invariant m}"
  by (intro exI[of _ empty_mem_exp] CollectI exI[of _ empty_mem_internal], auto)

setup_lifting type_definition_mem

lift_definition empty_mem :: mem is empty_mem_exp
  by (intro exI[of _ empty_mem_internal], auto)

lift_definition alloc :: "mem \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + (int \<times> int) \<times> mem" is alloc_exp
proof (elim exE, goal_cases)
  case (1 p ty n m)
  thus ?case using alloc_internal[of m ty n] alloc_exp[of m ty n]
    by (cases "alloc_internal m ty n", force+)
qed

lift_definition store :: "mem \<Rightarrow> int \<Rightarrow> llvm_type \<Rightarrow> stack_value \<Rightarrow> stuck + mem" is store_exp
proof (elim exE, goal_cases)
  case (1 p a ty v m)
  thus ?case using store_internal[of m a ty v]
    by (cases "store_internal m a ty v", force+)
qed

lift_definition bounds :: "mem \<Rightarrow> int \<Rightarrow> (int \<times> int)option" is bounds_exp .

lift_definition load :: "mem \<Rightarrow> llvm_type \<Rightarrow> int \<Rightarrow> stuck + stack_value" is load_exp .

lemma rel_fun_isOK[transfer_rule]: "rel_fun (rel_sum A B) (=) isOK isOK"
proof (simp add: rel_fun_def, clarsimp)
  show "rel_sum A B x y \<Longrightarrow> isOK x = isOK y" for x y
    by (induct x y rule: rel_sum.induct, auto)
qed

lemma alloc_ok: "0 < l \<Longrightarrow> isOK (alloc m t l)" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 l p t m)
  thus ?case using alloc_internal_ok[of l m t] alloc_exp[of m t l] by auto
qed

lemma alloc_bounds1: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> ub - lb = int (len_of t) * l" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 p t l lb ub p' m m')
  from 1(1) obtain m' where "alloc_internal m t l = Inr ((lb, ub), m')" 
    unfolding 1(2) alloc_exp by (cases "alloc_internal m t l", auto)
  from alloc_internal_bounds1[OF this] show ?case .
qed

lemma alloc_bounds2: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<in> {lb..<ub} \<Longrightarrow> 
  bounds m' a = Some (lb, ub)" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 p t l lb ub p' a m m')
  from 1(1) obtain m'' where "alloc_internal m t l = Inr ((lb, ub), m'')" "p' = project_mem m''"  
    unfolding 1(3) alloc_exp by (cases "alloc_internal m t l", auto)
  from alloc_internal_bounds2[OF this(1) 1(2)] this(2) show ?case by simp
qed

lemma alloc_bounds3: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} \<Longrightarrow> bounds m' a = bounds m a"
proof (transfer, elim exE conjE, goal_cases)
  case (1 p t l lb ub p' a m m')
  from 1(1) obtain m'' where "alloc_internal m t l = Inr ((lb, ub), m'')" "p' = project_mem m''"  
    unfolding 1(3) alloc_exp by (cases "alloc_internal m t l", auto)
  from alloc_internal_bounds3[OF this(1) 1(2)] this(2) 1(3) show ?case by simp
qed

lemma alloc_bounds4: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<in> {lb..<ub} \<Longrightarrow> bounds m a = None"
proof (transfer, elim exE conjE, goal_cases)
  case (1 p t l lb ub p' a m m')
  from 1(1) obtain m'' where "alloc_internal m t l = Inr ((lb, ub), m'')" "p' = project_mem m''"  
    unfolding 1(3) alloc_exp by (cases "alloc_internal m t l", auto)
  from alloc_internal_bounds4[OF 1(4) this(1) 1(2)] this(2) 1(3) show ?case by simp
qed

lemma bounds_store1: "bounds m a = Some (lb, ub) \<Longrightarrow>
       lb \<le> a \<Longrightarrow> a + int (len_of t) \<le> ub \<Longrightarrow> \<exists>m'. store m a t v = Inr m'"
proof (transfer, elim exE conjE, goal_cases)
  case (1 p a lb ub ty v m)
  from bounds_internal_store1[OF 1(5) 1(1)[unfolded 1(4) bounds_exp] 1(2-3), of v]
  show ?case unfolding 1(4) store_exp using store_internal[of m a ty v, OF 1(5)]
    by force
qed

lemma bounds_store2: "store m a t v = Inr m' \<Longrightarrow> bounds m' = bounds m" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 p a t v p' m m')
  from 1(1) obtain m'' where *: "store_internal m a t v = Inr m''" "p' = project_mem m''"  
    unfolding 1(2) store_exp by (cases "store_internal m a t v", auto)
  from bounds_internal_store2[OF this(1)] show ?case unfolding 1(2) *(2) bounds_exp .
qed

lemma alloc_load: "alloc m t l = Inr ((lb, ub), m') \<Longrightarrow> a \<notin> {lb..<ub} \<Longrightarrow> load m' t' a = load m t' a"
proof (transfer, elim exE conjE, goal_cases)
  case (1 p t l lb ub p' a ty m m')
  from 1(1) obtain m'' where *: "alloc_internal m t l = Inr ((lb, ub), m'')" "p' = project_mem m''"  
    unfolding 1(3) alloc_exp by (cases "alloc_internal m t l", auto)
  from alloc_load_internal[OF this(1) 1(2), of ty]
  show ?case unfolding load_exp *(2) 1(3) .
qed

lemma store_load1: "store m a t v = Inr m' \<Longrightarrow>
       a' + int (len_of t') \<le> a \<or> a + int (len_of t) \<le> a' \<Longrightarrow>
       load m' t' a' = load m t' a'" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 p a t v p' a' t' m m')
  from 1(1) obtain m'' where *: "store_internal m a t v = Inr m''" "p' = project_mem m''"  
    unfolding 1(3) store_exp by (cases "store_internal m a t v", auto)
  from store_load_internal1[OF 1(4) *(1) 1(2)]
  show ?case unfolding 1(3) *(2) load_exp .
qed

lemma store_load2: "store m a t v = Inr m' \<Longrightarrow> load m' t a = Inr v" 
proof (transfer, elim exE conjE, goal_cases)
  case (1 p a t v p' m m')
  from 1(1) obtain m'' where *: "store_internal m a t v = Inr m''" "p' = project_mem m''"  
    unfolding 1(2) store_exp by (cases "store_internal m a t v", auto)
  from store_load_internal2[OF *(1)]
  show ?case unfolding *(2) load_exp .
qed


interpretation ll_mem alloc store load empty_mem len_of bounds
proof (unfold_locales, goal_cases)
  case 1 
  show ?case by (rule len_of)
next
  case 2
  thus ?case by (rule alloc_ok)
next
  case 3
  thus ?case by (rule alloc_bounds1)
next
  case 4
  thus ?case by (rule alloc_load)
next
  case 5
  thus ?case by (rule alloc_bounds2)
next
  case 6
  thus ?case by (rule alloc_bounds3)
next
  case 7
  thus ?case by (rule alloc_bounds4)
next
  case 8
  thus ?case by (rule bounds_store1)
next
  case 9
  thus ?case by (rule bounds_store2)
next
  case 10
  thus ?case by (rule store_load1)
next
  case 11
  thus ?case by (rule store_load2)
qed
end