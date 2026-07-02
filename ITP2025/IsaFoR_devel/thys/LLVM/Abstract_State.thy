theory Abstract_State
  imports
  "LTS.IA_Instance"
begin

(*
  p = position,
  pv = program variable
  lv = logical variable
   n = node identifier
*)

datatype ('p,'pv,'lv,'type) abstract_state =
  As (pos : 'p)
     (stack : "'pv \<rightharpoonup> ('type \<times> 'lv IA.exp)")
     (kb : "'lv IA.formula")
     (allocs : "('lv \<times> 'lv) set")
     (pointers : "'lv \<rightharpoonup> ('type \<times> 'lv IA.exp)")
     (inits: "('lv \<times> 'lv \<times> 'type) set")

definition all_sym_vars :: "_ \<Rightarrow> 'lv set" where
  "all_sym_vars as = (\<Union>x \<in> ran (stack as). fst ` vars_term (snd x))
                     \<union> fst ` vars_formula (kb as)
                     \<union> fst ` allocs as
                     \<union> snd ` allocs as
                     \<union> dom (pointers as)
                     \<union> (\<Union>x \<in> ran (pointers as). fst ` vars_term (snd x))
                     \<union> fst ` inits as
                     \<union> fst ` snd ` inits as"

inductive as_as_step ::
  "('p, 'pv, 'lv, 'type) abstract_state
   \<Rightarrow> ('p, 'pv, 'lv, 'type) abstract_state
   \<Rightarrow> ('lv \<times> IA.ty \<Rightarrow> IA.val)
   \<Rightarrow> ('lv \<times> IA.ty \<Rightarrow> IA.val)
   \<Rightarrow> ('lv \<Rightarrow> 'lv)
   \<Rightarrow> bool"
  where
    "as_as_step as\<^sub>1 as\<^sub>2 v\<^sub>1 v\<^sub>2 \<mu>"
  if
    "IA.assignment v\<^sub>1"
    "IA.assignment v\<^sub>1'"
    "IA.assignment v\<^sub>2"
    "\<forall>lv \<in> all_sym_vars as\<^sub>1. \<forall>ty. v\<^sub>1 (lv,ty) = v\<^sub>1' (lv,ty)"
    "\<forall>lv ty. v\<^sub>2 (lv,ty) = v\<^sub>1' (\<mu> lv,ty)"
    "IA.satisfies v\<^sub>1' (kb as\<^sub>1)"
    "IA.satisfies v\<^sub>2 (kb as\<^sub>2)"

end