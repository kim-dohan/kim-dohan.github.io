(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Status_Impl
imports
  Weighted_Path_Order.Status
  Auxx.Map_Choice
begin
type_synonym 'f status_impl = "(('f \<times> nat) \<times> nat list)list"

lift_definition (code_dt) status_of :: "'f status_impl \<Rightarrow> 'f status option" is
  "\<lambda> s. if (\<forall> fidx \<in> set s. (\<forall> i \<in> set (snd fidx). i < snd (fst fidx)))
     then Some (fun_of_map_fun (map_of s) (\<lambda> (f,n). [0 ..< n])) else None"    
  using map_of_SomeD by (fastforce split: option.splits)

lemma status_of_Some: "status_of s = Some \<sigma> 
  \<Longrightarrow> status \<sigma> = (fun_of_map_fun (map_of s) (\<lambda> (f,n). [0 ..< n]))"
  using status_of.rep_eq[of s]
  by (transfer, auto split: if_splits)

lemma status_of_default: assumes s: "status_of s = Some \<sigma>"
  and f: "(f,n) \<notin> fst ` set s"
  shows "status \<sigma> (f,n) = [0 ..< n]"
proof -
  from map_of_eq_None_iff[of s "(f,n)"] f have "map_of s (f,n) = None" by simp
  then show ?thesis unfolding status_of_Some[OF s] by simp
qed
end
