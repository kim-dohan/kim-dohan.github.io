theory Tree_Automata_Det_Container
imports
  Tree_Automata_Det_Impl
  Containers.Containers
  "Transitive-Closure.Transitive_Closure_List_Impl"
begin

definition memo_list_rtrancl_set :: "('a \<times> 'a) list \<Rightarrow> ('a \<Rightarrow> 'a set)"
where
  "memo_list_rtrancl_set r \<equiv>
    let
      tr = rtrancl_list_impl r;
      rm = map_of (map (\<lambda>a. (a, set (tr [a]))) ((remdups \<circ> map fst) r))
    in
    (\<lambda>a. case rm a of None \<Rightarrow> {a} | Some as \<Rightarrow> as)"

lemma memo_list_rtrancl_set:
  "memo_list_rtrancl_set r a = {b. (a, b) \<in> (set r)\<^sup>*}" (is "?l = ?r")
unfolding memo_list_rtrancl[symmetric] memo_list_rtrancl_def memo_list_rtrancl_set_def Let_def
by (auto split: option.splits simp: map_of_eq_None_iff image_iff dest!: map_of_SomeD)

lemma memo_rtrancl_code [code]:
  fixes dxs :: "('a :: ceq \<times> 'a) set_dlist"
  and rbt :: "('b :: ccompare \<times> 'b) set_rbt"
  shows
  "memo_rtrancl (Set_Monad xs) = memo_list_rtrancl_set xs"
  (is "?monad")                      
  "memo_rtrancl (DList_set dxs) =
  (case ID CEQ('a) of None \<Rightarrow> Code.abort (STR ''memo_rtrancl DList_set: ceq = None'') (\<lambda>_. memo_rtrancl (DList_set dxs))
                  | Some _ \<Rightarrow> memo_list_rtrancl_set (list_of_dlist dxs))"
  (is "?dlist")
  "memo_rtrancl (RBT_set rbt) =
  (case ID CCOMPARE('b) of None \<Rightarrow> Code.abort (STR ''memo_rtrancl RBT_set: ccompare = None'') (\<lambda>_. memo_rtrancl (RBT_set rbt))
                     | Some _ \<Rightarrow> memo_list_rtrancl_set (RBT_Set2.keys rbt))"
  (is "?rbt")
proof -
  show ?monad by (simp add: fun_eq_iff memo_rtrancl_def memo_list_rtrancl_set)
  show ?dlist by (auto split: option.split simp: ceq_prod_def ID_Some Collect_member
      set_list_of_dlist_Abs_dlist DList_set_def memo_rtrancl_def memo_list_rtrancl_set)
  show ?rbt by
    (auto split: option.split simp:  RBT_set_def fun_eq_iff memo_list_rtrancl_set memo_rtrancl_def)
    (auto simp: ID_Some  ccompare_prod_def RBT_set_conv_keys[unfolded RBT_set_def comp_def])
qed

end
