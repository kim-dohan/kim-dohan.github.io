theory Inference_Rules_Exec
  imports
    Inference_Rules
  "HOL-ex.Sketch_and_Explore"
begin

lemma dvd_lia:
  fixes x y :: int
  assumes "y > 0" 
  shows  "y dvd x \<longleftrightarrow> (\<forall>q r. q * y + r = x \<and> r \<in> {0..<y} \<longrightarrow> r = 0)"
proof -
  have a: "r = 0" if "y dvd x" "q * y + r = x" "r \<in> {0..<y}"  for q r
  proof -
    have a: "y dvd r" 
      using assms that by (auto)
    show ?thesis
      using dvd_imp_le_int[OF _ a] that by auto
  qed
  have b: "y dvd x" if " (\<forall>q r. q * y + r = x \<and> r \<in> {0..<y} \<longrightarrow> r = 0)"
  proof -
    define r where "r = x mod y"
    define k where "k = x div y"
    have a: "k * y + r = x"
      unfolding r_def k_def by auto
    have b: "0 \<le> r \<and> r < y"
      unfolding r_def using that assms abs_mod_less by auto
    have r: "r = 0"
      using a b that by auto
    show ?thesis
      using a unfolding r by auto
  qed
  show ?thesis
    using a b by blast
qed

lemma dvd_liay:
  fixes x y :: int
  assumes "y > 0" "\<And>q r. q * y + r = x \<and> r \<in> {0..<y} \<longrightarrow> r = 0"
  shows  "y dvd x"
  using dvd_lia assms by blast

definition encode_dvd where
  "encode_dvd v i q =
  encode_eq (Fun (IA.ProdF 2) [encode_int_var q, encode_int_const i]) (encode_int_var v)
 "

lemma assumes "IA.satisfies e (encode_dvd v i q)" "IA.assignment e"
  shows "i dvd IA.to_int (e (v,IA.IntT))"
proof -
  show ?thesis
    using assms apply(auto simp add: encode_dvd_def)
    by (metis dvd_triv_right)

unbundle IA_formula_notation

thm list_ex_iff Bex_set

lift_definition "values" :: "('a, 'b) mapping \<Rightarrow> 'b set"
  is ran .

lift_definition "set_of_mapping" :: "('a, 'b) mapping \<Rightarrow> ('a \<times>'b) set"
  is set_of_map .

lift_definition "mapping_subset" :: "('a, 'b) mapping \<Rightarrow> ('a, 'b) mapping \<Rightarrow> bool"
  is map_le .

lemma mapping_values[code]: "values m = (the \<circ> Mapping.lookup m) ` Mapping.keys m"
  by (transfer) (meson ran_is_image)

lemma set_of_mapping[code]:
  "set_of_mapping m = (\<lambda>k. (k, the (Mapping.lookup m k))) ` Mapping.keys m"
  by (transfer) (auto simp add: set_of_map_def)

lemma Mapping_to_set: "(k,v) \<in> set_of_mapping m \<longleftrightarrow> Mapping.lookup m k = Some v"
  unfolding set_of_mapping by (auto simp add: domIff keys_dom_lookup image_def)

lemma Mapping_values_ran: "values m = ran (Mapping.lookup m)"
  by (transfer) (simp add: ran_alt_def)

lemma Mapping_filter:
  "Mapping.lookup (Mapping.filter P m) x = Some y \<Longrightarrow> Mapping.lookup m x = Some y"
  "Mapping.lookup m x = None \<Longrightarrow> Mapping.lookup (Mapping.filter P m) x = None"
  by (transfer, auto split: option.splits if_splits)+

datatype ('p,'pv,'lv,'type) abstract_state_impl =
  As_Impl
  (pos : 'p)
  (stack : "('pv, ('type \<times> 'lv)) mapping")
  (kb : "'lv IA.formula")
  (allocs : "('lv \<times> 'lv) set")
  (pointers : "('lv, ('type \<times> 'lv)) mapping")

lemma mapping_subset[code]:
  "mapping_subset m m' =(\<forall>x \<in> Mapping.keys m. Mapping.lookup m x = Mapping.lookup m' x)"
  by (transfer) (auto simp add: map_le_def)

lemma Mapping_subset:
  assumes "mapping_subset m m'"
  shows "Mapping.lookup m y = Some x \<Longrightarrow> Mapping.lookup m' y = Some x"
      "Mapping.lookup m' y = None \<Longrightarrow> Mapping.lookup m y = None"
  using assms is_none_code Option.is_none_def keys_is_none_rep unfolding mapping_subset
  by (metis)+

definition all_sym_vars :: "_ \<Rightarrow> 'lv set" where
  "all_sym_vars as = snd ` values (stack as) \<union> fst ` vars_formula (kb as)
                     \<union> fst ` allocs as \<union> snd ` allocs as \<union>
                     Mapping.keys (pointers as) \<union> snd ` values (pointers as)"

definition of_as_impl where
  "of_as_impl asi =
    As (pos asi) (Mapping.lookup (stack asi)) (kb asi) (allocs asi) (Mapping.lookup (pointers asi))"

lemma of_as_impl_simps[simp]:
  "abstract_state.stack (of_as_impl x) = Mapping.lookup (stack x)"
  "abstract_state.kb (of_as_impl x) = kb x"
  "abstract_state.pos (of_as_impl x) = pos x"
  "abstract_state.allocs (of_as_impl x) = allocs x"
  "abstract_state.pointers (of_as_impl x) = Mapping.lookup (pointers x)"
  by (cases x, auto simp add: of_as_impl_def)+

lemma asm_all_sym_vars_simps[simp]: "Abstract_State.all_sym_vars (of_as_impl x) = all_sym_vars x"
  by(auto simp add: keys_is_none_rep all_sym_vars_def Abstract_State.all_sym_vars_def Mapping_values_ran)

lemma Mapping_values:  "(x \<in> values m) \<longleftrightarrow> (\<exists>n. Mapping.lookup m n = Some x)"
proof -
  have "\<exists>n. Mapping.lookup m n = Some x" if a: "x \<in> values m"
  proof -
    obtain n where "n \<in> Mapping.keys m" "x = the (Mapping.lookup m n)"
      using a unfolding mapping_values by auto
    then have "Mapping.lookup m n = Some x"
      by (simp add: domIff keys_dom_lookup)
    then show ?thesis
      by blast
  qed
  moreover have "x \<in> values m" if a: "Mapping.lookup m n = Some x" for n
  proof -
    have "n \<in> Mapping.keys m"
      using a by (simp add: keys_is_none_rep)
    then show ?thesis
      unfolding mapping_values using a by (force simp add: image_def)
  qed
  ultimately show ?thesis
    by blast
qed


context formula
begin
lemma form_imp_implies: "valid (\<phi> \<longrightarrow>\<^sub>f \<rho>) \<longleftrightarrow> implies \<phi> \<rho>"
 using satisfies_Language valid_def by (auto)
end

lemma lookup_keys_None: "x \<notin> Mapping.keys m \<Longrightarrow> Mapping.lookup m x = None" 
  by (simp add: domIff keys_dom_lookup)

lemma lookup_keys: "(\<exists>y. Mapping.lookup m x = Some y) \<longleftrightarrow> x \<in> Mapping.keys m"
  by (simp add: domIff keys_dom_lookup)

lemma keys_lookup_eq:
  assumes "Mapping.keys m = Mapping.keys m'"
  shows "Option.is_none (Mapping.lookup m x) = Option.is_none (Mapping.lookup m' x)"
  using assms by (auto) (metis keys_is_none_rep)+

lemma is_none_Some: "(\<not> Option.is_none y) \<Longrightarrow> \<exists>x. y = Some x"
  by (cases y) auto

definition checkFormula where
  "checkFormula f = do {check (IA.formula f) (showsl STR ''Non well formed formula'');
                        IA.check_valid_formula f}"



lemma checkFormula:
  assumes "isOK (checkFormula (\<phi> \<longrightarrow>\<^sub>f \<rho>))"
  shows "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
  using assms
  unfolding checkFormula_def IA.form_imp_implies[symmetric]
  using IA.check_valid_formula by (force)+

definition update_asFun where
  "update_asFun as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi> =
   do {
    check (v\<^sub>n \<notin> all_sym_vars as\<^sub>1) (showsl STR ''update_asFun: vn in symbolic vars'');
    check (Mapping.lookup (stack as\<^sub>2) n = Some (t, v\<^sub>n)) (showsl STR ''update_asFun: vn not defined in as2'');
    check (\<forall>x \<in> Mapping.keys (stack as\<^sub>1). x \<noteq> n \<longrightarrow> Mapping.lookup (stack as\<^sub>1) x =  Mapping.lookup (stack as\<^sub>2) x)
          (showsl STR ''update_asFun: stack2 is not extensions of stack1'');
    check (Mapping.keys (stack as\<^sub>2) = Mapping.keys (stack as\<^sub>1) \<union> {n}) (showsl STR '''update_asFun:  stack2 is not extensions of stack1'');
    checkFormula (kb as\<^sub>1 \<and>\<^sub>f \<phi> \<longrightarrow>\<^sub>f kb as\<^sub>2)
 }"

definition evalAsFun where
  "evalAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n =
  (do {
       let fs = (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Assignment n (Binop binop o\<^sub>1 o\<^sub>2))) \<Rightarrow> Inr (n, binop, o\<^sub>1, o\<^sub>2)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''evalFun: Not a binop'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''evalFun: unexpected error''));
       (n, binop, o\<^sub>1, o\<^sub>2) \<leftarrow> fs;
       (l\<^sub>1, term\<^sub>1) \<leftarrow> case operand_value (of_as_impl as\<^sub>1) o\<^sub>1 of Some (IntType l, te) \<Rightarrow> Inr (l, te)
                                                               | _ \<Rightarrow> Inl (showsl STR ''evalFun 3'');
       (l\<^sub>2, term\<^sub>2) \<leftarrow> case operand_value (of_as_impl as\<^sub>1) o\<^sub>2 of Some (IntType l, te) \<Rightarrow> Inr (l, te)
                                                               | _ \<Rightarrow> Inl (showsl STR ''evalFun 3'');
       let \<phi> = encode_binop binop v\<^sub>n term\<^sub>1 term\<^sub>2;
       check (l\<^sub>1 = l\<^sub>2) (showsl STR ''evalFun'');
       check (pointers as\<^sub>1 = pointers as\<^sub>2) (showsl STR ''evalFun'');
       check (allocs as\<^sub>1 = allocs as\<^sub>2) (showsl STR ''evalFun'');
       check (0 < l\<^sub>1) (showsl STR ''evalFun'');
       update_asFun as\<^sub>1 as\<^sub>2 n (IntType l\<^sub>1) v\<^sub>n \<phi>;
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''evalFun'')
       })"

definition genAsFun where
  "genAsFun as\<^sub>1 as\<^sub>2 \<mu> =
  (do {check (pos as\<^sub>2 = pos as\<^sub>1) (showsl STR ''genFun 1'');
       check (Mapping.keys (stack as\<^sub>1) = Mapping.keys (stack as\<^sub>2)) (showsl STR ''genFun 2'');
       checkFormula (kb as\<^sub>1 \<longrightarrow>\<^sub>f rename_vars \<mu> (kb as\<^sub>2));
       check (\<forall>n \<in> Mapping.keys (stack as\<^sub>2).
               (case Mapping.lookup (stack as\<^sub>2) n of
                 Some (t, lv) \<Rightarrow> Mapping.lookup (stack as\<^sub>1) n = Some (t, \<mu> lv))) (showsl STR ''genFun 4'');
       check (\<forall>(lb, ub)\<in>allocs as\<^sub>2. (\<mu> lb, \<mu> ub) \<in> allocs as\<^sub>1)  (showsl STR ''genFun 5'');
       check (\<forall>p\<in>Mapping.keys (pointers as\<^sub>2). (case Mapping.lookup (pointers as\<^sub>2) p of
                 Some (t, lv) \<Rightarrow> Mapping.lookup (pointers as\<^sub>1) (\<mu> p) = Some (t, \<mu> lv)))  (showsl STR ''genFun 5'')
       })"

definition (in ll_mem_funs_extra) allocAsFun where
  "allocAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>l\<^sub>b v\<^sub>u\<^sub>b =
  (do {
       (n, lt, o\<^sub>1) \<leftarrow> (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Assignment n (Alloca lt o\<^sub>1))) \<Rightarrow> Inr (n, lt, o\<^sub>1)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''evalFun: Not a binop'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''evalFun: unexpected error''));
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''pos allocFun'');
       (l\<^sub>1, term\<^sub>1) \<leftarrow> (case o\<^sub>1 of None \<Rightarrow> Inr (32, encode_int_const 1)
                        | Some o\<^sub>1 \<Rightarrow> (case operand_value (of_as_impl as\<^sub>1) o\<^sub>1
                                     of Some (IntType l, te) \<Rightarrow> Inr (l, te)
                                    | _ \<Rightarrow> Inl (showsl STR ''allocFun 3'')));
       check (0 < l\<^sub>1) (showsl STR ''allocFun'');
       checkFormula (kb as\<^sub>1 \<longrightarrow>\<^sub>f encode_sig IA.LessF (encode_int_const 0) term\<^sub>1);
       check (v\<^sub>u\<^sub>b \<notin> all_sym_vars as\<^sub>1) (showsl STR ''allocFun vub'');
       check (v\<^sub>u\<^sub>b \<noteq> v\<^sub>l\<^sub>b) (showsl STR ''allocFun vub vlb'');
       let \<phi> = encode_alloc v\<^sub>l\<^sub>b v\<^sub>u\<^sub>b term\<^sub>1 lt;
       update_asFun as\<^sub>1 as\<^sub>2 n (PointerType lt) v\<^sub>l\<^sub>b \<phi>;
       check (pointers as\<^sub>1 = pointers as\<^sub>2) (showsl STR ''pointers allocFun'');
       check (allocs as\<^sub>2 = allocs as\<^sub>1 \<union> {(v\<^sub>l\<^sub>b, v\<^sub>u\<^sub>b)}) (showsl STR ''allocs allocFun'')
       })"

definition (in ll_mem_funs_extra) properStoreFun where
  "properStoreFun kb allocs va t lb ub =
  (do {
   checkFormula (kb \<longrightarrow>\<^sub>f encode_sig IA.LeF (encode_int_var lb) (encode_int_var va));
   checkFormula (kb \<longrightarrow>\<^sub>f encode_sig IA.LeF ((Fun (IA.SumF 2) 
                          [encode_int_var va, encode_int_const (len_of t)])) (encode_int_var ub))
       })" for kb allocs

definition (in ll_mem_funs_extra) filterPointerFun where
  "filterPointerFun kb pointers va t a =
  (do {
   (t', v') \<leftarrow> option_to_sum (Mapping.lookup pointers a) (showsl STR ''filterPointerFun'');
   checkFormula (kb \<longrightarrow>\<^sub>f (encode_sig IA.LeF (Fun (IA.SumF 2) [encode_int_var va, encode_int_const (len_of t)]) (encode_int_var a)
                \<or>\<^sub>f encode_sig IA.LeF (Fun (IA.SumF 2) [encode_int_var a, encode_int_const (len_of t')]) (encode_int_var va)))
       })" for kb pointers

definition (in ll_mem_funs_extra) storeAsFun where
  "storeAsFun prog as\<^sub>1 as\<^sub>2 w ps =
  (do {
       (t, ov, na) \<leftarrow> (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Store t ov (LocalReference na))) \<Rightarrow> Inr (t, ov, na)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''storeAsFun: Not a binop'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''storeAsFun: unexpected error''));
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''pos storeAsFun'');
       (type\<^sub>a, v\<^sub>a) \<leftarrow> option_to_sum (Mapping.lookup (stack as\<^sub>1) na) (showsl STR ''storeAsFun'');
       (type\<^sub>v, term\<^sub>v) \<leftarrow> option_to_sum (operand_value (of_as_impl as\<^sub>1) ov) (showsl STR ''storeAsFun'');
       check (type\<^sub>a = PointerType type\<^sub>v) (showsl STR ''storeAsFun'');
       check (t = type\<^sub>v) (showsl STR ''storeAsFun'');
       check (\<exists>(lb,ub) \<in> allocs as\<^sub>1. isOK (properStoreFun (kb as\<^sub>1) (allocs as\<^sub>1) v\<^sub>a type\<^sub>v lb ub)) (showsl STR ''storeAsFun'');
       check (w \<notin> all_sym_vars as\<^sub>1) (showsl STR ''storeAsFun'');
       checkFormula (kb as\<^sub>1 \<and>\<^sub>f encode_eq (encode_int_var w) term\<^sub>v \<longrightarrow>\<^sub>f kb as\<^sub>2);
       let ps' = Mapping.filter (\<lambda>k v. k \<in> set ps) (pointers as\<^sub>1);
       mapM_sum (filterPointerFun (kb as\<^sub>1) ps' v\<^sub>a type\<^sub>v) ps;
       check (pointers as\<^sub>2 = Mapping.update v\<^sub>a (type\<^sub>v, w) ps') (showsl STR ''storeAsFun'');
       check (stack as\<^sub>2 = stack as\<^sub>1) (showsl STR ''storeAsFun'');
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl STR ''storeAsFun'')
       })"

definition (in ll_mem_funs_extra) loadAsFun where
  "loadAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>p' v\<^sub>n =
  (do {
       (n, t\<^sub>1, na) \<leftarrow> (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Assignment n (Load t\<^sub>1 (LocalReference na)))) \<Rightarrow> Inr (n, t\<^sub>1, na)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''loadAsFun'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''loadAsFun''));
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''pos loadAsFun'');
       (t\<^sub>2, v\<^sub>p) \<leftarrow> case Mapping.lookup (stack as\<^sub>1) na of Some (PointerType t\<^sub>2, v\<^sub>p) \<Rightarrow> Inr (t\<^sub>2, v\<^sub>p)
                                                    | _ \<Rightarrow> Inl (showsl STR ''loadAsFun'');
       (t\<^sub>3, v\<^sub>v) \<leftarrow> option_to_sum (Mapping.lookup (pointers as\<^sub>1) v\<^sub>p') (showsl STR ''loadAsFun'');
       check (t\<^sub>2 = t\<^sub>1) (showsl STR ''loadAsFun'');
       check (t\<^sub>3 = t\<^sub>1) (showsl STR ''loadAsFun'');
       checkFormula ((kb as\<^sub>1) \<longrightarrow>\<^sub>f (encode_eq (encode_int_var v\<^sub>p) (encode_int_var v\<^sub>p')));
       update_asFun as\<^sub>1 as\<^sub>2 n t\<^sub>1 v\<^sub>n (encode_eq (encode_int_var v\<^sub>n) (encode_int_var v\<^sub>v));
       check (pointers as\<^sub>2 = pointers as\<^sub>1) (showsl STR ''storeAsFun'');
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl STR ''storeAsFun'')
       })"

definition refineAsFun where
  "refineAsFun as\<^sub>1 as\<^sub>2 as\<^sub>3 \<phi> =
  (do {
       check (pos as\<^sub>2 = pos as\<^sub>1) (showsl ''refineFun 1'');
       check (pos as\<^sub>3 = pos as\<^sub>1) (showsl ''refineFun 2'');
       check (stack as\<^sub>2 = stack as\<^sub>1) (showsl ''refineFun 3'');
       check (stack as\<^sub>3 = stack as\<^sub>1) (showsl ''refineFun 4'');
       check (allocs as\<^sub>3 = allocs as\<^sub>1) (showsl ''refineFun 5'');
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl ''refineFun 6'');
       check (pointers as\<^sub>3 = pointers as\<^sub>1) (showsl ''refineFun 7'');
       check (pointers as\<^sub>2 = pointers as\<^sub>1) (showsl ''refineFun 7'');
       checkFormula (kb as\<^sub>1 \<and>\<^sub>f \<phi> \<longrightarrow>\<^sub>f kb as\<^sub>2);
       checkFormula (kb as\<^sub>1 \<and>\<^sub>f (\<not>\<^sub>f \<phi>) \<longrightarrow>\<^sub>f kb as\<^sub>3)
       })"

definition phi_abstract'Fun where
  "phi_abstract'Fun as\<^sub>1 as\<^sub>2 x ps v\<^sub>x type\<^sub>x term\<^sub>x old_b_id = do {
       y\<^sub>x \<leftarrow> option_to_sum (small_step.phi_bid old_b_id ps) id;
       (let x = operand_value (of_as_impl as\<^sub>1) y\<^sub>x in check (x = Some (type\<^sub>x, term\<^sub>x)) (showsl STR ''phi_abstract'Fun 1 error: '' \<circ> showsl x \<circ> showsl STR '' != Some '' \<circ> showsl term\<^sub>x));
       check (Mapping.lookup (stack as\<^sub>2) x = Some (type\<^sub>x, v\<^sub>x))  (showsl STR ''phi_abstract Fun 3'');
       check (\<not> (v\<^sub>x \<in> all_sym_vars as\<^sub>1)) (showsl STR ''phi_abstract Fun 4'')
       }"

fun phi_abstractFun where
  "phi_abstractFun as\<^sub>1 as\<^sub>2 ((x, ps)#xs) ((v\<^sub>x, type_term, t\<^sub>x)#ys) old_b_id =
    do {phi_abstract'Fun as\<^sub>1 as\<^sub>2 x ps v\<^sub>x type_term t\<^sub>x old_b_id;
        phi_abstractFun as\<^sub>1 as\<^sub>2 xs ys old_b_id}"
| "phi_abstractFun as\<^sub>1 as\<^sub>2 [] [] old_b_id = Inr ()"
| "phi_abstractFun as\<^sub>1 as\<^sub>2 _ _ old_b_id = Inl (showsl STR ''phi_abstractFun'')"


definition branchAsFun where
  "branchAsFun prog as\<^sub>1 as\<^sub>2 \<phi>s =
  (do {let (f_id, old_b_id, p) = pos as\<^sub>1;
       let new_b_id' = (case find_statement prog (pos as\<^sub>1) of
                  Inr (Terminator (Br new_b_id)) \<Rightarrow> Inr new_b_id
                | Inr _ \<Rightarrow> Inl (showsl STR ''branchFun: Not a branch'')
                | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                | Inl _ \<Rightarrow> Inl (showsl STR ''branchFun: unexpected error''));
       new_b_id \<leftarrow> new_b_id';
       phis_stats \<leftarrow> map_sum (\<lambda>_. (showsl STR ''branchFun phis not found'')) id (find_phis prog f_id new_b_id);
       check (pos as\<^sub>2 = (f_id, new_b_id, length phis_stats)) (showsl STR ''branchFun Wrong position'');
       phi_abstractFun as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id;
       let f = (Conjunction (map (\<lambda>(v\<^sub>x,type_term, t\<^sub>x). encode_eq (encode_int_var v\<^sub>x) t\<^sub>x) \<phi>s)) \<and>\<^sub>f (kb as\<^sub>1) \<longrightarrow>\<^sub>f kb as\<^sub>2;
       checkFormula f;
       check (inj_on (map_option snd \<circ> Mapping.lookup (stack as\<^sub>2)) (fst ` set phis_stats)) ((showsl STR ''Not inj_on''));
       check ((\<forall>x \<in> Mapping.keys (stack as\<^sub>1).
                x \<notin> (fst ` set phis_stats) \<longrightarrow> Mapping.lookup (stack as\<^sub>2) x =
                                               Mapping.lookup (stack as\<^sub>1) x)) ((showsl STR ''Not same vars''));
       check (Mapping.keys (stack as\<^sub>2) = Mapping.keys (stack as\<^sub>1) \<union> fst ` set phis_stats) ((showsl STR ''Wrong key subset''));
       check (distinct (map fst \<phi>s)) ((showsl STR ''Not distinct''));
       check (distinct (map fst phis_stats)) (showsl STR ''Not distinct'');
       check (allocs as\<^sub>1 = allocs as\<^sub>2) (showsl STR ''allocs'');
       check (pointers as\<^sub>1 = pointers as\<^sub>2) (showsl STR ''pointers'')
       })"

definition condBranchAsFun where
  "condBranchAsFun prog as\<^sub>1 as\<^sub>2 \<phi>s b =
  (do {
       let (f_id, old_b_id, p) = pos as\<^sub>1;
       let new_b_id' = (case find_statement prog (pos as\<^sub>1) of
                  Inr (Terminator (CondBr c b\<^sub>t b\<^sub>f)) \<Rightarrow> Inr (c, b\<^sub>t, b\<^sub>f)
                | Inr _ \<Rightarrow> Inl (showsl STR ''condbranchFun: Not a branch'')
                | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                | Inl _ \<Rightarrow> Inl (showsl STR ''condbranchFun: unexpected error''));
       (c, b_id_true, b_id_false) \<leftarrow> new_b_id';
       c' \<leftarrow> case operand_value (of_as_impl as\<^sub>1) c of Some (IntType (Suc 0), c') \<Rightarrow> Inr c'
                                                        |  _ \<Rightarrow> Inl (showsl STR ''condBr 2'');
       let ft = kb as\<^sub>1 \<longrightarrow>\<^sub>f encode_eq c' (Fun (IA.ConstF 1) []);
       let ff = kb as\<^sub>1 \<longrightarrow>\<^sub>f encode_eq c' (Fun (IA.ConstF 0) []);
       let new_b_id = (if b then b_id_true else b_id_false);
       (if b then checkFormula ft else checkFormula ff);
       phis_stats \<leftarrow> map_sum (\<lambda>_. (showsl STR ''branchFun phis not found'')) id (find_phis prog f_id new_b_id);
       check (pos as\<^sub>2 = (f_id, new_b_id, length phis_stats)) (showsl STR ''branchFun Wrong position'');
       phi_abstractFun as\<^sub>1 as\<^sub>2 phis_stats \<phi>s old_b_id;
       let f = (Conjunction (map (\<lambda>(v\<^sub>x,type_term, t\<^sub>x). encode_eq (encode_int_var v\<^sub>x) t\<^sub>x) \<phi>s)) \<and>\<^sub>f (kb as\<^sub>1) \<longrightarrow>\<^sub>f kb as\<^sub>2;
       checkFormula f;
       check (inj_on (map_option snd \<circ> Mapping.lookup (stack as\<^sub>2)) (fst ` set phis_stats)) ((showsl STR ''Not inj_on''));
       check ((\<forall>x \<in> Mapping.keys (stack as\<^sub>1).
                x \<notin> (fst ` set phis_stats) \<longrightarrow> Mapping.lookup (stack as\<^sub>2) x =
                                               Mapping.lookup (stack as\<^sub>1) x)) ((showsl STR ''Not same vars''));
       check (Mapping.keys (stack as\<^sub>2) = Mapping.keys (stack as\<^sub>1) \<union> fst ` set phis_stats) ((showsl STR ''Wrong key subset''));
       check (distinct (map fst \<phi>s)) ((showsl STR ''Not distinct''));
       check (distinct (map fst phis_stats)) (showsl STR ''Not distinct'');
       check (allocs as\<^sub>1 = allocs as\<^sub>2) (showsl STR ''allocs'');
       check (pointers as\<^sub>1 = pointers as\<^sub>2) (showsl STR ''pointers'')
       })"

definition icmpAsFun where
  "icmpAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n b =
  (do {
       let fs = (case find_statement prog (pos as\<^sub>1) of
                   Inr (Instruction (Assignment n (Icmp p o\<^sub>1 o\<^sub>2))) \<Rightarrow> Inr (n, p, o\<^sub>1, o\<^sub>2)
                | Inr _ \<Rightarrow> Inl (showsl STR ''icmpFun: no icmp'')
                | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                | Inl _ \<Rightarrow> Inl (showsl STR ''icmpFun: unexpected error''));
       (n, p, o\<^sub>1, o\<^sub>2) \<leftarrow> fs;
       (type\<^sub>1, t\<^sub>1) \<leftarrow>  option_to_sum (operand_value (of_as_impl as\<^sub>1) o\<^sub>1) id;
       (type\<^sub>2, t\<^sub>2) \<leftarrow>  option_to_sum (operand_value (of_as_impl as\<^sub>1) o\<^sub>2) id;
       check (type\<^sub>1 = type\<^sub>2) (showsl STR ''icmpFun 1'');
       let \<phi> = encode_pred p t\<^sub>1 t\<^sub>2;
       let \<chi> = (if b then encode_eq (encode_int_var v\<^sub>n) (Fun (IA.ConstF 1) [])
                     else encode_eq (encode_int_var v\<^sub>n) (Fun (IA.ConstF 0) []));
       (if b then checkFormula (kb as\<^sub>1 \<longrightarrow>\<^sub>f \<phi>) else checkFormula (kb as\<^sub>1 \<longrightarrow>\<^sub>f (\<not>\<^sub>f \<phi>)));
       update_asFun as\<^sub>1 as\<^sub>2 n (IntType 1) v\<^sub>n \<chi>;
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''icmpFun 3'');
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl STR ''icmpFun 3'');
       check (pointers as\<^sub>2 = pointers as\<^sub>1) (showsl STR ''icmpFun 3'')
       })"

definition (in ll_mem_funs_extra) gepAsFun where
  "gepAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n =
  (do {
       (n, o\<^sub>1, o\<^sub>2) \<leftarrow> (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Assignment n (GetElementPtr o\<^sub>1 o\<^sub>2))) \<Rightarrow> Inr (n, o\<^sub>1, o\<^sub>2)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''gepAsFun'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''gepAsFun''));
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''gepAsFun'');
       (t\<^sub>1, te\<^sub>1) \<leftarrow> case operand_value (of_as_impl as\<^sub>1) o\<^sub>1 of Some (PointerType t, te) \<Rightarrow> Inr (t, te)
                                                               | _ \<Rightarrow> Inl (showsl STR ''gepAsFun'');
       (l\<^sub>2, te\<^sub>2) \<leftarrow> case operand_value (of_as_impl as\<^sub>1) o\<^sub>2 of Some (IntType l, te) \<Rightarrow> Inr (l, te)
                                                               | _ \<Rightarrow> Inl (showsl STR ''gepAsFun'');
       check (0 < l\<^sub>2) (showsl STR ''gepAsFun'');
       let \<phi> = encode_eq (encode_int_var v\<^sub>n)
                 (Fun (IA.SumF 2) [te\<^sub>1, (Fun (IA.ProdF 2) [te\<^sub>2, encode_int_const (len_of t\<^sub>1)])]);
       update_asFun as\<^sub>1 as\<^sub>2 n (PointerType t\<^sub>1) v\<^sub>n \<phi>;
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl STR ''gepAsFun'');
       check (pointers as\<^sub>2 = pointers as\<^sub>1) (showsl STR ''gepAsFun'')
       })"

definition ptrToIntAsFun where
  "ptrToIntAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n =
  (do {
       (n, o\<^sub>1, t) \<leftarrow> (case find_statement prog (pos as\<^sub>1) of
                  Inr (Instruction (Assignment n (PtrToInt o\<^sub>1 t))) \<Rightarrow> Inr (n, o\<^sub>1, t)
                  | Inr _ \<Rightarrow> Inl (showsl STR ''ptrToIntAsFun'')
                  | Inl (StaticError x) \<Rightarrow> Inl (showsl x)
                  | Inl _ \<Rightarrow> Inl (showsl STR ''ptrToIntAsFun''));
       check (pos as\<^sub>2 = inc_pos (pos as\<^sub>1)) (showsl STR ''ptrToIntAsFun'');
       (pt\<^sub>1, te\<^sub>1) \<leftarrow> case operand_value (of_as_impl as\<^sub>1) o\<^sub>1 of Some (PointerType t, te) \<Rightarrow> Inr (t, te)
                                                               | _ \<Rightarrow> Inl (showsl STR ''ptrToIntAsFun'');
       (case t of IntType _ \<Rightarrow> Inr () | _ \<Rightarrow> Inl (showsl STR ''ptrToIntAsFun''));
       let \<phi> = encode_eq (encode_int_var v\<^sub>n) te\<^sub>1;
       update_asFun as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi>;
       check (allocs as\<^sub>2 = allocs as\<^sub>1) (showsl STR ''ptrToIntAsFun'');
       check (pointers as\<^sub>2 = pointers as\<^sub>1) (showsl STR ''ptrToIntAsFun'')
       })"

lemma update_asFun:
  assumes "isOK (update_asFun as\<^sub>1 as\<^sub>2 n t v\<^sub>n \<phi>)"
  shows "update_as (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2) n t v\<^sub>n \<phi>"
proof -
  have "IA.implies (Formula.form_and (kb as\<^sub>1) \<phi>) (kb as\<^sub>2)"
    using assms by (subst IA.form_imp_implies[symmetric])
      (auto simp add: update_asFun_def checkFormula_def intro!: IA.check_valid_formula)
  moreover have "Mapping.lookup (abstract_state_impl.stack as\<^sub>2) x =
        (Mapping.lookup (abstract_state_impl.stack as\<^sub>1)(n \<mapsto> (t, v\<^sub>n))) x" for x
    using assms 
    by (cases "x \<in> Mapping.keys (abstract_state_impl.stack as\<^sub>1)")
      (auto simp add: lookup_keys_None update_asFun_def)
  ultimately show ?thesis
    using assms Mapping_values
    by (auto intro!: update_as.intros simp add: update_asFun_def)
qed

lemma evalAsFun_evalAsInf:
  assumes "isOK (evalAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n)"
  shows "evalAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  obtain n binop o\<^sub>1 o\<^sub>2 where
    "find_statement prog (abstract_state_impl.pos as\<^sub>1) =
          Inr (Instruction (Assignment n (Binop binop o\<^sub>1 o\<^sub>2)))"
    using assms by (auto simp add: evalAsFun_def split: stuck.splits step_splits)
  then show ?thesis
    using assms
    apply(auto simp add: evalAsFun_def isOK_def check_def
    split: option.splits sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
      step_splits llvm_type.splits
    elim!: option_to_sum.elims) (* let auto do the unfolding of evalAsFun *)
    by (intro evalAsInf.intros) (fastforce simp add: intro!: update_asFun evalAsInf.intros)+
qed

lemma genFun_genInf:
  fixes as\<^sub>1 :: "(_, _, 'lv::{linorder,showl}, _) abstract_state_impl"
  assumes "isOK (genAsFun as\<^sub>1 as\<^sub>2 \<mu>)"
  shows "genAsInf (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2) \<mu>"
proof -
  have 1: "IA.implies \<phi> \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()"
                               "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "'lv IA.formula"
    using that IA.check_valid_formula by (subst IA.form_imp_implies[symmetric]) blast
  have 2: "dom (abstract_state.stack (of_as_impl as\<^sub>1)) = dom (abstract_state.stack (of_as_impl as\<^sub>2))"
    using assms
    by (auto simp add: isOK_def check_def genAsFun_def Option.is_none_def keys_dom_lookup[symmetric]
        split: step_splits if_splits elim!: option_to_sum.elims)
  moreover have "abstract_state.kb (of_as_impl as\<^sub>1)
        \<Longrightarrow>\<^sub>I\<^sub>A map_formula (rename_vars \<mu>) (abstract_state.kb (of_as_impl as\<^sub>2))"
    using assms by (intro 1) (auto simp add: isOK_def check_def genAsFun_def checkFormula_def
        split: step_splits if_splits elim!: option_to_sum.elims)
  moreover have "\<forall>n lv t. abstract_state.stack (of_as_impl as\<^sub>2) n = Some (t, lv) \<longrightarrow> abstract_state.stack (of_as_impl as\<^sub>1) n = Some (t, \<mu> lv)"
    using assms
    by (auto simp add: isOK_def check_def genAsFun_def Option.is_none_def keys_dom_lookup[symmetric]
        split: step_splits if_splits elim!: option_to_sum.elims)
      (metis domI keys_dom_lookup)
  moreover have "\<forall>a lt x. abstract_state.pointers (of_as_impl as\<^sub>2) a = Some (lt, x) \<longrightarrow> abstract_state.pointers (of_as_impl as\<^sub>1) (\<mu> a) = Some (lt, \<mu> x)"
        using assms
        by (auto simp add: isOK_def check_def genAsFun_def Option.is_none_def keys_dom_lookup[symmetric]
        split: step_splits if_splits elim!: option_to_sum.elims)
      (metis domI keys_dom_lookup)
  ultimately show ?thesis
    using assms
    by (intro genAsInf.intros) (auto simp add: isOK_def check_def genAsFun_def  
    split: step_splits if_splits elim!: option_to_sum.elims)
qed

lemma (in ll_mem_funs_extra) allocAsFun_allocAsInf:
  assumes "isOK (allocAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>l\<^sub>b v\<^sub>u\<^sub>b)"
  shows "allocAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note Integer_Arithmetic.IA.implies_Language[simp del]
  obtain n lt o\<^sub>1 where
   n: "find_statement prog (abstract_state_impl.pos as\<^sub>1) =
         Inr (Instruction (Assignment n (Alloca lt o\<^sub>1)))"
    using assms by (auto simp add: allocAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits)
  then obtain l\<^sub>1 term\<^sub>1 where l: "(case o\<^sub>1 of None \<Rightarrow> Inr (32, encode_int_const 1)
                        | Some o\<^sub>1 \<Rightarrow> (case operand_value (of_as_impl as\<^sub>1) o\<^sub>1
                                     of Some (IntType l, te) \<Rightarrow> Inr (l, te)
                                    | _ \<Rightarrow> Inl (showsl STR ''allocFun 3''))) = Inr (l\<^sub>1, term\<^sub>1)"
    using assms by (auto simp add: allocAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits
      option.splits)
  show ?thesis
    apply(intro allocAsInf.intros[where n=n and lt=lt and o\<^sub>1=o\<^sub>1 and te\<^sub>1=term\<^sub>1])
    using assms n l
    by (auto simp add: allocAsFun_def 
    simp del: encode_alloc.simps encode_int_const.simps
    split: sum.splits option.splits llvm_type.splits intro!: update_asFun checkFormula)
qed

lemma (in ll_mem_funs_extra) storeAsFun_storeAsInf:
  assumes "isOK (storeAsFun prog as\<^sub>1 as\<^sub>2 w ps)"
  shows "storeAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note Integer_Arithmetic.IA.implies_Language[simp del]
  obtain t ov na where
   n: "find_statement prog (abstract_state.pos (of_as_impl as\<^sub>1)) =
         Inr (Instruction (Store t ov (LocalReference na)))"
    using assms by (auto simp add: storeAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits operand.splits)
  then obtain type\<^sub>a v\<^sub>a type\<^sub>v term\<^sub>v where p: "Mapping.lookup (stack as\<^sub>1) na = Some (type\<^sub>a, v\<^sub>a)"
    "operand_value (of_as_impl as\<^sub>1) ov = Some (type\<^sub>v, term\<^sub>v)"
    using assms by (auto simp add: storeAsFun_def option_to_sum_def
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits
      option.splits operand.splits)
  obtain lb ub where lb: "(lb,ub) \<in> allocs as\<^sub>1" "isOK (properStoreFun (kb as\<^sub>1) (allocs as\<^sub>1) v\<^sub>a type\<^sub>v lb ub)"
    using assms n p by (auto simp add: storeAsFun_def option_to_sum_def
      split: stuck.splits sum.splits option.splits operand.splits)
  have ps: "proper_store (kb as\<^sub>1) (allocs as\<^sub>1) v\<^sub>a type\<^sub>v"
    using lb unfolding properStoreFun_def 
    by (intro proper_store.intros[of lb ub]) (auto intro: checkFormula)
  let ?ps' = "Mapping.filter (\<lambda>k v. k \<in> set ps) (pointers as\<^sub>1)"
  have m: "isOK (mapM_sum (filterPointerFun (kb as\<^sub>1) ?ps' v\<^sub>a type\<^sub>v) ps)"
    using assms n p by (auto simp add: storeAsFun_def option_to_sum_def
      split: stuck.splits sum.splits option.splits operand.splits)
  have "abstract_state_impl.kb as\<^sub>1 \<Longrightarrow>\<^sub>I\<^sub>A
   (formula.Atom (Fun IA.LeF [Fun (IA.SumF 2) [Var (v\<^sub>a, IA.IntT), Fun (IA.ConstF (int (len_of type\<^sub>v))) []], Var (a, IA.IntT)])
    \<or>\<^sub>f formula.Atom (Fun IA.LeF [Fun (IA.SumF 2) [Var (a, IA.IntT), Fun (IA.ConstF (int (len_of t'))) []], Var (v\<^sub>a, IA.IntT)]))"
    if "Mapping.lookup (Mapping.filter (\<lambda>k v. k \<in> set ps) (abstract_state_impl.pointers as\<^sub>1)) a = Some (t', v')"
    for a t' v'
  proof -
    have 1: "a \<in> set ps"
      using that unfolding lookup_filter by (auto split: option.splits if_splits)
    show ?thesis
      using mapM_sum[OF m 1]
      unfolding filterPointerFun_def
      using that p by (auto simp add: option_to_sum_def split: option.splits intro: checkFormula)
  qed
  then have fp: "filter_pointers (kb as\<^sub>1) (Mapping.lookup (pointers as\<^sub>1)) (Mapping.lookup ?ps') v\<^sub>a type\<^sub>v"
    by (intro filter_pointers.intros)  (auto intro: Mapping_filter)
  show ?thesis
    apply(intro storeAsInf.intros[OF n, where type\<^sub>a=type\<^sub>a and v\<^sub>a=v\<^sub>a and type\<^sub>v=type\<^sub>v and term\<^sub>v=term\<^sub>v])
    using assms n p ps fp
    by (auto simp add: storeAsFun_def option_to_sum_def
    simp del: encode_alloc.simps encode_int_const.simps
    split: sum.splits option.splits llvm_type.splits intro!: update_asFun checkFormula)
qed

lemma (in ll_mem_funs_extra) loadAsFun_loadAsInf:
  assumes "isOK (loadAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>p' v\<^sub>n)"
  shows "loadAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note Integer_Arithmetic.IA.implies_Language[simp del]
  obtain n t\<^sub>1 na where
   n: "find_statement prog (abstract_state.pos (of_as_impl as\<^sub>1)) =
         Inr (Instruction (Assignment n (Load t\<^sub>1 (LocalReference na))))"
    using assms by (auto simp add: loadAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits operand.splits)
  then obtain t\<^sub>2 v\<^sub>p t\<^sub>3 v\<^sub>v where p: "Mapping.lookup (stack as\<^sub>1) na = Some (t\<^sub>2, v\<^sub>p)"
    "Mapping.lookup (pointers as\<^sub>1) v\<^sub>p' = Some (t\<^sub>3, v\<^sub>v)"
    using assms by (auto simp add: loadAsFun_def option_to_sum_def
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits
      option.splits operand.splits)
  show ?thesis
    apply(intro loadAsInf.intros[OF n])
    using assms n p
    by (auto simp add: loadAsFun_def option_to_sum_def
    simp del: encode_alloc.simps encode_int_const.simps
    split: sum.splits option.splits llvm_type.splits intro!: update_asFun checkFormula)
qed

lemma refineFun_refineInf:
  fixes as :: "(_, _, 'lv::{linorder,showl}, _) abstract_state_impl"
  assumes "isOK (refineAsFun as as\<^sub>t as\<^sub>f \<phi> )"
  shows "refineAsInf (of_as_impl as) (of_as_impl as\<^sub>t) (of_as_impl as\<^sub>f)"
proof -
  have 1: "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "'lv IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  have 2: "(kb as \<and>\<^sub>f \<phi>) \<Longrightarrow>\<^sub>I\<^sub>A kb as\<^sub>t"
   using assms by (intro 1) (auto simp add: isOK_def check_def refineAsFun_def checkFormula_def
        split: step_splits if_splits elim!: option_to_sum.elims)
  have 3: "kb as \<and>\<^sub>f (\<not>\<^sub>f \<phi>) \<Longrightarrow>\<^sub>I\<^sub>A kb as\<^sub>f"
   using assms by (intro 1) (auto simp add: isOK_def check_def refineAsFun_def checkFormula_def
        split: step_splits if_splits elim!: option_to_sum.elims)
  show ?thesis
    using assms 2 3 by (intro refineAsInf.intros)
    (auto simp add: isOK_def check_def refineAsFun_def
        split: step_splits if_splits elim!: option_to_sum.elims)
qed

lemma phi_abstract'Fun_phi_abstract':
  assumes "isOK (phi_abstract'Fun as\<^sub>1 as\<^sub>2 x ps v\<^sub>x type\<^sub>x t\<^sub>x old_b_id)"
  shows "phi_abstract' (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2) x ps v\<^sub>x type\<^sub>x t\<^sub>x old_b_id"
proof -
  have "ran (abstract_state.stack (of_as_impl as\<^sub>1)) = values (stack as\<^sub>1)"
    using Mapping_values by (fastforce simp add: ran_def)
  then show ?thesis
    using assms
    by (auto simp add: isOK_def check_def phi_abstract'Fun_def option_to_sum_def
        split: step_splits if_splits intro!: phi_abstract'.intros)
qed

lemma phi_abstractFun_phi_abstract:
  assumes "isOK (phi_abstractFun as\<^sub>1 as\<^sub>2 xs ys old_b_id)"
  shows "phi_abstract (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2) xs ys old_b_id"
proof -
  have "ran (abstract_state.stack (of_as_impl as\<^sub>1)) = values (stack as\<^sub>1)"
    using Mapping_values by (fastforce simp add: ran_def)
  then show ?thesis
    using assms
    by(induction as\<^sub>2 xs ys old_b_id rule: phi_abstractFun.induct)
      (auto simp add: isOK_def check_def split: step_splits
        intro!: update_asFun phi_abstract.intros phi_abstract'Fun_phi_abstract')
qed

lemma branchAsFun_branchAsInf:
  assumes "isOK (branchAsFun prog as\<^sub>1 as\<^sub>2 \<phi>s)"
  shows "branchAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note find_statement.simps[simp del] find_phis.simps[simp del] formula.simps[simp del] IA.implies_Language[simp del]
  obtain f_id old_b_id p where f_id: "abstract_state.pos (of_as_impl as\<^sub>1) = (f_id, old_b_id, p)"
    using prod.exhaust by metis
  have "\<exists>new_b_id . find_statement prog (pos as\<^sub>1) = Inr (Terminator (LLVM_Syntax.Br new_b_id))"
    using assms
    by (auto simp add: branchAsFun_def split: stuck.splits step_splits)
  then obtain new_b_id where t: "find_statement prog (pos as\<^sub>1) = Inr (Terminator (LLVM_Syntax.Br new_b_id))"
    by blast
  have "\<exists>phis_stats. find_phis prog f_id new_b_id = Inr phis_stats"
    using assms t f_id
    by (auto simp add: isOK_def branchAsFun_def map_sum_Inr_conv split: step_splits)
  then obtain phis_stats where phis_stats: "find_phis prog f_id new_b_id = Inr phis_stats"
    by metis
  have inj: "inj_on (map_option snd \<circ> Mapping.lookup (stack as\<^sub>2)) (fst ` set phis_stats)"
    using assms phis_stats f_id t
    by (auto simp add: check_def branchAsFun_def keys_dom_lookup split: named.splits
        intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
  show ?thesis
    apply(intro branchAsInf.intros[where \<phi>s=\<phi>s  and new_b_id=new_b_id
          and f_id=f_id and old_b_id=old_b_id and p=p and phis_stats=phis_stats])
    using assms phis_stats f_id t inj unfolding inj_on_def
    by (auto simp add: check_def branchAsFun_def keys_dom_lookup split: named.splits
        intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
qed

lemma condBranchAsFun_condBranchAsInf:
  assumes "isOK (condBranchAsFun prog as\<^sub>1 as\<^sub>2 \<phi>s b)"
  shows "condBranchAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note find_statement.simps[simp del] find_phis.simps[simp del] formula.simps[simp del] 
       IA.implies_Language[simp del] encode_eq.simps[simp del] option_to_sum.simps[simp del]
  have 1: "\<phi> \<Longrightarrow>\<^sub>I\<^sub>A \<rho>" if "IA.check_valid_formula (\<phi> \<longrightarrow>\<^sub>f \<rho>) = Inr ()" "IA.formula (\<phi> \<longrightarrow>\<^sub>f \<rho>)"
    for \<phi> \<rho> :: "name IA.formula"
    apply(subst IA.form_imp_implies[symmetric])
    using that IA.check_valid_formula by blast
  obtain f_id old_b_id p where f_id: "abstract_state.pos (of_as_impl as\<^sub>1) = (f_id, old_b_id, p)"
    using prod.exhaust by metis
  have "\<exists>c b\<^sub>t b\<^sub>f. find_statement prog (pos as\<^sub>1) = Inr (Terminator (LLVM_Syntax.CondBr c b\<^sub>t b\<^sub>f))"
    using assms
    by (auto simp add: condBranchAsFun_def split: sum.splits stuck.splits action.splits terminator.splits)
  then obtain c b\<^sub>t b\<^sub>f where t: "find_statement prog (pos as\<^sub>1) = Inr (Terminator (LLVM_Syntax.CondBr c b\<^sub>t b\<^sub>f))"
    by blast
  obtain c' where c': "operand_value (of_as_impl as\<^sub>1) c = Some (IntType (Suc 0), c')"
    using assms t
    by (auto simp add: condBranchAsFun_def split: option.splits prod.splits llvm_type.splits nat.splits)
  define new_b_id where "new_b_id = (if b then b\<^sub>t else b\<^sub>f)"
  have "\<exists>phis_stats. find_phis prog f_id new_b_id = Inr phis_stats"
    using assms t f_id 
    by (auto simp add: new_b_id_def isOK_def condBranchAsFun_def map_sum_Inr_conv split: step_splits)
  then obtain phis_stats where phis_stats: "find_phis prog f_id new_b_id = Inr phis_stats"
    by metis
  have inj: "inj_on (map_option snd \<circ> Mapping.lookup (stack as\<^sub>2)) (fst ` set phis_stats)"
    using assms phis_stats f_id t c' new_b_id_def
    by (auto simp add: check_def condBranchAsFun_def keys_dom_lookup split: named.splits
        intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
  show ?thesis
    apply(intro condBranchAsInf.intros[where \<phi>s=\<phi>s  and new_b_id=new_b_id
          and f_id=f_id and old_b_id=old_b_id and p=p and phis_stats=phis_stats and c=c
          and b_id_true=b\<^sub>t and b_id_false=b\<^sub>f and c'=c' and b=b])
    using assms phis_stats f_id t inj c' unfolding inj_on_def new_b_id_def
    by (auto simp add: check_def condBranchAsFun_def keys_dom_lookup split: named.splits
        intro!: update_asFun phi_abstract.intros phi_abstractFun_phi_abstract checkFormula)
qed

lemma icmpAsFun_icmpAsInf:
  assumes "isOK (icmpAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n b)"
  shows "icmpAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  obtain n p o\<^sub>1 o\<^sub>2 where
    "find_statement prog (abstract_state_impl.pos (as\<^sub>1)) =
          Inr (Instruction (Assignment n (LLVM_Syntax.Icmp p o\<^sub>1 o\<^sub>2)))"
    using assms by (auto simp add: icmpAsFun_def split: stuck.splits step_splits)
  then show ?thesis
    using assms
    apply(auto simp add: icmpAsFun_def isOK_def check_def
    split: sum.splits action.splits named.splits instruction.splits sum_bind_splits if_splits
    elim!: option_to_sum.elims)
    by (intro icmpAsInf.intros[where b=b and o\<^sub>1=o\<^sub>1 and o\<^sub>2=o\<^sub>2],
        auto simp add: option_to_sum_def split: option.splits
         intro!: checkFormula update_asFun simp del: IA.implies_Language)+
qed

lemma (in ll_mem_funs_extra) ptrToIntAsFun_ptrToIntAsInf:
  assumes "isOK (ptrToIntAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n)"
  shows "ptrToIntAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note Integer_Arithmetic.IA.implies_Language[simp del]
  obtain n o\<^sub>1 t where
   n: "find_statement prog (abstract_state.pos (of_as_impl as\<^sub>1)) =
         Inr (Instruction (Assignment n (PtrToInt o\<^sub>1 t)))"
    using assms by (auto simp add: ptrToIntAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits operand.splits)
  then obtain pt\<^sub>1 te\<^sub>1 l where 
    p: "operand_value (of_as_impl as\<^sub>1) o\<^sub>1 = Some (PointerType pt\<^sub>1, te\<^sub>1)" "t = IntType l"
    using assms by (auto simp add: ptrToIntAsFun_def option_to_sum_def
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits
      option.splits operand.splits llvm_type.splits)
  show ?thesis
    using assms n p
    by (intro ptrToIntAsInf.intros[OF n])  (auto simp add: ptrToIntAsFun_def option_to_sum_def
    simp del: encode_alloc.simps encode_int_const.simps 
    split: sum.splits option.splits llvm_type.splits intro!: update_asFun checkFormula)
qed

lemma (in ll_mem_funs_extra) gepAsFun_gepAsInf:
  assumes "isOK (gepAsFun prog as\<^sub>1 as\<^sub>2 v\<^sub>n)"
  shows "gepAsInf prog (of_as_impl as\<^sub>1) (of_as_impl as\<^sub>2)"
proof -
  note Integer_Arithmetic.IA.implies_Language[simp del]
  obtain n o\<^sub>1 o\<^sub>2 where
   n: "find_statement prog (abstract_state.pos (of_as_impl as\<^sub>1)) =
         Inr (Instruction (Assignment n (GetElementPtr o\<^sub>1 o\<^sub>2)))"
    using assms by (auto simp add: gepAsFun_def 
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits operand.splits)
  then obtain t\<^sub>1 te\<^sub>1 l\<^sub>2 te\<^sub>2 where 
    p: "operand_value (of_as_impl as\<^sub>1) o\<^sub>1 = Some (PointerType t\<^sub>1, te\<^sub>1)"
    "operand_value (of_as_impl as\<^sub>1) o\<^sub>2 = Some (IntType l\<^sub>2, te\<^sub>2)"
    using assms by (auto simp add: gepAsFun_def option_to_sum_def
      split: stuck.splits sum.splits action.splits instruction.splits r_instruction.splits
      option.splits operand.splits llvm_type.splits)
  show ?thesis
    using assms n p
    by (intro gepAsInf.intros[OF n]) (auto simp add: gepAsFun_def option_to_sum_def
    simp del: encode_alloc.simps encode_int_const.simps 
    split: sum.splits option.splits llvm_type.splits intro!: update_asFun checkFormula)
qed





(*
locale graph_exec =
  fixes as_map_of_node :: "'n \<Rightarrow> (LLVM_State.pos, name, ('lv::{linorder,showl}), llvm_type) abstract_state_mapping" and
        renaming_of_edge :: "('n \<times> 'n) \<Rightarrow> ('lv \<Rightarrow> 'lv) option" and
        edges ::  "('n \<times> 'n) set" and
        prog :: llvm_prog
begin

definition renaming_of_edge' where
  "renaming_of_edge' x = (case renaming_of_edge x of Some f \<Rightarrow> f | None \<Rightarrow> id)"

datatype ('n, 'v) edge_rule =
    Eval 'n 'v
  | Gen 'n "('v \<times> 'v) list"
  | Refine 'n 'n "(IA.sig, 'v \<times> IA.ty) Term.term formula"
  | Br 'n "('v \<times> (IA.sig, 'v \<times> IA.ty) Term.term) list"
  | CondBr 'n "('v \<times> (IA.sig, 'v \<times> IA.ty) Term.term) list" bool
  | Icmp 'n 'v bool
  | Return

fun target_list where
  "target_list (Eval n _) = [n]"
| "target_list (Gen n _) = [n]"
| "target_list (Refine n1 n2 _) = [n1,n2]"
| "target_list (Br n _) = [n]"
| "target_list (CondBr n _ _) = [n]"
| "target_list (Icmp n _ _) = [n]"
| "target_list (Return) = []"

definition target where "target x = set (target_list x)"

type_synonym ('pos, 'pv, 'lv) as_impl = "'pos \<times> ('pv \<times> 'lv) list \<times> 'lv IA.formula"

datatype ('node, 'lv) seg_impl =
  Seg_Impl
  (initial_node: "'node")
  (edges: "('node \<times> ('node, 'lv) edge_rule) list")
  (nodes_as: "('node \<times> ((name \<times> name \<times> nat), name, 'lv) as_impl) list")

(* Function to collect error messages and not just show the first one
   Useful for debugging
*)
fun collectErrorMessages :: "('e + 'a) list \<Rightarrow> 'e list + 'a list"
where
  "collectErrorMessages [] = Inr []" |
  "collectErrorMessages (m # ms) =
     (case collectErrorMessages ms of Inr ms' \<Rightarrow> map_sum (\<lambda>e. [e]) (\<lambda>m'. m'#ms') m
                | Inl es \<Rightarrow>
     case m of Inr m' \<Rightarrow> Inl es | Inl e \<Rightarrow> Inl (e#es))
  "

lemma collectErrorMessages_sequence: "isOK (collectErrorMessages xs) \<longleftrightarrow> isOK (sequence xs)"
proof -
  have "isOK m"
    if "isOK (sequence xs)" "collectErrorMessages xs = Inr xs'"
      "isOK (map_sum (\<lambda>e. [e]) (\<lambda>m'. m' # xs') m)" for m xs xs'
    using that by (cases m) (auto)
  then show ?thesis
    by (induction xs) (auto split: sum.splits)
qed

locale graph_exec' =
  fixes seg :: "('n::{showl}, 'lv::{linorder,showl}) seg_impl"
  and prog :: llvm_prog
begin

definition edges_list where
  "edges_list =
    concat (map (\<lambda>(n,r). map (\<lambda>t. (n, t)) (target_list r)) (seg_impl.edges seg))"

definition edges where "edges = set edges_list"
definition nodes_list where "nodes_list = remdups (map fst edges_list @ map snd edges_list)"
definition edge where "edge = Mapping.of_alist (seg_impl.edges seg)"

fun renaming_of_edge where
  "renaming_of_edge (n\<^sub>1, n\<^sub>2) =
    (case Mapping.lookup edge n\<^sub>1
      of Some (Gen n\<^sub>2' \<mu>) \<Rightarrow>
       if n\<^sub>2 = n\<^sub>2' then Some (\<lambda>x. case map_of \<mu> x of Some y \<Rightarrow> y | None \<Rightarrow> x)
                   else Some id
      | _ \<Rightarrow> None)"

definition nodes_asm_list where
  "nodes_asm_list =
    map (\<lambda>(n, (p, s, kb)). (n, \<lparr>pos = p, stack = Mapping.of_alist s, kb = kb\<rparr>))
    (seg_impl.nodes_as seg)"

definition as where "as = (Mapping.of_alist nodes_asm_list)"

sublocale graph_exec "the \<circ> (Mapping.lookup as)" renaming_of_edge edges prog .

definition choice_collect_error_messages where
  "choice_collect_error_messages ms =
    (try Error_Monad.choice ms catch (\<lambda>f. Inl (default_showsl_list id f)))"

fun checkEdge :: "'n \<Rightarrow> ('n, 'lv) edge_rule \<Rightarrow>  (String.literal \<Rightarrow> String.literal) + unit" where
  "checkEdge n1 (Eval n2 v\<^sub>n) = choice_collect_error_messages [evalFun n1 n2 v\<^sub>n, evalExternalFun n1 n2 v\<^sub>n]"
| "checkEdge n1 (Gen n2 \<mu>) = genFun n1 n2"
| "checkEdge n1 (Refine n2 n3 \<phi>) = refineFun n1 n2 n3 \<phi>"
| "checkEdge n1 (Br n2 \<phi>s) = branchFun n1 n2 \<phi>s"
| "checkEdge n1 (CondBr n2 \<phi>s b) = condBranchFun n1 n2 \<phi>s b"
| "checkEdge n1 (Icmp n2 v\<^sub>n b) = icmpFun n1 n2 v\<^sub>n b"
| "checkEdge n1 (Return) = returnFun n1"

definition checkEdge' where
  "checkEdge' n e = (let
     message_add = (\<lambda>em. showsl_lit STR ''Error on node '' \<circ> showsl n \<circ> showsl_lit STR '':'' \<circ> em)
   in
     map_sum message_add id (checkEdge n e))"

definition closedGraphFun' where
  "closedGraphFun' = (let
    check_n = (\<lambda>n.
      do {
        e \<leftarrow> option_to_sum (Mapping.lookup edge n) (showsl STR ''No edge found for node: '' \<circ> showsl n);
        checkEdge' n e
      })
  in
    map (check_n \<circ> fst) (nodes_as seg))"

definition closedGraphFun where
  "closedGraphFun = do {
     check (set (map fst (nodes_as seg)) = nodes) (showsl STR ''edges and node set not in sync'');
     map_sum (default_showsl_list id) id (collectErrorMessages closedGraphFun')}"

end

declare graph_exec'.edges_def [code]
declare graph_exec'.renaming_of_edge.simps [code]
declare graph_exec'.checkEdge.simps [code]
declare graph_exec'.checkEdge'_def [code]
declare graph_exec'.closedGraphFun'_def [code]
declare graph_exec'.closedGraphFun_def [code]
declare graph_exec'.nodes_list_def [code]
declare graph_exec'.edges_list_def [code]
declare graph_exec'.edge_def [code]
declare graph_exec'.as_def [code]
declare graph_exec'.nodes_asm_list_def [code]
declare graph_exec.evalExternalFun_def [code]
declare graph_exec'.choice_collect_error_messages_def [code]


unbundle no_IA_formula_notation
*)
end