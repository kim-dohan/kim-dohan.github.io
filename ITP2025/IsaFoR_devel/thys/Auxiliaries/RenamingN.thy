theory RenamingN
  imports
    Fresh_Identifiers.Fresh
begin

typedef ('v :: infinite) renamingN = "{ (ren1 :: nat \<times> 'v \<Rightarrow> 'v, ren2 :: 'v \<Rightarrow> 'v) | ren1 ren2. 
  inj ren1 \<and> inj ren2 \<and> range ren1 \<inter> range ren2 = {} }" 
proof -
  let ?U = "UNIV :: 'v set" 
  let ?N = "UNIV :: nat set" 
  have inf: "infinite ?U" by (rule infinite_UNIV)
  have "ordLeq3 (card_of (?N \<times> ?U)) (card_of ?U)"  
    by (metis card_of_Times_infinite_simps(3) empty_not_UNIV infinite_UNIV infinite_iff_card_of_nat ordIso_imp_ordLeq)
  from card_of_Plus_infinite1[OF inf this, folded card_of_ordIso] 
  obtain f where bij: "bij_betw f (?U <+> ?N \<times> ?U) ?U" by auto
  hence injf: "inj f" by (simp add: bij_is_inj)
  define ren1 where "ren1 = f o Inr"
  define ren2 where "ren2 = f o Inl" 
  show ?thesis proof (intro exI[of _ "(ren1, ren2)"], clarsimp, intro conjI allI impI)
    show "inj ren2" unfolding ren2_def by (intro inj_compose[OF injf], auto)
    show "inj ren1" unfolding ren1_def by (intro inj_compose[OF injf], auto)
    show "range ren1 \<inter> range ren2 = {}"
    proof (rule ccontr)
      assume "\<not> ?thesis" 
      then obtain nx x where "ren1 nx = ren2 x" 
        using injD injf ren1_def ren2_def by fastforce
      hence "f (Inl x) = f (Inr nx)" unfolding ren1_def ren2_def by auto
      with injf show False unfolding inj_on_def by blast
    qed
  qed
qed

setup_lifting type_definition_renamingN

lift_definition rename_many :: "'v :: infinite renamingN \<Rightarrow> nat \<times> 'v \<Rightarrow> 'v" is "fst" .
lift_definition rename_single :: "'v :: infinite renamingN \<Rightarrow> 'v \<Rightarrow> 'v" is snd .

lemma renameN: 
  "inj (rename_many r)" 
  "inj (rename_single r)" 
  "range (rename_many r) \<inter> range (rename_single r) = {}"
  by (transfer, force)+


end