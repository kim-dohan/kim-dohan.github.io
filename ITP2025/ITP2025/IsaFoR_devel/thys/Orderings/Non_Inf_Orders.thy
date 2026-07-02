theory Non_Inf_Orders
imports 
  Ordered_Algebra
  Non_Inf_Order
begin

context ord begin

abbreviation(input) "less_bounded b x y \<equiv> x < y \<and> b \<le> y"

end

context ord_syntax begin

abbreviation(input) less_bounded where "less_bounded \<equiv> ord.less_bounded less_eq less"

end

context quasi_order begin

lemma bounded: "class.quasi_order less_eq (less_bounded b)"
  by (unfold_locales, auto dest: less_trans less_le_trans le_less_trans order_trans less_imp_le)

end

class non_inf_quasi_order = quasi_order +
  assumes non_infp: "\<And>b. \<And> f :: nat \<Rightarrow> 'a. chainp greater f \<Longrightarrow> \<exists>i. \<not> b < f i"
begin

sublocale non_inf_order "rel_of (>)" "rel_of (\<ge>)" by (unfold_locales, rule, auto intro!: non_infp)

interpretation bounded: quasi_order less_eq "less_bounded b" by (fact bounded)

lemma bounded: "class.wf_order less_eq (less_bounded b)"
  apply unfold_locales
  apply (rule wf_induct_rule[OF bound_on_le_SN[unfolded SN_iff_wf bound_on_le_def, of b], simplified], auto)
done

end

end
