(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2013, 2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2012-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Orthogonality_Impl
imports 
  First_Order_Rewriting.Orthogonality 
  Critical_Pairs_Impl
  Framework.QDP_Framework_Impl
begin


subsection \<open>Proving confluence of TRSs\<close>

definition check_weakly_orthogonal where 
  "check_weakly_orthogonal ren R = do {
           check_left_linear_trs R;
           check_allm (\<lambda> (l,r). check (is_Fun l) (showsl_lit (STR ''the TRS has variables as left-hand sides''))) R;
           check_allm (\<lambda> (b,s,t). do {
              check (s = t) (showsl_lit (STR ''there is a non-trivial critical pair: '') \<circ> showsl s \<circ> showsl_lit (STR '' <- . -> '')
                \<circ> showsl t)
            }) (critical_pairs_impl ren R R) 
         }  <+? (\<lambda>s. s \<circ> showsl_lit (STR ''\<newline>hence, the following TRS is not weakly orthogonal\<newline>'') \<circ> showsl_trs R)"

lemma check_weakly_orthogonal: assumes "isOK(check_weakly_orthogonal ren R)"
  shows "CR (rstep (set R))"
  by (rule weakly_orthogonal_rstep_CR, insert assms[unfolded check_weakly_orthogonal_def], auto)

end
