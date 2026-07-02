(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  Guillaume Allais (2011)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Ceta
  imports
    Pre_Ceta
    Auxx.Diff_Array_Code_Haskell
    Berlekamp_Zassenhaus.Code_Abort_Gcd
    Real_Impl.Real_Unique_Impl
begin

declare eval_list_haskell[code_unfold]

text \<open>reactivate code mapping for Haskell Array\<close>
code_printing constant Array \<rightharpoonup> (Haskell) "Array.Array"
code_printing type_constructor array \<rightharpoonup> (Haskell) "Array.Array/ _"

end
