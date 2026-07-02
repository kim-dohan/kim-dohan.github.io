(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015, 2017, 2020)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2013-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Code_Haskell
  imports
    Proof_Checker.Ceta
    Proof_Checker.Version
begin

export_code certify_proof Certified Unsupported Error Inl Inr version
  nat_of_integer
  literal.explode
  in Haskell module_name Ceta

end

