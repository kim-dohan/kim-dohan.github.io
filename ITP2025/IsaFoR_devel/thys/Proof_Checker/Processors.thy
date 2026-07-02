(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2011-2015)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2013-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)

theory Processors
imports
  Not_SN.Nontermination_Processors
  SN.Termination_Processors

  Ord.Reduction_Pair_Implementations

  Sem_Lab.Semantic_Labeling_Carrier

  CR.Equational_Reasoning_Impl
  CR.Orthogonality_Impl
  CR.Critical_Pair_Closure_Impl
  CR.Parallel_Closed_Impl
  CR.Strongly_Closed_Impl
  CR.Development_Closed_Impl
  CR.Parallel_Critical_Pairs_Impl
  CR.Non_Confluence_Impl
  CR.Non_Commutation_Impl
  CR.Rule_Labeling_Impl
  CR.Redundant_Rules_Impl
  CR.Ordered_Completion_Impl

  CTRS.Unraveling_Impl
  Check_Level_Confluence

  CR.LS_Persistence_Impl
begin

end
