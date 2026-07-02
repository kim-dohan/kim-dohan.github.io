(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Defaults
imports Main
begin

(* defaults values for nfs flag in termination proofs *)
definition "default_nfs_trs = False"
definition "default_nfs_dp = True"

(* defaults values for nfs flag in nontermination proofs *)
definition "default_nfs_nt_trs = False"
definition "default_nfs_nt_dp = False"

end
