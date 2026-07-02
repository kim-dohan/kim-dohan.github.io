(*
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2014, 2015)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2014)
License: LGPL (see file COPYING.LESSER)
*)
theory Context_Sensitive_Impl
imports
  Context_Sensitive
begin
(* context sensitive replacement map \<mu> *)
type_synonym 'f muL = "(('f \<times> nat) \<times> (nat list))list"

(* default value: allow all replacements *)
definition mu_of :: "'f muL \<Rightarrow> 'f mu" where
  "mu_of \<mu> \<equiv> let m = map_of \<mu> in 
    (\<lambda> (f,a). case m (f,a) of None \<Rightarrow> { 0 ..< a} | Some is \<Rightarrow> set is)"

definition mu_to_fp_impl :: "'f muL \<Rightarrow> ('f,string) forb_pattern list" where
  "mu_to_fp_impl \<mu> \<equiv> let 
     fs = remdups (map fst \<mu>);
     m  = map_of \<mu>;
     fs_mus = concat (map (\<lambda> f. let xs = map Var (fresh_strings_list ''x'' 0 [] (snd f) )
       in map (\<lambda> i. (f,xs,i)) ([i . i <- [0 ..< snd f], i \<notin> set (the (m f))])) fs)     
   in [ (ctxt_of_pos_term [i] (Fun f xs), xs ! i, loc) . 
     ((f,a),xs,i) <- fs_mus, 
     loc <- [Forbidden_Patterns.B, Forbidden_Patterns.H]]" 

lemma mu_to_fp_impl[simp]: "set (mu_to_fp_impl \<mu>) = to_pi (mu_of \<mu>)" (is "?l = ?r")
proof -
  note d = mu_to_fp_impl_def to_pi_def mu_of_def Let_def split
  let ?fs = "remdups (map fst \<mu>)"
  let ?m = "map_of \<mu>"
  let ?fs_mus = "concat (map (\<lambda> f. let xs = map Var (fresh_strings_list ''x'' 0 [] (snd f) )
       in map (\<lambda> i. (f,xs,i)) ([i . i <- [0 ..< snd f], i \<notin> set (the (?m f))])) ?fs)"
  {
    fix c t loc 
    assume "(c,t,loc) \<in> ?r"
    from this obtain f a xs i where
      c: "c = ctxt_of_pos_term [i] (Fun f xs)" and
      t: "t = xs ! i" and
      i: "i < a" and
      mu: "i \<notin> mu_of \<mu> (f,a)" and
      xs: "xs = map Var (fresh_strings_list ''x'' 0 [] a)" and
      loc: "loc \<in> {location.B, location.H}" unfolding d by blast
    {
      assume "?m (f,a) = None"
      with mu i have False unfolding d by auto
    } note some = this
    then have fs: "(f,a) \<in> set ?fs" unfolding map_of_eq_None_iff by auto
    have id: "mu_of \<mu> (f,a) = set (the (?m (f,a)))" unfolding d
      by (metis some option.exhaust option.simps(5) option.sel)
    have "((f,a),xs,i) \<in> set ?fs_mus" 
      unfolding set_concat set_map 
      by (rule UN_I[OF imageI[of "(f, a)"]], insert xs id fs mu i, auto)
    then have "(c,t,loc) \<in> ?l" using loc unfolding c t d
      by auto
  }
  moreover
  {
    fix c t loc
    assume "(c,t,loc) \<in> ?l"
    from this obtain f a xs i where 
    c: "c = ctxt_of_pos_term [i] (Fun f xs)" and
    t: "t = xs ! i" and
    mem: "((f,a),xs,i) \<in> set ?fs_mus" and
    loc: "loc \<in> {Forbidden_Patterns.B, Forbidden_Patterns.H}"
      unfolding d by force
    from mem have xs: "xs = map Var (fresh_strings_list ''x'' 0 [] a)" by auto
    from mem have "(f,a) \<in> set ?fs" by auto
    then have "?m (f,a) \<noteq> None" unfolding map_of_eq_None_iff by auto
    then obtain "is" where m: "?m (f,a) = Some is" by auto
    from mem m have i: "i < a" and nmem: "i \<notin> set is" by auto
    from m nmem have nmem: "i \<notin> mu_of \<mu> (f,a)" unfolding d by auto
    from i nmem xs loc have "(c,t,loc) \<in> ?r" unfolding c t to_pi_def by blast
  }
  ultimately show ?thesis by auto
qed 
    
lemma csstep_iff_fpstep_impl: "csstep (mu_of \<mu>) = fpstep (set (mu_to_fp_impl \<mu>))"
  unfolding mu_to_fp_impl using csstep_iff_fpstep by blast

end
