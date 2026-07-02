(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2010-2018)
Author:  Julian Nagele <julian.nagele@uibk.ac.at> (2012-2017)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2010-2016)
Author:  Sarah Winkler <sarah.winkler@uibk.ac.at> (2013, 2014)
Author:  Thomas Sternagel <thomas.sternagel@uibk.ac.at> (2012)
Author:  Akihisa Yamada <akihisa.yamada@uibk.ac.at> (2017)
License: LGPL (see file COPYING.LESSER)
*)
theory CPF_Proof_Parser
  imports
    Proof_Checker
    CPF_Input_Parser
    LTS.LTS_Parser
begin

hide_const (open) Congruence.partition
hide_const (open) Invariant_Checker.name
hide_const (open) AC_Subterm_Criterion.proj_term
hide_const (open) Finite_Cartesian_Product.mat
hide_const (open) Simplex.Bounds
hide_const (open) Cooperation_Program.sharp.Sharp
hide_type (open) Finite_Cartesian_Product.vec
hide_const (open) Finite_Cartesian_Product.vec.vec_nth
no_notation Finite_Cartesian_Product.vec.vec_nth (infixl \<open>$\<close> 90)
hide_const (open) Congruence.eq
hide_const (open) UnivPoly.deg
hide_const (open) Parser_Monad.return (* we want return and *)
hide_const (open) Parser_Monad.error  (* error from Strict_Sum *)
hide_type (open) Polynomial.poly (* we want Polynomials.poly *)

abbreviation xml_singleton :: "ltag \<Rightarrow> 'a xmlt \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> 'b xmlt"
where "xml_singleton tag p f \<equiv> XMLdo tag {x \<leftarrow> p; xml_return (f x)}"

abbreviation xml_pair
where "xml_pair tag p1 p2 f \<equiv> XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; xml_return (f a b)}"

abbreviation xml_triple :: "ltag \<Rightarrow> 'a xmlt \<Rightarrow> 'b xmlt \<Rightarrow> 'c xmlt \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'c \<Rightarrow> 'd) \<Rightarrow> 'd xmlt"
where "xml_triple tag p1 p2 p3 f \<equiv> XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; c \<leftarrow> p3; xml_return (f a b c)}"

abbreviation xml_many where "xml_many tag p f \<equiv> XMLdo tag {a \<leftarrow>* p; xml_return (f a)}"
abbreviation xml_tuple4 where "xml_tuple4 tag p1 p2 p3 p4 f \<equiv>
  XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; c \<leftarrow> p3; d \<leftarrow> p4; xml_return (f a b c d)}"
abbreviation xml_tuple5 where "xml_tuple5 tag p1 p2 p3 p4 p5 f \<equiv>
  XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; c \<leftarrow> p3; d \<leftarrow> p4; e \<leftarrow> p5; xml_return (f a b c d e)}"
abbreviation "xml_tuple6 tag p1 p2 p3 p4 p5 p6 t \<equiv>
 XMLdo tag {a \<leftarrow> p1; b \<leftarrow> p2; c \<leftarrow> p3; d \<leftarrow> p4; e \<leftarrow> p5; f \<leftarrow> p6; xml_return (t a b c d e f)}"

partial_function (sum_bot) arith_fun :: "arithFun xmlt"
  where
  [code]: "arith_fun xml = XMLdo (STR ''arithFunction'') {
    a \<leftarrow>
      xml_change (xml_nat (STR ''natural'')) (\<lambda> n. xml_return (Const n))
      XMLor xml_change (xml_nat (STR ''variable'')) (\<lambda> n. xml_return (Arg (n - 1)))
      XMLor XMLdo (STR ''sum'') { as \<leftarrow>* arith_fun; xml_return (Sum as)}
      XMLor XMLdo (STR ''product'') { as \<leftarrow>* arith_fun; xml_return (Prod as)}
      XMLor XMLdo (STR ''max'') { as \<leftarrow>* arith_fun; xml_return (Semantic_Labeling_Carrier.Max as)}
      XMLor xml_many (STR ''min'') arith_fun Semantic_Labeling_Carrier.Min \<comment> \<open>just illustrate other style\<close>
      XMLor XMLdo (STR ''ifEqual'') { a \<leftarrow> arith_fun; b \<leftarrow> arith_fun; c \<leftarrow> arith_fun; d  \<leftarrow> arith_fun;
         xml_return (IfEqual a b c d)}
    ;
    xml_return a
  } xml"

definition sl_variant :: "'f xmlt \<Rightarrow> ('f, string) sl_variant xmlt"
where
  "sl_variant xml2name = xml_singleton (STR ''model'') (
     XMLdo (STR ''rootLabeling'') { fo \<leftarrow>? xml2name;
        xml_return (Rootlab (case fo of None \<Rightarrow> None | Some f \<Rightarrow> Some (f,1))) }
     XMLor XMLdo (STR ''finiteModel'') {
        n \<leftarrow> xml_change (xml_nat (STR ''carrierSize'')) (\<lambda> n. xml_return (n - 1));
        to \<leftarrow>? xml_singleton (STR ''tupleOrder'') (xml_leaf (STR ''pointWise'') ()) id;
        inter \<leftarrow>* xml_triple (STR ''interpret'')
           xml2name
           (xml_nat (STR ''arity''))
           arith_fun
           (\<lambda> f a inter. ((f,a),inter));
        xml_return (case to of
          None \<Rightarrow> Finitelab (SL_Inter n inter)
        | Some _ \<Rightarrow> QuasiFinitelab (SL_Inter n inter) [])
     }
   ) id"
hide_const (open) sl_variant

context
  fixes C :: "'a ring" (structure)
begin
fun sum_lpoly :: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "sum_lpoly [] ys = ys"
| "sum_lpoly xs [] = xs"
| "sum_lpoly (x # xs) (y # ys) = (x \<oplus> y) # sum_lpoly xs ys"

fun
  lpoly_of ::
    "(nat, 'a) tpoly \<Rightarrow> String.literal +\<^sub>\<bottom> ('a \<times> 'a list)"
where
  "lpoly_of (PNum i) = return (i, [])"
| "lpoly_of (PVar x) = return (\<zero>, replicate x \<zero> @ [\<one>])"
| "lpoly_of (PSum []) = return (\<zero>, [])"
| "lpoly_of (PSum (p # ps)) = (
     lpoly_of  p
  \<bind> (\<lambda>(cp, ncp). lpoly_of (PSum ps)
  \<bind> (\<lambda>(cq, ncq). return (cp \<oplus> cq, sum_lpoly ncp ncq))))"
| "lpoly_of (PMult []) = return (\<one>, [])"
| "lpoly_of (PMult (p # ps)) = (
     lpoly_of p
  \<bind> (\<lambda>(cp, ncp). lpoly_of (PMult ps)
  \<bind> (\<lambda>(cq, ncq). if (Ball (set ncp) ((=) \<zero>))
       then return (cp \<otimes> cq, map ((\<otimes>) cp) ncq)
       else (if (Ball (set ncq) ((=) \<zero>))
         then return (cp \<otimes> cq, map (\<lambda> x. x \<otimes> cq) ncp)
         else error (STR ''cannot transform non-linear polynomial to linear polynomial'')))))"

primrec fit_length :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "fit_length (Suc n) as = (case as of
    [] \<Rightarrow> replicate (Suc n) \<zero>
  | b # bs \<Rightarrow> b # fit_length n bs)"
| "fit_length 0 _ = []"
end

partial_function (sum_bot) polynomial :: "'a xmlt \<Rightarrow> (nat, 'a) tpoly xmlt" where
  [code]: "polynomial xml2coeff x =
       (xml_change xml2coeff (\<lambda> n. xml_return (PNum n))
       XMLor xml_change (xml_nat (STR ''variable'')) (\<lambda> n. xml_return (PVar (n - 1)))
       XMLor xml_many (STR ''sum'') (polynomial xml2coeff) PSum
       XMLor xml_many (STR ''product'') (polynomial xml2coeff) PMult
     ) x"

definition "int_coeff = xml_int (STR ''integer'')"
hide_const (open) int_coeff

definition "nat_coeff = xml_nat (STR ''nat'')"
hide_const (open) nat_coeff

definition vec_coeff :: "'a xmlt \<Rightarrow> 'a vec xmlt" where
  "vec_coeff xml2coeff = xml_many (STR ''vector'') xml2coeff vec_of_list"
hide_const (open) vec_coeff

(* allow vectors and convert them to matrices by filling in zeros *)
definition mat_coeff :: "nat \<Rightarrow> 'a \<Rightarrow> 'a xmlt \<Rightarrow> 'a mat xmlt" where
  "mat_coeff n ze xml2coeff =
     xml_many (STR ''matrix'') (CPF_Proof_Parser.vec_coeff xml2coeff) (mat_of_rows n)
     XMLor xml_change (CPF_Proof_Parser.vec_coeff xml2coeff) (\<lambda> v. xml_return (mat n n (\<lambda> (i,j). if j = 0 then v $ i else ze)))"
hide_const (open) mat_coeff

definition arctic_coeff :: "arctic xmlt" where
  "arctic_coeff = xml_change CPF_Proof_Parser.int_coeff (xml_return o Num_arc)
     XMLor xml_leaf (STR ''minusInfinity'') MinInfty"
hide_const (open) arctic_coeff

definition xml_rat :: "rat xmlt"
where
  "xml_rat = xml_change (xml_int (STR ''integer'')) (xml_return o of_int)
     XMLor xml_pair (STR ''rational'')
        (xml_int (STR ''numerator''))
        (xml_int (STR ''denominator''))
        (\<lambda> x y. of_int x / of_int y)"

definition arctic_rat_coeff :: "rat arctic_delta xmlt" where
  "arctic_rat_coeff = xml_change xml_rat (xml_return o Num_arc_delta)
       XMLor xml_leaf (STR ''minusInfinity'') MinInfty_delta"

hide_const (open) arctic_rat_coeff

datatype Domain =
  Natural nat | Integer | NegativeInteger | Arctic | Arctic_rat | Int_mat nat nat | Arctic_mat nat
| Arctic_rat_mat nat | Rational rat nat | Rat_mat nat nat | Mini_Alg real nat
| Mini_Alg_mat nat nat | Int_core_mat nat "nat list" core_matrix_mode

definition rat_domain :: "rat xmlt" where
  "rat_domain = xml_singleton (STR ''rationals'') (xml_singleton (STR ''delta'') xml_rat id) id"
hide_const (open) rat_domain

definition xml_real :: "real xmlt" where
  "xml_real = xml_change xml_rat (xml_return o real_of_rat)
      XMLor xml_triple (STR ''algebraic'') xml_rat xml_rat xml_rat
        (\<lambda>a b c. (real_of_rat a + real_of_rat b * sqrt (real_of_rat c)))"

definition real_domain :: "real xmlt" where
  "real_domain = xml_singleton (STR ''algebraicNumbers'') (xml_singleton (STR ''delta'') xml_real id) id"
hide_const (open) real_domain

definition basic_domain :: "(nat \<Rightarrow> Domain) xmlt" where
  "basic_domain = xml_leaf (STR ''naturals'') Natural
    XMLor xml_leaf (STR ''integers'') (\<lambda> d. Integer)
     XMLor xml_leaf (STR ''negativeIntegers'') (\<lambda> d. NegativeInteger)
    XMLor xml_change CPF_Proof_Parser.rat_domain (xml_return o Rational)
    XMLor xml_change CPF_Proof_Parser.real_domain (xml_return o Mini_Alg)
    XMLor xml_singleton (STR ''arctic'') (xml_singleton (STR ''domain'') (
      xml_leaf (STR ''naturals'') (\<lambda> d. Arctic)
      XMLor xml_leaf (STR ''integers'') (\<lambda> d. Arctic)
      XMLor xml_change CPF_Proof_Parser.rat_domain (\<lambda> r. xml_return (\<lambda> d. Arctic_rat))
     ) id) id"
hide_const (open) basic_domain


term xml_tuple4
definition interpretation_type :: "Domain xmlt" where
  "interpretation_type = xml_singleton (STR ''type'') (
     xml_triple (STR ''matrixInterpretation'')
       (xml_singleton (STR ''domain'') CPF_Proof_Parser.basic_domain id)
       (xml_nat (STR ''dimension''))
       (xml_nat (STR ''strictDimension''))
       (\<lambda>domain di sd. case domain 0 of
         Natural _ \<Rightarrow> Int_mat di sd
       | Integer \<Rightarrow> Int_mat di sd
       | Rational _ _  \<Rightarrow> Rat_mat di sd
       | Mini_Alg _ _  \<Rightarrow> Mini_Alg_mat di sd
       | Arctic \<Rightarrow> Arctic_mat di
       | Arctic_rat \<Rightarrow> Arctic_rat_mat di
       )
    XMLor (XMLdo (STR ''coreMatrixInterpretation'') {
      domain \<leftarrow> xml_singleton (STR ''domain'') CPF_Proof_Parser.basic_domain id;
      di \<leftarrow> xml_nat (STR ''dimension'');
      ids \<leftarrow> xml_many (STR ''indices'') CPF_Proof_Parser.nat_coeff (map (\<lambda> x. x - 1));
      m \<leftarrow> XMLdo (STR ''mode'') { 
         m \<leftarrow> (xml_leaf (STR ''E'') E_I XMLor xml_leaf (STR ''M'') M_I);
         xml_return m};
      let b = (case domain 0 of Natural _ \<Rightarrow> True | Integer \<Rightarrow> True | _ \<Rightarrow> False);
      if b then xml_return (Int_core_mat di ids m)
        else xml_error (STR ''domain must be integers in coreMatrixInterpretation'')}
      )
    XMLor xml_pair (STR ''polynomial'')
       (xml_singleton (STR ''domain'') (
          CPF_Proof_Parser.basic_domain
          XMLor xml_triple (STR ''matrices'')
            (xml_nat (STR ''dimension''))
            (xml_nat (STR ''strictDimension''))
            (xml_singleton (STR ''domain'') CPF_Proof_Parser.basic_domain id)
            (\<lambda>di sd domain d. case domain d of
               Natural _ \<Rightarrow> Int_mat di sd
             | Rational _ _ \<Rightarrow> Rat_mat di sd
             | Mini_Alg _ _ \<Rightarrow> Mini_Alg_mat di sd
             | Integer \<Rightarrow> Int_mat di sd
             | Arctic \<Rightarrow> Arctic_mat di
             | Arctic_rat \<Rightarrow> Arctic_rat_mat di)
          ) id)
       (xml_nat (STR ''degree''))
       (\<lambda>type d. type d)
   ) id"
hide_const (open) interpretation_type


type_synonym ('f,'a) inter = "('f \<times> nat) \<times> 'a \<times> 'a list"
type_synonym ('f,'a) mat_inter = "('f \<times> nat) \<times> 'a mat \<times> 'a mat list"
type_synonym ('f,'a) nl_inter = "('f \<times> nat) \<times> (nat, 'a) poly"

datatype (dead 'f) "interpretation" =
  (* linear polynomials (with support of negative constants *)
  Int_linear_poly (int_linear_poly: "('f,int)inter")
| Rat_linear_poly  (rat_linear_poly: "('f,rat)inter")
| Arctic_linear_poly (arctic_linear_poly:  "('f,arctic)inter")
| Arctic_rat_linear_poly  (arctic_rat_linear_poly: "('f,rat arctic_delta)inter")
| Real_linear_poly  (real_linear_poly: "('f,real)inter")
  (* linear polynomials over matrices (with support of negative constants *)
| Int_matrix  (int_matrix: "('f,int)mat_inter")
| Rat_matrix  (rat_matrix: "('f,rat)mat_inter")
| Arctic_matrix  (arctic_matrix: "('f,arctic)mat_inter")
| Arctic_rat_matrix  (arctic_rat_matrix: "('f,rat arctic_delta)mat_inter")
| Real_matrix  (real_matrix: "('f,real)mat_inter")
  (* linear polynomials over matrices with the core property (without support of negative constants) *)
| Int_core_matrix (int_core_matrix: "('f, int)mat_inter")
  (* non linear polynomials (without support of negative constants) *)
| Int_non_linear_poly  (int_non_linear_poly: "('f,int)nl_inter")
| Rat_non_linear_poly  (rat_non_linear_poly: "('f,rat)nl_inter")
| Real_non_linear_poly  (real_non_linear_poly: "('f,real)nl_inter")

(* the flag bi is to indicate that we are interested in bounded increase,
   where rationals always have to be chosen as non-linear variant *)
abbreviation class_ring where
  "class_ring t \<equiv> class_semiring t ()"

abbreviation mat_ring :: "('a :: semiring_1) itself \<Rightarrow> nat \<Rightarrow> 'a mat ring" where
  "mat_ring t n \<equiv> ring_mat t n ()"

definition "xml_change' f p x = bind2 (f p) (\<lambda> e. xml_error e x) Right"

definition "interpretation" :: "bool \<Rightarrow> 'a xmlt \<Rightarrow> 'a redtriple_impl xmlt" where
  "interpretation bi xml2name = XMLdo (STR ''interpretation'') {
       type \<leftarrow> CPF_Proof_Parser.interpretation_type;
       pi \<leftarrow>* XMLdo (STR ''interpret'') {f \<leftarrow> xml2name; a \<leftarrow> (xml_nat (STR ''arity''));
         case type of
           Integer \<Rightarrow> XMLdo {
             poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.int_coeff) (xml_return o poly_of);
             xml_return (Int_non_linear_poly ((f,a),poly))}
         | NegativeInteger \<Rightarrow> XMLdo {
             poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.int_coeff) (xml_return o poly_of);
             xml_return (Int_non_linear_poly ((f,a),poly))}
         | Natural deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then let c = class_ring (TYPE(int)) in
              (XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.int_coeff) (xml_change' (lpoly_of c));
               xml_return (Int_linear_poly ((f,a),(fst poly, fit_length c a (snd poly))))})
              else
              XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.int_coeff) (xml_return o poly_of);
               xml_return (Int_non_linear_poly ((f,a),poly))}
         | Rational d deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then let c = class_ring (TYPE(rat)) in
              (XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial xml_rat) (xml_change' (lpoly_of c));
               xml_return (Rat_linear_poly ((f,a),(fst poly, fit_length c a (snd poly))))})
              else
              XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial xml_rat) (xml_return o poly_of);
               xml_return (Rat_non_linear_poly ((f,a),poly))}
         | Mini_Alg d deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then let c = class_ring (TYPE(real)) in
              (XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial xml_real) (xml_change' (lpoly_of c));
               xml_return (Real_linear_poly ((f,a),(fst poly, fit_length c a (snd poly))))})
              else
              XMLdo {
               poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial xml_real) (xml_return o poly_of);
               xml_return (Real_non_linear_poly ((f,a),poly))}
         | Arctic \<Rightarrow> let c = class_ring (TYPE(arctic)) in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.arctic_coeff) (xml_change' (lpoly_of c));
                 xml_return (Arctic_linear_poly ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Arctic_rat \<Rightarrow> let c = class_ring (TYPE(rat arctic_delta)) in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial CPF_Proof_Parser.arctic_rat_coeff) (xml_change' (lpoly_of c));
                 xml_return (Arctic_rat_linear_poly ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Int_mat n sd \<Rightarrow> let c = mat_ring (TYPE(int)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 CPF_Proof_Parser.int_coeff)) (xml_change' (lpoly_of c));
                 xml_return (Int_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Rat_mat n sd \<Rightarrow> let c = mat_ring (TYPE(rat)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 xml_rat)) (xml_change' (lpoly_of c));
                 xml_return (Rat_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Int_core_mat n ids m \<Rightarrow> let c = mat_ring (TYPE(int)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 CPF_Proof_Parser.int_coeff)) (xml_change' (lpoly_of c));
                 xml_return (Int_core_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Mini_Alg_mat n sd \<Rightarrow> let c = mat_ring (TYPE(real)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 xml_real)) (xml_change' (lpoly_of c));
                 xml_return (Real_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Arctic_mat n \<Rightarrow> let c = mat_ring (TYPE(arctic)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 CPF_Proof_Parser.arctic_coeff)) (xml_change' (lpoly_of c));
                 xml_return (Arctic_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
         | Arctic_rat_mat n \<Rightarrow> let c = mat_ring (TYPE(rat arctic_delta)) n in
              (XMLdo {
                 poly \<leftarrow> xml_change (CPF_Proof_Parser.polynomial(CPF_Proof_Parser.mat_coeff n 0 CPF_Proof_Parser.arctic_rat_coeff)) (xml_change' (lpoly_of c));
                 xml_return (Arctic_rat_matrix ((f,a),(fst poly, fit_length c a (snd poly))))})
       };
       xml_return (case type of
            Natural deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then Int_carrier (map int_linear_poly pi) else Int_nl_carrier (map int_non_linear_poly pi)
          | Integer \<Rightarrow> Int_nl_carrier (map int_non_linear_poly pi)
          | NegativeInteger \<Rightarrow> Neg_Integer_Poly (map int_non_linear_poly pi)
          | Rational d deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then Rat_carrier (map rat_linear_poly pi) else Rat_nl_carrier d (map rat_non_linear_poly pi)
          | Mini_Alg d deg \<Rightarrow> if deg \<le> 1 \<and> \<not> bi then Real_carrier (map real_linear_poly pi) else Real_nl_carrier d (map real_non_linear_poly pi)
          | Arctic \<Rightarrow> Arctic_carrier (map arctic_linear_poly pi)
          | Arctic_rat \<Rightarrow> Arctic_rat_carrier (map arctic_rat_linear_poly pi)
          | Int_mat n sd \<Rightarrow> Int_mat_carrier n sd (map int_matrix pi)
          | Rat_mat n sd \<Rightarrow> Rat_mat_carrier n sd (map rat_matrix pi)
          | Int_core_mat n ids m \<Rightarrow> Core_matrix (Core_Matrix_Inter m n ids
                        (map (\<lambda>(f, c, cs). (f, cs, c)) (map int_core_matrix pi)))
          | Mini_Alg_mat n sd \<Rightarrow> Real_mat_carrier n sd (map real_matrix pi)
          | Arctic_mat n \<Rightarrow> Arctic_mat_carrier n (map arctic_matrix pi)
          | Arctic_rat_mat n \<Rightarrow> Arctic_rat_mat_carrier n (map arctic_rat_matrix pi)
      )
    }
  "
hide_const (open) "interpretation"

definition bounds_type :: "boundstype xmlt" where
  "bounds_type = xml_singleton (STR ''type'') (
     xml_leaf (STR ''roof'') Roof
     XMLor xml_leaf (STR ''match'') Match
   ) id"

definition bounds_bound :: "nat xmlt" where
  "bounds_bound = xml_nat (STR ''bound'')"


definition ta_bounds_lhs where
  "ta_bounds_lhs xml2name = XMLdo (STR ''lhs'') {
    XMLdo {
      a \<leftarrow> state;
      xml_return (Inr a)
    } XMLor XMLdo {
      f \<leftarrow> xml2name;
      h \<leftarrow> xml_nat (STR ''height'');
      qs \<leftarrow>* state;
      xml_return (Inl ((f, h), qs))
    }
  }"


definition closed_criterion :: "string ta_relation xmlt" where
 "closed_criterion = XMLdo (STR ''criterion'') {
    ret \<leftarrow>
      xml_leaf (STR ''compatibility'') Id_Relation
      XMLor xml_singleton (STR ''stateCompatibility'') (
        XMLdo (STR ''relation'') {
          ret \<leftarrow>* xml_pair (STR ''entry'') state state Pair;
          xml_return ret
        }
      ) Some_Relation
      XMLor xml_leaf (STR ''decisionProcedure'') Decision_Proc
      XMLor xml_leaf (STR ''decisionProcedureOld'') Decision_Proc_Old;
    xml_return ret
  }"

definition bounds_info :: "'a xmlt \<Rightarrow> ('a, string) bounds_info xmlt"
  where
    "bounds_info xml2name = XMLdo (STR ''bounds'') {
      a \<leftarrow> bounds_type;
      b \<leftarrow> bounds_bound;
      c \<leftarrow> final_states;
      d \<leftarrow> tree_automaton (ta_bounds_lhs xml2name);
      e \<leftarrow>[Id_Relation] closed_criterion;
      xml_return (Bounds_Info a b c d e)
    }"

context
  fixes xml2name :: "'a :: showl xmlt"
    and termIndexMap :: "'a termIndexMap"
    and ruleMap :: "'a ruleIndexMap" 
    and shp :: "'a \<Rightarrow> 'a" 
begin

partial_function (sum_bot) ctxt ::  "('a, string) ctxt xmlt"
where
 [code]: "ctxt x = (
    XMLdo (STR ''box'') {xml_return Hole}
    XMLor XMLdo (STR ''funContext'') {
      name \<leftarrow> xml2name;
      left \<leftarrow> XMLdo (STR ''before'') {
        left \<leftarrow>* term xml2name termIndexMap;
        xml_return left
      };
      mid \<leftarrow> ctxt;
      right \<leftarrow> XMLdo (STR ''after'') {
        right \<leftarrow>* term xml2name termIndexMap;
        xml_return right
      };
      xml_return (More name left mid right)
   }) x"


definition flat_contexts :: "('a, string) ctxt list xmlt" where "flat_contexts =
  xml_do (STR ''flatContexts'') (xml_take_many 0 \<infinity> ctxt xml_return)"

definition subst :: "('a, string) substL xmlt"
  where
    "subst = XMLdo (STR ''substitution'') {
      list \<leftarrow>* XMLdo (STR ''substEntry'') {
        var \<leftarrow> xml_do (STR ''var'') (xml_take_text xml_return);
        trm \<leftarrow> term xml2name termIndexMap;
        xml_return (var,trm)
      };
      xml_return list
    }"

definition afs :: "'a afs_list xmlt"
  where
    "afs = XMLdo (STR ''argumentFilter'') {
      ret \<leftarrow>* XMLdo (STR ''argumentFilterEntry'') {
        name \<leftarrow> xml2name;
        arity \<leftarrow> xml_nat (STR ''arity'');
        main \<leftarrow> xml_change (xml_nat (STR ''collapsing'')) (\<lambda>n. xml_return (Collapse (n - 1)))
          XMLor XMLdo (STR ''nonCollapsing'') {
            ls \<leftarrow>* position;
            xml_return (AFList ls)
          };
        xml_return ((name, arity), main)
      };
      xml_return ret
    }"

definition proj :: "'a projL xmlt" where
  "proj = xml_change (CPF_Proof_Parser.afs xml2name) (\<lambda>afl. xml_return (Projection
    (map (\<lambda>(fa, e). case e of
      Collapse i \<Rightarrow> Pair fa i
    | _ \<Rightarrow> Pair fa (snd fa)) afl)))"


definition multiset_af :: "'a status_impl xmlt" where
  "multiset_af = XMLdo (STR ''multisetArgumentFilter'') {
    ret \<leftarrow>* XMLdo (STR ''multisetArgumentFilterEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_do (STR ''status'') (xml_take_many 0 \<infinity> position xml_return);
      xml_return ((f,a), p)
    };
    xml_return ret
  }"

definition
  relstep :: "(pos \<times> ('a, string) rule \<times> bool \<times> ('a, string) term) xmlt"
where
  "relstep = XMLdo (STR ''rewriteStep'') {
    p \<leftarrow> pos;
    r \<leftarrow> rule xml2name termIndexMap ruleMap;
    rel \<leftarrow>? xml_leaf (STR ''relative'') ();
    t \<leftarrow> term xml2name termIndexMap;
    xml_return (p, r, rel = None, t)
  }"

definition
  rstep :: "(pos \<times> ('a, string) rule \<times> ('a, string) term) xmlt"
where
  "rstep = XMLdo (STR ''rewriteStep'') {
    p \<leftarrow> pos;
    r \<leftarrow> rule xml2name termIndexMap ruleMap;
    t \<leftarrow> term xml2name termIndexMap;
    xml_return (p, r, t)
  }"

definition
  estep :: "(pos \<times> ('a, string) rule \<times> bool \<times> ('a, string) term) xmlt"
where
  "estep = XMLdo (STR ''equationStep'') {
    p \<leftarrow> pos;
    r \<leftarrow> rule xml2name termIndexMap ruleMap;
    b \<leftarrow> xml_leaf (STR ''leftRight'') True XMLor xml_leaf (STR ''rightLeft'') False;
    t \<leftarrow> term xml2name termIndexMap;
    xml_return (p, r, b, t)
  }"

definition
  relsteps :: "(('a,string)term \<times> ('a,string)prseq) xmlt"
where
  "relsteps = XMLdo (STR ''rewriteSequence'') {
    start \<leftarrow> xml_singleton (STR ''startTerm'') (term xml2name termIndexMap) id;
    steps \<leftarrow>* relstep;
    xml_return (start, steps)
  }"

definition
  rsteps :: "(('a, string) term \<times> ('a, string) rseq) xmlt"
where
  "rsteps = XMLdo (STR ''rewriteSequence'') {
    start \<leftarrow> xml_singleton (STR ''startTerm'') (term xml2name termIndexMap) id;
    steps \<leftarrow>* rstep;
    xml_return (start, steps)
  }"


definition pat_eqv_prf :: "('a, string) pat_eqv_prf xmlt"
  where
    "pat_eqv_prf =
      (let sub = subst in
      xml_singleton (STR ''patternEquivalence'') (
        XMLdo (STR ''domainRenaming'') {n \<leftarrow> sub; xml_return (Pat_Dom_Renaming n)}
        XMLor XMLdo (STR ''irrelevant'') {n \<leftarrow> sub; n2 \<leftarrow> sub; xml_return (Pat_Irrelevant n n2)}
        XMLor XMLdo (STR ''simplification'') {n \<leftarrow> sub; n2 \<leftarrow> sub; xml_return (Pat_Simplify n n2)}
      ) id)"

definition pat_term :: "(('a,string)term \<times> ('a,string)substL \<times> ('a,string)substL) xmlt"
  where
    "pat_term = XMLdo (STR ''patternTerm'') {
      t \<leftarrow> term xml2name termIndexMap;
      s1 \<leftarrow> subst;
      s2 \<leftarrow> subst;
      xml_return (t,s1,s2)
    }"

abbreviation (input) pat_rule_fun where "pat_rule_fun x pat \<equiv> (let
   sub = subst;
   pt = pat_term;
   var = xml_text (STR ''var'')
in
(XMLdo (STR ''patternRule'') {
  pt1 \<leftarrow> pt;
  pt2 \<leftarrow> pt;
  z \<leftarrow> XMLdo (STR ''originalRule'') {
      r \<leftarrow> rule xml2name termIndexMap ruleMap;
      b \<leftarrow> xml_bool (STR ''isPair'');
      xml_return (Pat_OrigRule r b)
    } XMLor XMLdo (STR ''initialPumping'') {
      a \<leftarrow> pat;
      b \<leftarrow> sub;
      c \<leftarrow> sub;
      xml_return (Pat_InitPump a b c)
    } XMLor XMLdo (STR ''initialPumpingContext'') {
      a \<leftarrow> pat;
      b \<leftarrow> sub;
      c \<leftarrow> pos;
      d \<leftarrow> var;
      xml_return (Pat_InitPumpCtxt a b c d)
    } XMLor XMLdo (STR ''equivalence'') {
      a \<leftarrow> pat;
      b \<leftarrow> xml_leaf (STR ''left'') True XMLor xml_leaf (STR ''right'') False;
      c \<leftarrow> pat_eqv_prf;
      xml_return (Pat_Equiv a b c)
    } XMLor XMLdo (STR ''narrowing'') {
      a \<leftarrow> pat;
      b \<leftarrow> pat;
      c \<leftarrow> pos;
      xml_return (Pat_Narrow a b c)
    } XMLor XMLdo (STR ''instantiation'') {
      a \<leftarrow> pat;
      b \<leftarrow> sub;
      c \<leftarrow> xml_leaf (STR ''base'') Pat_Base XMLor xml_leaf (STR ''pumping'') Pat_Pump XMLor xml_leaf (STR ''closing'') Pat_Close;
      xml_return (Pat_Inst a b c)
    } XMLor XMLdo (STR ''instantiationPumping'') {
      a \<leftarrow> pat;
      b \<leftarrow> xml_nat (STR ''power'');
      xml_return (Pat_Exp_Sigma a b)
    } XMLor XMLdo (STR ''rewriting'') {
      a \<leftarrow> pat;
      b \<leftarrow> rsteps;
      (po,va) \<leftarrow>
        xml_leaf (STR ''base'') (Pat_Base,[])
        XMLor XMLdo (STR ''pumping'') { v \<leftarrow> var; xml_return (Pat_Pump,v) }
        XMLor XMLdo (STR ''closing'') { v \<leftarrow> var; xml_return (Pat_Close,v) };
      xml_return (Pat_Rewr a b po va)
    };
   xml_return z
  }) x)"

partial_function (sum_bot) pat_rule_prf :: "('a,string)pat_rule_prf xmlt"
  where "pat_rule_prf x = pat_rule_fun x pat_rule_prf"

(* one cannot put the 'let pat = ... ' directly into partial function, since then the monotonicity fails *)
lemma pat_rule_prf [code]:
  "pat_rule_prf x = (let pat = pat_rule_prf in pat_rule_fun x pat)"
     unfolding pat_rule_prf.simps[of x] Let_def by simp

definition
  conversion :: "('a,string)term list xmlt"
where
  "conversion = XMLdo (STR ''conversion'') {
    a \<leftarrow>* term xml2name termIndexMap;
    xml_return a
  }"

definition subsumption_proof :: "('a,string)subsumption_proof xmlt"
where "subsumption_proof = XMLdo (STR ''subsumptionProof'') {
  ret \<leftarrow>* XMLdo (STR ''ruleSubsumptionProof'') {
    r \<leftarrow> rule xml2name termIndexMap ruleMap;
    e \<leftarrow> conversion;
    xml_return (r, e)
  };
  xml_return ret
}"

definition xml2crit_pair_info :: "('a,string)crit_pair_info xmlt" where
  "xml2crit_pair_info = XMLdo (STR ''critPairInfo'') {
     s \<leftarrow> xml_singleton (STR ''left'') (term xml2name termIndexMap) id;
     t \<leftarrow>? xml_singleton (STR ''peak'') (term xml2name termIndexMap) id;
     u \<leftarrow> xml_singleton (STR ''right'') (term xml2name termIndexMap) id;
     pos \<leftarrow>? XMLdo (STR ''overlapPositions'') {
         ps \<leftarrow>* pos;
         xml_return ps};
     labels \<leftarrow>? XMLdo (STR ''labels'') {
         left \<leftarrow> xml_nat (STR ''maxLeft'');
         right \<leftarrow> xml_nat (STR ''right'');
         xml_return (left,right)};
     joins \<leftarrow> XMLdo (STR ''intermediateTerms'') {
          ts \<leftarrow>* term xml2name termIndexMap;
          xml_return ts };
     xml_return (Crit_Pair_Info s t u joins pos labels)
    }" 

definition "joinAutoBfs = xml_change (xml_int (STR ''joinAutoBfs'')) (\<lambda> x. xml_return (if x < 0 then None else Some (nat x)))" 
definition "joinAutoBfs1 = xml_change joinAutoBfs (\<lambda> x. xml_return (case x of Some n \<Rightarrow> n | _ \<Rightarrow> 1))" 
definition "joinSequences = XMLdo (STR ''joinSequences'') {
            joins \<leftarrow>* xml2crit_pair_info; 
            xml_return joins}"

definition xml2cp_join_info :: "('a,string) cp_join_hints xmlt" where
  "xml2cp_join_info = xml_change joinAutoBfs1 (xml_return o CP_Auto)
      XMLor xml_change joinSequences (\<lambda> joins. xml_return (CP_Sequences joins))" 


definition wcr_proof :: "('a,string) join_info xmlt"
  where "wcr_proof = xml_singleton (STR ''wcrProof'') (
    xml_change (xml2cp_join_info) (xml_return \<circ> Guided_BFS )
    XMLor xml_leaf (STR ''joinAutoNF'') Join_NF
  ) id"

definition
  loop ::
    "(('a, string) term \<times> ('a, string) prseq \<times> ('a, string) substL \<times> ('a, string) ctxt) xmlt"
where [code]:
  "loop = XMLdo (STR ''loop'') {
    (s,rseq) \<leftarrow> relsteps;
    \<sigma> \<leftarrow> subst;
    c \<leftarrow> ctxt;
    xml_return (s, rseq, \<sigma>, c)
  }"

definition
  start_term :: "('a, string) term \<Rightarrow> ('a, string) term xmlt"
where
  "start_term t = XMLdo (STR ''startTerm'') {
    s \<leftarrow> term xml2name termIndexMap;
    if s = t then xml_return t
    else xml_error (STR ''<startTerm> does not match lhs'')
  }"

definition
  rseq ::
    "'a proj \<Rightarrow> ('a, string) rule \<Rightarrow> (('a,string)rule \<times> ('a,string)rseq)xmlt"
where
  "rseq \<pi> r = XMLdo (STR ''rewriteSequence'') {
     _ \<leftarrow> start_term (proj_term \<pi> (fst r));
     rseq \<leftarrow>* rstep;
     xml_return (r, rseq)
  }"

definition
  projected_rseq ::
    "'a proj \<Rightarrow> (('a, string) rule \<times> ('a,string)rseq) xmlt"
where
  "projected_rseq \<pi> =
    XMLdo (STR ''projectedRewriteSequence'') {
      r \<leftarrow> rule xml2name termIndexMap ruleMap;
      ret \<leftarrow> rseq \<pi> r;
      xml_return ret
    }"

definition rule_labeling_function :: "(_, string) rule_lab_repr xmlt"
where
  "rule_labeling_function = xml_many (STR ''ruleLabelingFunction'')
   (xml_pair (STR ''ruleLabelingFunctionEntry'')
    (rule xml2name termIndexMap ruleMap)
    (xml_nat (STR ''label''))
    Pair) id"

definition status_precedence :: "('a status_prec_repr) xmlt" where
  "status_precedence = XMLdo (STR ''statusPrecedence'') {
    ret \<leftarrow>* XMLdo (STR ''statusPrecedenceEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_nat (STR ''precedence'');
      s \<leftarrow> xml_leaf (STR ''lex'') Lex XMLor xml_leaf (STR ''mul'') Mul;
      xml_return ((f,a), (p,s))
    };
    xml_return ret
  }"

definition path_order :: "'a redtriple_impl xmlt"
  where
    "path_order = XMLdo (STR ''recursivePathOrder'') {
      prec\<tau> \<leftarrow> CPF_Proof_Parser.status_precedence xml2name;
      af \<leftarrow>[[]] CPF_Proof_Parser.afs xml2name;
      xml_return (RPO prec\<tau> af)
    }"

definition precedence_weight :: "(nat \<Rightarrow> 'a prec_weight_repr) xmlt"
  where
    "precedence_weight = XMLdo (STR ''precedenceWeight'') {
      ret \<leftarrow>* XMLdo (STR ''precedenceWeightEntry'') {
        f \<leftarrow> xml2name;
        a \<leftarrow> xml_nat (STR ''arity'');
        p \<leftarrow> xml_nat (STR ''precedence'');
        w \<leftarrow> xml_nat (STR ''weight'');
        e \<leftarrow>? XMLdo (STR ''subtermCoefficientEntries'') {
          ret \<leftarrow>* xml_nat (STR ''entry'');
          xml_return ret
        };
        xml_return ((f,a), (p,w,e))
      };
      xml_return (Pair ret)
    }"

definition precedence_weight_ac :: "(nat \<Rightarrow> 'a prec_weight_ac_repr) xmlt" where
  "precedence_weight_ac = XMLdo (STR ''precedenceWeight'') {
    ret \<leftarrow>* XMLdo (STR ''precedenceWeightEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_nat (STR ''precedence'');
      w \<leftarrow> xml_nat (STR ''weight'');
      e \<leftarrow>[False] xml_bool (STR ''isAC'');
      xml_return ((f,a), (p,w,e))
    };
    xml_return (Pair ret)
  }"

definition wpo_params :: "'a wpo_params xmlt" where
  "wpo_params = XMLdo (STR ''precedenceStatus'') {
    ret \<leftarrow>* XMLdo (STR ''precedenceStatusEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_nat (STR ''precedence'');
      ot \<leftarrow>? (xml_leaf (STR ''lex'') Lex XMLor xml_leaf (STR ''mul'') Mul);
      s \<leftarrow> XMLdo (STR ''status'') {ps \<leftarrow>* position; xml_return ps};
      xml_return ((f,a), (p,s, case ot of Some lm \<Rightarrow> lm | None \<Rightarrow> Lex))
    };
    xml_return ret
  }"

definition precedence_list :: "((('a \<times> nat) \<times> nat) list) xmlt" where
  "precedence_list = XMLdo (STR ''precedenceList'') {
    ret \<leftarrow>* XMLdo (STR ''precedenceListEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      p \<leftarrow> xml_nat (STR ''precedence'');
      xml_return ((f,a), p)
    };
    xml_return ret
  }"

definition knuth_bendix_order :: "'a redtriple_impl xmlt" where
  "knuth_bendix_order = XMLdo (STR ''knuthBendixOrder'') {
   w0 \<leftarrow> xml_nat (STR ''w0'');
   prw \<leftarrow> CPF_Proof_Parser.precedence_weight xml2name;
   afs \<leftarrow>[[]] CPF_Proof_Parser.afs xml2name;
   xml_return (KBO (prw w0) afs)
  }"

definition ac_knuth_bendix_order :: "'a redtriple_impl xmlt" where
  "ac_knuth_bendix_order = XMLdo (STR ''ACKBO'') {
   w0 \<leftarrow> xml_nat (STR ''w0'');
   prw \<leftarrow> CPF_Proof_Parser.precedence_weight_ac xml2name;
   afs \<leftarrow>[[]] CPF_Proof_Parser.afs xml2name;
   xml_return (ACKBO (prw w0) afs)
  }"

partial_function (sum_bot) max_poly_parser :: "(max_poly.sig, nat) term xmlt" where
  [code]: "max_poly_parser xml = (
  XMLdo (STR ''product'') {
    exps \<leftarrow>* max_poly_parser;
    xml_return (Fun max_poly.ProdF exps)
  } XMLor XMLdo (STR ''sum'') {
    exps \<leftarrow>* max_poly_parser;
    xml_return (Fun max_poly.SumF exps)
  } XMLor XMLdo (STR ''max'') {
    exps \<leftarrow>^{1..\<infinity>} max_poly_parser;
    xml_return (Fun max_poly.MaxF exps)
  } XMLor XMLdo (STR ''constant'') {n \<leftarrow>nat; xml_return (max_poly.const n)}
    XMLor XMLdo (STR ''variable'') {n \<leftarrow>nat; xml_return (Var (n - 1))}
  ) xml"

partial_function (sum_bot) max_monus_parser :: "(max_monus.sig, nat) term xmlt" where
  [code]: "max_monus_parser xml = (
  XMLdo (STR ''sum'') {
    exps \<leftarrow>* max_monus_parser;
    xml_return (Fun max_monus.SumF exps)
  } XMLor XMLdo (STR ''max'') {
    exps \<leftarrow>^{1..\<infinity>} max_monus_parser;
    xml_return (Fun max_monus.MaxF exps)
  } XMLor XMLdo (STR ''maxExt'') {
    c0 \<leftarrow> xml_nat (STR ''min'');
    cdes \<leftarrow>* (XMLdo (STR ''maxExtEntry'') {
      c \<leftarrow> xml_int (STR ''intercept'');
      d \<leftarrow> xml_nat (STR ''slope'');
      e \<leftarrow> max_monus_parser;
      xml_return ((c, d), e)
    });
    xml_return (Fun (max_monus.MaxExtF c0 (map fst cdes)) (map snd cdes))
  } XMLor XMLdo (STR ''constant'') {n \<leftarrow>nat; xml_return (max_monus.const n)}
    XMLor XMLdo (STR ''variable'') {n \<leftarrow>nat; xml_return (Var (n - 1))}
  ) xml"

definition level_mapping :: "'a scnp_af xmlt" where
  "level_mapping = XMLdo (STR ''levelMapping'') {
    ret \<leftarrow>* XMLdo (STR ''levelMappingEntry'') {
      f \<leftarrow> xml2name;
      a \<leftarrow> xml_nat (STR ''arity'');
      ps \<leftarrow>* xml_pair (STR ''positionLevelEntry'')
         (xml_nat (STR ''position''))
         (xml_nat (STR ''level''))
         Pair;
      xml_return ((f,a), map (\<lambda> (p,l). (if p = 0 then a else p - 1,l)) ps)
    };
    xml_return ret
  }"

partial_function (sum_bot) redtriple :: "bool \<Rightarrow> 'a redtriple_impl xmlt" where
  [code]: "redtriple bi xml = (
    path_order
    XMLor knuth_bendix_order
    XMLor ac_knuth_bendix_order
    XMLor CPF_Proof_Parser.interpretation bi xml2name
    XMLor XMLdo (STR ''maxPoly'') {
      inters \<leftarrow>* XMLdo (STR ''interpret'') {
        f \<leftarrow> xml2name;
        a \<leftarrow> xml_nat (STR ''arity'');
        e \<leftarrow> max_poly_parser;
        xml_return ((f, a), e)
      };
      xml_return (Max_poly inters)
    } XMLor XMLdo (STR ''maxMonus'') {
      inters \<leftarrow>* XMLdo (STR ''interpret'') {
        f \<leftarrow> xml2name;
        a \<leftarrow> xml_nat (STR ''arity'');
        e \<leftarrow> max_monus_parser;
        xml_return ((f, a), e)
      };
      xml_return (Max_monus inters)
    } XMLor XMLdo (STR ''coWeightedPathOrder'') {
      a \<leftarrow> wpo_params;
      b \<leftarrow> redtriple bi;
      xml_return (COWPO a b)
    } XMLor XMLdo (STR ''weightedPathOrder'') {
      a \<leftarrow> wpo_params;
      b \<leftarrow> redtriple bi;
      xml_return (WPO a b)
    } XMLor XMLdo (STR ''generalizedWeightedPathOrder'') {
      pr \<leftarrow> precedence_list;
      b \<leftarrow> redtriple bi;
      xml_return (GWPO (pr, shp) b)
    } XMLor XMLdo (STR ''monotonicSemanticPathOrder'') {
      a \<leftarrow> redtriple bi;
      xml_return (MSPO a)
    } XMLor XMLdo (STR ''filteredRedPair'') {
      af \<leftarrow>[[]] CPF_Proof_Parser.afs xml2name;
      b \<leftarrow> redtriple bi;
      xml_return (Filtered_Redtriple af b)
    } XMLor XMLdo (STR ''scnp'') {
      a \<leftarrow> XMLdo (STR ''status'') {
        ret \<leftarrow>
          xml_leaf (STR ''ms'') MS_Ext
          XMLor xml_leaf (STR ''min'') Min_Ext
          XMLor xml_leaf (STR ''dms'') Dms_Ext
          XMLor xml_leaf (STR ''max'') Max_Ext;
        xml_return ret
      };
      b \<leftarrow> level_mapping;
      c \<leftarrow> redtriple False;
      xml_return (SCNP a b c)
    }
   ) xml"

definition scg_position :: "nat xmlt" where
  "scg_position = xml_nat (STR ''position'')"

definition
  scg :: "(('a, string) rule \<times> ((nat \<times> nat) list \<times> (nat \<times> nat) list)) xmlt"
where
  "scg = XMLdo (STR ''sizeChangeGraph'') {
    lr \<leftarrow> rule xml2name termIndexMap ruleMap;
    edges \<leftarrow>* XMLdo (STR ''edge'') {
       p \<leftarrow> CPF_Proof_Parser.scg_position;
       s \<leftarrow> xml_bool (STR ''strict'');
       q \<leftarrow> CPF_Proof_Parser.scg_position;
       xml_return (s,(p,q))
    };
    xml_return (lr,(map snd (filter fst edges), map snd (filter (\<lambda> x. \<not> fst x) edges)))
  }"

definition uncurry_info :: "('a, string) uncurry_info xmlt" where
  "uncurry_info = XMLdo (STR ''uncurryInformation'') {
    a \<leftarrow> xml2name;
    sml \<leftarrow> XMLdo (STR ''uncurriedSymbols'') {
      ret \<leftarrow>* XMLdo (STR ''uncurriedSymbolEntry'') {
        f \<leftarrow> xml2name;
        n \<leftarrow> xml_nat (STR ''arity'');
        fs \<leftarrow>* xml2name;
        xml_return ((f, n), fs)
      };
      xml_return ret
    };
    U \<leftarrow> xml_singleton (STR ''uncurryRules'') (rules xml2name termIndexMap ruleMap) id;
    E \<leftarrow> xml_singleton (STR ''etaRules'') (rules xml2name termIndexMap ruleMap) id;
    xml_return (a, sml, U, E)
  }"

partial_function (sum_bot)
  xml2cond_constraint :: "('a,string) cond_constraint xmlt" where
  [code]: "xml2cond_constraint x = xml_singleton (STR ''conditionalConstraint'') (
    XMLdo (STR ''all'') {
      a \<leftarrow> xml_text (STR ''var'');
      b \<leftarrow> xml2cond_constraint;
      xml_return (CC_all a b)
    } XMLor XMLdo (STR ''implication'') {
      c \<leftarrow> xml2cond_constraint;
      cs \<leftarrow>* xml2cond_constraint;
      let ccs = c # cs;
      xml_return (CC_impl (take (length cs) ccs) (last ccs))
    } XMLor XMLdo (STR ''constraint'') {
      s \<leftarrow> term xml2name termIndexMap;
      rel \<leftarrow>
        xml_leaf (STR ''rewrite'') None
        XMLor xml_leaf (STR ''strict'') (Some True)
        XMLor xml_leaf (STR ''nonStrict'') (Some False);
      t \<leftarrow> term xml2name termIndexMap;
      xml_return (case rel of None \<Rightarrow> CC_rewr s t | Some stri \<Rightarrow> CC_cond stri (s,t))
    }) id x"


partial_function (sum_bot) xml2cond_constraint_prf :: "('a,string) cond_constraint_prf xmlt" where
  [code]: "xml2cond_constraint_prf x = (
  let cc = xml2cond_constraint in
  xml_singleton (STR ''conditionalConstraintProof'') (
    xml_leaf (STR ''final'') Final
    XMLor XMLdo (STR ''differentConstructor'') {
      a \<leftarrow> cc;
      xml_return (Different_Constructor a)
    } XMLor XMLdo (STR ''sameConstructor'') {
      a \<leftarrow> cc; b \<leftarrow> cc; c \<leftarrow> xml2cond_constraint_prf;
      xml_return (Same_Constructor a b c)
    } XMLor XMLdo (STR ''variableEquation'') {
      a \<leftarrow> xml_text (STR ''var''); b \<leftarrow> term xml2name termIndexMap; c \<leftarrow>  cc;
      d \<leftarrow> xml2cond_constraint_prf;
      xml_return (Variable_Equation a b c d)
    } XMLor XMLdo (STR ''funargIntoVar'') {
      a \<leftarrow> cc;
      b \<leftarrow> position;
      c \<leftarrow> xml_text (STR ''var'');
      d \<leftarrow> cc;
      e \<leftarrow> (xml2cond_constraint_prf);
      xml_return (Funarg_Into_Var a b c d e)
    } XMLor XMLdo (STR ''simplifyCondition'') {
      a \<leftarrow> cc; b \<leftarrow> subst; c \<leftarrow> cc; d \<leftarrow> (xml2cond_constraint_prf);
      xml_return (Simplify_Condition a b c d)
    } XMLor XMLdo (STR ''induction'') {
      a \<leftarrow> cc;
      b \<leftarrow> XMLdo (STR ''conjuncts'') {ret \<leftarrow>* cc; xml_return ret};
      c \<leftarrow> XMLdo (STR ''ruleConstraintProofs'') {
        ret \<leftarrow>* XMLdo (STR ''ruleConstraintProof'') {
          lr \<leftarrow> rule xml2name termIndexMap ruleMap;
          rys \<leftarrow> XMLdo (STR ''subtermVarEntries'') {
            ret \<leftarrow>* XMLdo (STR ''subtermVarEntry'') {
              a \<leftarrow> term xml2name termIndexMap;
              b \<leftarrow>* xml_text (STR ''var'');
              xml_return (a,b)
            };
            xml_return ret
          };
          cc \<leftarrow> cc;
          p \<leftarrow> xml2cond_constraint_prf;
          xml_return (lr,rys,cc,p)
        };
        xml_return ret
      };
      xml_return (Induction a b c)
    } XMLor XMLdo (STR ''deleteCondition'') {
      a \<leftarrow> cc;
      b \<leftarrow> xml2cond_constraint_prf;
      xml_return (Delete_Condition a b)
   }) id
    x)"

definition
  xml2cond_red_pair_proof :: "('a, string) cond_red_pair_prf xmlt" where
  "xml2cond_red_pair_proof = XMLdo (STR ''condRedPairProof'') {
    c \<leftarrow> xml2name;
    b \<leftarrow> xml_nat (STR ''before'');
    a \<leftarrow> xml_nat (STR ''after'');
    ccs \<leftarrow> XMLdo (STR ''conditions'') {
      ret \<leftarrow>* XMLdo (STR ''condition'') {
         c \<leftarrow> xml2cond_constraint;
         s \<leftarrow> xml_singleton (STR ''dpSequence'') (rules xml2name termIndexMap ruleMap) id;
         p \<leftarrow> xml2cond_constraint_prf;
         xml_return (c,s,p)
      };
      xml_return ret
    };
    xml_return (Cond_Red_Pair_Prf c ccs b a)
  }"

partial_function (sum_bot) xml2eq_proof :: "('a, string) eq_proof xmlt" where
  [code]: "xml2eq_proof x = (
    xml_singleton (STR ''refl'') (term xml2name termIndexMap) Equational_Reasoning.Refl
    XMLor xml_singleton (STR ''sym'') xml2eq_proof Sym
    XMLor xml_pair (STR ''trans'') xml2eq_proof xml2eq_proof Trans
    XMLor xml_pair (STR ''assm'') (rule xml2name termIndexMap ruleMap) subst (\<lambda>r s. Assm r (mk_subst Var s))
    XMLor XMLdo (STR ''cong'') {
      a \<leftarrow> xml2name;
      b \<leftarrow>* xml2eq_proof;
      xml_return (Cong a b)
   }) x"


definition renaming :: "('a \<times> 'a)list xmlt" where
  "renaming = XMLdo (STR ''renaming'') {
    ret \<leftarrow>* XMLdo (STR ''renamingEntry'') {
      a \<leftarrow> xml2name;
      b \<leftarrow> xml2name;
      xml_return (a,b)
    };
    xml_return ret
  }"

definition symbols_no_arity :: "ltag \<Rightarrow> 'a list xmlt"
where
  "symbols_no_arity tagname =
    XMLdo tagname {ret \<leftarrow>* xml2name; xml_return ret}"

text \<open>
  Parse a list of pairs of rules, where the first argument gives the name of the outermost tag
  and the second argument the name of the tag around each pair.
\<close>
definition
  rule_pairs :: "ltag \<Rightarrow> ltag \<Rightarrow> (('a, string) rule \<times> ('a, string) rule) list xmlt"
where
  "rule_pairs s p = XMLdo s {
    ret \<leftarrow>* xml_pair p
      (rule xml2name termIndexMap ruleMap)
      (rule xml2name termIndexMap ruleMap)
      Pair;
    xml_return ret
  }"

definition xml2dp_input' where
  "xml2dp_input' termination = xml_change (dp_input xml2name termIndexMap ruleMap)
    (\<lambda>ret. case ret of DP_input m p q r \<Rightarrow>
     xml_return (if termination then default_nfs_dp else default_nfs_nt_dp, m, p, [], strategy_to_Q q r, [], r))"


(* TODO: 
definition xml2inn_fp_trs_assm where
  "xml2inn_fp_trs_assm = xml_change (xml2_trs_input xml2name) (\<lambda>inp.
    case inp of
      Inn_TRS_input inn r s start \<Rightarrow>
        if start \<noteq> start_term.Full then
          xml_error (STR ''start term is not allowed here'')
        else
          xml_return (Inl (default_nfs_trs, strategy_to_Q inn r, r, s))
    | FP_TRS_input fp r \<Rightarrow> xml_return (Inr (strategy_to_fp fp r, r))
    | _ \<Rightarrow> xml_error (STR ''trs as input required'')
  )"

definition xml2inn_trs_assm where
  "xml2inn_trs_assm = xml_change xml2inn_fp_trs_assm (\<lambda>inp.
    case inp of
      Inl i \<Rightarrow> xml_return i
    | _ \<Rightarrow> xml_error (STR ''innermost (relative) TRS expected at this point'')
   )"

definition xml2fp_trs_assm where
  "xml2fp_trs_assm = xml_change xml2inn_fp_trs_assm (\<lambda>inp.
    case inp of
      Inr i \<Rightarrow> xml_return i
    | _ \<Rightarrow> xml_error (STR ''FP TRS expected at this point'')
   )"

definition xml2complexity_input' where
  "xml2complexity_input' = xml_change xml2complexity_input
    (\<lambda> ret. case ret of CPX_input q s w cm cc \<Rightarrow> xml_return (strategy_to_Q q (s @ w), s, w, cm,cc))"
*)
definition "xml2inn_trs_assm = undefined"
definition "xml2fp_trs_assm = undefined"
definition "xml2inn_fp_trs_assm = undefined" 
definition "xml2complexity_input' = undefined" 


end


context fixes xml2name :: "('f :: {showl,compare_order}, 'l :: {showl,compare_order}) lab xmlt"
  and termIndexMap :: "('f,'l)lab termIndexMap"
  and ruleMap :: "('f,'l)lab ruleIndexMap" 
begin

abbreviation "red_triple \<equiv> redtriple xml2name Sharp" 

partial_function_mr (sum_bot)
  xml2dp_termination_proof :: "('f, 'l, string) dp_termination_proof xmlt"
  and xml2trs_termination_proof :: "('f, 'l, string) trs_termination_proof xmlt"
  and xml2fptrs_termination_proof :: "('f, 'l, string) fptrs_termination_proof xmlt"
  and xml2unknown_proof :: "('f, 'l, string) unknown_proof xmlt"
  and xml2subproof
where
  "xml2dp_termination_proof x =
  xml_singleton (STR ''dpProof'') (
    XMLdo (STR ''pIsEmpty'') {
      xml_return P_is_Empty
    } XMLor XMLdo (STR ''depGraphProc'') {
      a \<leftarrow>* XMLdo (STR ''component'') {
        dps \<leftarrow> (xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id);
        prfOpt \<leftarrow>? xml2dp_termination_proof;
        xml_return (prfOpt, dps)
      };
      xml_return (Dep_Graph_Proc a)
    } XMLor XMLdo (STR ''redPairProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2dp_termination_proof;
      xml_return (Redpair_Proc a b c)
    } XMLor XMLdo (STR ''usableRulesProc'') {
      a \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml2dp_termination_proof;
      xml_return (Usable_Rules_Proc a b)
    } XMLor XMLdo (STR ''innermostLhssRemovalProc'') {
      a \<leftarrow> innermostLhss xml2name termIndexMap;
      b \<leftarrow> xml2dp_termination_proof;
      xml_return (Q_Reduction_Proc a b)
    } XMLor XMLdo (STR ''rewritingProc'') {
      (s,t) \<leftarrow> rule xml2name termIndexMap ruleMap;
      (p,lr,t') \<leftarrow> rstep xml2name termIndexMap ruleMap;
      st'' \<leftarrow>[(s,t')] rule xml2name termIndexMap ruleMap;
      ur \<leftarrow>? xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      prof \<leftarrow> xml2dp_termination_proof;
      xml_return (Rewriting_Proc ur (s,t) (s,t') st'' lr p prof)
    } XMLor XMLdo (STR ''narrowingProc'') {
      a \<leftarrow> rule xml2name termIndexMap ruleMap;
      b \<leftarrow> pos;
      c \<leftarrow> xml_singleton (STR ''narrowings'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml2dp_termination_proof;
      xml_return (Narrowing_Proc a b c d)
    } XMLor XMLdo (STR ''instantiationProc'') {
      a \<leftarrow> rule xml2name termIndexMap ruleMap;
      b \<leftarrow> xml_singleton (STR ''instantiations'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2dp_termination_proof;
      xml_return (Instantiation_Proc a b c)
    } XMLor XMLdo (STR ''forwardInstantiationProc'') {
      a \<leftarrow> rule xml2name termIndexMap ruleMap;
      b \<leftarrow> xml_singleton (STR ''instantiations'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow>? xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml2dp_termination_proof;
      xml_return (Forward_Instantiation_Proc a b c d)
    } XMLor XMLdo (STR ''semlabProc'') {
      sli \<leftarrow> CPF_Proof_Parser.sl_variant xml2name;
      lp \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      lr \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      lq \<leftarrow>[[]] innermostLhss xml2name termIndexMap;
      p \<leftarrow> xml2dp_termination_proof;
      xml_return (Semlab_Proc sli lp lq lr p)
    } XMLor XMLdo (STR ''subtermProc'') {
      pi_mpi \<leftarrow> xml_change (CPF_Proof_Parser.proj xml2name) (xml_return \<circ> Inl)
        XMLor xml_change (CPF_Proof_Parser.multiset_af xml2name) (xml_return \<circ> Inr);
      seq \<leftarrow>* CPF_Proof_Parser.projected_rseq xml2name termIndexMap ruleMap (create_proj (case pi_mpi of Inl lpi \<Rightarrow> lpi | Inr mpi \<Rightarrow> Projection []));
      dps \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_termination_proof;
      xml_return (case pi_mpi of
         Inl lpi \<Rightarrow> Subterm_Criterion_Proc lpi seq dps prf
       | Inr mpi \<Rightarrow> Gen_Subterm_Criterion_Proc mpi dps prf)
    } XMLor XMLdo (STR ''redPairUrProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml2dp_termination_proof;
      xml_return (Redpair_UR_Proc a b c d)
    } XMLor XMLdo (STR ''monoRedPairUrProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      e \<leftarrow> xml2dp_termination_proof;
      xml_return (Mono_Redpair_UR_Proc a b c d e)
    } XMLor XMLdo (STR ''monoRedPairProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml2dp_termination_proof;
      xml_return (Mono_Redpair_Proc a b c d)
    } XMLor XMLdo (STR ''innermostMonoRedPairProc'') {
      rp \<leftarrow> red_triple False;
      p \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2dp_termination_proof;
      xml_return (Mono_URM_Redpair_Proc rp p r c)
    } XMLor XMLdo (STR ''uncurryProc'') {
      a \<leftarrow>? xml_nat (STR ''applicativeTop'');
      b \<leftarrow> uncurry_info xml2name termIndexMap ruleMap;
      c \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      e \<leftarrow> xml2dp_termination_proof;
      xml_return (Uncurry_Proc a b c d e)
    } XMLor XMLdo (STR ''flatContextClosureProc'') {
      a \<leftarrow> xml_singleton (STR ''freshSymbol'') xml2name id;
      b \<leftarrow> CPF_Proof_Parser.flat_contexts xml2name termIndexMap;
      c \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      e \<leftarrow> xml2dp_termination_proof;
      xml_return (Fcc_Proc a b c d e)
    } XMLor XMLdo (STR ''switchInnermostProc'') {
      a \<leftarrow> wcr_proof xml2name termIndexMap;
      b \<leftarrow> xml2dp_termination_proof;
      xml_return (Switch_Innermost_Proc a b)
    } XMLor XMLdo (STR ''splitProc'') {
      a \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2dp_termination_proof;
      d \<leftarrow> xml2dp_termination_proof;
      xml_return (Split_Proc a b c d)
    } XMLor XMLdo (STR ''finitenessAssumption'') {
      dpp \<leftarrow> xml2dp_input' xml2name termIndexMap ruleMap True;
      xml_return (Assume_Finite dpp [])
    } XMLor XMLdo (STR ''unknownProof'') {
      a \<leftarrow> xml_text (STR ''description'');
      b \<leftarrow> xml2dp_input' xml2name termIndexMap ruleMap True;
      c \<leftarrow>* xml2subproof;
      xml_return (Assume_Finite b c)
    } XMLor XMLdo (STR ''switchToTRS'') {
      a \<leftarrow> xml2trs_termination_proof;
      xml_return (To_Trs_Proc a)
    } XMLor XMLdo (STR ''generalRedPairProc'') {
      rp \<leftarrow> red_triple True;
      s \<leftarrow> xml_singleton (STR ''strict'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml_singleton (STR ''bound'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2cond_red_pair_proof xml2name termIndexMap ruleMap;
      ps \<leftarrow> xml2dp_termination_proof;
      pbo \<leftarrow>? xml2dp_termination_proof;
      xml_return (General_Redpair_Proc rp s b c (case pbo of None \<Rightarrow> [ps] | Some pb \<Rightarrow> [ps,pb]))
    } XMLor XMLdo (STR ''complexConstantRemovalProc'') {
      t \<leftarrow> term xml2name termIndexMap;
      rls \<leftarrow> XMLdo (STR ''ruleMap'') {
        ret \<leftarrow>* XMLdo (STR ''ruleMapEntry'') {
          a \<leftarrow> rule xml2name termIndexMap ruleMap;
          b \<leftarrow> rule xml2name termIndexMap ruleMap;
          xml_return (a,b)
        };
        xml_return ret
      };
      prf \<leftarrow> xml2dp_termination_proof;
      xml_return (Complex_Constant_Removal_Proc (Complex_Constant_Removal_Proof t rls) prf)
    } XMLor XMLdo (STR ''sizeChangeProc'') {
      version \<leftarrow> xml_leaf (STR ''subtermCriterion'') None
        XMLor XMLdo (STR ''reductionPair'') {
          redp \<leftarrow> red_triple False;
          ur \<leftarrow>? xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
          xml_return (Some (redp,ur))
        };
      b \<leftarrow>* CPF_Proof_Parser.scg xml2name termIndexMap ruleMap;
      case version of
          None \<Rightarrow> xml_return (Size_Change_Subterm_Proc b)
        | Some redp_ur \<Rightarrow> xml_return (Size_Change_Redpair_Proc (fst redp_ur) (snd redp_ur) b)
    }
  ) id x"
| "xml2trs_termination_proof x = xml_singleton (STR ''trsTerminationProof'') (
    XMLdo (STR ''rIsEmpty'') {
      xml_return R_is_Empty
    } XMLor XMLdo (STR ''semlab'') {
       sli \<leftarrow> CPF_Proof_Parser.sl_variant xml2name;
       lr \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
       lq \<leftarrow>[[]] innermostLhss xml2name termIndexMap;
       p \<leftarrow> xml2trs_termination_proof;
       xml_return (Semlab sli lq lr p)
    } XMLor XMLdo (STR ''split'') {
      a \<leftarrow> (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id);
      b \<leftarrow> xml2trs_termination_proof;
      c \<leftarrow> xml2trs_termination_proof;
      xml_return (Split a b c)
    } XMLor XMLdo (STR ''dpTrans'') {
      dps \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_termination_proof;
      xml_return (DP_Trans default_nfs_dp True dps prf)
    } XMLor XMLdo (STR ''ruleRemoval'') {
      ord \<leftarrow> red_triple False;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      p \<leftarrow> xml2trs_termination_proof;
      xml_return (Rule_Removal ord r p)
    } XMLor xml_change (bounds_info xml2name) (xml_return \<circ> Bounds)
    XMLor XMLdo (STR ''stringReversal'') {
      _ \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2trs_termination_proof;
      xml_return (String_Reversal prf)
    } XMLor XMLdo (STR ''equalityRemoval'') {
      a \<leftarrow> xml2trs_termination_proof;
      xml_return (Drop_Equality a)
    } XMLor XMLdo (STR ''rightGroundTermination'') {
      xml_return Right_Ground_Termination
    } XMLor XMLdo (STR ''constantToUnary'') {
       v \<leftarrow> plain_var;
       ren \<leftarrow> CPF_Proof_Parser.renaming xml2name;
       S \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
       p \<leftarrow> xml2trs_termination_proof;
       xml_return (Constant_String (Const_string_sound_proof v ren S) p)
    } XMLor XMLdo (STR ''removeNonApplicableRules'') {
      a \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml2trs_termination_proof;
      xml_return (Remove_Nonapplicable_Rules a b)
    } XMLor XMLdo (STR ''uncurry'') {
      i \<leftarrow> uncurry_info xml2name termIndexMap ruleMap;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      p \<leftarrow> xml2trs_termination_proof;
      xml_return (Uncurry i r p)
    } XMLor XMLdo (STR ''flatContextClosure'') {
      i \<leftarrow> CPF_Proof_Parser.flat_contexts xml2name termIndexMap;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      p \<leftarrow> xml2trs_termination_proof;
      xml_return (Fcc i r p)
    } XMLor XMLdo (STR ''switchInnermost'') {
      a \<leftarrow> CPF_Proof_Parser.wcr_proof xml2name termIndexMap;
      b \<leftarrow> xml2trs_termination_proof;
      xml_return (Switch_Innermost a b)
    } XMLor XMLdo (STR ''permutingArgumentFilter'') {
      a \<leftarrow> CPF_Proof_Parser.afs xml2name;
      b \<leftarrow> xml2trs_termination_proof;
      xml_return (Permuting_AFS a b)
    } XMLor XMLdo (STR ''terminationAssumption'') {
      qtrs \<leftarrow> xml2inn_trs_assm xml2name;
      xml_return (Assume_SN qtrs [])
    } XMLor XMLdo (STR ''unknownProof'') {
        a \<leftarrow> xml_text (STR ''description'');
        b \<leftarrow> xml2inn_trs_assm xml2name;
        c \<leftarrow>* xml2subproof;
        xml_return (Assume_SN b c)
    }
  ) id x"
| "xml2fptrs_termination_proof x = (
    XMLdo (STR ''trsTerminationProof'') {
      r \<leftarrow> XMLdo (STR ''terminationAssumption'') {
        inp \<leftarrow> xml2fp_trs_assm xml2name;
        xml_return (Assume_FP_SN inp [])
      } XMLor XMLdo (STR ''unknownProof'') {
        inp \<leftarrow> xml2fp_trs_assm xml2name;
        subprfs \<leftarrow>* xml2subproof;
        xml_return (Assume_FP_SN inp subprfs)
      };
      xml_return r
    }
  ) x"
| "xml2unknown_proof x =
  XMLdo (STR ''unknownInputProof'') {
    ret \<leftarrow> XMLdo (STR ''unknownAssumption'') {
      u \<leftarrow> unknown_input';
      xml_return (Assume_Unknown u [])
    } XMLor XMLdo (STR ''unknownProof'') {
      desc \<leftarrow> xml_text (STR ''description'');
      b \<leftarrow> unknown_input';
      c \<leftarrow>* xml2subproof;
      xml_return (Assume_Unknown b c)
    };
    xml_return ret
  } x"
| "xml2subproof x =
    XMLdo (STR ''subProof'') {
      XMLdo {
        inp \<leftarrow> xml2dp_input' xml2name termIndexMap ruleMap True;
        prf \<leftarrow> xml2dp_termination_proof;
        xml_return (Finite_assm_proof inp prf)
      } XMLor XMLdo {
        inp \<leftarrow> xml2inn_fp_trs_assm xml2name;
        case inp
        of Inl qtrs \<Rightarrow>
          XMLdo {
            prf \<leftarrow> xml2trs_termination_proof;
            xml_return (SN_assm_proof qtrs prf)
          }
        | Inr fptrs \<Rightarrow>
          XMLdo {
            prf \<leftarrow> xml2fptrs_termination_proof;
            xml_return (SN_FP_assm_proof fptrs prf)
          }
      }
    } x"

lemma drop_size_xml[dest]:
  assumes y: "drop n z = y" shows "sum_list (map size_xml y) \<le> sum_list (map size_xml z)"
proof (fold y, induct z arbitrary:n y)
  case Nil
  then show ?case by simp
next
  case (Cons a z)
  from le_trans[OF this le_add2] show ?case by (cases n, auto)
qed

partial_function (sum_bot)
  xml2complexity_proof :: "('f, 'l, string) complexity_proof xmlt"
where
  [code]: "xml2complexity_proof x = xml_singleton (STR ''complexityProof'') (
    XMLdo (STR ''ruleShifting'') {
      rp \<leftarrow> red_triple True;
      del \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      ur \<leftarrow>? xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2complexity_proof;
      xml_return (Rule_Shift_Complexity rp del ur prf)
    } XMLor XMLdo (STR ''usableRules'') {
      a \<leftarrow> xml_singleton (STR ''nonUsableRules'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml2complexity_proof;
      xml_return (Usable_Rules_Complexity a b)
    } XMLor XMLdo (STR ''split'') {
      a \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml2complexity_proof;
      c \<leftarrow> xml2complexity_proof;
      xml_return (Split_Complexity a b c)
    } XMLor XMLdo (STR ''removeNonApplicableRules'') {
      a \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      b \<leftarrow> xml2complexity_proof;
      xml_return (Remove_Nonapplicable_Rules_Complexity a b)
    } XMLor xml_change (bounds_info xml2name) (xml_return \<circ> Matchbounds_Complexity)
    XMLor XMLdo (STR ''relativeBounds'') {
      a \<leftarrow> bounds_info xml2name;
      b \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2complexity_proof;
      xml_return (Matchbounds_Rel_Complexity a b c)
    } XMLor XMLdo (STR ''rIsEmpty'') {
      xml_return RisEmpty_Complexity
    } XMLor XMLdo (STR ''dtTransformation'') {
      S \<leftarrow> CPF_Proof_Parser.rule_pairs xml2name termIndexMap ruleMap (STR ''strictDTs'') (STR ''ruleWithDT'');
      W \<leftarrow> CPF_Proof_Parser.rule_pairs xml2name termIndexMap ruleMap (STR ''weakDTs'') (STR ''ruleWithDT'');
      inn \<leftarrow> innermostLhss xml2name termIndexMap;
      p \<leftarrow> xml2complexity_proof;
      xml_return (DT_Transformation (DT_Transformation_Info S W inn) p)
    } XMLor XMLdo (STR ''wdpTransformation'') {
      Comp \<leftarrow> symbols xml2name (STR ''compoundSymbols'');
      S \<leftarrow> CPF_Proof_Parser.rule_pairs xml2name termIndexMap ruleMap (STR ''strictWDPs'') (STR ''ruleWithWDP'');
      W \<leftarrow> CPF_Proof_Parser.rule_pairs xml2name termIndexMap ruleMap (STR ''weakWDPs'') (STR ''ruleWithWDP'');
      Q' \<leftarrow> innermostLhss xml2name termIndexMap;
      p \<leftarrow> xml2complexity_proof;
      xml_return (WDP_Transformation (WDP_Trans_Info (set Comp) S W Q') p)
    } XMLor XMLdo (STR ''unknownProof'') {
      a \<leftarrow> xml_text (STR ''description'');
      b \<leftarrow> xml2complexity_input' xml2name;
      c \<leftarrow>* XMLdo (STR ''subProof'') {
        inp \<leftarrow> xml2complexity_input' xml2name;
        prf \<leftarrow> xml2complexity_proof;
        xml_return (Complexity_assm_proof inp prf)
      };
      xml_return (Complexity_Assumption b c)
    } XMLor XMLdo (STR ''complexityAssumption'') {
       p \<leftarrow> xml2complexity_input' xml2name;
       xml_return (Complexity_Assumption p [])
    }
  ) id x"


partial_function (sum_bot) xml2ac_dp_termination_proof :: "(_, string) ac_dp_termination_proof xmlt"
where [code]: "xml2ac_dp_termination_proof x = xml_singleton (STR ''acDPTerminationProof'') (
    XMLdo (STR ''acRedPairProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml2ac_dp_termination_proof;
      xml_return (AC_Redpair_UR_Proc a b c d)
    } XMLor XMLdo (STR ''acSubtermProc'') {
      pi \<leftarrow> CPF_Proof_Parser.multiset_af xml2name;
      r \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2ac_dp_termination_proof;
      xml_return (AC_Subterm_Proc pi r prf)
    } XMLor XMLdo (STR ''acTrivialProc'') {
      xml_return AC_P_is_Empty
    } XMLor XMLdo (STR ''acMonoRedPairProc'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      d \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      e \<leftarrow> xml2ac_dp_termination_proof;
      xml_return (AC_Mono_Redpair_UR_Proc a b c d e)
    } XMLor XMLdo (STR ''acDepGraphProc'') {
      ret \<leftarrow>* XMLdo (STR ''component'') {
        dps \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
        prfOpt \<leftarrow>? xml2ac_dp_termination_proof;
        xml_return (prfOpt, dps)
      };
      xml_return (AC_Dep_Graph_Proc ret)
    }
   ) id x"

partial_function (sum_bot) xml2ac_termination_proof :: "('f, 'l, string) ac_termination_proof xmlt"
where [code]: "xml2ac_termination_proof x = xml_singleton (STR ''acTerminationProof'') (
    XMLdo (STR ''acDependencyPairs'') {
      e \<leftarrow> xml_singleton (STR ''equations'') (rules xml2name termIndexMap ruleMap) id;
      dpe \<leftarrow> xml_singleton (STR ''dpEquations'') (rules xml2name termIndexMap ruleMap) id;
      dp \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      rext \<leftarrow> xml_singleton (STR ''extensions'') (rules xml2name termIndexMap ruleMap) id;
      p1 \<leftarrow> xml2ac_dp_termination_proof;
      p2opt \<leftarrow>? xml2ac_dp_termination_proof;
      case p2opt
      of Some p2 \<Rightarrow> xml_return (AC_DP_Trans (AC_dependency_pairs_proof e dp dpe rext) p1 p2)
      | None \<Rightarrow> xml_return (AC_DP_Trans_Single (AC_dependency_pairs_proof e dp dpe rext) p1)
    } XMLor XMLdo (STR ''acRuleRemoval'') {
      a \<leftarrow> red_triple False;
      b \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      c \<leftarrow> xml2ac_termination_proof;
      xml_return (AC_Rule_Removal a b c)
    } XMLor XMLdo (STR ''acRIsEmpty'') {
      xml_return AC_R_is_Empty
    }) id x"

definition nonloop :: "(_,string) non_loop_prf xmlt" where
  "nonloop = XMLdo (STR ''nonLoop'') {
    a \<leftarrow> CPF_Proof_Parser.pat_rule_prf xml2name termIndexMap ruleMap;
    b \<leftarrow> CPF_Proof_Parser.subst xml2name termIndexMap;
    c \<leftarrow> CPF_Proof_Parser.subst xml2name termIndexMap;
    d \<leftarrow> xml_nat (STR ''natural'');
    e \<leftarrow> xml_nat (STR ''natural'');
    f \<leftarrow> pos;
    xml_return (Non_loop_prf a b c d e f)
  }"

definition string :: "_ list xmlt" where
  "string = xml_many (STR ''string'') xml2name id"

definition oc_srs :: "_ srs_rule xmlt" where
  "oc_srs = xml_pair (STR ''overlapClosureSRS'') string string Pair"

definition word_pattern :: "_ word_pat xmlt" where
  "word_pattern =
    XMLdo (STR ''wordPattern'') {
      l \<leftarrow> string;
      m \<leftarrow> string;
      f \<leftarrow> xml_nat (STR ''factor'');
      c \<leftarrow> xml_nat (STR ''constant'');
      r \<leftarrow> string;
      xml_return (l,(f,c,m),r)
  }"

definition derivation_pattern :: "_ deriv_pat xmlt" where
  "derivation_pattern = xml_pair (STR ''derivationPattern'')
     word_pattern word_pattern Pair"

definition derivation_pattern_proof :: "_ dp_proof_step xmlt" where
  "derivation_pattern_proof =
    (let
      oc = oc_srs;
      dp = derivation_pattern;
      s = string in
    xml_singleton (STR ''derivationPatternProof'') (
      xml_pair (STR ''OC1'') oc (xml_bool (STR ''isPair'')) OC1
    XMLor xml_tuple6 (STR ''OC2'') oc oc oc s s s OC2
    XMLor xml_tuple6 (STR ''OC2prime'') oc oc oc s s s OC2p
    XMLor xml_tuple5 (STR ''OC3'') oc oc oc s s  OC3
    XMLor xml_tuple5 (STR ''OC3prime'') oc oc oc s s OC3p
    XMLor xml_pair (STR ''OCintoDP1'') dp oc OCDP1
    XMLor xml_pair (STR ''OCintoDP2'') dp oc OCDP2
    XMLor xml_pair (STR ''equivalent'') dp dp WPEQ
    XMLor xml_pair (STR ''lift'') dp dp Lift
    XMLor xml_tuple5 (STR ''DP_OC_1_1'') dp dp oc s s DPOC1_1
    XMLor xml_tuple6 (STR ''DP_OC_1_2'') dp dp oc s s s DPOC1_2
    XMLor xml_tuple5 (STR ''DP_OC_2'') dp dp oc s s DPOC2
    XMLor xml_tuple5 (STR ''DP_OC_3_1'') dp dp oc s s DPOC3_1
    XMLor xml_tuple6 (STR ''DP_OC_3_2'') dp dp oc s s s DPOC3_2
    XMLor xml_tuple5 (STR ''DP_DP_1_1'') dp dp dp s s DPDP1_1
    XMLor xml_tuple5 (STR ''DP_DP_1_2'') dp dp dp s s DPDP1_2
    XMLor xml_tuple5 (STR ''DP_DP_2_1'') dp dp dp s s DPDP2_1
    XMLor xml_tuple5 (STR ''DP_DP_2_2'') dp dp dp s s DPDP2_2
  ) id)"

definition nonloop_srs_reason :: "(_ dp_proof_step list \<Rightarrow> _ non_loop_srs_proof)xmlt" where
  "nonloop_srs_reason =
    xml_triple (STR ''selfEmbeddingOC'')
        string string string
        (\<lambda> l m r. SE_OC (m, l @ m @ r) l r)
    XMLor xml_triple (STR ''selfEmbeddingDP'')
        derivation_pattern string string
        SE_DP"

definition nonloop_srs :: "_ non_loop_srs_proof xmlt" where
  "nonloop_srs = xml_pair (STR ''nonterminatingSRS'')
    (xml_many (STR ''derivationPatterns'') derivation_pattern_proof id)
    nonloop_srs_reason
    (\<lambda> list prf. prf list)"

definition not_wn_ta :: "(_, string) not_wn_ta_prf xmlt" where
  "not_wn_ta = xml_pair (STR ''notWNTreeAutomaton'')
    (tree_automaton (ta_normal_lhs xml2name))
    closed_criterion
    (\<lambda> ta rel. Not_wn_ta_prf ta rel)"

(* TODO: 
definition xml2inn_fp_nt_trs_assm ::
    "(('f, 'l, string) qtrsLL + ('f, 'l, string) fptrsLL) xmlt"
where
  "xml2inn_fp_nt_trs_assm = xml_change (xml2_trs_input xml2name) (\<lambda> inp.
   case inp of
     Inn_TRS_input inn r s start \<Rightarrow>
      if s \<noteq> [] then
        xml_error (STR ''relative rules are not allowed here'')
      else if start \<noteq> Full then
        xml_error (STR ''start terms not allowed here'')
      else
        xml_return (Inl (default_nfs_nt_trs, strategy_to_Q inn r, r))
    | FP_TRS_input fp r \<Rightarrow> xml_return (Inr (strategy_to_fp fp r, r))
    | _ \<Rightarrow> xml_error (STR ''non-relative TRS expected'')
  )"


definition xml2fp_nt_trs_assm :: "('f, 'l, string) fptrsLL xmlt"
where
  "xml2fp_nt_trs_assm = xml_change (xml2_trs_input xml2name) (\<lambda>inp.
    case inp of
      FP_TRS_input fp r \<Rightarrow> xml_return (strategy_to_fp fp r, r)
    | _ \<Rightarrow> xml_error (STR ''outermost/forbidden-pattern/context-sensitive TRS expected'')
  )"

definition xml2inn_nt_trs_assm where
  "xml2inn_nt_trs_assm = xml_change (xml2_trs_input xml2name) (\<lambda>inp.
    case inp of Inn_TRS_input inn r s start \<Rightarrow>
      if s \<noteq> [] then xml_error (STR ''(innermost) TRS without relative rules expected'')
      else if start \<noteq> Full then xml_error (STR ''start term is not allowed here'')
      else xml_return (default_nfs_nt_trs, strategy_to_Q inn r, r)
   )"


definition xml2inn_rel_nt_trs_assm where
  "xml2inn_rel_nt_trs_assm = xml_change (xml2_trs_input xml2name) (\<lambda>inp.
    case inp of Inn_TRS_input inn r s start \<Rightarrow>
    if start \<noteq> Full then xml_error (STR ''start term is not allowed here'')
    else xml_return (default_nfs_nt_trs, strategy_to_Q inn r, r, s)
   )"
*)

definition "xml2inn_rel_nt_trs_assm = undefined" 
definition "xml2inn_nt_trs_assm = undefined" 
(*
abbreviation sub_disproof where "sub_disproof xml2name
  xml2trs_nontermination_proof
  xml2dp_nontermination_proof
  xml2reltrs_nontermination_proof
  xml2fp_nontermination_proof
  xml2unknown_disproof
  x \<equiv>
    let cs = Xml.children x
     in (if length cs \<noteq> 2 then Xmlt.fail ''subProof'' x
      else let inp = take 2 (Xml.tag (cs ! 1)) in
      (if inp = ''tr'' then
        do {
          io_trs <- xml2inn_fp_nt_trs_assm xml2name (hd cs);
          (case io_trs of
            Inl qtrs \<Rightarrow> Xmlt.change xml2trs_nontermination_proof (\<lambda> prf. Not_SN_assm_proof qtrs prf :: ('f, 'l, string, 'a, 'b, 'c, 'd,'e) generic_assm_proof)
          | Inr fptrs \<Rightarrow> Xmlt.change xml2fp_nontermination_proof (\<lambda> prf. Not_SN_FP_assm_proof fptrs prf)) (cs ! 1)
        }
      else if inp = ''dp'' then
        Xmlt.pair ''subProof'' (xml2dp_input' False xml2name) xml2dp_nontermination_proof (\<lambda> qdp prf. Infinite_assm_proof qdp prf :: ('f, 'l, string, 'a, 'b, 'c, 'd,'e) generic_assm_proof) x
      else if inp = ''re'' then
        Xmlt.pair ''subProof'' (xml2inn_rel_nt_trs_assm xml2name) xml2reltrs_nontermination_proof Not_RelSN_assm_proof x
      else if inp = ''un'' then
        Xmlt.pair ''subProof'' xml2unknown_input xml2unknown_disproof Unknown_assm_proof x
      else Xmlt.fail ''subProof'' x))"
*)

partial_function_mr (sum_bot) xml2dp_nontermination_proof ::
    "('f, 'l, string) dp_nontermination_proof xmlt" and
  xml2trs_nontermination_proof ::
    "('f, 'l, string) trs_nontermination_proof xmlt" and
  xml2reltrs_nontermination_proof ::
    "('f, 'l, string) reltrs_nontermination_proof xmlt" and
  xml2unknown_disproof :: "('f, 'l, string) neg_unknown_proof xmlt"
  where
  "xml2dp_nontermination_proof x = xml_singleton (STR ''dpNonterminationProof'') (
    XMLdo (STR ''dpRuleRemoval'') {
      p \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Rule_Removal (Rule_removal_nonterm_dp_prf p r) prf)
    } XMLor XMLdo (STR ''loop'') {
      (s,rseq) \<leftarrow> relsteps xml2name termIndexMap ruleMap;
      \<sigma> \<leftarrow> CPF_Proof_Parser.subst xml2name termIndexMap;
      c \<leftarrow> CPF_Proof_Parser.ctxt xml2name termIndexMap;
      xml_return (DP_Loop (DP_loop_prf s rseq \<sigma> c))
    } XMLor xml_change nonloop
      (xml_return \<circ> DP_Nonloop)
    XMLor XMLdo (STR ''innermostLhssRemovalProc'') {
      q \<leftarrow> innermostLhss xml2name termIndexMap;
      p \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Q_Reduction (DP_q_reduction_nonterm_prf q) p)
    } XMLor XMLdo (STR ''innermostLhssIncreaseProc'') {
      q \<leftarrow> innermostLhss xml2name termIndexMap;
      p \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Q_Increase (Q_increase_nonterm_dp_prf q) p)
    } XMLor XMLdo (STR ''instantiationProc'') {
      p \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Instantiation (Instantiation_complete_proc_prf p) prf)
    } XMLor XMLdo (STR ''narrowingProc'') {
      st \<leftarrow> rule xml2name termIndexMap ruleMap;
      po \<leftarrow> pos;
      p \<leftarrow> xml_singleton (STR ''narrowings'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Narrowing (Narrowing_complete_proc_prf st po p) prf)
    } XMLor XMLdo (STR ''rewritingProc'') {
      (s,t) \<leftarrow> rule xml2name termIndexMap ruleMap;
      (p,lr,t') \<leftarrow> rstep xml2name termIndexMap ruleMap;
      st'' \<leftarrow> rule xml2name termIndexMap ruleMap;
      U \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
      prf \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Rewriting (Rewriting_complete_proc_prf (Some U) (s,t) (s,t') st'' lr p) prf)
    } XMLor XMLdo (STR ''switchFullStrategyProc'') {
      a \<leftarrow> wcr_proof xml2name termIndexMap;
      b \<leftarrow> xml2dp_nontermination_proof;
      xml_return (DP_Termination_Switch a b)
    } XMLor XMLdo (STR ''infinitenessAssumption'') {
      qdp \<leftarrow> xml2dp_input' xml2name termIndexMap ruleMap False;
      xml_return (DP_Assume_Infinite qdp [])
    } XMLor XMLdo (STR ''unknownProof'') {
      a \<leftarrow> xml_text (STR ''description'');
      b \<leftarrow> xml2dp_input' xml2name termIndexMap ruleMap False;
      c \<leftarrow>* xml_any;
      xml_return (DP_Assume_Infinite b [])
  }) id x"
| "xml2trs_nontermination_proof x =
  xml_singleton (STR ''trsNonterminationProof'') (
  XMLdo (STR ''variableConditionViolated'') {
    xml_return TRS_Not_Well_Formed
  } XMLor xml_change (loop xml2name termIndexMap ruleMap)
    (\<lambda>(s, rseq, \<sigma>, C). xml_return (TRS_Loop (TRS_loop_prf s (map (\<lambda>(x, y, _, z). (x, y, z)) rseq) \<sigma> C)))
  XMLor xml_change nonloop (xml_return \<circ> TRS_Nonloop)
  XMLor xml_change nonloop_srs (xml_return \<circ> TRS_Nonloop_SRS)
  XMLor XMLdo (STR ''rightGroundNontermination'') {
      xml_return TRS_Not_RG_Decision 
  } XMLor XMLdo (STR ''ruleRemoval'') {
    r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
    p \<leftarrow> xml2trs_nontermination_proof;
    xml_return (TRS_Rule_Removal (Rule_removal_nonterm_trs_prf r) p)
  } XMLor XMLdo (STR ''dpTrans'') {
    p \<leftarrow> xml_singleton (STR ''dps'') (rules xml2name termIndexMap ruleMap) id;
    c \<leftarrow> xml2dp_nontermination_proof;
    xml_return (TRS_DP_Trans (DP_trans_nontermination_tt_prf p) c)
  } XMLor XMLdo (STR ''stringReversal'') {
    _ \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
    p \<leftarrow> xml2trs_nontermination_proof;
    xml_return (TRS_String_Reversal p)
  } XMLor XMLdo (STR ''constantToUnary'') {
     v \<leftarrow> plain_var;
     ren \<leftarrow> CPF_Proof_Parser.renaming xml2name;
     S \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
     p \<leftarrow> xml2trs_nontermination_proof;
     xml_return (TRS_Constant_String (Const_string_complete_proof v ren S) p)
  } XMLor XMLdo (STR ''innermostLhssIncrease'') {
    q \<leftarrow> innermostLhss xml2name termIndexMap;
    r \<leftarrow> xml2trs_nontermination_proof;
    xml_return (TRS_Q_Increase (Q_increase_nonterm_trs_prf q) r)
  } XMLor XMLdo (STR ''switchFullStrategy'') {
    a \<leftarrow> wcr_proof xml2name termIndexMap;
    b \<leftarrow> xml2trs_nontermination_proof;
    xml_return (TRS_Termination_Switch a b)
  } XMLor XMLdo (STR ''uncurry'') {
      i \<leftarrow> uncurry_info xml2name termIndexMap ruleMap;
      r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      p \<leftarrow> xml2trs_nontermination_proof;
      xml_return (TRS_Uncurry (Uncurry_nt_proof i r) p)
  } XMLor xml_change (CPF_Proof_Parser.not_wn_ta xml2name)
    (xml_return \<circ> TRS_Not_WN_Tree_Automaton)
  XMLor XMLdo (STR ''nonterminationAssumption'') {
    qtrs \<leftarrow> xml2inn_nt_trs_assm;
    xml_return (TRS_Assume_Not_SN qtrs [])
  } XMLor XMLdo (STR ''unknownProof'') {
    a \<leftarrow> xml_text (STR ''description'');
    b \<leftarrow> xml2inn_nt_trs_assm;
    c \<leftarrow>* xml_any;
    xml_return (TRS_Assume_Not_SN b [])
  }) id x"
| "xml2reltrs_nontermination_proof x =
  xml_singleton (STR ''relativeNonterminationProof'') (
  XMLdo (STR ''variableConditionViolated'') {
    xml_return Rel_Not_Well_Formed
  } XMLor xml_change (loop xml2name termIndexMap ruleMap)
      (\<lambda>(s, rseq, \<sigma>, C). xml_return (Rel_Loop (Rel_trs_loop_prf s rseq \<sigma> C)))
  XMLor XMLdo (STR ''ignoreRelativePart'') {
      prf \<leftarrow> xml2trs_nontermination_proof;
      xml_return (Rel_R_Not_SN prf)
  } XMLor XMLdo (STR ''ruleRemoval'') {
    r \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
    s \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
    p \<leftarrow> xml2reltrs_nontermination_proof;
    xml_return (Rel_Rule_Removal (Rule_removal_nonterm_reltrs_prf r s) p)
  } XMLor XMLdo (STR ''stringReversal'') {
    _ \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) Some;
    _ \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) Some;
    p \<leftarrow> xml2reltrs_nontermination_proof;
    xml_return (Rel_TRS_String_Reversal p)
  } XMLor XMLdo (STR ''nonterminationAssumption'') {
    qtrs \<leftarrow> xml2inn_rel_nt_trs_assm;
    xml_return (Rel_TRS_Assume_Not_SN qtrs [])
  } XMLor XMLdo (STR ''unknownProof'') {
      a \<leftarrow> xml_text (STR ''description'');
      b \<leftarrow> xml2inn_rel_nt_trs_assm;
      c \<leftarrow>* xml_any;
      xml_return (Rel_TRS_Assume_Not_SN b [])
  }) id x"
| "xml2unknown_disproof x = xml_singleton (STR ''unknownInputProof'') (
    xml_singleton (STR ''unknownAssumption'')
        unknown_input'
        (\<lambda> u. Assume_NT_Unknown u [])
    XMLor XMLdo (STR ''unknownProof'') {
        a \<leftarrow> xml_text (STR ''description'');
        b \<leftarrow> unknown_input';
        c \<leftarrow>* xml_any;
        xml_return (Assume_NT_Unknown b [])
  }) id x"


fun add_source_lab_proof
where
  "add_source_lab_proof (Rule_Labeling rl js _) _ prf = Rule_Labeling rl js (Some prf)"
| "add_source_lab_proof (Rule_Labeling_Conv rl cs _) (Some n) prf = Rule_Labeling_Conv rl cs (Some (n, prf))"


definition xml2ms_signature
  where "xml2ms_signature = xml_many (STR ''manySortedSignature'') (
       xml_triple (STR ''manySortedFunction'')
         xml2name
         (xml_many (STR ''args'') (xml_text (STR ''sort'')) id)
         (xml_singleton (STR ''result'') (xml_text (STR ''sort'')) id)
       (\<lambda>a b c. (a, b, c))
    ) id"

partial_function (sum_bot) xml2cr_proof :: "(_,_,string) cr_proof xmlt"
where [code]: "xml2cr_proof x = xml_singleton (STR ''crProof'') (
    xml_pair (STR ''wcrAndSN'')
        (wcr_proof xml2name termIndexMap)
        xml2trs_termination_proof
      SN_WCR
    XMLor xml_leaf (STR ''orthogonal'') Weakly_Orthogonal
    XMLor XMLdo (STR ''stronglyClosed'') { n \<leftarrow> joinAutoBfs1; xml_return (Strongly_Closed n)}
    XMLor XMLdo (STR ''parallelClosed'') { n \<leftarrow> joinAutoBfs; xml_return (Parallel_Closed n)}
    XMLor XMLdo (STR ''pcpClosed'') {
            hints_cp \<leftarrow> xml_singleton (STR ''ordinaryCriticalPairs'') (xml2cp_join_info xml2name termIndexMap) id;
            hints_pcp \<leftarrow> xml_singleton (STR ''parallelCriticalPairs'') (xml2cp_join_info xml2name termIndexMap) id;
            xml_return (PCP_Closed hints_cp hints_pcp)
         } 
    XMLor XMLdo (STR ''compositionalPcp'') {
            trsC \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
            hints \<leftarrow> xml2cp_join_info xml2name termIndexMap;
            prf \<leftarrow> xml2cr_proof;
            xml_return (Compositional_PCP trsC hints prf)
         } 
    XMLor XMLdo (STR ''compositionalPcps'') {
            trsC \<leftarrow> xml_singleton (STR ''trsC'') (rules xml2name termIndexMap ruleMap) id;
            trsP \<leftarrow> xml_singleton (STR ''trsP'') (rules xml2name termIndexMap ruleMap) id;
            hintsP \<leftarrow> xml2cp_join_info xml2name termIndexMap;
            hints \<leftarrow> xml2cp_join_info xml2name termIndexMap;
            sn_prf \<leftarrow> xml2trs_termination_proof;
            cr_prf \<leftarrow> xml2cr_proof;
            xml_return (Compositional_PCPS trsC trsP hintsP hints sn_prf cr_prf)
         } 
    XMLor XMLdo (STR ''developmentClosed'') { n \<leftarrow> joinAutoBfs; xml_return (Development_Closed n)}
    XMLor xml_triple (STR ''criticalPairClosingSystem'')
        (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
        xml2trs_termination_proof
        joinAutoBfs1
      Critical_Pair_Closing_System
    XMLor xml_pair (STR ''ruleLabeling'')
        (rule_labeling_function xml2name termIndexMap ruleMap)
        (joinSequences xml2name termIndexMap)
      (\<lambda> rl js. Rule_Labeling rl js None)
    XMLor XMLdo (STR ''pcpRuleLabeling'') {
      lab \<leftarrow> rule_labeling_function xml2name termIndexMap ruleMap;
      joins \<leftarrow> xml2cp_join_info xml2name termIndexMap;
      xml_return (PCP_Rule_Lab (PCP_Sequences (rule_lab_repr_to_lab lab) joins))
    }
    XMLor XMLdo (STR ''compositionalPcpRuleLabeling'') {
      lab \<leftarrow> rule_labeling_function xml2name termIndexMap ruleMap;
      lab' \<leftarrow>? rule_labeling_function xml2name termIndexMap ruleMap;
      joinsRS \<leftarrow> xml_singleton (STR ''joinsRS'') (xml2cp_join_info xml2name termIndexMap) id;
      joinsSR \<leftarrow>? xml_singleton (STR ''joinsSR'') (xml2cp_join_info xml2name termIndexMap) id;
      trs \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      subPrf \<leftarrow> xml2cr_proof;
      xml_return (Compositional_PCP_Rule_Lab trs (PCP_Sequences_Com 
         (rule_lab_repr_to_lab lab) 
         (map_option rule_lab_repr_to_lab lab') 
         joinsRS (case joinsSR of None \<Rightarrow> joinsRS | Some j \<Rightarrow> j) ) subPrf)
    }
    XMLor XMLdo (STR ''decreasingDiagrams'') {
        a \<leftarrow>? xml2trs_termination_proof;
        ret \<leftarrow>
          XMLdo (STR ''ruleLabeling'') {
            rl \<leftarrow> rule_labeling_function xml2name termIndexMap ruleMap;
            js \<leftarrow> joinSequences xml2name termIndexMap;
            case a of
              Some prf \<Rightarrow> xml_return (add_source_lab_proof (Rule_Labeling rl js None) None prf)
            | _ \<Rightarrow> xml_return (Rule_Labeling rl js None)
          } XMLor XMLdo (STR ''ruleLabelingConv'') {
            rl \<leftarrow> rule_labeling_function xml2name termIndexMap ruleMap;
            cs \<leftarrow> joinSequences xml2name termIndexMap;
            case a of
              Some prf \<Rightarrow> XMLdo {
                n \<leftarrow> xml_nat (STR ''nrSteps'');
                xml_return (add_source_lab_proof (Rule_Labeling_Conv rl cs None) (Some n) prf)
              }
            | _ \<Rightarrow> xml_return (Rule_Labeling_Conv rl cs None)
          };
        xml_return ret
    } XMLor XMLdo (STR ''redundantRules'') {
      trs \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      n \<leftarrow> xml_nat (STR ''nrSteps'');
      cs \<leftarrow>[[]] xml_many (STR ''conversions'') (conversion xml2name termIndexMap) id;
      prf \<leftarrow> xml2cr_proof;
      xml_return (Redundant_Rules trs n cs prf)
    } XMLor XMLdo (STR ''persistentDecomposition'') {
      sig \<leftarrow> xml2ms_signature;
      subs \<leftarrow>* xml_pair (STR ''component'')
       (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
       xml2cr_proof
       Pair;
      xml_return (Persistent_Decomposition sig subs)
  }) id x"

definition compatible_ta :: "ltag \<Rightarrow> ((string,_)tree_automaton \<times> string ta_relation) xmlt" where
  "compatible_ta tag = XMLdo tag {
    a \<leftarrow> tree_automaton (ta_normal_lhs xml2name);
    b \<leftarrow>[Id_Relation] closed_criterion;
    xml_return (a,b)
  }"

definition xml2completion_proof :: "(_,_,string) completion_proof xmlt"
where "xml2completion_proof = XMLdo (STR ''completionProof'') {
     w \<leftarrow> wcr_proof xml2name termIndexMap;
     t \<leftarrow> xml2trs_termination_proof;
     (s1,s2) \<leftarrow> XMLdo (STR ''equivalenceProof'') {
       s1 \<leftarrow> subsumption_proof xml2name termIndexMap ruleMap;
       s2 \<leftarrow>? subsumption_proof xml2name termIndexMap ruleMap;
       xml_return (s1,s2)
      };
     xml_return (SN_WCR_Eq w t s1 s2)
  }"

definition xml2approx_completion_proof :: "(_,_,string) approx_completion_proof xmlt"
where "xml2approx_completion_proof = XMLdo (STR ''approxCompletionProof'') {
     w \<leftarrow> wcr_proof xml2name termIndexMap;
     t \<leftarrow> xml2trs_termination_proof;
     s \<leftarrow>? subsumption_proof xml2name termIndexMap ruleMap;
     xml_return (SN_WCR_Subsumption w t s)
  }"

definition xml2ordered_completion_step :: "(_,string) oc_irule xmlt"
  where "xml2ordered_completion_step =
      xml_triple (STR ''deduce'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda> s t u. OC_Deduce s t u)
    XMLor
      (xml_pair (STR ''orientl'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t. OC_Orientl s t))
    XMLor
      (xml_pair (STR ''orientr'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t. OC_Orientr s t))
    XMLor
      (xml_singleton (STR ''delete'')
        (term xml2name termIndexMap)
        (\<lambda>s. OC_Delete s))
    XMLor
      (xml_triple (STR ''compose'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t u. OC_Compose s t u))
    XMLor
      (xml_triple (STR ''simplifyl'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t u. OC_Simplifyl s t u))
    XMLor
      (xml_triple (STR ''simplifyr'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t u. OC_Simplifyr s t u))
    XMLor
      (xml_triple (STR ''collapse'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (\<lambda>s t u. OC_Collapse s t u))
"

definition "xml2ordered_completion_proof =
      xml_singleton (STR ''orderedCompletionProof'') (
        xml_many (STR ''run'')
          (xml_singleton (STR ''orderedCompletionStep'') xml2ordered_completion_step id)
          id
      ) OKB"

definition "unraveling_info =
  (xml_many (STR ''unravelingInformation'') (XMLdo (STR ''unravelingEntry'') {
     a \<leftarrow> crule xml2name termIndexMap (STR ''conditionalRule'');
     b \<leftarrow>* rule xml2name termIndexMap ruleMap;
     xml_return (a,b)
  }) id)"

definition "xml2quasi_reductive_proof = xml_singleton (STR ''quasiReductiveProof'') (
  xml_pair (STR ''unraveling'')
    unraveling_info
    xml2trs_termination_proof
    Unravel
  ) id"

definition "split_if_info =
  (XMLdo (STR ''splitIfInformation'') {
     t \<leftarrow> term xml2name termIndexMap;
     f \<leftarrow> term xml2name termIndexMap;
     es \<leftarrow>* XMLdo (STR ''normalUnravelingEntry'') {
        a \<leftarrow> crule xml2name termIndexMap (STR ''rule'');
        f \<leftarrow> xml2name; 
        ts \<leftarrow>* term xml2name termIndexMap;
        xml_return (a, f, ts)
     };
     xml_return (t, f, es)
  })"

definition "xml2state_map = xml_many (STR ''stateMap'')
  (xml_pair (STR ''entry'') state (term xml2name termIndexMap) Pair)
  (\<lambda>xs x. the (map_of xs x))"

definition "xml2nonreachable_etac_info = xml_tuple5 (STR ''nonreachableEtac'')
  (CPFsignature xml2name)
  xml2name
  xml2name
  (tree_automaton (ta_normal_lhs xml2name))
  (xml2state_map)
  (\<lambda>F a c A m. Nonreachable_ETAC F a c (map_states_impl m A))"

definition "xml2ordered_completion = XMLdo (STR ''orderedCompletion'') {
  (rs, es, ro) \<leftarrow> XMLdo (STR ''orderedCompletionResult'') {
    rs \<leftarrow> XMLdo (STR ''trs'') { ret \<leftarrow> rules xml2name termIndexMap ruleMap; xml_return ret };
    es \<leftarrow> XMLdo (STR ''equations'') { ret \<leftarrow> rules xml2name termIndexMap ruleMap; xml_return ret };
    ro \<leftarrow> XMLdo (STR ''reductionOrder'') {
       ro \<leftarrow> kbo_input xml2name;
       xml_return ro
    };
    xml_return (rs, es, ro)
  };
  p \<leftarrow> xml2ordered_completion_proof;
  xml_return (rs, es, ro, p)
}"

definition
  xml2equational_proof :: "('f, 'l, string) equational_proof xmlt"
where
  "xml2equational_proof =
    xml_singleton (STR ''equationalProof'') (
      xml_singleton (STR ''equationalProofTree'') (xml2eq_proof xml2name termIndexMap ruleMap) Equational_Proof_Tree
      XMLor xml_change (CPF_Proof_Parser.conversion xml2name termIndexMap) (\<lambda> e. xml_return (Conversion e))
      XMLor xml_change (CPF_Proof_Parser.subsumption_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Conversion_With_History)
      XMLor xml_pair (STR ''completionAndNormalization'')
        (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
        xml2completion_proof
        Completion_and_Normalization
    ) id"

definition xml2equational_disproof ::
    "('f, 'l, string) equational_disproof xmlt"
  where
    "xml2equational_disproof =
      xml_singleton (STR ''equationalDisproof'') (
        (xml_pair (STR ''completionAndNormalization'')
          (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
          xml2completion_proof
          Completion_and_Normalization_Different)
        XMLor (xml_pair (STR ''approxAndCompletionAndNormalization'')
          (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
          xml2approx_completion_proof
          Approx_and_Completion_and_Normalization_Different)
        XMLor (xml_triple (STR ''approxAndOrderedCompletionAndNormalization'')
          (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
          (xml_singleton (STR ''equations'') (rules xml2name termIndexMap ruleMap) id)
          (xml_singleton (STR ''reductionOrder'') (kbo_input xml2name) id) 
          Approx_and_Ordered_Completion_and_Normalization_Different)
        XMLor xml_change xml2ordered_completion (\<lambda>(rs, es, ro, p).
          xml_return (Ordered_Completion_and_Normalization_Different rs es ro p))        
      ) id"

partial_function (sum_bot) xml2nonreachability_proof :: "(_, _,_,_) nonreachability_proof xmlt"
where [code]: "xml2nonreachability_proof x = xml_singleton (STR ''nonreachabilityProof'') (
    xml_leaf (STR ''nonreachableTcap'') Nonreachable_Gtcap
    XMLor xml2nonreachable_etac_info
    XMLor xml_pair (STR ''nonreachableSubstApprox'')
      (rules xml2name termIndexMap ruleMap)
      xml2nonreachability_proof
      Nonreachable_Subst_Approx
    XMLor xml_singleton (STR ''nonreachableReverse'') xml2nonreachability_proof
      Nonreachable_Reverse
    XMLor xml_singleton (STR ''nonreachableCorewritePair'') (red_triple False)
      (Nonreachable_Co_Rewrite_Pair default_rel_impl)
    XMLor xml_singleton (STR ''nonreachableEquationalDisproof'') xml2equational_disproof
       Nonreachable_Equational_Disproof
    XMLor (XMLdo (STR ''nonreachableFGCR'') {
      eq \<leftarrow> XMLdo (STR ''eqSymbol'') {x \<leftarrow> xml2name; xml_return x};
      tr \<leftarrow> XMLdo (STR ''trueSymbol'') {x \<leftarrow> xml2name; xml_return x};
      fa \<leftarrow> XMLdo (STR ''falseSymbol'') {x \<leftarrow> xml2name; xml_return x};
      (rs, es, ro, p) \<leftarrow> xml2ordered_completion;
      xml_return (Nonreachable_FGCR eq tr fa es rs ro p)
    })
  ) id x"


definition "xml2nonjoinability_proof = xml_singleton (STR ''nonjoinabilityProof'') (
  xml_leaf (STR ''nonjoinableTcap'') Nonjoinable_Tcap
  XMLor xml_change xml2nonreachability_proof (xml_return \<circ> Nonjoinable_Ground_NF)
  ) id"

definition xml2inline_cond_info
  where "xml2inline_cond_info = XMLdo (STR ''inlinedRules'') {
    ret \<leftarrow>* XMLdo (STR ''inlinedRule'') {
      rule \<leftarrow> crule xml2name termIndexMap (STR ''rule'');
      conds \<leftarrow> conditions xml2name termIndexMap (STR ''inlinedConditions'');
      xml_return (rule,conds)
    };
    xml_return ret
  }"

partial_function (sum_bot) xml2infeasibility_proof :: "(_,_,_,_) infeasibility_proof xmlt"
where [code]: "xml2infeasibility_proof x = xml_singleton (STR ''infeasibilityProof'') (
    xml_pair (STR ''infeasibleCompoundConditions'')
      xml2name
      xml2nonreachability_proof
      Infeasible_Compound_Conditions
    XMLor xml_pair (STR ''infeasibleEquation'')
      (rule xml2name termIndexMap ruleMap)
      xml2nonreachability_proof
      (\<lambda>(l, r). Infeasible_Equation l r)
    XMLor xml_pair (STR ''infeasibleSubset'')
      (rules xml2name termIndexMap ruleMap)
      xml2infeasibility_proof
      Infeasible_Subset
    XMLor xml_tuple4 (STR ''infeasibleRhssEqual'')
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
      xml2nonjoinability_proof
      Infeasible_Rhss_Equal
    XMLor xml_tuple4 (STR ''infeasibleTrans'')
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
      xml2nonreachability_proof
      Infeasible_Trans
    XMLor xml_pair (STR ''infeasibleSplitIf'')
      split_if_info
      xml2nonreachability_proof
      Infeasible_Split_If
    XMLor xml_triple (STR ''infeasibleGoalLifting'')
      xml2name
      xml2name
      xml2infeasibility_proof
      Infeasible_Goal_Lifting
    XMLor xml_pair (STR ''ifritRules'')
      (XMLdo (STR ''rules'') { ret \<leftarrow>* crule xml2name termIndexMap (STR ''rule''); xml_return ret })
      xml2infeasibility_proof
      (Infeasible_Transform \<circ> Ifrit_Rules_Inf)
    XMLor xml_triple (STR ''leftInlineConditions'')
      (XMLdo (STR ''rules'') { ret \<leftarrow>* crule xml2name termIndexMap (STR ''rule''); xml_return ret })
      xml2inline_cond_info
      xml2infeasibility_proof
      (Infeasible_Transform \<circ>\<circ> Left_Inline_Conditions_Inf)
    XMLor xml_triple (STR ''rightInlineConditions'')
      (XMLdo (STR ''rules'') { ret \<leftarrow>* crule xml2name termIndexMap (STR ''rule''); xml_return ret })
      xml2inline_cond_info
      xml2infeasibility_proof
      (Infeasible_Transform \<circ>\<circ> Right_Inline_Conditions_Inf)
  ) id x"

definition "xml2ao_infeasibility_proof = xml_singleton (STR ''aoInfeasibilityProof'') (
  xml_change xml2infeasibility_proof (xml_return \<circ> AO_Infeasibility_Proof)
  XMLor xml_tuple4 (STR ''aoLhssEqual'')
    (term xml2name termIndexMap)
    (term xml2name termIndexMap)
    (term xml2name termIndexMap)
    xml2nonjoinability_proof
    AO_Lhss_Equal
  ) id"

definition xml2infeasible_conds
where
  "xml2infeasible_conds = xml_many (STR ''infeasibleConditions'')
    (xml_pair (STR ''infeasibleCondition'')
      (conditions xml2name termIndexMap (STR ''conditions''))
      xml2infeasibility_proof
      Pair)
    id"

definition xml2ao_infeasible_conds
where
  "xml2ao_infeasible_conds = xml_many (STR ''aoInfeasibleConditions'')
    (xml_triple (STR ''aoInfeasibleCondition'')
      (conditions xml2name termIndexMap (STR ''conditions''))
      (conditions xml2name termIndexMap (STR ''conditions''))
      xml2ao_infeasibility_proof
      (\<lambda>cs\<^sub>1 cs\<^sub>2 p. (cs\<^sub>1, cs\<^sub>2, p)))
    id"

partial_function_mr (sum_bot) cstep :: "(_, _) cstep_proof xmlt"
     and csteps :: "(_, _) cstep_proof list xmlt"
where
  "cstep x = xml_tuple6 (STR ''conditionalRewriteStep'')
    (crule xml2name termIndexMap (STR ''rule''))
    pos
    (CPF_Proof_Parser.subst xml2name termIndexMap)
    (xml_singleton (STR ''source'') (term xml2name termIndexMap) id)
    (xml_singleton (STR ''target'') (term xml2name termIndexMap) id)
    (xml_many (STR ''conditions'') csteps id)
    (\<lambda>r p s t u qs. Cstep_step r p (mk_subst Var s) t u qs) x"
| "csteps x = xml_many (STR ''conditionalRewritingSequence'') cstep id x"

definition xml2feasibility_proof :: "(_,_) feasibility_proof xmlt"
  where "xml2feasibility_proof x = xml_singleton (STR ''feasibilityProof'') (
    XMLdo (STR ''substitutionAndSteps'') {
      sigma \<leftarrow> CPF_Proof_Parser.subst xml2name termIndexMap;
      prfs \<leftarrow>* csteps;
      xml_return (Feasible_Witness sigma prfs)
    }
  ) id x"

definition xml2const_map :: "(_ \<Rightarrow> string option) xmlt"
where
  "xml2const_map = xml_many (STR ''constMap'') (xml_pair (STR ''entry'')
    (xml_singleton (STR ''symbol'') xml2name id)
    (xml_text (STR ''const''))
    Pair)
    (\<lambda>xs. map_of xs)"

definition xml2context_joinable_proof :: "(_, _) context_joinable_proof xmlt"
where
  "xml2context_joinable_proof = xml_tuple4 (STR ''contextJoinabilityProof'')
    (term xml2name termIndexMap)
    (CPF_Proof_Parser.csteps xml2name termIndexMap)
    (CPF_Proof_Parser.csteps xml2name termIndexMap)
    xml2const_map
    (\<lambda>t ps qs m. Contextual_Join (orig_term m t) (map (orig_cstep m) ps) (map (orig_cstep m) qs))"

definition xml2context_joinable_ccps ::
  "((_, string) term \<times> (_, string) term \<times> (_, string) rules \<times> (_, string) context_joinable_proof) list xmlt"
where
  "xml2context_joinable_ccps = XMLdo (STR ''contextJoinableCCPs'') {
    ret \<leftarrow>* XMLdo (STR ''contextJoinableCCP'') {
      s \<leftarrow> term xml2name termIndexMap;
      t \<leftarrow> term xml2name termIndexMap;
      cs \<leftarrow> conditions xml2name termIndexMap (STR ''conditions'');
      p \<leftarrow> xml2context_joinable_proof;
      xml_return (s, t, cs, p)
    };
    xml_return ret
  }"

definition xml2unfeasible_proof :: "(_, string) unfeasible_proof xmlt"
where
  "xml2unfeasible_proof = xml_tuple5 (STR ''unfeasibilityProof'')
    (xml_triple (STR ''terms'')
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
      (term xml2name termIndexMap)
    (\<lambda>t u v. (t, u, v)))
    csteps
    csteps
    (xml_pair (STR ''rules'') (crule xml2name termIndexMap (STR ''rule'')) (crule xml2name termIndexMap (STR ''rule'')) Pair)
    xml2const_map
    (\<lambda>(t, u, v) ps qs (r, r') m.
      UnfeasibleOverlap (orig_term m t) (orig_term m u) (orig_term m v)
        (map (orig_cstep m) ps) (map (orig_cstep m) qs) r r')"

definition xml2unfeasible_ccps ::
  "((_, string) subst \<times> (_, string) unfeasible_proof) list xmlt"
where
  "xml2unfeasible_ccps = xml_many (STR ''unfeasibleCCPs'')
    (xml_pair (STR ''unfeasibleCCP'')
      (CPF_Proof_Parser.subst xml2name termIndexMap)
      xml2unfeasible_proof
      (\<lambda>s p. (subst_of s, p)))
    id"

definition xml2infeasible_rules_info
  where
    "xml2infeasible_rules_info = xml_many (STR ''infeasibleRules'')
      (xml_pair (STR ''infeasibleRule'')
        (crule xml2name termIndexMap (STR ''rule''))
        xml2infeasibility_proof
        Pair)
      id"

partial_function (sum_bot) xml2conditional_cr_proof ::
    "(_, _, string,_) conditional_cr_proof xmlt"
where [code]: "xml2conditional_cr_proof x = xml_singleton (STR ''conditionalCrProof'') (
    xml_singleton (STR ''unconditional'')
      xml2cr_proof
      Unconditional_CR
    XMLor xml_pair (STR ''unraveling'')
      unraveling_info
      xml2cr_proof
      Unravel_CR
    XMLor xml_triple (STR ''inlineConditions'')
      (XMLdo (STR ''rules'') { ret \<leftarrow>* crule xml2name termIndexMap (STR ''rule''); xml_return ret })
      xml2inline_cond_info
      xml2conditional_cr_proof
      (Transformation_CR \<circ>\<circ> Inline_Conditions_CCRT)
    XMLor xml_pair (STR ''infeasibleRuleRemoval'')
      xml2infeasible_rules_info
      xml2conditional_cr_proof
      (Transformation_CR \<circ> Infeasible_Rule_Removal_CCRT)
    XMLor xml_leaf (STR ''almostOrthogonal'') Almost_Orthogonal_CR
    XMLor xml_singleton (STR ''almostOrthogonalModuloInfeasibility'')
        xml2ao_infeasible_conds Almost_Orthogonal_Modulo_Infeasibility_CR'
    XMLor xml_tuple4 (STR ''al94'')
      xml2quasi_reductive_proof
      xml2context_joinable_ccps
      xml2infeasible_conds
      xml2unfeasible_ccps
      AL94_CR
  ) id x"

partial_function (sum_bot) xml2comm_proof :: "('f,'l,string) comm_proof xmlt"
  where [code]: "xml2comm_proof x = xml_singleton (STR ''comProof'') (       
      XMLdo (STR ''parallelClosed'') { n \<leftarrow> joinAutoBfs; xml_return (Parallel_Closed_Comm n)}
    XMLor XMLdo (STR ''developmentClosed'') { n \<leftarrow> joinAutoBfs; xml_return (Development_Closed_Comm n)}
    XMLor XMLdo (STR ''pcpClosed'') {
            hints_cp \<leftarrow> xml_singleton (STR ''ordinaryCriticalPairs'') (xml2cp_join_info xml2name termIndexMap) id;
            hints_pcp \<leftarrow> xml_singleton (STR ''parallelCriticalPairs'') (xml2cp_join_info xml2name termIndexMap) id;
            xml_return (PCP_Closed_Comm hints_cp hints_pcp)
         } 
    XMLor XMLdo (STR ''pcpRuleLabeling'') {
      lab \<leftarrow> CPF_Proof_Parser.rule_labeling_function xml2name termIndexMap ruleMap;
      lab' \<leftarrow>? CPF_Proof_Parser.rule_labeling_function xml2name termIndexMap ruleMap;
      joinsRS \<leftarrow> xml_singleton (STR ''joinsRS'') (xml2cp_join_info xml2name termIndexMap) id;
      joinsSR \<leftarrow> xml_singleton (STR ''joinsSR'') (xml2cp_join_info xml2name termIndexMap) id;
      xml_return (PCP_Rule_Lab_Comm (PCP_Sequences_Com 
         (rule_lab_repr_to_lab lab) 
         (map_option rule_lab_repr_to_lab lab') 
         joinsRS joinsSR))
    }
    XMLor XMLdo (STR ''compositionalPcpRuleLabeling'') {
      lab \<leftarrow> CPF_Proof_Parser.rule_labeling_function xml2name termIndexMap ruleMap;
      lab' \<leftarrow>? CPF_Proof_Parser.rule_labeling_function xml2name termIndexMap ruleMap;
      joinsRS \<leftarrow> xml_singleton (STR ''joinsRS'') (xml2cp_join_info xml2name termIndexMap) id;
      joinsSR \<leftarrow> xml_singleton (STR ''joinsSR'') (xml2cp_join_info xml2name termIndexMap) id;
      C \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      D \<leftarrow> xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id;
      subPrf \<leftarrow> xml2comm_proof;
      xml_return (PCP_Compositional_Rule_Lab_Comm C D (PCP_Sequences_Com 
         (rule_lab_repr_to_lab lab) 
         (map_option rule_lab_repr_to_lab lab') 
         joinsRS joinsSR) subPrf)
    }
    XMLor XMLdo (STR ''compositionalPcps'') {
      trsC \<leftarrow> xml_singleton (STR ''trsC'') (rules xml2name termIndexMap ruleMap) id;
      trsD \<leftarrow> xml_singleton (STR ''trsD'') (rules xml2name termIndexMap ruleMap) id;
      trsP \<leftarrow> xml_singleton (STR ''trsP'') (rules xml2name termIndexMap ruleMap) id;
      hintsP_RS \<leftarrow> xml2cp_join_info xml2name termIndexMap;
      hintsP_SR \<leftarrow> xml2cp_join_info xml2name termIndexMap;
      hintsRS \<leftarrow> xml2cp_join_info xml2name termIndexMap;
      hintsSR \<leftarrow> xml2cp_join_info xml2name termIndexMap;
      sn_prf \<leftarrow> xml2trs_termination_proof;
      com_prf \<leftarrow> xml2comm_proof;
      xml_return (Compositional_PCPS_Comm trsC trsD trsP hintsP_RS hintsP_SR hintsRS hintsSR sn_prf com_prf)
    }
    XMLor
      xml_singleton (STR ''swapTRSs'') xml2comm_proof Swap_Comm
    XMLor
      xml_singleton (STR ''switchToCrProof'') xml2cr_proof CR_Proof
    ) id x"

end
hide_const (open) string

type_synonym lsymbol = "(string, label_type) lab"

context
  fixes xml2name :: "lsymbol xmlt" 
  and termIndexMap :: "lsymbol termIndexMap" 
  and ruleMap :: "lsymbol ruleIndexMap" 
begin

partial_function (sum_bot) xml2non_join_info :: "(string lt,string,string,_) non_join_info xmlt" where
  [code]: "xml2non_join_info x = (
    xml_leaf (STR ''distinctNormalForms'') Diff_NFs
    XMLor xml_leaf (STR ''capNotUnif'') Tcap_Not_Unif
    XMLor xml_pair (STR ''subterm'')
        pos
        xml2non_join_info
        Subterm_NJ
    XMLor xml_pair (STR ''grounding'')
        (CPF_Proof_Parser.subst xml2name termIndexMap)
        xml2non_join_info
        Grounding
    XMLor xml_pair (STR ''emptyTreeAutomataIntersection'')
        (compatible_ta xml2name (STR ''firstAutomaton''))
        (compatible_ta xml2name (STR ''secondAutomaton''))
        (\<lambda> (ta1,rel1) (ta2,rel2). Tree_Aut_Intersect_Empty ta1 rel1 ta2 rel2)
    XMLor xml_singleton (STR ''differentInterpretation'')
        (CPF_Proof_Parser.sl_variant xml2name)
        Finite_Model_Gt
    XMLor xml_singleton (STR ''strictDecrease'')
        (CPF_Proof_Parser.redtriple xml2name Sharp False)
        (Discr_Pair_Gt default_rel_impl)
    XMLor xml_pair (STR ''argumentFilterNonJoin'')
        (CPF_Proof_Parser.afs xml2name)
        xml2non_join_info
        Argument_Filter_NJ
    XMLor XMLdo (STR ''usableRulesNonJoin'') {
      a \<leftarrow>? xml_leaf (STR ''left'') True XMLor xml_leaf (STR ''right'') False;
      case a of None \<Rightarrow> XMLdo {
          b \<leftarrow> xml2non_join_info;
          xml_return (Usable_Rules_Reach_NJ b)
        }
      | Some left \<Rightarrow> XMLdo {
          U \<leftarrow> xml_singleton (STR ''usableRules'') (rules xml2name termIndexMap ruleMap) id;
          p \<leftarrow> xml2non_join_info;
          xml_return (Usable_Rules_Reach_Unif_NJ (if left then Inl U else Inr U) p)
        }
    }
    XMLor xml_leaf (STR ''finitelyReachable'') Finitely_Reachable
  ) x"

partial_function (sum_bot) xml2ncomm_proof :: "(string, label_type,string,string) ncomm_proof xmlt"
where [code]: "xml2ncomm_proof x = (let rew = CPF_Proof_Parser.rsteps xml2name termIndexMap ruleMap in
    xml_singleton (STR ''comDisproof'') (
      xml_triple (STR ''nonJoinableFork'') rew rew
           xml2non_join_info
           (\<lambda> (s,seq1) (_,seq2). Non_Join_Comm s seq1 seq2)
      XMLor xml_singleton (STR ''swapTRSs'') xml2ncomm_proof Swap_Not_Comm
  ) id x)"

partial_function (sum_bot) xml2ncr_proof :: "(string, label_type,string,string) ncr_proof xmlt"
where [code]: "xml2ncr_proof x = (let rew = CPF_Proof_Parser.rsteps xml2name termIndexMap ruleMap in
    xml_singleton (STR ''crDisproof'') (
      XMLdo (STR ''nonWcrAndSN'') {
       _ \<leftarrow> xml_any;
       prf \<leftarrow> xml2trs_termination_proof xml2name termIndexMap ruleMap;
       xml_return (SN_NWCR prf)
    } XMLor xml_triple (STR ''nonJoinableFork'') rew rew
           xml2non_join_info
           (\<lambda> (s,seq1) (_,seq2). Non_Join s seq1 seq2)
    XMLor xml_pair (STR ''modularityDisjoint'')
        (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
        xml2ncr_proof
        NCR_Disj_Subtrs
    XMLor xml_triple (STR ''redundantRules'')
        (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
        (xml_nat (STR ''nrSteps''))
        xml2ncr_proof
      NCR_Redundant_Rules
    XMLor xml_triple (STR ''ruleRemoval'')
        (xml_singleton (STR ''removedRules'') (rules xml2name termIndexMap ruleMap) id)
        (xml_many (STR ''simulations'') 
           (xml_pair (STR ''ruleSimulation'')
              (rule xml2name termIndexMap ruleMap) 
              rew 
             (\<lambda> lr seq. Pair lr (snd seq)))
           id)
        xml2ncr_proof
        NCR_Rule_Removal
    XMLor xml_pair (STR ''persistentDecomposition'')
        (xml2ms_signature xml2name)
        (xml_pair (STR ''component'')
            (xml_singleton (STR ''trs'') (rules xml2name termIndexMap ruleMap) id)
            xml2ncr_proof
            (\<lambda> trs prf. (trs, prf)))
       (\<lambda> sig (trs, prf). NCR_Persistent_Decomposition sig trs prf)
  ) id x)"

partial_function (sum_bot) xml2conditional_ncr_proof ::
    "(string, label_type, string, string, _) conditional_ncr_proof xmlt"
where [code]: "xml2conditional_ncr_proof x = xml_singleton (STR ''conditionalCrDisproof'') (
    xml_singleton (STR ''unconditional'')
      xml2ncr_proof
      Unconditional_CNCR
    XMLor xml_triple (STR ''inlineConditions'')
      (XMLdo (STR ''rules'') {ret \<leftarrow>* crule xml2name termIndexMap (STR ''rule''); xml_return ret})
      (xml2inline_cond_info xml2name termIndexMap)
      xml2conditional_ncr_proof
      (Transformation_CNCR \<circ>\<circ> Inline_Conditions_CCRT)
    XMLor xml_pair (STR ''infeasibleRuleRemoval'')
      (xml2infeasible_rules_info xml2name termIndexMap ruleMap)
      xml2conditional_ncr_proof 
      (Transformation_CNCR \<circ> Infeasible_Rule_Removal_CCRT)
    XMLor xml_tuple4 (STR ''nonJoinableFork'')
      (xml_triple (STR ''terms'')
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
        (term xml2name termIndexMap)
      (\<lambda>s t u. (s, t, u)))
      (CPF_Proof_Parser.csteps xml2name termIndexMap)
      (CPF_Proof_Parser.csteps xml2name termIndexMap)
      xml2non_join_info
      (\<lambda>(s, t, u) ps qs i. Non_Join_CNCR s t u ps qs i)
  ) id x"

definition "proof" :: "(string, label_type, string)proof xmlt"
where
  "proof = XMLdo (STR ''proof'') {
      p \<leftarrow> xml_change (xml2trs_termination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> TRS_Termination_Proof)
        XMLor xml_change (xml2trs_nontermination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> TRS_Nontermination_Proof)
        XMLor xml_change (xml2reltrs_nontermination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Relative_TRS_Nontermination_Proof)
        XMLor xml_change (xml2cr_proof xml2name termIndexMap ruleMap) (xml_return \<circ> TRS_Confluence_Proof)
        XMLor xml_change xml2ncr_proof (xml_return \<circ> TRS_Non_Confluence_Proof)
        XMLor xml_change (xml2dp_termination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> DP_Termination_Proof)
        XMLor xml_change (xml2dp_nontermination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> DP_Nontermination_Proof)
        XMLor xml_change (xml2completion_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Completion_Proof)
        XMLor xml_change (xml2ordered_completion_proof xml2name termIndexMap) (xml_return \<circ> Ordered_Completion_Proof)
        XMLor xml_change (xml2equational_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Equational_Proof)
        XMLor xml_change (xml2equational_disproof xml2name termIndexMap ruleMap) (xml_return \<circ> Equational_Disproof)
        XMLor xml_change (xml2complexity_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Complexity_Proof)
        XMLor xml_change (xml2quasi_reductive_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Quasi_Reductive_Proof)
        XMLor xml_change (xml2conditional_cr_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Conditional_CR_Proof)
        XMLor xml_change xml2conditional_ncr_proof (xml_return \<circ> Conditional_Non_CR_Proof)
        XMLor xml_change xml2ncomm_proof (xml_return \<circ> TRS_Non_Commutation_Proof)
        XMLor xml_change (xml2comm_proof xml2name termIndexMap ruleMap) (xml_return \<circ> TRS_Commutation_Proof)
        XMLor xml_singleton (STR ''treeAutomatonClosedProof'') closed_criterion Tree_Automata_Closed_Proof
        XMLor xml_change (xml2ac_termination_proof xml2name termIndexMap ruleMap) (xml_return \<circ> AC_Termination_Proof)
        XMLor xml_singleton (STR ''ltsTerminationProof'') lts_termination_proof_parser LTS_Termination_Proof
        XMLor xml_singleton (STR ''ltsSafetyProof'') lts_safety_proof_parser LTS_Safety_Proof
        XMLor xml_change (xml2infeasibility_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Infeasibility_Proof)
        XMLor xml_change (xml2feasibility_proof xml2name termIndexMap) (xml_return \<circ> Feasibility_Proof)
        XMLor xml_change (xml2unknown_proof xml2name termIndexMap ruleMap) (xml_return \<circ> Unknown_Proof)
        XMLor xml_change (xml2unknown_disproof xml2name termIndexMap ruleMap) (xml_return \<circ> Unknown_Disproof);
      xml_return p
    }"
end

partial_function (sum_bot) symbol_parser :: "lsymbol xmlt"
where [code]: "symbol_parser x = (
    xml_change (xml_text (STR ''name'')) (xml_return \<circ> UnLab)
    XMLor xml_singleton (STR ''sharp'') symbol_parser Sharp
    XMLor xml_pair (STR ''labeledSymbol'') symbol_parser (
        xml_many (STR ''numberLabel'') (xml_nat (STR ''number'')) Inl
        XMLor xml_many (STR ''symbolLabel'') symbol_parser Inr
      )
      (\<lambda>f l. case l of
        Inl ls  \<Rightarrow> Lab f ls
      | Inr ls \<Rightarrow> FunLab f ls)
  ) x"

definition "proof_parser = proof symbol_parser" 
definition "input_parser = input symbol_parser" 
definition "answer_parser = answer symbol_parser" 
definition "property_parser = property symbol_parser" 
end
