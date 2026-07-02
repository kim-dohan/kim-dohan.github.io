(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2009-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2009-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Ceta_Verifier
imports 
  CPF_Parser
  Framework.QDP_Framework_Impl
  Framework.Dependency_Pair_Problem_Impl
  Framework.Termination_Problem_Impl
  Framework.AC_Dependency_Pair_Problem_Impl
  Framework.AC_Termination_Problem_Impl
begin

(*
abbreviation drop_white_space :: "string \<Rightarrow> string" where
  "drop_white_space \<equiv> filter (\<lambda>c. c \<notin> set wspace)"

definition eq_white_space :: "string \<Rightarrow> string \<Rightarrow> bool" (infix "=\<^sub>w" 50) where
  "s1 =\<^sub>w s2 \<longleftrightarrow> debug (showsl_lit (STR ''0''))
    (STR ''comparing whether parsed input corresponds to real input'')
    (drop_white_space s1 = s2)"

fun find_ctxt_len :: "string \<Rightarrow> string \<Rightarrow> nat \<Rightarrow> (string \<times> string) option"
where
  "find_ctxt_len [] ys n = None" |
  "find_ctxt_len xs ys n =
    (if take n xs = ys then Some ([], drop n xs)
    else do {
      (us, vs) \<leftarrow> find_ctxt_len (tl xs) ys n;
      Some (hd xs # us, vs)
    })"

lemma find_ctxt_len_sound:
  fixes t s before after :: string
  assumes "find_ctxt_len t s n = Some (before, after)"
  shows "t = (before @ s @ after)"
using assms
proof (induct t arbitrary: before)
  case Nil
  then show ?case by (cases s) auto
next
  case (Cons h tt)
  show ?case 
  proof (cases "take n (h # tt) = s")
    case True
    with Cons show ?thesis by auto 
  next
    case False with \<open>find_ctxt_len (h # tt) s n = Some (before, after)\<close> 
    have res: "(case find_ctxt_len tt s n of None \<Rightarrow> None | Some (bef,aft) \<Rightarrow> Some (h # bef, aft)) =
      Some (before, after)" by (auto split: bind_splits)
    show ?thesis 
    proof (cases "find_ctxt_len tt s n")
      case None with res show ?thesis by auto
    next
      case (Some befaft)
      show ?thesis
      proof (cases befaft)
        case (Pair bef aft)
        with Some res
          have "find_ctxt_len tt s n = Some (bef, aft) \<and> before = h # bef \<and> after = aft" by auto
        with Cons show ?thesis by auto
      qed
    qed
  qed
qed

declare find_ctxt_len.simps [simp del]    

abbreviation find_ctxt :: "string \<Rightarrow> string \<Rightarrow> (string \<times> string) option" where
  "find_ctxt t s \<equiv> find_ctxt_len t s (length s)"

definition starts_with :: "string \<Rightarrow> string \<Rightarrow> bool" where
  "starts_with t s \<longleftrightarrow> take (length s) (trim t) = s"

abbreviation s_proof :: string where "s_proof \<equiv> ''<proof>''"
abbreviation s_input :: string where "s_input \<equiv> ''<input>''"
abbreviation e_input :: string where "e_input \<equiv> ''</input>''"

definition extract_input_proof :: "string \<Rightarrow> (string \<times> string \<times> string) option"
where
  "extract_input_proof s = do {
    (_, minput) \<leftarrow> find_ctxt (drop_white_space s) s_input;
    (input, s') \<leftarrow> find_ctxt minput e_input;
    (version, proof) \<leftarrow> find_ctxt s' s_proof;
    Some (input, version, proof)
  }"

lemma extract_input_proof_sound: 
  assumes res: "extract_input_proof s = Some (the_input, version, the_proof)"
  shows "\<exists>t. s =\<^sub>w (t @ ''<input>'' @ the_input @ ''</input>'' @ version @ ''<proof>'' @ the_proof)"
proof (cases "find_ctxt (drop_white_space s) s_input")
  case None
  with res show ?thesis by (auto simp: extract_input_proof_def)
next
  case (Some bef_minput)
  note extract_input_proof_def [simp]
  let ?s = "drop_white_space s"
  show ?thesis
  proof (cases bef_minput)
    case (Pair bef minput)
    with Some have s1: "find_ctxt ?s s_input = Some (bef, minput)" by auto
    show ?thesis 
    proof (cases "find_ctxt minput e_input")
      case None
      with res s1 show ?thesis by auto
    next
      case (Some input_sp)
      show ?thesis
      proof (cases input_sp)
        case (Pair tthe_input s')
        with Some s1 have s2: "find_ctxt minput e_input = Some (tthe_input, s')" by auto
        show ?thesis
        proof (cases "find_ctxt s' s_proof")
          case None 
          with res s1 s2 show ?thesis by auto
        next
          case (Some vers_proof)
          show ?thesis
          proof (cases vers_proof)
            case (Pair _ _)
            with Some s1 s2 res have s3: "find_ctxt s' s_proof = Some (version, the_proof)" by auto  
            from res s1 s2 s3 have input: "tthe_input = the_input" by simp
            from s1 have sp1: "?s = (bef @ s_input @ minput)" by (rule find_ctxt_len_sound)
            from s2 have sp2: "minput = (tthe_input @ e_input @ s')" by (rule find_ctxt_len_sound)
            from s3 have sp3: "s' = (version @ s_proof @ the_proof)" by (rule find_ctxt_len_sound)            
            from sp1 sp2 sp3
              have sp: "?s = (bef @ s_input @ tthe_input @ e_input @ version @ s_proof @ the_proof)"
              (is "_ = ?r")
              by simp
            have eq: "s =\<^sub>w ?r" unfolding eq_white_space_def sp by simp
            show ?thesis
              by (rule exI [of _ bef], rule eq [unfolded input])
          qed
        qed
      qed
    qed
  qed
qed
*)

text \<open>Here we choose the implementation.\<close>

abbreviation tp_impl where "tp_impl \<equiv> tp_rbt_impl"
abbreviation dpp_impl where "dpp_impl \<equiv> dpp_rbt_impl"
abbreviation ac_tp_impl where "ac_tp_impl \<equiv> ac_tp_list_impl"
abbreviation ac_dpp_impl where "ac_dpp_impl \<equiv> ac_dpp_rbt_impl"

definition bind2' :: "'a +\<^sub>\<bottom>'b \<Rightarrow> ('a \<Rightarrow> cert_result) \<Rightarrow> ('b \<Rightarrow> cert_result) \<Rightarrow> cert_result" where
  "bind2' x f g = (case x of 
      Left a \<Rightarrow> f a
    | Right b \<Rightarrow> g b
    | Bottom \<Rightarrow> Error (STR ''nontermination''))" 

lemma bind2'_code[code]:
  "bind2' (sumbot a) f g = (case a of Inl a \<Rightarrow> f a | Inr b \<Rightarrow> g b)"
  by (cases a) (auto simp: bind2'_def)
 
definition certify_proof :: "bool \<Rightarrow> string option \<Rightarrow> string option \<Rightarrow> string option \<Rightarrow> string \<Rightarrow> cert_result" where
  "certify_proof a inp_o prop_o answ_o prfs \<equiv>
    bind2' (parse_combined_cert_problem inp_o prop_o answ_o prfs) Unsupported 
     (\<lambda> (inp, prop, answ, prf). certify_cert_problem tp_impl dpp_impl ac_tp_impl ac_dpp_impl a inp prop answ prf)" 

(*
theorem certify_proof_sound:
  assumes ret: "certify_proof False (Some input_str) (Inr claim_str) proof_str = Certified"
  notes [simp] = certify_proof_def bind2_def bind2'_def
  shows "\<exists>input claim.
    parse_xtc plain_name input_str = Right input \<and>
    parse_claim plain_name claim_str = Right claim \<and>
    desired_property input claim"
proof (cases "parse_xtc plain_name input_str")
  case [simp]: (Right input)
  show ?thesis
  proof (cases "parse_claim plain_name claim_str :: string +\<^sub>\<bottom> ((string, nat list) lab, string) claim")
    case [simp]: (Right claim)
    show ?thesis
    proof (cases "parse_cert_problem proof_str")
      case [simp]: (Right "proof")
      note main = certify_cert_problem_sound[OF tp_rbt_impl dpp_rbt_impl ac_tp_list_impl ac_dpp_rbt_impl]
      show ?thesis using ret by (cases "proof", auto intro: main)
    qed (insert ret, auto)
  qed (insert ret, auto)
qed (insert ret, auto)
*)

(*
definition max_tag :: nat where
  "max_tag = 29"

lemma max_tag:
  assumes ti: "tp_spec ti" and di: "dpp_spec di" and ati: "ac_tp_spec ati" and adi: "ac_dpp_spec adi"
    and res: "certify_cert_problem ti di ati adi a input claim proof = Certified"
  shows "length tag \<le> max_tag"
proof -
  from certify_cert_problem_with_assms_sound [OF ti di ati adi res]
    have tag: "tag = xml_tag cp" by simp
  show ?thesis 
  proof (cases cp)
    case (TRS_Termination_Proof nfs a b c d)
    thus ?thesis unfolding max_tag_def tag by (cases c) auto
  qed (auto simp: max_tag_def tag)
qed
*)

definition eval_list :: "'a list \<Rightarrow> string +\<^sub>\<bottom> 'a list" where 
  "eval_list x = return x"

(* function which enforces that a list is strictly evaluated within the monad *)

fun eval_list_haskell :: "'a list \<Rightarrow> string +\<^sub>\<bottom> 'a list" where
  "eval_list_haskell (x # xs) = do {ys \<leftarrow> eval_list_haskell xs; return (x # ys)}"
| "eval_list_haskell [] = return []"

lemma eval_list_haskell:
  "eval_list = eval_list_haskell"
proof (rule ext, rule sym)
  fix xs :: "'a list"
  show "eval_list_haskell xs = eval_list xs" by (induct xs) (auto simp: eval_list_def)
qed

lemma trim_take:
  "trim (take n (trim xs)) = take n (trim xs)"
proof (induct xs arbitrary: n)
  case (Cons x xs)
  then show ?case by (cases n) (auto simp: trim_def)
qed (simp add: trim_def)


(*
  )
  | None \<Rightarrow> (try
    (case extract_input_proof s of
      None \<Rightarrow> return (Unsupported ''could not extract input and proof from given string'')
    | Some (the_input, version, the_proof) \<Rightarrow>
      do {
       short_prf \<leftarrow> eval_list (take max_tag (trim the_proof)); (* to enable garbage collection of the_proof *)
       cp \<leftarrow> parse_cert_problem None s;
       return
         (if show (xml_cert_problem cp) =\<^sub>w the_input then
           (case certify_cert_problem tp_impl dpp_impl ac_tp_impl ac_dpp_impl a cp of
             Certified tag \<Rightarrow>
               if starts_with short_prf tag then Certified tag
               else Error (''proven property '' @ tag @
                 '' does not correspond to proof in input string: '' @ short_prf)
           | e \<Rightarrow> e)
         else Unsupported (concat [''parsed problem does not correspond to input'', [CHR ''\<newline>''], 
           ''input:'', [CHR ''\<newline>''], drop_white_space the_input, [CHR ''\<newline>''], [CHR ''\<newline>''],
           ''parsed:'', [CHR ''\<newline>''], drop_white_space (show (xml_cert_problem cp)), [CHR ''\<newline>'']]))
      }) catch (\<lambda> err. return (Unsupported (''error while parsing'' @ [CHR ''\<newline>''] @ err))))"


text \<open>
If the certifier gives an answer then

\begin{itemize}

\item
the given string contains an input and a proof of some desired property,

\item
there is a certification problem whose string representation is exactly the same (modulo white
space) as the input contained in the given string and the desired properties are identical, and

\item
the desired property holds for the certification problem (possibly modulo some assumptions that are
explicitly indicated).

\end{itemize}
\<close>
lemma certify_proof_sound: 
  assumes answer: "certify_proof a None s = return Certified"
  shows "\<exists>input the_problem the_input version the_proof. 
    s =\<^sub>w the_problem @ ''<input>'' @ the_input @ ''</input>''@ version @ ''<proof>'' @ the_proof \<and>
    show (xml_input input) =\<^sub>w the_input \<and>
    starts_with the_proof (xml_tag cp) \<and>
    xml_tag cp = answer \<and> ((\<forall>p\<in>set (cert_assms a cp). holds p) \<longrightarrow> desired_property the_input claim)"
proof -
  note impl = tp_impl dpp_impl ac_tp_impl ac_dpp_impl
  note answer = answer [unfolded certify_proof_def]
  from answer obtain triple where ex: "extract_input_proof s = Some triple"
    by (cases "extract_input_proof s") auto
  obtain the_input version the_proof
    where triple: "triple = (the_input, version, the_proof)" by (cases triple) auto
  note ex = ex [unfolded triple]
  from extract_input_proof_sound [OF ex] obtain bef
    where problem: "s =\<^sub>w bef @ s_input @ the_input @ e_input @ version @ s_proof @ the_proof" ..
  def short \<equiv> "take max_tag (trim the_proof)"
  note answer = answer [unfolded ex option.simps prod.simps eval_list_def short_def [symmetric] return_def]
  from answer obtain cp where parse: "parse_cert_problem None s = Right cp"
    by (cases "parse_cert_problem None s") auto
  note answer = answer [unfolded parse]
  from answer have eqw: "show (xml_cert_problem cp) =\<^sub>w the_input" by (cases ?thesis) auto
  from answer eqw obtain answ
    where cert: "certify_cert_problem tp_impl dpp_impl ac_tp_impl ac_dpp_impl a cp = Certified answ"
    by (auto split: cert_result.splits)
  from certify_cert_problem_with_assms_sound [OF impl cert]
    have sound: "(\<forall>p\<in>set (cert_assms a cp). holds p) \<longrightarrow> desired_property cp"
    and xml: "xml_tag cp = answ" by auto
  from max_tag [OF impl cert] have len: "length answ \<le> max_tag" by auto
  from answer cert eqw have start: "starts_with short answ" by (cases ?thesis) auto
  from answer cert eqw start have answ: "answer = answ" by auto
  have "starts_with the_proof (xml_tag cp) = (take (length answ) (trim the_proof) = answ)"
    unfolding xml short_def starts_with_def by simp
  also have "\<dots> = (take (length answ) (trim the_proof) = take (length answ) (trim short))"
    using start unfolding starts_with_def by simp
  also have "trim short = trim (take max_tag (trim the_proof))" unfolding short_def by simp
  also have "\<dots> = take max_tag (trim the_proof)" unfolding trim_take by simp
  also have "take (length answ) (trim the_proof) = take (length answ) (take max_tag (trim the_proof))"
    by (metis length_take take_all take_take len)
  finally have start: "starts_with the_proof (xml_tag cp)" by simp
  show ?thesis
    unfolding answ append_def
    by (intro exI conjI, rule problem, rule eqw, rule start, rule xml, rule sound)
qed
*)

end
