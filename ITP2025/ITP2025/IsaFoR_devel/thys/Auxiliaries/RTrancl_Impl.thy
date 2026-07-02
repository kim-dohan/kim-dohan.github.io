(* Dohan Kim, René Thiemann *)
theory RTrancl_Impl imports Main
begin

context 
  fixes R :: "'a rel" 
  and succsR :: "'a \<Rightarrow> 'a list" 
begin

(* we store the set of all visited elements as list ts (for result) and as set tsS (for efficient membership test) *)
partial_function (option) all_reachable_main :: "'a set \<Rightarrow> 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list option" where
  [code]: "all_reachable_main tsS ts todos = (let n_terms = List.maps succsR todos;
     really_new = filter (\<lambda> t. t \<notin> tsS) n_terms
    in if really_new = [] then Some ts else all_reachable_main (foldr insert really_new tsS) (really_new @ ts) really_new)" 


lemma all_reachable_main: assumes "all_reachable_main tsS ts us = Some reach"
  and succsR[simp]: "\<And> x. set (succsR x) = { y. (x,y) \<in> R}"  
shows "tsS = set ts \<longrightarrow> set ts = (\<Union> i \<le> n. (R^^i) `` I) \<longrightarrow> set us = (R ^^ n) `` I - (\<Union> i < n. (R^^i) `` I) \<longrightarrow> set reach = R^* `` I"  
proof (induct arbitrary: n rule: all_reachable_main.raw_induct[OF _ assms(1)])
  case (1 all_reachable_main tsS ts todos reach n)
  define n_terms where "n_terms =  List.maps succsR todos"
  define really_new where "really_new = filter (\<lambda> t. t \<notin> tsS) n_terms"
  note result = 1(2)[unfolded Let_def, folded n_terms_def, folded really_new_def]
  show ?case
  proof (intro impI)
    assume ts:"set ts = (\<Union>i\<le>n. (R ^^ i) `` I)"
      and tsS: "tsS = set ts" 
      and todo: "set todos = (R ^^ n) `` I - (\<Union>i<n. (R ^^ i) `` I)" 
    have really_new: "really_new = filter (\<lambda> t. t \<notin> set ts) n_terms" unfolding really_new_def tsS by auto
    have todo_ts:"set todos \<subseteq> set ts" using todo ts by auto
    from todo show "set reach = R\<^sup>* `` I"
    proof(cases "really_new = []")
      case True
      with result have rts: "reach = ts" by (auto split: if_splits)
      from True have sr:"set really_new = {}" by auto
      note todor = this[unfolded really_new n_terms_def List.maps_def, simplified]
      have one_step_closed: "s \<in> set todos \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> t \<in> set reach" for s t using rts todor by auto
      have one_step_closed_ts: "s \<in> set ts \<Longrightarrow> (s, t) \<in> R \<Longrightarrow> t \<in> set ts" for s t
      proof -
        assume s:"s \<in> set ts"
        then show "(s, t) \<in> R \<Longrightarrow> t \<in> set ts" for t
        proof -
          assume st:"(s, t) \<in> R"
          then show "t \<in> set ts"
          proof(cases "s \<in> set todos")
            case True
            with this[unfolded really_new n_terms_def List.maps_def, simplified]
            show ?thesis using one_step_closed[of s t] st todor by auto
          next
            case False
            hence "s \<in> (\<Union>i<n. (R ^^ i) `` I)" using ts todo s by force
            then obtain u where u:"u \<in> I" and us:"(u, s) \<in> (\<Union>i<n. (R ^^ i))" by auto
            then obtain m where mn:"m < n" and "(u, s) \<in> (R ^^ m)" by auto
            then have ut:"(u, t) \<in> (R ^^ (m + 1))" using st by auto
            from mn have "m + 1 \<le> n" by auto
            with ut have "(u, t) \<in> (\<Union>i\<le>n. (R ^^ i))" by force
            then show ?thesis using u ts by auto
          qed
        qed
      qed
      have starclosed:"(s, t) \<in> R\<^sup>* \<Longrightarrow> s \<in> set ts \<Longrightarrow> t \<in> set ts" for s t 
        by (induct rule: rtrancl_induct, insert one_step_closed_ts, auto)
      then show ?thesis 
      proof -
        have sub1:"set ts \<subseteq> R\<^sup>* `` I" using ts 
          using relpow_imp_rtrancl by force
        have sub2:"R\<^sup>* `` I \<subseteq> set ts" 
        proof -
          { fix t
            assume "t \<in> R\<^sup>* `` I"
            then obtain u where "u \<in> I" and ut:"(u, t) \<in> R\<^sup>*" by auto
            hence "u \<in> (R ^^ 0) `` I" by auto
            hence "u \<in> set ts" using ts by fastforce
            hence "t \<in> set ts" using ut starclosed by auto
          } then show ?thesis by auto
        qed
        then show ?thesis using sub1 sub2 rts by auto
      qed
    next
      case False
      let ?tsS' = "foldr insert really_new tsS" 
      from False result have all:"all_reachable_main ?tsS' (really_new @ ts) really_new = Some reach" by auto
      from 1(1)[OF this, of "n + 1"] False
      have srn:"set really_new \<noteq> {}" by auto
      have rts:"(\<Union>i<n + 1. (R ^^ i) `` I) = set ts"
      proof -
        have "(\<Union>i<n + 1. (R ^^ i) `` I) = (\<Union>i\<le>n. (R ^^ i) `` I)" by fastforce
        moreover have "... = set ts" using ts by auto
        ultimately show "(\<Union>i<n + 1. (R ^^ i) `` I) = set ts" by simp
      qed
      have rn: "set really_new = (R ^^ (n + 1)) `` I - set ts"
      proof -
        have sub1:"set really_new \<subseteq> (R ^^ (n + 1)) `` I - set ts"
        proof 
          fix s
          assume s:"s \<in> set really_new"
          then show "s \<in> (R ^^ (n + 1)) `` I - set ts"
          proof -
            from s[unfolded really_new n_terms_def List.maps_def, simplified]
            obtain td where td:"td \<in> set todos" and "(td, s) \<in> R" and "s \<notin> set ts" by auto
            thus ?thesis using s ts todo by auto
          qed
        qed
        have sub2:"((R ^^ (n + 1)) `` I - set ts) \<subseteq> set really_new"
        proof
          fix s
          assume s:"s \<in> (R ^^ (n + 1)) `` I - set ts"
          hence snts:"s \<notin> set ts" by auto
          then show "s \<in> set really_new"
          proof -
            { assume asm:"s \<notin> set really_new"
              from this[unfolded really_new n_terms_def List.maps_def, simplified]
              have tots:"(\<forall>x\<in>set todos. (x, s) \<notin> R) \<or> s \<in> set ts" by auto
              hence False using asm
              proof(cases "s \<in> set ts")
                case True
                then show ?thesis using snts by auto
              next
                case False
                then have ntodo:"(\<forall>x\<in>set todos. (x, s) \<notin> R)" using tots by auto
                from s obtain u where u:"u \<in> (R ^^ n) `` I" and us:"(u, s)\<in> R" by auto
                have si:"s \<in> (R ^^ (n + 1)) `` I" using s by auto
                hence sn: "s \<notin> (\<Union>i\<le>n. (R ^^ i) `` I)" using s ts by auto
                hence "u \<notin> (\<Union>i<n. (R ^^ i) `` I)"
                proof -
                  { assume asm:"u \<in> (\<Union>i<n. (R ^^ i) `` I)"
                    with us have "s \<in> (\<Union>i\<le>n. (R ^^ i) `` I)"
                    proof -
                      from asm obtain init where init:"init \<in> I" and "(init, u) \<in> (\<Union>i<n. (R ^^ i))" by auto
                      then obtain m where "(init, u) \<in> R ^^ m" and mn:"m < n" by auto
                      with us have inits:"(init, s) \<in> R ^^ (m + 1)" by auto
                      from mn have "m + 1 \<le> n" by auto
                      with inits have "(init, s) \<in> (\<Union>i\<le>n. (R ^^ i))" by force
                      with init show ?thesis by auto
                    qed
                    then have False using sn by auto 
                  } then show ?thesis by auto
                qed
                hence "u \<in> set todos" using todo s using u by auto
                then show ?thesis using ntodo us by auto
              qed
            } then show ?thesis by auto
          qed
        qed
        then show ?thesis using sub1 sub2 by auto
      qed
      have rtseq:"(\<Union>i\<le>n + 1. (R ^^ i) `` I) = ((R ^^ (n + 1)) `` I) \<union> set ts" 
        using ts atMost_Suc by force
      have id: "?tsS' = set (really_new @ ts)" unfolding set_append tsS[symmetric]
        by (induct really_new arbitrary: tsS, auto)
      have "set (really_new @ ts) = ((R ^^ (n + 1)) `` I) \<union> set ts" 
        using rn set_append[of "really_new" "ts"] Un_Diff_cancel by auto
      then show ?thesis using rtseq rn 1(1)[OF all, of "n + 1"] rts id by auto
    qed
  qed
qed

partial_function (option) rtrancl_option :: "'a list  \<Rightarrow> 'a list option" where
  [code]: "rtrancl_option ts = all_reachable_main (set ts) ts ts"

lemma rtrancl_option: assumes asm_reach:"rtrancl_option ts = Some reach"
  and succsR[simp]: "\<And> x. set (succsR x) = { y. (x,y) \<in> R}"
  and ts:"set ts = I"
shows "set reach = R^* `` I"
proof -
  have "rtrancl_option ts = all_reachable_main (set ts) ts ts" 
    by (simp add: rtrancl_option.simps)
  with asm_reach have "all_reachable_main (set ts) ts ts = Some reach" by simp
  hence IH:"\<forall>n. set ts = (\<Union> i \<le> n. (R^^i) `` I) \<longrightarrow> set ts = (R ^^ n) `` I - (\<Union> i < n. (R^^i) `` I) \<longrightarrow> set reach = R^* `` I"
    using all_reachable_main by force
  then show ?thesis using assms by fastforce
qed

end
end
