(*
Author:  Christian Sternagel <c.sternagel@gmail.com> (2012-2015)
Author:  René Thiemann <rene.thiemann@uibk.ac.at> (2011-2015)
License: LGPL (see file COPYING.LESSER)
*)
theory Generic_Usable_Rules
imports
  Ord.Term_Order
  TRS.Q_Restricted_Rewriting
  First_Order_Rewriting.Trs_Impl
begin

type_synonym ('f,'v)usable_rules_checker = "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> 'f af \<Rightarrow> ('f,'v)terms \<Rightarrow> ('f,'v)rules \<Rightarrow> ('f,'v)rules option \<Rightarrow> ('f,'v)trs \<Rightarrow> ('f,'v)rules option"

definition usable_rules_checker :: "('f,'v)usable_rules_checker \<Rightarrow> bool"
  where "usable_rules_checker checker \<equiv> \<forall> nfs m c Q R \<pi> U_opt sts U S NS. checker nfs m c (wwf_qtrs Q (set R)) \<pi> Q R U_opt sts = Some U \<longrightarrow> af_redpair S NS \<pi> \<longrightarrow> set U \<subseteq> NS \<longrightarrow> (c \<longrightarrow> ce_compatible NS) \<longrightarrow> (\<exists> f. 
           (\<forall> s t u \<sigma> \<tau>. (s,t) \<in> sts \<longrightarrow> s \<cdot> \<sigma> \<in> NF_terms Q \<longrightarrow> NF_subst nfs (s,t) \<sigma> Q \<longrightarrow> (t \<cdot> \<sigma>, u \<cdot> \<tau>) \<in> (qrstep nfs Q (set R))^* \<longrightarrow> (m \<longrightarrow> SN_on (qrstep nfs Q (set R)) {t \<cdot> \<sigma>}) \<longrightarrow> (t \<cdot> f \<sigma>, u \<cdot> f \<tau>) \<in> NS^*))"


end

