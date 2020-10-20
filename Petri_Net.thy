(*  Title:      E-Abstraction/Petri_Net.thy
    Author:     Nicolas Amat
*)

section \<open>Petri Net\<close>

text \<open>This section contains Petri nets formalization\<close>

theory Petri_Net
  imports
  "HOL-Library.Function_Algebras"
begin


subsection \<open>Petri Nets\<close>

record ('pl,'tr) petri_net =
  P :: "'pl set"
  T :: "'tr set"
  Pre :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"
  Post :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"


subsection \<open>Markings\<close>

typedef ('pl) markings = "{(m::'pl \<Rightarrow> nat). True}"
  by auto


subsection \<open>Behavior\<close>

definition enabled :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> bool" where
  "enabled pn m tr \<equiv> (Rep_markings m) \<ge> (Pre pn tr)"

definition fired :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> ('pl) markings" where
  "fired pn m tr \<equiv> Abs_markings ((Rep_markings m) - (Pre pn tr) + (Post pn tr))"


subsection \<open>Firing Sequence\<close>

fun firing_sequence :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> bool" where
"firing_sequence pn m [] = True" |
"firing_sequence pn m (tr#seq) = ((enabled pn m tr) \<and> (firing_sequence pn (fired pn m tr) seq))"

fun resulting_marking_firing_sequence :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> ('pl) markings" where
"resulting_marking_firing_sequence pn m [] = m" |
"resulting_marking_firing_sequence pn m (tr#seq) = resulting_marking_firing_sequence pn (fired pn m tr) seq"


subsection \<open>Reachable Markings\<close>

definition reachable_marking :: "('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
  "reachable_marking pn m0 m \<equiv> \<exists>seq. (firing_sequence pn m0 seq) \<and> (resulting_marking_firing_sequence pn m0 seq = m)"

definition reachable_markings :: "('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings set" where
"reachable_markings pn m0 = {m. reachable_marking pn m0 m} "

lemma init_reachable_marking:
  fixes pn::"('pl,'tr) petri_net"
    and m0::"('pl) markings"
  shows "reachable_marking pn m0 m0"
  using firing_sequence.simps(1) reachable_marking_def resulting_marking_firing_sequence.simps(1) by blast


subsection \<open>Pre and Post Sets\<close>

definition transition_pre_set :: "('pl,'tr) petri_net \<Rightarrow> 'tr \<Rightarrow> 'pl set" where
"transition_pre_set pn tr \<equiv> {pl. Pre pn tr pl > 0}"

definition transition_post_set :: "('pl,'tr) petri_net \<Rightarrow> 'tr \<Rightarrow> 'pl set" where
"transition_post_set pn tr \<equiv> {pl. Post pn tr pl > 0}"

definition place_pre_set :: "('pl,'tr) petri_net \<Rightarrow> 'pl \<Rightarrow> 'tr set" where
"place_pre_set pn pl \<equiv> {tr. Post pn tr pl > 0}"

definition place_post_set :: "('pl,'tr) petri_net \<Rightarrow> 'pl \<Rightarrow> 'tr set" where
"place_post_set pn pl \<equiv> {tr. Pre pn tr pl > 0}"


subsection \<open>Labelling\<close>

typedef ('tr,'lb) labellings = "{(l::'tr \<Rightarrow> 'lb option). True}"
  by auto

fun observable_sequence :: "('tr,'lb) labellings \<Rightarrow> 'tr list \<Rightarrow> 'lb option list" where
"observable_sequence l [] = []" |
"observable_sequence l (tr#tr_seq) = (Rep_labellings l tr)#(observable_sequence l tr_seq)"

  
subsection \<open>Compatible Markings\<close>

definition compatible_markings :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
"compatible_markings N1 m1 N2 m2 \<equiv> \<forall>p \<in> (P N1) \<inter> (P N2). (Rep_markings m1 p) = (Rep_markings m2 p)"


subsection \<open>System of Equations\<close>

typedef ('pl, 'ad_var) system_equations = "{(E::'ad_var list \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings \<Rightarrow> bool). True}"
  by simp

definition solvable :: "('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list \<Rightarrow> bool" where
"solvable E ad_vars \<equiv> (\<forall>m1. \<exists>m2. (Rep_system_equations E) ad_vars m1 m2) \<and> (\<forall>m2. \<exists>m1. (Rep_system_equations E) ad_vars m1 m2)"


subsection \<open>E-Abstraction\<close>

definition initial_markings_cond :: "('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list  \<Rightarrow> ('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
"initial_markings_cond E ad_vars N1 m1 N2 m2 \<equiv> (compatible_markings N1 m1 N2 m2) \<and> (Rep_system_equations E) ad_vars m1 m2"

definition observable_sequences_cond :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> ('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list  \<Rightarrow> ('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> bool" where 
"observable_sequences_cond N1 m1 l1 E ad_vars N2 m2 l2 \<equiv> 
  \<forall>s1::('lb option list). 
    (\<exists>m1'::(('pl) markings).  \<exists>tr1::(('tr) list). (firing_sequence N1 m1 tr1) \<and> (s1 = observable_sequence l1 tr1))
    \<longrightarrow>
    (\<exists>tr2::(('tr) list). \<exists>m2'::(('pl) markings). (firing_sequence N2 m2 tr2) \<and> (s1 = observable_sequence l2 tr2))"

definition E_abstraction :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> ('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list  \<Rightarrow> ('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> bool" where
"E_abstraction N1 m1 l1 E ad_vars N2 m2 l2 \<equiv> (initial_markings_cond E ad_vars N1 m1 N2 m2) \<and> (observable_sequences_cond  N1 m1 l1 E ad_vars N2 m2 l2)"

definition E_abstraction_equivalence :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> ('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list  \<Rightarrow> ('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('tr,'lb) labellings \<Rightarrow> bool" where
"E_abstraction_equivalence N1 m1 l1 E ad_vars N2 m2 l2 \<equiv> (E_abstraction N1 m1 l1 E ad_vars N2 m2 l2) \<and>  (E_abstraction N2 m2 l2 E ad_vars N1 m1 l1)"


end