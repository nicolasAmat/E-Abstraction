(*  Title:      E-Abstraction/Petri_Net.thy
    Author:     Nicolas Amat
*)

section \<open>Petri Net Formalization\<close>

text \<open>This section contains Petri nets formalization\<close>

theory Petri_Net
  imports
  "HOL-Library.Function_Algebras"
begin


subsection \<open>Markings\<close>

typedef ('pl) markings = "{(m::'pl \<Rightarrow> nat). True}"
  by simp

subsection \<open>Labelling Functions\<close>

typedef ('tr,'lb) labellings = "{(l::'tr \<Rightarrow> 'lb option). True}"
  by simp

subsection \<open>Petri Nets\<close>

record ('pl,'tr,'lb) petri_net =
  P :: "'pl set"
  T :: "'tr set"
  Pre :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"
  Post :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"  
  m0 :: "('pl) markings"
  l :: "('tr,'lb) labellings"

subsection \<open>Behavior\<close>

definition transition_enabled :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> bool" where
  "transition_enabled pn m tr \<equiv> (Rep_markings m) \<ge> (Pre pn tr)"

definition resulting_marking_firing_transition :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> ('pl) markings" where
  "resulting_marking_firing_transition pn m tr \<equiv> Abs_markings ((Rep_markings m) - (Pre pn tr) + (Post pn tr))"

subsection \<open>Firing Sequence\<close>

fun firing_sequence :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> bool" where
"firing_sequence pn m [] = True" |
"firing_sequence pn m (tr#seq) = ((transition_enabled pn m tr) \<and> (firing_sequence pn (resulting_marking_firing_transition pn m tr) seq))"

fun resulting_marking_firing_sequence :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> ('pl) markings" where
"resulting_marking_firing_sequence pn m [] = m" |
"resulting_marking_firing_sequence pn m (tr#seq) = resulting_marking_firing_sequence pn (resulting_marking_firing_transition pn m tr) seq"

subsection \<open>Reachable Markings\<close>

definition reachable_marking :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
  "reachable_marking pn m \<equiv> \<exists>seq. (firing_sequence pn (m0 pn) seq) \<and> (resulting_marking_firing_sequence pn (m0 pn) seq = m)"

definition set_reachable_markings :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings set" where
"set_reachable_markings pn = {m. reachable_marking pn m}"

lemma init_reachable_marking:
  fixes pn::"('pl,'tr,'lb) petri_net"
  shows "reachable_marking pn (m0 pn)"
  using firing_sequence.simps(1) reachable_marking_def resulting_marking_firing_sequence.simps(1) by blast

subsection \<open>Pre and Post Sets\<close>

definition transition_pre_set :: "('pl,'tr,'lb) petri_net \<Rightarrow> 'tr \<Rightarrow> 'pl set" where
"transition_pre_set pn tr \<equiv> {pl. Pre pn tr pl > 0}"

definition transition_post_set :: "('pl,'tr,'lb) petri_net \<Rightarrow> 'tr \<Rightarrow> 'pl set" where
"transition_post_set pn tr \<equiv> {pl. Post pn tr pl > 0}"

definition place_pre_set :: "('pl,'tr,'lb) petri_net \<Rightarrow> 'pl \<Rightarrow> 'tr set" where
"place_pre_set pn pl \<equiv> {tr. Post pn tr pl > 0}"

definition place_post_set :: "('pl,'tr,'lb) petri_net \<Rightarrow> 'pl \<Rightarrow> 'tr set" where
"place_post_set pn pl \<equiv> {tr. Pre pn tr pl > 0}"

subsection \<open>Observable Sequence\<close>

fun observable_sequence :: "('pl,'tr,'lb) petri_net \<Rightarrow> 'tr list \<Rightarrow> 'lb option list" where
"observable_sequence pn [] = []" |
"observable_sequence pn (tr#seq) = ((Rep_labellings (l pn)) tr)#(observable_sequence pn seq)"

fun similar_observable_sequences :: "'lb option list \<Rightarrow> 'lb option list \<Rightarrow> bool" where
"similar_observable_sequences [] [] = True" |
"similar_observable_sequences (Some l1#seq1) (Some l2#seq2) = ((l1 = l2) \<and> (similar_observable_sequences seq1 seq2))" |
"similar_observable_sequences (Some l1#seq1) [] = False" |
"similar_observable_sequences [] (Some l2#seq2) = False" |
"similar_observable_sequences (None#seq1) seq2 = similar_observable_sequences seq1 seq2" |
"similar_observable_sequences seq1 (None#seq2) = similar_observable_sequences seq1 seq2"

subsection \<open>Compatible Markings\<close>

definition compatible_markings :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl,'tr,'lb) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
"compatible_markings N1 m1 N2 m2 \<equiv> \<forall>p \<in> (P N1) \<inter> (P N2). (Rep_markings m1 p) = (Rep_markings m2 p)"

subsection \<open>System of Equations\<close>

typedef ('pl,'add_var) system_equations = "{(E::'add_var list \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings \<Rightarrow> bool). True}"
  by simp

definition solvable :: "('pl,'add_var) system_equations \<Rightarrow> 'add_var list \<Rightarrow> bool" where
"solvable E add_vars \<equiv> (\<forall>m1. \<exists>m2. (Rep_system_equations E) add_vars m1 m2) 
                     \<and> (\<forall>m2. \<exists>m1. (Rep_system_equations E) add_vars m1 m2)"

subsection \<open>E-Abstraction\<close>

definition initial_markings_cond :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl,'add_var) system_equations \<Rightarrow> 'add_var list \<Rightarrow> ('pl,'tr,'lb) petri_net \<Rightarrow> bool" where
"initial_markings_cond N1 E add_vars N2 \<equiv> (compatible_markings N1 (m0 N1) N2 (m0 N2)) \<and> ((Rep_system_equations E) add_vars (m0 N1) (m0 N2))"

definition observable_sequences_cond :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl, 'add_var) system_equations \<Rightarrow> 'add_var list  \<Rightarrow> ('pl,'tr,'lb) petri_net \<Rightarrow> bool" where 
"observable_sequences_cond N1 E add_vars N2 \<equiv> 
  \<forall>s1::('lb option list). \<forall>m1::(('pl) markings). \<forall>tr1::(('tr) list).
    ((firing_sequence N1 (m0 N1) tr1) \<and> (m1 = (resulting_marking_firing_sequence N1 (m0 N1) tr1)))
      \<longrightarrow> (\<forall>m2::(('pl) markings). ((compatible_markings N1 m1 N2 m2) \<and> ((Rep_system_equations E) add_vars m1 m2))
        \<longrightarrow> (\<exists>tr2. (firing_sequence N2 (m0 N2) tr2) \<and> (similar_observable_sequences s1 (observable_sequence N2 tr2))))"

definition E_abstraction :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl, 'add_var) system_equations \<Rightarrow> 'add_var list  \<Rightarrow> ('pl,'tr,'lb) petri_net \<Rightarrow> bool" where
"E_abstraction N1 E add_vars N2 \<equiv> (initial_markings_cond N1 E add_vars N2) \<and> (observable_sequences_cond  N1 E add_vars N2)"

definition E_abstraction_equivalence :: "('pl,'tr,'lb) petri_net \<Rightarrow> ('pl, 'ad_var) system_equations \<Rightarrow> 'ad_var list  \<Rightarrow> ('pl,'tr,'lb) petri_net \<Rightarrow> bool" where
"E_abstraction_equivalence N1 E ad_vars N2 \<equiv> (E_abstraction N1 E ad_vars N2) \<and>  (E_abstraction N2 E ad_vars N1)"


end