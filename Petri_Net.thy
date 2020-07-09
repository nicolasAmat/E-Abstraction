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

definition fireable :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> bool" where
  "fireable pn m tr \<equiv> (Rep_markings m) \<ge> (Pre pn tr)"

definition fired :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> ('pl) markings" where
  "fired pn m tr \<equiv> Abs_markings ((Rep_markings m) - (Pre pn tr) + (Post pn tr))"


subsection \<open>Firing Sequence\<close>

fun firing_sequence :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> bool" where
  "firing_sequence pn m [] = True"
| "firing_sequence pn m (tr#seq) = ((fireable pn m tr) \<and> (firing_sequence pn (fired pn m tr) seq))"

fun reached_marking_sequence :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr list \<Rightarrow> ('pl) markings" where
  "reached_marking_sequence pn m [] = m"
| "reached_marking_sequence pn m (tr#seq) = reached_marking_sequence pn (fired pn m tr) seq"


subsection \<open>Reachable Markings\<close>

definition reachable_marking :: "('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings \<Rightarrow> bool" where
  "reachable_marking pn m0 m \<equiv> \<exists>seq. (firing_sequence pn m0 seq) \<and> (reached_marking_sequence pn m0 seq = m)"

definition reachable_markings :: "('pl, 'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> ('pl) markings set" where
"reachable_markings pn m0 = {m. reachable_marking pn m0 m} "

lemma init_reachable_marking:
  fixes pn::"('pl,'tr) petri_net"
    and m0::"('pl) markings"
  shows "reachable_marking pn m0 m0"
  using firing_sequence.simps(1) reachable_marking_def reached_marking_sequence.simps(1) by blast


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


end