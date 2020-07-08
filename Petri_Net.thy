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
  "fireable pn m t \<equiv> (Rep_markings m) \<ge> (Pre pn t)"

definition fired :: "('pl,'tr) petri_net \<Rightarrow> ('pl) markings \<Rightarrow> 'tr \<Rightarrow> ('pl) markings" where
  "fired pn m t \<equiv> Abs_markings ((Rep_markings m) + (Pre pn t))"


end