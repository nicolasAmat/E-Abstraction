(*  Title:      E-Abstraction/Petri_Net.thy
    Author:     Nicolas Amat
*)

section \<open>Petri Net\<close>

text \<open>This section contains Petri nets formalization\<close>

theory Petri_Net
imports 
  Main
begin


subsection \<open>Petri Net\<close>

record ('pl,'tr) petri_net =
  P :: "'pl set"
  T :: "'tr set"
  Pre :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"
  Post :: "'tr \<Rightarrow> 'pl \<Rightarrow> nat"

