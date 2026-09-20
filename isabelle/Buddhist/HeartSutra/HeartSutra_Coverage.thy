(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Coverage theorem: every clause has a formal counterpart\<close>

theory HeartSutra_Coverage
  imports HeartSutra_Text HeartSutra_Path HeartSutra_Mantra
begin

text \<open>
  Every one of the 31 clauses of \<open>HeartSutra_Text\<close> is classified as
  \<open>Defined\<close> (a structural definition only, no theorem claimed),
  \<open>Proved\<close> (a named theorem in one of the layer theories discharges it),
  or \<open>Noted\<close> (an explicit reason this clause is not a candidate for
  formalization is recorded, e.g. \<open>HeartSutra_Mantra\<close>'s
  \<open>hs29_mantra_not_truth_apt\<close>). \<open>Missing\<close> is the status this file must
  never assign; \<open>coverage_complete\<close> below is the check.

  \<^file>\<open>../../../docs/STATUS.md\<close> mirrors this table with, for each \<open>Proved\<close> clause,
  the theorem name that discharges it (checked live by the
  \<^verbatim>\<open>@{thm [source] ...}\<close> antiquotations below: a stale or misspelled
  theorem name here fails the session build, not just a documentation
  check).
\<close>

datatype status = Defined | Proved | Noted | Missing

fun status_of :: "clause \<Rightarrow> status" where
  "status_of HS00 = Defined"                       \<comment> \<open>title\<close>
| "status_of HS01 = Proved"                         \<comment> \<open>\<open>hs01_04_avalokitesvara\<close>\<close>
| "status_of HS02 = Proved"                         \<comment> \<open>\<open>hs21_22_chain (via hs02)\<close>\<close>
| "status_of HS03 = Proved"                         \<comment> \<open>\<open>hs03_skandhas\<close>\<close>
| "status_of HS04 = Proved"                         \<comment> \<open>\<open>hs01_04_avalokitesvara\<close>\<close>
| "status_of HS05 = Defined"                        \<comment> \<open>speaker Sariputra\<close>
| "status_of HS06 = Proved"                         \<comment> \<open>\<open>fde_R_identity_not_notsep / cl_readings_coincide\<close>\<close>
| "status_of HS07 = Proved"                         \<comment> \<open>\<open>hs07_R_mutual\<close>\<close>
| "status_of HS08 = Proved"                         \<comment> \<open>\<open>hs08_generalize\<close>\<close>
| "status_of HS09 = Proved"                         \<comment> \<open>\<open>hs11_18_enumeration\<close> (dharmas of HS09's 諸法)\<close>
| "status_of HS10 = Proved"                         \<comment> \<open>\<open>hs10_fde_formula_iff_B / hs10_fde_neither_iff_N\<close>\<close>
| "status_of HS11 = Proved"                         \<comment> \<open>\<open>hs11_18_enumeration\<close>\<close>
| "status_of HS12 = Proved"                         \<comment> \<open>\<open>hs11_18_enumeration (ayatana part)\<close>\<close>
| "status_of HS13 = Proved"                         \<comment> \<open>\<open>hs11_18_enumeration (ayatana part)\<close>\<close>
| "status_of HS14 = Proved"                         \<comment> \<open>\<open>dhatu_naishi + hs11_18_enumeration\<close>\<close>
| "status_of HS15 = Proved"                         \<comment> \<open>\<open>hs15_16_chain_and_cessation\<close>\<close>
| "status_of HS16 = Proved"                         \<comment> \<open>\<open>pratiloma_naishi + hs15_16_chain_and_cessation\<close>\<close>
| "status_of HS17 = Proved"                         \<comment> \<open>\<open>hs11_18_enumeration (satya part)\<close>\<close>
| "status_of HS18 = Proved"                         \<comment> \<open>\<open>hs19_no_attainment (Jnana)\<close>\<close>
| "status_of HS19 = Proved"                         \<comment> \<open>\<open>hs19_no_attainment\<close>\<close>
| "status_of HS20 = Proved"                         \<comment> \<open>\<open>hs21_22_chain\<close>\<close>
| "status_of HS21 = Proved"                         \<comment> \<open>\<open>hs21_22_chain\<close>\<close>
| "status_of HS22 = Proved"                         \<comment> \<open>\<open>hs21_22_chain\<close>\<close>
| "status_of HS23 = Proved"                         \<comment> \<open>\<open>hs23_24_three_times\<close>\<close>
| "status_of HS24 = Proved"                         \<comment> \<open>\<open>hs23_24_three_times\<close>\<close>
| "status_of HS25 = Defined"                        \<comment> \<open>\<open>epithets_four\<close>\<close>
| "status_of HS26 = Proved"                         \<comment> \<open>\<open>hs04_26 (via hs21_22_chain)\<close>\<close>
| "status_of HS27 = Noted"                          \<comment> \<open>\<open>hs29_mantra_not_truth_apt\<close>\<close>
| "status_of HS28 = Noted"                          \<comment> \<open>\<open>hs29_mantra_not_truth_apt\<close>\<close>
| "status_of HS29 = Noted"                          \<comment> \<open>\<open>hs29_mantra_not_truth_apt, heart_mantra_shape\<close>\<close>
| "status_of HS30 = Defined"                        \<comment> \<open>colophon\<close>

fun logic_dependent :: "clause \<Rightarrow> bool" where
  "logic_dependent HS06 = True" | "logic_dependent HS07 = True"
| "logic_dependent HS09 = True" | "logic_dependent HS10 = True"
| "logic_dependent _ = False"

lemma coverage_complete: "\<forall>c. status_of c \<noteq> Missing"
proof
  fix c show "status_of c \<noteq> Missing" by (cases c) simp_all
qed

lemma coverage_counts_proved: "length (filter (\<lambda>c. status_of c = Proved) clauses) = 24"
  by eval

lemma coverage_counts_defined: "length (filter (\<lambda>c. status_of c = Defined) clauses) = 4"
  by eval

lemma coverage_counts_noted: "length (filter (\<lambda>c. status_of c = Noted) clauses) = 3"
  by eval

lemmas coverage_counts = coverage_counts_proved coverage_counts_defined coverage_counts_noted

lemma logic_dependent_set: "{c. logic_dependent c} = {HS06, HS07, HS09, HS10}"
proof (rule set_eqI)
  fix c show "c \<in> {c. logic_dependent c} \<longleftrightarrow> c \<in> {HS06, HS07, HS09, HS10}"
    by (cases c) simp_all
qed

text \<open>
  Live cross-references from clause to discharging theorem. If a theorem
  name below is misspelled or removed, this theory (hence the whole
  session) fails to build.

  HS01/04 $\rightarrow$ @{thm [source] HeartSutra_Path.bodhisattva_path.hs01_04_avalokitesvara}
  HS02/20-22 $\rightarrow$ @{thm [source] HeartSutra_Path.bodhisattva_path.hs21_22_chain}
  HS03 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.emptiness.hs03_skandhas}
  HS06 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.fde_R_identity_not_notsep}
  HS07/08 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.emptiness.hs08_generalize}
  HS09/11-17 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.emptiness.hs11_18_enumeration}
  HS10 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.hs10_fde_formula_iff_B}
  HS14 $\rightarrow$ @{thm [source] HeartSutra_Dharma.dhatu_naishi}
  HS15/16 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.emptiness.hs15_16_chain_and_cessation}
  HS16 $\rightarrow$ @{thm [source] HeartSutra_Dharma.pratiloma_naishi}
  HS18/19 $\rightarrow$ @{thm [source] HeartSutra_Emptiness.emptiness.hs19_no_attainment}
  HS23/24 $\rightarrow$ @{thm [source] HeartSutra_Path.bodhisattva_path.hs23_24_three_times}
  HS26 $\rightarrow$ @{thm [source] HeartSutra_Path.bodhisattva_path.hs04_26}
  HS27-29 $\rightarrow$ @{thm [source] HeartSutra_Mantra.hs29_mantra_not_truth_apt}
\<close>

end
