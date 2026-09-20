(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>A generic many-valued propositional logic\<close>

theory ManyValuedLogic
  imports Main
begin

text \<open>
  A single formula datatype and a single, executable evaluator, parametric
  in the carrier's negation and connective operations. \<^theory_text>\<open>FiniteLogics\<close>
  instantiates this three ways (classical, Belnap-Dunn FDE, Priest's
  FDE-plus-fifth-value) over the *same* formulas, so that a sutra clause can
  be read once and evaluated under each logic.

  The evaluator \<open>mv_eval\<close> is deliberately defined \<^emph>\<open>outside\<close>
  the \<open>mv_logic\<close> locale below: a \<^theory_text>\<open>fun\<close> declared inside a
  locale is not executable (no code equations) until it is discharged by a
  \<^theory_text>\<open>global_interpretation ... defines\<close>, which would have to be
  repeated for every instance. Keeping \<open>mv_eval\<close> as a plain
  function of its operations makes \<^theory_text>\<open>value\<close> and Nitpick work
  uniformly on every instance without extra plumbing.
\<close>

datatype 'a fm =
    Atom 'a
  | Neg "'a fm"
  | Conj "'a fm" "'a fm"
  | Disj "'a fm" "'a fm"

fun mv_eval ::
  "('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'v) \<Rightarrow> 'a fm \<Rightarrow> 'v"
where
  "mv_eval neg mconj mdisj v (Atom a) = v a"
| "mv_eval neg mconj mdisj v (Neg A) = neg (mv_eval neg mconj mdisj v A)"
| "mv_eval neg mconj mdisj v (Conj A B) = mconj (mv_eval neg mconj mdisj v A) (mv_eval neg mconj mdisj v B)"
| "mv_eval neg mconj mdisj v (Disj A B) = mdisj (mv_eval neg mconj mdisj v A) (mv_eval neg mconj mdisj v B)"

locale mv_logic =
  fixes D    :: "'v set"
    and neg  :: "'v \<Rightarrow> 'v"
    and mconj :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
    and mdisj :: "'v \<Rightarrow> 'v \<Rightarrow> 'v"
  assumes D_nonempty: "D \<noteq> {}"
      and D_proper:   "D \<noteq> UNIV"
begin

definition eval :: "('a \<Rightarrow> 'v) \<Rightarrow> 'a fm \<Rightarrow> 'v" where
  "eval v A = mv_eval neg mconj mdisj v A"

definition sat :: "('a \<Rightarrow> 'v) \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "sat v A \<longleftrightarrow> eval v A \<in> D"

definition entails :: "'a fm set \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "entails \<Gamma> A \<longleftrightarrow> (\<forall>v. (\<forall>B \<in> \<Gamma>. sat v B) \<longrightarrow> sat v A)"

definition imp :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "imp A B = Disj (Neg A) B"

definition iff_fm :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a fm" where
  "iff_fm A B = Conj (imp A B) (imp B A)"

lemma eval_iff_fm: "eval v (iff_fm A B) = mconj (eval v (imp A B)) (eval v (imp B A))"
  by (simp add: iff_fm_def eval_def)

definition valid :: "'a fm \<Rightarrow> bool" where
  "valid A \<longleftrightarrow> entails {} A"

lemma entails_refl: "A \<in> \<Gamma> \<Longrightarrow> entails \<Gamma> A"
  unfolding entails_def by blast

lemma entails_mono: "\<Gamma> \<subseteq> \<Delta> \<Longrightarrow> entails \<Gamma> A \<Longrightarrow> entails \<Delta> A"
  unfolding entails_def by blast

lemma entails_cut:
  assumes "entails \<Gamma> A" and "entails (insert A \<Gamma>) B"
  shows "entails \<Gamma> B"
  using assms unfolding entails_def by blast

lemma valid_iff_all_sat: "valid A \<longleftrightarrow> (\<forall>v. sat v A)"
  unfolding valid_def entails_def by simp

end

end
