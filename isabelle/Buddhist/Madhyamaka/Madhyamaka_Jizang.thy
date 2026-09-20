(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Jizang's fourfold two truths: a hierarchy that truth-functional semantics cannot climb\<close>

theory Madhyamaka_Jizang
  imports FiniteLogics
begin

text \<open>
  Jizang (吉藏, 549-623), \<^emph>\<open>Dasheng xuanlun\<close> (大乘玄論), lays out the two
  truths in four tiers (四重二諦):

  \<^enum> existence (有) is conventional, emptiness (空) is ultimate;
  \<^enum> both existence and emptiness are conventional, "neither existence nor
    emptiness" (非有非空) is ultimate;
  \<^enum> the duality "existence / emptiness" and the non-duality "neither" are
    both conventional; "neither duality nor non-duality" (非二非不二) is
    ultimate;
  \<^enum> all three preceding tiers are conventional; the ultimate is beyond
    words and thought (言忘慮絶).

  The rule that generates the ladder is uniform: the next conventional
  truth is the \<^emph>\<open>pair\<close> of the previous two truths, taken as positions, and
  the next ultimate truth is the denial of that pair. Taking "pair of
  positions" as disjunction and "denial" as negation gives the recursion
  \<open>conv (n+1) = conv n \<or> ult n\<close>, \<open>ult n = \<not> conv n\<close>, hence
  \<open>conv (n+1) = conv n \<or> \<not> conv n\<close>: each tier is an instance of excluded
  middle applied to the previous tier, and each ultimate its negation.

  Result. Under every truth-functional semantics of this session the ladder
  stabilises at the second tier: classically \<open>conv n\<close> is a tautology and
  \<open>ult n\<close> unsatisfiable for all \<open>n \<ge> 1\<close>; under FDE and FDE5 the value of
  \<open>(conv n, ult n)\<close> is the same for all \<open>n \<ge> 1\<close> -- \<open>(T, F)\<close> for a bivalent
  input, \<open>(B, B)\<close> for a glut, \<open>(N, N)\<close> for a gap, \<open>(E, E)\<close> for the
  ineffable. The designation-level reading of "neither" (as in HS10) does
  not help: it too is constant from the second tier on. The four ultimates
  are four distinct formulas with, on any such semantics, one value. So
  Jizang's ascent is not an ascent in truth value; whatever separates the
  tiers must be non-truth-functional (an assertion or attachment operator
  on the speaker's side, which is how Jizang himself describes the
  tiers -- as successive antidotes to attachment). This theory establishes
  the negative result; it does not propose the pragmatic semantics.
\<close>

fun jz_conv :: "'a fm \<Rightarrow> nat \<Rightarrow> 'a fm" where
  "jz_conv A 0 = A"
| "jz_conv A (Suc n) = Disj (jz_conv A n) (Neg (jz_conv A n))"

definition jz_ult :: "'a fm \<Rightarrow> nat \<Rightarrow> 'a fm" where
  "jz_ult A n = Neg (jz_conv A n)"

text \<open>Tier \<open>k\<close> (1-based) is the pair \<open>(jz_conv A (k-1), jz_ult A (k-1))\<close>.\<close>

lemma jz_conv_Suc_as_pair: "jz_conv A (Suc n) = Disj (jz_conv A n) (jz_ult A n)"
  by (simp add: jz_ult_def)

subsection \<open>Syntactically, the tiers are distinct\<close>

lemma jz_conv_size: "size (jz_conv A (Suc n)) > size (jz_conv A n)"
  by simp

lemma jz_conv_size_mono: "n < m \<Longrightarrow> size (jz_conv A n) < size (jz_conv A m)"
  by (induction m) (auto simp: less_Suc_eq)

theorem jz_tiers_distinct: "n \<noteq> m \<Longrightarrow> jz_ult A n \<noteq> jz_ult A m"
  unfolding jz_ult_def using jz_conv_size_mono[of n m A] jz_conv_size_mono[of m n A]
  by (cases "n < m") auto

subsection \<open>Evaluation shorthands\<close>

abbreviation ev2 :: "('a \<Rightarrow> bool) \<Rightarrow> 'a fm \<Rightarrow> bool" where "ev2 \<equiv> mv_eval Not (\<and>) (\<or>)"
abbreviation ev4 :: "('a \<Rightarrow> tv4) \<Rightarrow> 'a fm \<Rightarrow> tv4" where "ev4 \<equiv> mv_eval neg4 conj4 disj4"
abbreviation ev5 :: "('a \<Rightarrow> tv5) \<Rightarrow> 'a fm \<Rightarrow> tv5" where "ev5 \<equiv> mv_eval neg5 conj5 disj5"

lemma cl_sat_ev2: "cl.sat v X \<longleftrightarrow> ev2 v X" by (simp add: cl.sat_def cl.eval_def)
lemma fde_sat_ev4: "fde.sat v X \<longleftrightarrow> ev4 v X \<in> {T, B}" by (simp add: fde.sat_def fde.eval_def)
lemma fde5_sat_ev5: "fde5.sat v X \<longleftrightarrow> ev5 v X \<in> {Fin T, Fin B}" by (simp add: fde5.sat_def fde5.eval_def)

subsection \<open>Classically the ladder collapses at tier 2\<close>

theorem jz_cl_conv_valid: "cl.valid (jz_conv A (Suc n))"
  by (simp add: cl.valid_def cl.entails_def cl_sat_ev2)

theorem jz_cl_ult_unsat: "\<not> cl.sat v (jz_ult A (Suc n))"
  by (simp add: jz_ult_def cl_sat_ev2)

subsection \<open>Under FDE and FDE5 the ladder stabilises at tier 2\<close>

definition lem4 :: "tv4 \<Rightarrow> tv4" where "lem4 x = disj4 x (neg4 x)"
definition lem5 :: "tv5 \<Rightarrow> tv5" where "lem5 x = disj5 x (neg5 x)"

lemma lem4_values: "lem4 T = T" "lem4 F = T" "lem4 B = B" "lem4 N = N"
  by (simp_all add: lem4_def disj4_def neg4_def mk_def)

lemma lem4_idem: "lem4 (lem4 x) = lem4 x"
  by (cases x) (simp_all add: lem4_values)

lemma lem5_Fin: "lem5 (Fin x) = Fin (lem4 x)" and lem5_E: "lem5 E = E"
  by (simp_all add: lem5_def lem4_def)

lemma lem5_idem: "lem5 (lem5 x) = lem5 x"
  by (cases x) (simp_all add: lem5_Fin lem5_E lem4_idem)

lemma ev4_conv_Suc: "ev4 v (jz_conv A (Suc n)) = lem4 (ev4 v (jz_conv A n))"
  by (simp add: lem4_def)

lemma ev5_conv_Suc: "ev5 v (jz_conv A (Suc n)) = lem5 (ev5 v (jz_conv A n))"
  by (simp add: lem5_def)

theorem jz_fde_stabilizes: "ev4 v (jz_conv A (Suc n)) = lem4 (ev4 v A)"
  by (induction n) (simp_all only: ev4_conv_Suc lem4_idem jz_conv.simps(1))

theorem jz_fde5_stabilizes: "ev5 v (jz_conv A (Suc n)) = lem5 (ev5 v A)"
  by (induction n) (simp_all only: ev5_conv_Suc lem5_idem jz_conv.simps(1))

theorem jz_fde_ult_stabilizes: "ev4 v (jz_ult A (Suc n)) = neg4 (lem4 (ev4 v A))"
  by (simp only: jz_ult_def mv_eval.simps jz_fde_stabilizes)

theorem jz_fde5_ult_stabilizes: "ev5 v (jz_ult A (Suc n)) = neg5 (lem5 (ev5 v A))"
  by (simp only: jz_ult_def mv_eval.simps jz_fde5_stabilizes)

text \<open>The three fixed points (four with the ineffable), for an atomic \<open>A\<close>.\<close>

theorem jz_fde_fixed_points:
  "v a \<in> {T, F} \<Longrightarrow> ev4 v (jz_conv (Atom a) (Suc n)) = T \<and> ev4 v (jz_ult (Atom a) (Suc n)) = F"
  "v a = B \<Longrightarrow> ev4 v (jz_conv (Atom a) (Suc n)) = B \<and> ev4 v (jz_ult (Atom a) (Suc n)) = B"
  "v a = N \<Longrightarrow> ev4 v (jz_conv (Atom a) (Suc n)) = N \<and> ev4 v (jz_ult (Atom a) (Suc n)) = N"
  unfolding jz_fde_stabilizes jz_fde_ult_stabilizes mv_eval.simps(1)
  by (auto simp: lem4_values neg4_def mk_def)

theorem jz_fde5_ineffable_fixed_point:
  "v a = E \<Longrightarrow> ev5 v (jz_conv (Atom a) (Suc n)) = E \<and> ev5 v (jz_ult (Atom a) (Suc n)) = E"
  unfolding jz_fde5_stabilizes jz_fde5_ult_stabilizes mv_eval.simps(1)
  by (simp add: lem5_E)

subsection \<open>Tiers 2, 3, 4 are indistinguishable, at either level of reading\<close>

theorem jz_tiers_same_designation_fde:
  "fde.sat v (jz_ult A (Suc n)) \<longleftrightarrow> fde.sat v (jz_ult A (Suc m))"
  by (simp add: fde_sat_ev4 jz_fde_ult_stabilizes)

theorem jz_tiers_same_designation_fde5:
  "fde5.sat v (jz_ult A (Suc n)) \<longleftrightarrow> fde5.sat v (jz_ult A (Suc m))"
  by (simp add: fde5_sat_ev5 jz_fde5_ult_stabilizes)

text \<open>
  Designation-level "neither" (neither the conventional nor the ultimate
  formula of a tier is designated), the reading that made HS10 come out as
  a gap: constant from tier 2 on, and equivalent to \<open>A\<close> being a gap.
\<close>

definition jz_neither :: "('a \<Rightarrow> tv4) \<Rightarrow> 'a fm \<Rightarrow> nat \<Rightarrow> bool" where
  "jz_neither v A n \<longleftrightarrow> \<not> fde.sat v (jz_conv A n) \<and> \<not> fde.sat v (jz_ult A n)"

theorem jz_neither_stabilizes: "jz_neither v A (Suc n) \<longleftrightarrow> ev4 v A = N"
  unfolding jz_neither_def fde_sat_ev4 jz_fde_ult_stabilizes jz_fde_stabilizes
  by (cases "ev4 v A") (simp_all add: lem4_values neg4_def mk_def)

text \<open>
  Summary theorem: on every semantics of this session, all ultimates from
  the second tier up have one and the same value, although they are
  pairwise distinct formulas.
\<close>

theorem jizang_ladder_is_not_truth_functional:
  "n \<noteq> m \<Longrightarrow> jz_ult A (Suc n) \<noteq> jz_ult A (Suc m)"
  "ev4 v (jz_ult A (Suc n)) = ev4 v (jz_ult A (Suc m))"
  "ev5 w (jz_ult A (Suc n)) = ev5 w (jz_ult A (Suc m))"
  "ev2 u (jz_ult A (Suc n)) = ev2 u (jz_ult A (Suc m))"
proof -
  show "n \<noteq> m \<Longrightarrow> jz_ult A (Suc n) \<noteq> jz_ult A (Suc m)" by (rule jz_tiers_distinct) simp
  show "ev4 v (jz_ult A (Suc n)) = ev4 v (jz_ult A (Suc m))" by (simp only: jz_fde_ult_stabilizes)
  show "ev5 w (jz_ult A (Suc n)) = ev5 w (jz_ult A (Suc m))" by (simp only: jz_fde5_ult_stabilizes)
  show "ev2 u (jz_ult A (Suc n)) = ev2 u (jz_ult A (Suc m))" by (simp add: jz_ult_def)
qed

end
