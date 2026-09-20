(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>MMK 1:1, the four-fold non-arising, as a prasanga\<close>

theory Madhyamaka_MMK1
  imports FiniteLogics
begin

text \<open>
  諸法不自生 亦不從他生 不共不無因 是故知無生 (MMK 1:1, Kumarajiva): nothing
  arises from itself, from another, from both, or without cause; therefore
  nothing arises. The argument has two parts: four refutations, each a
  reductio (modus tollens: "if it arose from itself, [absurdity]"), and a
  final step from the exhaustive four-fold disjunction to non-arising.

  \<^item> Classically the final step is valid (\<open>catuh_utpada_cl\<close>).
  \<^item> Under FDE the final step is valid at the formula level -- from the
    four negations the negation of "arises" is designated
    (\<open>anutpada_fde_formula\<close>) -- but the designation-level conclusion "it
    is not the case that arising is designated" fails: a glut on every
    corner makes all four negations designated and "arises" designated
    too (\<open>anutpada_fde_designation_fails\<close>). This is the glut/gap split of
    HS10 again.
  \<^item> The refutations themselves lean on modus tollens, which fails in FDE
    exactly as modus ponens does (\<open>fde_mt_fails\<close>, witness \<open>A = T\<close>,
    \<open>B = B\<close>). So a paraconsistent reading of the four-fold negation has to
    recapture classical reasoning for each reductio -- Cotnoir's point,
    now for MMK 1:1 rather than for the catuskoti.
\<close>

datatype origin = Self | Other | Both | Neither
datatype utpada_atom = From origin

definition arises :: "utpada_atom fm" where
  "arises = Disj (Disj (Atom (From Self)) (Atom (From Other)))
                 (Disj (Atom (From Both)) (Atom (From Neither)))"

definition refutations :: "utpada_atom fm set" where
  "refutations = (\<lambda>og. Neg (Atom (From og))) ` UNIV"

lemma refutations_iff: "(\<forall>Y \<in> refutations. P Y) \<longleftrightarrow> (\<forall>og. P (Neg (Atom (From og))))"
  by (auto simp: refutations_def)

theorem catuh_utpada_cl: "cl.entails refutations (Neg arises)"
  unfolding cl.entails_def cl.sat_def cl.eval_def refutations_iff arises_def by simp

lemma neg4_TB_iff: "neg4 x \<in> {T, B} \<longleftrightarrow> x = B \<or> x = F"
  by (cases x) (simp_all add: neg4_def mk_def)

lemma disj4_BF: "x = B \<or> x = F \<Longrightarrow> y = B \<or> y = F \<Longrightarrow> disj4 x y = B \<or> disj4 x y = F"
  by (auto simp: disj4_def mk_def)

theorem anutpada_fde_formula: "fde.entails refutations (Neg arises)"
proof -
  { fix v :: "utpada_atom \<Rightarrow> tv4"
    assume A: "\<forall>Y \<in> refutations. fde.sat v Y"
    have c: "\<And>og. v (From og) = B \<or> v (From og) = F"
    proof -
      fix og
      have "neg4 (v (From og)) \<in> {T, B}"
        using A[unfolded refutations_iff fde.sat_def fde.eval_def, rule_format, of og] by simp
      then show "v (From og) = B \<or> v (From og) = F"
        by (cases "v (From og)") (simp_all add: neg4_def mk_def)
    qed
    have "mv_eval neg4 conj4 disj4 v arises = B \<or> mv_eval neg4 conj4 disj4 v arises = F"
      unfolding arises_def by (simp only: mv_eval.simps) (intro disj4_BF c)
    then have "fde.sat v (Neg arises)"
      unfolding fde.sat_def fde.eval_def by (auto simp: neg4_def mk_def)
  }
  then show ?thesis unfolding fde.entails_def by blast
qed

theorem anutpada_fde_designation_fails:
  "\<exists>v. (\<forall>Y \<in> refutations. fde.sat v Y) \<and> fde.sat v arises"
  by (rule exI[of _ "\<lambda>_. B"])
     (simp add: fde.sat_def fde.eval_def refutations_iff arises_def neg4_def disj4_def mk_def)

subsection \<open>Modus tollens\<close>

lemma cl_mt: "cl.entails {cl.imp (Atom p) (Atom q), Neg (Atom q)} (Neg (Atom p))"
  unfolding cl.entails_def cl.sat_def cl.eval_def cl.imp_def by auto

definition v_mt :: "atom \<Rightarrow> tv4" where "v_mt a = (if a = p then T else if a = q then B else F)"

theorem fde_mt_fails: "\<not> fde.entails {fde.imp (Atom p) (Atom q), Neg (Atom q)} (Neg (Atom p))"
  unfolding fde.entails_def fde.sat_def fde.eval_def fde.imp_def
  by (rule notI, drule spec[of _ v_mt]) (simp add: v_mt_def neg4_def disj4_def mk_def)

end
