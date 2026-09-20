(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The fourteen unanswered questions: silence as gap, and a pitfall of universal designation\<close>

theory Avyakata
  imports Catuskoti UniversalDesignation
begin

text \<open>
  The Buddha declined to answer fourteen questions (\<open>avyakata\<close>, 十四無記;
  \<^emph>\<open>Culamalunkya-sutta\<close>, MN 63; the Chinese Agamas count fourteen, the Pali
  ten): whether the world is eternal, not eternal, both, or neither;
  finite, infinite, both, or neither; whether the Tathagata exists after
  death, does not, both, or neither; whether the soul is the same as the
  body or different. Three of the four topics are complete catuskotis all
  of whose corners are set aside.

  \<^item> Read at the formula level -- the conjunction of the negations of all
    four corners -- the rejection is classically unsatisfiable and under
    FDE/FDE5 designated exactly at the glut (\<open>rejection_formula_fde\<close>,
    \<open>rejection_formula_fde5\<close>): "none of the four" as an asserted formula
    is a contradiction, not a silence.
  \<^item> Read at the designation level -- no corner is designated -- the
    rejection is exactly corner K4 of \<open>Catuskoti\<close>: under FDE the gap
    \<open>N\<close>, under FDE5 the gap or the ineffable \<open>E\<close>
    (\<open>rejection_designation_fde5\<close>). So the unanswered question is a gap,
    and Priest's fifth value is indistinguishable from it here
    (\<open>silence_gap_or_ineffable\<close>).
  \<^item> Under \<^emph>\<open>universal\<close> designation with general plurivalence
    (\<open>UniversalDesignation\<close>) the picture inverts: an atom with no
    value is vacuously designated, and so is its negation, so the
    unanswered question lands in corner K3 -- "both" -- rather than K4
    (\<open>silence_is_assent_under_universal_designation\<close>). Under existential
    designation it stays in K4 (\<open>silence_is_gap_under_existential_designation\<close>).
    Whatever else one wants from universal designation, it cannot model
    the Buddha's silence.
\<close>

datatype avyakata_topic = WorldEternal | WorldFinite | TathagataAfterDeath | SoulBody
datatype avyakata_question = Q avyakata_topic koti

definition avyakata_questions :: "avyakata_question list" where
  "avyakata_questions =
     [Q WorldEternal K1, Q WorldEternal K2, Q WorldEternal K3, Q WorldEternal K4,
      Q WorldFinite K1, Q WorldFinite K2, Q WorldFinite K3, Q WorldFinite K4,
      Q TathagataAfterDeath K1, Q TathagataAfterDeath K2, Q TathagataAfterDeath K3, Q TathagataAfterDeath K4,
      Q SoulBody K1, Q SoulBody K2]"

lemma fourteen: "length avyakata_questions = 14 \<and> distinct avyakata_questions"
  by (simp add: avyakata_questions_def)

subsection \<open>The four corners of one question\<close>

definition corner :: "'a \<Rightarrow> koti \<Rightarrow> 'a fm" where
  "corner a k = (case k of
      K1 \<Rightarrow> Atom a
    | K2 \<Rightarrow> Neg (Atom a)
    | K3 \<Rightarrow> Conj (Atom a) (Neg (Atom a))
    | K4 \<Rightarrow> Conj (Neg (Atom a)) (Neg (Neg (Atom a))))"

definition rejection :: "'a \<Rightarrow> 'a fm" where   \<comment> \<open>formula-level: every corner negated\<close>
  "rejection a = Conj (Conj (Neg (corner a K1)) (Neg (corner a K2)))
                      (Conj (Neg (corner a K3)) (Neg (corner a K4)))"

theorem rejection_formula_cl: "\<not> cl.sat v (rejection a)"
  by (simp add: rejection_def corner_def cl.sat_def cl.eval_def)

theorem rejection_formula_fde: "fde.sat v (rejection a) \<longleftrightarrow> v a = B"
  unfolding rejection_def corner_def fde.sat_def fde.eval_def
  by (cases "v a") (simp_all add: neg4_def conj4_def mk_def)

theorem rejection_formula_fde5: "fde5.sat v (rejection a) \<longleftrightarrow> v a = Fin B"
proof (cases "v a")
  case (Fin x)
  then show ?thesis
    unfolding rejection_def corner_def fde5.sat_def fde5.eval_def
    by (cases x) (simp_all add: neg4_def conj4_def mk_def)
next
  case E
  then show ?thesis unfolding rejection_def corner_def fde5.sat_def fde5.eval_def by simp
qed

subsection \<open>Designation level: no corner designated\<close>

context mv_logic
begin

definition rejects_all :: "('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> bool" where
  "rejects_all v a \<longleftrightarrow> (\<forall>k. \<not> sat v (corner a k))"

end

theorem rejection_designation_fde: "fde.rejects_all v a \<longleftrightarrow> v a = N"
  unfolding fde.rejects_all_def fde.sat_def fde.eval_def
  by (cases "v a") (auto simp: corner_def neg4_def conj4_def mk_def split: koti.split)

theorem rejection_designation_fde5: "fde5.rejects_all v a \<longleftrightarrow> v a = Fin N \<or> v a = E"
proof (cases "v a")
  case (Fin x)
  then show ?thesis
    unfolding fde5.rejects_all_def fde5.sat_def fde5.eval_def
    by (cases x) (auto simp: corner_def neg4_def conj4_def mk_def split: koti.split)
next
  case E
  then show ?thesis unfolding fde5.rejects_all_def fde5.sat_def fde5.eval_def
    by (auto simp: corner_def split: koti.split)
qed

theorem rejection_is_K4_fde: "fde.rejects_all v a \<longleftrightarrow> fde.koti_of (v a) = K4"
proof -
  have "fde.rejects_all v a \<longleftrightarrow> v a = N" by (rule rejection_designation_fde)
  also have "\<dots> \<longleftrightarrow> fde.koti_of (v a) = K4"
    by (cases "v a") (simp_all add: fde.koti_of_def neg4_def mk_def)
  finally show ?thesis .
qed

theorem rejection_is_K4_fde5: "fde5.rejects_all w a \<longleftrightarrow> fde5.koti_of (w a) = K4"
proof -
  have "fde5.rejects_all w a \<longleftrightarrow> (w a = Fin N \<or> w a = E)" by (rule rejection_designation_fde5)
  also have "\<dots> \<longleftrightarrow> fde5.koti_of (w a) = K4"
  proof (cases "w a")
    case (Fin x) then show ?thesis by (cases x) (simp_all add: fde5.koti_of_def neg4_def mk_def)
  next
    case E then show ?thesis by (simp add: fde5.koti_of_def)
  qed
  finally show ?thesis .
qed

theorem silence_gap_or_ineffable:
  "fde5.koti_of (Fin N) = K4" "fde5.koti_of E = K4"
  by (simp_all add: fde5.koti_of_def neg4_def mk_def)

subsection \<open>Universal versus existential designation of a valueless question\<close>

theorem silence_is_assent_under_universal_designation:
  assumes "V a = {}"
  shows "cl.upsat V (Atom a)" and "cl.upsat V (Neg (Atom a))"
    and "cl.pkoti_of (V a) = K4" and "cl.upsat V (corner a K3)"
  using assms by (simp_all add: cl.upsat_def cl.pkoti_of_def corner_def)

theorem silence_is_gap_under_existential_designation:
  assumes "V a = {}"
  shows "\<not> cl.psat V (Atom a)" and "\<not> cl.psat V (Neg (Atom a))" and "cl.pkoti_of (V a) = K4"
  using assms by (simp_all add: cl.psat_def cl.pkoti_of_def)

text \<open>
  Under universal designation the valueless atom satisfies corner K3 as a
  formula (both it and its negation are "designated"), although the
  set-level classification \<open>pkoti_of\<close> still says K4 because it looks at
  existence of designated values. The two notions come apart on exactly
  the questions the Buddha left open.
\<close>

end
