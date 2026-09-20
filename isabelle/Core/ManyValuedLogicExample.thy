(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>A worked example: adding a logic to the framework in forty lines\<close>

theory ManyValuedLogicExample
  imports Catuskoti
begin

text \<open>
  Nothing in this theory is about the Heart Sutra. It exists to answer the
  question a reader of \<^file>\<open>../../docs/REUSE.md\<close> will ask next: what does it
  actually take to put \<^emph>\<open>my\<close> logic into this framework and get its
  properties out?

  The answer is a datatype, three operations, a designated set, and one
  \<^theory_text>\<open>global_interpretation\<close>. Everything the locale
  proves -- satisfaction, consequence, validity, the material conditional,
  the four corners of \<^theory>\<open>Buddhist_Comparative_Logic.Catuskoti\<close> -- is then
  available under the new prefix, and the new logic can be compared with
  the three already there against the same formulas.

  The example is strong Kleene \<open>K3\<close>: three values, a gap but no glut. It is
  the natural companion to FDE, and putting the two side by side shows the
  single fact that separates them.
\<close>

datatype k3 = Kt | Ku | Kf

fun negk :: "k3 \<Rightarrow> k3" where
  "negk Kt = Kf" | "negk Ku = Ku" | "negk Kf = Kt"

fun conjk :: "k3 \<Rightarrow> k3 \<Rightarrow> k3" where
  "conjk Kf _ = Kf" | "conjk _ Kf = Kf"
| "conjk Ku _ = Ku" | "conjk _ Ku = Ku"
| "conjk Kt Kt = Kt"

fun disjk :: "k3 \<Rightarrow> k3 \<Rightarrow> k3" where
  "disjk Kt _ = Kt" | "disjk _ Kt = Kt"
| "disjk Ku _ = Ku" | "disjk _ Ku = Ku"
| "disjk Kf Kf = Kf"

text \<open>
  The two proof obligations are that the designated set is neither empty
  nor everything. That is all the locale assumes.
\<close>

global_interpretation k3: mv_logic "{Kt}" negk conjk disjk
  defines k3_eval = k3.eval
proof
  show "{Kt} \<noteq> {}" by simp
  show "{Kt} \<noteq> UNIV" using k3.exhaust by blast
qed

text \<open>
  From here the vocabulary is inherited. Two facts, proved the same way the
  corresponding facts about FDE are proved in
  \<^theory>\<open>Buddhist_Comparative_Logic.FiniteLogics\<close>.
\<close>

definition gap_p :: "atom \<Rightarrow> k3" where
  "gap_p a = (if a = p then Ku else Kf)"

theorem k3_lem_fails: "\<not> k3.valid (Disj (Atom p) (Neg (Atom p)))"
proof -
  have "k3.eval gap_p (Disj (Atom p) (Neg (Atom p))) = Ku"
    by (simp add: k3.eval_def gap_p_def)
  then have "\<not> k3.sat gap_p (Disj (Atom p) (Neg (Atom p)))"
    by (simp add: k3.sat_def)
  then show ?thesis using k3.valid_iff_all_sat by blast
qed

theorem k3_explosion: "k3.entails {Atom p, Neg (Atom p)} (Atom q)"
proof -
  have "\<not> (k3.sat v (Atom p) \<and> k3.sat v (Neg (Atom p)))" for v :: "atom \<Rightarrow> k3"
    by (cases "v p") (simp_all add: k3.sat_def k3.eval_def)
  then show ?thesis unfolding k3.entails_def by blast
qed

text \<open>
  The comparison the framework is for. \<open>K3\<close> and FDE both lose excluded
  middle, so that is not what separates them; what separates them is that
  only FDE keeps a contradiction from proving everything, and it does so by
  having a glut, which \<open>K3\<close> does not.
\<close>

theorem k3_and_fde_agree_on_excluded_middle:
  "\<not> k3.valid (Disj (Atom p) (Neg (Atom p)))"
  "\<not> fde.valid (Disj (Atom p) (Neg (Atom p)))"
  by (rule k3_lem_fails, rule fde_lem_fails)

theorem k3_and_fde_differ_on_explosion:
  "k3.entails {Atom p, Neg (Atom p)} (Atom q)"
  "\<not> fde.entails {Atom p, Neg (Atom p)} (Atom q)"
  by (rule k3_explosion, rule fde_no_explosion)

text \<open>
  The four corners come for free, and record the same difference: \<open>K3\<close>
  realizes the first, second and fourth, and not the third, because the
  third corner is the glut.
\<close>

theorem k3_corners: "k3.realizable k \<longleftrightarrow> k \<in> {K1, K2, K4}"
proof
  assume "k3.realizable k"
  then obtain x where "k3.koti_of x = k" unfolding k3.realizable_def by blast
  then show "k \<in> {K1, K2, K4}" by (cases x) (simp_all add: k3.koti_of_def)
next
  assume "k \<in> {K1, K2, K4}"
  then consider "k = K1" | "k = K2" | "k = K4" by blast
  then show "k3.realizable k"
  proof cases
    case 1
    have "k3.koti_of Kt = K1" by (simp add: k3.koti_of_def)
    with 1 show ?thesis unfolding k3.realizable_def by blast
  next
    case 2
    have "k3.koti_of Kf = K2" by (simp add: k3.koti_of_def)
    with 2 show ?thesis unfolding k3.realizable_def by blast
  next
    case 3
    have "k3.koti_of Ku = K4" by (simp add: k3.koti_of_def)
    with 3 show ?thesis unfolding k3.realizable_def by blast
  qed
qed

end
