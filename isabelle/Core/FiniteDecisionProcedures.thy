(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Executable decision procedures for the three-atom fragment\<close>

theory FiniteDecisionProcedures
  imports Madhyamaka_Jizang HeartSutra_Connexive HeartSutra_Emptiness
begin

text \<open>
  All logics in this session are finite matrices, so validity and
  entailment over the three atoms \<open>p, q, r\<close> are decidable by enumerating
  valuations: 8 classical, 64 for FDE, 125 for FDE5. This theory defines
  the enumerations, proves they are exhaustive, proves the resulting
  checkers correct with respect to the semantic definitions, and then
  re-derives several of the session's results by evaluation
  (\<^theory_text>\<open>by eval\<close>). In the vocabulary of this repository these are
  executable certificates: the same facts, established by computation
  instead of proof search.
\<close>

definition mkv :: "'v \<Rightarrow> 'v \<Rightarrow> 'v \<Rightarrow> atom \<Rightarrow> 'v" where
  "mkv x y z a = (case a of p \<Rightarrow> x | q \<Rightarrow> y | r \<Rightarrow> z)"

definition all_vals :: "'v list \<Rightarrow> (atom \<Rightarrow> 'v) list" where
  "all_vals vs = concat (map (\<lambda>x. concat (map (\<lambda>y. map (\<lambda>z. mkv x y z) vs) vs)) vs)"

lemma mkv_self: "mkv (f p) (f q) (f r) = f"
  by (rule ext) (simp add: mkv_def split: atom.split)

lemma all_vals_UNIV:
  assumes "set (vs :: 'v list) = UNIV"
  shows "set (all_vals vs) = UNIV"
proof
  show "UNIV \<subseteq> set (all_vals vs)"
  proof
    fix f :: "atom \<Rightarrow> 'v"
    have "mkv (f p) (f q) (f r) \<in> set (all_vals vs)"
      unfolding all_vals_def using assms by auto
    then show "f \<in> set (all_vals vs)" by (simp add: mkv_self)
  qed
qed simp

definition tv5s :: "tv5 list" where "tv5s = [Fin T, Fin B, Fin N, Fin F, E]"
definition bools :: "bool list" where "bools = [True, False]"

lemma set_tv4s: "set tv4s = UNIV"
  by (auto simp: tv4s_def) (metis tv4.exhaust)
lemma set_tv5s: "set tv5s = UNIV"
  by (auto simp: tv5s_def) (metis tv5.exhaust tv4.exhaust)
lemma set_bools: "set bools = UNIV"
  by (auto simp: bools_def)

subsection \<open>Checkers and their correctness\<close>

definition valid2 :: "atom fm \<Rightarrow> bool" where
  "valid2 X \<longleftrightarrow> list_all (\<lambda>v. mv_eval Not (\<and>) (\<or>) v X) (all_vals bools)"
definition valid4 :: "atom fm \<Rightarrow> bool" where
  "valid4 X \<longleftrightarrow> list_all (\<lambda>v. mv_eval neg4 conj4 disj4 v X \<in> {T, B}) (all_vals tv4s)"
definition valid5 :: "atom fm \<Rightarrow> bool" where
  "valid5 X \<longleftrightarrow> list_all (\<lambda>v. mv_eval neg5 conj5 disj5 v X \<in> {Fin T, Fin B}) (all_vals tv5s)"
definition entails4 :: "atom fm list \<Rightarrow> atom fm \<Rightarrow> bool" where
  "entails4 \<Gamma> X \<longleftrightarrow> list_all (\<lambda>v. list_all (\<lambda>Y. mv_eval neg4 conj4 disj4 v Y \<in> {T, B}) \<Gamma>
                                 \<longrightarrow> mv_eval neg4 conj4 disj4 v X \<in> {T, B}) (all_vals tv4s)"
definition cvalid_dec :: "(tv4 \<Rightarrow> tv4 \<Rightarrow> tv4) \<Rightarrow> atom cfm \<Rightarrow> bool" where
  "cvalid_dec imp X \<longleftrightarrow> list_all (\<lambda>v. ceval imp v X \<in> {T, B}) (all_vals tv4s)"

theorem valid2_correct: "cl.valid X \<longleftrightarrow> valid2 X"
  unfolding cl.valid_iff_all_sat cl.sat_def cl.eval_def valid2_def list_all_iff
            all_vals_UNIV[OF set_bools] by simp

theorem valid4_correct: "fde.valid X \<longleftrightarrow> valid4 X"
  unfolding fde.valid_iff_all_sat fde.sat_def fde.eval_def valid4_def list_all_iff
            all_vals_UNIV[OF set_tv4s] by simp

theorem valid5_correct: "fde5.valid X \<longleftrightarrow> valid5 X"
  unfolding fde5.valid_iff_all_sat fde5.sat_def fde5.eval_def valid5_def list_all_iff
            all_vals_UNIV[OF set_tv5s] by simp

theorem entails4_correct: "fde.entails (set \<Gamma>) X \<longleftrightarrow> entails4 \<Gamma> X"
  unfolding fde.entails_def fde.sat_def fde.eval_def entails4_def list_all_iff
            all_vals_UNIV[OF set_tv4s] by simp

theorem cvalid_dec_correct: "cvalid imp X \<longleftrightarrow> cvalid_dec imp X"
  unfolding cvalid_def csat_def cvalid_dec_def list_all_iff all_vals_UNIV[OF set_tv4s] by simp

subsection \<open>The session's results, recomputed\<close>

lemma "valid2 (Disj (Atom p) (Neg (Atom p)))" by eval
lemma "\<not> valid4 (Disj (Atom p) (Neg (Atom p)))" by eval
lemma "\<not> valid5 (Disj (Atom p) (Neg (Atom p)))" by eval
lemma "\<not> entails4 [Atom p, Disj (Neg (Atom p)) (Atom q)] (Atom q)" by eval   \<comment> \<open>modus ponens\<close>
lemma "\<not> entails4 [Atom p, Neg (Atom p)] (Atom q)" by eval                     \<comment> \<open>explosion\<close>
lemma "cvalid_dec cimp4 (CNeg (CImp (CAtom p) (CNeg (CAtom p))))" by eval      \<comment> \<open>Aristotle\<close>
lemma "\<not> cvalid_dec mimp4 (CNeg (CImp (CAtom p) (CNeg (CAtom p))))" by eval
lemma "cvalid_dec cimp4 (CImp (CImp (CAtom p) (CAtom q)) (CNeg (CImp (CAtom p) (CNeg (CAtom q)))))"
  by eval                                                                          \<comment> \<open>Boethius\<close>

text \<open>HS10 at the formula level: designated exactly at the glut.\<close>

lemma "list_all (\<lambda>v. (mv_eval neg4 conj4 disj4 v (hs10_formula p) \<in> {T, B}) = (v p = B)) (all_vals tv4s)"
  by eval

text \<open>Jizang's ladder: tiers 2, 3, 4 have one value, under every FDE valuation.\<close>

lemma "list_all (\<lambda>v. ev4 v (jz_ult (Atom p) 1) = ev4 v (jz_ult (Atom p) 2) \<and>
                      ev4 v (jz_ult (Atom p) 2) = ev4 v (jz_ult (Atom p) 3)) (all_vals tv4s)"
  by eval

text \<open>The truth tables of the FDE connectives, as data.\<close>

value "map (\<lambda>x. (x, neg4 x)) tv4s"
value "map (\<lambda>(x, y). ((x, y), conj4 x y)) (List.product tv4s tv4s)"

end
