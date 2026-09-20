(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The two truths as two evaluation points: does localizing consistency recover HS06?\<close>

theory HeartSutra_TwoTruths
  imports Madhyamaka_MMK24
begin

text \<open>
  \<open>HeartSutra_Emptiness\<close> found that under FDE the "not different from" reading of
  HS06 (\<open>色不異空 空不異色\<close>) is \<^emph>\<open>not\<close> derivable from the sutra's own
  premises: a glut for own-being (\<open>sv x = B\<close>) satisfies "own-being is
  negated" while still letting "form together with own-being" be
  designated. This theory tests the standard Madhyamaka remedy, the two
  truths (\<open>satyadvaya\<close>, 二諦): evaluate "form" at the conventional truth
  (\<open>samvrti\<close>, 世俗諦) and "own-being" at the ultimate truth
  (\<open>paramartha\<close>, 勝義諦), and read HS06-07 as \<^emph>\<open>cross-truth\<close> statements.

  Result. The two-truths semantics recovers HS06 under FDE, and makes all
  three readings of HS06-07 coincide again, exactly when each truth is
  \<^emph>\<open>internally consistent\<close> about its own subject matter: no glut for
  "form" at the conventional level and no glut for "own-being" at the
  ultimate level. Drop either consistency assumption and the corresponding
  conjunct of HS06 fails again (two countermodels below). So what the two
  truths buy is not paraconsistency but its \<^emph>\<open>localization\<close>: the
  contradiction "form and no own-being" is spread over two evaluation
  points, each of which is classical about what it asserts.
\<close>

datatype satya2 = Samvrti | Paramartha

locale two_truths = mv_logic D neg mconj mdisj
  for D :: "'v set" and neg mconj mdisj +
  fixes val   :: "satya2 \<Rightarrow> dharma \<Rightarrow> 'v"   \<comment> \<open>appearance / being of \<open>x\<close> at a truth\<close>
    and sv_at :: "satya2 \<Rightarrow> dharma \<Rightarrow> 'v"   \<comment> \<open>own-being of \<open>x\<close> at a truth\<close>
  assumes conv_appears: "val Samvrti x \<in> D"           \<comment> \<open>conventionally, form appears\<close>
      and ult_empty:    "neg (sv_at Paramartha x) \<in> D"  \<comment> \<open>ultimately, no own-being\<close>
begin

definition sunya_at :: "satya2 \<Rightarrow> dharma \<Rightarrow> 'v" where
  "sunya_at t x = neg (sv_at t x)"

text \<open>The three readings of HS06-07, now across the two truths.\<close>

definition X_identity :: "dharma \<Rightarrow> bool" where
  "X_identity x \<longleftrightarrow> val Samvrti x = sunya_at Paramartha x"

definition X_mutual :: "dharma \<Rightarrow> bool" where
  "X_mutual x \<longleftrightarrow> (val Samvrti x \<in> D \<longleftrightarrow> sunya_at Paramartha x \<in> D)"

definition X_notsep :: "dharma \<Rightarrow> bool" where
  "X_notsep x \<longleftrightarrow>
     mconj (val Samvrti x) (sv_at Paramartha x) \<notin> D \<and>
     mconj (sunya_at Paramartha x) (neg (val Samvrti x)) \<notin> D"

lemma X_mutual_always: "X_mutual x"
  unfolding X_mutual_def sunya_at_def using conv_appears ult_empty by blast

end

text \<open>
  Every single-truth \<open>emptiness\<close> model is a two-truths model in which both
  truths coincide, so \<open>two_truths\<close> is a generalization, not a rival.
\<close>

sublocale emptiness \<subseteq> flat: two_truths D neg mconj mdisj "\<lambda>_. appears" "\<lambda>_. sv"
  by unfold_locales (simp_all add: samvrti mmk_24_18 pratitya)

subsection \<open>FDE with locally consistent truths\<close>

locale two_truths_fde = two_truths "{T, B}" neg4 conj4 disj4 val sv_at
  for val sv_at :: "satya2 \<Rightarrow> dharma \<Rightarrow> tv4" +
  assumes conv_consistent: "neg4 (val Samvrti x) \<notin> {T, B}"    \<comment> \<open>form is not a glut conventionally\<close>
      and ult_consistent:  "sv_at Paramartha x \<notin> {T, B}"       \<comment> \<open>own-being is not a glut ultimately\<close>
begin

lemma conv_T: "val Samvrti x = T"
  using conv_appears[of x] conv_consistent[of x]
  by (cases "val Samvrti x") (simp_all add: neg4_def mk_def)

lemma ult_F: "sv_at Paramartha x = F"
  using ult_empty[of x] ult_consistent[of x]
  by (cases "sv_at Paramartha x") (simp_all add: neg4_def mk_def)

theorem hs06_two_truths: "X_notsep x"
  unfolding X_notsep_def sunya_at_def
  by (simp add: conv_T ult_F neg4_def conj4_def mk_def)

theorem hs07_two_truths: "X_identity x"
  unfolding X_identity_def sunya_at_def by (simp add: conv_T ult_F neg4_def mk_def)

theorem two_truths_readings_coincide:
  "X_identity x" "X_mutual x" "X_notsep x"
  by (rule hs07_two_truths) (rule X_mutual_always, rule hs06_two_truths)

end

text \<open>
  Necessity of both consistency assumptions. Each countermodel satisfies
  \<open>two_truths\<close> under FDE and violates exactly one of them, and in each the
  corresponding conjunct of \<open>X_notsep\<close> fails.
\<close>

text \<open>
  The first countermodel needs no new interpretation: it is the flattening
  (\<open>flat\<close>) of the single-truth glut model \<open>fde_glut\<close> from \<open>HeartSutra_Emptiness\<close>
  (own-being \<open>B\<close>, appearance \<open>T\<close>), which the \<open>sublocale\<close> above turns into
  a two-truths model with \<open>sv_at Paramartha x = B\<close>.
\<close>

lemma ult_glut_breaks_hs06: "\<not> fde_glut.flat.X_notsep x"
  unfolding fde_glut.flat.X_notsep_def fde_glut.flat.sunya_at_def
  by (simp add: neg4_def conj4_def mk_def)

interpretation tt_conv_glut: two_truths "{T, B}" neg4 conj4 disj4
  "\<lambda>_ _. B" "\<lambda>_ _. F"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

lemma conv_glut_breaks_hs06: "\<not> tt_conv_glut.X_notsep x"
  unfolding tt_conv_glut.X_notsep_def tt_conv_glut.sunya_at_def
  by (simp add: neg4_def conj4_def mk_def)

text \<open>
  Non-vacuity: the locally consistent two-truths locale has a model, and
  it is the model one expects -- form plainly true conventionally, own-being
  plainly false ultimately.
\<close>

lemma two_truths_fde_consistent:
  "two_truths_fde (\<lambda>_ _. T) (\<lambda>_ _. F)"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

text \<open>
  Where the glut went. In the single-truth FDE model that defeated HS06,
  own-being carried the value \<open>B\<close>. In the two-truths model the same dharma
  carries \<open>T\<close> (as form, conventionally) and \<open>F\<close> (as own-being, ultimately):
  the information-order join of the two verdicts on "\<open>x\<close> is (there)" is a
  glut, but no single evaluation point holds it.
\<close>

definition info_join :: "tv4 \<Rightarrow> tv4 \<Rightarrow> tv4" where
  "info_join x y = mk (tr x \<or> tr y) (fa x \<or> fa y)"

lemma info_join_T_F: "info_join T F = B"
  by (simp add: info_join_def mk_def)

end
