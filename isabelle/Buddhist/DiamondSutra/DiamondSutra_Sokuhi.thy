(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The Diamond Sutra's "logic of sokuhi": A, not-A, therefore called A\<close>

theory DiamondSutra_Sokuhi
  imports HeartSutra_TwoTruths HeartSutra_Connexive
begin

text \<open>
  The \<^emph>\<open>Vajracchedika\<close> (金剛般若經, Kumarajiva's translation T235) repeats one
  schema: "\<open>X\<close> as spoken of by the Tathagata is not \<open>X\<close>; that is why it is
  called \<open>X\<close>" -- 「X者 即非X 是名X」. D. T. Suzuki named the pattern
  \<^emph>\<open>sokuhi no ronri\<close> (即非の論理), "the logic of is/is-not", and read it as
  "\<open>A\<close> is \<open>A\<close> because \<open>A\<close> is not \<open>A\<close>". Instances in T235 include
  (section numbers follow the traditional 32-section division):

  般若波羅蜜 (13), 微塵 (13), 世界 (13), 三十二相 (13), 第一波羅蜜 (14),
  忍辱波羅蜜 (14), 一切法 (17), 莊嚴佛土 (10, 17), 具足色身 (20),
  諸相具足 (20), 衆生 (21), 善法 (23), 凡夫 (25), 一合相 (30), 法相 (31),
  我見人見衆生見壽者見 (31).

  The schema has three clauses: \<^emph>\<open>setsu\<close> (説, the Tathagata speaks of \<open>X\<close>),
  \<^emph>\<open>sokuhi\<close> (即非, it is not \<open>X\<close>), \<^emph>\<open>zemyo\<close> (是名, it is called \<open>X\<close>). We
  evaluate the triple under the readings already available in this session
  and prove:

  \<^item> Read at a \<^emph>\<open>single\<close> level -- "\<open>X\<close>" and "not \<open>X\<close>" about the same
    value -- the first two clauses are classically unsatisfiable, and under
    FDE (or FDE5) they are jointly satisfiable exactly when \<open>X\<close> is a glut.
    A connexive reading of 即非 as \<open>\<not>(X \<rightarrow> X)\<close> says only "\<open>X\<close> is not plainly
    true", and together with 説 again forces the glut.
  \<^item> Read across the \<^emph>\<open>two truths\<close> -- 説 about the conventional appearance
    of \<open>X\<close>, 即非 about its ultimate own-being -- the triple is satisfiable
    with bivalent values, no contradiction is asserted anywhere, and 是名
    is exactly \<open>prajnapti\<close> (dependent designation, MMK 24:18): the thing
    appears and lacks own-being. On this reading Suzuki's "because" is the
    observation that 是名 follows from 説 together with 即非 but not from
    説 alone: what makes a name a \<^emph>\<open>mere\<close> name is the denial of own-being.

  So the "logic of sokuhi" needs no logic beyond the two truths of
  \<open>HeartSutra_TwoTruths\<close>; the paraconsistent readings are available but pay for the
  schema with a true contradiction that the two-truths reading avoids.
\<close>

datatype sokuhi_term =
    Prajnaparamita | Paramanu | Lokadhatu | Laksana32 | PrathamaParamita
  | KsantiParamita | Sarvadharma | Ksetravyuha | Rupakaya | LaksanaSampat
  | Sattva | Kusaladharma | Prthagjana | Pindagraha | Dharmalaksana | Atmadrsti

definition sokuhi_sections :: "(sokuhi_term \<times> nat) list" where
  "sokuhi_sections =
     [(Prajnaparamita, 13), (Paramanu, 13), (Lokadhatu, 13), (Laksana32, 13),
      (PrathamaParamita, 14), (KsantiParamita, 14), (Sarvadharma, 17), (Ksetravyuha, 17),
      (Rupakaya, 20), (LaksanaSampat, 20), (Sattva, 21), (Kusaladharma, 23),
      (Prthagjana, 25), (Pindagraha, 30), (Dharmalaksana, 31), (Atmadrsti, 31)]"

lemma sokuhi_sections_shape: "length sokuhi_sections = 16 \<and> distinct (map fst sokuhi_sections)"
  by (simp add: sokuhi_sections_def)

subsection \<open>Single-level readings\<close>

context mv_logic
begin

definition setsu :: "('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> bool" where "setsu v a \<longleftrightarrow> v a \<in> D"
definition hi    :: "('a \<Rightarrow> 'v) \<Rightarrow> 'a \<Rightarrow> bool" where "hi v a \<longleftrightarrow> neg (v a) \<in> D"

end

theorem sokuhi_classical_unsat: "\<not> (cl.setsu v a \<and> cl.hi v a)"
  by (simp add: cl.setsu_def cl.hi_def)

theorem sokuhi_fde_iff_glut: "fde.setsu w a \<and> fde.hi w a \<longleftrightarrow> w a = B"
  by (cases "w a") (simp_all add: fde.setsu_def fde.hi_def neg4_def mk_def)

theorem sokuhi_fde5_iff_glut: "fde5.setsu v a \<and> fde5.hi v a \<longleftrightarrow> v a = Fin B"
proof (cases "v a")
  case (Fin x) then show ?thesis by (cases x) (simp_all add: fde5.setsu_def fde5.hi_def neg4_def mk_def)
next
  case E then show ?thesis by (simp add: fde5.setsu_def fde5.hi_def)
qed

text \<open>Connexive reading of 即非: "it is not the case that \<open>X\<close>, if \<open>X\<close>" (MC).\<close>

theorem sokuhi_connexive_iff: "csat cimp4 v (CNeg (CImp (CAtom a) (CAtom a))) \<longleftrightarrow> v a \<noteq> T"
  unfolding csat_def in_TB_iff_tr by (cases "v a") (simp_all add: cimp4_def neg4_def)

theorem sokuhi_connexive_forces_glut:
  "csat cimp4 v (CAtom a) \<and> csat cimp4 v (CNeg (CImp (CAtom a) (CAtom a))) \<longleftrightarrow> v a = B"
  unfolding csat_def in_TB_iff_tr by (cases "v a") (simp_all add: cimp4_def neg4_def)

subsection \<open>The two-truths reading\<close>

locale sokuhi_two_truths =
  fixes named :: "'t \<Rightarrow> tv4"   \<comment> \<open>説X: \<open>X\<close> as conventionally spoken of\<close>
    and own   :: "'t \<Rightarrow> tv4"   \<comment> \<open>own-being of \<open>X\<close>, ultimately\<close>
  assumes setsu_c: "named x \<in> {T, B}"
      and hi_u:    "neg4 (own x) \<in> {T, B}"
      and conv_consistent: "neg4 (named x) \<notin> {T, B}"
      and ult_consistent:  "own x \<notin> {T, B}"
begin

definition zemyo :: "'t \<Rightarrow> bool" where   \<comment> \<open>是名X: mere designation = prajnapti\<close>
  "zemyo x \<longleftrightarrow> named x \<in> {T, B} \<and> neg4 (own x) \<in> {T, B}"

lemma named_T: "named x = T"
  using setsu_c[of x] conv_consistent[of x] by (cases "named x") (simp_all add: neg4_def mk_def)

lemma own_F: "own x = F"
  using hi_u[of x] ult_consistent[of x] by (cases "own x") (simp_all add: neg4_def mk_def)

theorem sokuhi_bivalent: "named x \<in> {T, F} \<and> own x \<in> {T, F}"
  by (simp add: named_T own_F)

theorem sokuhi_no_contradiction: "named x \<noteq> B \<and> own x \<noteq> B"
  by (simp add: named_T own_F)

theorem zemyo_holds: "zemyo x"
  unfolding zemyo_def by (simp add: named_T own_F neg4_def mk_def)

end

text \<open>
  The two-truths reading of the Heart Sutra (\<open>two_truths_fde\<close>) is a model of
  the sokuhi schema for every dharma: 説 is conventional appearance, 即非 is
  ultimate emptiness, and 是名 is \<open>prajnapti\<close>.
\<close>

sublocale two_truths_fde \<subseteq> sokuhi: sokuhi_two_truths "val Samvrti" "sv_at Paramartha"
  by unfold_locales (rule conv_appears ult_empty conv_consistent ult_consistent)+

text \<open>
  Suzuki's "because": 是名 is not derivable from 説 alone. The eternalist
  model -- named and own-being both plainly true -- has 説X without 即非X,
  and there \<open>X\<close> is not a mere name.
\<close>

definition zemyo_of :: "('t \<Rightarrow> tv4) \<Rightarrow> ('t \<Rightarrow> tv4) \<Rightarrow> 't \<Rightarrow> bool" where
  "zemyo_of named own x \<longleftrightarrow> named x \<in> {T, B} \<and> neg4 (own x) \<in> {T, B}"

theorem zemyo_needs_hi:
  "(\<lambda>_. T) x \<in> {T, B} \<and> \<not> zemyo_of (\<lambda>_. T) (\<lambda>_. T) x"
  by (simp add: zemyo_of_def neg4_def mk_def)

theorem zemyo_iff_setsu_and_hi:
  "zemyo_of named own x \<longleftrightarrow> fde.setsu named x \<and> fde.hi own x"
  by (simp add: zemyo_of_def fde.setsu_def fde.hi_def)

end
