(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Standpoint frames: a non-truth-functional semantics for the two truths and their iterations\<close>

theory Madhyamaka_StandpointSemantics
  imports HeartSutra_TwoTruths Madhyamaka_Jizang
begin

text \<open>
  \<open>Madhyamaka_Jizang\<close> proved a negative result: no truth-functional semantics of
  this session distinguishes Jizang's tiers beyond the second. This theory
  supplies the positive complement. A \<^emph>\<open>standpoint frame\<close> has a set of
  standpoints, a relation \<open>R w w'\<close> ("\<open>w'\<close> is a more ultimate standpoint
  than \<open>w\<close>"), and for each standpoint the set of formulas \<^emph>\<open>asserted\<close>
  there. No truth values occur. Conventional truth at \<open>w\<close> is assertion at
  \<open>w\<close>; the negation that produces an ultimate truth is \<^emph>\<open>external\<close> --
  non-assertion -- and "ultimately, from \<open>w\<close>" means "at every more
  ultimate standpoint" (Kreutz 2019 reads the catuskoti's negation as
  such an illocutionary act). Results:

  \<^item> A two-standpoint chain with the conventional standpoint asserting the
    appearances and the ultimate one withholding own-being is exactly a
    \<open>two_truths_fde\<close> model, bivalent at each standpoint by construction
    (\<open>two_points_is_two_truths\<close>): the localised consistency that
    \<open>HeartSutra_TwoTruths\<close> had to assume is here automatic.
  \<^item> A four-standpoint chain whose assertion sets are Jizang's successive
    pairs separates the four tiers (\<open>jizang_tiers_separated\<close>); each tier's
    positions are withheld at the next standpoint (\<open>each_tier_denied\<close>);
    the standpoint after the fourth asserts nothing -- 言忘慮絶
    (\<open>final_silence\<close>). Meanwhile the FDE values of the tiers' ultimates
    coincide (\<open>separation_beyond_values\<close>): assertion separates what value
    cannot.
  \<^item> Tiantai's three truths. If every standpoint asserts all three
    (\<open>yuanrong\<close>, the perfect interfusion 即空即仮即中), then nothing is
    ultimately withheld anywhere except at standpoints with no more
    ultimate standpoint at all (\<open>yuanrong_no_ultimate_denial\<close>): the
    interfused three truths abolish the conventional/ultimate hierarchy,
    as Tiantai says they do, in contrast to the separated three truths
    (隔歴三諦), which form a chain (\<open>gereki_hierarchical\<close>).
  \<^item> The Svatantrika/Prasangika difference as a frame condition: a
    standpoint whose assertion set is closed under modus ponens
    (\<open>mp_closed\<close>) versus a standpoint that asserts nothing
    (\<open>prasangika\<close>). The empty standpoint withholds every thesis
    (\<open>prasangika_no_thesis\<close>) and is trivially closed under every rule
    (\<open>prasangika_mp_closed\<close>) -- the Prasangika breaks no logic at the
    ultimate level because there is nothing there to reason from.
\<close>

locale standpoint_frame =
  fixes R :: "'w \<Rightarrow> 'w \<Rightarrow> bool"          \<comment> \<open>\<open>R w w'\<close>: \<open>w'\<close> is a more ultimate standpoint than \<open>w\<close>\<close>
    and asserted :: "'w \<Rightarrow> 'a fm set"    \<comment> \<open>what is asserted at a standpoint\<close>
begin

definition conv_true :: "'w \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "conv_true w X \<longleftrightarrow> X \<in> asserted w"

definition ext_neg :: "'w \<Rightarrow> 'a fm \<Rightarrow> bool" where   \<comment> \<open>external negation: not asserted\<close>
  "ext_neg w X \<longleftrightarrow> X \<notin> asserted w"

definition ult_denies :: "'w \<Rightarrow> 'a fm \<Rightarrow> bool" where  \<comment> \<open>withheld at every more ultimate standpoint\<close>
  "ult_denies w X \<longleftrightarrow> (\<forall>w'. R w w' \<longrightarrow> X \<notin> asserted w')"

definition mp_closed :: "'w \<Rightarrow> bool" where
  "mp_closed w \<longleftrightarrow> (\<forall>X Y. X \<in> asserted w \<longrightarrow> Disj (Neg X) Y \<in> asserted w \<longrightarrow> Y \<in> asserted w)"

definition prasangika :: "'w \<Rightarrow> bool" where
  "prasangika w \<longleftrightarrow> asserted w = {}"

lemma prasangika_no_thesis: "prasangika w \<Longrightarrow> ext_neg w X"
  by (simp add: prasangika_def ext_neg_def)

lemma prasangika_mp_closed: "prasangika w \<Longrightarrow> mp_closed w"
  by (simp add: prasangika_def mp_closed_def)

lemma terminal_denies: "\<not> (\<exists>w'. R w w') \<Longrightarrow> ult_denies w X"
  by (simp add: ult_denies_def)

end

subsection \<open>Two standpoints are the two truths\<close>

datatype hatom = Ap dharma | Own dharma   \<comment> \<open>"\<open>x\<close> appears", "\<open>x\<close> has own-being"\<close>

definition R2 :: "satya2 \<Rightarrow> satya2 \<Rightarrow> bool" where
  "R2 w w' \<longleftrightarrow> w = Samvrti \<and> w' = Paramartha"

definition tt_val :: "(satya2 \<Rightarrow> hatom fm set) \<Rightarrow> satya2 \<Rightarrow> dharma \<Rightarrow> tv4" where
  "tt_val asr t x = (if Atom (Ap x) \<in> asr t then T else F)"

definition tt_sv :: "(satya2 \<Rightarrow> hatom fm set) \<Rightarrow> satya2 \<Rightarrow> dharma \<Rightarrow> tv4" where
  "tt_sv asr t x = (if Atom (Own x) \<in> asr t then T else F)"

lemma fde_mv_logic: "mv_logic {T, B}"
  by unfold_locales (simp_all add: TB_not_UNIV)

context
  fixes asr :: "satya2 \<Rightarrow> hatom fm set"
begin

interpretation tp: standpoint_frame R2 asr .

theorem two_points_is_two_truths:
  "two_truths_fde (tt_val asr) (tt_sv asr) \<longleftrightarrow>
     (\<forall>x. tp.conv_true Samvrti (Atom (Ap x))) \<and> (\<forall>x. tp.ult_denies Samvrti (Atom (Own x)))"
  unfolding two_truths_fde_def two_truths_def two_truths_axioms_def two_truths_fde_axioms_def
            tp.conv_true_def tp.ult_denies_def R2_def
  using fde_mv_logic by (auto simp: tt_val_def tt_sv_def neg4_def mk_def)

end

subsection \<open>Four standpoints separate Jizang's four tiers\<close>

context
  fixes a :: 'a
begin

definition jz_positions :: "nat \<Rightarrow> 'a fm set" where
  "jz_positions k = {jz_conv (Atom a) k, jz_ult (Atom a) k}"

definition jz_asserted :: "nat \<Rightarrow> 'a fm set" where
  "jz_asserted k = (if k < 4 then jz_positions k else {})"

interpretation jzf: standpoint_frame "\<lambda>k k'. k' = Suc k" jz_asserted .

lemma conv_not_ult: "jz_conv (Atom a) k \<noteq> jz_ult (Atom a) k'"
  by (cases k) (simp_all add: jz_ult_def)

lemma conv_inj: "jz_conv (Atom a) k = jz_conv (Atom a) k' \<Longrightarrow> k = k'"
proof (rule ccontr)
  assume eq: "jz_conv (Atom a) k = jz_conv (Atom a) k'" and ne: "k \<noteq> k'"
  have "size (jz_conv (Atom a) k) \<noteq> size (jz_conv (Atom a) k')"
    using ne jz_conv_size_mono[of k k' "Atom a"] jz_conv_size_mono[of k' k "Atom a"]
    by (auto simp: neq_iff)
  then show False using eq by simp
qed

lemma ult_inj: "jz_ult (Atom a) k = jz_ult (Atom a) k' \<Longrightarrow> k = k'"
  using jz_tiers_distinct[of k k' "Atom a"] by blast

theorem jizang_tiers_separated:
  "k < 4 \<Longrightarrow> k' < 4 \<Longrightarrow> k \<noteq> k' \<Longrightarrow> jz_asserted k \<noteq> jz_asserted k'"
  unfolding jz_asserted_def jz_positions_def
  using conv_inj[of k k'] conv_not_ult[of k k'] by auto

theorem each_tier_denied: "X \<in> jz_asserted k \<Longrightarrow> jzf.ult_denies k X"
  unfolding jzf.ult_denies_def jz_asserted_def jz_positions_def
  using conv_inj[of k "Suc k"] conv_not_ult[of k "Suc k"] conv_not_ult[of "Suc k" k]
        ult_inj[of k "Suc k"]
  by auto

theorem final_silence: "jz_asserted 4 = {}" "jzf.prasangika 4"
  by (simp_all add: jz_asserted_def jzf.prasangika_def)

theorem separation_beyond_values:
  assumes "Suc n < 4" "Suc m < 4" "n \<noteq> m"
  shows "jz_asserted (Suc n) \<noteq> jz_asserted (Suc m)"
    and "ev4 v (jz_ult (Atom a) (Suc n)) = ev4 v (jz_ult (Atom a) (Suc m))"
  using assms jizang_tiers_separated[of "Suc n" "Suc m"] by (simp_all add: jz_fde_ult_stabilizes)

end

subsection \<open>Tiantai: interfused versus separated three truths\<close>

datatype santai = Kong | Jia | Zhong   \<comment> \<open>空 · 仮 · 中\<close>

definition yuanrong :: "('w \<Rightarrow> santai fm set) \<Rightarrow> bool" where   \<comment> \<open>圓融三諦: all three everywhere\<close>
  "yuanrong asr \<longleftrightarrow> (\<forall>w. {Atom Kong, Atom Jia, Atom Zhong} \<subseteq> asr w)"

context
  fixes R :: "'w \<Rightarrow> 'w \<Rightarrow> bool" and asr :: "'w \<Rightarrow> santai fm set"
begin

interpretation tt: standpoint_frame R asr .

theorem yuanrong_no_ultimate_denial:
  assumes "yuanrong asr" and "s \<in> {Kong, Jia, Zhong}"
  shows "tt.ult_denies w (Atom s) \<longleftrightarrow> \<not> (\<exists>w'. R w w')"
  using assms unfolding yuanrong_def tt.ult_denies_def by auto

end

datatype stage = St_Jia | St_Kong | St_Zhong

definition R3 :: "stage \<Rightarrow> stage \<Rightarrow> bool" where
  "R3 w w' \<longleftrightarrow> (w = St_Jia \<and> w' = St_Kong) \<or> (w = St_Kong \<and> w' = St_Zhong)"

definition asr3 :: "stage \<Rightarrow> santai fm set" where
  "asr3 w = (case w of St_Jia \<Rightarrow> {Atom Jia} | St_Kong \<Rightarrow> {Atom Kong} | St_Zhong \<Rightarrow> {Atom Zhong})"

interpretation gereki: standpoint_frame R3 asr3 .

theorem gereki_hierarchical:
  "gereki.conv_true St_Jia (Atom Jia)" "gereki.ult_denies St_Jia (Atom Jia)"
  "gereki.conv_true St_Kong (Atom Kong)" "gereki.ult_denies St_Kong (Atom Kong)"
  by (auto simp: gereki.conv_true_def gereki.ult_denies_def R3_def asr3_def)

theorem gereki_not_yuanrong: "\<not> yuanrong asr3"
  unfolding yuanrong_def by (rule notI, drule spec[of _ St_Jia]) (simp add: asr3_def)

end
