(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The Vigrahavyavartani: the emptiness of the statement of emptiness, and "I have no thesis"\<close>

theory Madhyamaka_Vigrahavyavartani
  imports Madhyamaka_MMK24 Madhyamaka_StandpointSemantics
begin

text \<open>
  The opponent of the \<^emph>\<open>Vigrahavyavartani\<close> (廻諍論) opens: if all things
  lack own-being, so does your statement "all things lack own-being", and
  a statement without own-being cannot negate anything (VV 1-2).
  Nagarjuna's reply (VV 21-29): the statement is indeed empty
  (\<^emph>\<open>sunyata-sunyata\<close>, 空空), empty things nonetheless do their work, as a
  chariot carries and fire burns (VV 22); the opponent's principle would
  disable the opponent's own objection (VV 20); and "I have no thesis"
  (\<open>nasti ca mama pratijna\<close>, VV 29).

  Formalization. The statement and the objection are added as items
  alongside the dharmas. In a Madhyamaka-style locale where every item is
  dependently arisen and own-being is non-arising:

  \<^item> the statement is empty (\<open>sunyata_sunyata\<close>) -- there is no
    self-reference problem, because "empty" is a property of items, not a
    truth predicate on sentences;
  \<^item> classically, the opponent's premise "only what has own-being
    works" entails that nothing works, the objection included
    (\<open>opponent_premise_self_refuting\<close>, \<open>opponent_premise_kills_objection\<close>);
    Nagarjuna's counter-premise "what is arisen works" makes the
    statement both empty and effective (\<open>nagarjuna_reply\<close>);
  \<^item> under FDE the opponent's premise and an effective statement can be
    held together, but only by making the statement's own-being a glut
    (\<open>vv_fde_glut\<close>): the paraconsistent way out asserts that the
    statement both has and lacks own-being;
  \<^item> in a standpoint frame "I have no thesis" is exact: the statement is
    asserted at the conventional standpoint, withheld at the ultimate one,
    and the ultimate standpoint asserts nothing at all
    (\<open>no_thesis_consistent\<close>) -- asserting while holding no thesis is
    consistent once the two acts are located at two standpoints.

  Chapman (2026) formalizes the same self-application in classical modal
  logic over Belnap-Dunn values in Lean 4, with a modal operator carrying
  the "no thesis" content. Here no modal operator is used: the two
  standpoints and their assertion sets do that work.
\<close>

datatype vdharma = VD dharma | Statement | Objection

locale vigraha = mv_logic D neg mconj mdisj
  for D :: "'v set" and neg mconj mdisj +
  fixes arisen    :: "vdharma \<Rightarrow> 'v"
    and works :: "vdharma \<Rightarrow> bool"   \<comment> \<open>does its work (negates, carries, burns)\<close>
  assumes neg_invol_v: "neg (neg w) = w"
      and arisen_all:  "arisen x \<in> D"
begin

definition svabhava_v :: "vdharma \<Rightarrow> 'v" where "svabhava_v x = neg (arisen x)"
definition empty_v :: "vdharma \<Rightarrow> bool" where "empty_v x \<longleftrightarrow> neg (svabhava_v x) \<in> D"

theorem all_empty: "empty_v x"
  unfolding empty_v_def svabhava_v_def by (simp add: neg_invol_v arisen_all)

theorem sunyata_sunyata: "empty_v Statement"
  by (rule all_empty)

definition opponent_premise :: bool where   \<comment> \<open>VV 1: only what has own-being works\<close>
  "opponent_premise \<longleftrightarrow> (\<forall>x. works x \<longrightarrow> svabhava_v x \<in> D)"

definition nagarjuna_premise :: bool where  \<comment> \<open>VV 22: what is dependently arisen works\<close>
  "nagarjuna_premise \<longleftrightarrow> (\<forall>x. arisen x \<in> D \<longrightarrow> works x)"

theorem nagarjuna_reply: "nagarjuna_premise \<Longrightarrow> works Statement \<and> empty_v Statement"
  unfolding nagarjuna_premise_def using arisen_all sunyata_sunyata by blast

end

subsection \<open>Classically the opponent's principle silences the opponent\<close>

locale cl_vigraha = vigraha "{True}" Not "(\<and>)" "(\<or>)" arisen works
  for arisen :: "vdharma \<Rightarrow> bool" and works
begin

lemma cl_no_svabhava: "svabhava_v x \<notin> {True}"
  unfolding svabhava_v_def using arisen_all[of x] by simp

theorem opponent_premise_self_refuting: "opponent_premise \<Longrightarrow> \<not> works x"
  unfolding opponent_premise_def using cl_no_svabhava by blast

theorem opponent_premise_kills_objection: "opponent_premise \<Longrightarrow> \<not> works Objection"
  by (rule opponent_premise_self_refuting)

end

subsection \<open>Under FDE the paraconsistent escape is a glut on own-being\<close>

locale fde_vigraha = vigraha "{T, B}" neg4 conj4 disj4 arisen works
  for arisen :: "vdharma \<Rightarrow> tv4" and works
begin

theorem vv_fde_glut: "opponent_premise \<Longrightarrow> works x \<Longrightarrow> arisen x = B"
  unfolding opponent_premise_def svabhava_v_def
  using arisen_all[of x] by (cases "arisen x") (auto simp: neg4_def mk_def)

end

text \<open>The glut model exists: everything both is and is not arisen, and everything works.\<close>

interpretation vv_glut: vigraha "{T, B}" neg4 conj4 disj4 "\<lambda>_. B" "\<lambda>_. True"
  by unfold_locales (simp_all add: TB_not_UNIV)

lemma cl_vigraha_nonvacuous: "cl_vigraha (\<lambda>_. True)"
  by unfold_locales (simp_all add: True_not_UNIV)

lemma fde_vigraha_nonvacuous: "fde_vigraha (\<lambda>_. B)"
  by unfold_locales (simp_all add: TB_not_UNIV)

theorem vv_fde_glut_model:
  "vv_glut.opponent_premise" "vv_glut.empty_v Statement" "(\<lambda>_. True) Statement"
  by (simp_all add: vv_glut.opponent_premise_def vv_glut.svabhava_v_def vv_glut.empty_v_def
                    neg4_def mk_def)

subsection \<open>"I have no thesis": two standpoints\<close>

datatype vatom = Thesis   \<comment> \<open>"all dharmas are empty", as a formula to be asserted or withheld\<close>

definition asr_vv :: "satya2 \<Rightarrow> vatom fm set" where
  "asr_vv w = (case w of Samvrti \<Rightarrow> {Atom Thesis} | Paramartha \<Rightarrow> {})"

interpretation vv: standpoint_frame R2 asr_vv .

theorem no_thesis_consistent:
  "vv.conv_true Samvrti (Atom Thesis)"
  "vv.ult_denies Samvrti (Atom Thesis)"
  "vv.prasangika Paramartha"
  "vv.ext_neg Paramartha (Atom Thesis)"
  by (simp_all add: vv.conv_true_def vv.ult_denies_def vv.prasangika_def vv.ext_neg_def
                    asr_vv_def R2_def)

end
