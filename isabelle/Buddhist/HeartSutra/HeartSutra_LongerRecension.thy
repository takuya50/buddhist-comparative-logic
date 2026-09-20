(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The longer recension: the frame around the core, and the samadhi as the ultimate standpoint\<close>

theory HeartSutra_LongerRecension
  imports HeartSutra_Coverage HeartSutra_Mantra Madhyamaka_StandpointSemantics
begin

text \<open>
  Everything so far formalized the short recension (\<open>HeartSutra_Text\<close>, 262
  characters). The longer recension -- surviving in Sanskrit and in five
  Chinese translations (T253 Prajna and Liyan, T254 Prajnacakra, T255
  Facheng, T257 Danapala, and the fragment T252) -- wraps that core in a
  narrative frame:

  \<^item> the setting (\<open>nidana\<close>, 序分): 如是我聞, the Buddha on Vulture Peak
    (王舍城耆闍崛山) with the assembly of monks and bodhisattvas;
  \<^item> the Buddha enters a samadhi called "vast and profound" (廣大甚深) and
    says nothing while it lasts;
  \<^item> Sariputra, moved by the Buddha's power, asks Avalokitesvara how one
    who would practise the deep perfection of wisdom should train (云何修行);
  \<^item> Avalokitesvara answers -- the answer is the short text;
  \<^item> the Buddha emerges from the samadhi and endorses the answer:
    善哉善哉, "just so, just so, as you have said";
  \<^item> the assembly rejoices (皆大歡喜, 信受奉行).

  The wording differs across the five translations and no critical edition
  is reconstructed here; unlike \<open>HeartSutra_Text\<close>, where \<open>body_262\<close> checks a
  character count, this theory formalizes only the \<^emph>\<open>structure\<close> of the
  frame and the speech act of each part. Two results:

  \<^item> Of the six parts only the answer carries assertoric content: the
    others narrate, ask, endorse or rejoice (\<open>only_answer_assertoric\<close>),
    and the answer's content is the core unchanged (\<open>answer_is_core\<close>).
    So the long recension does not add doctrine; it adds the speech
    situation, which is exactly what \<open>HeartSutra_Mantra\<close> had to note was missing
    when it classified 真言 and 是名 as not truth-apt.
  \<^item> The frame stages the two standpoints of \<open>Madhyamaka_StandpointSemantics\<close> literally.
    While in the samadhi the Buddha asserts nothing; on emerging he
    asserts the teaching. Taking those as the two standpoints, the long
    recension is a model of \<open>Madhyamaka_Vigrahavyavartani\<close>'s reading of "I have no thesis":
    the teaching is asserted at the speaking standpoint and withheld at
    the silent one (\<open>samadhi_realizes_no_thesis\<close>). The silence is not a
    gap in the text; it is the ultimate standpoint.
\<close>

subsection \<open>The six parts of the frame\<close>

datatype frame_part =
    Nidana                \<comment> \<open>序分: 如是我聞 ... 耆闍崛山\<close>
  | EnterSamadhi          \<comment> \<open>入廣大甚深三摩地\<close>
  | Question              \<comment> \<open>舍利弗問: 云何修行\<close>
  | Answer                \<comment> \<open>觀自在の答え = 262字の本文\<close>
  | Endorsement           \<comment> \<open>出定して印可: 善哉善哉\<close>
  | Rejoicing             \<comment> \<open>流通分: 皆大歡喜 信受奉行\<close>

definition frame :: "frame_part list" where
  "frame = [Nidana, EnterSamadhi, Question, Answer, Endorsement, Rejoicing]"

lemma frame_shape: "length frame = 6 \<and> distinct frame \<and> set frame = UNIV"
  by (auto simp: frame_def) (metis frame_part.exhaust)

datatype speech_kind = Narration | Silence | Asking | Instruction | Approval | Joy

fun kind_of :: "frame_part \<Rightarrow> speech_kind" where
  "kind_of Nidana = Narration"
| "kind_of EnterSamadhi = Silence"
| "kind_of Question = Asking"
| "kind_of Answer = Instruction"
| "kind_of Endorsement = Approval"
| "kind_of Rejoicing = Joy"

lemma kind_of_inj: "kind_of f = kind_of g \<Longrightarrow> f = g"
  by (cases f; cases g) simp_all

subsection \<open>Only the answer asserts, and what it asserts is the core\<close>

datatype latom = Core   \<comment> \<open>the teaching of the 262 characters, as one assertible content\<close>

fun content :: "frame_part \<Rightarrow> latom utterance option" where
  "content Answer = Some (Assert (Atom Core))"
| "content _ = None"

definition assertoric :: "frame_part \<Rightarrow> bool" where
  "assertoric f \<longleftrightarrow> (case content f of None \<Rightarrow> False | Some u \<Rightarrow> truth_apt u)"

theorem only_answer_assertoric: "assertoric f \<longleftrightarrow> f = Answer"
  by (cases f) (simp_all add: assertoric_def)

theorem answer_is_core: "content Answer = Some (Assert (Atom Core))"
  by simp

text \<open>
  The core the answer carries is the short recension's body: the same
  twenty-nine clauses, with the same character count, that
  \<open>HeartSutra_Text.body_262\<close> and \<open>HeartSutra_Coverage.coverage_complete\<close> already checked.
  The frame adds parts, not clauses.
\<close>

definition long_recension :: "frame_part list \<times> clause list" where
  "long_recension = (frame, body)"

theorem core_unchanged: "snd long_recension = body \<and> sum_list (map char_count (snd long_recension)) = 262"
  by (simp add: long_recension_def body_262)

subsection \<open>Coverage of the frame\<close>

fun frame_status :: "frame_part \<Rightarrow> status" where
  "frame_status Nidana = Noted"          \<comment> \<open>narrative setting; no propositional counterpart\<close>
| "frame_status EnterSamadhi = Proved"   \<comment> \<open>the silent standpoint, below\<close>
| "frame_status Question = Noted"        \<comment> \<open>an interrogative, not truth-apt\<close>
| "frame_status Answer = Proved"         \<comment> \<open>the whole of the short recension\<close>
| "frame_status Endorsement = Proved"    \<comment> \<open>assertion at the speaking standpoint, below\<close>
| "frame_status Rejoicing = Noted"       \<comment> \<open>an expressive, not truth-apt\<close>

theorem frame_coverage_complete: "\<forall>f. frame_status f \<noteq> Missing"
  by (rule allI, case_tac f) simp_all

theorem frame_coverage_counts:
  "length (filter (\<lambda>f. frame_status f = Proved) frame) = 3"
  "length (filter (\<lambda>f. frame_status f = Noted) frame) = 3"
  by (simp_all add: frame_def)

subsection \<open>The samadhi is the ultimate standpoint\<close>

datatype lstandpoint = InSamadhi | Speaking

definition R_long :: "lstandpoint \<Rightarrow> lstandpoint \<Rightarrow> bool" where
  "R_long w w' \<longleftrightarrow> w = Speaking \<and> w' = InSamadhi"

definition asr_long :: "lstandpoint \<Rightarrow> latom fm set" where
  "asr_long w = (case w of InSamadhi \<Rightarrow> {} | Speaking \<Rightarrow> {Atom Core})"

interpretation lg: standpoint_frame R_long asr_long .

theorem samadhi_realizes_no_thesis:
  "lg.conv_true Speaking (Atom Core)"
  "lg.ult_denies Speaking (Atom Core)"
  "lg.prasangika InSamadhi"
  "lg.ext_neg InSamadhi (Atom Core)"
  by (simp_all add: lg.conv_true_def lg.ult_denies_def lg.prasangika_def lg.ext_neg_def
                    asr_long_def R_long_def)

text \<open>
  The endorsement adds no content: the Buddha, on emerging, asserts what
  Avalokitesvara asserted, so both speakers occupy the same standpoint and
  the assertion set is unchanged.
\<close>

definition asserted_by :: "frame_part \<Rightarrow> latom fm set" where
  "asserted_by f = (if f \<in> {Answer, Endorsement} then {Atom Core} else {})"

theorem endorsement_adds_nothing: "asserted_by Endorsement = asserted_by Answer"
  by (simp add: asserted_by_def)

theorem silence_asserts_nothing: "asserted_by EnterSamadhi = {}"
  by (simp add: asserted_by_def)

theorem frame_assertions_are_the_speaking_standpoint:
  "(\<Union>f \<in> set frame. asserted_by f) = asr_long Speaking"
  by (simp add: frame_def asserted_by_def asr_long_def)

end
