(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Dharmakirti's three kinds of reason, and where the inductive premise hides\<close>

theory Dharmakirti_Reasons
  imports Dignaga_Hetucakra
begin

text \<open>
  \<open>Dignaga_Hetucakra\<close> showed that Dignaga's three marks do not by themselves
  yield the thesis: a uniformity premise is needed. Dharmakirti's reform
  (\<^emph>\<open>Nyayabindu\<close> II) is to make that premise explicit as \<^emph>\<open>pervasion\<close>
  (\<open>vyapti\<close>) and to ask what grounds it. He admits three kinds of reason:

  \<^item> \<open>svabhava-hetu\<close> (自性因), the reason is a property included in the
    property to be proved -- "it is a tree, because it is a simsapa";
  \<^item> \<open>karya-hetu\<close> (果因), the reason is an effect of the property to be
    proved -- "there is fire, because there is smoke";
  \<^item> \<open>anupalabdhi-hetu\<close> (不可得因), non-perception of something perceptible
    proves its absence -- "there is no pot here, because none is seen".

  Formally: with pervasion the marks are deductively sound (\<open>vyapti_sound\<close>),
  and pervasion implies the third mark (\<open>vyapti_gives_vyatireka\<close>) but the
  three marks do not imply pervasion (the \<open>nofire\<close> model of \<open>Dignaga_Hetucakra\<close>).
  For the identity reason pervasion is a conceptual inclusion and holds by
  stipulation. For the effect reason pervasion is a causal law that must
  be supplied from outside the inference: without it the marks can hold
  and the thesis fail (\<open>karyahetu_needs_causal_law\<close>). For non-perception
  the missing premise is \<^emph>\<open>perceptibility\<close> (\<open>drsyanupalabdhi\<close>): an
  imperceptible thing can be present and unperceived
  (\<open>anupalabdhi_needs_perceptibility\<close>). In each case the formal system
  locates the same thing: the inductive or empirical premise that the
  Buddhist logicians debated is exactly the gap between the three marks
  and the conclusion.
\<close>

subsection \<open>Pervasion\<close>

locale dharmakirti = anumana paksa S H
  for paksa :: 'l and S H :: "'l \<Rightarrow> bool" +
  fixes vyapti :: bool
  assumes vyapti_iff: "vyapti \<longleftrightarrow> (\<forall>x. H x \<longrightarrow> S x)"
begin

theorem vyapti_sound: "vyapti \<Longrightarrow> paksadharmata \<Longrightarrow> S paksa"
  by (simp add: vyapti_iff paksadharmata_def)

theorem vyapti_gives_vyatireka: "vyapti \<Longrightarrow> vyatireka"
  by (auto simp: vyapti_iff vyatireka_def vipaksa_def)

theorem vyapti_gives_verdict:
  "vyapti \<Longrightarrow> anvaya \<Longrightarrow> wheel_verdict = Valid"
  by (simp add: wheel_valid_iff vyapti_gives_vyatireka)

end

text \<open>The marks without pervasion: the smoking mountain without fire.\<close>

interpretation nofire_dk: dharmakirti Mountain "\<lambda>l. l = Kitchen" "\<lambda>l. l \<noteq> Lake" False
  by unfold_locales (simp add: locus_all)

text \<open>
  (The \<open>anumana\<close> part of this interpretation coincides with \<open>nofire\<close> from
  \<open>Dignaga_Hetucakra\<close>, so its marks are \<open>nofire.trairupya\<close>; the pervasion parameter
  is the constant \<open>False\<close>, and the theorem spells out why it must be.)
\<close>

theorem marks_without_vyapti:
  "nofire.trairupya \<and> \<not> (\<forall>x. x \<noteq> Lake \<longrightarrow> x = Kitchen)"
  using no_deductive_soundness by (auto intro: exI[of _ Mountain])

subsection \<open>The identity reason: pervasion by inclusion\<close>

locale svabhavahetu = dharmakirti +
  assumes inclusion: "H x \<Longrightarrow> S x"   \<comment> \<open>the reason-property is contained in the sadhya-property\<close>
begin

theorem svabhavahetu_vyapti: "vyapti"
  by (simp add: vyapti_iff inclusion)

theorem svabhavahetu_sound: "paksadharmata \<Longrightarrow> S paksa"
  using svabhavahetu_vyapti vyapti_sound by blast

end

text \<open>
  Simsapa and tree: the subject is one simsapa, a second simsapa is the
  similar instance that carries the reason, the oak is a similar instance
  without it, grass is the dissimilar instance. Cell 8, valid, and the
  pervasion is the inclusion "every simsapa is a tree".
\<close>

datatype plant = Simsapa1 | Simsapa2 | Oak | Grass

lemma plant_all: "(\<forall>x :: plant. P x) \<longleftrightarrow> P Simsapa1 \<and> P Simsapa2 \<and> P Oak \<and> P Grass"
  by (metis plant.exhaust)

lemma plant_ex: "(\<exists>x :: plant. P x) \<longleftrightarrow> P Simsapa1 \<or> P Simsapa2 \<or> P Oak \<or> P Grass"
  by (metis plant.exhaust)

interpretation simsapa: svabhavahetu Simsapa1 "\<lambda>x. x \<noteq> Grass" "\<lambda>x. x = Simsapa1 \<or> x = Simsapa2" True
  by unfold_locales (auto simp: plant_all)

lemma plant_ne_grass: "x = Simsapa1 \<or> x = Simsapa2 \<Longrightarrow> x \<noteq> Grass"
  by (erule disjE) simp_all

theorem simsapa_tree: "simsapa.wheel_verdict = Valid \<and> (\<lambda>x. x \<noteq> Grass) Simsapa1"
  unfolding simsapa.wheel_valid_iff simsapa.anvaya_def simsapa.vyatireka_def
            simsapa.sapaksa_def simsapa.vipaksa_def
  by (simp add: Ball_def Bex_def plant_all plant_ex plant_ne_grass)

subsection \<open>The effect reason: pervasion is a causal law\<close>

text \<open>
  The effect reason is sound exactly when the causal law "no effect
  without its cause" holds over the loci. The law is what Dharmakirti's
  five-step procedure (\<open>pancakarani\<close>) is meant to establish empirically;
  formally it is the pervasion premise and nothing less.
\<close>

locale karyahetu = anumana paksa S H
  for paksa :: 'l and S H :: "'l \<Rightarrow> bool" +
  fixes causal_law :: bool
  assumes causal_law_iff: "causal_law \<longleftrightarrow> (\<forall>x. H x \<longrightarrow> S x)"   \<comment> \<open>wherever the effect, the cause\<close>
begin

theorem karyahetu_sound: "causal_law \<Longrightarrow> paksadharmata \<Longrightarrow> S paksa"
  by (simp add: causal_law_iff paksadharmata_def)

end

text \<open>
  Without the law: the \<open>nofire\<close> situation again -- smoke-like mist on the
  mountain, all three marks satisfied by the kitchen and the lake, no fire.
\<close>

interpretation mist: karyahetu Mountain "\<lambda>l. l = Kitchen" "\<lambda>l. l \<noteq> Lake" False
  by unfold_locales (simp add: locus_all)

theorem karyahetu_needs_causal_law:
  "nofire.trairupya \<and> \<not> (\<forall>x. x \<noteq> Lake \<longrightarrow> x = Kitchen) \<and> \<not> (\<lambda>l. l = Kitchen) Mountain"
  using no_deductive_soundness by (auto intro: exI[of _ Mountain])

subsection \<open>The non-perception reason: perceptibility is the premise\<close>

locale anupalabdhi =
  fixes present perceived perceptible :: "'o \<Rightarrow> bool"
  assumes visibility: "present x \<Longrightarrow> perceptible x \<Longrightarrow> perceived x"
begin

theorem drsyanupalabdhi_sound: "perceptible x \<Longrightarrow> \<not> perceived x \<Longrightarrow> \<not> present x"
  using visibility by blast

end

datatype thing_here = Pot | Ghost

lemma thing_here_all: "(\<forall>x :: thing_here. P x) \<longleftrightarrow> P Pot \<and> P Ghost"
  by (metis thing_here.exhaust)

text \<open>The pot is perceptible and unperceived, hence absent; the ghost is present, imperceptible, unperceived.\<close>

interpretation here: anupalabdhi "\<lambda>x. x = Ghost" "\<lambda>_. False" "\<lambda>x. x = Pot"
  by unfold_locales simp

theorem anupalabdhi_needs_perceptibility:
  "\<not> (\<lambda>x. x = Ghost) Pot \<and> (\<lambda>x. x = Ghost) Ghost \<and> \<not> (\<lambda>_. False) Ghost"
  by simp

end
