(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Dharma-structure layer: skandhas, ayatanas, dhatus, nidanas, truths\<close>

theory HeartSutra_Dharma
  imports Main
begin

text \<open>
  This theory fixes the standard Abhidharma enumerations whose own-being
  HS03, HS08, and HS11-HS17 deny. It is purely structural: no claim about
  emptiness is made here, only that the standard counts (5 skandhas, 12
  ayatanas, 18 dhatus, 12 nidana links, 4 truths) hold of the types as
  defined, and that the two elisions marked \<open>elided\<close> in \<open>HeartSutra_Text\<close>
  (HS14's \<open>dhatu\<close> list, HS16's cessation chain) really do abbreviate an
  exhaustive, ordered enumeration with the stated first and last member.

  Each finite type comes with an explicit enumeration list and a lemma
  that the list is exhaustive and duplicate-free; cardinalities follow
  from \<open>card_of_list\<close>. (Explicit lists are used instead of the \<open>enum\<close>
  type class to keep every fact here elementary.)
\<close>

lemma card_of_list:
  fixes xs :: "'a list"
  assumes "set xs = UNIV" and "distinct xs"
  shows "card (UNIV :: 'a set) = length xs"
proof -
  have "card (UNIV :: 'a set) = card (set xs)" by (simp add: assms(1))
  also have "\<dots> = length xs" using assms(2) by (rule distinct_card)
  finally show ?thesis .
qed

subsection \<open>Five skandhas (HS03, HS08)\<close>

datatype skandha = rupa | vedana | samjna | samskara | vijnana

definition skandhas :: "skandha list" where
  "skandhas = [rupa, vedana, samjna, samskara, vijnana]"

lemma skandhas_univ: "set skandhas = UNIV \<and> distinct skandhas"
proof
  show "set skandhas = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set skandhas \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: skandhas_def)
  qed
qed (simp add: skandhas_def)

lemma card_skandha: "card (UNIV :: skandha set) = 5"
  using card_of_list[OF skandhas_univ[THEN conjunct1] skandhas_univ[THEN conjunct2]]
  by (simp add: skandhas_def eval_nat_numeral)

subsection \<open>Six roots, six objects, twelve ayatanas, eighteen dhatus (HS12-HS14)\<close>

text \<open>\<open>indriya\<close>: the six roots 眼耳鼻舌身意; \<open>visaya\<close>: the six objects 色聲香味觸法.\<close>

datatype indriya = caksus | srotra | ghrana | jihva | kaya | manas
datatype visaya  = rupa_v | sabda | gandha | rasa | sprastavya | dharma_v

definition indriyas :: "indriya list" where
  "indriyas = [caksus, srotra, ghrana, jihva, kaya, manas]"

definition visayas :: "visaya list" where
  "visayas = [rupa_v, sabda, gandha, rasa, sprastavya, dharma_v]"

lemma indriyas_univ: "set indriyas = UNIV \<and> distinct indriyas"
proof
  show "set indriyas = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set indriyas \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: indriyas_def)
  qed
qed (simp add: indriyas_def)

lemma visayas_univ: "set visayas = UNIV \<and> distinct visayas"
proof
  show "set visayas = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set visayas \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: visayas_def)
  qed
qed (simp add: visayas_def)

fun visaya_of :: "indriya \<Rightarrow> visaya" where
  "visaya_of caksus = rupa_v" | "visaya_of srotra = sabda"
| "visaya_of ghrana = gandha" | "visaya_of jihva = rasa"
| "visaya_of kaya = sprastavya" | "visaya_of manas = dharma_v"

lemma visaya_of_bij: "bij visaya_of"
proof (rule bijI)
  show "inj visaya_of"
  proof (rule injI)
    fix x y assume "visaya_of x = visaya_of y"
    then show "x = y" by (cases x; cases y) simp_all
  qed
  show "surj visaya_of"
  proof (rule surjI)
    fix v show "visaya_of (case v of rupa_v \<Rightarrow> caksus | sabda \<Rightarrow> srotra | gandha \<Rightarrow> ghrana
                              | rasa \<Rightarrow> jihva | sprastavya \<Rightarrow> kaya | dharma_v \<Rightarrow> manas) = v"
      by (cases v) simp_all
  qed
qed

text \<open>The twelve \<open>ayatana\<close> (十二處): six roots and six objects.\<close>

datatype ayatana = In indriya | Vi visaya

definition ayatanas :: "ayatana list" where
  "ayatanas = map In indriyas @ map Vi visayas"

lemma ayatanas_univ: "set ayatanas = UNIV \<and> distinct ayatanas"
proof
  show "set ayatanas = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set ayatanas \<longleftrightarrow> x \<in> UNIV"
      using indriyas_univ visayas_univ by (cases x) (simp_all add: ayatanas_def)
  qed
next
  show "distinct ayatanas"
    using indriyas_univ visayas_univ
    by (auto simp: ayatanas_def distinct_map inj_on_def)
qed

lemma card_ayatana: "card (UNIV :: ayatana set) = 12"
  using card_of_list[OF ayatanas_univ[THEN conjunct1] ayatanas_univ[THEN conjunct2]]
  by (simp add: ayatanas_def indriyas_def visayas_def eval_nat_numeral)

datatype dhatu_kind = Root | Object | Consciousness

type_synonym dhatu = "indriya \<times> dhatu_kind"  \<comment> \<open>the eighteen \<open>dhatu\<close> (十八界)\<close>

text \<open>
  The eighteen dhatus in the traditional order: for each of the six roots,
  its root-dhatu, its object-dhatu, then its consciousness-dhatu. This
  makes HS14's elision (無眼界 乃至無意識界, "no eye-realm, ... no
  mind-consciousness-realm") a concrete list whose head and last element
  match the text.
\<close>

definition dhatus :: "dhatu list" where
  "dhatus = concat (map (\<lambda>i. [(i, Root), (i, Object), (i, Consciousness)]) indriyas)"

lemma dhatu_naishi:
  "hd dhatus = (caksus, Root) \<and> last dhatus = (manas, Consciousness)
   \<and> distinct dhatus \<and> set dhatus = UNIV"
proof (intro conjI)
  show "hd dhatus = (caksus, Root)" by (simp add: dhatus_def indriyas_def)
  show "last dhatus = (manas, Consciousness)" by (simp add: dhatus_def indriyas_def)
  show "distinct dhatus" by (simp add: dhatus_def indriyas_def)
  show "set dhatus = UNIV"
  proof (rule set_eqI)
    fix x :: dhatu
    obtain i k where x: "x = (i, k)" by (cases x)
    show "x \<in> set dhatus \<longleftrightarrow> x \<in> UNIV"
      unfolding x by (cases i; cases k) (simp_all add: dhatus_def indriyas_def)
  qed
qed

lemma card_dhatu: "card (UNIV :: dhatu set) = 18"
proof -
  have "set dhatus = UNIV" and "distinct dhatus" using dhatu_naishi by blast+
  from card_of_list[OF this] show ?thesis by (simp add: dhatus_def indriyas_def eval_nat_numeral)
qed

subsection \<open>Twelve links of dependent origination, forward and cessation (HS15-HS16)\<close>

datatype nidana =
  avidya | samskara_n | vijnana_n | namarupa | sadayatana | sparsa
| vedana_n | trsna | upadana | bhava | jati | jaramarana

fun nidana_next :: "nidana \<Rightarrow> nidana option" where
  "nidana_next avidya = Some samskara_n"
| "nidana_next samskara_n = Some vijnana_n"
| "nidana_next vijnana_n = Some namarupa"
| "nidana_next namarupa = Some sadayatana"
| "nidana_next sadayatana = Some sparsa"
| "nidana_next sparsa = Some vedana_n"
| "nidana_next vedana_n = Some trsna"
| "nidana_next trsna = Some upadana"
| "nidana_next upadana = Some bhava"
| "nidana_next bhava = Some jati"
| "nidana_next jati = Some jaramarana"
| "nidana_next jaramarana = None"

definition anuloma :: "nidana list" where     \<comment> \<open>順觀, forward order\<close>
  "anuloma = [avidya, samskara_n, vijnana_n, namarupa, sadayatana, sparsa,
              vedana_n, trsna, upadana, bhava, jati, jaramarana]"

definition pratiloma :: "nidana list" where   \<comment> \<open>reverse order, for the cessation reading\<close>
  "pratiloma = rev anuloma"

lemma anuloma_complete: "set anuloma = UNIV \<and> distinct anuloma \<and> length anuloma = 12"
proof (intro conjI)
  show "set anuloma = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set anuloma \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: anuloma_def)
  qed
qed (simp_all add: anuloma_def eval_nat_numeral)

lemma pratiloma_naishi:
  "hd pratiloma = jaramarana \<and> last pratiloma = avidya
   \<and> set pratiloma = UNIV \<and> distinct pratiloma"
proof (intro conjI)
  show "hd pratiloma = jaramarana" by (simp add: pratiloma_def anuloma_def)
  show "last pratiloma = avidya" by (simp add: pratiloma_def anuloma_def)
  show "set pratiloma = UNIV" using anuloma_complete by (simp add: pratiloma_def)
  show "distinct pratiloma" using anuloma_complete by (simp add: pratiloma_def)
qed

lemma card_nidana: "card (UNIV :: nidana set) = 12"
  using anuloma_complete card_of_list by metis

subsection \<open>Four noble truths (HS17)\<close>

datatype satya = duhkha | samudaya | nirodha | marga

definition satyas :: "satya list" where
  "satyas = [duhkha, samudaya, nirodha, marga]"

lemma satyas_univ: "set satyas = UNIV \<and> distinct satyas"
proof
  show "set satyas = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set satyas \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: satyas_def)
  qed
qed (simp add: satyas_def)

lemma card_satya: "card (UNIV :: satya set) = 4"
  using card_of_list[OF satyas_univ[THEN conjunct1] satyas_univ[THEN conjunct2]]
  by (simp add: satyas_def eval_nat_numeral)

end
