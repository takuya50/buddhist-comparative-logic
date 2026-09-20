(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Dignaga's hetucakra: the wheel of reasons, and what the three marks do and do not prove\<close>

theory Dignaga_Hetucakra
  imports Main
begin

text \<open>
  This theory is independent of the Heart Sutra; it lives in the same
  session because it covers the \<^emph>\<open>inferential\<close> side of Buddhist logic
  (\<open>hetuvidya\<close>, 因明) that the sutra's negations presuppose. Dignaga's
  \<^emph>\<open>Hetucakra\<close> classifies a reason (\<open>hetu\<close>, 因) for a thesis "the subject
  (\<open>paksa\<close>, 宗) has the property to be proved (\<open>sadhya\<close>)" by where the
  reason occurs among the other loci: in the similar instances (\<open>sapaksa\<close>,
  同品 -- loci that have the sadhya) and the dissimilar instances
  (\<open>vipaksa\<close>, 異品 -- loci that lack it). Each class admits three extents,
  present in all (有), in none (非有), or in some (倶), giving nine cells
  (九句因). Two are valid reasons (正因: cells 2 and 8), two are
  contradictory (相違因: cells 4 and 6), five are inconclusive (不定因).

  The three marks of a good reason (\<open>trairupya\<close>, 因三相) are: presence in
  the subject (遍是宗法性), presence in some similar instance (同品定有性),
  absence from every dissimilar instance (異品遍無性). We formalize the
  wheel, prove that its "valid" cells are exactly the reasons satisfying
  the second and third marks, and then prove a point often blurred in
  informal presentations: the three marks are \<^emph>\<open>not\<close> deductively sufficient
  for the thesis. Absence from the dissimilar instances gives pervasion of
  the reason by the sadhya \<^emph>\<open>off the subject\<close>; extending it to the subject
  needs a uniformity assumption, which is stated explicitly.
\<close>

subsection \<open>The wheel as a table\<close>

datatype extent = Ext_all | Ext_none | Ext_some       \<comment> \<open>有 / 非有 / 倶\<close>
datatype verdict = Valid | Contradictory | Inconclusive \<comment> \<open>正因 / 相違因 / 不定因\<close>

fun hetucakra :: "extent \<Rightarrow> extent \<Rightarrow> verdict" where  \<comment> \<open>sapaksa extent, vipaksa extent\<close>
  "hetucakra Ext_all  Ext_none = Valid"
| "hetucakra Ext_some Ext_none = Valid"
| "hetucakra Ext_none Ext_all  = Contradictory"
| "hetucakra Ext_none Ext_some = Contradictory"
| "hetucakra _ _ = Inconclusive"

definition wheel :: "(extent \<times> extent) list" where
  "wheel = concat (map (\<lambda>s. map (\<lambda>v. (s, v)) [Ext_all, Ext_none, Ext_some]) [Ext_all, Ext_none, Ext_some])"

lemma wheel_nine: "length wheel = 9" and wheel_distinct: "distinct wheel"
  by (simp_all add: wheel_def)

text \<open>Cells 1-9 in Dignaga's order (rows: sapaksa 有/非有/倶; columns: vipaksa 有/非有/倶).\<close>

lemma wheel_verdicts:
  "map (\<lambda>(s, v). hetucakra s v) wheel =
     [Inconclusive, Valid, Inconclusive,
      Contradictory, Inconclusive, Contradictory,
      Inconclusive, Valid, Inconclusive]"
  by (simp add: wheel_def)

lemma valid_iff: "hetucakra s v = Valid \<longleftrightarrow> v = Ext_none \<and> s \<noteq> Ext_none"
  by (cases s; cases v) simp_all

lemma contradictory_iff: "hetucakra s v = Contradictory \<longleftrightarrow> s = Ext_none \<and> v \<noteq> Ext_none"
  by (cases s; cases v) simp_all

subsection \<open>Semantics: subject, sadhya, hetu over a domain of loci\<close>

locale anumana =
  fixes paksa :: 'l
    and S :: "'l \<Rightarrow> bool"   \<comment> \<open>sadhya: the property to be proved\<close>
    and H :: "'l \<Rightarrow> bool"   \<comment> \<open>hetu: the reason\<close>
begin

definition sapaksa :: "'l set" where "sapaksa = {x. x \<noteq> paksa \<and> S x}"
definition vipaksa :: "'l set" where "vipaksa = {x. x \<noteq> paksa \<and> \<not> S x}"

definition extent_of :: "'l set \<Rightarrow> extent" where
  "extent_of L = (if \<forall>x\<in>L. \<not> H x then Ext_none else if \<forall>x\<in>L. H x then Ext_all else Ext_some)"

definition wheel_verdict :: verdict where
  "wheel_verdict = hetucakra (extent_of sapaksa) (extent_of vipaksa)"

text \<open>The three marks.\<close>

definition paksadharmata :: bool where "paksadharmata \<longleftrightarrow> H paksa"
definition anvaya        :: bool where "anvaya \<longleftrightarrow> (\<exists>x\<in>sapaksa. H x)"
definition vyatireka     :: bool where "vyatireka \<longleftrightarrow> (\<forall>x\<in>vipaksa. \<not> H x)"
definition trairupya     :: bool where "trairupya \<longleftrightarrow> paksadharmata \<and> anvaya \<and> vyatireka"

lemma extent_none_iff: "extent_of L = Ext_none \<longleftrightarrow> (\<forall>x\<in>L. \<not> H x)"
  by (simp add: extent_of_def)

theorem wheel_valid_iff: "wheel_verdict = Valid \<longleftrightarrow> anvaya \<and> vyatireka"
  unfolding wheel_verdict_def valid_iff extent_none_iff anvaya_def vyatireka_def by auto

theorem wheel_contradictory_iff:
  "wheel_verdict = Contradictory \<longleftrightarrow> (\<forall>x\<in>sapaksa. \<not> H x) \<and> (\<exists>x\<in>vipaksa. H x)"
  unfolding wheel_verdict_def contradictory_iff extent_none_iff by auto

text \<open>
  What the marks give: pervasion of the reason by the sadhya away from the
  subject (from the third mark), and, for a contradictory reason, pervasion
  by the sadhya's absence.
\<close>

theorem vyatireka_gives_vyapti_off_paksa:
  "vyatireka \<Longrightarrow> \<forall>x. x \<noteq> paksa \<longrightarrow> H x \<longrightarrow> S x"
  by (auto simp: vyatireka_def vipaksa_def)

theorem contradictory_indicates_absence:
  "wheel_verdict = Contradictory \<Longrightarrow> \<forall>x. x \<noteq> paksa \<longrightarrow> H x \<longrightarrow> \<not> S x"
  by (auto simp: wheel_contradictory_iff sapaksa_def)

text \<open>
  What the marks do not give: the thesis itself. Soundness needs the
  explicit uniformity premise that the subject is no exception to the
  pervasion observed everywhere else.
\<close>

theorem sound_under_uniformity:
  assumes "trairupya"
      and uniformity: "(\<forall>x. x \<noteq> paksa \<longrightarrow> H x \<longrightarrow> S x) \<Longrightarrow> H paksa \<longrightarrow> S paksa"
  shows "S paksa"
  using assms vyatireka_gives_vyapti_off_paksa
  unfolding trairupya_def paksadharmata_def by blast

text \<open>
  Under the three marks, this particular uniformity condition is equivalent
  to the disputed thesis. It is therefore an explicit bridge condition, not
  independent support for the thesis.
\<close>

theorem uniformity_iff_thesis_under_marks:
  assumes "trairupya"
  shows "(((\<forall>x. x \<noteq> paksa \<longrightarrow> H x \<longrightarrow> S x) \<longrightarrow>
             H paksa \<longrightarrow> S paksa) \<longleftrightarrow> S paksa)"
  using assms vyatireka_gives_vyapti_off_paksa
  unfolding trairupya_def paksadharmata_def by blast

end

subsection \<open>Examples, and the non-deductive character of the wheel\<close>

datatype locus = Mountain | Kitchen | Lake

lemma locus_all: "(\<forall>l :: locus. P l) \<longleftrightarrow> P Mountain \<and> P Kitchen \<and> P Lake"
  by (metis locus.exhaust)

lemma locus_ex: "(\<exists>l :: locus. P l) \<longleftrightarrow> P Mountain \<or> P Kitchen \<or> P Lake"
  by (metis locus.exhaust)

text \<open>
  The stock example: "the mountain has fire, because it has smoke". Fire is
  in the kitchen and not at the lake; smoke likewise. Cell 2 (or 8), valid.
\<close>

interpretation smoke: anumana Mountain "\<lambda>l. l \<noteq> Lake" "\<lambda>l. l \<noteq> Lake" .

lemma smoke_valid: "smoke.wheel_verdict = Valid"
  unfolding smoke.wheel_valid_iff smoke.anvaya_def smoke.vyatireka_def
            smoke.sapaksa_def smoke.vipaksa_def
  by (simp add: Ball_def Bex_def locus_all locus_ex)

text \<open>
  The same reason with a different hidden truth: the mountain has smoke but
  \<^emph>\<open>no\<close> fire. The wheel still says Valid -- every mark holds, since the
  marks never look at the subject's sadhya -- and the thesis is false. This
  is the precise sense in which Dignaga's inference is not deductive.
\<close>

interpretation nofire: anumana Mountain "\<lambda>l. l = Kitchen" "\<lambda>l. l \<noteq> Lake" .

theorem no_deductive_soundness:
  "nofire.trairupya \<and> nofire.wheel_verdict = Valid \<and> \<not> (\<lambda>l. l = Kitchen) Mountain"
  unfolding nofire.trairupya_def nofire.paksadharmata_def nofire.wheel_valid_iff
            nofire.anvaya_def nofire.vyatireka_def nofire.sapaksa_def nofire.vipaksa_def
  by (simp add: Ball_def Bex_def locus_all locus_ex)

text \<open>
  The classic inconclusive reason (cell 5, 不共不定): "sound is eternal,
  because it is audible". Audibility occurs neither in the eternal
  (space) nor in the non-eternal (pot) instances.
\<close>

datatype thing = Sound | Space | Pot

lemma thing_all: "(\<forall>t :: thing. P t) \<longleftrightarrow> P Sound \<and> P Space \<and> P Pot"
  by (metis thing.exhaust)

lemma thing_ex: "(\<exists>t :: thing. P t) \<longleftrightarrow> P Sound \<or> P Space \<or> P Pot"
  by (metis thing.exhaust)

interpretation audible: anumana Sound "\<lambda>t. t = Space" "\<lambda>t. t = Sound" .

lemma audible_inconclusive: "audible.wheel_verdict = Inconclusive"
  unfolding audible.wheel_verdict_def audible.extent_of_def audible.sapaksa_def audible.vipaksa_def
  by (simp add: Ball_def locus_all thing_all)

end
