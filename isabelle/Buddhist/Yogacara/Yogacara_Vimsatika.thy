(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Vasubandhu's Vimsatika: an adequacy proof and an atomism dilemma\<close>

theory Yogacara_Vimsatika
  imports Main
begin

text \<open>
  The \<open>Vimsatika\<close> ("Twenty Verses") defends \<open>vijnaptimatra\<close>, the thesis
  that what is given is appearance without an external object. Verses 2 and
  3 state the objection in the form of four conditions that any such theory
  must meet, and the rest of the text answers them:

  \<^enum> \<open>desaniyama\<close> -- why is the appearance restricted to a place?
  \<^enum> \<open>kalaniyama\<close> -- why restricted to a time?
  \<^enum> \<open>samtana-aniyama\<close> -- why is it \<^emph>\<open>not\<close> restricted to one continuum, that
    is, why do several people see the same thing?
  \<^enum> \<open>krtyakriya\<close> -- why does it do the work an object would do?

  Vasubandhu's answer is by example: dreams meet the first, second and
  fourth, and the hell-guards -- seen alike by all the beings whose
  collective karma projects them -- meet the third as well.

  What can be established formally is exactly what Vasubandhu claims and no
  more: the four conditions are \<^emph>\<open>jointly satisfiable\<close> by a structure in
  which nothing but appearance is posited. That is a consistency result, not
  an argument that there are no external objects; the verses are answering
  an objection, not proving a thesis, and the formalization keeps to that.

  The second half formalizes verses 12 to 14, the refutation of atomism,
  which is an argument rather than an example and so has more content. If
  an atom is partless then it can only be touched as a whole, and then a
  cluster of atoms in contact occupies one place and has no extension; if
  the cluster has extension then the atoms are touched side by side and so
  have sides, that is, parts. Both horns are theorems below.
\<close>


subsection \<open>The four conditions, and models that meet them\<close>

locale vijnapti =
  fixes appears   :: "'s \<Rightarrow> 'p \<Rightarrow> 't \<Rightarrow> bool"   \<comment> \<open>subject, place, time\<close>
    and effective :: "'s \<Rightarrow> 'p \<Rightarrow> 't \<Rightarrow> bool"   \<comment> \<open>the appearance does the object's work\<close>
begin

definition desaniyama :: bool where
  "desaniyama \<longleftrightarrow> (\<forall>s t. (\<exists>p. appears s p t) \<longrightarrow> (\<exists>p'. \<not> appears s p' t))"

definition kalaniyama :: bool where
  "kalaniyama \<longleftrightarrow> (\<forall>s p. (\<exists>t. appears s p t) \<longrightarrow> (\<exists>t'. \<not> appears s p t'))"

definition samtana_aniyama :: bool where
  "samtana_aniyama \<longleftrightarrow> (\<exists>s s' p t. s \<noteq> s' \<and> appears s p t \<and> appears s' p t)"

definition krtyakriya :: bool where
  "krtyakriya \<longleftrightarrow> (\<forall>s p t. appears s p t \<longrightarrow> effective s p t)"

definition adequate :: bool where
  "adequate \<longleftrightarrow> desaniyama \<and> kalaniyama \<and> samtana_aniyama \<and> krtyakriya"

end

datatype person = Alpha | Beta | Gamma
datatype place  = Here | There
datatype moment = Now | Later

definition dream_app :: "person \<Rightarrow> place \<Rightarrow> moment \<Rightarrow> bool" where
  "dream_app s p t \<longleftrightarrow> (s = Alpha \<and> p = Here \<and> t = Now)"

definition naraka_app :: "person \<Rightarrow> place \<Rightarrow> moment \<Rightarrow> bool" where
  "naraka_app s p t \<longleftrightarrow> (p = Here \<and> t = Now)"

interpretation dream: vijnapti dream_app dream_app .
interpretation naraka: vijnapti naraka_app naraka_app .

text \<open>
  The dream meets three of the four conditions and fails the third: what one
  dreams, only the dreamer sees.
\<close>

theorem dream_meets_three:
  "dream.desaniyama" "dream.kalaniyama" "dream.krtyakriya"
  by (auto simp: dream.desaniyama_def dream.kalaniyama_def dream.krtyakriya_def dream_app_def)

theorem dream_lacks_intersubjectivity: "\<not> dream.samtana_aniyama"
  by (auto simp: dream.samtana_aniyama_def dream_app_def)

theorem dream_not_adequate: "\<not> dream.adequate"
  using dream_lacks_intersubjectivity by (simp add: dream.adequate_def)

text \<open>
  The hell-guards -- appearing alike to everyone whose karma projects them --
  meet all four. So the objection of verses 2 and 3 does not refute the
  thesis: there is a structure with appearances, restrictions of place and
  time, shared appearance and efficacy, and no object anywhere in it.
\<close>

theorem naraka_meets_all_four: "naraka.adequate"
proof -
  have "naraka.desaniyama"
    unfolding naraka.desaniyama_def
    by (intro allI impI, rule exI[of _ There]) (simp add: naraka_app_def)
  moreover have "naraka.kalaniyama"
    unfolding naraka.kalaniyama_def
    by (intro allI impI, rule exI[of _ Later]) (simp add: naraka_app_def)
  moreover have "naraka.samtana_aniyama"
    unfolding naraka.samtana_aniyama_def
    by (rule exI[of _ Alpha], rule exI[of _ Beta]) (simp add: naraka_app_def)
  moreover have "naraka.krtyakriya"
    by (simp add: naraka.krtyakriya_def)
  ultimately show ?thesis by (simp add: naraka.adequate_def)
qed

theorem vijnaptimatra_is_consistent_with_the_four_conditions:
  "\<exists>A E :: person \<Rightarrow> place \<Rightarrow> moment \<Rightarrow> bool. vijnapti.adequate A E"
  using naraka_meets_all_four by blast


subsection \<open>Verses 12 to 14: the atom has no sides, so the cluster has no size\<close>

text \<open>
  \<open>pos\<close> is where an atom is; \<open>contact\<close> is the joining relation. To be
  partless is to have no side by which to touch, so contact can only be
  whole to whole -- which is to say, in the same place.
\<close>

definition partless_contact :: "('a \<Rightarrow> 'p) \<Rightarrow> ('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> bool" where
  "partless_contact pos contact \<longleftrightarrow> (\<forall>x y. contact x y \<longrightarrow> pos x = pos y)"

definition has_extension :: "('a \<Rightarrow> 'p) \<Rightarrow> 'a set \<Rightarrow> bool" where
  "has_extension pos S \<longleftrightarrow> (\<exists>x\<in>S. \<exists>y\<in>S. pos x \<noteq> pos y)"

definition clustered :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a set \<Rightarrow> bool" where
  "clustered contact c S \<longleftrightarrow> (\<forall>x\<in>S. contact c x)"

text \<open>
  Verse 12's six directions: an atom joined from all sides by six others.
  If the joining is whole to whole, the seven are in one place.
\<close>

theorem six_directions_collapse:
  assumes "partless_contact pos contact" and "clustered contact c S"
  shows "\<forall>x\<in>S. pos x = pos c"
  using assms by (auto simp: partless_contact_def clustered_def)

theorem atomism_dilemma:
  assumes pl: "partless_contact pos contact" and cl: "clustered contact c S" and cS: "c \<in> S"
  shows "\<not> has_extension pos S"
proof
  assume "has_extension pos S"
  then obtain x y where xy: "x \<in> S" "y \<in> S" "pos x \<noteq> pos y"
    unfolding has_extension_def by blast
  have "\<forall>z\<in>S. pos z = pos c" by (rule six_directions_collapse[OF pl cl])
  with xy show False by auto
qed

text \<open>
  The other horn, stated as its contrapositive: a cluster that has size is a
  cluster whose members are touched somewhere rather than everywhere, and to
  have a somewhere is to have parts.
\<close>

theorem extension_needs_parts:
  assumes "clustered contact c S" and "c \<in> S" and "has_extension pos S"
  shows "\<not> partless_contact pos contact"
proof
  assume "partless_contact pos contact"
  from atomism_dilemma[OF this assms(1) assms(2)] assms(3) show False by simp
qed

text \<open>
  Both horns are occupied, so the dilemma is not vacuous: there are clusters
  of the first kind and clusters of the second.
\<close>

definition two_atoms :: "bool \<Rightarrow> place" where
  "two_atoms b = (if b then Here else There)"

theorem dilemma_horns_are_both_realized:
  "partless_contact (\<lambda>_ :: bool. Here) (\<lambda>_ _. True)"
  "\<not> partless_contact two_atoms (\<lambda>_ _. True)"
  "has_extension two_atoms {True, False}"
  by (auto simp: partless_contact_def has_extension_def two_atoms_def)

end
