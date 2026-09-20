(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Apoha: what exactly is wrong with defining "cow" as the exclusion of non-cows\<close>

theory Dignaga_Apoha
  imports Dignaga_Hetucakra
begin

text \<open>
  Dignaga's \<open>apoha\<close> theory holds that a general term has no positive general
  referent: "cow" means the exclusion of non-cows (\<open>agonivrtti\<close>). Kumarila's
  standard objection is that this is circular -- "non-cow" is fixed only once
  "cow" is -- and Dharmakirti's reply grounds the exclusion in the causal
  efficacy shared by the particulars.

  Formalizing this needs care about which framework applies. The operator
  behind the theory, \<open>M \<mapsto> - M\<close>, is \<^emph>\<open>antitone\<close>, so the Knaster-Tarski
  machinery of least and greatest fixed points does not apply to it at all;
  reaching for \<open>lfp\<close> here would be a mistake. The framework that does apply
  is the one built for circular definitions: Gupta and Belnap's revision
  theory, where a definition is judged by whether its revision sequence
  settles.

  Three results, and they separate the objection into parts that are true
  and parts that are not.

  \<^item> The single equation "cow is the exclusion of cow" has \<^emph>\<open>no\<close> solution
    (\<open>apoha_no_fixpoint\<close>), and its revision sequence oscillates with period
    two and never settles (\<open>revision_oscillates\<close>,
    \<open>revision_never_stabilises\<close>). This much of the circularity charge is
    exactly right, and it is the vicious case in Gupta and Belnap's sense.

  \<^item> The two-term system "cow is the exclusion of non-cow, non-cow is the
    exclusion of cow" is \<^emph>\<open>not\<close> contradictory: every set solves it
    (\<open>apoha_pair_underdetermined\<close>), and the system's whole content is that
    the second term is the complement of the first
    (\<open>apoha_pair_no_constraint\<close>). So the objection's correct form is not
    "there is no meaning" but "the theory does not determine which meaning",
    which is a weaker and more interesting charge.

  \<^item> Dharmakirti's causal grounding answers exactly that weaker charge. If
    the shared effect is an equivalence relation, one particular fixes the
    whole extension (\<open>causal_grounding_unique\<close>); mere similarity, which is
    reflexive and symmetric but not transitive, does not
    (\<open>grounding_needs_transitivity\<close>). Grounding does not dissolve the
    circle -- the grounded extension is still one of the many solutions
    (\<open>grounding_selects_a_solution\<close>) -- it selects within it.

  The last section connects this to \<^theory>\<open>Buddhist_Comparative_Logic.Dignaga_Hetucakra\<close>: the
  similar and dissimilar classes of Dignaga's own inference schema are an
  apoha pair off the subject, and leaving the exclusion unfixed leaves the
  wheel's verdict unfixed too.

  What is formalized here is the \<^emph>\<open>double-negation\<close> reading of apoha, which
  is the reading Kumarila's circularity objection attacks. Katsura and
  others argue that Dignaga did not intend double negation at all, but a
  componential analysis in which "cow" excludes what lacks dewlap, horns
  and the rest; on that reading the objection does not arise in this form,
  and nothing below applies to it. So these results bear on the objection
  and its standard target, not on Dignaga's considered position.
\<close>


subsection \<open>The single equation has no solution\<close>

theorem apoha_no_fixpoint: "(M :: 'i set) \<noteq> - M"
proof
  assume "M = - M"
  then have "\<forall>x. x \<in> M \<longleftrightarrow> x \<notin> M" by auto
  then show False by blast
qed


subsection \<open>The two-term system has too many\<close>

definition apoha_pair :: "'i set \<Rightarrow> 'i set \<Rightarrow> bool" where
  "apoha_pair M N \<longleftrightarrow> M = - N \<and> N = - M"

theorem apoha_pair_underdetermined: "apoha_pair S (- S)"
  by (simp add: apoha_pair_def)

theorem apoha_pair_no_constraint: "apoha_pair M N \<longleftrightarrow> N = - M"
  by (auto simp: apoha_pair_def)

text \<open>
  Two readings of the same doctrine, then, with opposite verdicts: taken as
  one equation it is unsatisfiable, taken as two it is satisfied by
  everything. Neither reading gives a meaning.
\<close>

theorem circularity_is_underdetermination:
  "\<not> (\<exists>M :: 'i set. M = - M)"
  "\<forall>S :: 'i set. \<exists>N. apoha_pair S N"
  using apoha_no_fixpoint by (auto simp: apoha_pair_def)


subsection \<open>Revision: the definition does not settle\<close>

text \<open>
  Gupta and Belnap evaluate a circular definition by iterating it from an
  arbitrary starting hypothesis. Here the iteration has period two, so no
  hypothesis is stable and no set is a categorical outcome.
\<close>

fun rev_seq :: "'i set \<Rightarrow> nat \<Rightarrow> 'i set" where
  "rev_seq S 0 = S"
| "rev_seq S (Suc n) = - (rev_seq S n)"

theorem revision_oscillates: "rev_seq S (Suc (Suc n)) = rev_seq S n"
  by simp

theorem revision_never_stabilises: "rev_seq S (Suc n) \<noteq> rev_seq S n"
  using apoha_no_fixpoint by (metis rev_seq.simps(2))

theorem revision_has_no_stable_set: "\<not> (\<exists>n. rev_seq S (Suc n) = rev_seq S n)"
  using revision_never_stabilises by blast


subsection \<open>Dharmakirti: grounding the exclusion in a shared effect\<close>

locale apoha_grounded =
  fixes same_effect :: "'i \<Rightarrow> 'i \<Rightarrow> bool"   \<comment> \<open>\<open>ekapratyavamarsa\<close>: same practical effect\<close>
  assumes se_refl:  "same_effect x x"
      and se_sym:   "same_effect x y \<Longrightarrow> same_effect y x"
      and se_trans: "same_effect x y \<Longrightarrow> same_effect y z \<Longrightarrow> same_effect x z"
begin

definition cls :: "'i \<Rightarrow> 'i set" where
  "cls x = {y. same_effect x y}"

definition grounded :: "'i set \<Rightarrow> bool" where
  "grounded M \<longleftrightarrow> (\<exists>x. M = cls x)"

lemma mem_cls_self: "x \<in> cls x"
  by (simp add: cls_def se_refl)

lemma cls_eq: "same_effect x y \<Longrightarrow> cls x = cls y"
  unfolding cls_def using se_sym se_trans by blast

theorem causal_grounding_unique:
  assumes "grounded M" and "grounded N" and "x \<in> M" and "x \<in> N"
  shows "M = N"
proof -
  from assms obtain a b where M: "M = cls a" and N: "N = cls b"
    unfolding grounded_def by blast
  from assms M N have "same_effect a x" and "same_effect b x"
    by (simp_all add: cls_def)
  then have "same_effect a b" using se_sym se_trans by blast
  then show ?thesis using M N cls_eq by simp
qed

text \<open>
  Grounding does not remove the circle: the grounded extension and its
  exclusion are still a solution of the two-term system, just a selected
  one.
\<close>

theorem grounding_selects_a_solution: "grounded M \<Longrightarrow> apoha_pair M (- M)"
  by (simp add: apoha_pair_def)

end

interpretation identity_effect: apoha_grounded "(=) :: 'i \<Rightarrow> 'i \<Rightarrow> bool"
  by unfold_locales auto

interpretation parity_effect: apoha_grounded "\<lambda>m n :: nat. m mod 2 = n mod 2"
  by unfold_locales auto

text \<open>
  Transitivity is what does the work. Bare similarity -- reflexive,
  symmetric, not transitive -- is the relation the Buddhist epistemologists
  actually had available before the appeal to causal efficacy, and it does
  not fix an extension: two similarity classes can share a member and still
  differ.
\<close>

definition close :: "nat \<Rightarrow> nat \<Rightarrow> bool" where
  "close m n \<longleftrightarrow> (m \<le> n \<and> n \<le> m + 1) \<or> (n \<le> m \<and> m \<le> n + 1)"

definition ccls :: "nat \<Rightarrow> nat set" where
  "ccls x = {y. close x y}"

theorem grounding_needs_transitivity:
  "close x x"
  "close x y \<Longrightarrow> close y x"
  "\<not> (\<forall>x y z. close x y \<longrightarrow> close y z \<longrightarrow> close x z)"
  "1 \<in> ccls 0 \<and> 1 \<in> ccls 1 \<and> ccls 0 \<noteq> ccls 1"
proof -
  show "close x x" by (simp add: close_def)
  show "close x y \<Longrightarrow> close y x" by (auto simp: close_def)
  show "\<not> (\<forall>x y z. close x y \<longrightarrow> close y z \<longrightarrow> close x z)"
  proof
    assume *: "\<forall>x y z. close x y \<longrightarrow> close y z \<longrightarrow> close x z"
    have c01: "close 0 1" by (simp add: close_def)
    have c12: "close 1 2" by (simp add: close_def)
    from *[rule_format, OF c01 c12] show False by (simp add: close_def)
  qed
  show "1 \<in> ccls 0 \<and> 1 \<in> ccls 1 \<and> ccls 0 \<noteq> ccls 1"
  proof -
    have "(2 :: nat) \<in> ccls 1" by (simp add: ccls_def close_def)
    moreover have "(2 :: nat) \<notin> ccls 0" by (simp add: ccls_def close_def)
    ultimately show ?thesis by (auto simp: ccls_def close_def)
  qed
qed


subsection \<open>The similar and dissimilar classes are an apoha pair\<close>

text \<open>
  Dignaga's inference schema already runs on an exclusion. Off the subject
  of the inference, the dissimilar class is the complement of the similar
  class, so the two are related exactly as the apoha pair is.
\<close>

context anumana
begin

theorem vipaksa_is_apoha_of_sapaksa:
  "vipaksa = - sapaksa - {paksa}"
  by (auto simp: vipaksa_def sapaksa_def)

theorem sapaksa_vipaksa_partition:
  "sapaksa \<union> vipaksa = - {paksa}"
  "sapaksa \<inter> vipaksa = {}"
  by (auto simp: vipaksa_def sapaksa_def)

end

text \<open>
  And leaving the exclusion unfixed leaves the inference unfixed: with the
  same subject and the same reason, two choices of the property to be
  proved give opposite verdicts. So the wheel presupposes that something
  outside it has already fixed the classes -- which is the work
  \<open>causal_grounding_unique\<close> does.
\<close>

theorem apoha_underdetermines_the_wheel:
  "anumana.wheel_verdict (0 :: nat) (\<lambda>_. True) (\<lambda>x. x = 2) = Valid"
  "anumana.wheel_verdict (0 :: nat) (\<lambda>_. False) (\<lambda>x. x = 2) = Contradictory"
  unfolding anumana.wheel_verdict_def anumana.sapaksa_def anumana.vipaksa_def
            anumana.extent_of_def
  by auto

end
