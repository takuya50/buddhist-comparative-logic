(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The mantra and its epithets: what is deliberately not formalized as a proposition\<close>

theory HeartSutra_Mantra
  imports FiniteLogics HeartSutra_Dharma
begin

text \<open>
  HS25-29 do not make a claim of the form the earlier layers handle. HS25
  praises \<open>prajnaparamita\<close> under four epithets; HS28-29 introduce and then
  utter a mantra; HS27 asserts (of the mantra? of the whole sutra?) that it
  is "true, not false". An invocation such as \<open>gate gate paragate
  parasamgate bodhi svaha\<close> is not a declarative sentence and so is not a
  candidate for a truth value in any of the logics of \<open>FiniteLogics\<close>.
  We record this explicitly, as a theorem about the datatype of utterances,
  rather than silently omitting these clauses.
\<close>

datatype mantra_word = gate | paragate | parasamgate | bodhi_w | svaha

definition heart_mantra :: "mantra_word list" where
  "heart_mantra = [gate, gate, paragate, parasamgate, bodhi_w, svaha]"

lemma heart_mantra_shape:
  "length heart_mantra = 6 \<and> hd heart_mantra = gate \<and> last heart_mantra = svaha"
  by (simp add: heart_mantra_def)

datatype epithet = MahaMantra | MahaVidyaMantra | AnuttaraMantra | AsamasamaMantra

definition epithets :: "epithet list" where
  "epithets = [MahaMantra, MahaVidyaMantra, AnuttaraMantra, AsamasamaMantra]"

lemma epithets_univ: "set epithets = UNIV \<and> distinct epithets"
proof
  show "set epithets = UNIV"
  proof (rule set_eqI)
    fix x show "x \<in> set epithets \<longleftrightarrow> x \<in> UNIV" by (cases x) (simp_all add: epithets_def)
  qed
qed (simp add: epithets_def)

lemma epithets_four: "card (UNIV :: epithet set) = 4"
  using card_of_list[OF epithets_univ[THEN conjunct1] epithets_univ[THEN conjunct2]]
  by (simp add: epithets_def eval_nat_numeral)

datatype 'a utterance =
    Assert "'a fm"
  | Invoke "mantra_word list"

fun truth_apt :: "'a utterance \<Rightarrow> bool" where
  "truth_apt (Assert _) = True"
| "truth_apt (Invoke _) = False"

text \<open>
  The explicit non-formalizability lemma for HS27/HS28/HS29: an invocation
  carries no truth value in any \<^locale>\<open>mv_logic\<close> instance, so
  \<open>truthful \<noteq> provable\<close>. The sutra's endorsement \<open>真實不虛\<close> ("true, not
  false") is a speech act about an invocation, and this development neither
  asserts nor denies it; it is recorded in \<^file>\<open>../../../docs/STATUS.md\<close> with
  status \<open>noted\<close>. The one propositional residue among HS25-29 is HS26
  \<open>能除一切苦\<close> ("able to remove all suffering"), which is discharged in
  \<open>HeartSutra_Path\<close> (\<open>hs04_26\<close>, via \<open>nirvana m \<Longrightarrow> \<not> suffers m\<close>), not here.
\<close>

lemma hs29_mantra_not_truth_apt: "\<not> truth_apt (Invoke heart_mantra :: atom utterance)"
  by simp

end
