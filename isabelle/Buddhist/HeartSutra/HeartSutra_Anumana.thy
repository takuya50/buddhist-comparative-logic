(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>"All dharmas are empty, because dependently arisen": the sutra's negations as an inference\<close>

theory HeartSutra_Anumana
  imports Dignaga_Hetucakra Madhyamaka_MMK24
begin

text \<open>
  The sutra states 是諸法空相 and then negates dharma after dharma. In the
  Madhyamaka of \<open>Madhyamaka_MMK24\<close> the ground is dependent arising. Read as a
  Dignaga-style inference: thesis "\<open>x\<close> is empty", reason "\<open>x\<close> is
  dependently arisen", loci = the dharmas. Two facts follow.

  \<^item> Inside the Madhyamaka locale every dharma is empty, so the dissimilar
    class (\<open>vipaksa\<close>) is empty and the third mark holds vacuously; the
    reason is present in every similar instance; the wheel's verdict is
    Valid (cell 2). The uniformity premise that \<open>Dignaga_Hetucakra\<close> showed to be
    necessary for soundness is trivially available, because the thesis is
    universal. This is the shape of Bhavaviveka's independent inference
    (\<open>svatantranumana\<close>) for emptiness.
  \<^item> Against an opponent who admits unconditioned dharmas with own-being
    (the Sarvastivada \<open>asamskrta\<close>: space, cessation), the inference still
    comes out Valid provided the opponent grants one agreed example that
    is both empty and arisen -- the magical illusion (\<open>maya\<close>) of the
    Prajnaparamita similes. Withdraw the agreed example and the same
    reason becomes \<^emph>\<open>contradictory\<close> (cell 4/6), because the illusion now
    counts as a dissimilar instance in which the reason is present. That
    is the formal content of the Prasangika objection that an independent
    inference for emptiness needs premises the opponent shares.
\<close>

subsection \<open>Inside the Madhyamaka locale\<close>

context madhyamaka
begin

definition H_arisen :: "dharma \<Rightarrow> bool" where "H_arisen d \<longleftrightarrow> arisen d \<in> D"

lemma H_all: "H_arisen d"
  unfolding H_arisen_def by (rule mmk_24_19)

lemma vipaksa_empty: "anumana.vipaksa x empty_of = {}"
  unfolding anumana.vipaksa_def using sarva_dharma_sunya by auto

lemma sapaksa_all: "anumana.sapaksa x empty_of = UNIV - {x}"
  unfolding anumana.sapaksa_def using sarva_dharma_sunya by auto

lemma another_dharma: "\<exists>y. y \<noteq> (x :: dharma)"
  by (cases x) (auto intro: exI[of _ "Sk rupa"] exI[of _ "Sk vedana"])

theorem sunyata_anumana_valid: "anumana.wheel_verdict x empty_of H_arisen = Valid"
  unfolding anumana.wheel_valid_iff anumana.anvaya_def anumana.vyatireka_def
            sapaksa_all vipaksa_empty
  using H_all another_dharma[of x] by auto

theorem uniformity_trivial:
  "(\<forall>y. y \<noteq> x \<longrightarrow> H_arisen y \<longrightarrow> empty_of y) \<Longrightarrow> H_arisen x \<longrightarrow> empty_of x"
  using sarva_dharma_sunya by blast

end

subsection \<open>Against the Sarvastivada: the agreed example decides\<close>

datatype adharma = Samskrta | Maya | Asamskrta   \<comment> \<open>conditioned things, the illusion, the unconditioned\<close>

lemma adharma_all: "(\<forall>d :: adharma. P d) \<longleftrightarrow> P Samskrta \<and> P Maya \<and> P Asamskrta"
  by (metis adharma.exhaust)

lemma adharma_ex: "(\<exists>d :: adharma. P d) \<longleftrightarrow> P Samskrta \<or> P Maya \<or> P Asamskrta"
  by (metis adharma.exhaust)

text \<open>
  Bhavaviveka: subject = conditioned things; sadhya "empty" holds of the
  subject (the thesis) and of the illusion, not of the unconditioned;
  reason "arisen" likewise.
\<close>

interpretation bhavaviveka: anumana Samskrta "\<lambda>d. d \<noteq> Asamskrta" "\<lambda>d. d \<noteq> Asamskrta" .

theorem bhavaviveka_valid: "bhavaviveka.wheel_verdict = Valid"
  unfolding bhavaviveka.wheel_valid_iff bhavaviveka.anvaya_def bhavaviveka.vyatireka_def
            bhavaviveka.sapaksa_def bhavaviveka.vipaksa_def
  by (simp add: Ball_def Bex_def adharma_all adharma_ex)

text \<open>
  The same reason with the illusion withdrawn from the class of the empty
  (the opponent grants no example): the illusion is now a dissimilar
  instance in which the reason is present, and the reason is contradictory.
\<close>

interpretation no_example: anumana Samskrta "\<lambda>d. d = Samskrta" "\<lambda>d. d \<noteq> Asamskrta" .

theorem no_agreed_example_contradictory: "no_example.wheel_verdict = Contradictory"
  unfolding no_example.wheel_contradictory_iff no_example.sapaksa_def no_example.vipaksa_def
  by (simp add: Ball_def Bex_def adharma_all adharma_ex)

end
