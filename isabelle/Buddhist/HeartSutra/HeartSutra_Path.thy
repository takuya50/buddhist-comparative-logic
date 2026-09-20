(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Path layer: the bodhisattva's and the buddhas' reliance on prajna\<close>

theory HeartSutra_Path
  imports HeartSutra_Emptiness
begin

text \<open>
  HS20-24 state a chain of implications: relying on \<open>prajnaparamita\<close>
  removes hindrance, which removes fear and inverted thinking, which
  culminates in nirvana and the cessation of suffering (HS04, HS26); the
  buddhas of the three times likewise rely on it and thereby attain
  \<open>anuttara-samyak-sambodhi\<close> (HS23-24). We formalize this as a locale
  whose \<^bold>\<open>assumptions are the sutra's own stated implications\<close>: the
  theorems below only show that the chain composes as claimed. This is a
  \<^emph>\<open>definitional reconstruction\<close>, not a proof that reliance on
  \<open>prajnaparamita\<close> in fact removes hindrance or fear; nothing here is
  evidence for the doctrine (see \<^file>\<open>../../../docs/STATUS.md\<close>, label
  \<open>isabelle-theorem (definitional)\<close>).
\<close>

datatype kala = Past | Present | Future

locale bodhisattva_path = emptiness D neg mconj mdisj sv appears dep
  for D :: "'v set" and neg mconj mdisj
  and sv appears :: "dharma \<Rightarrow> 'v" and dep +
  fixes relies_prajna :: "'m \<Rightarrow> bool"
    and hindered  :: "'m \<Rightarrow> bool"
    and fears     :: "'m \<Rightarrow> bool"
    and inverted  :: "'m \<Rightarrow> bool"
    and nirvana   :: "'m \<Rightarrow> bool"
    and suffers   :: "'m \<Rightarrow> bool"
    and bodhi     :: "'m \<Rightarrow> bool"
    and buddha    :: "kala \<Rightarrow> 'm \<Rightarrow> bool"
    and avalokitesvara :: 'm
  assumes hs02:     "relies_prajna avalokitesvara"
      and hs20_21a: "relies_prajna m \<Longrightarrow> \<not> hindered m"
      and hs21b:    "\<not> hindered m \<Longrightarrow> \<not> fears m"
      and hs22a:    "\<not> hindered m \<Longrightarrow> \<not> inverted m"
      and hs22b:    "\<not> inverted m \<Longrightarrow> nirvana m"
      and hs04_26:  "nirvana m \<Longrightarrow> \<not> suffers m"
      and hs23:     "buddha t b \<Longrightarrow> relies_prajna b"
      and hs24:     "buddha t b \<Longrightarrow> relies_prajna b \<Longrightarrow> bodhi b"
begin

lemma hs21_22_chain:
  assumes "relies_prajna m"
  shows "\<not> hindered m \<and> \<not> fears m \<and> \<not> inverted m \<and> nirvana m \<and> \<not> suffers m"
  using assms hs20_21a hs21b hs22a hs22b hs04_26 by blast

lemma hs23_24_three_times: "buddha t b \<Longrightarrow> bodhi b"
  using hs23 hs24 by blast

lemma hs01_04_avalokitesvara: "nirvana avalokitesvara \<and> \<not> suffers avalokitesvara"
  using hs02 hs21_22_chain by blast

end

text \<open>
  Non-vacuity: a one-point model of minds (\<open>'m = unit\<close>) where everyone
  relies on \<open>prajnaparamita\<close>, no one is hindered, fearful, inverted, or
  suffering, everyone has attained nirvana and \<open>bodhi\<close>, and every buddha
  in every era is that single mind, discharges every assumption. The
  bodhisattva-path layer is therefore not vacuously true of every claim.
\<close>

interpretation path_consistent:
  bodhisattva_path "{True}" "Not" "(\<and>)" "(\<or>)"
    "\<lambda>_. False" "\<lambda>_. True" "\<lambda>x y. True"
    "\<lambda>_::unit. True" "\<lambda>_. False" "\<lambda>_. False" "\<lambda>_. False"
    "\<lambda>_. True" "\<lambda>_. False" "\<lambda>_. True" "\<lambda>_ _. True" "()"
  by unfold_locales auto

end
