(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Mulamadhyamakakarika 24:18-19: deriving the emptiness axiom from dependent arising\<close>

theory Madhyamaka_MMK24
  imports HeartSutra_Emptiness
begin

text \<open>
  \<open>HeartSutra_Emptiness\<close> takes \<open>mmk_24_18\<close> ("whatever is dependently arisen is
  empty") as a locale \<^emph>\<open>assumption\<close>. This theory pushes the justification
  one step upstream, following Nagarjuna's own chain:

  \<^item> MMK 15:2 -- own-being (\<open>svabhava\<close>) is what is "not made and not
    dependent on another" (\<open>akrtrimah svabhavo hi nirapeksah paratra ca\<close>).
    We take this as a \<^emph>\<open>definition\<close>: the own-being value of \<open>x\<close> is the
    negation of the value of "\<open>x\<close> is dependently arisen".
  \<^item> MMK 24:19a -- "there is no dharma whatever that is not dependently
    arisen" (\<open>apratitya samutpanno dharmah kascin na vidyate\<close>): an
    assumption, \<open>mmk_24_19\<close>.
  \<^item> MMK 24:19b / 24:18a -- "therefore there is no dharma whatever that is
    not empty", i.e. \<open>neg (svabhava x)\<close> is designated: now a \<^emph>\<open>theorem\<close>,
    provided negation is involutive (\<open>neg (neg x) = x\<close>), which holds in
    all three logics of \<open>FiniteLogics\<close>.

  MMK 24:18b-d ("that is dependent designation, that itself is the middle
  way") is also given a formal counterpart: \<open>prajnapti\<close> (a dharma appears
  conventionally and is empty) and \<open>madhyama\<close> (neither the eternalist
  extreme -- own-being affirmed -- nor the nihilist extreme -- appearance
  denied). The middle way turns out to be logic-dependent in the same way
  as HS06 in \<open>HeartSutra_Emptiness\<close>: under FDE it requires that "dependently
  arisen" not be a glut.
\<close>

locale madhyamaka = mv_logic D neg mconj mdisj
  for D :: "'v set" and neg mconj mdisj +
  fixes arisen  :: "dharma \<Rightarrow> 'v"   \<comment> \<open>value of "\<open>x\<close> is dependently arisen" (\<open>pratityasamutpanna\<close>)\<close>
    and appears :: "dharma \<Rightarrow> 'v"
    and dep     :: "dharma \<Rightarrow> dharma \<Rightarrow> bool"
  assumes neg_invol:  "neg (neg w) = w"
      and mmk_24_19:  "arisen x \<in> D"
      and arisen_dep: "arisen x \<in> D \<Longrightarrow> \<exists>y. dep y x"
      and samvrti_m:  "appears x \<in> D"
      and nidana_dep_m: "nidana_next n = Some m \<Longrightarrow> dep (Ni n) (Ni m)"
begin

definition svabhava :: "dharma \<Rightarrow> 'v" where   \<comment> \<open>MMK 15:2, as a definition\<close>
  "svabhava x = neg (arisen x)"

text \<open>MMK 24:19b: the emptiness axiom of \<open>HeartSutra_Emptiness\<close>, now derived.\<close>

lemma mmk_24_18_derived: "neg (svabhava x) \<in> D"
  unfolding svabhava_def by (simp add: neg_invol mmk_24_19)

lemma pratitya_derived: "\<exists>y. dep y x"
  using arisen_dep mmk_24_19 by blast

sublocale emptiness D neg mconj mdisj svabhava appears dep
  by unfold_locales (auto simp: mmk_24_18_derived pratitya_derived samvrti_m nidana_dep_m)

text \<open>
  MMK 24:18b-d. \<open>prajnapti\<close>: the dharma is conventionally there and empty.
  \<open>madhyama\<close>: neither eternalism (\<open>svabhava\<close> designated) nor nihilism
  (appearance not designated).
\<close>

definition prajnapti :: "dharma \<Rightarrow> bool" where
  "prajnapti x \<longleftrightarrow> appears x \<in> D \<and> empty_of x"

definition eternalism :: "dharma \<Rightarrow> bool" where
  "eternalism x \<longleftrightarrow> svabhava x \<in> D"

definition nihilism :: "dharma \<Rightarrow> bool" where
  "nihilism x \<longleftrightarrow> appears x \<notin> D"

definition madhyama :: "dharma \<Rightarrow> bool" where
  "madhyama x \<longleftrightarrow> \<not> eternalism x \<and> \<not> nihilism x"

lemma mmk_24_18_prajnapti: "prajnapti x"
  unfolding prajnapti_def using samvrti_m sarva_dharma_sunya by blast

lemma no_nihilism: "\<not> nihilism x"
  unfolding nihilism_def using samvrti_m by blast

lemma madhyama_iff_no_eternalism: "madhyama x \<longleftrightarrow> svabhava x \<notin> D"
  unfolding madhyama_def eternalism_def using no_nihilism by blast

end

subsection \<open>Instances, and the logic-dependence of the middle way\<close>

lemma neg4_invol [simp]: "neg4 (neg4 x) = x"
  by (cases x) (simp_all add: neg4_def mk_def)

lemma neg5_invol [simp]: "neg5 (neg5 x) = x"
  by (cases x) simp_all

text \<open>
  Classically, the middle way is automatic: every dharma is arisen, so no
  dharma has own-being. Under FDE the same premises leave room for
  \<open>arisen x = B\<close>, in which case \<open>svabhava x = neg4 B = B\<close> is designated
  too and the eternalist extreme is \<^emph>\<open>not\<close> excluded. The middle way holds
  under FDE exactly when "dependently arisen" is not a glut.
\<close>

locale cl_madhyamaka = madhyamaka "{True}" Not "(\<and>)" "(\<or>)" arisen appears dep
  for arisen appears :: "dharma \<Rightarrow> bool" and dep
begin

lemma cl_madhyama: "madhyama x"
  unfolding madhyama_iff_no_eternalism svabhava_def using mmk_24_19 by simp

end

locale fde_madhyamaka = madhyamaka "{T, B}" neg4 conj4 disj4 arisen appears dep
  for arisen appears :: "dharma \<Rightarrow> tv4" and dep
begin

lemma fde_arisen_TB: "arisen x = T \<or> arisen x = B"
  using mmk_24_19 by auto

lemma fde_madhyama_iff_consistent: "madhyama x \<longleftrightarrow> arisen x = T"
proof -
  have "arisen x \<in> {T, B}" by (rule mmk_24_19)
  then show ?thesis
    unfolding madhyama_iff_no_eternalism svabhava_def
    by (cases "arisen x") (auto simp: neg4_def mk_def)
qed

end

text \<open>Non-vacuity of both instances.\<close>

lemma madhyamaka_consistent_cl:
  "madhyamaka {True} Not (\<lambda>_. True) (\<lambda>_. True) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: True_not_UNIV)

lemma madhyamaka_consistent_fde:
  "madhyamaka {T, B} neg4 (\<lambda>_. T) (\<lambda>_. T) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: TB_not_UNIV)

lemma cl_madhyamaka_nonvacuous:
  "cl_madhyamaka (\<lambda>_. True) (\<lambda>_. True) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: True_not_UNIV)

lemma fde_madhyamaka_nonvacuous:
  "fde_madhyamaka (\<lambda>_. T) (\<lambda>_. T) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: TB_not_UNIV)

text \<open>
  The glut model: every dharma "both is and is not" dependently arisen.
  It satisfies all premises, yet the middle way fails for every dharma.
\<close>

interpretation fde_glut_arisen: madhyamaka "{T, B}" neg4 conj4 disj4
  "\<lambda>_. B" "\<lambda>_. T" "\<lambda>x y. True"
  by unfold_locales (simp_all add: TB_not_UNIV)

lemma fde_glut_defeats_middle_way: "\<not> fde_glut_arisen.madhyama x"
  unfolding fde_glut_arisen.madhyama_iff_no_eternalism fde_glut_arisen.svabhava_def
  by (simp add: neg4_def mk_def)

end
