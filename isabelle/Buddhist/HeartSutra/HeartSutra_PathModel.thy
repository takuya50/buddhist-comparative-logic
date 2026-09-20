(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>A grasping model for the path layer: the HS20-26 implications as theorems\<close>

theory HeartSutra_PathModel
  imports HeartSutra_Path
begin

text \<open>
  \<open>HeartSutra_Path\<close> took the sutra's chain 依般若波羅蜜多故 心無罣礙 ... 究竟涅槃 as locale
  assumptions and proved only that they compose. This theory builds a
  model in which each link is a \<^emph>\<open>theorem\<close>. A mind state \<open>m\<close> has a set
  \<open>grasp m\<close> of dharmas it holds as having own-being (\<open>upadana\<close>, 取, 執),
  and a relation \<open>sees m d\<close>, "\<open>m\<close> sees \<open>d\<close> as empty" (照見). The one
  substantive bridge axiom is that what is seen as empty is not grasped.
  Then:

  \<^item> reliance on prajna = seeing every dharma as empty;
  \<^item> hindrance (罣礙) = grasping something;
  \<^item> fear (恐怖) and suffering (苦) = grasping something impermanent, and
    every dharma is impermanent;
  \<^item> inversion (顛倒) = grasping as substantial something that is empty,
    and every dharma is empty;
  \<^item> nirvana = the extinction of grasping;
  \<^item> bodhi = seeing all as empty with no grasping left.

  The eight assumptions of \<open>bodhisattva_path\<close> become provable, so the
  grasping model is a sublocale, and \<open>HeartSutra_Path\<close>'s chain theorems hold in it
  for free. Two things the model adds: the sutra's chain is partly
  reversible (fear presupposes hindrance; nirvana excludes inversion,
  fear and suffering), and the one step that is not reversible is the
  first: a mind can be free of grasping without seeing (a model is
  exhibited). The label remains "definitional": these are consequences of
  the definitions of grasping, fear and so on, not evidence that the
  definitions are right.
\<close>

locale grasping_model = emptiness D neg mconj mdisj sv appears dep
  for D :: "'v set" and neg mconj mdisj
  and sv appears :: "dharma \<Rightarrow> 'v" and dep +
  fixes grasp  :: "'m \<Rightarrow> dharma set"          \<comment> \<open>取: dharmas held as having own-being\<close>
    and sees   :: "'m \<Rightarrow> dharma \<Rightarrow> bool"      \<comment> \<open>照見: sees the dharma as empty\<close>
    and anitya :: "dharma \<Rightarrow> bool"             \<comment> \<open>impermanent\<close>
    and buddha :: "kala \<Rightarrow> 'm \<Rightarrow> bool"
    and avalokitesvara :: 'm
  assumes no_grasp_when_seen: "sees m d \<Longrightarrow> d \<notin> grasp m"
      and sarva_anitya:       "anitya d"
      and avalokitesvara_sees: "sees avalokitesvara d"   \<comment> \<open>照見五蘊皆空, taken for all dharmas\<close>
      and buddha_sees:        "buddha t b \<Longrightarrow> sees b d"
begin

definition relies_prajna_m :: "'m \<Rightarrow> bool" where "relies_prajna_m m \<longleftrightarrow> (\<forall>d. sees m d)"
definition hindered_m :: "'m \<Rightarrow> bool" where "hindered_m m \<longleftrightarrow> grasp m \<noteq> {}"
definition fears_m    :: "'m \<Rightarrow> bool" where "fears_m m \<longleftrightarrow> (\<exists>d \<in> grasp m. anitya d)"
definition inverted_m :: "'m \<Rightarrow> bool" where "inverted_m m \<longleftrightarrow> (\<exists>d \<in> grasp m. empty_of d)"
definition nirvana_m  :: "'m \<Rightarrow> bool" where "nirvana_m m \<longleftrightarrow> grasp m = {}"
definition suffers_m  :: "'m \<Rightarrow> bool" where "suffers_m m \<longleftrightarrow> (\<exists>d \<in> grasp m. anitya d)"
definition bodhi_m    :: "'m \<Rightarrow> bool" where "bodhi_m m \<longleftrightarrow> (\<forall>d. sees m d) \<and> grasp m = {}"

lemma relies_no_grasp: "relies_prajna_m m \<Longrightarrow> grasp m = {}"
  unfolding relies_prajna_m_def using no_grasp_when_seen by blast

lemma inverted_iff_hindered: "inverted_m m \<longleftrightarrow> hindered_m m"
  unfolding inverted_m_def hindered_m_def using sarva_dharma_sunya by blast

lemma fears_iff_hindered: "fears_m m \<longleftrightarrow> hindered_m m"
  unfolding fears_m_def hindered_m_def using sarva_anitya by blast

lemma suffers_iff_hindered: "suffers_m m \<longleftrightarrow> hindered_m m"
  unfolding suffers_m_def hindered_m_def using sarva_anitya by blast

sublocale path: bodhisattva_path D neg mconj mdisj sv appears dep
  relies_prajna_m hindered_m fears_m inverted_m nirvana_m suffers_m bodhi_m buddha avalokitesvara
proof unfold_locales
  show "relies_prajna_m avalokitesvara" unfolding relies_prajna_m_def using avalokitesvara_sees by blast
next
  fix m assume "relies_prajna_m m" then show "\<not> hindered_m m"
    unfolding hindered_m_def using relies_no_grasp by blast
next
  fix m assume "\<not> hindered_m m" then show "\<not> fears_m m" by (simp add: fears_iff_hindered)
next
  fix m assume "\<not> hindered_m m" then show "\<not> inverted_m m" by (simp add: inverted_iff_hindered)
next
  fix m assume "\<not> inverted_m m" then show "nirvana_m m"
    unfolding nirvana_m_def using inverted_iff_hindered hindered_m_def by blast
next
  fix m assume "nirvana_m m" then show "\<not> suffers_m m"
    unfolding nirvana_m_def suffers_m_def by simp
next
  fix t b assume "buddha t b" then show "relies_prajna_m b"
    unfolding relies_prajna_m_def using buddha_sees by blast
next
  fix t b assume "buddha t b" "relies_prajna_m b" then show "bodhi_m b"
    unfolding bodhi_m_def relies_prajna_m_def using relies_no_grasp relies_prajna_m_def by blast
qed

text \<open>The sutra's chain, inherited from \<open>HeartSutra_Path\<close>, and its partial converses.\<close>

theorem derived_chain:
  "relies_prajna_m m \<Longrightarrow> \<not> hindered_m m \<and> \<not> fears_m m \<and> \<not> inverted_m m \<and> nirvana_m m \<and> \<not> suffers_m m"
  by (rule path.hs21_22_chain)

theorem chain_converses:
  "fears_m m \<Longrightarrow> hindered_m m"
  "nirvana_m m \<Longrightarrow> \<not> inverted_m m \<and> \<not> fears_m m \<and> \<not> suffers_m m"
  by (simp_all add: fears_iff_hindered inverted_iff_hindered suffers_iff_hindered
                    hindered_m_def nirvana_m_def)

end

text \<open>
  Non-vacuity, and the one irreversible step: a model with two minds,
  neither grasping anything, only one of which sees.
\<close>

interpretation two_minds: grasping_model "{True}" Not "(\<and>)" "(\<or>)"
  "\<lambda>_. False" "\<lambda>_. True" "\<lambda>x y. True"
  "\<lambda>_. {}" "\<lambda>m d. m" "\<lambda>_. True" "\<lambda>_ m. m" True
  by unfold_locales (simp_all add: True_not_UNIV)

theorem nirvana_without_prajna:
  "two_minds.nirvana_m False" and "\<not> two_minds.relies_prajna_m False"
  by (simp_all add: two_minds.nirvana_m_def two_minds.relies_prajna_m_def)

end
