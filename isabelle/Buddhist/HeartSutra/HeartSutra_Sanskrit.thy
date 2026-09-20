(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The Sanskrit recension of HS06-07, and why "emptiness is form" needs the conventional\<close>

theory HeartSutra_Sanskrit
  imports HeartSutra_TwoTruths
begin

text \<open>
  Conze's edition of the short Sanskrit text gives HS06-07 three
  formulations, where Xuanzang has two clauses:

  \<^item> \<open>rupam sunyata sunyataiva rupam\<close> -- a nominal sentence, "form
    [is] emptiness, emptiness itself [is] form": predication or identity,
    formalized as \<open>R_identity\<close> (value identity) or \<open>R_mutual\<close>
    (co-designation);
  \<^item> \<open>rupan na prthak sunyata, sunyataya na prthag rupam\<close> -- "emptiness is
    not separate from form, form is not separate from emptiness": the
    "not different" reading \<open>R_notsep\<close> (= 色不異空 空不異色);
  \<^item> \<open>yad rupam sa sunyata, ya sunyata tad rupam\<close> -- the correlative
    construction "what is form, that is emptiness; what is emptiness, that
    is form": coextension, again \<open>R_mutual\<close>.

  Attwood (2017) argues that the earliest recoverable form of the first
  clause was \<open>rupam mayopamam\<close>, "form is like an illusion" (as in the
  Pancavimsatisahasrika). We add it as a fourth reading, \<open>R_maya\<close>: the
  thing is present to experience (its appearance is designated) and absent
  in reality (its own-being is not designated). Results:

  \<^item> Classically all four readings coincide.
  \<^item> Under FDE, \<open>R_maya\<close> says exactly that own-being is not a glut
    (\<open>fde_maya_iff_sv_F\<close>); together with a consistent appearance it
    implies the other three readings, but alone it does not imply
    \<open>R_notsep\<close> (a glut for appearance defeats it).
  \<^item> The converse clause 空即是色 ("emptiness is form") is not a logical
    consequence of 色即是空: read as an implication it is equivalent to the
    \<open>samvrti\<close> assumption that every item under discussion appears
    (\<open>ku_soku_ze_shiki_iff_samvrti\<close>), and a model with an item that is
    empty but does not appear (the stock "rabbit's horn") refutes it
    (\<open>rabbit_horn\<close>). This is the observation, often made informally (e.g.
    by A. Sumanasara), that Western logic licenses 色即是空 but not its
    converse: the converse is not logic but the sutra's own premise that
    the skandhas do appear.
\<close>

context emptiness
begin

definition R_maya :: "dharma \<Rightarrow> bool" where   \<comment> \<open>\<open>rupam mayopamam\<close>: appears, yet without own-being\<close>
  "R_maya x \<longleftrightarrow> appears x \<in> D \<and> sv x \<notin> D"

lemma R_maya_iff: "R_maya x \<longleftrightarrow> sv x \<notin> D"
  unfolding R_maya_def using samvrti by blast

end

subsection \<open>Classical: the fourth reading joins the other three\<close>

context cl_emptiness
begin

lemma cl_maya: "R_maya x"
  unfolding R_maya_iff using mmk_24_18[of x] pratitya[of x] by auto

lemma cl_sv_False: "sv x = False"
  using mmk_24_18[of x] pratitya[of x] by auto

lemma cl_four_readings_coincide:
  "R_maya x" "R_identity x" "R_mutual x" "R_notsep x"
  unfolding R_maya_def R_identity_def R_mutual_def R_notsep_def sunya_def
  using cl_sv_False[of x] samvrti[of x] by simp_all

end

subsection \<open>FDE: illusion means "no glut on own-being"\<close>

locale fde_emptiness = emptiness "{T, B}" neg4 conj4 disj4 sv appears dep
  for sv appears :: "dharma \<Rightarrow> tv4" and dep
begin

lemma sv_BF: "sv x = B \<or> sv x = F"
  using mmk_24_18[of x] pratitya[of x] by (cases "sv x") (auto simp: neg4_def mk_def)

theorem fde_maya_iff_sv_F: "R_maya x \<longleftrightarrow> sv x = F"
  unfolding R_maya_iff using sv_BF[of x] by auto

theorem fde_maya_consistent_coincide:
  assumes "R_maya x" and "appears x = T"
  shows "R_identity x" "R_mutual x" "R_notsep x"
  using assms unfolding fde_maya_iff_sv_F R_identity_def R_mutual_def R_notsep_def sunya_def
  by (simp_all add: neg4_def conj4_def mk_def)

end

lemma fde_emptiness_nonvacuous:
  "fde_emptiness (\<lambda>_. B) (\<lambda>_. T) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

text \<open>Without a consistent appearance, illusion does not give "not different".\<close>

interpretation maya_glut: emptiness "{T, B}" neg4 conj4 disj4
  "\<lambda>_. F" "\<lambda>_. B" "\<lambda>x y. True"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

lemma fde_maya_not_notsep:
  "maya_glut.R_maya x" and "\<not> maya_glut.R_notsep x"
  unfolding maya_glut.R_maya_def maya_glut.R_notsep_def maya_glut.sunya_def
  by (simp_all add: neg4_def conj4_def mk_def)

subsection \<open>空即是色 is the conventional premise, not a consequence\<close>

locale emptiness_nosamvrti = mv_logic D neg mconj mdisj
  for D :: "'v set" and neg mconj mdisj +
  fixes sv appears :: "'t \<Rightarrow> 'v"
  assumes empty_all: "neg (sv x) \<in> D"
begin

definition shiki_soku_ku :: bool where   \<comment> \<open>色即是空 as an implication over all items\<close>
  "shiki_soku_ku \<longleftrightarrow> (\<forall>x. appears x \<in> D \<longrightarrow> neg (sv x) \<in> D)"

definition ku_soku_ze_shiki :: bool where   \<comment> \<open>空即是色 as an implication over all items\<close>
  "ku_soku_ze_shiki \<longleftrightarrow> (\<forall>x. neg (sv x) \<in> D \<longrightarrow> appears x \<in> D)"

theorem shiki_soku_ku_holds: "shiki_soku_ku"
  unfolding shiki_soku_ku_def using empty_all by blast

theorem ku_soku_ze_shiki_iff_samvrti: "ku_soku_ze_shiki \<longleftrightarrow> (\<forall>x. appears x \<in> D)"
  unfolding ku_soku_ze_shiki_def using empty_all by blast

end

text \<open>
  The rabbit's horn: an item (\<open>False\<close>) that is empty like everything else
  but does not appear. 色即是空 holds, 空即是色 fails.
\<close>

interpretation rabbit_horn: emptiness_nosamvrti "{True}" Not "(\<and>)" "(\<or>)" "\<lambda>_. False" "\<lambda>x. x"
  by unfold_locales (simp_all add: True_not_UNIV)

theorem rabbit_horn:
  "rabbit_horn.shiki_soku_ku" and "\<not> rabbit_horn.ku_soku_ze_shiki"
  unfolding rabbit_horn.shiki_soku_ku_def rabbit_horn.ku_soku_ze_shiki_def by auto

end
