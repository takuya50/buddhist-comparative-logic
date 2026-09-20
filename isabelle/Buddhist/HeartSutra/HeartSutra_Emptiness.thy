(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Emptiness layer: svabhava, dependent origination, three readings of HS06-07\<close>

theory HeartSutra_Emptiness
  imports HeartSutra_Dharma Catuskoti
begin

text \<open>
  \<open>dharma\<close> collects every entity the sutra denies own-being of: the five
  skandhas (HS03, HS08), the twelve ayatanas and eighteen dhatus (HS11-14),
  the twelve nidana links and their cessations (HS15-16), the four truths
  (HS17), and the two items of HS18-19 (knowledge, attainment).
\<close>

datatype dharma =
    Sk skandha
  | Ay ayatana
  | Dh dhatu
  | Ni nidana
  | NiNirodha nidana
  | Sa satya
  | Jnana
  | Prapti

text \<open>
  The locale fixes: \<open>sv\<close>, a dharma's own-being value; \<open>appears\<close>, its
  conventional appearance (the "form" of \<open>rupa\<close>, phenomenally); \<open>dep\<close>,
  the dependent-origination relation. The assumptions model a selected reading
  of Nagarjuna's \<^emph>\<open>Mulamadhyamakakarika\<close> 24:18 ("whatever is dependently
  arisen, that we declare to be empty"), the claim that every listed dharma
  is so arisen, and the observation that the skandhas etc. do conventionally
  appear (\<open>samvrti\<close>, without which "form is emptiness" would be vacuous by
  \<open>appears x \<notin> D\<close> for a nonexistent \<open>x\<close>).
\<close>

text \<open>
  HS11-19's enumeration: the five skandhas, twelve ayatanas, eighteen
  dhatus, twelve nidana links, their twelve cessations, the four truths,
  and knowledge and attainment -- 65 dharmas in all, matching
  五蘊, 十二處, 十八界, 十二因緣, 十二因緣盡, 四諦, 智, 得.
\<close>

definition negated_dharmas :: "dharma list" where
  "negated_dharmas =
     map Sk skandhas @ map Ay ayatanas @ map Dh dhatus
   @ map Ni anuloma @ map NiNirodha anuloma @ map Sa satyas
   @ [Jnana, Prapti]"

lemma negated_dharmas_length: "length negated_dharmas = 65"
  by (simp add: negated_dharmas_def skandhas_def ayatanas_def indriyas_def visayas_def
      dhatus_def anuloma_def satyas_def eval_nat_numeral)

lemma negated_dharmas_distinct: "distinct negated_dharmas"
  by eval

lemma negated_dharmas_covers:
  "set negated_dharmas =
     Sk ` UNIV \<union> Ay ` UNIV \<union> Dh ` UNIV \<union> Ni ` UNIV \<union> NiNirodha ` UNIV \<union> Sa ` UNIV \<union> {Jnana, Prapti}"
  using skandhas_univ ayatanas_univ dhatu_naishi anuloma_complete satyas_univ
  by (simp add: negated_dharmas_def image_Un) blast

subsection \<open>Unbundled premises\<close>

text \<open>
  The weak interface below separates four predicates on the semantic data
  before the full locale bundles them. Universal emptiness uses only the first
  two. This proof is universal instantiation and modus ponens; its value here is
  the explicit dependency boundary, not mathematical depth.
\<close>

definition emptiness_mmk_24_18 ::
  "'v set \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> (dharma \<Rightarrow> 'v) \<Rightarrow>
    (dharma \<Rightarrow> dharma \<Rightarrow> bool) \<Rightarrow> bool" where
  "emptiness_mmk_24_18 D neg sv dep \<longleftrightarrow>
    (\<forall>x. (\<exists>y. dep y x) \<longrightarrow> neg (sv x) \<in> D)"

definition emptiness_pratitya ::
  "(dharma \<Rightarrow> dharma \<Rightarrow> bool) \<Rightarrow> bool" where
  "emptiness_pratitya dep \<longleftrightarrow> (\<forall>x. \<exists>y. dep y x)"

definition emptiness_samvrti ::
  "'v set \<Rightarrow> (dharma \<Rightarrow> 'v) \<Rightarrow> bool" where
  "emptiness_samvrti D appears \<longleftrightarrow> (\<forall>x. appears x \<in> D)"

definition emptiness_nidana_dep ::
  "(dharma \<Rightarrow> dharma \<Rightarrow> bool) \<Rightarrow> bool" where
  "emptiness_nidana_dep dep \<longleftrightarrow>
    (\<forall>n m. nidana_next n = Some m \<longrightarrow> dep (Ni n) (Ni m))"

definition emptiness_all ::
  "'v set \<Rightarrow> ('v \<Rightarrow> 'v) \<Rightarrow> (dharma \<Rightarrow> 'v) \<Rightarrow> bool" where
  "emptiness_all D neg sv \<longleftrightarrow> (\<forall>x. neg (sv x) \<in> D)"

lemma sarva_dharma_sunya_from_core:
  assumes "emptiness_mmk_24_18 D neg sv dep" and "emptiness_pratitya dep"
  shows "emptiness_all D neg sv"
  using assms unfolding emptiness_mmk_24_18_def emptiness_pratitya_def
    emptiness_all_def by blast

text \<open>
  The following concrete omissions retain the same nontrivial classical
  logic, conventional appearance, and nidana-chain requirement. In the second
  model only Jnana has own-being, and exactly that target has no incoming
  dependence. Thus no required nidana edge is lost. The two-premise set is
  deletion-minimal relative to this signature and model class, not an absolute
  weakest condition or a claim about doctrinal necessity.
\<close>

lemma emptiness_without_mmk:
  "mv_logic {True} \<and>
    emptiness_samvrti {True} (\<lambda>_. True) \<and>
    emptiness_nidana_dep (\<lambda>_ _. True) \<and>
    emptiness_pratitya (\<lambda>_ _. True) \<and>
    \<not> emptiness_mmk_24_18 {True} Not (\<lambda>_. True) (\<lambda>_ _. True) \<and>
    \<not> emptiness_all {True} Not (\<lambda>_. True)"
  by (simp add: mv_logic_def True_not_UNIV emptiness_samvrti_def
    emptiness_nidana_dep_def emptiness_pratitya_def
    emptiness_mmk_24_18_def emptiness_all_def)

lemma emptiness_without_pratitya:
  "mv_logic {True} \<and>
    emptiness_samvrti {True} (\<lambda>_. True) \<and>
    emptiness_nidana_dep (\<lambda>_ x. x \<noteq> Jnana) \<and>
    emptiness_mmk_24_18 {True} Not (\<lambda>x. x = Jnana) (\<lambda>_ x. x \<noteq> Jnana) \<and>
    \<not> emptiness_pratitya (\<lambda>_ x. x \<noteq> Jnana) \<and>
    \<not> emptiness_all {True} Not (\<lambda>x. x = Jnana)"
  by (simp add: mv_logic_def True_not_UNIV emptiness_samvrti_def
    emptiness_nidana_dep_def emptiness_pratitya_def
    emptiness_mmk_24_18_def emptiness_all_def)

lemma emptiness_core_relative_independence:
  "(\<exists>sv dep. mv_logic {True} \<and>
      emptiness_samvrti {True} (\<lambda>_. True) \<and> emptiness_nidana_dep dep \<and>
      emptiness_pratitya dep \<and> \<not> emptiness_mmk_24_18 {True} Not sv dep \<and>
      \<not> emptiness_all {True} Not sv) \<and>
   (\<exists>sv dep. mv_logic {True} \<and>
      emptiness_samvrti {True} (\<lambda>_. True) \<and> emptiness_nidana_dep dep \<and>
      emptiness_mmk_24_18 {True} Not sv dep \<and> \<not> emptiness_pratitya dep \<and>
      \<not> emptiness_all {True} Not sv)"
  using emptiness_without_mmk emptiness_without_pratitya by blast

locale emptiness = mv_logic D neg mconj mdisj
  for D :: "'v set" and neg mconj mdisj +
  fixes sv      :: "dharma \<Rightarrow> 'v"
    and appears :: "dharma \<Rightarrow> 'v"
    and dep     :: "dharma \<Rightarrow> dharma \<Rightarrow> bool"
  assumes mmk_24_18: "(\<exists>y. dep y x) \<Longrightarrow> neg (sv x) \<in> D"
      and pratitya:  "\<exists>y. dep y x"
      and samvrti:   "appears x \<in> D"
      and nidana_dep: "nidana_next n = Some m \<Longrightarrow> dep (Ni n) (Ni m)"
begin

definition sunya :: "dharma \<Rightarrow> 'v" where
  "sunya x = neg (sv x)"

definition empty_of :: "dharma \<Rightarrow> bool" where
  "empty_of x \<longleftrightarrow> sunya x \<in> D"

text \<open>Three candidate readings of \<open>色即是空 空即是色\<close> / \<open>色不異空 空不異色\<close>.\<close>

definition R_identity :: "dharma \<Rightarrow> bool" where          \<comment> \<open>value identity\<close>
  "R_identity x \<longleftrightarrow> appears x = sunya x"

definition R_mutual :: "dharma \<Rightarrow> bool" where             \<comment> \<open>mutual implication at designation\<close>
  "R_mutual x \<longleftrightarrow> (appears x \<in> D \<longleftrightarrow> sunya x \<in> D)"

definition R_notsep :: "dharma \<Rightarrow> bool" where              \<comment> \<open>"not different from" (Attwood)\<close>
  "R_notsep x \<longleftrightarrow> mconj (appears x) (sv x) \<notin> D \<and> mconj (sunya x) (neg (appears x)) \<notin> D"

lemma sarva_dharma_sunya: "empty_of x"
  using sarva_dharma_sunya_from_core[of D neg sv dep] mmk_24_18 pratitya
  unfolding empty_of_def sunya_def emptiness_mmk_24_18_def
    emptiness_pratitya_def emptiness_all_def by blast

lemma hs03_skandhas: "\<forall>s. empty_of (Sk s)"
  using sarva_dharma_sunya by blast

lemma hs07_R_mutual: "R_mutual x"
  unfolding R_mutual_def using samvrti sarva_dharma_sunya empty_of_def by blast

lemma hs08_generalize: "\<forall>s. R_mutual (Sk s)"
  using hs07_R_mutual by blast

lemma hs11_18_enumeration: "\<forall>d \<in> set negated_dharmas. empty_of d"
  using sarva_dharma_sunya by blast

lemma hs15_16_chain_and_cessation: "\<forall>n. empty_of (Ni n) \<and> empty_of (NiNirodha n)"
  using sarva_dharma_sunya by blast

lemma hs19_no_attainment: "empty_of Prapti"
  using sarva_dharma_sunya by blast

end

subsection \<open>Reading comparison, per logic\<close>

text \<open>
  Classically the three readings of HS06-07 coincide: with \<open>D = {True}\<close>,
  identity, mutual implication and Attwood's "not separate" reading all say
  the same thing about a two-valued \<open>appears\<close>/\<open>sunya\<close> pair. Under FDE they
  come apart: a glut for \<open>appears\<close> or \<open>sv\<close> can make one reading hold
  while another fails, which is a genuine logic-dependence result, not an
  artifact of the encoding.
\<close>

locale cl_emptiness = emptiness "{True}" Not "(\<and>)" "(\<or>)" sv appears dep
  for sv appears :: "dharma \<Rightarrow> bool" and dep
begin

lemma cl_readings_coincide:
  "R_identity x \<longleftrightarrow> R_mutual x" and "R_mutual x \<longleftrightarrow> R_notsep x"
  unfolding R_identity_def R_mutual_def R_notsep_def sunya_def by auto

end

text \<open>
  Within the locale, FDE forces \<open>sv x \<in> {B, F}\<close> (its negation must be
  designated) and \<open>appears x \<in> {T, B}\<close>. Two glut models separate the
  readings: \<open>fde_glut\<close> (own-being is a glut, appearance is plainly true)
  satisfies the mutual-implication reading but not value identity;
  \<open>fde_allglut\<close> (both are gluts) satisfies value identity but not the
  "not different from" reading, because \<open>B \<sqinter> B = B\<close> is designated.
\<close>

interpretation fde_glut: emptiness "{T,B}" neg4 conj4 disj4
  "\<lambda>_. B" "\<lambda>_. T" "\<lambda>x y. True"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

lemma fde_R_mutual_not_identity:
  "fde_glut.R_mutual x" and "\<not> fde_glut.R_identity (Sk rupa)"
  unfolding fde_glut.R_mutual_def fde_glut.R_identity_def fde_glut.sunya_def
  by (simp_all add: neg4_def mk_def)

interpretation fde_allglut: emptiness "{T,B}" neg4 conj4 disj4
  "\<lambda>_. B" "\<lambda>_. B" "\<lambda>x y. True"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

lemma fde_R_identity_not_notsep:
  "fde_allglut.R_identity x" and "\<not> fde_allglut.R_notsep (Sk rupa)"
  unfolding fde_allglut.R_identity_def fde_allglut.R_notsep_def fde_allglut.sunya_def
  by (simp_all add: neg4_def conj4_def mk_def)

text \<open>
  Non-vacuity: each locale instance used above and below is exhibited with
  a concrete model, so the emptiness layer is not trivially inconsistent.
  (The locale predicate \<open>emptiness\<close> only takes the parameters that occur
  in some assumption -- \<open>D\<close>, \<open>neg\<close>, \<open>sv\<close>, \<open>appears\<close>, \<open>dep\<close> -- since the
  connectives are constrained by no axiom.)
\<close>

lemma emptiness_consistent_cl:
  "emptiness {True} Not (\<lambda>_. False) (\<lambda>_. True) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: True_not_UNIV)

lemma emptiness_consistent_fde:
  "emptiness {T,B} neg4 (\<lambda>_. B) (\<lambda>_. T) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: TB_not_UNIV neg4_def mk_def)

text \<open>
  The same for the classical specialization below. Every locale in this
  session carries a model witness -- an \<^theory_text>\<open>interpretation\<close>, a
  \<^theory_text>\<open>sublocale\<close> from a locale that has one, or a lemma named
  \<open>..._nonvacuous\<close> -- so that no theorem proved inside a locale is
  vacuously true. \<^file>\<open>../../../tools/check_names.py\<close> enforces the convention.
\<close>

lemma cl_emptiness_nonvacuous:
  "cl_emptiness (\<lambda>_. False) (\<lambda>_. True) (\<lambda>x y. True)"
  by unfold_locales (simp_all add: True_not_UNIV)

subsection \<open>HS10: neither arising nor ceasing, neither defiled nor pure, neither increasing nor decreasing\<close>

datatype anta = Arise | Cease | Defiled | Pure | Increase | Decrease

definition anta_pairs :: "(anta \<times> anta) list" where
  "anta_pairs = [(Arise, Cease), (Defiled, Pure), (Increase, Decrease)]"

text \<open>
  The three pairs are one schema three times: the members of a pair are
  distinct, the first members and the second members do not overlap, and
  together they exhaust \<open>anta\<close>. The HS10 analysis below is stated for an
  arbitrary atom, so it applies to each pair without change; nothing in it
  turns on which of the three is meant.
\<close>

lemma anta_pairs_length: "length anta_pairs = 3"
  by (simp add: anta_pairs_def)

lemma anta_pairs_distinct_members: "\<forall>(x, y) \<in> set anta_pairs. x \<noteq> y"
  by (simp add: anta_pairs_def)

lemma anta_pairs_sides_disjoint:
  "set (map fst anta_pairs) \<inter> set (map snd anta_pairs) = {}"
  by (simp add: anta_pairs_def)

lemma anta_pairs_cover: "set (map fst anta_pairs) \<union> set (map snd anta_pairs) = UNIV"
proof (rule set_eqI)
  fix x :: anta
  show "x \<in> set (map fst anta_pairs) \<union> set (map snd anta_pairs) \<longleftrightarrow> x \<in> UNIV"
    by (cases x) (simp_all add: anta_pairs_def)
qed

text \<open>
  Two readings of "neither \<open>P\<close> nor \<open>\<not>P\<close>", evaluated per logic:
  (a) \<^emph>\<open>formula level\<close> -- the conjunction \<open>\<not>P \<and> \<not>\<not>P\<close> is designated;
  (b) \<^emph>\<open>designation level\<close> -- neither \<open>P\<close> nor \<open>\<not>P\<close> is itself designated.
  These are genuinely different statements and get different answers under
  FDE: (a) holds exactly when the atom's value is \<open>B\<close> (a glut), while (b)
  holds exactly when it is \<open>N\<close> (a gap). Neither is possible classically.
  \<^file>\<open>../../../docs/STATUS.md\<close> must present both, not conflate them into a single
  "FDE says neither arising nor ceasing is \<open>N\<close>" claim.
\<close>

definition hs10_formula :: "atom \<Rightarrow> atom fm" where
  "hs10_formula a = Conj (Neg (Atom a)) (Neg (Neg (Atom a)))"

lemma hs10_cl_contradictory_unsat: "\<not> cl.sat v (hs10_formula a)"
  unfolding hs10_formula_def cl.sat_def cl.eval_def by simp

lemma hs10_fde_formula_iff_B: "fde.sat v (hs10_formula a) \<longleftrightarrow> v a = B"
  unfolding hs10_formula_def fde.sat_def fde.eval_def
  by (cases "v a") (simp_all add: neg4_def conj4_def mk_def)

definition hs10_neither :: "(atom \<Rightarrow> tv4) \<Rightarrow> atom \<Rightarrow> bool" where
  "hs10_neither v a \<longleftrightarrow> v a \<notin> {T,B} \<and> neg4 (v a) \<notin> {T,B}"

lemma hs10_cl_neither_impossible:
  "\<not> (\<exists>v :: atom \<Rightarrow> bool. \<not> v a \<and> \<not> \<not> v a)"
  by simp

lemma hs10_fde_neither_iff_N: "hs10_neither v a \<longleftrightarrow> v a = N"
  unfolding hs10_neither_def by (cases "v a") (simp_all add: neg4_def mk_def)

definition hs10_neither5 :: "(atom \<Rightarrow> tv5) \<Rightarrow> atom \<Rightarrow> bool" where
  "hs10_neither5 v a \<longleftrightarrow> v a \<notin> {Fin T, Fin B} \<and> neg5 (v a) \<notin> {Fin T, Fin B}"

lemma hs10_fde5_neither_iff_N_or_E: "hs10_neither5 v a \<longleftrightarrow> v a = Fin N \<or> v a = E"
proof (cases "v a")
  case (Fin x)
  then show ?thesis
    by (cases x) (simp_all add: hs10_neither5_def neg4_def mk_def)
next
  case E
  then show ?thesis by (simp add: hs10_neither5_def)
qed

end
