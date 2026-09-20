(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Plurivalent semantics: where Priest's fifth value comes from\<close>

theory PlurivalentSemantics
  imports Catuskoti
begin

text \<open>
  Priest's plurivalent logics let a formula take several values at once, or
  none. There are two natural ways to lift the connectives to sets of values:

  \<^item> \<^emph>\<open>functional\<close> (image): the value set of \<open>A \<and> B\<close> is the image of
    \<open>\<lbrakk>A\<rbrakk> \<times> \<lbrakk>B\<rbrakk>\<close> under the connective. This is Priest's own definition
    (Priest 2014, section 3: "\<open>v \<in> \<delta>(X\<^sub>1, ..., X\<^sub>n)\<close> iff for some \<open>v\<^sub>i \<in> X\<^sub>i\<close>,
    \<open>v = \<delta>(v\<^sub>1, ..., v\<^sub>n)\<close>").
  \<^item> \<^emph>\<open>relational\<close> (Dunn-style): "\<open>A \<and> B\<close> is true iff \<open>A\<close> is true and \<open>B\<close>
    is true; \<open>A \<and> B\<close> is false iff \<open>A\<close> is false or \<open>B\<close> is false", each
    clause read independently (Dunn 1976; the reading Priest attributes to
    Shramko and Wansing in his footnote 10).

  On non-empty value sets the two agree. They part company at the empty set:
  under the image semantics the empty set is \<^emph>\<open>absorbing\<close>, whereas under
  the relational semantics \<open>A \<and> B\<close> can be false although \<open>B\<close> has no value.

  None of the three theorems below is new as a mathematical fact; what this
  theory adds is a machine-checked, side-by-side statement of results that
  are spread over Priest (2014), its footnotes, and folklore, with the
  liftings made explicit.

  \<^enum> Relational plurivalent \<^emph>\<open>classical\<close> logic is FDE: the standard
    reading of FDE as classical logic with gaps and gluts (Dunn 1976).
  \<^enum> Functional plurivalent classical logic is \<^emph>\<open>not\<close> FDE. In Priest's
    taxonomy (2014, section 4) it is the logic with values \<open>{t, f, b, e}\<close>,
    i.e. Oller's AL (1999): FDE5 without the gap \<open>N\<close>. This is the content
    of Priest's remark (footnote 10) that "applying plurivalence to
    classical logic does not produce FDE", made precise.
  \<^enum> FDE5 is the "at most one value" fragment of functional plurivalent
    FDE, with \<open>e\<close> as the empty set. This is the special case for FDE of
    Priest's general-plurivalence theorem (2014, section 6): the general
    plurivalent consequence relation of a semantics \<open>M\<close> equals the
    positive plurivalent consequence relation of \<open>M\<close> extended by an
    absorbing undesignated value \<open>e\<close>. Indeed Priest's \<open>e\<close> abbreviates
    "empty", and his truth tables stipulate that "any function gives an
    output \<open>e\<close> iff some input is \<open>e\<close>" (2014, section 4).

  So the absorbing truth tables adopted for \<open>e\<close> in \<open>FiniteLogics\<close> are
  Priest's own, and they are what the functional reading of "has no value"
  forces. The collapse of the fifth corner at the designation level
  (\<open>Catuskoti\<close>) persists verbatim: a valueless formula is simply
  undesignated. Beall and Camrud (2020) show that iterating \<^emph>\<open>positive\<close>
  plurivalence over FDE never leaves FDE; the empty set, which they exclude,
  is exactly where the functional and relational readings diverge.
\<close>

subsection \<open>Functional (image) plurivalent evaluation\<close>

fun peval ::
  "('v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('v \<Rightarrow> 'v \<Rightarrow> 'v) \<Rightarrow> ('a \<Rightarrow> 'v set) \<Rightarrow> 'a fm \<Rightarrow> 'v set"
where
  "peval neg mconj mdisj V (Atom a) = V a"
| "peval neg mconj mdisj V (Neg X) = neg ` peval neg mconj mdisj V X"
| "peval neg mconj mdisj V (Conj X Y) =
     (\<lambda>(x, y). mconj x y) ` (peval neg mconj mdisj V X \<times> peval neg mconj mdisj V Y)"
| "peval neg mconj mdisj V (Disj X Y) =
     (\<lambda>(x, y). mdisj x y) ` (peval neg mconj mdisj V X \<times> peval neg mconj mdisj V Y)"

lemma peval_singleton: "peval ng cj dj (\<lambda>a. {v a}) X = {mv_eval ng cj dj v X}"
  by (induction X) auto

context mv_logic
begin

definition psat :: "('a \<Rightarrow> 'v set) \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "psat V A \<longleftrightarrow> peval neg mconj mdisj V A \<inter> D \<noteq> {}"

definition pentails :: "'a fm set \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "pentails \<Gamma> X \<longleftrightarrow> (\<forall>V. (\<forall>Y \<in> \<Gamma>. psat V Y) \<longrightarrow> psat V X)"

text \<open>
  Plurivalent consequence is stronger than univalent consequence: a
  univalent valuation is the plurivalent valuation whose value sets are
  singletons, so anything that holds of all plurivalent valuations holds
  of all univalent ones. (The converse is what \<open>PlurivalentSemantics\<close>'s main
  theorems are about, and it can fail.)
\<close>

lemma psat_singleton: "psat (\<lambda>a. {v a}) X \<longleftrightarrow> sat v X"
  by (simp add: psat_def sat_def eval_def peval_singleton)

lemma pentails_refl: "X \<in> \<Gamma> \<Longrightarrow> pentails \<Gamma> X"
  by (simp add: pentails_def)

lemma pentails_mono: "\<Gamma> \<subseteq> \<Delta> \<Longrightarrow> pentails \<Gamma> X \<Longrightarrow> pentails \<Delta> X"
  unfolding pentails_def by blast

lemma entails_of_pentails:
  assumes "pentails \<Gamma> X" shows "entails \<Gamma> X"
  unfolding entails_def
proof (intro allI impI)
  fix v assume "\<forall>Y \<in> \<Gamma>. sat v Y"
  then have "\<forall>Y \<in> \<Gamma>. psat (\<lambda>a. {v a}) Y" by (simp add: psat_singleton)
  then have "psat (\<lambda>a. {v a}) X" using assms unfolding pentails_def by blast
  then show "sat v X" by (simp add: psat_singleton)
qed

text \<open>The four corners for a value \<^emph>\<open>set\<close>, by designation of it and of its negation.\<close>

definition pkoti_of :: "'v set \<Rightarrow> koti" where
  "pkoti_of S =
    (if S \<inter> D \<noteq> {} \<and> neg ` S \<inter> D = {} then K1
     else if S \<inter> D = {} \<and> neg ` S \<inter> D \<noteq> {} then K2
     else if S \<inter> D \<noteq> {} \<and> neg ` S \<inter> D \<noteq> {} then K3
     else K4)"

lemma pkoti_empty: "pkoti_of {} = K4"
  by (simp add: pkoti_of_def)

end

subsection \<open>Theorem 3: FDE5 is the at-most-one-value fragment of functional plurivalent FDE\<close>

fun sing :: "tv5 \<Rightarrow> tv4 set" where
  "sing (Fin x) = {x}"
| "sing E = {}"

lemma sing_neg: "neg4 ` sing t = sing (neg5 t)"
  by (cases t) auto

lemma sing_conj: "(\<lambda>(x, y). conj4 x y) ` (sing s \<times> sing t) = sing (conj5 s t)"
  by (cases s; cases t) auto

lemma sing_disj: "(\<lambda>(x, y). disj4 x y) ` (sing s \<times> sing t) = sing (disj5 s t)"
  by (cases s; cases t) auto

theorem fde5_is_singleton_fragment:
  "peval neg4 conj4 disj4 (sing \<circ> V) A = sing (mv_eval neg5 conj5 disj5 V A)"
  by (induction A) (simp_all add: sing_neg sing_conj sing_disj)

theorem fde5_sat_is_fde_psat: "fde5.sat V A \<longleftrightarrow> fde.psat (sing \<circ> V) A"
  unfolding fde5.sat_def fde5.eval_def fde.psat_def fde5_is_singleton_fragment
  by (cases "mv_eval neg5 conj5 disj5 V A") auto

text \<open>The collapse of the fifth corner (\<open>Catuskoti\<close>) is inherited value for value.\<close>

theorem pkoti_sing: "fde.pkoti_of (sing t) = fde5.koti_of t"
  by (cases t) (simp_all add: fde.pkoti_of_def fde5.koti_of_def)

corollary fifth_corner_is_valueless: "fde.pkoti_of {} = K4"
  by (rule fde.pkoti_empty)

subsection \<open>Theorem 2: functional plurivalent classical logic is Oller's AL (FDE5 without the gap)\<close>

definition bs :: "bool set \<Rightarrow> tv4" where
  "bs S = mk (True \<in> S) (False \<in> S)"

definition bs5 :: "bool set \<Rightarrow> tv5" where
  "bs5 S = (if S = {} then E else Fin (bs S))"

lemma img_conj_T: "True \<in> (\<lambda>(x, y). x \<and> y) ` (S \<times> S') \<longleftrightarrow> True \<in> S \<and> True \<in> S'"
  by (auto simp: image_iff)

lemma img_conj_F:
  "S \<noteq> {} \<Longrightarrow> S' \<noteq> {} \<Longrightarrow> False \<in> (\<lambda>(x, y). x \<and> y) ` (S \<times> S') \<longleftrightarrow> False \<in> S \<or> False \<in> S'"
  by (auto simp: image_iff)

lemma img_disj_T:
  "S \<noteq> {} \<Longrightarrow> S' \<noteq> {} \<Longrightarrow> True \<in> (\<lambda>(x, y). x \<or> y) ` (S \<times> S') \<longleftrightarrow> True \<in> S \<or> True \<in> S'"
  by (auto simp: image_iff)

lemma img_disj_F: "False \<in> (\<lambda>(x, y). x \<or> y) ` (S \<times> S') \<longleftrightarrow> False \<in> S \<and> False \<in> S'"
  by (auto simp: image_iff)

lemma img_neg_T: "True \<in> Not ` S \<longleftrightarrow> False \<in> S" and img_neg_F: "False \<in> Not ` S \<longleftrightarrow> True \<in> S"
  by auto

text \<open>The simplifier normalizes boolean-set membership to bounded existentials; these bridge back.\<close>

lemma bex_id [simp]: "(\<exists>x\<in>S. x) \<longleftrightarrow> True \<in> S" and bex_not [simp]: "(\<exists>x\<in>S. \<not> x) \<longleftrightarrow> False \<in> S"
  by auto

lemma img_nonempty: "S \<noteq> {} \<Longrightarrow> S' \<noteq> {} \<Longrightarrow> (\<lambda>(x, y). f x y) ` (S \<times> S') \<noteq> {}"
  by auto

lemma bs5_neg: "bs5 (Not ` S) = neg5 (bs5 S)"
  by (cases "S = {}") (simp_all add: bs5_def bs_def neg4_def img_neg_T img_neg_F)

lemma bs5_conj: "bs5 ((\<lambda>(x, y). x \<and> y) ` (S \<times> S')) = conj5 (bs5 S) (bs5 S')"
proof (cases "S = {} \<or> S' = {}")
  case True
  then show ?thesis by (auto simp: bs5_def)
next
  case False
  then have ne: "S \<noteq> {}" "S' \<noteq> {}" by auto
  then show ?thesis
    using img_nonempty[OF ne, of "(\<and>)"] img_conj_T img_conj_F[OF ne]
    by (simp add: bs5_def bs_def conj4_def)
qed

lemma bs5_disj: "bs5 ((\<lambda>(x, y). x \<or> y) ` (S \<times> S')) = disj5 (bs5 S) (bs5 S')"
proof (cases "S = {} \<or> S' = {}")
  case True
  then show ?thesis by (auto simp: bs5_def)
next
  case False
  then have ne: "S \<noteq> {}" "S' \<noteq> {}" by auto
  then show ?thesis
    using img_nonempty[OF ne, of "(\<or>)"] img_disj_T[OF ne] img_disj_F
    by (simp add: bs5_def bs_def disj4_def)
qed

theorem image_plurivalent_classical_is_fde5:
  "bs5 (peval Not (\<and>) (\<or>) V A) = mv_eval neg5 conj5 disj5 (bs5 \<circ> V) A"
  by (induction A) (simp_all add: bs5_neg bs5_conj bs5_disj)

theorem image_plurivalent_classical_has_no_gap: "bs5 S \<noteq> Fin N"
proof
  assume "bs5 S = Fin N"
  then have ne: "S \<noteq> {}" and noT: "True \<notin> S" and noF: "False \<notin> S"
    by (auto simp: bs5_def bs_def mk_def split: if_splits)
  from ne obtain x where "x \<in> S" by blast
  then show False using noT noF by (cases x) auto
qed

theorem image_plurivalent_classical_sat:
  "cl.psat V A \<longleftrightarrow> fde5.sat (bs5 \<circ> V) A"
  unfolding cl.psat_def fde5.sat_def fde5.eval_def image_plurivalent_classical_is_fde5[symmetric]
  by (auto simp: bs5_def bs_def mk_def)

subsection \<open>Theorem 1: relational plurivalent classical logic is FDE\<close>

fun reval :: "('a \<Rightarrow> bool set) \<Rightarrow> 'a fm \<Rightarrow> bool set" where
  "reval V (Atom a) = V a"
| "reval V (Neg X) = {b. (b \<and> False \<in> reval V X) \<or> (\<not> b \<and> True \<in> reval V X)}"
| "reval V (Conj X Y) =
     {b. (b \<and> True \<in> reval V X \<and> True \<in> reval V Y) \<or>
         (\<not> b \<and> (False \<in> reval V X \<or> False \<in> reval V Y))}"
| "reval V (Disj X Y) =
     {b. (b \<and> (True \<in> reval V X \<or> True \<in> reval V Y)) \<or>
         (\<not> b \<and> False \<in> reval V X \<and> False \<in> reval V Y)}"

theorem relational_plurivalent_classical_is_fde:
  "mv_eval neg4 conj4 disj4 (bs \<circ> V) A = bs (reval V A)"
  by (induction A) (simp_all add: bs_def neg4_def conj4_def disj4_def)

theorem relational_plurivalent_classical_sat:
  "True \<in> reval V A \<longleftrightarrow> fde.sat (bs \<circ> V) A"
proof -
  have "True \<in> reval V A \<longleftrightarrow> tr (bs (reval V A))" by (simp add: bs_def)
  also have "\<dots> \<longleftrightarrow> bs (reval V A) \<in> {T, B}" by (cases "bs (reval V A)") simp_all
  finally show ?thesis
    unfolding fde.sat_def fde.eval_def relational_plurivalent_classical_is_fde .
qed

subsection \<open>The two semantics differ exactly at the empty value set\<close>

definition V_gap :: "atom \<Rightarrow> bool set" where
  "V_gap a = (if a = p then {False} else {})"

lemma image_vs_relational:
  "peval Not (\<and>) (\<or>) V_gap (Conj (Atom p) (Atom q)) = {}" and
  "reval V_gap (Conj (Atom p) (Atom q)) = {False}"
  by (auto simp: V_gap_def)

lemma bool_set_eq_iff:
  "(S :: bool set) = S' \<longleftrightarrow> (True \<in> S \<longleftrightarrow> True \<in> S') \<and> (False \<in> S \<longleftrightarrow> False \<in> S')"
  by (simp add: set_eq_iff all_bool_eq)

lemma nonempty_agree_mem:
  assumes "\<forall>a. V a \<noteq> {}"
  shows "peval Not (\<and>) (\<or>) V X \<noteq> {} \<and>
         (True \<in> peval Not (\<and>) (\<or>) V X \<longleftrightarrow> True \<in> reval V X) \<and>
         (False \<in> peval Not (\<and>) (\<or>) V X \<longleftrightarrow> False \<in> reval V X)"
proof (induction X)
  case (Atom a)
  then show ?case using assms by simp
next
  case (Neg X)
  then show ?case by (simp add: img_neg_T img_neg_F)
next
  case (Conj X Y)
  then show ?case
    using img_nonempty[of "peval Not (\<and>) (\<or>) V X" "peval Not (\<and>) (\<or>) V Y" "(\<and>)"]
          img_conj_T img_conj_F[of "peval Not (\<and>) (\<or>) V X" "peval Not (\<and>) (\<or>) V Y"]
    by simp
next
  case (Disj X Y)
  then show ?case
    using img_nonempty[of "peval Not (\<and>) (\<or>) V X" "peval Not (\<and>) (\<or>) V Y" "(\<or>)"]
          img_disj_T[of "peval Not (\<and>) (\<or>) V X" "peval Not (\<and>) (\<or>) V Y"] img_disj_F
    by simp
qed

theorem nonempty_agree:
  assumes "\<forall>a. V a \<noteq> {}"
  shows "peval Not (\<and>) (\<or>) V X = reval V X"
  using nonempty_agree_mem[OF assms, of X] by (simp add: bool_set_eq_iff)

end
