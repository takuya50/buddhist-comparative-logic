(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>A connexive reading of HS10: neither arising nor ceasing as a vacuous conditional\<close>

theory HeartSutra_Connexive
  imports FiniteLogics
begin

text \<open>
  \<open>HeartSutra_Emptiness\<close> showed that under FDE the formula-level reading of
  \<open>不生不滅\<close> forces a glut and the designation-level reading forces a gap.
  This theory tests a third option: read the negation \<open>不\<close> as governing a
  \<^emph>\<open>conditional\<close> -- "it is not the case that, if \<open>x\<close> is (with own-being),
  \<open>x\<close> arises" -- and give that conditional the \<^emph>\<open>connexive\<close> falsity condition
  of Wansing's logic \<open>C\<close>: \<open>\<not>(A \<rightarrow> B)\<close> is true exactly when \<open>A \<rightarrow> \<not>B\<close> is.
  Concretely we use the \<^emph>\<open>material connexive logic\<close> MC of Wansing and
  Unterhuber (2019), with truth and falsity tracked independently as in
  FDE: \<open>A \<rightarrow> B\<close> is true iff (\<open>A\<close> true \<open>\<longrightarrow>\<close> \<open>B\<close> true), and false iff
  (\<open>A\<close> not true or \<open>B\<close> false), which is MC's falsity clause and coincides
  with the one-state fragment of Wansing's \<open>C\<close> (2005).

  Result. Under this reading \<open>不生不滅\<close> is satisfiable with \<^emph>\<open>bivalent\<close>
  values -- no glut, no gap -- and, in a bivalent model, it is true exactly
  when the antecedent "\<open>x\<close> is, with own-being" is \<^emph>\<open>false\<close>: the pair of
  negated conditionals is vacuously true of what has no own-being. That is
  Nagarjuna's own argument (MMK 15: what has own-being could neither arise
  nor cease), recovered as a truth-table fact. With the material conditional
  instead, the same clause forces both the existence of the subject and a
  glut on "arises". Connexive negation, in other words, turns \<open>不生不滅\<close> into
  \<open>無自性\<close>.
\<close>

datatype 'a cfm =
    CAtom 'a
  | CNeg "'a cfm"
  | CConj "'a cfm" "'a cfm"
  | CDisj "'a cfm" "'a cfm"
  | CImp "'a cfm" "'a cfm"

definition cimp4 :: "tv4 \<Rightarrow> tv4 \<Rightarrow> tv4" where   \<comment> \<open>connexive: false iff \<open>A \<rightarrow> \<not>B\<close> true\<close>
  "cimp4 x y = mk (tr x \<longrightarrow> tr y) (tr x \<longrightarrow> fa y)"

definition mimp4 :: "tv4 \<Rightarrow> tv4 \<Rightarrow> tv4" where   \<comment> \<open>material over FDE, for contrast\<close>
  "mimp4 x y = disj4 (neg4 x) y"

fun ceval :: "(tv4 \<Rightarrow> tv4 \<Rightarrow> tv4) \<Rightarrow> ('a \<Rightarrow> tv4) \<Rightarrow> 'a cfm \<Rightarrow> tv4" where
  "ceval imp v (CAtom a) = v a"
| "ceval imp v (CNeg X) = neg4 (ceval imp v X)"
| "ceval imp v (CConj X Y) = conj4 (ceval imp v X) (ceval imp v Y)"
| "ceval imp v (CDisj X Y) = disj4 (ceval imp v X) (ceval imp v Y)"
| "ceval imp v (CImp X Y) = imp (ceval imp v X) (ceval imp v Y)"

definition csat :: "(tv4 \<Rightarrow> tv4 \<Rightarrow> tv4) \<Rightarrow> ('a \<Rightarrow> tv4) \<Rightarrow> 'a cfm \<Rightarrow> bool" where
  "csat imp v A \<longleftrightarrow> ceval imp v A \<in> {T, B}"

definition cvalid :: "(tv4 \<Rightarrow> tv4 \<Rightarrow> tv4) \<Rightarrow> 'a cfm \<Rightarrow> bool" where
  "cvalid imp A \<longleftrightarrow> (\<forall>v. csat imp v A)"

lemma in_TB_iff_tr: "x \<in> {T, B} \<longleftrightarrow> tr x"
  by (cases x) simp_all

lemma B_iff: "x = B \<longleftrightarrow> tr x \<and> fa x"
  by (cases x) simp_all

lemma F_iff: "x = F \<longleftrightarrow> \<not> tr x \<and> fa x"
  by (cases x) simp_all

subsection \<open>The connexive theses hold, and are not artefacts of the material conditional\<close>

theorem aristotle_connexive: "cvalid cimp4 (CNeg (CImp X (CNeg X)))"
  unfolding cvalid_def csat_def in_TB_iff_tr by (simp add: cimp4_def neg4_def)

theorem boethius_connexive: "cvalid cimp4 (CImp (CImp X Y) (CNeg (CImp X (CNeg Y))))"
  unfolding cvalid_def csat_def in_TB_iff_tr by (simp add: cimp4_def neg4_def)

definition v_pF :: "atom \<Rightarrow> tv4" where "v_pF a = F"

theorem aristotle_fails_material: "\<not> cvalid mimp4 (CNeg (CImp (CAtom p) (CNeg (CAtom p))))"
  unfolding cvalid_def
  by (rule notI, drule spec[of _ v_pF])
     (simp add: csat_def mimp4_def v_pF_def neg4_def disj4_def mk_def)

definition v_pFqT :: "atom \<Rightarrow> tv4" where "v_pFqT a = (if a = q then T else F)"

theorem connexive_not_symmetric:
  "\<not> cvalid cimp4 (CImp (CImp (CAtom p) (CAtom q)) (CImp (CAtom q) (CAtom p)))"
  unfolding cvalid_def
  by (rule notI, drule spec[of _ v_pFqT])
     (simp add: csat_def cimp4_def v_pFqT_def mk_def)

subsection \<open>HS10 under the connexive reading\<close>

text \<open>
  \<open>hs10_conn e a\<close>: "\<open>x\<close> does not arise and does not cease", with "arises"
  the atom \<open>a\<close>, "ceases" its contradictory \<open>\<not>a\<close> (as in \<open>HeartSutra_Emptiness\<close>), and
  \<open>e\<close> the atom "\<open>x\<close> is, with own-being" that both conditionals presuppose.
\<close>

definition hs10_conn :: "'a \<Rightarrow> 'a \<Rightarrow> 'a cfm" where
  "hs10_conn e a = CConj (CNeg (CImp (CAtom e) (CAtom a))) (CNeg (CImp (CAtom e) (CNeg (CAtom a))))"

theorem hs10_connexive_iff:
  "csat cimp4 v (hs10_conn e a) \<longleftrightarrow> (tr (v e) \<longrightarrow> v a = B)"
  unfolding csat_def in_TB_iff_tr hs10_conn_def B_iff
  by (simp add: cimp4_def neg4_def conj4_def) blast

theorem hs10_material_iff:
  "csat mimp4 v (hs10_conn e a) \<longleftrightarrow> tr (v e) \<and> v a = B"
  unfolding csat_def in_TB_iff_tr hs10_conn_def B_iff
  by (simp add: mimp4_def neg4_def conj4_def disj4_def) blast

text \<open>
  In a bivalent model (no gluts, no gaps) the material reading is
  unsatisfiable, while the connexive reading is satisfied exactly when the
  subject with own-being is not there.
\<close>

theorem hs10_connexive_bivalent:
  assumes "v e \<in> {T, F}" and "v a \<in> {T, F}"
  shows "csat cimp4 v (hs10_conn e a) \<longleftrightarrow> v e = F"
  using assms by (auto simp: hs10_connexive_iff)

theorem hs10_material_bivalent_unsat:
  assumes "v e \<in> {T, F}" and "v a \<in> {T, F}"
  shows "\<not> csat mimp4 v (hs10_conn e a)"
  using assms by (auto simp: hs10_material_iff)

text \<open>
  Witness: own-being absent (\<open>e = F\<close>), everything else plainly two-valued.
  This is the model in which \<open>不生不滅\<close> and \<open>無自性\<close> are the same fact.
\<close>

definition v_nosvabhava :: "atom \<Rightarrow> tv4" where
  "v_nosvabhava a = (if a = p then F else T)"

lemma hs10_connexive_witness: "csat cimp4 v_nosvabhava (hs10_conn p q)"
  by (simp add: hs10_connexive_iff v_nosvabhava_def)

end
