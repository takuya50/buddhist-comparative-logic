(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Proof theory for FDE and FDE5: relevance, containment, and a complete decision procedure\<close>

theory FDEProofTheory
  imports UniversalDesignation FiniteDecisionProcedures
begin

text \<open>
  \<open>FiniteDecisionProcedures\<close> decides validity and entailment for the three-atom fragment by
  enumerating all valuations. That is enough to recompute the session's
  examples but says nothing about arbitrary formulas over arbitrary atoms.
  This theory supplies the general proof theory:

  \<^enum> \<^emph>\<open>Relevance.\<close> FDE has the variable-sharing property: if \<open>X \<Turnstile> Y\<close> then
    \<open>X\<close> and \<open>Y\<close> share an atom (\<open>fde_variable_sharing\<close>). The witness is the
    pair of constant valuations that make everything a glut and everything
    a gap.
  \<^enum> \<^emph>\<open>Containment.\<close> FDE5, the logic of \<open>FiniteLogics\<close> with Priest's absorbing
    fifth value, is exactly FDE plus atom containment:
    \<open>X \<Turnstile>\<^sub>F\<^sub>D\<^sub>E\<^sub>5 Y \<longleftrightarrow> atoms Y \<subseteq> atoms X \<and> X \<Turnstile>\<^sub>F\<^sub>D\<^sub>E Y\<close>
    (\<open>fde5_is_fde_plus_containment\<close>). So FDE5 belongs to the family of
    containment logics (Parry, Bochvar, Oller's AL) -- the same family the
    plurivalent analysis in \<open>PlurivalentSemantics\<close> placed it in, now as a
    statement about the consequence relation rather than the matrix.
  \<^enum> \<^emph>\<open>Decision procedure.\<close> A signed-literal calculus in the style of the
    Belnap-Dunn "coupled trees": each signed formula is decomposed into a
    finite list of branches of signed literals, a branch being satisfiable
    exactly when it is open, because in FDE the true-bit and the false-bit
    of each atom are independent and unconstrained (\<open>open_sat\<close>). Hence
    \<open>fde_dec\<close> is sound and complete for arbitrary formulas over arbitrary
    atoms (\<open>fde_dec_correct\<close>), and with the containment test so is
    \<open>fde5_dec\<close> (\<open>fde5_dec_correct\<close>). Both are executable, and on the
    three-atom fragment they agree with the brute-force checkers of
    \<open>FiniteDecisionProcedures\<close> (\<open>decide_agree\<close>).

  The relevance result is the formal counterpart of a requirement the
  Buddhist logicians also imposed: Dignaga's first mark asks the reason to
  be a property of the subject, so an inference whose reason and thesis
  share nothing is rejected before its truth is considered
  (\<open>Dignaga_Hetucakra.anumana.paksadharmata\<close>).
\<close>

subsection \<open>Bits of the four values\<close>

lemma tr_neg4 [simp]: "tr (neg4 x) = fa x" and fa_neg4 [simp]: "fa (neg4 x) = tr x"
  by (simp_all add: neg4_def)

lemma tr_conj4 [simp]: "tr (conj4 x y) = (tr x \<and> tr y)"
  and fa_conj4 [simp]: "fa (conj4 x y) = (fa x \<or> fa y)"
  by (simp_all add: conj4_def)

lemma tr_disj4 [simp]: "tr (disj4 x y) = (tr x \<or> tr y)"
  and fa_disj4 [simp]: "fa (disj4 x y) = (fa x \<and> fa y)"
  by (simp_all add: disj4_def)

lemma in_TB_iff_tr4: "x \<in> {T, B} \<longleftrightarrow> tr x"
  by (cases x) simp_all

lemma TB_disj_iff_tr4: "(x = T \<or> x = B) \<longleftrightarrow> tr x"
  by (cases x) simp_all

lemma atoms_nonempty: "atoms X \<noteq> {}"
  by (induction X) auto

subsection \<open>Relevance: the variable-sharing property\<close>

lemma eval4_const_B: "\<forall>a \<in> atoms X. v a = B \<Longrightarrow> mv_eval neg4 conj4 disj4 v X = B"
  by (induction X) (auto simp: neg4_def conj4_def disj4_def mk_def)

lemma eval4_const_N: "\<forall>a \<in> atoms X. v a = N \<Longrightarrow> mv_eval neg4 conj4 disj4 v X = N"
  by (induction X) (auto simp: neg4_def conj4_def disj4_def mk_def)

theorem fde_variable_sharing:
  assumes "fde.entails {X} Y"
  shows "atoms X \<inter> atoms Y \<noteq> {}"
proof (rule ccontr)
  assume "\<not> atoms X \<inter> atoms Y \<noteq> {}"
  then have disj: "atoms X \<inter> atoms Y = {}" by simp
  define v where "v a = (if a \<in> atoms X then B else N)" for a
  have "mv_eval neg4 conj4 disj4 v X = B" by (rule eval4_const_B) (simp add: v_def)
  then have satX: "fde.sat v X" by (simp add: fde.sat_def fde.eval_def)
  have "mv_eval neg4 conj4 disj4 v Y = N"
    using disj by (intro eval4_const_N) (auto simp: v_def)
  then have "\<not> fde.sat v Y" by (simp add: fde.sat_def fde.eval_def)
  with satX assms show False unfolding fde.entails_def by blast
qed

text \<open>
  Sharing an atom is not sufficient: a glut on the shared atom satisfies
  the premise and not the conclusion.
\<close>

lemma sharing_not_sufficient:
  "atoms (Conj (Atom p) (Neg (Atom p))) \<inter> atoms (Conj (Atom p) (Atom q)) \<noteq> {}"
  "\<not> fde.entails {Conj (Atom p) (Neg (Atom p))} (Conj (Atom p) (Atom q))"
proof -
  show "atoms (Conj (Atom p) (Neg (Atom p))) \<inter> atoms (Conj (Atom p) (Atom q)) \<noteq> {}" by simp
  show "\<not> fde.entails {Conj (Atom p) (Neg (Atom p))} (Conj (Atom p) (Atom q))"
    unfolding fde.entails_def fde.sat_def fde.eval_def
    by (rule notI, drule spec[of _ glut_p]) (simp add: glut_p_def conj4_def neg4_def mk_def)
qed

text \<open>Neither FDE nor FDE5 has a valid formula; classically there are some.\<close>

theorem fde_no_valid_formula: "\<not> fde.valid X"
proof -
  have "mv_eval neg4 conj4 disj4 (\<lambda>_. N) X = N" by (rule eval4_const_N) simp
  then have "\<not> fde.sat (\<lambda>_. N) X" by (simp add: fde.sat_def fde.eval_def)
  then show ?thesis unfolding fde.valid_iff_all_sat by blast
qed

theorem fde5_no_valid_formula: "\<not> fde5.valid X"
proof -
  have "\<exists>a. a \<in> atoms X" using atoms_nonempty[of X] by auto
  then obtain a where a: "a \<in> atoms X" ..
  have "mv_eval neg5 conj5 disj5 (\<lambda>_. E) X = E" using a by (intro eval5_infect) auto
  then have "\<not> fde5.sat (\<lambda>_. E) X" by (simp add: fde5.sat_def fde5.eval_def)
  then show ?thesis unfolding fde5.valid_iff_all_sat by blast
qed

subsection \<open>FDE5 is FDE plus containment\<close>

lemma eval5_all_Fin:
  "mv_eval neg5 conj5 disj5 (\<lambda>a. Fin (w a)) X = Fin (mv_eval neg4 conj4 disj4 w X)"
  by (induction X) simp_all

theorem fde5_is_fde_plus_containment:
  "fde5.entails {X} Y \<longleftrightarrow> atoms Y \<subseteq> atoms X \<and> fde.entails {X} Y"
proof
  assume L: "fde5.entails {X} Y"
  have cont: "atoms Y \<subseteq> atoms X"
  proof (rule ccontr)
    assume "\<not> atoms Y \<subseteq> atoms X"
    then obtain a where a: "a \<in> atoms Y" "a \<notin> atoms X" by blast
    define v where "v b = (if b = a then E else Fin B)" for b
    have clean: "\<forall>b \<in> atoms X. v b \<noteq> E" using a by (auto simp: v_def)
    have "mv_eval neg5 conj5 disj5 v X = Fin (mv_eval neg4 conj4 disj4 (proj \<circ> v) X)"
      using clean by (rule eval5_clean)
    moreover have "mv_eval neg4 conj4 disj4 (proj \<circ> v) X = B"
      using a by (intro eval4_const_B) (auto simp: v_def)
    ultimately have "fde5.sat v X" by (simp add: fde5.sat_def fde5.eval_def)
    moreover have "mv_eval neg5 conj5 disj5 v Y = E"
      using a by (intro eval5_infect) (auto simp: v_def)
    then have "\<not> fde5.sat v Y" by (simp add: fde5.sat_def fde5.eval_def)
    ultimately show False using L unfolding fde5.entails_def by blast
  qed
  moreover have "fde.entails {X} Y"
    unfolding fde.entails_def
  proof (intro allI impI)
    fix w :: "'a \<Rightarrow> tv4" assume "\<forall>Z \<in> {X}. fde.sat w Z"
    then have "fde5.sat (\<lambda>a. Fin (w a)) X"
      by (simp add: fde.sat_def fde.eval_def fde5.sat_def fde5.eval_def eval5_all_Fin)
    then have "fde5.sat (\<lambda>a. Fin (w a)) Y" using L unfolding fde5.entails_def by blast
    then show "fde.sat w Y"
      by (simp add: fde.sat_def fde.eval_def fde5.sat_def fde5.eval_def eval5_all_Fin)
  qed
  ultimately show "atoms Y \<subseteq> atoms X \<and> fde.entails {X} Y" by blast
next
  assume R: "atoms Y \<subseteq> atoms X \<and> fde.entails {X} Y"
  show "fde5.entails {X} Y"
    unfolding fde5.entails_def
  proof (intro allI impI)
    fix v :: "'a \<Rightarrow> tv5" assume "\<forall>Z \<in> {X}. fde5.sat v Z"
    then have satX: "fde5.sat v X" by blast
    have cleanX: "\<forall>a \<in> atoms X. v a \<noteq> E"
    proof (rule ccontr)
      assume "\<not> (\<forall>a \<in> atoms X. v a \<noteq> E)"
      then have "mv_eval neg5 conj5 disj5 v X = E" by (intro eval5_infect) auto
      with satX show False by (simp add: fde5.sat_def fde5.eval_def)
    qed
    then have cleanY: "\<forall>a \<in> atoms Y. v a \<noteq> E" using R by blast
    have evX: "mv_eval neg5 conj5 disj5 v X = Fin (mv_eval neg4 conj4 disj4 (proj \<circ> v) X)"
      using cleanX by (rule eval5_clean)
    have evY: "mv_eval neg5 conj5 disj5 v Y = Fin (mv_eval neg4 conj4 disj4 (proj \<circ> v) Y)"
      using cleanY by (rule eval5_clean)
    have "fde.sat (proj \<circ> v) X"
      using satX evX by (simp add: fde5.sat_def fde5.eval_def fde.sat_def fde.eval_def)
    then have "fde.sat (proj \<circ> v) Y" using R unfolding fde.entails_def by blast
    then show "fde5.sat v Y"
      using evY by (simp add: fde5.sat_def fde5.eval_def fde.sat_def fde.eval_def)
  qed
qed

corollary fde5_variable_sharing:
  assumes "fde5.entails {X} Y"
  shows "atoms X \<inter> atoms Y \<noteq> {}"
proof -
  have "fde.entails {X} Y" using assms fde5_is_fde_plus_containment[of X Y] by blast
  then show ?thesis by (rule fde_variable_sharing)
qed

subsection \<open>Signed literals and their branches\<close>

datatype sgn = STr | SFl              \<comment> \<open>which bit of the value: at least true, at least false\<close>
datatype 'a slit = SL bool sgn 'a     \<comment> \<open>the bit is (or is not) set at this atom\<close>

fun bitv :: "sgn \<Rightarrow> tv4 \<Rightarrow> bool" where
  "bitv STr x = tr x"
| "bitv SFl x = fa x"

fun flipsgn :: "sgn \<Rightarrow> sgn" where
  "flipsgn STr = SFl"
| "flipsgn SFl = STr"

lemma bitv_neg4: "bitv s (neg4 x) = bitv (flipsgn s) x"
  by (cases s) simp_all

fun holds_lit :: "('a \<Rightarrow> tv4) \<Rightarrow> 'a slit \<Rightarrow> bool" where
  "holds_lit v (SL pol s a) = (bitv s (v a) = pol)"

fun neg_lit :: "'a slit \<Rightarrow> 'a slit" where
  "neg_lit (SL pol s a) = SL (\<not> pol) s a"

definition meetl :: "'a slit list list \<Rightarrow> 'a slit list list \<Rightarrow> 'a slit list list" where
  "meetl us ws = concat (map (\<lambda>u. map (\<lambda>w. u @ w) ws) us)"

definition satb :: "('a \<Rightarrow> tv4) \<Rightarrow> 'a slit list list \<Rightarrow> bool" where
  "satb v brs \<longleftrightarrow> (\<exists>b \<in> set brs. \<forall>l \<in> set b. holds_lit v l)"

lemma satb_single [simp]: "satb v [[l]] \<longleftrightarrow> holds_lit v l"
  by (simp add: satb_def)

lemma satb_append [simp]: "satb v (us @ ws) \<longleftrightarrow> satb v us \<or> satb v ws"
  by (auto simp: satb_def)

lemma satb_meetl [simp]: "satb v (meetl us ws) \<longleftrightarrow> satb v us \<and> satb v ws"
  by (auto simp: satb_def meetl_def)

fun expandl :: "bool \<Rightarrow> sgn \<Rightarrow> 'a fm \<Rightarrow> 'a slit list list" where
  "expandl pol s (Atom a) = [[SL pol s a]]"
| "expandl pol s (Neg X) = expandl pol (flipsgn s) X"
| "expandl pol STr (Conj X Y) =
     (if pol then meetl (expandl True STr X) (expandl True STr Y)
             else expandl False STr X @ expandl False STr Y)"
| "expandl pol SFl (Conj X Y) =
     (if pol then expandl True SFl X @ expandl True SFl Y
             else meetl (expandl False SFl X) (expandl False SFl Y))"
| "expandl pol STr (Disj X Y) =
     (if pol then expandl True STr X @ expandl True STr Y
             else meetl (expandl False STr X) (expandl False STr Y))"
| "expandl pol SFl (Disj X Y) =
     (if pol then meetl (expandl True SFl X) (expandl True SFl Y)
             else expandl False SFl X @ expandl False SFl Y)"

text \<open>
  Adequacy: a branch list produced for a signed formula is satisfied by
  exactly the valuations that give the formula the signed bit. Both
  subformulas of a binary connective are expanded at the \<^emph>\<open>same\<close> sign and
  polarity -- only negation flips the sign -- so one instance of each
  induction hypothesis suffices.
\<close>

theorem expandl_correct:
  "(bitv s (mv_eval neg4 conj4 disj4 v X) = pol) \<longleftrightarrow> satb v (expandl pol s X)"
proof (induction X arbitrary: pol s)
  case (Atom a) show ?case by simp
next
  case (Neg X) show ?case using Neg.IH[where pol = pol and s = "flipsgn s"] by (simp add: bitv_neg4)
next
  case (Conj X Y)
  show ?case
    using Conj.IH(1)[where pol = pol and s = s] Conj.IH(2)[where pol = pol and s = s]
    by (cases s; cases pol) simp_all
next
  case (Disj X Y)
  show ?case
    using Disj.IH(1)[where pol = pol and s = s] Disj.IH(2)[where pol = pol and s = s]
    by (cases s; cases pol) simp_all
qed

subsection \<open>A branch is satisfiable exactly when it is open\<close>

definition closed_lits :: "'a slit list \<Rightarrow> bool" where
  "closed_lits b \<longleftrightarrow> (\<exists>l \<in> set b. neg_lit l \<in> set b)"

lemma closed_unsat:
  assumes "closed_lits b"
  shows "\<not> (\<forall>l \<in> set b. holds_lit v l)"
proof
  assume all: "\<forall>l \<in> set b. holds_lit v l"
  from assms obtain l where l: "l \<in> set b" "neg_lit l \<in> set b"
    unfolding closed_lits_def by blast
  obtain pol s a where la: "l = SL pol s a" by (cases l)
  from all l(1) have "holds_lit v l" by blast
  with la have p1: "bitv s (v a) = pol" by simp
  from all l(2) have "holds_lit v (neg_lit l)" by blast
  with la have "bitv s (v a) = (\<not> pol)" by simp
  with p1 show False by simp
qed

text \<open>
  The converse is where FDE differs from classical logic: the two bits of
  an atom are independent and unconstrained, so any open branch is
  satisfied by reading the branch off as a valuation.
\<close>

definition branch_val :: "'a slit list \<Rightarrow> 'a \<Rightarrow> tv4" where
  "branch_val b a = mk (SL True STr a \<in> set b) (SL True SFl a \<in> set b)"

lemma branch_val_holds:
  assumes "\<not> closed_lits b"
  shows "\<forall>l \<in> set b. holds_lit (branch_val b) l"
proof -
  have "\<forall>l \<in> set b. holds_lit (branch_val b) l"
  proof
    fix l assume l: "l \<in> set b"
    obtain pol s a where la: "l = SL pol s a" by (cases l)
    show "holds_lit (branch_val b) l"
    proof (cases pol)
      case True
      with l la show ?thesis by (cases s) (simp_all add: branch_val_def)
    next
      case False
      have "SL True s a \<notin> set b"
      proof
        assume pos: "SL True s a \<in> set b"
        have "closed_lits b"
          unfolding closed_lits_def by (intro bexI[of _ "SL True s a"]) (use pos l la False in simp_all)
        with assms show False ..
      qed
      with False la show ?thesis by (cases s) (simp_all add: branch_val_def)
    qed
  qed
  then show ?thesis by blast
qed

lemma open_sat:
  "\<not> closed_lits b \<Longrightarrow> \<exists>v. \<forall>l \<in> set b. holds_lit v l"
  using branch_val_holds by blast

subsection \<open>The decision procedures\<close>

definition fde_dec :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "fde_dec X Y \<longleftrightarrow> list_all closed_lits (meetl (expandl True STr X) (expandl False STr Y))"

theorem fde_dec_correct: "fde.entails {X} Y \<longleftrightarrow> fde_dec X Y"
proof -
  define BR where "BR = meetl (expandl True STr X) (expandl False STr Y)"
  have satX: "fde.sat v X \<longleftrightarrow> satb v (expandl True STr X)" for v
    using expandl_correct[where s = STr and pol = True and v = v and X = X]
    by (simp add: fde.sat_def fde.eval_def TB_disj_iff_tr4)
  have unsatY: "(\<not> fde.sat v Y) \<longleftrightarrow> satb v (expandl False STr Y)" for v
    using expandl_correct[where s = STr and pol = False and v = v and X = Y]
    by (simp add: fde.sat_def fde.eval_def TB_disj_iff_tr4)
  have "(\<not> fde.entails {X} Y) \<longleftrightarrow> (\<exists>v. fde.sat v X \<and> \<not> fde.sat v Y)"
    unfolding fde.entails_def by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>v. satb v (expandl True STr X) \<and> satb v (expandl False STr Y))"
    using satX unsatY by blast
  also have "\<dots> \<longleftrightarrow> (\<exists>v. satb v BR)"
    unfolding BR_def by (simp add: satb_meetl)
  also have "\<dots> \<longleftrightarrow> (\<exists>b \<in> set BR. \<not> closed_lits b)"
  proof
    assume "\<exists>v. satb v BR"
    then obtain v b where b: "b \<in> set BR" "\<forall>l \<in> set b. holds_lit v l"
      unfolding satb_def by blast
    then show "\<exists>b \<in> set BR. \<not> closed_lits b" using closed_unsat by blast
  next
    assume "\<exists>b \<in> set BR. \<not> closed_lits b"
    then obtain b where b: "b \<in> set BR" "\<not> closed_lits b" by blast
    then obtain v where "\<forall>l \<in> set b. holds_lit v l" using open_sat by blast
    with b(1) show "\<exists>v. satb v BR" unfolding satb_def by blast
  qed
  also have "\<dots> \<longleftrightarrow> (\<not> fde_dec X Y)"
    unfolding fde_dec_def BR_def list_all_iff by blast
  finally show ?thesis by blast
qed

fun atomsl :: "'a fm \<Rightarrow> 'a list" where
  "atomsl (Atom a) = [a]"
| "atomsl (Neg X) = atomsl X"
| "atomsl (Conj X Y) = atomsl X @ atomsl Y"
| "atomsl (Disj X Y) = atomsl X @ atomsl Y"

lemma set_atomsl: "set (atomsl X) = atoms X"
  by (induction X) auto

definition fde5_dec :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "fde5_dec X Y \<longleftrightarrow> list_all (\<lambda>a. a \<in> set (atomsl X)) (atomsl Y) \<and> fde_dec X Y"

theorem fde5_dec_correct: "fde5.entails {X} Y \<longleftrightarrow> fde5_dec X Y"
proof -
  have "fde5.entails {X} Y \<longleftrightarrow> atoms Y \<subseteq> atoms X \<and> fde.entails {X} Y"
    by (rule fde5_is_fde_plus_containment)
  also have "\<dots> \<longleftrightarrow> list_all (\<lambda>a. a \<in> set (atomsl X)) (atomsl Y) \<and> fde_dec X Y"
    unfolding list_all_iff set_atomsl fde_dec_correct by blast
  finally show ?thesis unfolding fde5_dec_def .
qed

subsection \<open>Executable finite countermodel certificates\<close>

text \<open>
  These functions expose the witnesses of the existing branch decision
  procedure as finite data. Assignment tables can repeat an atom with the
  same value. A table is read with a default for atoms absent from the inputs;
  no enumeration of the (possibly infinite) atom type is required.
\<close>

fun assignment_val :: "'v \<Rightarrow> ('a \<times> 'v) list \<Rightarrow> 'a \<Rightarrow> 'v" where
  "assignment_val d [] a = d"
| "assignment_val d ((b, v) # rest) a = (if a = b then v else assignment_val d rest a)"

lemma assignment_val_map:
  "a \<in> set xs \<Longrightarrow> assignment_val d (map (\<lambda>b. (b, v b)) xs) a = v a"
  by (induction xs) auto

lemma eval4_agree_on_atoms:
  "(\<forall>a \<in> atoms X. v a = w a) \<Longrightarrow>
    mv_eval neg4 conj4 disj4 v X = mv_eval neg4 conj4 disj4 w X"
  by (induction X) auto

definition fde_countermodel :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> ('a \<times> tv4) list option" where
  "fde_countermodel X Y = map_option
    (\<lambda>b. map (\<lambda>a. (a, branch_val b a)) (atomsl X @ atomsl Y))
    (List.find (\<lambda>b. \<not> closed_lits b) (meetl (expandl True STr X) (expandl False STr Y)))"

lemma find_Some_member:
  "List.find P xs = Some x \<Longrightarrow> x \<in> set xs \<and> P x"
  by (auto simp: find_Some_iff)

theorem fde_countermodel_sound:
  assumes "fde_countermodel X Y = Some table"
  shows "fde.sat (assignment_val N table) X \<and> \<not> fde.sat (assignment_val N table) Y"
proof -
  from assms obtain b where b:
    "List.find (\<lambda>b. \<not> closed_lits b) (meetl (expandl True STr X) (expandl False STr Y)) = Some b"
    "table = map (\<lambda>a. (a, branch_val b a)) (atomsl X @ atomsl Y)"
    unfolding fde_countermodel_def by (cases "List.find (\<lambda>b. \<not> closed_lits b)
      (meetl (expandl True STr X) (expandl False STr Y))") auto
  from find_Some_member[OF b(1)] have bm:
    "b \<in> set (meetl (expandl True STr X) (expandl False STr Y))" "\<not> closed_lits b" by auto
  have hs: "satb (branch_val b) (meetl (expandl True STr X) (expandl False STr Y))"
    using bm branch_val_holds[OF bm(2)] unfolding satb_def by blast
  have hx: "bitv STr (mv_eval neg4 conj4 disj4 (branch_val b) X) = True"
    using hs expandl_correct[where s = STr and pol = True and v = "branch_val b" and X = X]
    by simp
  have hy: "bitv STr (mv_eval neg4 conj4 disj4 (branch_val b) Y) = False"
    using hs expandl_correct[where s = STr and pol = False and v = "branch_val b" and X = Y]
    by simp
  have agree: "assignment_val N table a = branch_val b a" if "a \<in> atoms X \<union> atoms Y" for a
  proof (subst b(2), rule assignment_val_map)
    show "a \<in> set (atomsl X @ atomsl Y)" using that by (simp add: set_atomsl)
  qed
  have ex: "mv_eval neg4 conj4 disj4 (assignment_val N table) X =
      mv_eval neg4 conj4 disj4 (branch_val b) X"
    by (rule eval4_agree_on_atoms) (use agree in auto)
  have ey: "mv_eval neg4 conj4 disj4 (assignment_val N table) Y =
      mv_eval neg4 conj4 disj4 (branch_val b) Y"
    by (rule eval4_agree_on_atoms) (use agree in auto)
  show ?thesis using hx hy
    by (simp add: fde.sat_def fde.eval_def ex ey TB_disj_iff_tr4)
qed

theorem fde_countermodel_none_iff:
  "fde_countermodel X Y = None \<longleftrightarrow> fde.entails {X} Y"
  by (auto simp: fde_countermodel_def find_None_iff fde_dec_correct fde_dec_def list_all_iff)

theorem fde_countermodel_complete:
  "(\<exists>table. fde_countermodel X Y = Some table) \<longleftrightarrow> \<not> fde.entails {X} Y"
  using fde_countermodel_none_iff[of X Y] by (cases "fde_countermodel X Y") auto

datatype 'a countermodel5 = AtomEscape 'a | FDEWitness "('a \<times> tv4) list"

fun countermodel5_table :: "'a countermodel5 \<Rightarrow> ('a \<times> tv5) list" where
  "countermodel5_table (AtomEscape a) = [(a, E)]"
| "countermodel5_table (FDEWitness table) = map (\<lambda>(a,v). (a, Fin v)) table"

fun countermodel5_default :: "'a countermodel5 \<Rightarrow> tv5" where
  "countermodel5_default (AtomEscape a) = Fin B"
| "countermodel5_default (FDEWitness table) = Fin N"

definition countermodel5_val :: "'a countermodel5 \<Rightarrow> 'a \<Rightarrow> tv5" where
  "countermodel5_val c = assignment_val (countermodel5_default c) (countermodel5_table c)"

lemma countermodel5_val_escape [simp]:
  "countermodel5_val (AtomEscape a) b = (if b = a then E else Fin B)"
  by (simp add: countermodel5_val_def)

lemma assignment_val_lift:
  "assignment_val (Fin N) (map (\<lambda>(a,v). (a, Fin v)) table) a = Fin (assignment_val N table a)"
  by (induction table) (auto split: prod.splits)

lemma countermodel5_val_fde [simp]:
  "countermodel5_val (FDEWitness table) a = Fin (assignment_val N table a)"
  by (simp add: countermodel5_val_def assignment_val_lift)

definition fde5_countermodel :: "'a fm \<Rightarrow> 'a fm \<Rightarrow> 'a countermodel5 option" where
  "fde5_countermodel X Y = (case List.find (\<lambda>a. a \<notin> set (atomsl X)) (atomsl Y) of
    Some a \<Rightarrow> Some (AtomEscape a)
  | None \<Rightarrow> map_option FDEWitness (fde_countermodel X Y))"

theorem fde5_countermodel_sound:
  assumes "fde5_countermodel X Y = Some c"
  shows "fde5.sat (countermodel5_val c) X \<and> \<not> fde5.sat (countermodel5_val c) Y"
proof (cases "List.find (\<lambda>a. a \<notin> set (atomsl X)) (atomsl Y)")
  case (Some a)
  from assms Some have c: "c = AtomEscape a" by (simp add: fde5_countermodel_def)
  from find_Some_member[OF Some] have a: "a \<in> atoms Y" "a \<notin> atoms X"
    by (auto simp: set_atomsl)
  have clean: "\<forall>b \<in> atoms X. countermodel5_val c b \<noteq> E" using a by (auto simp: c)
  have ex: "mv_eval neg5 conj5 disj5 (countermodel5_val c) X =
      Fin (mv_eval neg4 conj4 disj4 (proj \<circ> countermodel5_val c) X)"
    using clean by (rule eval5_clean)
  have exB: "mv_eval neg4 conj4 disj4 (proj \<circ> countermodel5_val c) X = B"
    using a by (intro eval4_const_B) (auto simp: c)
  have ey: "mv_eval neg5 conj5 disj5 (countermodel5_val c) Y = E"
    using a by (intro eval5_infect) (auto simp: c)
  show ?thesis by (simp add: fde5.sat_def fde5.eval_def ex exB ey)
next
  case None
  from assms None obtain table where table: "fde_countermodel X Y = Some table" "c = FDEWitness table"
    by (cases "fde_countermodel X Y") (auto simp: fde5_countermodel_def)
  have val: "countermodel5_val c = (\<lambda>a. Fin (assignment_val N table a))"
    by (rule ext) (simp add: table(2))
  show ?thesis using fde_countermodel_sound[OF table(1)]
    by (simp add: fde5.sat_def fde5.eval_def val eval5_all_Fin fde.sat_def fde.eval_def)
qed

theorem fde5_countermodel_none_iff:
  "fde5_countermodel X Y = None \<longleftrightarrow> fde5.entails {X} Y"
proof (cases "List.find (\<lambda>a. a \<notin> set (atomsl X)) (atomsl Y)")
  case None
  then have "atoms Y \<subseteq> atoms X" by (auto simp: find_None_iff set_atomsl)
  with None show ?thesis by (simp add: fde5_countermodel_def fde_countermodel_none_iff fde5_is_fde_plus_containment)
next
  case (Some a)
  then have "\<not> atoms Y \<subseteq> atoms X" using find_Some_member[OF Some] by (auto simp: set_atomsl)
  with Some show ?thesis by (simp add: fde5_countermodel_def fde5_is_fde_plus_containment)
qed

theorem fde5_countermodel_complete:
  "(\<exists>c. fde5_countermodel X Y = Some c) \<longleftrightarrow> \<not> fde5.entails {X} Y"
  using fde5_countermodel_none_iff[of X Y] by (cases "fde5_countermodel X Y") auto

subsection \<open>Agreement with the brute-force checkers, and worked examples\<close>

theorem decide_agree: "entails4 [X] Y \<longleftrightarrow> fde_dec X Y"
  using entails4_correct[of "[X]" Y] fde_dec_correct[of X Y] by simp

lemma dec_mp: "\<not> fde_dec (Conj (Atom p) (Disj (Neg (Atom p)) (Atom q))) (Atom q)" by eval
lemma dec_explosion: "\<not> fde_dec (Conj (Atom p) (Neg (Atom p))) (Atom q)" by eval
lemma dec_conj_elim: "fde_dec (Conj (Atom p) (Atom q)) (Atom p)" by eval
lemma dec_disj_intro: "fde_dec (Atom p) (Disj (Atom p) (Atom q))" by eval
lemma dec_demorgan: "fde_dec (Neg (Conj (Atom p) (Atom q))) (Disj (Neg (Atom p)) (Neg (Atom q)))" by eval
lemma dec_double_neg: "fde_dec (Neg (Neg (Atom p))) (Atom p)" by eval
lemma dec_distribution:
  "fde_dec (Conj (Atom p) (Disj (Atom q) (Atom r))) (Disj (Conj (Atom p) (Atom q)) (Conj (Atom p) (Atom r)))"
  by eval

text \<open>
  Containment separates the two logics on an FDE-valid step: disjunction
  introduction is FDE-valid but not FDE5-valid, because the new disjunct
  brings in an atom the premise does not contain.
\<close>

lemma dec5_disj_intro_fails: "\<not> fde5_dec (Atom p) (Disj (Atom p) (Atom q))" by eval
lemma dec5_conj_elim: "fde5_dec (Conj (Atom p) (Atom q)) (Atom p)" by eval
lemma dec5_double_neg: "fde5_dec (Neg (Neg (Atom p))) (Atom p)" by eval

lemma countermodel_explosion:
  "fde_countermodel (Conj (Atom p) (Neg (Atom p))) (Atom q) = Some [(p,B), (p,B), (q,N)]" by code_simp

lemma countermodel_conj_elim:
  "fde_countermodel (Conj (Atom p) (Atom q)) (Atom p) = None" by code_simp

lemma countermodel5_atom_escape:
  "fde5_countermodel (Atom p) (Disj (Atom p) (Atom q)) = Some (AtomEscape q)" by code_simp

lemma countermodel5_valid_conj:
  "fde5_countermodel (Conj (Atom p) (Neg (Atom p))) (Neg (Atom p)) = None" by code_simp

lemma countermodel5_same_atoms:
  "fde5_countermodel (Atom p) (Neg (Atom p)) = Some (FDEWitness [(p,T), (p,T)])" by code_simp

end
