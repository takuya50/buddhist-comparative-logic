(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Universal designation for arbitrary bases: variable inclusion plus positive plurivalence\<close>

theory UniversalDesignationFDE
  imports UniversalDesignation
begin

text \<open>
  \<open>UniversalDesignation\<close> proves a characterization for the classical
  base through the \<open>bs5\<close> matrix. The proof uses nothing classical except
  that homomorphism, and this theory states the generic form:

  \<^enum> For \<^emph>\<open>every\<close> univalent base \<open>M\<close> (any \<open>mv_logic\<close> instance), general
    plurivalent consequence under universal designation is positive
    plurivalent consequence under universal designation after discarding
    every premise that mentions an atom absent from the conclusion
    (\<open>upentails_variable_inclusion\<close>). The only facts used are that the image
    lifting makes the empty value set absorbing and that a compound with
    non-empty parts is non-empty.
  \<^enum> For the FDE base, positive plurivalent consequence under universal
    designation is FDE consequence itself. This is the claim Priest makes
    in his appendix "one may check" for the map \<open>\<theta>\<close> that sends a non-empty
    set of FDE values to a single value (\<open>N\<close> if it contains \<open>N\<close>, or both
    \<open>T\<close> and \<open>F\<close>; otherwise the obvious value); we check it
    (\<open>theta_hom_conj\<close>, \<open>theta_hom_disj\<close>, \<open>theta_hom_neg\<close>,
    \<open>theta_designated\<close>), so \<open>pos_up_fde_is_fde\<close> checks Priest's appendix
    claim directly.
  \<^enum> Together: \<open>\<Sigma> \<Turnstile> A\<close> in general plurivalent FDE with universal designation
    iff \<open>{B \<in> \<Sigma>. atoms B \<subseteq> atoms A} \<Turnstile>\<^sub>F\<^sub>D\<^sub>E A\<close> (\<open>priest_open_question_fde\<close>).
    This is the FDE instance of the same variable-inclusion pattern as
    the classical characterization; there it was \<open>K3\<close>, because positive universal
    designation over \<open>{t, f}\<close> supplies a gap but no glut.
\<close>

subsection \<open>Generic facts about the image lifting\<close>

lemma peval_cong:
  assumes "\<And>a. a \<in> atoms A \<Longrightarrow> V a = W a"
  shows "peval neg mconj mdisj V A = peval neg mconj mdisj W A"
  using assms by (induction A) auto

lemma peval_empty_infect:
  "\<exists>a \<in> atoms A. V a = {} \<Longrightarrow> peval neg mconj mdisj V A = {}"
proof (induction A)
  case (Atom a) then show ?case by simp
next
  case (Neg X) then show ?case by simp
next
  case (Conj X Y)
  from Conj.prems have "(\<exists>a \<in> atoms X. V a = {}) \<or> (\<exists>a \<in> atoms Y. V a = {})" by auto
  then show ?case
  proof
    assume "\<exists>a \<in> atoms X. V a = {}"
    then have "peval neg mconj mdisj V X = {}" by (rule Conj.IH(1))
    then show ?case by simp
  next
    assume "\<exists>a \<in> atoms Y. V a = {}"
    then have "peval neg mconj mdisj V Y = {}" by (rule Conj.IH(2))
    then show ?case by simp
  qed
next
  case (Disj X Y)
  from Disj.prems have "(\<exists>a \<in> atoms X. V a = {}) \<or> (\<exists>a \<in> atoms Y. V a = {})" by auto
  then show ?case
  proof
    assume "\<exists>a \<in> atoms X. V a = {}"
    then have "peval neg mconj mdisj V X = {}" by (rule Disj.IH(1))
    then show ?case by simp
  next
    assume "\<exists>a \<in> atoms Y. V a = {}"
    then have "peval neg mconj mdisj V Y = {}" by (rule Disj.IH(2))
    then show ?case by simp
  qed
qed

lemma peval_nonempty:
  "\<forall>a \<in> atoms A. V a \<noteq> {} \<Longrightarrow> peval neg mconj mdisj V A \<noteq> {}"
  by (induction A) auto

lemma peval_sing:
  "peval neg mconj mdisj (\<lambda>a. {w a}) A = {mv_eval neg mconj mdisj w A}"
  by (induction A) auto

subsection \<open>The generic reduction\<close>

context mv_logic
begin

definition pos_upentails :: "'a fm set \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "pos_upentails \<Gamma> X \<longleftrightarrow> (\<forall>V. (\<forall>a. V a \<noteq> {}) \<longrightarrow> (\<forall>Y \<in> \<Gamma>. upsat V Y) \<longrightarrow> upsat V X)"

theorem upentails_variable_inclusion:
  "upentails \<Gamma> A \<longleftrightarrow> pos_upentails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
proof
  assume L: "upentails \<Gamma> A"
  show "pos_upentails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
    unfolding pos_upentails_def
  proof (intro allI impI)
    fix V' :: "'a \<Rightarrow> 'v set"
    assume pos: "\<forall>a. V' a \<noteq> {}" and prem: "\<forall>Y \<in> {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A}. upsat V' Y"
    define V where "V a = (if a \<in> atoms A then V' a else {})" for a
    have agree: "\<And>Y. atoms Y \<subseteq> atoms A \<Longrightarrow> peval neg mconj mdisj V Y = peval neg mconj mdisj V' Y"
      by (rule peval_cong) (auto simp: V_def)
    have "\<forall>Y \<in> \<Gamma>. upsat V Y"
    proof
      fix Y assume Y: "Y \<in> \<Gamma>"
      show "upsat V Y"
      proof (cases "atoms Y \<subseteq> atoms A")
        case True
        then show ?thesis using prem Y by (simp add: upsat_def agree)
      next
        case False
        then have "\<exists>a \<in> atoms Y. V a = {}" by (auto simp: V_def)
        then show ?thesis by (simp add: upsat_def peval_empty_infect)
      qed
    qed
    with L have "upsat V A" unfolding upentails_def by blast
    then show "upsat V' A" by (simp add: upsat_def agree)
  qed
next
  assume R: "pos_upentails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
  show "upentails \<Gamma> A"
    unfolding upentails_def
  proof (intro allI impI)
    fix V :: "'a \<Rightarrow> 'v set" assume prem: "\<forall>Y \<in> \<Gamma>. upsat V Y"
    show "upsat V A"
    proof (cases "\<exists>a \<in> atoms A. V a = {}")
      case True
      then show ?thesis by (simp add: upsat_def peval_empty_infect)
    next
      case False
      define V' where "V' a = (if V a = {} then {undefined} else V a)" for a
      have pos: "\<forall>a. V' a \<noteq> {}" by (simp add: V'_def)
      have agree: "\<And>Y. atoms Y \<subseteq> atoms A \<Longrightarrow> peval neg mconj mdisj V' Y = peval neg mconj mdisj V Y"
        using False by (intro peval_cong) (auto simp: V'_def)
      have "\<forall>Y \<in> {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A}. upsat V' Y"
        using prem by (auto simp: upsat_def agree)
      with R pos have "upsat V' A" unfolding pos_upentails_def by blast
      then show ?thesis by (simp add: upsat_def agree)
    qed
  qed
qed

end

subsection \<open>The FDE base: Priest's \<open>\<theta>\<close>, checked\<close>

definition theta_bits :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> tv4" where
  "theta_bits t b n f =
     (if n then N else if t \<and> f then N else if t then T else if f then F else B)"

definition theta :: "tv4 set \<Rightarrow> tv4" where
  "theta X = theta_bits (T \<in> X) (B \<in> X) (N \<in> X) (F \<in> X)"

lemma tv4_set_nonempty_iff: "(X :: tv4 set) \<noteq> {} \<longleftrightarrow> T \<in> X \<or> B \<in> X \<or> N \<in> X \<or> F \<in> X"
proof
  assume "X \<noteq> {}"
  then obtain x where "x \<in> X" by blast
  then show "T \<in> X \<or> B \<in> X \<or> N \<in> X \<or> F \<in> X" by (cases x) auto
qed auto

lemma theta_designated:
  "X \<noteq> {} \<Longrightarrow> (X \<subseteq> {T, B} \<longleftrightarrow> theta X \<in> {T, B})"
proof -
  assume ne: "X \<noteq> {}"
  have sub: "X \<subseteq> {T, B} \<longleftrightarrow> N \<notin> X \<and> F \<notin> X"
    by (auto) (metis tv4.exhaust)
  show ?thesis
    unfolding sub theta_def theta_bits_def
    using ne[unfolded tv4_set_nonempty_iff] by auto
qed

text \<open>Value tables of the FDE connectives, as membership conditions.\<close>

lemma conj4_eq:
  "conj4 x y = T \<longleftrightarrow> x = T \<and> y = T"
  "conj4 x y = F \<longleftrightarrow> x = F \<or> y = F \<or> (x = B \<and> y = N) \<or> (x = N \<and> y = B)"
  "conj4 x y = B \<longleftrightarrow> (x = B \<and> (y = T \<or> y = B)) \<or> (y = B \<and> (x = T \<or> x = B))"
  "conj4 x y = N \<longleftrightarrow> (x = N \<and> (y = T \<or> y = N)) \<or> (y = N \<and> (x = T \<or> x = N))"
  by (cases x; cases y; simp add: conj4_def mk_def)+

lemma disj4_eq:
  "disj4 x y = F \<longleftrightarrow> x = F \<and> y = F"
  "disj4 x y = T \<longleftrightarrow> x = T \<or> y = T \<or> (x = B \<and> y = N) \<or> (x = N \<and> y = B)"
  "disj4 x y = B \<longleftrightarrow> (x = B \<and> (y = F \<or> y = B)) \<or> (y = B \<and> (x = F \<or> x = B))"
  "disj4 x y = N \<longleftrightarrow> (x = N \<and> (y = F \<or> y = N)) \<or> (y = N \<and> (x = F \<or> x = N))"
  by (cases x; cases y; simp add: disj4_def mk_def)+

lemma neg4_eq:
  "neg4 x = T \<longleftrightarrow> x = F" "neg4 x = F \<longleftrightarrow> x = T" "neg4 x = B \<longleftrightarrow> x = B" "neg4 x = N \<longleftrightarrow> x = N"
  by (cases x; simp add: neg4_def mk_def)+

lemma tv4_eq_flip:
  "(T = conj4 x y) = (conj4 x y = T)" "(B = conj4 x y) = (conj4 x y = B)"
  "(N = conj4 x y) = (conj4 x y = N)" "(F = conj4 x y) = (conj4 x y = F)"
  "(T = disj4 x y) = (disj4 x y = T)" "(B = disj4 x y) = (disj4 x y = B)"
  "(N = disj4 x y) = (disj4 x y = N)" "(F = disj4 x y) = (disj4 x y = F)"
  "(T = neg4 x) = (neg4 x = T)" "(B = neg4 x) = (neg4 x = B)"
  "(N = neg4 x) = (neg4 x = N)" "(F = neg4 x) = (neg4 x = F)"
  by auto

lemma img_conj4_mem:
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "T \<in> (\<lambda>(x, y). conj4 x y) ` (X \<times> Y) \<longleftrightarrow> T \<in> X \<and> T \<in> Y"
    and "F \<in> (\<lambda>(x, y). conj4 x y) ` (X \<times> Y) \<longleftrightarrow> F \<in> X \<or> F \<in> Y \<or> (B \<in> X \<and> N \<in> Y) \<or> (N \<in> X \<and> B \<in> Y)"
    and "B \<in> (\<lambda>(x, y). conj4 x y) ` (X \<times> Y) \<longleftrightarrow> (B \<in> X \<and> (T \<in> Y \<or> B \<in> Y)) \<or> (B \<in> Y \<and> (T \<in> X \<or> B \<in> X))"
    and "N \<in> (\<lambda>(x, y). conj4 x y) ` (X \<times> Y) \<longleftrightarrow> (N \<in> X \<and> (T \<in> Y \<or> N \<in> Y)) \<or> (N \<in> Y \<and> (T \<in> X \<or> N \<in> X))"
  using assms by (auto simp: image_iff tv4_eq_flip conj4_eq)

lemma img_disj4_mem:
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "F \<in> (\<lambda>(x, y). disj4 x y) ` (X \<times> Y) \<longleftrightarrow> F \<in> X \<and> F \<in> Y"
    and "T \<in> (\<lambda>(x, y). disj4 x y) ` (X \<times> Y) \<longleftrightarrow> T \<in> X \<or> T \<in> Y \<or> (B \<in> X \<and> N \<in> Y) \<or> (N \<in> X \<and> B \<in> Y)"
    and "B \<in> (\<lambda>(x, y). disj4 x y) ` (X \<times> Y) \<longleftrightarrow> (B \<in> X \<and> (F \<in> Y \<or> B \<in> Y)) \<or> (B \<in> Y \<and> (F \<in> X \<or> B \<in> X))"
    and "N \<in> (\<lambda>(x, y). disj4 x y) ` (X \<times> Y) \<longleftrightarrow> (N \<in> X \<and> (F \<in> Y \<or> N \<in> Y)) \<or> (N \<in> Y \<and> (F \<in> X \<or> N \<in> X))"
  using assms by (auto simp: image_iff tv4_eq_flip disj4_eq)

lemma img_neg4_mem:
  "T \<in> neg4 ` X \<longleftrightarrow> F \<in> X" "F \<in> neg4 ` X \<longleftrightarrow> T \<in> X" "B \<in> neg4 ` X \<longleftrightarrow> B \<in> X" "N \<in> neg4 ` X \<longleftrightarrow> N \<in> X"
  by (auto simp: image_iff tv4_eq_flip neg4_eq)

lemma theta_bits_conj:
  assumes "tX \<or> bX \<or> nX \<or> fX" and "tY \<or> bY \<or> nY \<or> fY"
  shows "theta_bits (tX \<and> tY)
                    ((bX \<and> (tY \<or> bY)) \<or> (bY \<and> (tX \<or> bX)))
                    ((nX \<and> (tY \<or> nY)) \<or> (nY \<and> (tX \<or> nX)))
                    (fX \<or> fY \<or> (bX \<and> nY) \<or> (nX \<and> bY))
         = conj4 (theta_bits tX bX nX fX) (theta_bits tY bY nY fY)"
  using assms
  by (cases tX; cases bX; cases nX; cases fX; cases tY; cases bY; cases nY; cases fY)
     (simp_all add: theta_bits_def conj4_def mk_def)

lemma theta_bits_disj:
  assumes "tX \<or> bX \<or> nX \<or> fX" and "tY \<or> bY \<or> nY \<or> fY"
  shows "theta_bits (tX \<or> tY \<or> (bX \<and> nY) \<or> (nX \<and> bY))
                    ((bX \<and> (fY \<or> bY)) \<or> (bY \<and> (fX \<or> bX)))
                    ((nX \<and> (fY \<or> nY)) \<or> (nY \<and> (fX \<or> nX)))
                    (fX \<and> fY)
         = disj4 (theta_bits tX bX nX fX) (theta_bits tY bY nY fY)"
  using assms
  by (cases tX; cases bX; cases nX; cases fX; cases tY; cases bY; cases nY; cases fY)
     (simp_all add: theta_bits_def disj4_def mk_def)

lemma theta_bits_neg:
  "theta_bits f b n t = neg4 (theta_bits t b n f)"
  by (cases t; cases b; cases n; cases f) (simp_all add: theta_bits_def neg4_def mk_def)

theorem theta_hom_conj:
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "theta ((\<lambda>(x, y). conj4 x y) ` (X \<times> Y)) = conj4 (theta X) (theta Y)"
  unfolding theta_def img_conj4_mem[OF assms]
  by (rule theta_bits_conj) (use assms[unfolded tv4_set_nonempty_iff] in blast)+

theorem theta_hom_disj:
  assumes "X \<noteq> {}" "Y \<noteq> {}"
  shows "theta ((\<lambda>(x, y). disj4 x y) ` (X \<times> Y)) = disj4 (theta X) (theta Y)"
  unfolding theta_def img_disj4_mem[OF assms]
  by (rule theta_bits_disj) (use assms[unfolded tv4_set_nonempty_iff] in blast)+

theorem theta_hom_neg: "theta (neg4 ` X) = neg4 (theta X)"
  unfolding theta_def img_neg4_mem by (rule theta_bits_neg)

theorem theta_hom_eval:
  assumes "\<forall>a. V a \<noteq> {}"
  shows "theta (peval neg4 conj4 disj4 V A) = mv_eval neg4 conj4 disj4 (theta \<circ> V) A"
proof (induction A)
  case (Atom a) then show ?case by simp
next
  case (Neg X) then show ?case by (simp add: theta_hom_neg)
next
  case (Conj X Y)
  have ne: "peval neg4 conj4 disj4 V X \<noteq> {}" "peval neg4 conj4 disj4 V Y \<noteq> {}"
    using assms by (auto intro!: peval_nonempty)
  show ?case by (simp only: peval.simps mv_eval.simps theta_hom_conj[OF ne] Conj.IH)
next
  case (Disj X Y)
  have ne: "peval neg4 conj4 disj4 V X \<noteq> {}" "peval neg4 conj4 disj4 V Y \<noteq> {}"
    using assms by (auto intro!: peval_nonempty)
  show ?case by (simp only: peval.simps mv_eval.simps theta_hom_disj[OF ne] Disj.IH)
qed

theorem pos_up_fde_is_fde: "fde.pos_upentails \<Gamma> A \<longleftrightarrow> fde.entails \<Gamma> A"
proof
  assume L: "fde.pos_upentails \<Gamma> A"
  show "fde.entails \<Gamma> A"
    unfolding fde.entails_def
  proof (intro allI impI)
    fix w :: "'a \<Rightarrow> tv4" assume prem: "\<forall>Y \<in> \<Gamma>. fde.sat w Y"
    have up: "\<forall>Y \<in> \<Gamma>. fde.upsat (\<lambda>a. {w a}) Y"
      using prem by (simp add: fde.upsat_def fde.sat_def fde.eval_def peval_sing)
    have "fde.upsat (\<lambda>a. {w a}) A"
      using L[unfolded fde.pos_upentails_def, THEN spec[of _ "\<lambda>a. {w a}"]] up by simp
    then show "fde.sat w A" by (simp add: fde.upsat_def fde.sat_def fde.eval_def peval_sing)
  qed
next
  assume R: "fde.entails \<Gamma> A"
  show "fde.pos_upentails \<Gamma> A"
    unfolding fde.pos_upentails_def
  proof (intro allI impI)
    fix V :: "'a \<Rightarrow> tv4 set" assume pos: "\<forall>a. V a \<noteq> {}" and prem: "\<forall>Y \<in> \<Gamma>. fde.upsat V Y"
    have key: "\<And>Y. fde.upsat V Y \<longleftrightarrow> fde.sat (theta \<circ> V) Y"
    proof -
      fix Y
      have ne: "peval neg4 conj4 disj4 V Y \<noteq> {}" using pos by (intro peval_nonempty) simp
      show "fde.upsat V Y \<longleftrightarrow> fde.sat (theta \<circ> V) Y"
        unfolding fde.upsat_def fde.sat_def fde.eval_def theta_hom_eval[OF pos, symmetric]
        by (rule theta_designated[OF ne])
    qed
    from prem have "\<forall>Y \<in> \<Gamma>. fde.sat (theta \<circ> V) Y" by (simp add: key)
    then have "fde.sat (theta \<circ> V) A" using R unfolding fde.entails_def by blast
    then show "fde.upsat V A" by (simp add: key)
  qed
qed

theorem priest_open_question_fde:
  "fde.upentails \<Gamma> A \<longleftrightarrow> fde.entails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
  unfolding fde.upentails_variable_inclusion pos_up_fde_is_fde ..

text \<open>The two examples from Priest's appendix for the FDE base.\<close>

corollary fde_up_conj_elim_fails: "\<not> fde.upentails {Conj (Atom p) (Atom q)} (Atom p)"
proof -
  have eq: "{Y \<in> {Conj (Atom p) (Atom q)}. atoms Y \<subseteq> atoms (Atom p)} = {}" by auto
  have "\<not> fde.entails {} (Atom p)"
    unfolding fde.entails_def fde.sat_def fde.eval_def
    by (rule notI, drule spec[of _ "\<lambda>_. F"]) simp
  then show ?thesis unfolding priest_open_question_fde eq .
qed

corollary fde_up_disj_intro: "fde.upentails {Atom p} (Disj (Atom p) (Atom q))"
proof -
  have eq: "{Y \<in> {Atom p}. atoms Y \<subseteq> atoms (Disj (Atom p) (Atom q))} = {Atom p}" by auto
  have "fde.entails {Atom p} (Disj (Atom p) (Atom q))"
    unfolding fde.entails_def fde.sat_def fde.eval_def
    by (auto simp: disj4_def mk_def)
  then show ?thesis unfolding priest_open_question_fde eq .
qed

end
