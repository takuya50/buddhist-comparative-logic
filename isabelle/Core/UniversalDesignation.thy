(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>General plurivalence under universal designation: the classical base\<close>

theory UniversalDesignation
  imports PlurivalentSemantics
begin

text \<open>
  Priest ("Plurivalent Logics", 2014, appendix) considers the variant of
  plurivalent semantics in which a formula is \<^emph>\<open>designated iff all of its
  values are designated\<close> (universal rather than existential designation).
  With positive plurivalence this changes little; with \<^emph>\<open>general\<close>
  plurivalence (the empty value set allowed) he observes that the
  alignment with the univalent \<open>e\<close>-extension "disappears in both
  directions" -- \<open>p \<and> q\<close> no longer entails \<open>p\<close>, while \<open>p\<close> now entails
  \<open>p \<or> q\<close> -- and closes: "What one can say to characterise general
  plurivalence in this case is still an open question."

  This theory proves a characterization for the encoded classical base, which
  is the case discussed by Priest.

  \<^enum> The consequence relation is that of a finite matrix: the image of the
    map \<open>bs5\<close> from \<open>PlurivalentSemantics\<close>, i.e. the four values \<open>t, f, b, e\<close> of
    Oller's AL, with designated set \<open>{t, e}\<close> (the empty value set is
    \<^emph>\<open>vacuously\<close> designated). So the logic is decidable, and it is the
    three-valued strong Kleene matrix \<open>K3\<close> (values \<open>t, b, f\<close>, only \<open>t\<close>
    designated) extended by a \<^emph>\<open>designated infectious\<close> value.
  \<^enum> Consequence has a variable-inclusion characterisation of the kind
    known for paraconsistent weak Kleene (Ciuni and Carrara 2014) and for
    the infectious extensions of FDE (Ciuni, Ferguson and Szmuc 2018):
    \<open>\<Sigma> \<Turnstile> A\<close> iff \<open>\<Sigma>\<^sub>A \<Turnstile>\<^sub>K\<^sub>3 A\<close>, where \<open>\<Sigma>\<^sub>A\<close> is the set of premises all of whose
    atoms occur in \<open>A\<close>. Premises that mention any other atom can be
    neutralised by giving that atom the empty value set.
  \<^enum> Consequently \<open>\<and>\<close>-elimination, explosion, excluded middle and modus
    ponens all fail, while \<open>\<or>\<close>-introduction holds -- the mirror image of
    positive plurivalence. Priest's own witness for the failure of
    \<open>\<and>\<close>-elimination ("let \<open>B\<close> relate \<open>q\<close> to just \<open>f\<close>, and \<open>p\<close> to nothing")
    is checked and found \<^emph>\<open>not\<close> to be a countermodel under vacuous
    designation, because \<open>p\<close> with no value is itself designated; the
    claim is right, the witness has to be \<open>p \<mapsto> {t, f}\<close>, \<open>q \<mapsto> \<emptyset>\<close>.

  Whether the same theorem holds for the whole FDE family is left open
  here; the proof below uses nothing specific to the classical base
  beyond the \<open>bs5\<close> homomorphism, so it should transfer.
\<close>

subsection \<open>Atoms and congruence\<close>

fun atoms :: "'a fm \<Rightarrow> 'a set" where
  "atoms (Atom a) = {a}"
| "atoms (Neg X) = atoms X"
| "atoms (Conj X Y) = atoms X \<union> atoms Y"
| "atoms (Disj X Y) = atoms X \<union> atoms Y"

lemma mv_eval_cong:
  assumes "\<And>a. a \<in> atoms A \<Longrightarrow> v a = w a"
  shows "mv_eval neg mconj mdisj v A = mv_eval neg mconj mdisj w A"
  using assms by (induction A) auto

subsection \<open>Universal designation\<close>

context mv_logic
begin

definition upsat :: "('a \<Rightarrow> 'v set) \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "upsat V A \<longleftrightarrow> peval neg mconj mdisj V A \<subseteq> D"

definition upentails :: "'a fm set \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "upentails \<Gamma> X \<longleftrightarrow> (\<forall>V. (\<forall>Y \<in> \<Gamma>. upsat V Y) \<longrightarrow> upsat V X)"

lemma upsat_empty: "peval neg mconj mdisj V A = {} \<Longrightarrow> upsat V A"
  by (simp add: upsat_def)

lemma upentails_refl: "upentails {A} A"
  by (simp add: upentails_def)

end

subsection \<open>Priest's examples, checked\<close>

definition V_glut_gap :: "atom \<Rightarrow> bool set" where
  "V_glut_gap a = (if a = p then {True, False} else {})"

definition V_priest :: "atom \<Rightarrow> bool set" where   \<comment> \<open>Priest's stated witness: \<open>q \<mapsto> {f}\<close>, \<open>p \<mapsto> \<emptyset>\<close>\<close>
  "V_priest a = (if a = q then {False} else {})"

lemma cl_up_conj_elim_fails: "\<not> cl.upentails {Conj (Atom p) (Atom q)} (Atom p)"
  unfolding cl.upentails_def cl.upsat_def
  by (rule notI, drule spec[of _ V_glut_gap]) (simp add: V_glut_gap_def)

lemma priest_witness_is_not_a_countermodel:
  "cl.upsat V_priest (Conj (Atom p) (Atom q))" and "cl.upsat V_priest (Atom p)"
  by (simp_all add: cl.upsat_def V_priest_def)

lemma cl_up_disj_intro: "cl.upentails {Atom p} (Disj (Atom p) (Atom q))"
  unfolding cl.upentails_def cl.upsat_def by auto

lemma cl_up_explosion_fails: "\<not> cl.upentails {Atom p, Neg (Atom p)} (Atom q)"
  unfolding cl.upentails_def cl.upsat_def
  by (rule notI, drule spec[of _ V_priest]) (simp add: V_priest_def)

lemma cl_up_mp_fails: "\<not> cl.upentails {Atom p, cl.imp (Atom p) (Atom q)} (Atom q)"
  unfolding cl.upentails_def cl.upsat_def cl.imp_def
  by (rule notI, drule spec[of _ V_priest]) (simp add: V_priest_def)

lemma cl_up_lem_fails: "\<not> cl.upentails {} (Disj (Atom p) (Neg (Atom p)))"
  unfolding cl.upentails_def cl.upsat_def
  by (rule notI, drule spec[of _ V_glut_gap]) (auto simp: V_glut_gap_def)

subsection \<open>The finite matrix\<close>

lemma subset_True_iff: "(S :: bool set) \<subseteq> {True} \<longleftrightarrow> False \<notin> S"
  by (auto simp: subset_iff all_bool_eq)

lemma subset_True_iff_bs5: "(S :: bool set) \<subseteq> {True} \<longleftrightarrow> bs5 S \<in> {Fin T, E}"
proof (cases "S = {}")
  case True then show ?thesis by (simp add: bs5_def)
next
  case False
  then have "bs5 S \<in> {Fin T, E} \<longleftrightarrow> True \<in> S \<and> False \<notin> S"
    by (auto simp: bs5_def bs_def mk_def)
  moreover from False have "False \<notin> S \<Longrightarrow> True \<in> S"
    by (metis (full_types) ex_in_conv)
  ultimately show ?thesis by (auto simp: subset_True_iff)
qed

theorem cl_upsat_matrix:
  "cl.upsat V A \<longleftrightarrow> mv_eval neg5 conj5 disj5 (bs5 \<circ> V) A \<in> {Fin T, E}"
  unfolding cl.upsat_def image_plurivalent_classical_is_fde5[symmetric] subset_True_iff_bs5 ..

lemma FinTE_not_UNIV: "{Fin T, E} \<noteq> UNIV"
  by (metis insert_iff singletonD tv5.distinct(1) tv5.inject tv4.distinct(1) UNIV_I)

global_interpretation ud: mv_logic "{Fin T, E}" neg5 conj5 disj5
  by unfold_locales (simp_all add: FinTE_not_UNIV)

definition nfree :: "('a \<Rightarrow> tv5) \<Rightarrow> bool" where
  "nfree v \<longleftrightarrow> (\<forall>a. v a \<noteq> Fin N)"

fun sb5 :: "tv5 \<Rightarrow> bool set" where
  "sb5 (Fin T) = {True}"
| "sb5 (Fin F) = {False}"
| "sb5 (Fin B) = {True, False}"
| "sb5 (Fin N) = {}"
| "sb5 E = {}"

lemma bs5_sb5: "x \<noteq> Fin N \<Longrightarrow> bs5 (sb5 x) = x"
  by (cases x rule: sb5.cases) (simp_all add: bs5_def bs_def mk_def)

theorem cl_upentails_matrix:
  "cl.upentails \<Gamma> A \<longleftrightarrow> (\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A)"
proof
  assume L: "cl.upentails \<Gamma> A"
  show "\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A"
  proof (intro allI impI)
    fix v :: "'a \<Rightarrow> tv5" assume nf: "nfree v" and prem: "\<forall>Y \<in> \<Gamma>. ud.sat v Y"
    have eq: "bs5 \<circ> (sb5 \<circ> v) = v"
      using nf by (auto simp: nfree_def fun_eq_iff bs5_sb5)
    have "\<forall>Y \<in> \<Gamma>. cl.upsat (sb5 \<circ> v) Y"
      using prem unfolding cl_upsat_matrix eq ud.sat_def ud.eval_def by simp
    then have "cl.upsat (sb5 \<circ> v) A" using L unfolding cl.upentails_def by blast
    then show "ud.sat v A" unfolding cl_upsat_matrix eq ud.sat_def ud.eval_def .
  qed
next
  assume R: "\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A"
  show "cl.upentails \<Gamma> A"
    unfolding cl.upentails_def
  proof (intro allI impI)
    fix V :: "'a \<Rightarrow> bool set" assume prem: "\<forall>Y \<in> \<Gamma>. cl.upsat V Y"
    have nf: "nfree (bs5 \<circ> V)"
      by (simp add: nfree_def image_plurivalent_classical_has_no_gap)
    have "\<forall>Y \<in> \<Gamma>. ud.sat (bs5 \<circ> V) Y"
      using prem unfolding cl_upsat_matrix ud.sat_def ud.eval_def by simp
    then have "ud.sat (bs5 \<circ> V) A" using R nf by blast
    then show "cl.upsat V A" unfolding cl_upsat_matrix ud.sat_def ud.eval_def .
  qed
qed

subsection \<open>The variable-inclusion characterisation\<close>

text \<open>
  \<open>K3\<close> here is the strong Kleene matrix presented on \<open>{T, B, F}\<close> with \<open>T\<close>
  the only designated value; the FDE tables restricted to these three
  values are the strong Kleene tables with \<open>B\<close> as the middle value
  (\<open>k3_tables\<close>), so this is \<open>K3\<close> up to renaming \<open>B\<close> as \<open>n\<close>.
\<close>

lemma k3_tables:
  "neg4 B = B" "conj4 T B = B" "conj4 B T = B" "conj4 B B = B" "conj4 B F = F" "conj4 F B = F"
  "disj4 T B = T" "disj4 B T = T" "disj4 B B = B" "disj4 B F = B" "disj4 F B = B"
  by (simp_all add: neg4_def conj4_def disj4_def mk_def)

definition k3_entails :: "'a fm set \<Rightarrow> 'a fm \<Rightarrow> bool" where
  "k3_entails \<Gamma> A \<longleftrightarrow>
     (\<forall>w :: 'a \<Rightarrow> tv4. (\<forall>a. w a \<noteq> N) \<longrightarrow>
        (\<forall>Y \<in> \<Gamma>. mv_eval neg4 conj4 disj4 w Y = T) \<longrightarrow> mv_eval neg4 conj4 disj4 w A = T)"

fun proj :: "tv5 \<Rightarrow> tv4" where
  "proj (Fin x) = x"
| "proj E = T"

lemma eval5_infect:
  "\<exists>a \<in> atoms A. v a = E \<Longrightarrow> mv_eval neg5 conj5 disj5 v A = E"
proof (induction A)
  case (Atom a) then show ?case by simp
next
  case (Neg X) then show ?case by simp
next
  case (Conj X Y)
  from Conj.prems have "(\<exists>a \<in> atoms X. v a = E) \<or> (\<exists>a \<in> atoms Y. v a = E)" by auto
  then show ?case
  proof
    assume "\<exists>a \<in> atoms X. v a = E"
    then have "mv_eval neg5 conj5 disj5 v X = E" by (rule Conj.IH(1))
    then show ?case by simp
  next
    assume "\<exists>a \<in> atoms Y. v a = E"
    then have "mv_eval neg5 conj5 disj5 v Y = E" by (rule Conj.IH(2))
    then show ?case by simp
  qed
next
  case (Disj X Y)
  from Disj.prems have "(\<exists>a \<in> atoms X. v a = E) \<or> (\<exists>a \<in> atoms Y. v a = E)" by auto
  then show ?case
  proof
    assume "\<exists>a \<in> atoms X. v a = E"
    then have "mv_eval neg5 conj5 disj5 v X = E" by (rule Disj.IH(1))
    then show ?case by simp
  next
    assume "\<exists>a \<in> atoms Y. v a = E"
    then have "mv_eval neg5 conj5 disj5 v Y = E" by (rule Disj.IH(2))
    then show ?case by simp
  qed
qed

lemma eval5_clean:
  assumes "\<forall>a \<in> atoms A. v a \<noteq> E"
  shows "mv_eval neg5 conj5 disj5 v A = Fin (mv_eval neg4 conj4 disj4 (proj \<circ> v) A)"
  using assms
proof (induction A)
  case (Atom a)
  then show ?case by (cases "v a") simp_all
qed auto

lemma ud_sat_Fin: "ud.sat v A \<Longrightarrow> mv_eval neg5 conj5 disj5 v A = Fin x \<Longrightarrow> x = T"
  unfolding ud.sat_def ud.eval_def by auto

theorem ud_variable_inclusion:
  "(\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A)
   \<longleftrightarrow> k3_entails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
proof
  assume L: "\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A"
  show "k3_entails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
    unfolding k3_entails_def
  proof (intro allI impI)
    fix w :: "'a \<Rightarrow> tv4"
    assume wN: "\<forall>a. w a \<noteq> N"
      and prem: "\<forall>Y \<in> {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A}. mv_eval neg4 conj4 disj4 w Y = T"
    define v where "v a = (if a \<in> atoms A then Fin (w a) else E)" for a
    have nf: "nfree v" using wN by (simp add: nfree_def v_def)
    have agree: "\<And>Y. atoms Y \<subseteq> atoms A \<Longrightarrow>
                  mv_eval neg4 conj4 disj4 (proj \<circ> v) Y = mv_eval neg4 conj4 disj4 w Y"
      by (rule mv_eval_cong) (auto simp: v_def)
    have "\<forall>Y \<in> \<Gamma>. ud.sat v Y"
    proof
      fix Y assume Y: "Y \<in> \<Gamma>"
      show "ud.sat v Y"
      proof (cases "atoms Y \<subseteq> atoms A")
        case True
        then have "\<forall>a \<in> atoms Y. v a \<noteq> E" by (auto simp: v_def)
        then have "mv_eval neg5 conj5 disj5 v Y = Fin (mv_eval neg4 conj4 disj4 w Y)"
          by (simp add: eval5_clean agree[OF True])
        also have "mv_eval neg4 conj4 disj4 w Y = T" using prem Y True by simp
        finally show ?thesis by (simp add: ud.sat_def ud.eval_def)
      next
        case False
        then have "\<exists>a \<in> atoms Y. v a = E" by (auto simp: v_def)
        then show ?thesis by (simp add: ud.sat_def ud.eval_def eval5_infect)
      qed
    qed
    with L nf have "ud.sat v A" by blast
    moreover have "mv_eval neg5 conj5 disj5 v A = Fin (mv_eval neg4 conj4 disj4 w A)"
      by (simp add: eval5_clean agree v_def)
    ultimately show "mv_eval neg4 conj4 disj4 w A = T" by (rule ud_sat_Fin)
  qed
next
  assume R: "k3_entails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
  show "\<forall>v. nfree v \<longrightarrow> (\<forall>Y \<in> \<Gamma>. ud.sat v Y) \<longrightarrow> ud.sat v A"
  proof (intro allI impI)
    fix v :: "'a \<Rightarrow> tv5" assume nf: "nfree v" and prem: "\<forall>Y \<in> \<Gamma>. ud.sat v Y"
    show "ud.sat v A"
    proof (cases "\<exists>a \<in> atoms A. v a = E")
      case True
      then show ?thesis by (simp add: ud.sat_def ud.eval_def eval5_infect)
    next
      case False
      define w where "w = proj \<circ> v"
      have wN: "\<forall>a. w a \<noteq> N"
      proof
        fix a show "w a \<noteq> N"
          using nf[unfolded nfree_def, rule_format, of a] unfolding w_def by (cases "v a") auto
      qed
      have "\<forall>Y \<in> {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A}. mv_eval neg4 conj4 disj4 w Y = T"
      proof
        fix Y assume "Y \<in> {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A}"
        then have Y: "Y \<in> \<Gamma>" and sub: "atoms Y \<subseteq> atoms A" by auto
        from False sub have "\<forall>a \<in> atoms Y. v a \<noteq> E" by auto
        then have "mv_eval neg5 conj5 disj5 v Y = Fin (mv_eval neg4 conj4 disj4 w Y)"
          by (simp add: eval5_clean w_def)
        with prem Y show "mv_eval neg4 conj4 disj4 w Y = T" by (auto intro: ud_sat_Fin)
      qed
      with R wN have "mv_eval neg4 conj4 disj4 w A = T" unfolding k3_entails_def by blast
      moreover from False have "mv_eval neg5 conj5 disj5 v A = Fin (mv_eval neg4 conj4 disj4 w A)"
        by (simp add: eval5_clean w_def)
      ultimately show ?thesis by (simp add: ud.sat_def ud.eval_def)
    qed
  qed
qed

theorem priest_open_question_classical:
  "cl.upentails \<Gamma> A \<longleftrightarrow> k3_entails {Y \<in> \<Gamma>. atoms Y \<subseteq> atoms A} A"
  unfolding cl_upentails_matrix ud_variable_inclusion ..

text \<open>
  Reading the characterisation back: \<open>p \<and> q \<Turnstile> p\<close> fails because the only
  premise mentions \<open>q \<notin> atoms p\<close> and is discarded, leaving \<open>\<emptyset> \<Turnstile>\<^sub>K\<^sub>3 p\<close>;
  \<open>p \<Turnstile> p \<or> q\<close> holds because the premise survives and \<open>p \<Turnstile>\<^sub>K\<^sub>3 p \<or> q\<close>.
  Explosion fails because \<open>p, \<not>p\<close> are discarded against the conclusion \<open>q\<close>.
\<close>

corollary conj_elim_explained: "\<not> k3_entails {} (Atom p)"
  unfolding k3_entails_def by (rule notI, drule spec[of _ "\<lambda>_. F"]) simp

corollary disj_intro_explained: "k3_entails {Atom p} (Disj (Atom p) (Atom q))"
  unfolding k3_entails_def by (auto simp: disj4_def mk_def)

end
