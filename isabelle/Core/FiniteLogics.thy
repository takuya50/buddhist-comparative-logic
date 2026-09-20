(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Three semantics: classical, Belnap-Dunn FDE, and FDE plus a fifth value\<close>

theory FiniteLogics
  imports ManyValuedLogic
begin

text \<open>
  Truth tables adopted here (recorded so the choice is a visible parameter,
  not an implicit assumption):

  \<^item> \<open>tv4\<close> is Belnap and Dunn's four values \<open>{T, B, N, F}\<close> (Belnap 1977),
    ordered by the truth order \<open>F < B, N < T\<close> (B and N incomparable);
    \<open>conj4\<close>/\<open>disj4\<close> are meet/join of that order, so \<open>B \<sqinter> N = F\<close> and
    \<open>B \<squnion> N = T\<close>; negation swaps \<open>T\<close>/\<open>F\<close> and fixes \<open>B\<close>, \<open>N\<close>.
    Designated set \<open>D = {T, B}\<close> ("at least true").
  \<^item> \<open>tv5\<close> adds Priest's fifth, "ineffable" value \<open>e\<close> (Priest, The Fifth
    Corner of Four, 2018, ch. 5; Priest, Plurivalent Logics, 2014): \<open>e\<close> is
    absorbing for \<open>\<sqinter>\<close> and \<open>\<squnion>\<close> and self-dual under negation. We adopt
    \<open>e \<notin> D\<close> (interpretation \<open>fde5\<close>) as the primary reading, and record the
    variant \<open>e \<in> D\<close> (interpretation \<open>fde5D\<close>) side by side so the
    designation choice for \<open>e\<close> is a parameter rather than a silent decision;
    see \<open>Catuskoti\<close> for where the two variants diverge.

  Exact section/page references for Priest (2018) should be checked against
  the book before being quoted in docs/STATUS.md; this theory only commits to
  the truth tables, not to a page number.
\<close>

subsection \<open>Belnap-Dunn four-valued semantics\<close>

datatype tv4 = T | B | N | F

fun tr :: "tv4 \<Rightarrow> bool" where
  "tr T = True" | "tr B = True" | "tr N = False" | "tr F = False"

fun fa :: "tv4 \<Rightarrow> bool" where
  "fa T = False" | "fa B = True" | "fa N = False" | "fa F = True"

definition mk :: "bool \<Rightarrow> bool \<Rightarrow> tv4" where
  "mk t f = (if t \<and> \<not>f then T else if t \<and> f then B else if \<not>t \<and> \<not>f then N else F)"

lemma mk_tr_fa [simp]: "mk (tr x) (fa x) = x"
  by (cases x) (simp_all add: mk_def)

lemma tr_mk [simp]: "tr (mk t f) = t" and fa_mk [simp]: "fa (mk t f) = f"
  by (simp_all add: mk_def)

definition neg4 :: "tv4 \<Rightarrow> tv4" where
  "neg4 x = mk (fa x) (tr x)"

definition conj4 :: "tv4 \<Rightarrow> tv4 \<Rightarrow> tv4" where
  "conj4 x y = mk (tr x \<and> tr y) (fa x \<or> fa y)"

definition disj4 :: "tv4 \<Rightarrow> tv4 \<Rightarrow> tv4" where
  "disj4 x y = mk (tr x \<or> tr y) (fa x \<and> fa y)"

definition tv4s :: "tv4 list" where "tv4s = [T, B, N, F]"

text \<open>Sample truth tables, printed for the generated document.\<close>

value "map (\<lambda>x. (x, neg4 x)) tv4s"
value "map (\<lambda>(x,y). (x, y, conj4 x y)) (List.product tv4s tv4s)"
value "map (\<lambda>(x,y). (x, y, disj4 x y)) (List.product tv4s tv4s)"

lemma conj4_B_N [simp]: "conj4 B N = F" and disj4_B_N [simp]: "disj4 B N = T"
  by (simp_all add: conj4_def disj4_def mk_def)

lemma TB_not_UNIV: "{T, B} \<noteq> UNIV"
proof
  assume "{T, B} = UNIV"
  then have "N \<in> {T, B}" by simp
  then show False by simp
qed

subsection \<open>Priest's fifth, ineffable value\<close>

datatype tv5 = Fin tv4 | E

fun neg5 :: "tv5 \<Rightarrow> tv5" where
  "neg5 (Fin x) = Fin (neg4 x)" | "neg5 E = E"

fun conj5 :: "tv5 \<Rightarrow> tv5 \<Rightarrow> tv5" where
  "conj5 (Fin x) (Fin y) = Fin (conj4 x y)" | "conj5 _ _ = E"

fun disj5 :: "tv5 \<Rightarrow> tv5 \<Rightarrow> tv5" where
  "disj5 (Fin x) (Fin y) = Fin (disj4 x y)" | "disj5 _ _ = E"

lemma conj5_E_left [simp]: "conj5 E y = E"
  by (cases y) simp_all

lemma conj5_E_right [simp]: "conj5 x E = E"
  by (cases x) simp_all

lemma disj5_E_left [simp]: "disj5 E y = E"
  by (cases y) simp_all

lemma disj5_E_right [simp]: "disj5 x E = E"
  by (cases x) simp_all

lemma fde5_E_absorbing: "neg5 E = E \<and> conj5 E y = E \<and> conj5 x E = E \<and> disj5 E y = E \<and> disj5 x E = E"
  by simp

lemma FinTB_not_UNIV: "{Fin T, Fin B} \<noteq> UNIV"
proof
  assume "{Fin T, Fin B} = UNIV"
  then have "E \<in> {Fin T, Fin B}" by simp
  then show False by simp
qed

lemma FinTBE_not_UNIV: "{Fin T, Fin B, E} \<noteq> UNIV"
proof
  assume "{Fin T, Fin B, E} = UNIV"
  then have "Fin N \<in> {Fin T, Fin B, E}" by simp
  then show False by simp
qed

subsection \<open>Classical embedding\<close>

definition emb :: "bool \<Rightarrow> tv4" where
  "emb b = (if b then T else F)"

lemma emb_neg [simp]: "neg4 (emb b) = emb (\<not> b)"
  by (cases b) (simp_all add: emb_def neg4_def mk_def)

lemma emb_conj [simp]: "conj4 (emb a) (emb b) = emb (a \<and> b)"
  by (cases a; cases b) (simp_all add: emb_def conj4_def mk_def)

lemma emb_disj [simp]: "disj4 (emb a) (emb b) = emb (a \<or> b)"
  by (cases a; cases b) (simp_all add: emb_def disj4_def mk_def)

lemma emb_range: "emb b \<in> {T, F}"
  by (simp add: emb_def)

lemma emb_TB_iff: "emb b \<in> {T, B} \<longleftrightarrow> b"
  by (simp add: emb_def)

lemma emb_hom: "mv_eval neg4 conj4 disj4 (emb \<circ> v) A = emb (mv_eval Not (\<and>) (\<or>) v A)"
  by (induct A) simp_all

subsection \<open>Three logics (and one variant) as instances of \<^locale>\<open>mv_logic\<close>\<close>

datatype atom = p | q | r

lemma True_not_UNIV: "{True} \<noteq> UNIV"
proof
  assume "{True} = UNIV" then have "False \<in> {True}" by simp then show False by simp
qed

global_interpretation cl: mv_logic "{True}" "Not" "(\<and>)" "(\<or>)"
  by unfold_locales (simp, rule True_not_UNIV)

global_interpretation fde: mv_logic "{T, B}" neg4 conj4 disj4
  by unfold_locales (simp, rule TB_not_UNIV)

global_interpretation fde5: mv_logic "{Fin T, Fin B}" neg5 conj5 disj5
  by unfold_locales (simp, rule FinTB_not_UNIV)

global_interpretation fde5D: mv_logic "{Fin T, Fin B, E}" neg5 conj5 disj5
  by unfold_locales (simp, rule FinTBE_not_UNIV)

lemma fde_conservative_over_cl:
  "cl.sat v A \<longleftrightarrow> fde.sat (emb \<circ> v) A"
  unfolding cl.sat_def fde.sat_def cl.eval_def fde.eval_def emb_hom emb_TB_iff by simp

subsection \<open>Explosion, modus ponens, and the law of excluded middle\<close>

text \<open>
  Classical entailment explodes from a contradiction; FDE does not, because
  a "glut" (both true and false, value \<open>B\<close>) can satisfy \<open>p\<close> and \<open>\<not>p\<close>
  together without forcing every \<open>q\<close> to be designated. The same glut is
  the witness for Cotnoir's objection (Cotnoir 2015): FDE's material
  conditional does not validate modus ponens.
\<close>

lemma cl_explosion: "cl.entails {Atom p, Neg (Atom p)} (Atom q)"
  unfolding cl.entails_def cl.sat_def cl.eval_def by simp

definition glut_p :: "atom \<Rightarrow> tv4" where
  "glut_p a = (if a = p then B else F)"

lemma fde_no_explosion: "\<not> fde.entails {Atom p, Neg (Atom p)} (Atom q)"
proof -
  have "fde.sat glut_p (Atom p)" "fde.sat glut_p (Neg (Atom p))" "\<not> fde.sat glut_p (Atom q)"
    unfolding fde.sat_def fde.eval_def glut_p_def neg4_def mk_def by simp_all
  then show ?thesis unfolding fde.entails_def by blast
qed

lemma cl_mp: "cl.entails {Atom p, cl.imp (Atom p) (Atom q)} (Atom q)"
  unfolding cl.entails_def cl.sat_def cl.eval_def cl.imp_def by simp

lemma fde_mp_fails: "\<not> fde.entails {Atom p, fde.imp (Atom p) (Atom q)} (Atom q)"
proof -
  have "fde.sat glut_p (Atom p)"
    unfolding fde.sat_def fde.eval_def glut_p_def by simp
  moreover have "fde.sat glut_p (fde.imp (Atom p) (Atom q))"
    unfolding fde.sat_def fde.eval_def fde.imp_def glut_p_def
    by (simp add: neg4_def disj4_def mk_def)
  moreover have "\<not> fde.sat glut_p (Atom q)"
    unfolding fde.sat_def fde.eval_def glut_p_def by simp
  ultimately show ?thesis unfolding fde.entails_def by blast
qed

text \<open>
  Nitpick regression. On the set-based \<open>fde.entails\<close> statement Nitpick
  reports only a "potentially spurious" countermodel (the conjecture lies
  outside its supported fragment), so the regression is stated on the
  equivalent explicitly quantified form, where Nitpick finds a genuine
  countermodel (\<open>p := B, q := N\<close>). If it ever stops finding one, the
  truth tables have changed and \<open>fde_mp_fails\<close> should be re-examined.
\<close>

lemma "\<forall>v :: atom \<Rightarrow> tv4.
         fde.sat v (Atom p) \<and> fde.sat v (fde.imp (Atom p) (Atom q)) \<longrightarrow> fde.sat v (Atom q)"
  nitpick [card atom = 3, expect = genuine, timeout = 120]
  \<comment> \<open>Deliberate. The statement is false (it is the negation of \<open>fde_mp_fails\<close>,
    proved above), so no proof is attempted; \<open>oops\<close> only discards the goal.
    \<open>expect = genuine\<close> makes the session fail if Nitpick stops finding a
    countermodel, so this block is a checked regression, not an unfinished proof.\<close>
  oops

definition glut5_p :: "atom \<Rightarrow> tv5" where
  "glut5_p a = (if a = p then Fin B else Fin F)"

lemma fde5_mp_fails: "\<not> fde5.entails {Atom p, fde5.imp (Atom p) (Atom q)} (Atom q)"
proof -
  have "fde5.sat glut5_p (Atom p)"
    unfolding fde5.sat_def fde5.eval_def glut5_p_def by simp
  moreover have "fde5.sat glut5_p (fde5.imp (Atom p) (Atom q))"
    unfolding fde5.sat_def fde5.eval_def fde5.imp_def glut5_p_def
    by (simp add: neg4_def disj4_def mk_def)
  moreover have "\<not> fde5.sat glut5_p (Atom q)"
    unfolding fde5.sat_def fde5.eval_def glut5_p_def by simp
  ultimately show ?thesis unfolding fde5.entails_def by blast
qed

text \<open>
  Nitpick regression for FDE5, stated on the explicitly quantified form for
  the same reason as above (countermodel \<open>p := Fin B, q := Fin N\<close>). The proved
  counterpart is \<open>fde5_mp_fails\<close>. These two blocks are the only uses of
  \<open>oops\<close> in the session; both are guarded by \<open>expect = genuine\<close>, and
  \<^file>\<open>../../tools/check_names.py\<close> rejects any \<open>oops\<close> not preceded by a Nitpick call.
\<close>

lemma "\<forall>v :: atom \<Rightarrow> tv5.
         fde5.sat v (Atom p) \<and> fde5.sat v (fde5.imp (Atom p) (Atom q)) \<longrightarrow> fde5.sat v (Atom q)"
  nitpick [card atom = 3, expect = genuine, timeout = 120]
  \<comment> \<open>Deliberate; see the note above \<open>fde_mp_fails\<close>'s regression block.\<close>
  oops

text \<open>Modus ponens is recovered on bivalent valuations: its failure needs a glut.\<close>

lemma fde_mp_bivalent:
  assumes bival: "range v \<subseteq> {T, F}"
      and A: "fde.sat v A" and AB: "fde.sat v (fde.imp A C)"
  shows "fde.sat v C"
proof -
  define w where "w = (\<lambda>a. v a = T)"
  have vw: "v = emb \<circ> w"
  proof
    fix a
    from bival have "v a \<in> {T, F}" by auto
    then show "v a = (emb \<circ> w) a" by (auto simp: emb_def w_def)
  qed
  have "cl.sat w A" using A unfolding vw by (simp add: fde_conservative_over_cl)
  moreover have "cl.sat w (cl.imp A C)"
    using AB unfolding vw fde.imp_def cl.imp_def by (simp add: fde_conservative_over_cl)
  ultimately have "cl.sat w C"
    unfolding cl.sat_def cl.eval_def cl.imp_def by simp
  then show ?thesis unfolding vw by (simp add: fde_conservative_over_cl)
qed

lemma fde_lem_fails: "\<not> fde.valid (Disj (Atom p) (Neg (Atom p)))"
proof -
  have "\<not> fde.sat (\<lambda>_. N) (Disj (Atom p) (Neg (Atom p)))"
    unfolding fde.sat_def fde.eval_def by (simp add: neg4_def disj4_def mk_def)
  then show ?thesis using fde.valid_iff_all_sat by blast
qed

text \<open>
  The biconditional tracks co-designation classically but not in FDE: with
  a glut on \<open>p\<close> and \<open>q\<close> plainly false, both directions of the material
  biconditional are designated although the two sides are not.
\<close>

lemma cl_iff_fm_sat: "cl.sat v (cl.iff_fm X Y) \<longleftrightarrow> (cl.sat v X \<longleftrightarrow> cl.sat v Y)"
  by (simp add: cl.iff_fm_def cl.imp_def cl.sat_def cl.eval_def) blast

lemma fde_iff_fm_not_equivalence:
  "fde.sat glut_p (fde.iff_fm (Atom p) (Atom q))"
  "fde.sat glut_p (Atom p)" "\<not> fde.sat glut_p (Atom q)"
  by (simp_all add: fde.iff_fm_def fde.imp_def fde.sat_def fde.eval_def
                    glut_p_def neg4_def conj4_def disj4_def mk_def)

lemma cl_lem: "cl.valid (Disj (Atom p) (Neg (Atom p)))"
  unfolding cl.valid_iff_all_sat cl.sat_def cl.eval_def by simp

end
