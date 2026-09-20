(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The four corners, and where the fifth value sits relative to them\<close>

theory Catuskoti
  imports FiniteLogics
begin

text \<open>
  The \<open>catuskoti\<close> (four-cornered negation) distinguishes, for a claim,
  four positions: it holds (K1), it does not (K2), both (K3), neither (K4).
  We classify a truth value by the designation of it and of its negation,
  generically over any \<^locale>\<open>mv_logic\<close> instance.
\<close>

datatype koti = K1 | K2 | K3 | K4

context mv_logic
begin

definition koti_of :: "'v \<Rightarrow> koti" where
  "koti_of x =
    (if x \<in> D \<and> neg x \<notin> D then K1
     else if x \<notin> D \<and> neg x \<in> D then K2
     else if x \<in> D \<and> neg x \<in> D then K3
     else K4)"

definition realizable :: "koti \<Rightarrow> bool" where
  "realizable k \<longleftrightarrow> (\<exists>x. koti_of x = k)"

lemma koti_total: "\<exists>!k. koti_of x = k"
  by (simp add: koti_of_def)

end

lemma cl_koti: "cl.realizable k \<longleftrightarrow> k \<in> {K1, K2}"
proof
  assume "cl.realizable k"
  then obtain x where "cl.koti_of x = k" unfolding cl.realizable_def by blast
  then show "k \<in> {K1, K2}" by (cases x) (simp_all add: cl.koti_of_def)
next
  assume "k \<in> {K1, K2}"
  then show "cl.realizable k"
    unfolding cl.realizable_def cl.koti_of_def
    by (auto intro: exI[of _ True] exI[of _ False])
qed

lemma fde_koti_all: "fde.realizable k"
proof (cases k)
  case K1 then show ?thesis
    unfolding fde.realizable_def fde.koti_of_def
    by (intro exI[of _ T]) (simp add: neg4_def mk_def)
next
  case K2 then show ?thesis
    unfolding fde.realizable_def fde.koti_of_def
    by (intro exI[of _ F]) (simp add: neg4_def mk_def)
next
  case K3 then show ?thesis
    unfolding fde.realizable_def fde.koti_of_def
    by (intro exI[of _ B]) (simp add: neg4_def mk_def)
next
  case K4 then show ?thesis
    unfolding fde.realizable_def fde.koti_of_def
    by (intro exI[of _ N]) (simp add: neg4_def mk_def)
qed

text \<open>
  Priest's fifth value \<open>e\<close> is, at the level of \<^emph>\<open>designation\<close>, not a
  fifth corner: since it is undesignated in the \<open>fde5\<close> reading
  (\<open>e \<notin> D\<close>) and its own negation is likewise undesignated (\<open>neg5 E = E\<close>),
  it collapses into corner K4 ("neither"), exactly where \<open>N\<close> already sits.
  In the \<open>fde5D\<close> variant (\<open>e \<in> D\<close>) it instead collapses into K3
  ("both"), alongside \<open>B\<close>. Either way, "the fifth corner" is not a fifth
  \<^emph>\<open>koti\<close>; it is a fifth \<^emph>\<open>value\<close> that happens to land on an existing
  corner. \<^file>\<open>../../docs/STATUS.md\<close> must not claim "the catuskoti has five
  corners" on the strength of this development.
\<close>

lemma fde5_koti_of_E: "fde5.koti_of E = K4"
  unfolding fde5.koti_of_def by simp

lemma fde5D_koti_of_E: "fde5D.koti_of E = K3"
  unfolding fde5D.koti_of_def by simp

lemma fifth_corner_value_level: "E \<notin> range Fin"
  by (auto elim: tv5.exhaust)

end
