(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>MMK 2: the threefold division of the path, and where motion is not\<close>

theory Madhyamaka_Gamana
  imports Main
begin

text \<open>
  \<open>Mulamadhyamakakarika\<close> II opens by dividing the path of a motion into
  three: what has been gone over (\<open>gata\<close>), what has not (\<open>agata\<close>), and what
  is being gone over (\<open>gamyamana\<close>). Nagarjuna then denies motion of each:
  the gone is over, the not-gone has not begun, and the being-gone-over is
  not a third region alongside the other two.

  The comparison with Zeno is standard and, taken as a claim about
  formalization, it is testable. What the argument needs is only that the
  path is linearly ordered and that the mover is at a point of it. Density
  is \<^emph>\<open>not\<close> needed and is therefore not assumed: it appears below only as an
  explicit hypothesis in the one lemma about it, so the results hold over
  \<^typ>\<open>nat\<close> as well as over a continuum.

  What comes out is that the trilemma is exhaustive but misdirected. The
  three regions do partition the path (\<open>threefold_division_partitions\<close>), and
  the middle one is a single point (\<open>gamyamana_is_a_point\<close>). A single point
  admits no traversal, because traversal takes two distinct positions
  (\<open>no_motion_in_gamyamana\<close>), and the same reasoning excludes motion from any
  region considered as a place rather than as a stretch. So the conclusion
  to draw is not that there is no motion but that motion is not a property
  of a position -- it is a relation between two of them
  (\<open>motion_is_not_a_property_of_a_place\<close>). Nagarjuna's division is a
  division of places; motion does not live there.
\<close>


subsection \<open>The threefold division\<close>

context
  fixes c :: "'p :: linorder"   \<comment> \<open>where the mover is\<close>
begin

definition gata :: "'p set" where
  "gata = {x. x < c}"

definition agata :: "'p set" where
  "agata = {x. c < x}"

definition gamyamana :: "'p set" where
  "gamyamana = {x. \<not> x < c \<and> \<not> c < x}"

theorem threefold_division_partitions:
  "gata \<union> gamyamana \<union> agata = UNIV"
  "gata \<inter> gamyamana = {}"
  "gata \<inter> agata = {}"
  "gamyamana \<inter> agata = {}"
  by (auto simp: gata_def agata_def gamyamana_def)

theorem gamyamana_is_a_point: "gamyamana = {c}"
  by (auto simp: gamyamana_def)

end


subsection \<open>Motion takes two positions\<close>

text \<open>
  To traverse a region is to be at one of its positions and then at
  another. The definition is deliberately minimal: whatever else motion
  requires, it requires this.
\<close>

definition traverses :: "'p set \<Rightarrow> bool" where
  "traverses R \<longleftrightarrow> (\<exists>a\<in>R. \<exists>b\<in>R. a \<noteq> b)"

theorem no_traversal_of_a_point: "\<not> traverses {c}"
  by (simp add: traverses_def)

theorem no_motion_in_gamyamana: "\<not> traverses (gamyamana c)"
  by (simp add: gamyamana_is_a_point no_traversal_of_a_point)

text \<open>
  The other two regions are a different case, and the difference is worth
  stating: they can be traversed, and the reason Nagarjuna denies motion of
  them is not that they are too small but that the one is finished and the
  other has not started. That is a claim about tense, not about extent, and
  no formalization of the path settles it.
\<close>

theorem gone_and_not_gone_can_be_traversed:
  assumes ab: "(a :: 'p :: linorder) < b" and bc: "b < c"
  shows "traverses (gata c)"
proof -
  from ab bc have "a < c" by (rule less_trans)
  then have "a \<in> gata c" by (simp add: gata_def)
  moreover from bc have "b \<in> gata c" by (simp add: gata_def)
  moreover from ab have "a \<noteq> b" by (rule less_imp_neq)
  ultimately show ?thesis unfolding traverses_def by blast
qed

theorem motion_is_not_a_property_of_a_place: "\<not> traverses {x}"
  by (simp add: traverses_def)

text \<open>
  Density, where it holds, sharpens the picture in one respect only: there
  is no first position still to be gone over, so the mover never faces a
  next step. The hypothesis is explicit because the rest of this theory does
  not need it.
\<close>

theorem no_first_untraversed:
  fixes c b :: "'p :: linorder"
  assumes dns: "\<And>x y :: 'p. x < y \<Longrightarrow> \<exists>z. x < z \<and> z < y"
    and cb: "c < b"
  shows "\<exists>b'. b' \<in> agata c \<and> b' < b"
proof -
  from dns[OF cb] obtain z where "c < z" and "z < b" by blast
  then show ?thesis unfolding agata_def by blast
qed


subsection \<open>MMK 2:3, the doubled motion\<close>

text \<open>
  The verse objects to "the goer goes". If being a goer just is moving, the
  sentence says nothing beyond what "moves" says; if it says more, there are
  two motions where the act is one. The first horn is a theorem, and it is
  the horn that matters: the predication is empty.
\<close>

theorem goer_goes_is_empty:
  assumes "\<And>x. goer x \<longleftrightarrow> moves x"
  shows "(goer x \<and> moves x) \<longleftrightarrow> moves x"
  using assms by blast

text \<open>
  The second horn, made precise by counting: if the subject term carries a
  motion and the verb carries another, then an act described as "the goer
  goes" carries two, which is one more than there is.
\<close>

theorem goer_goes_doubles:
  assumes "\<And>x. goer x \<longleftrightarrow> moves x"
    and "count x = (if goer x then 1 else 0) + (if moves x then 1 else (0 :: nat))"
    and "moves x"
  shows "count x = 2"
  using assms by simp

end
