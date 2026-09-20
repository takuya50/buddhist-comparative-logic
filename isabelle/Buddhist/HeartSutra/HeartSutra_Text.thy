(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>Text layer: the 262-character recension segmented into clauses\<close>

theory HeartSutra_Text
  imports Main
begin

text \<open>
  This theory fixes the base text: Xuanzang's short recension of the
  Prajnaparamitahrdaya (T251), 262 characters in the popularly transmitted
  form (which includes the two characters 一切 in the phrase
  遠離一切顛倒夢想; the Taisho
  critical edition of T251 omits those two characters, giving 260). Each
  clause below carries the character count of the transmitted form.

  The Chinese text itself is not stored as an Isabelle string literal
  (Isabelle's ASCII lexer does not accept CJK identifiers or \<open>''...''\<close>
  literals containing them cleanly); it lives in these \<open>text\<close>
  cartouches and in \<^file>\<open>../../../docs/STATUS.md\<close>, whose clause table is
  cross-checked against the numbers declared here by
  \<^file>\<open>../../../tools/check_text.py\<close>.

  HS00 (title) and HS30 (colophon) are not part of the 262-character body;
  they are included in the clause enumeration so that every character of
  the received document, not only the sutra's argument, has a formal
  counterpart (Defined) in \<^file>\<open>HeartSutra_Coverage.thy\<close>.
\<close>

datatype clause =
    HS00 | HS01 | HS02 | HS03 | HS04 | HS05 | HS06 | HS07 | HS08 | HS09
  | HS10 | HS11 | HS12 | HS13 | HS14 | HS15 | HS16 | HS17 | HS18 | HS19
  | HS20 | HS21 | HS22 | HS23 | HS24 | HS25 | HS26 | HS27 | HS28 | HS29
  | HS30

text \<open>
  HS00 般若波羅蜜多心經 (title, 8, not in body)
  HS01 觀自在菩薩 (5)
  HS02 行深般若波羅蜜多時 (9)
  HS03 照見五蘊皆空 (6)
  HS04 度一切苦厄 (5)
  HS05 舍利子 (3)
  HS06 色不異空 空不異色 (8)
  HS07 色即是空 空即是色 (8)
  HS08 受想行識 亦復如是 (8)
  HS09 舍利子 是諸法空相 (8)
  HS10 不生不滅 不垢不淨 不增不減 (12)
  HS11 是故空中無色 無受想行識 (11)
  HS12 無眼耳鼻舌身意 (7)
  HS13 無色聲香味觸法 (7)
  HS14 無眼界 乃至無意識界 (9)
  HS15 無無明 亦無無明盡 (8)
  HS16 乃至無老死 亦無老死盡 (10)
  HS17 無苦集滅道 (5)
  HS18 無智亦無得 (5)
  HS19 以無所得故 (5)
  HS20 菩提薩埵 依般若波羅蜜多故 (12)
  HS21 心無罣礙 無罣礙故 無有恐怖 (12)
  HS22 遠離一切顛倒夢想 究竟涅槃 (12)
  HS23 三世諸佛 依般若波羅蜜多故 (12)
  HS24 得阿耨多羅三藐三菩提 (10)
  HS25 故知般若波羅蜜多 是大神咒 是大明咒 是無上咒 是無等等咒 (25)
  HS26 能除一切苦 (5)
  HS27 真實不虛 (4)
  HS28 故說般若波羅蜜多咒 即說咒曰 (13)
  HS29 揭諦揭諦 波羅揭諦 波羅僧揭諦 菩提薩婆訶 (18)
  HS30 般若心經 (colophon, 4, not in body)
\<close>

definition clauses :: "clause list" where
  "clauses =
    [HS00, HS01, HS02, HS03, HS04, HS05, HS06, HS07, HS08, HS09,
     HS10, HS11, HS12, HS13, HS14, HS15, HS16, HS17, HS18, HS19,
     HS20, HS21, HS22, HS23, HS24, HS25, HS26, HS27, HS28, HS29, HS30]"

definition body :: "clause list" where
  "body =
    [HS01, HS02, HS03, HS04, HS05, HS06, HS07, HS08, HS09,
     HS10, HS11, HS12, HS13, HS14, HS15, HS16, HS17, HS18, HS19,
     HS20, HS21, HS22, HS23, HS24, HS25, HS26, HS27, HS28, HS29]"

fun char_count :: "clause \<Rightarrow> nat" where
  "char_count HS00 = 8" | "char_count HS01 = 5" | "char_count HS02 = 9"
| "char_count HS03 = 6" | "char_count HS04 = 5" | "char_count HS05 = 3"
| "char_count HS06 = 8" | "char_count HS07 = 8" | "char_count HS08 = 8"
| "char_count HS09 = 8" | "char_count HS10 = 12" | "char_count HS11 = 11"
| "char_count HS12 = 7" | "char_count HS13 = 7" | "char_count HS14 = 9"
| "char_count HS15 = 8" | "char_count HS16 = 10" | "char_count HS17 = 5"
| "char_count HS18 = 5" | "char_count HS19 = 5" | "char_count HS20 = 12"
| "char_count HS21 = 12" | "char_count HS22 = 12" | "char_count HS23 = 12"
| "char_count HS24 = 10" | "char_count HS25 = 25" | "char_count HS26 = 5"
| "char_count HS27 = 4" | "char_count HS28 = 13" | "char_count HS29 = 18"
| "char_count HS30 = 4"

text \<open>
  \<open>elided\<close> marks the two clauses whose transmitted text itself contains
  an elision marker (乃至, "and so on up to"): HS14 abbreviates the
  eighteen \<open>dhatu\<close>s to their first and last member, and HS16 abbreviates
  the twelve-link chain of dependent origination and its cessation the same
  way. \<^file>\<open>HeartSutra_Dharma.thy\<close> gives the formal content of both elisions
  (\<open>dhatu_naishi\<close>, \<open>pratiloma_naishi\<close>): the enumeration the ellipsis
  stands for is exhaustive and has the stated first and last element.
\<close>

fun elided :: "clause \<Rightarrow> bool" where
  "elided HS14 = True" | "elided HS16 = True" | "elided _ = False"

datatype interlocutor = Avalokitesvara | Sariputra

text \<open>HS01/HS02/HS04 speak of Avalokitesvara; HS05/HS09 address Sariputra.\<close>

definition speaker :: "clause \<Rightarrow> interlocutor option" where
  "speaker c = (if c \<in> {HS01, HS02, HS03, HS04} then Some Avalokitesvara
                else if c \<in> {HS05, HS09} then Some Sariputra
                else None)"

lemma clauses_exhaustive: "set clauses = UNIV"
proof (rule set_eqI)
  fix c show "c \<in> set clauses \<longleftrightarrow> c \<in> UNIV"
    by (cases c) (simp_all add: clauses_def)
qed

lemma clauses_distinct: "distinct clauses"
  unfolding clauses_def by simp

lemma body_length: "length body = 29"
  unfolding body_def by simp

lemma body_262: "sum_list (map char_count body) = 262"
  unfolding body_def by eval

lemma title_colophon_outside: "HS00 \<notin> set body \<and> HS30 \<notin> set body"
  unfolding body_def by simp

lemma body_subset_clauses: "set body \<subseteq> set clauses"
  unfolding body_def clauses_def by auto

end
