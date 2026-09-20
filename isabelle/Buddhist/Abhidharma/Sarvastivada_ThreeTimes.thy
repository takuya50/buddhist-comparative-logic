(* SPDX-License-Identifier: Apache-2.0 *)
section \<open>The Sarvastivada three times: four accounts, and which of them define a present\<close>

theory Sarvastivada_ThreeTimes
  imports Main
begin

text \<open>
  The Sarvastivada holds that a \<open>dharma\<close> exists as a substance in all three
  times, past, present and future alike, and that what comes and goes is not
  the thing but its \<open>karitra\<close>, the function it performs. The obvious
  question is then what makes one of the three times the present one. The
  \<open>Mahavibhasa\<close> records four answers, and Vasubandhu reports and judges them
  in \<open>Abhidharmakosabhasya\<close> V:

  \<^item> Dharmatrata, change of \<^emph>\<open>mode of being\<close> (\<open>bhava-anyathatva\<close>);
  \<^item> Ghosaka, change of \<^emph>\<open>mark\<close> (\<open>laksana-anyathatva\<close>): a dharma carries all
    three time-marks and differs in which is to the fore;
  \<^item> Vasumitra, change of \<^emph>\<open>state\<close> (\<open>avastha-anyathatva\<close>): a dharma is present
    when it is performing its function;
  \<^item> Buddhadeva, change of \<^emph>\<open>relatum\<close> (\<open>anyonya-anyathatva\<close>): a dharma is past or
    future relative to what it is compared with.

  Vasubandhu prefers Vasumitra's. This theory asks what separates the four
  formally, and the separation is sharp: two of them fail to define a
  present at all. Two conditions are asked of an account. \<^bold>\<open>Uniqueness\<close>: a
  dharma is in at most one of the three times at a given moment.
  \<^bold>\<open>Change\<close>: which time it is in can differ from moment to moment,
  otherwise nothing ever becomes present.

  Ghosaka's account fails uniqueness, since carrying all three marks is
  being in all three times at once -- which is precisely Vasubandhu's
  objection that the times would be mixed. What is formalized is
  Vasubandhu's reading of Ghosaka, on which the marks of the other two
  times are never given up; a reading on which only one mark is borne at a
  time would not be this predicate and is not treated here. Buddhadeva's fails it too, once
  the relatum is allowed to vary, since the same dharma is then past
  relative to one thing and future relative to another. Vasumitra's meets
  both. Dharmatrata's meets both as well, and the objection to it is not
  inconsistency but that it defines the same present-predicate as an
  account in which the thing itself alters -- Samkhya transformation, which
  a Buddhist may not have; that indistinguishability is stated as a theorem
  rather than as a charge. The comparison itself is not new -- it is the
  subject of a literature on the Sarvastivada theories of time and the
  Patanjala Yoga theory of \<open>parinama\<close> -- and what is added here is only that
  the two definitions are literally the same function.

  The last section states the Sautrantika objection that applies to all
  four: if the function belongs to a thing that exists at every time, and
  belongs to it intrinsically, then nothing ever changes.
\<close>

datatype phase = Past | Present | Future


subsection \<open>The common frame\<close>

locale tri_temporal =
  fixes exists_at :: "'d \<Rightarrow> 't :: linorder \<Rightarrow> bool"
    and active    :: "'d \<Rightarrow> 't \<Rightarrow> bool"          \<comment> \<open>\<open>karitra\<close>: performing its function\<close>
  assumes sarvasti: "exists_at d t"                \<comment> \<open>the thesis: it exists at every time\<close>
begin

text \<open>
  Vasumitra: the present is when the function is being performed, the past
  is when it has been, the future when it has not yet.
\<close>

definition vasumitra :: "'d \<Rightarrow> 't \<Rightarrow> phase \<Rightarrow> bool" where
  "vasumitra d now ph \<longleftrightarrow>
     (case ph of
        Present \<Rightarrow> active d now
      | Past    \<Rightarrow> \<not> active d now \<and> (\<exists>t < now. active d t)
      | Future  \<Rightarrow> \<not> active d now \<and> \<not> (\<exists>t < now. active d t))"

theorem vasumitra_unique_present:
  "vasumitra d now ph \<Longrightarrow> vasumitra d now ph' \<Longrightarrow> ph = ph'"
  by (cases ph; cases ph') (auto simp: vasumitra_def)

theorem vasumitra_total: "\<exists>ph. vasumitra d now ph"
proof (cases "active d now")
  case True
  then show ?thesis by (intro exI[of _ Present]) (simp add: vasumitra_def)
next
  case notnow: False
  show ?thesis
  proof (cases "\<exists>t < now. active d t")
    case True
    with notnow show ?thesis by (intro exI[of _ Past]) (simp add: vasumitra_def)
  next
    case False
    with notnow show ?thesis by (intro exI[of _ Future]) (simp add: vasumitra_def)
  qed
qed

end

text \<open>A model: the thing exists always and functions exactly once.\<close>

interpretation once: tri_temporal "\<lambda>_ (_ :: nat). True" "\<lambda>_ t. t = 5"
  by unfold_locales simp

theorem tri_temporal_nonvacuous: "once.vasumitra d 5 Present"
  by (simp add: once.vasumitra_def)


subsection \<open>Ghosaka: all three marks at once\<close>

text \<open>
  On the mark account a dharma carries the marks of all three times
  throughout, and differs only in which mark is manifest. Read as a claim
  about what times the dharma is in, it puts it in all three.
\<close>

definition ghosaka :: "'d \<Rightarrow> 't \<Rightarrow> phase \<Rightarrow> bool" where
  "ghosaka d now ph \<longleftrightarrow> True"

theorem ghosaka_violates_uniqueness:
  "ghosaka d now Past \<and> ghosaka d now Present \<and> ghosaka d now Future"
  by (simp add: ghosaka_def)

theorem ghosaka_times_are_mixed: "\<exists>ph ph'. ph \<noteq> ph' \<and> ghosaka d now ph \<and> ghosaka d now ph'"
  by (auto simp: ghosaka_def)


subsection \<open>Buddhadeva: past and future relative to different relata\<close>

text \<open>
  On the relatum account the phase is a three-place matter: a dharma at a
  time is past or future \<^emph>\<open>with respect to\<close> another time. Fixing the relatum
  gives a unique phase; letting it vary, which is what the account requires
  in order to be an account of the three times rather than of one
  comparison, does not.
\<close>

definition buddhadeva :: "'t :: linorder \<Rightarrow> 't \<Rightarrow> phase \<Rightarrow> bool" where
  "buddhadeva now rel ph \<longleftrightarrow>
     (case ph of Past \<Rightarrow> now < rel | Present \<Rightarrow> now = rel | Future \<Rightarrow> rel < now)"

theorem buddhadeva_unique_given_relatum:
  "buddhadeva now rel ph \<Longrightarrow> buddhadeva now rel ph' \<Longrightarrow> ph = ph'"
  by (cases ph; cases ph') (auto simp: buddhadeva_def)

theorem buddhadeva_relative_collapse:
  "buddhadeva (5 :: nat) 7 Past \<and> buddhadeva (5 :: nat) 3 Future"
  by (simp add: buddhadeva_def)

theorem buddhadeva_no_absolute_phase:
  "\<exists>now rel rel' :: nat. \<exists>ph ph'. ph \<noteq> ph' \<and> buddhadeva now rel ph \<and> buddhadeva now rel' ph'"
  using buddhadeva_relative_collapse by blast


subsection \<open>Dharmatrata: the mode of being changes\<close>

datatype mode = Latent | Actual | Spent

text \<open>
  On the mode account the present is when the mode is \<open>Actual\<close>. It defines a
  unique phase and it allows change, so it passes both conditions. The
  difficulty Vasubandhu raises is different: it is the same predicate as one
  gets by saying that the thing itself alters from one mode to the next,
  which is transformation in the Samkhya sense. That is stated here as an
  equality of definitions, which is what "indistinguishable" means
  formally -- it is not by itself an objection.
\<close>

definition dharmatrata :: "('d \<Rightarrow> 't \<Rightarrow> mode) \<Rightarrow> 'd \<Rightarrow> 't \<Rightarrow> phase \<Rightarrow> bool" where
  "dharmatrata bhava d now ph \<longleftrightarrow>
     (case ph of Present \<Rightarrow> bhava d now = Actual
               | Past    \<Rightarrow> bhava d now = Spent
               | Future  \<Rightarrow> bhava d now = Latent)"

theorem dharmatrata_unique_present:
  "dharmatrata bhava d now ph \<Longrightarrow> dharmatrata bhava d now ph' \<Longrightarrow> ph = ph'"
  by (cases ph; cases ph') (auto simp: dharmatrata_def)

theorem dharmatrata_allows_change:
  "dharmatrata (\<lambda>_ t. if t = (0 :: nat) then Latent else Actual) d 0 Future"
  "dharmatrata (\<lambda>_ t. if t = (0 :: nat) then Latent else Actual) d 1 Present"
  by (simp_all add: dharmatrata_def)

definition parinama :: "('d \<Rightarrow> 't \<Rightarrow> mode) \<Rightarrow> 'd \<Rightarrow> 't \<Rightarrow> phase \<Rightarrow> bool" where
  "parinama nature d now ph \<longleftrightarrow>
     (case ph of Present \<Rightarrow> nature d now = Actual
               | Past    \<Rightarrow> nature d now = Spent
               | Future  \<Rightarrow> nature d now = Latent)"

theorem dharmatrata_is_parinama: "dharmatrata f = parinama f"
  by (rule ext)+ (simp add: dharmatrata_def parinama_def)


subsection \<open>Which accounts define a present\<close>

text \<open>
  Buddhadeva's account with the relatum quantified away -- which is what it
  must be to be an account of the three times rather than of one comparison.
\<close>

definition buddhadeva_abs :: "'t :: linorder \<Rightarrow> phase \<Rightarrow> bool" where
  "buddhadeva_abs now ph \<longleftrightarrow> (\<exists>rel. buddhadeva now rel ph)"

theorem buddhadeva_abs_violates_uniqueness:
  "buddhadeva_abs (5 :: nat) Past"
  "buddhadeva_abs (5 :: nat) Present"
  "buddhadeva_abs (5 :: nat) Future"
  unfolding buddhadeva_abs_def
    apply (rule exI[of _ 7], simp add: buddhadeva_def)
   apply (rule exI[of _ 5], simp add: buddhadeva_def)
  apply (rule exI[of _ 3], simp add: buddhadeva_def)
  done

text \<open>
  The comparison. Of the four accounts, Vasumitra's
  (\<open>tri_temporal.vasumitra_unique_present\<close>) and Dharmatrata's
  (\<open>dharmatrata_unique_present\<close>) assign a dharma exactly one of the three
  times; Ghosaka's and Buddhadeva's assign it all three. That is the formal
  content of Vasubandhu's report that the first two are defensible and his
  preference for the state account, since Dharmatrata's is the one that
  coincides with transformation.
\<close>

theorem accounts_that_fail_uniqueness:
  "\<not> (\<forall>ph ph'. ghosaka d (now :: nat) ph \<longrightarrow> ghosaka d now ph' \<longrightarrow> ph = ph')"
  "\<not> (\<forall>ph ph'. buddhadeva_abs (5 :: nat) ph \<longrightarrow> buddhadeva_abs (5 :: nat) ph' \<longrightarrow> ph = ph')"
proof -
  show "\<not> (\<forall>ph ph'. ghosaka d (now :: nat) ph \<longrightarrow> ghosaka d now ph' \<longrightarrow> ph = ph')"
  proof
    assume *: "\<forall>ph ph'. ghosaka d (now :: nat) ph \<longrightarrow> ghosaka d now ph' \<longrightarrow> ph = ph'"
    have "ghosaka d (now :: nat) Past" and "ghosaka d (now :: nat) Present"
      by (simp_all add: ghosaka_def)
    with * have "Past = Present" by blast
    then show False by simp
  qed
  show "\<not> (\<forall>ph ph'. buddhadeva_abs (5 :: nat) ph \<longrightarrow> buddhadeva_abs (5 :: nat) ph' \<longrightarrow> ph = ph')"
  proof
    assume *: "\<forall>ph ph'. buddhadeva_abs (5 :: nat) ph \<longrightarrow> buddhadeva_abs (5 :: nat) ph' \<longrightarrow> ph = ph'"
    from buddhadeva_abs_violates_uniqueness(1) buddhadeva_abs_violates_uniqueness(2) *
    have "Past = Present" by blast
    then show False by simp
  qed
qed


subsection \<open>The Sautrantika objection: an intrinsic function cannot come and go\<close>

text \<open>
  All four accounts leave the same question. The thing exists at every time;
  its function does not. If what the function is depends only on the thing,
  then it cannot depend on the time, and a thing that ever functions
  functions always. So the Sarvastivada must make the function depend on
  something outside the thing -- which is to concede that the thing alone is
  not what is real at every time.
\<close>

theorem karitra_must_be_extrinsic:
  assumes intrinsic: "\<And>d t t'. active d t = active d t'"
  shows "(\<forall>t. active d t) \<or> (\<forall>t. \<not> active d t)"
  using intrinsic by blast

theorem no_change_without_extrinsic_condition:
  assumes intrinsic: "\<And>d t t'. active d t = active d t'"
  shows "\<not> (\<exists>d t t'. active d t \<and> \<not> active d t')"
  using intrinsic by blast

end
