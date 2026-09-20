/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# Text layer: the 262-character recension segmented into clauses

This is the Lean 4 counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Text.thy`.  The Chinese source text
remains in the prose documentation; this module records its clause structure,
the transmitted-form character counts, its two explicit elisions, and the
interlocutor annotations.
-/

namespace BuddhistComparativeLogic

inductive Clause where
  | HS00 | HS01 | HS02 | HS03 | HS04 | HS05 | HS06 | HS07 | HS08 | HS09
  | HS10 | HS11 | HS12 | HS13 | HS14 | HS15 | HS16 | HS17 | HS18 | HS19
  | HS20 | HS21 | HS22 | HS23 | HS24 | HS25 | HS26 | HS27 | HS28 | HS29
  | HS30
  deriving DecidableEq, Repr, Inhabited

open Clause

def clauses : List Clause :=
  [HS00, HS01, HS02, HS03, HS04, HS05, HS06, HS07, HS08, HS09,
   HS10, HS11, HS12, HS13, HS14, HS15, HS16, HS17, HS18, HS19,
   HS20, HS21, HS22, HS23, HS24, HS25, HS26, HS27, HS28, HS29, HS30]

def body : List Clause :=
  [HS01, HS02, HS03, HS04, HS05, HS06, HS07, HS08, HS09,
   HS10, HS11, HS12, HS13, HS14, HS15, HS16, HS17, HS18, HS19,
   HS20, HS21, HS22, HS23, HS24, HS25, HS26, HS27, HS28, HS29]

def char_count : Clause → Nat
  | HS00 => 8  | HS01 => 5  | HS02 => 9  | HS03 => 6  | HS04 => 5
  | HS05 => 3  | HS06 => 8  | HS07 => 8  | HS08 => 8  | HS09 => 8
  | HS10 => 12 | HS11 => 11 | HS12 => 7  | HS13 => 7  | HS14 => 9
  | HS15 => 8  | HS16 => 10 | HS17 => 5  | HS18 => 5  | HS19 => 5
  | HS20 => 12 | HS21 => 12 | HS22 => 12 | HS23 => 12 | HS24 => 10
  | HS25 => 25 | HS26 => 5  | HS27 => 4  | HS28 => 13 | HS29 => 18
  | HS30 => 4

/-- The clauses containing 乃至, the received text's explicit elision marker. -/
def elided : Clause → Bool
  | HS14 | HS16 => true
  | _ => false

inductive Interlocutor where
  | Avalokitesvara
  | Sariputra
  deriving DecidableEq, Repr, Inhabited

open Interlocutor

/-- HS01--HS04 concern Avalokitesvara; HS05 and HS09 address Sariputra. -/
def speaker : Clause → Option Interlocutor
  | HS01 | HS02 | HS03 | HS04 => some Avalokitesvara
  | HS05 | HS09 => some Sariputra
  | _ => none

/-- The explicit clause enumeration contains every constructor. -/
theorem clauses_exhaustive (c : Clause) : c ∈ clauses := by
  cases c <;> decide

theorem clauses_distinct : clauses.Nodup := by
  decide

theorem body_length : body.length = 29 := by
  decide

theorem body_262 : (body.map char_count).sum = 262 := by
  decide

theorem title_colophon_outside : HS00 ∉ body ∧ HS30 ∉ body := by
  decide

theorem body_subset_clauses : ∀ c, c ∈ body → c ∈ clauses := by
  intro c
  cases c <;> decide

end BuddhistComparativeLogic
