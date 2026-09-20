/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.HeartSutra.Text
import BuddhistComparativeLogic.Buddhist.HeartSutra.Emptiness
import BuddhistComparativeLogic.Buddhist.HeartSutra.Path
import BuddhistComparativeLogic.Buddhist.HeartSutra.Mantra

/-!
# Coverage theorem

The Lean counterpart of `isabelle/Buddhist/HeartSutra/HeartSutra_Coverage.thy`.  Every clause is classified as
defined, proved, or explicitly noted; `Missing` is never assigned.
-/

namespace BuddhistComparativeLogic

open Clause

inductive Status where
  | Defined | Proved | Noted | Missing
  deriving DecidableEq, Repr, Inhabited

open Status

def status_of : Clause → Status
  | HS00 => Defined
  | HS01 => Proved
  | HS02 => Proved
  | HS03 => Proved
  | HS04 => Proved
  | HS05 => Defined
  | HS06 => Proved
  | HS07 => Proved
  | HS08 => Proved
  | HS09 => Proved
  | HS10 => Proved
  | HS11 => Proved
  | HS12 => Proved
  | HS13 => Proved
  | HS14 => Proved
  | HS15 => Proved
  | HS16 => Proved
  | HS17 => Proved
  | HS18 => Proved
  | HS19 => Proved
  | HS20 => Proved
  | HS21 => Proved
  | HS22 => Proved
  | HS23 => Proved
  | HS24 => Proved
  | HS25 => Defined
  | HS26 => Proved
  | HS27 => Noted
  | HS28 => Noted
  | HS29 => Noted
  | HS30 => Defined

def logic_dependent : Clause → Bool
  | HS06 | HS07 | HS09 | HS10 => true
  | _ => false

theorem coverage_complete : ∀ c, status_of c ≠ Missing := by
  intro c
  cases c <;> decide

theorem coverage_counts_proved :
    (clauses.filter fun c => status_of c = Proved).length = 24 := by
  decide

theorem coverage_counts_defined :
    (clauses.filter fun c => status_of c = Defined).length = 4 := by
  decide

theorem coverage_counts_noted :
    (clauses.filter fun c => status_of c = Noted).length = 3 := by
  decide

theorem coverage_counts :
    (clauses.filter fun c => status_of c = Proved).length = 24 ∧
    (clauses.filter fun c => status_of c = Defined).length = 4 ∧
    (clauses.filter fun c => status_of c = Noted).length = 3 := by
  exact ⟨coverage_counts_proved, coverage_counts_defined, coverage_counts_noted⟩

theorem logic_dependent_set (c : Clause) :
    logic_dependent c = true ↔
      c = HS06 ∨ c = HS07 ∨ c = HS09 ∨ c = HS10 := by
  cases c <;> decide

/-! ## Live, typed cross-references

These aliases play the role of Isabelle's `@{thm [source] ...}` references.
They elaborate the actual theorem at its clause-specific type, so deleting a
discharging theorem or changing its statement breaks this module.
-/

namespace CoverageWitness

theorem hs01_hs04 (P : BodhisattvaPath V M) :
    P.nirvana P.avalokitesvara ∧ ¬ P.suffers P.avalokitesvara :=
  P.hs01_04_avalokitesvara

theorem hs02_hs20_hs22 (P : BodhisattvaPath V M) {m : M}
    (h : P.reliesPrajna m) :
    ¬ P.hindered m ∧ ¬ P.fears m ∧ ¬ P.inverted m ∧
      P.nirvana m ∧ ¬ P.suffers m :=
  P.hs21_22_chain h

theorem hs03 (E : Emptiness V) : ∀ s, E.emptyOf (Dharma.sk s) :=
  E.hs03_skandhas

theorem hs06 (x : Dharma) :
    fdeAllGlutEmptiness.RIdentity x ∧
      ¬ fdeAllGlutEmptiness.RNotsep (Dharma.sk Skandha.rupa) :=
  fde_R_identity_not_notsep x

theorem hs07_hs08 (E : Emptiness V) :
    (∀ x, E.RMutual x) ∧ (∀ s, E.RMutual (Dharma.sk s)) :=
  ⟨E.hs07_R_mutual, E.hs08_generalize⟩

theorem hs09_hs11_hs17 (E : Emptiness V) :
    ∀ d, d ∈ negated_dharmas → E.emptyOf d :=
  E.hs11_18_enumeration

theorem hs10 (v : Atom → TV4) (a : Atom) :
    mvFDE.sat v (hs10Formula a) ↔ v a = TV4.B :=
  hs10_fde_formula_iff_B v a

theorem hs14 :
    dhatus.head? = some (Indriya.caksus, DhatuKind.Root) ∧
    dhatus.getLast? = some (Indriya.manas, DhatuKind.Consciousness) ∧
    dhatus.Nodup ∧ (∀ x : Dhatu, x ∈ dhatus) :=
  dhatu_naishi

theorem hs15_hs16 (E : Emptiness V) :
    ∀ n, E.emptyOf (Dharma.ni n) ∧ E.emptyOf (Dharma.niNirodha n) :=
  E.hs15_16_chain_and_cessation

theorem hs16_elision :
    pratiloma.head? = some Nidana.jaramarana ∧
    pratiloma.getLast? = some Nidana.avidya ∧
    (∀ x : Nidana, x ∈ pratiloma) ∧ pratiloma.Nodup :=
  pratiloma_naishi

theorem hs18_hs19 (E : Emptiness V) :
    E.emptyOf Dharma.jnana ∧ E.emptyOf Dharma.prapti :=
  ⟨E.sarva_dharma_sunya Dharma.jnana, E.hs19_no_attainment⟩

theorem hs23_hs24 (P : BodhisattvaPath V M) {t : Kala} {b : M}
    (h : P.buddha t b) : P.bodhi b :=
  P.hs23_24_three_times h

theorem hs25 : epithets.length = 4 :=
  epithets_four

theorem hs26 (P : BodhisattvaPath V M) {m : M}
    (h : P.nirvana m) : ¬ P.suffers m :=
  P.hs04_26 m h

theorem hs27_hs29 :
    truth_apt (Utterance.Invoke heart_mantra : Utterance Atom) = false ∧
      heart_mantra.length = 6 ∧
      heart_mantra.head? = some MantraWord.gate ∧
      heart_mantra.getLast? = some MantraWord.svaha :=
  ⟨hs29_mantra_not_truth_apt, heart_mantra_shape⟩

end CoverageWitness

end BuddhistComparativeLogic
