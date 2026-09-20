/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Core.Foundation

/-!
# Dharma-structure layer

This module ports `isabelle/Buddhist/HeartSutra/HeartSutra_Dharma.thy`: the five skandhas, twelve ayatanas,
eighteen dhatus, twelve nidanas, and four truths.  Each finite type has an
explicit exhaustive, duplicate-free list.  In bare Lean these lists are also
the constructive witnesses for the standard cardinalities.
-/

namespace BuddhistComparativeLogic

/--
A library-free cardinality witness: an exhaustive, duplicate-free enumeration
of exactly `n` values.  This replaces Isabelle's finite-set cardinality in the
bare Lean port.
-/
def HasCardinality (α : Type) (n : Nat) : Prop :=
  ∃ xs : List α, (∀ x : α, x ∈ xs) ∧ xs.Nodup ∧ xs.length = n

theorem card_of_list (xs : List α)
    (exhaustive : ∀ x : α, x ∈ xs) (distinct : xs.Nodup) :
    HasCardinality α xs.length := by
  exact ⟨xs, exhaustive, distinct, rfl⟩

inductive Skandha where
  | rupa | vedana | samjna | samskara | vijnana
  deriving DecidableEq, Repr, Inhabited

open Skandha

def skandhas : List Skandha := [rupa, vedana, samjna, samskara, vijnana]

theorem skandhas_univ : (∀ x : Skandha, x ∈ skandhas) ∧ skandhas.Nodup := by
  constructor
  · intro x
    cases x <;> decide
  · decide

/-- The exhaustive, duplicate-free skandha enumeration has five members. -/
theorem card_skandha : HasCardinality Skandha 5 := by
  exact ⟨skandhas, skandhas_univ.1, skandhas_univ.2, by decide⟩

inductive Indriya where
  | caksus | srotra | ghrana | jihva | kaya | manas
  deriving DecidableEq, Repr, Inhabited

inductive Visaya where
  | rupa_v | sabda | gandha | rasa | sprastavya | dharma_v
  deriving DecidableEq, Repr, Inhabited

open Indriya Visaya

def indriyas : List Indriya := [caksus, srotra, ghrana, jihva, kaya, manas]

def visayas : List Visaya := [rupa_v, sabda, gandha, rasa, sprastavya, dharma_v]

theorem indriyas_univ : (∀ x : Indriya, x ∈ indriyas) ∧ indriyas.Nodup := by
  constructor
  · intro x
    cases x <;> decide
  · decide

theorem visayas_univ : (∀ x : Visaya, x ∈ visayas) ∧ visayas.Nodup := by
  constructor
  · intro x
    cases x <;> decide
  · decide

def visaya_of : Indriya → Visaya
  | caksus => rupa_v
  | srotra => sabda
  | ghrana => gandha
  | jihva => rasa
  | kaya => sprastavya
  | manas => dharma_v

/-- Lean-style alias retained for clients that use camel case. -/
abbrev visayaOf := visaya_of

theorem visaya_of_bij :
    (∀ x y, visaya_of x = visaya_of y → x = y) ∧
    (∀ y, ∃ x, visaya_of x = y) := by
  constructor
  · intro x y h
    cases x <;> cases y <;> simp_all [visaya_of]
  · intro y
    cases y
    · exact ⟨caksus, rfl⟩
    · exact ⟨srotra, rfl⟩
    · exact ⟨ghrana, rfl⟩
    · exact ⟨jihva, rfl⟩
    · exact ⟨kaya, rfl⟩
    · exact ⟨manas, rfl⟩

inductive Ayatana where
  | In : Indriya → Ayatana
  | Vi : Visaya → Ayatana
  deriving DecidableEq, Repr, Inhabited

open Ayatana

def ayatanas : List Ayatana := indriyas.map In ++ visayas.map Vi

theorem ayatanas_univ : (∀ x : Ayatana, x ∈ ayatanas) ∧ ayatanas.Nodup := by
  constructor
  · intro x
    cases x with
    | In i => cases i <;> decide
    | Vi v => cases v <;> decide
  · decide

theorem card_ayatana : HasCardinality Ayatana 12 := by
  exact ⟨ayatanas, ayatanas_univ.1, ayatanas_univ.2, by decide⟩

inductive DhatuKind where
  | Root | Object | Consciousness
  deriving DecidableEq, Repr, Inhabited

abbrev Dhatu := Indriya × DhatuKind

open DhatuKind

/-- The traditional order: root, object, and consciousness for each root. -/
def dhatus : List Dhatu :=
  indriyas.flatMap fun i => [(i, Root), (i, Object), (i, Consciousness)]

theorem dhatu_naishi :
    dhatus.head? = some (caksus, Root) ∧
    dhatus.getLast? = some (manas, Consciousness) ∧
    dhatus.Nodup ∧
    (∀ x : Dhatu, x ∈ dhatus) := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · decide
  · intro x
    rcases x with ⟨i, k⟩
    cases i <;> cases k <;> decide

theorem card_dhatu : HasCardinality Dhatu 18 := by
  exact ⟨dhatus, dhatu_naishi.2.2.2, dhatu_naishi.2.2.1, by decide⟩

inductive Nidana where
  | avidya | samskara_n | vijnana_n | namarupa | sadayatana | sparsa
  | vedana_n | trsna | upadana | bhava | jati | jaramarana
  deriving DecidableEq, Repr, Inhabited

open Nidana

def nidana_next : Nidana → Option Nidana
  | avidya => some samskara_n
  | samskara_n => some vijnana_n
  | vijnana_n => some namarupa
  | namarupa => some sadayatana
  | sadayatana => some sparsa
  | sparsa => some vedana_n
  | vedana_n => some trsna
  | trsna => some upadana
  | upadana => some bhava
  | bhava => some jati
  | jati => some jaramarana
  | jaramarana => none

abbrev nidanaNext := nidana_next

def anuloma : List Nidana :=
  [avidya, samskara_n, vijnana_n, namarupa, sadayatana, sparsa,
   vedana_n, trsna, upadana, bhava, jati, jaramarana]

def pratiloma : List Nidana := anuloma.reverse

theorem anuloma_complete :
    (∀ x : Nidana, x ∈ anuloma) ∧ anuloma.Nodup ∧ anuloma.length = 12 := by
  constructor
  · intro x
    cases x <;> decide
  constructor <;> decide

theorem pratiloma_naishi :
    pratiloma.head? = some jaramarana ∧
    pratiloma.getLast? = some avidya ∧
    (∀ x : Nidana, x ∈ pratiloma) ∧
    pratiloma.Nodup := by
  constructor
  · decide
  constructor
  · decide
  constructor
  · intro x
    cases x <;> decide
  · decide

theorem card_nidana : HasCardinality Nidana 12 := by
  exact ⟨anuloma, anuloma_complete.1, anuloma_complete.2.1,
    anuloma_complete.2.2⟩

inductive Satya where
  | duhkha | samudaya | nirodha | marga
  deriving DecidableEq, Repr, Inhabited

open Satya

def satyas : List Satya := [duhkha, samudaya, nirodha, marga]

theorem satyas_univ : (∀ x : Satya, x ∈ satyas) ∧ satyas.Nodup := by
  constructor
  · intro x
    cases x <;> decide
  · decide

theorem card_satya : HasCardinality Satya 4 := by
  exact ⟨satyas, satyas_univ.1, satyas_univ.2, by decide⟩

end BuddhistComparativeLogic
