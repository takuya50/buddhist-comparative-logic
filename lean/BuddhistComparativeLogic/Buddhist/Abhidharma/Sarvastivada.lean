/- SPDX-License-Identifier: Apache-2.0 -/

import Std

/-!
# Sarvāstivāda accounts of the three times

The formal comparison is kept separate from any particular clock.  A
`TriTemporal` model supplies its own `before` relation; the concrete
Buddhadeva countermodel uses natural-number time.
-/

namespace BuddhistComparativeLogic.Sarvastivada

inductive Phase where
  | past | present | future
  deriving DecidableEq, Repr

open Phase

structure TriTemporal (D : Type u) (T : Type v) where
  existsAt : D → T → Prop
  active : D → T → Prop
  before : T → T → Prop
  sarvasti : ∀ d t, existsAt d t

namespace TriTemporal

variable {D : Type u} {T : Type v} (m : TriTemporal D T)

def vasumitra (d : D) (now : T) : Phase → Prop
  | .present => m.active d now
  | .past => ¬ m.active d now ∧ ∃ t, m.before t now ∧ m.active d t
  | .future => ¬ m.active d now ∧ ¬ ∃ t, m.before t now ∧ m.active d t

theorem vasumitra_unique_present {d : D} {now : T} {ph ph' : Phase}
    (h : m.vasumitra d now ph) (h' : m.vasumitra d now ph') : ph = ph' := by
  cases ph <;> cases ph' <;> simp_all [vasumitra]
  case future.past =>
    rcases h' with ⟨t, ht, ha⟩
    exact h.2 t ht ha

theorem vasumitra_total (d : D) (now : T) : ∃ ph, m.vasumitra d now ph := by
  classical
  by_cases hn : m.active d now
  · exact ⟨.present, hn⟩
  · by_cases hp : ∃ t, m.before t now ∧ m.active d t
    · exact ⟨.past, hn, hp⟩
    · exact ⟨.future, hn, hp⟩

end TriTemporal

def once : TriTemporal Unit Nat where
  existsAt := fun _ _ => True
  active := fun _ t => t = 5
  before := (· < ·)
  sarvasti := fun _ _ => trivial

theorem tri_temporal_nonvacuous : once.vasumitra () 5 .present := by
  rfl

/-! ## Ghoṣaka -/

def ghosaka (_d : D) (_now : T) (_ph : Phase) : Prop := True

theorem ghosaka_violates_uniqueness (d : D) (now : T) :
    ghosaka d now .past ∧ ghosaka d now .present ∧ ghosaka d now .future :=
  ⟨trivial, trivial, trivial⟩

theorem ghosaka_times_are_mixed (d : D) (now : T) :
    ∃ ph ph', ph ≠ ph' ∧ ghosaka d now ph ∧ ghosaka d now ph' :=
  ⟨.past, .present, by decide, trivial, trivial⟩

/-! ## Buddhadeva -/

def buddhadeva (now rel : Nat) : Phase → Prop
  | .past => now < rel
  | .present => now = rel
  | .future => rel < now

theorem buddhadeva_unique_given_relatum {now rel : Nat} {ph ph' : Phase}
    (h : buddhadeva now rel ph) (h' : buddhadeva now rel ph') : ph = ph' := by
  cases ph <;> cases ph' <;> simp_all [buddhadeva] <;> omega

theorem buddhadeva_relative_collapse :
    buddhadeva 5 7 .past ∧ buddhadeva 5 3 .future := by
  simp [buddhadeva]

theorem buddhadeva_no_absolute_phase :
    ∃ now rel rel' ph ph',
      ph ≠ ph' ∧ buddhadeva now rel ph ∧ buddhadeva now rel' ph' :=
  ⟨5, 7, 3, .past, .future, by decide,
    by simp [buddhadeva], by simp [buddhadeva]⟩

/-! ## Dharmatrāta -/

inductive Mode where
  | latent | actual | spent
  deriving DecidableEq, Repr

open Mode

def dharmatrata (bhava : D → T → Mode) (d : D) (now : T) : Phase → Prop
  | .present => bhava d now = .actual
  | .past => bhava d now = .spent
  | .future => bhava d now = .latent

theorem dharmatrata_unique_present {bhava : D → T → Mode}
    {d : D} {now : T} {ph ph' : Phase}
    (h : dharmatrata bhava d now ph)
    (h' : dharmatrata bhava d now ph') : ph = ph' := by
  cases ph <;> cases ph' <;> simp_all [dharmatrata]

def changingMode (_ : Unit) (t : Nat) : Mode :=
  if t = 0 then .latent else .actual

theorem dharmatrata_allows_change :
    dharmatrata changingMode () 0 .future ∧
      dharmatrata changingMode () 1 .present := by
  simp [dharmatrata, changingMode]

def parinama (nature : D → T → Mode) (d : D) (now : T) : Phase → Prop
  | .present => nature d now = .actual
  | .past => nature d now = .spent
  | .future => nature d now = .latent

theorem dharmatrata_is_parinama (f : D → T → Mode) :
    dharmatrata f = parinama f := by
  funext d t ph
  cases ph <;> rfl

/-! ## Which accounts define a present -/

def buddhadevaAbs (now : Nat) (ph : Phase) : Prop :=
  ∃ rel, buddhadeva now rel ph

theorem buddhadeva_abs_violates_uniqueness :
    buddhadevaAbs 5 .past ∧ buddhadevaAbs 5 .present ∧
      buddhadevaAbs 5 .future :=
  ⟨⟨7, by simp [buddhadeva]⟩, ⟨5, rfl⟩,
    ⟨3, by simp [buddhadeva]⟩⟩

theorem accounts_that_fail_uniqueness :
    (¬ ∀ ph ph', ghosaka () 0 ph → ghosaka () 0 ph' → ph = ph') ∧
      (¬ ∀ ph ph', buddhadevaAbs 5 ph → buddhadevaAbs 5 ph' → ph = ph') := by
  constructor
  · intro h
    exact (by decide : Phase.past ≠ .present) (h .past .present trivial trivial)
  · intro h
    exact (by decide : Phase.past ≠ .present)
      (h .past .present buddhadeva_abs_violates_uniqueness.1
        buddhadeva_abs_violates_uniqueness.2.1)

/-! ## The Sautrāntika objection -/

theorem karitra_must_be_extrinsic {D : Type u} {T : Type v} [Nonempty T]
    (active : D → T → Prop)
    (intrinsic : ∀ d t t', active d t ↔ active d t') (d : D) :
    (∀ t, active d t) ∨ (∀ t, ¬ active d t) := by
  classical
  let t0 : T := Classical.choice inferInstance
  by_cases h : active d t0
  · left
    intro t
    exact (intrinsic d t0 t).mp h
  · right
    intro t ht
    exact h ((intrinsic d t t0).mp ht)

theorem no_change_without_extrinsic_condition
    (active : D → T → Prop)
    (intrinsic : ∀ d t t', active d t ↔ active d t') :
    ¬ ∃ d t t', active d t ∧ ¬ active d t' := by
  rintro ⟨d, t, t', ht, hnot⟩
  exact hnot ((intrinsic d t t').mp ht)

end BuddhistComparativeLogic.Sarvastivada
