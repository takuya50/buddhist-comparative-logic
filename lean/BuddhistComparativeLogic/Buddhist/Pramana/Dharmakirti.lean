/- SPDX-License-Identifier: Apache-2.0 -/

import BuddhistComparativeLogic.Buddhist.Pramana.Hetucakra

/-!
# Dharmakīrti's three kinds of reason

This ports the semantic content of `isabelle/Buddhist/Pramana/Dharmakirti_Reasons.thy`: pervasion supplies
the premise missing from the three marks, while identity, effect and
non-perception reasons expose different sources for that premise.
-/

namespace BuddhistComparativeLogic.Dharmakirti

open BuddhistComparativeLogic.Hetucakra

structure Model (L : Type u) extends Anumana L where
  vyapti : Prop
  vyapti_iff : vyapti ↔ ∀ x, reason x → sadhya x

namespace Model

variable {L : Type u} (m : Model L)

theorem vyapti_sound
    (hv : m.vyapti) (hp : m.toAnumana.paksadharmata) :
    m.sadhya m.paksa := by
  exact (m.vyapti_iff.mp hv) m.paksa hp

theorem vyapti_gives_vyatireka
    (hv : m.vyapti) : m.toAnumana.vyatireka := by
  intro x hx hreason
  exact hx.2 ((m.vyapti_iff.mp hv) x hreason)

theorem vyapti_gives_verdict
    (hv : m.vyapti) (ha : m.toAnumana.anvaya) :
    m.toAnumana.wheelVerdict = .valid := by
  apply m.toAnumana.wheel_valid_iff.mpr
  exact ⟨ha, m.vyapti_gives_vyatireka hv⟩

end Model

theorem marks_without_vyapti :
    Hetucakra.nofire.trairupya ∧
      ¬ (∀ x, Hetucakra.nofire.reason x → Hetucakra.nofire.sadhya x) := by
  refine ⟨Hetucakra.no_deductive_soundness.1, ?_⟩
  intro h
  exact Hetucakra.no_deductive_soundness.2.2
    (h .mountain (by simp [Hetucakra.nofire]))

/-! ## The identity reason -/

structure SvabhavaHetu (L : Type u) extends Model L where
  inclusion : ∀ x, reason x → sadhya x

namespace SvabhavaHetu

variable {L : Type u} (m : SvabhavaHetu L)

theorem svabhavahetu_vyapti : m.vyapti :=
  m.vyapti_iff.mpr m.inclusion

theorem svabhavahetu_sound
    (hp : m.toAnumana.paksadharmata) : m.sadhya m.paksa :=
  m.toModel.vyapti_sound m.svabhavahetu_vyapti hp

end SvabhavaHetu

inductive Plant where
  | simsapa1 | simsapa2 | oak | grass
  deriving DecidableEq, Repr

open Plant

def simsapa : SvabhavaHetu Plant where
  paksa := .simsapa1
  sadhya := fun x => x ≠ .grass
  reason := fun x => x = .simsapa1 ∨ x = .simsapa2
  vyapti := True
  vyapti_iff := by
    constructor
    · intro _ x hx
      rcases hx with rfl | rfl <;> decide
    · intro _
      trivial
  inclusion := by
    intro x hx
    rcases hx with rfl | rfl <;> decide

theorem plant_ne_grass {x : Plant}
    (h : x = .simsapa1 ∨ x = .simsapa2) : x ≠ .grass := by
  rcases h with rfl | rfl <;> decide

theorem simsapa_tree :
    simsapa.toAnumana.wheelVerdict = .valid ∧
      simsapa.sadhya .simsapa1 := by
  have hanv : simsapa.toAnumana.anvaya :=
    ⟨.simsapa2, ⟨by decide, by simp [simsapa]⟩, Or.inr rfl⟩
  exact ⟨simsapa.toModel.vyapti_gives_verdict trivial hanv, by simp [simsapa]⟩

/-! ## The effect reason -/

structure KaryaHetu (L : Type u) extends Anumana L where
  causalLaw : Prop
  causal_law_iff : causalLaw ↔ ∀ x, reason x → sadhya x

namespace KaryaHetu

variable {L : Type u} (m : KaryaHetu L)

theorem karyahetu_sound
    (law : m.causalLaw) (hp : m.toAnumana.paksadharmata) :
    m.sadhya m.paksa :=
  (m.causal_law_iff.mp law) m.paksa hp

end KaryaHetu

theorem karyahetu_needs_causal_law :
    Hetucakra.nofire.trairupya ∧
      ¬ (∀ x, Hetucakra.nofire.reason x → Hetucakra.nofire.sadhya x) ∧
      ¬ Hetucakra.nofire.sadhya .mountain :=
  ⟨marks_without_vyapti.1, marks_without_vyapti.2,
    Hetucakra.no_deductive_soundness.2.2⟩

/-! ## The non-perception reason -/

structure Anupalabdhi (O : Type u) where
  present : O → Prop
  perceived : O → Prop
  perceptible : O → Prop
  visibility : ∀ {x}, present x → perceptible x → perceived x

namespace Anupalabdhi

variable {O : Type u} (m : Anupalabdhi O)

theorem drsyanupalabdhi_sound {x : O}
    (hvisible : m.perceptible x) (hunseen : ¬ m.perceived x) :
    ¬ m.present x := by
  intro hpresent
  exact hunseen (m.visibility hpresent hvisible)

end Anupalabdhi

inductive ThingHere where
  | pot | ghost
  deriving DecidableEq, Repr

def here : Anupalabdhi ThingHere where
  present := fun x => x = .ghost
  perceived := fun _ => False
  perceptible := fun x => x = .pot
  visibility := by
    intro x hp hv
    cases x <;> simp_all

theorem anupalabdhi_needs_perceptibility :
    ¬ here.present .pot ∧ here.present .ghost ∧ ¬ here.perceived .ghost := by
  simp [here]

end BuddhistComparativeLogic.Dharmakirti
