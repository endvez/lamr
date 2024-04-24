import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

/-
Replace each `sorry` by a proof. The examples from lecture will be helpful.

Each problem is worth 1 point.
-/

open Function

section

variable {α β : Type} (p q : α → Prop) (r : α → β → Prop)

example : (∀ x, p x) ∧ (∀ x, q x) → ∀ x, p x ∧ q x := by
  intro h
  intro x
  exact ⟨h.1 x, h.2 x⟩

example : (∀ x, p x) ∨ (∀ x, q x) → ∀ x, p x ∨ q x := by
  intro h
  intro x
  match h with
  | Or.inl hp => left; apply hp
  | Or.inr hq => right; apply hq

example : (∃ x, p x ∧ q x) → ∃ x, p x := by
  rintro ⟨x, ⟨hp, _⟩⟩
  use x


example : (∃ x, ∀ y, r x y) → ∀ y, ∃ x, r x y := by
  rintro ⟨x, h⟩
  intro y
  use x
  exact h y

end

section
open Function

#check Injective
#check Surjective

variable (f : α → β) (g : β → γ)

example (injgf : Injective (g ∘ f)) :
    Injective f := by
  intros x1 x2 h
  apply injgf
  rw [comp_apply, comp_apply, h]

-- this one is worth two points
example (surjgf : Surjective (g ∘ f)) (injg : Injective g) :
    Surjective f := by
  intro b
  obtain ⟨x, hgf⟩ : ∃ x, g (f x) = g b := surjgf (g b)
  use x
  apply injg
  exact hgf
end
