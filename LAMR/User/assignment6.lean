import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

variable (P Q R S : Prop)

/-
Replace the following sorry's by proofs.
-/

example : (P → Q) ∧ (Q → R) → P → R := by
  intro h
  intro hp
  apply h.right
  apply h.left
  exact hp
example (h : P → Q) (h1 : P ∧ R) : Q ∧ R := by
  apply And.intro
  · apply h
    exact h1.left
  · exact h1.right

example (h : ¬ (P ∧ Q)) : P → ¬ Q := by
  intro hp
  intro hq
  apply h
  exact ⟨hp, hq⟩

example (h : ¬ (P → Q)) : ¬ Q := by
  intro hq
  apply h
  intro _
  exact hq

example (h : P ∧ ¬ Q) : ¬ (P → Q) := by
  intro h1
  apply h.right
  apply h1
  exact h.left

example (h1 : P ∨ Q) (h2 : P → R) : R ∨ Q := by
  rcases h1 with hp | hq
  · left
    apply h2
    exact hp
  · right
    exact hq

example (h1 : P ∨ Q → R) : (P → R) ∧ (Q → R) := by
  apply And.intro
  · intro hp
    apply h1
    apply Or.inl
    exact hp
  · intro hq
    apply h1
    apply Or.inr
    exact hq

example (h1 : P → R) (h2 : Q → R) : P ∨ Q → R := by
  intro h
  rcases h with hp | hq
  · apply h1
    exact hp
  · apply h2
    exact hq

example (h : ¬ (P ∨ Q)) : ¬ P ∧ ¬ Q := by
  apply And.intro
  · intro hp
    apply h
    apply Or.inl
    exact hp
  · intro hq
    apply h
    apply Or.inr
    exact hq

-- this one requires classical logic!
example (h : ¬ (P ∧ Q)) : ¬ P ∨ ¬ Q := by
  by_cases hp : P
  · right
    intro hq
    apply h
    exact ⟨hp, hq⟩
  · left
    exact hp

-- this one too
example (h : P → Q) : ¬ P ∨ Q := by
  by_cases hp : P
  · right
    apply h
    exact hp
  · left
    exact hp

/-
Prove the following using only `rw` and the identities given.

Remember that you can use `rw [← h]` to use an identity in the reverse direction,
and you can provides argument to general identities to instantiate them.
-/

#check add_assoc
#check add_comm
#check pow_mul
#check mul_comm
#check mul_add
example (a b c : Nat) : (c * b) * a = b * (a * c) := by
  rw [mul_assoc, mul_comm, ←mul_assoc]

example (x y z : Nat) : (x + y) + z = (z + y) + x := by
  rw [add_assoc]
  rw [add_comm y z]
  rw [←add_comm]

example (x y z : Nat) : (x^y)^z = (x^z)^y := by
  rw [←pow_mul]
  rw [mul_comm]
  rw [pow_mul]

example (x y z w : Nat) : (x^y)^(z + w) = x^(y * z + y * w) := by
  rw [←pow_mul x y (z + w)]
  rw [mul_add y z w]

/-
A *group* is a structure with *, ⁻¹, 1 satisfing the basic group laws.

  https://en.wikipedia.org/wiki/Group_(mathematics)
-/

section
-- Lean lets us declare a group as follows.
variable {G : Type*} [Group G]

#check @mul_left_inv
#check @mul_right_inv
#check @mul_one
#check @one_mul
#check @mul_assoc

example (x y : G) : x * y * y⁻¹ = x := by
  rw [mul_assoc, mul_right_inv, mul_one]

/-
A group is *abelian* if it satisfies the additional law that
`x * y = y * x` for all `x` and `y`.

Fill in the sorry's in the next two theorems. The final one shows that
any group satisfying `x * x = 1` for every `x` is abelian.

You can use `rw [h]` to replace any expression of the form `e * e` by `1`.
-/
theorem fact1 (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = y * (y * z) * (y * z) * z := by
  rw [mul_assoc y (y * z) (y * z), h (y * z), mul_one]

theorem fact2 (h : ∀ x : G, x * x = 1) (y z : G) :
    z * y = y * (y * z) * (y * z) * z := by
  rw [←mul_assoc y y z, h y, one_mul, ←mul_assoc, mul_assoc, h z, mul_one]

theorem main (h : ∀ x : G, x * x = 1) (y z : G) :
    y * z = z * y := by
  rw [fact1 h y z, fact2 h y z]

end
