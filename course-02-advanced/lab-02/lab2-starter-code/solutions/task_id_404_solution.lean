import Mathlib
import Aesop

-- Implementation
def myMin (a : Int) (b : Int) : Int :=
  if a ≤ b then a else b


-- Theorem: The minValue is either a or b; The minValue is less than or equal to both a and b
def myMin_spec (a : Int) (b : Int) (result : Int) : Prop :=
  (result ≤ a ∧ result ≤ b) ∧
  (result = a ∨ result = b)

theorem myMin_spec_satisfied (a : Int) (b : Int) :
  myMin_spec a b (myMin a b) := by
  unfold myMin myMin_spec
  by_cases h : a ≤ b
  . simp [h]
    apply And.intro
    . apply And.intro
      . apply le_refl
      . assumption
    . apply Or.inl; rfl
  . simp [h]
    apply And.intro
    . apply And.intro
      . apply le_of_lt
        apply lt_of_not_ge
        assumption
      . apply le_refl
    . apply Or.inr; rfl 