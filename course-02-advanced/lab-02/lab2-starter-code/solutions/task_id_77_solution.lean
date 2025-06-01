import Mathlib
import Aesop

-- Implementation
def isDivisibleBy11 (n : Int) : Bool :=
  decide (n % 11 = 0)


-- Theorem: The result is true if n is divisible by 11
def isDivisibleBy11_spec (n : Int) (result : Bool) : Prop :=
  n % 11 = 0 ↔ result

theorem isDivisibleBy11_spec_satisfied (n : Int) :
  isDivisibleBy11_spec n (isDivisibleBy11 n) := by
  unfold isDivisibleBy11 isDivisibleBy11_spec
  simp [decide_eq_true_iff] 