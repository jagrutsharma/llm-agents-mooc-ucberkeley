## Example: isDivisible

```lean
-- Code for checking if a number is divisible by another
def isDivisible (n : Int) (m : Int) : Bool :=
  decide (n % m = 0)

-- Proof for the specification
theorem isDivisible_spec (n : Int) (m : Int) :
  (n % m = 0) ↔ (isDivisible n m) := by
  unfold isDivisible
  simp [decide_eq_true_iff]
```

## Example: Verification Error Handling with decide

```lean
-- Common error in decide proofs
def isEven (n : Int) : Bool :=
  decide (n % 2 = 0)

-- Error in proof
theorem isEven_spec_wrong (n : Int) :
  (n % 2 = 0) ↔ (isEven n) := by
  unfold isEven
  -- This is incomplete and will cause an error
  rfl

-- Correct proof
theorem isEven_spec_correct (n : Int) :
  (n % 2 = 0) ↔ (isEven n) := by
  unfold isEven
  simp [decide_eq_true_iff]
```

## Example: Other decide proofs

```lean
def isZero (n : Int) : Bool :=
  decide (n = 0)

theorem isZero_spec (n : Int) :
  (n = 0) ↔ (isZero n) := by
  unfold isZero
  simp [decide_eq_true_iff]
``` 