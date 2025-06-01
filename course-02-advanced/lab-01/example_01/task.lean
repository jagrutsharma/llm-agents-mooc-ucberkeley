def reverseList (xs : List α) : List α :=
  -- << CODE START >>
  match xs with
  | [] => []
  | h :: t => reverseList t ++ [h]
  -- << CODE END >>

def reverseList_spec_empty : reverseList ([] : List α) = [] :=
  -- << SPEC START >>
  rfl
  -- << SPEC END >>

theorem reverseList_spec_reverseReverse (xs : List α) : reverseList (reverseList xs) = xs := by
  -- << SPEC START >>
  induction xs with
  | nil =>
    unfold reverseList
    rfl
  | cons h t ih =>
    unfold reverseList
    simp
    exact ih
  -- << SPEC END >>

theorem reverseList_spec_length (xs : List α) : List.length (reverseList xs) = List.length xs := by
  -- << SPEC START >>
  induction xs with
  | nil =>
    unfold reverseList
    rfl
  | cons h t ih =>
    unfold reverseList
    simp
    exact ih
  -- << SPEC END >>

-- Test the reverse list function
#eval reverseList [1, 2, 3]  -- Should output [3, 2, 1]
#eval reverseList ([] : List Nat)  -- Should output []
#eval reverseList ["a", "b", "c"]  -- Should output ["c", "b", "a"]