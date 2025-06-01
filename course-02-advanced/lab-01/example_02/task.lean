/-- Function to check if a character should be kept in the normalized string -/
def isAlphaNumeric (c : Char) : Bool :=
  -- << CODE START >>
  c.isAlpha || c.isDigit
  -- << CODE END >>

/-- Function to normalize a string by removing non-alphanumeric characters and converting to lowercase -/
def normalize (s : String) : String :=
  -- << CODE START >>
  let chars := s.toList
  let filtered := chars.filter (fun c => isAlphaNumeric c)
  let lowercased := filtered.map Char.toLower
  String.mk lowercased
  -- << CODE END >>

/-- Function to reverse a string -/
def reverseString (s : String) : String :=
  -- << CODE START >>
  String.mk (s.toList.reverse)
  -- << CODE END >>

/-- Function to check if a string is a palindrome -/
def isPalindrome (s : String) : Bool :=
  -- << CODE START >>
  let normalized := normalize s
  normalized == reverseString normalized
  -- << CODE END >>

theorem isPalindrome_empty : isPalindrome "" = true := by
  -- << SPEC START >>
  simp [isPalindrome, normalize, reverseString]
  -- << SPEC END >>

-- Basic test cases
#eval! isPalindrome ""  -- true (empty string)
#eval! isPalindrome "a"  -- true (single character)
#eval! isPalindrome "racecar"  -- true (simple palindrome)
#eval! isPalindrome "hello"  -- false (non-palindrome)
#eval! isPalindrome "abc"  -- false (non-palindrome)

-- Complex test cases with spaces and punctuation
#eval! isPalindrome "A man a plan a canal Panama"  -- true
#eval! isPalindrome "Madam, I'm Adam"  -- true
#eval! isPalindrome "No lemon, no melon"  -- true
#eval! isPalindrome "Was it a car or a cat I saw?"  -- true

-- Edge cases and non-palindromes
#eval! isPalindrome "Lean 4"  -- false
#eval! isPalindrome "Almost a palindrome, emordnilap a tsomla"  -- false