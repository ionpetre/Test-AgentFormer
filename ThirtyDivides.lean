import Lean

/-- For every integer `n`, the integer `n^5 - n` is divisible by 30. -/
theorem thirty_dvd_pow_five_sub_self (n : Int) : 30 ∣ n ^ 5 - n := by
  have factorization : n ^ 5 - n = (n - 1) * n * (n + 1) * (n * n + 1) := by
    grind

  have of_factor {d : Int}
      (h : d ∣ n - 1 ∨ d ∣ n ∨ d ∣ n + 1 ∨ d ∣ n * n + 1) :
      d ∣ n ^ 5 - n := by
    rw [factorization]
    rcases h with h | h | h | h
    · exact Int.dvd_mul_of_dvd_left <| Int.dvd_mul_of_dvd_left <| Int.dvd_mul_of_dvd_left h
    · exact Int.dvd_mul_of_dvd_left <| Int.dvd_mul_of_dvd_left <| Int.dvd_mul_of_dvd_right h
    · exact Int.dvd_mul_of_dvd_left <| Int.dvd_mul_of_dvd_right h
    · exact Int.dvd_mul_of_dvd_right h

  have by_two : 2 ∣ n ^ 5 - n := by
    apply of_factor
    have h : 2 ∣ n - 1 ∨ 2 ∣ n := by omega
    exact h.elim Or.inl fun h => Or.inr (Or.inl h)

  have by_three : 3 ∣ n ^ 5 - n := by
    apply of_factor
    have h : 3 ∣ n - 1 ∨ 3 ∣ n ∨ 3 ∣ n + 1 := by omega
    rcases h with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))

  have by_five : 5 ∣ n ^ 5 - n := by
    apply of_factor
    have residues : n % 5 = 0 ∨ n % 5 = 1 ∨ n % 5 = 2 ∨
        n % 5 = 3 ∨ n % 5 = 4 := by omega
    rcases residues with h | h | h | h | h
    · right; left; omega
    · left; omega
    · right; right; right
      apply Int.dvd_iff_emod_eq_zero.mpr
      rw [Int.add_emod, Int.mul_emod, h]
      decide
    · right; right; right
      apply Int.dvd_iff_emod_eq_zero.mpr
      rw [Int.add_emod, Int.mul_emod, h]
      decide
    · right; right; left; omega

  -- Combine the divisibilities using 6(a - b) = 2a when 2a = 3b.
  have by_six : 6 ∣ n ^ 5 - n := by
    obtain ⟨a, ha⟩ := by_two
    obtain ⟨b, hb⟩ := by_three
    exact ⟨a - b, by omega⟩

  obtain ⟨a, ha⟩ := by_six
  obtain ⟨b, hb⟩ := by_five
  exact ⟨b - a, by omega⟩
