import Wolst.Basic

namespace Wolst

lemma a_one : a 1 = 1 := by
  rw [a_eq, H]; norm_num [Finset.sum_Icc_succ_top]
lemma a_two : a 2 = 5 := by
  rw [a_eq, H]; norm_num [Finset.sum_Icc_succ_top]
lemma a_three : a 3 = 49 := by
  rw [a_eq, H]; norm_num [Finset.sum_Icc_succ_top]

lemma a_pos {n : ℕ} (hn : 1 ≤ n) : 0 < a n := by
  rw [a_eq]
  have := Rat.num_ne_zero.2 (H_pos hn).ne'
  omega

lemma leading_bounds {q m : ℕ} (hq : 1 < q) (hm : 1 ≤ m) :
    1 ≤ m / q ^ Nat.log q m ∧ m / q ^ Nat.log q m < q := by
  have hqs_pos : 0 < q ^ Nat.log q m := pow_pos (by omega) _
  have hle : q ^ Nat.log q m ≤ m := Nat.pow_log_le_self q (by omega)
  have hlt : m < q ^ (Nat.log q m + 1) := Nat.lt_pow_succ_log_self hq m
  constructor
  · rw [Nat.le_div_iff_mul_le hqs_pos]; omega
  · rw [Nat.div_lt_iff_lt_mul hqs_pos]
    calc m < q ^ (Nat.log q m + 1) := hlt
      _ = q * q ^ Nat.log q m := by ring

/-- `2` never divides a Wolstenholme number `a m` (`m ≥ 1`). -/
theorem two_not_dvd_a {m : ℕ} (hm : 1 ≤ m) : ¬ 2 ∣ a m := by
  rcases Nat.lt_or_ge m 2 with h | h
  · obtain rfl : m = 1 := by omega
    rw [a_one]; decide
  · apply not_dvd_a Nat.prime_two h
    obtain ⟨h1, h2⟩ := leading_bounds (q := 2) (by norm_num) hm
    have : m / 2 ^ Nat.log 2 m = 1 := by omega
    rw [this, a_one]; decide

/-- `3` never divides a Wolstenholme number `a m` (`m ≥ 1`). -/
theorem three_not_dvd_a {m : ℕ} (hm : 1 ≤ m) : ¬ 3 ∣ a m := by
  have key : ∀ U, 1 ≤ U → U < 3 → ¬ 3 ∣ a U := by
    intro U h1 h2
    interval_cases U
    · rw [a_one]; decide
    · rw [a_two]; decide
  rcases Nat.lt_or_ge m 3 with h | h
  · exact key m hm h
  · apply not_dvd_a Nat.prime_three h
    obtain ⟨h1, h2⟩ := leading_bounds (q := 3) (by norm_num) hm
    exact key _ h1 h2

lemma prime_dvd_smooth {k i j : ℕ} (hk : k.Prime) (h : k ∣ 2 ^ i * 3 ^ j) : k = 2 ∨ k = 3 := by
  rcases (Nat.Prime.dvd_mul hk).1 h with h | h
  · left; exact (Nat.prime_dvd_prime_iff_eq hk Nat.prime_two).1 (hk.dvd_of_dvd_pow h)
  · right; exact (Nat.prime_dvd_prime_iff_eq hk Nat.prime_three).1 (hk.dvd_of_dvd_pow h)

/-- **Theorem.** For every `m ≥ 1`, `gcd(6, a m) = 1`. -/
theorem coprime_six_a {m : ℕ} (hm : 1 ≤ m) : Nat.Coprime 6 (a m) := by
  apply Nat.coprime_of_dvd
  intro k hk hdvd
  have : k = 2 ∨ k = 3 := prime_dvd_smooth (i := 1) (j := 1) hk (by simpa using hdvd)
  rcases this with rfl | rfl
  · exact two_not_dvd_a hm
  · exact three_not_dvd_a hm

/-- **Theorem (3-smooth `n`).** The Eldar–Ordowski conjecture holds for every
`n = 2^i 3^j > 3`. -/
theorem conjecture_smooth (i j : ℕ) (hn : 3 < 2 ^ i * 3 ^ j) :
    Nat.gcd (2 ^ i * 3 ^ j) (a (2 ^ i * 3 ^ j - 1)) = A89026 (2 ^ i * 3 ^ j) := by
  set n := 2 ^ i * 3 ^ j
  have hnp : ¬ n.Prime := by
    intro hp
    rcases prime_dvd_smooth hp (dvd_refl _) with h | h <;> omega
  rw [A89026, if_neg hnp]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro k hk hdvd
  rcases prime_dvd_smooth hk hdvd with rfl | rfl
  · exact two_not_dvd_a (by omega)
  · exact three_not_dvd_a (by omega)

/-- **Theorem (`n = c q`).** Let `c = 2^i 3^j ≥ 2`, and let `q > c` be a prime not dividing
`a (c-1)`. Then the conjecture holds for `n = c q`. -/
theorem conjecture_smooth_mul_prime (i j q : ℕ) (hc : 2 ≤ 2 ^ i * 3 ^ j)
    (hq : q.Prime) (hcq : 2 ^ i * 3 ^ j < q) (hnd : ¬ q ∣ a (2 ^ i * 3 ^ j - 1)) :
    Nat.gcd (2 ^ i * 3 ^ j * q) (a (2 ^ i * 3 ^ j * q - 1)) = A89026 (2 ^ i * 3 ^ j * q) := by
  set c := 2 ^ i * 3 ^ j with hcdef
  have hq2 := hq.two_le
  have hcq_ge : 2 * q ≤ c * q := Nat.mul_le_mul_right q hc
  have hnp : ¬ (c * q).Prime := Nat.not_prime_mul (by omega) (by omega)
  rw [A89026, if_neg hnp]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro k hk hdvd
  rcases (Nat.Prime.dvd_mul hk).1 hdvd with h | h
  · rcases prime_dvd_smooth hk h with rfl | rfl
    · exact two_not_dvd_a (by omega)
    · exact three_not_dvd_a (by omega)
  · obtain rfl : k = q := (Nat.prime_dvd_prime_iff_eq hk hq).1 h
    set m := c * k - 1 with hm
    have hqm : k ≤ m := by omega
    apply not_dvd_a hk hqm
    have hc1 : c ≤ k - 1 := by omega
    have hmlt : m < k ^ 2 := by
      have : c * k ≤ (k - 1) * k := Nat.mul_le_mul_right k hc1
      have : (k - 1) * k + k = k ^ 2 := by
        cases k with
        | zero => omega
        | succ k => simp [sq]; ring
      omega
    have hlog : Nat.log k m = 1 := by
      rw [Nat.log_eq_iff (by norm_num)]
      exact ⟨by simpa using hqm, by simpa using hmlt⟩
    rw [hlog, pow_one]
    have hdiv : m / k = c - 1 := by
      apply Nat.div_eq_of_lt_le
      · have : (c - 1) * k = c * k - k := Nat.sub_one_mul c k
        omega
      · have : (c - 1 + 1) * k = c * k := by
          rw [Nat.sub_add_cancel (by omega)]
        omega
    rw [hdiv]; exact hnd

/-- **Corollary.** The conjecture holds for `n = 2q`, every prime `q ≥ 3`. -/
theorem conjecture_two_mul_prime (q : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) :
    Nat.gcd (2 * q) (a (2 * q - 1)) = A89026 (2 * q) := by
  have := conjecture_smooth_mul_prime 1 0 q (by norm_num) hq (by norm_num; omega)
    (by norm_num [a_one]; exact hq.ne_one)
  simpa using this

/-- **Corollary.** The conjecture holds for `n = 3q`, every prime `q ≥ 7`. -/
theorem conjecture_three_mul_prime (q : ℕ) (hq : q.Prime) (h7 : 7 ≤ q) :
    Nat.gcd (3 * q) (a (3 * q - 1)) = A89026 (3 * q) := by
  have := conjecture_smooth_mul_prime 0 1 q (by norm_num) hq (by norm_num; omega)
    (by
      norm_num [a_two]
      intro h
      have := Nat.le_of_dvd (by norm_num) h
      omega)
  simpa using this

/-- **Corollary.** The conjecture holds for `n = 4q`, every prime `q ≥ 5`, `q ≠ 7`. -/
theorem conjecture_four_mul_prime (q : ℕ) (hq : q.Prime) (h5 : 5 ≤ q) (h7 : q ≠ 7) :
    Nat.gcd (4 * q) (a (4 * q - 1)) = A89026 (4 * q) := by
  have := conjecture_smooth_mul_prime 2 0 q (by norm_num) hq (by norm_num; omega)
    (by
      norm_num [a_three]
      intro h
      have h' : q ∣ 7 ^ 2 := by norm_num; exact h
      have := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 (hq.dvd_of_dvd_pow h')
      exact h7 this)
  simpa using this

/-- **Corollary.** For each `3`-smooth `c ≥ 2`, the conjecture holds for `n = c q` for all
sufficiently large primes `q`. -/
theorem conjecture_smooth_mul_large_prime (i j : ℕ) (hc : 2 ≤ 2 ^ i * 3 ^ j) :
    ∃ N, ∀ q, q.Prime → N < q →
      Nat.gcd (2 ^ i * 3 ^ j * q) (a (2 ^ i * 3 ^ j * q - 1)) = A89026 (2 ^ i * 3 ^ j * q) := by
  refine ⟨max (2 ^ i * 3 ^ j) (a (2 ^ i * 3 ^ j - 1)), fun q hq hN => ?_⟩
  apply conjecture_smooth_mul_prime i j q hc hq (lt_of_le_of_lt (le_max_left _ _) hN)
  intro h
  have hpos := a_pos (n := 2 ^ i * 3 ^ j - 1) (by omega)
  have := Nat.le_of_dvd hpos h
  have := le_max_right (2 ^ i * 3 ^ j) (a (2 ^ i * 3 ^ j - 1))
  omega

end Wolst

namespace Wolst

/-- **General criterion.** If `n > 3` is composite and every prime `q ∣ n` fails to divide
`a(U_q)`, where `U_q` is the leading base-`q` digit of `n - 1`, then the conjecture holds at `n`. -/
theorem conjecture_of_leading_digits (n : ℕ) (hn : 3 < n) (hnp : ¬ n.Prime)
    (h : ∀ q, q.Prime → q ∣ n → ¬ q ∣ a ((n - 1) / q ^ Nat.log q (n - 1))) :
    Nat.gcd n (a (n - 1)) = A89026 n := by
  rw [A89026, if_neg hnp]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro q hq hqn
  have hqlt : q < n := lt_of_le_of_ne (Nat.le_of_dvd (by omega) hqn)
    (fun he => hnp (he ▸ hq))
  exact not_dvd_a hq (by omega) (h q hq hqn)

end Wolst
