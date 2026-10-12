import Wolst.Families

/-! # Wolstenholme's theorem for `H^{(2)}` and the prime direction of the conjecture -/

namespace Wolst
open Finset Nat

lemma sum_zmod_pow (p : ℕ) [Fact p.Prime] (i : ℕ) :
    ∑ k ∈ range p, ((k : ZMod p)) ^ i = ∑ x : ZMod p, x ^ i := by
  refine Finset.sum_nbij (fun k : ℕ => (k : ZMod p)) ?_ ?_ ?_ ?_
  · intro _ _; simp
  · intro x hx y hy h
    simp only [coe_range, Set.mem_Iio] at hx hy
    exact (ZMod.natCast_eq_natCast_iff' x y p).1 h |> fun h' => by
      rwa [Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy] at h'
  · intro x _
    refine ⟨x.val, by simp [ZMod.val_lt], ZMod.natCast_zmod_val x⟩
  · intro _ _; rfl

/-- Wolstenholme: for a prime `p ≥ 5`, `p` divides the numerator of `H^{(2)}_{p-1}`. -/
theorem prime_dvd_a {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p) : p ∣ a (p - 1) := by
  have : Fact p.Prime := ⟨hp⟩
  set F := (p - 1)! with hF
  set N : ℕ := ∑ k ∈ Icc 1 (p - 1), (F / k) ^ 2 with hN
  -- `H * F^2 = N`
  have hHN : H (p - 1) * (F : ℚ) ^ 2 = (N : ℚ) := by
    rw [H, Finset.sum_mul, hN]; push_cast
    refine Finset.sum_congr rfl (fun k hk => ?_)
    obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
    have hdvd : k ∣ F := Nat.dvd_factorial (by omega) hk2
    have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
    rw [Nat.cast_div hdvd hk0]
    field_simp
  -- `p ∣ N`
  have hpN : p ∣ N := by
    rw [← ZMod.natCast_eq_zero_iff]
    have hW : (F : ZMod p) = -1 := ZMod.wilsons_lemma (p := p)
    have hterm : ∀ k ∈ Icc 1 (p - 1), (((F / k) ^ 2 : ℕ) : ZMod p) = (k : ZMod p) ^ (p - 3) := by
      intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
      have hdvd : k ∣ F := Nat.dvd_factorial (by omega) hk2
      have hk0 : (k : ZMod p) ≠ 0 := by
        rw [Ne, ZMod.natCast_eq_zero_iff]
        intro h; have := Nat.le_of_dvd (by omega) h; omega
      have hmul : (k : ZMod p) * ((F / k : ℕ) : ZMod p) = -1 := by
        rw [← hW, ← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      have hferm : (k : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hk0
      have he : p - 1 = 2 + (p - 3) := by omega
      push_cast
      calc ((F / k : ℕ) : ZMod p) ^ 2
          = ((F / k : ℕ) : ZMod p) ^ 2 * (k : ZMod p) ^ (p - 1) := by rw [hferm, mul_one]
        _ = ((k : ZMod p) * ((F / k : ℕ) : ZMod p)) ^ 2 * (k : ZMod p) ^ (p - 3) := by
            rw [he, pow_add]; ring
        _ = (k : ZMod p) ^ (p - 3) := by rw [hmul]; ring
    rw [hN]; push_cast
    rw [Finset.sum_congr rfl (fun k hk => by exact_mod_cast hterm k hk)]
    have hsplit : ∑ k ∈ range p, ((k : ZMod p)) ^ (p - 3)
        = ∑ k ∈ Icc 1 (p - 1), ((k : ZMod p)) ^ (p - 3) := by
      have : range p = insert 0 (Icc 1 (p - 1)) := by
        ext k; simp only [mem_range, mem_insert, mem_Icc]; omega
      rw [this, Finset.sum_insert (by simp)]
      simp [zero_pow (by omega : p - 3 ≠ 0)]
    push_cast
    rw [← hsplit, sum_zmod_pow, FiniteField.sum_pow_lt_card_sub_one]
    rw [ZMod.card]; omega
  -- transfer to the numerator
  have hpF : ¬ p ∣ F ^ 2 := by
    intro h
    have := (Nat.Prime.dvd_factorial hp).1 (hp.dvd_of_dvd_pow h)
    omega
  set x := H (p - 1)
  have hx : (x.num : ℚ) * (F : ℚ) ^ 2 = (N : ℚ) * x.den := by
    rw [← Rat.mul_den_eq_num, ← hHN]; ring
  have hxz : x.num * ((F ^ 2 : ℕ) : ℤ) = (N : ℤ) * x.den := by
    exact_mod_cast hx
  have : (p : ℤ) ∣ x.num * ((F ^ 2 : ℕ) : ℤ) := by
    rw [hxz]; exact Dvd.dvd.mul_right (Int.natCast_dvd_natCast.2 hpN) _
  rcases (Int.Prime.dvd_mul' hp this) with h | h
  · rw [a_eq]; exact Int.natCast_dvd.mp h
  · exact absurd (Int.natCast_dvd_natCast.1 h) hpF

/-- **Prime direction of the conjecture** (all primes `p > 3`). -/
theorem conjecture_prime {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    Nat.gcd p (a (p - 1)) = A89026 p := by
  rw [A89026, if_pos hp]
  have h4 : p ≠ 4 := by rintro rfl; norm_num at hp
  exact Nat.gcd_eq_left (prime_dvd_a hp (by omega))

end Wolst

namespace Wolst

/-- **Theorem (`n = c q^k`).** Let `c = 2^i 3^j ≥ 2`, `q > c` prime with `q ∤ a (c-1)`, `k ≥ 1`.
Then the conjecture holds for `n = c q^k`. -/
theorem conjecture_smooth_mul_prime_pow (i j q k : ℕ) (hc : 2 ≤ 2 ^ i * 3 ^ j)
    (hq : q.Prime) (hcq : 2 ^ i * 3 ^ j < q) (hk : 1 ≤ k)
    (hnd : ¬ q ∣ a (2 ^ i * 3 ^ j - 1)) :
    Nat.gcd (2 ^ i * 3 ^ j * q ^ k) (a (2 ^ i * 3 ^ j * q ^ k - 1))
      = A89026 (2 ^ i * 3 ^ j * q ^ k) := by
  set c := 2 ^ i * 3 ^ j with hcdef
  have hq2 := hq.two_le
  set Q := q ^ k with hQ
  have hQ2 : q ≤ Q := by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ k := Nat.pow_le_pow_right (by omega) hk
  have hcQ : 2 * Q ≤ c * Q := Nat.mul_le_mul_right Q hc
  have hnp : ¬ (c * Q).Prime := Nat.not_prime_mul (by omega) (by omega)
  rw [A89026, if_neg hnp]
  apply Nat.Coprime.gcd_eq_one
  apply Nat.coprime_of_dvd
  intro r hr hdvd
  rcases (Nat.Prime.dvd_mul hr).1 hdvd with h | h
  · rcases prime_dvd_smooth hr h with rfl | rfl
    · exact two_not_dvd_a (by omega)
    · exact three_not_dvd_a (by omega)
  · have hrq : r = q := (Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h)
    subst hrq
    set m := c * Q - 1 with hm
    have hqm : r ≤ m := by omega
    apply not_dvd_a hr hqm
    have hc1 : c ≤ r - 1 := by omega
    have hlo : (c - 1) * Q ≤ m := by
      have : (c - 1) * Q = c * Q - Q := Nat.sub_one_mul c Q
      omega
    have hhi : m < c * Q := by omega
    have hmlt : m < r ^ (k + 1) := by
      have : c * Q ≤ (r - 1) * Q := Nat.mul_le_mul_right Q hc1
      have : (r - 1) * Q = r * Q - Q := Nat.sub_one_mul r Q
      have : r ^ (k + 1) = r * Q := by rw [hQ, pow_succ, mul_comm]
      omega
    have hQle : Q ≤ m := by
      have : 1 * Q ≤ (c - 1) * Q := Nat.mul_le_mul_right Q (by omega)
      omega
    have hlog : Nat.log r m = k := by
      rw [Nat.log_eq_iff (by omega)]
      exact ⟨hQle, hmlt⟩
    rw [hlog, ← hQ]
    have hdiv : m / Q = c - 1 := by
      apply Nat.div_eq_of_lt_le hlo
      rw [Nat.sub_add_cancel (by omega)]; exact hhi
    rw [hdiv]; exact hnd

/-- **Corollary.** For every prime `q ≥ 3` and `k ≥ 1`, the conjecture holds at `n = 2 q^k`. -/
theorem conjecture_two_mul_prime_pow (q k : ℕ) (hq : q.Prime) (h3 : 3 ≤ q) (hk : 1 ≤ k) :
    Nat.gcd (2 * q ^ k) (a (2 * q ^ k - 1)) = A89026 (2 * q ^ k) := by
  have := conjecture_smooth_mul_prime_pow 1 0 q k (by norm_num) hq (by norm_num; omega) hk
    (by norm_num [a_one]; exact hq.ne_one)
  simpa using this

/-- **Combined statement.** The full conjecture `gcd(n, a(n-1)) = A089026(n)` holds for every
`n > 3` that is prime, or 3-smooth, or of the form `2 q^k` with `q` an odd prime. -/
theorem conjecture_on_families (n : ℕ) (hn : 3 < n)
    (h : n.Prime ∨ (∃ i j, n = 2 ^ i * 3 ^ j) ∨ (∃ q k, q.Prime ∧ 3 ≤ q ∧ 1 ≤ k ∧ n = 2 * q ^ k)) :
    Nat.gcd n (a (n - 1)) = A89026 n := by
  rcases h with h | ⟨i, j, rfl⟩ | ⟨q, k, hq, h3, hk, rfl⟩
  · exact conjecture_prime h hn
  · exact conjecture_smooth i j hn
  · exact conjecture_two_mul_prime_pow q k hq h3 hk

end Wolst
