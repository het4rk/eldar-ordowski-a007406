import Mathlib

/-!
# Partial results on the Eldar–Ordowski conjecture for A007406

`a n` is the numerator of `∑_{k=1}^n 1/k^2` (OEIS A007406), stated exactly as in
`google-deepmind/formal-conjectures`, `FormalConjectures/OEIS/7406.lean`.
-/

namespace Wolst

open Finset

/-- OEIS A007406, verbatim from formal-conjectures. -/
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

/-- OEIS A089026, verbatim from formal-conjectures. -/
def A89026 (n : ℕ) : ℕ :=
  if n.Prime then n else 1

/-- The second-order harmonic number. -/
def H (n : ℕ) : ℚ := ∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2

lemma a_eq (n : ℕ) : a n = (H n).num.natAbs := rfl

lemma H_pos {n : ℕ} (hn : 1 ≤ n) : 0 < H n := by
  unfold H
  apply Finset.sum_pos
  · intro k hk
    have : (0:ℚ) < k := by
      have := (Finset.mem_Icc.1 hk).1; exact_mod_cast (by omega : 0 < k)
    positivity
  · exact ⟨1, by simp [hn]⟩

/-- Valuation of a finite sum of positive rationals is at least the minimum bound. -/
lemma le_padicValRat_sum {q : ℕ} [Fact q.Prime] {c : ℤ} (S : Finset ℕ) (F : ℕ → ℚ)
    (hpos : ∀ i ∈ S, 0 < F i) (hS : S.Nonempty)
    (hF : ∀ i ∈ S, c ≤ padicValRat q (F i)) : c ≤ padicValRat q (∑ i ∈ S, F i) := by
  induction hS using Finset.Nonempty.cons_induction with
  | singleton k => simpa using hF k (by simp)
  | cons s S' hnot hne ih =>
    rw [Finset.sum_cons]
    have h1 : 0 < F s := hpos s (by simp)
    have h2 : 0 < ∑ i ∈ S', F i :=
      Finset.sum_pos (fun i hi => hpos i (by simp [hi])) hne
    refine le_trans (le_min (hF s (by simp)) (ih (fun i hi => hpos i (by simp [hi]))
      (fun i hi => hF i (by simp [hi])))) ?_
    exact padicValRat.min_le_padicValRat_add (ne_of_gt (add_pos h1 h2))

lemma padicValRat_inv_sq {q : ℕ} [Fact q.Prime] {k : ℕ} (hk : k ≠ 0) :
    padicValRat q ((1 : ℚ) / (k : ℚ) ^ 2) = -2 * (padicValNat q k : ℤ) := by
  have hk' : (k : ℚ) ≠ 0 := by exact_mod_cast hk
  rw [one_div, padicValRat.inv, padicValRat.pow, padicValRat.of_nat]
  ring

/-- If `U < q` and `q` does not divide the numerator of `H U`, then `v_q(H U) = 0`. -/
lemma padicValRat_H_small {q : ℕ} [hq : Fact q.Prime] {U : ℕ} (hU1 : 1 ≤ U) (hUq : U < q)
    (hnd : ¬ q ∣ a U) : padicValRat q (H U) = 0 := by
  have hpos := H_pos hU1
  have hge : (0 : ℤ) ≤ padicValRat q (H U) := by
    unfold H
    apply le_padicValRat_sum
    · intro k hk
      have : (0:ℚ) < k := by
        have := (Finset.mem_Icc.1 hk).1; exact_mod_cast (by omega : 0 < k)
      positivity
    · exact ⟨1, by simp [hU1]⟩
    · intro k hk
      obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
      rw [padicValRat_inv_sq (by omega)]
      have : padicValNat q k = 0 :=
        padicValNat.eq_zero_of_not_dvd (fun h => by
          have := Nat.le_of_dvd (by omega) h; omega)
      simp [this]
  have hle : padicValRat q (H U) ≤ 0 := by
    rw [padicValRat]
    have hnum : padicValInt q (H U).num = 0 := by
      apply padicValInt.eq_zero_of_not_dvd
      intro h
      apply hnd
      rw [a_eq]
      exact Int.natCast_dvd.mp h |> fun h' => by simpa using h'
    rw [hnum]; simp
  omega

/-- The key "leading digit" lemma: with `s = log_q m` and `U = ⌊m/q^s⌋`,
`v_q(H m) = -2s` provided `q ∤ a U`. -/
theorem padicValRat_H {q : ℕ} [hq : Fact q.Prime] {m : ℕ} (hm : 1 ≤ m)
    (hnd : ¬ q ∣ a (m / q ^ Nat.log q m)) :
    padicValRat q (H m) = -2 * (Nat.log q m : ℤ) := by
  set s := Nat.log q m with hs
  set U := m / q ^ s with hUdef
  have hq1 : 1 < q := hq.out.one_lt
  have hqs_pos : 0 < q ^ s := pow_pos (by omega) s
  have hqs_le : q ^ s ≤ m := Nat.pow_log_le_self q (by omega)
  have hm_lt : m < q ^ (s + 1) := Nat.lt_pow_succ_log_self hq1 m
  have hU1 : 1 ≤ U := by
    rw [hUdef, Nat.le_div_iff_mul_le hqs_pos]; omega
  have hUq : U < q := by
    rw [hUdef, Nat.div_lt_iff_lt_mul hqs_pos]
    calc m < q ^ (s+1) := hm_lt
      _ = q * q ^ s := by ring
  have hHU := padicValRat_H_small hU1 hUq hnd
  -- split the sum
  set S1 := (Finset.Icc 1 m).filter (fun k => q ^ s ∣ k) with hS1
  set S0 := (Finset.Icc 1 m).filter (fun k => ¬ q ^ s ∣ k) with hS0
  have hsplit : H m = (∑ k ∈ S1, (1:ℚ) / (k:ℚ)^2) + ∑ k ∈ S0, (1:ℚ) / (k:ℚ)^2 := by
    unfold H; rw [Finset.sum_filter_add_sum_filter_not]
  -- S1 sum
  have hS1sum : (∑ k ∈ S1, (1:ℚ) / (k:ℚ)^2) = (((q:ℚ) ^ s) ^ 2)⁻¹ * H U := by
    have : S1 = (Finset.Icc 1 U).map ⟨fun u => q ^ s * u, fun x y h => Nat.eq_of_mul_eq_mul_left hqs_pos h⟩ := by
      ext k
      simp only [hS1, Finset.mem_filter, Finset.mem_Icc, Finset.mem_map,
        Function.Embedding.coeFn_mk]
      constructor
      · rintro ⟨⟨hk1, hk2⟩, ⟨u, rfl⟩⟩
        refine ⟨u, ⟨?_, ?_⟩, rfl⟩
        · rcases Nat.eq_zero_or_pos u with h | h
          · subst h; simp at hk1
          · exact h
        · rw [hUdef, Nat.le_div_iff_mul_le hqs_pos]; linarith [mul_comm u (q ^ s)]
      · rintro ⟨u, ⟨hu1, hu2⟩, rfl⟩
        show (1 ≤ q ^ s * u ∧ q ^ s * u ≤ m) ∧ q ^ s ∣ q ^ s * u
        refine ⟨⟨?_, ?_⟩, dvd_mul_right _ _⟩
        · exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero hqs_pos.ne' (by omega))
        · rw [hUdef, Nat.le_div_iff_mul_le hqs_pos] at hu2; linarith [mul_comm u (q ^ s)]
    rw [this, Finset.sum_map]
    unfold H
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun u hu => ?_)
    have hu0 : (u:ℚ) ≠ 0 := by
      have := (Finset.mem_Icc.1 hu).1; exact_mod_cast (by omega : u ≠ 0)
    have hq0' : (q:ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
    show (1:ℚ) / ((q ^ s * u : ℕ) : ℚ) ^ 2 = (((q:ℚ) ^ s) ^ 2)⁻¹ * (1 / (u:ℚ) ^ 2)
    push_cast
    field_simp
  have hq0 : (q:ℚ) ≠ 0 := by exact_mod_cast hq.out.ne_zero
  have hHUpos := H_pos hU1
  have hv1 : padicValRat q (∑ k ∈ S1, (1:ℚ) / (k:ℚ)^2) = -2 * (s:ℤ) := by
    rw [hS1sum, padicValRat.mul (by positivity) hHUpos.ne', hHU, padicValRat.inv,
      padicValRat.pow, padicValRat.pow, padicValRat.self hq1]
    ring
  have hS1pos : 0 < ∑ k ∈ S1, (1:ℚ) / (k:ℚ)^2 := by rw [hS1sum]; positivity
  rcases S0.eq_empty_or_nonempty with h0 | h0
  · rw [hsplit, h0, Finset.sum_empty, add_zero, hv1]
  · have hS0pos : 0 < ∑ k ∈ S0, (1:ℚ) / (k:ℚ)^2 := by
      apply Finset.sum_pos _ h0
      intro k hk
      have : (0:ℚ) < k := by
        have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
        exact_mod_cast (by omega : 0 < k)
      positivity
    have hv0 : -2 * (s:ℤ) + 1 ≤ padicValRat q (∑ k ∈ S0, (1:ℚ) / (k:ℚ)^2) := by
      apply le_padicValRat_sum _ _ _ h0
      · intro k hk
        obtain ⟨hk, hnd'⟩ := Finset.mem_filter.1 hk
        obtain ⟨hk1, hk2⟩ := Finset.mem_Icc.1 hk
        rw [padicValRat_inv_sq (by omega)]
        have : padicValNat q k < s := by
          by_contra hcon
          push Not at hcon
          exact hnd' ((padicValNat_dvd_iff_le (by omega)).2 hcon)
        omega
      · intro k hk
        have : (0:ℚ) < k := by
          have := (Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1).1
          exact_mod_cast (by omega : 0 < k)
        positivity
    rw [hsplit, padicValRat.add_eq_of_lt (by positivity) hS1pos.ne' hS0pos.ne' (by omega), hv1]

/-- Leading-digit criterion: `q ∤ a m` whenever `q ∤ a (⌊m / q^{log_q m}⌋)` and `log_q m ≥ 1`
(in fact `≥ 0` suffices for the valuation, but we need `s ≥ 1` to conclude). -/
theorem not_dvd_a {q : ℕ} (hqp : q.Prime) {m : ℕ} (hqm : q ≤ m)
    (hnd : ¬ q ∣ a (m / q ^ Nat.log q m)) : ¬ q ∣ a m := by
  have : Fact q.Prime := ⟨hqp⟩
  have hm : 1 ≤ m := le_trans hqp.one_lt.le hqm
  have hv := padicValRat_H hm hnd
  have hs : 1 ≤ Nat.log q m := Nat.le_log_of_pow_le hqp.one_lt (by simpa using hqm)
  intro hdvd
  have hpos := H_pos hm
  have hnum : 1 ≤ padicValInt q (H m).num := by
    have hne : (H m).num.natAbs ≠ 0 := by
      simpa using (Rat.num_ne_zero.2 hpos.ne')
    show 1 ≤ padicValNat q (H m).num.natAbs
    exact one_le_padicValNat_of_dvd hne (by simpa [a_eq] using hdvd)
  have hden : padicValNat q (H m).den = 0 := by
    rcases Rat.num_or_den_zero_padicVal (H m) hqp with h | h
    · omega
    · exact h
  have : padicValRat q (H m) = padicValInt q (H m).num - padicValNat q (H m).den := rfl
  omega

end Wolst
