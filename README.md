# Partial results on the Eldar–Ordowski conjecture (OEIS A007406)

**Conjecture** (A. Eldar and T. Ordowski, 2019; listed as open on https://oeis.org/A007406, and as
`OeisA7406.conjecture`, tagged `research open`, in google-deepmind/formal-conjectures):
for n > 3, gcd(n, a(n-1)) = A089026(n), where a(n) is the numerator of sum_{k<=n} 1/k^2.
The prime case is Wolstenholme's theorem, so what remains open is that gcd(n, a(n-1)) = 1 for composite n.

**Proved here (Lean 4 + Mathlib, no sorry, axioms = propext, Classical.choice, Quot.sound):**
- `padicValRat_H`, `not_dvd_a`: leading-digit lemma. Let U be the leading base-q digit of m.
  If q does not divide a(U), then v_q(H_m) = -2*floor(log_q m), and in particular q does not divide a(m).
- `conjecture_of_leading_digits`: a general sufficient criterion for any composite n.
- `coprime_six_a`: gcd(6, a(m)) = 1 for all m >= 1.
- `conjecture_smooth`: the conjecture holds for all n = 2^i 3^j > 3.
- `conjecture_smooth_mul_prime`: the conjecture holds for n = c*q, where c >= 2 is 3-smooth,
  q > c is prime, and q does not divide a(c-1).
- `conjecture_two_mul_prime`, `conjecture_three_mul_prime`, `conjecture_four_mul_prime`: the cases
  n = 2q (q >= 3), n = 3q (q >= 7) and n = 4q (q >= 5, q != 7).
- `conjecture_smooth_mul_prime_pow`: n = c*q^k for any k >= 1 under the same hypotheses; `conjecture_two_mul_prime_pow`: n = 2*q^k for every odd prime q.
- `prime_dvd_a`, `conjecture_prime`: Wolstenholme's theorem p | a(p-1) for p >= 5, formalized, so the conjectured equality holds at every prime n > 3.
- `conjecture_on_families`: the full equality holds for every n > 3 that is prime, 3-smooth, or 2*q^k.
- `conjecture_smooth_mul_large_prime`: for each 3-smooth c, the conjecture holds at n = c*q for all large primes q.

Each statement ends in exactly `Nat.gcd n (a (n - 1)) = A89026 n`, with `a` and `A89026` copied verbatim from formal-conjectures.

Not covered: n = q^k (leading digit q-1, which q always divides), general n = pq, and the q^2 case (would need Glaisher-type congruences).

Build: `cd Wolst && lake build && lake env lean Axioms.lean` (see `Wolst/axioms.txt`).
Paper: `paper/paper.pdf`. Coverage script: `paper/coverage.py`. The criterion settles 84% of the composites up to 10^5; this is computed, not formalized.
The full conjecture remains open. The criterion can never cover, for example, n = q^2, since q divides a(q-1).

## Exact match with upstream definitions

Upstream: [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures) at commit `34ee0e3c5fd52d202d62a71094a37970cb5fb870` (main, Oct 12 2026).

`FormalConjectures/OEIS/7406.lean`:
```lean
def a (n : ℕ) : ℕ :=
  (∑ k ∈ Finset.Icc 1 n, (1 : ℚ) / (k : ℚ) ^ 2).num.natAbs

theorem conjecture (n : ℕ) (hn : 3 < n) :
    Nat.gcd n (a (n - 1)) = OeisA89026.a n := by
  sorry
```
`FormalConjectures/OEIS/89026.lean`:
```lean
def a (n : ℕ) : ℕ :=
  if n.Prime then n else 1
```
`Wolst.a` and `Wolst.A89026` in `Wolst/Wolst/Basic.lean` have exactly these bodies, character for character, and every main theorem concludes `Nat.gcd n (a (n - 1)) = A89026 n`. (Upstream issue #4410 concerns a different, auto-generated file on the `auto_oeis` branch, not this one.)

## Independent verification

`verification/clean_build.log` comes from a fresh `git clone` of this repo, followed by `lake exe cache get`, `lake build` (`Build completed successfully (9024 jobs)`) and `lake env lean Axioms.lean`. All 15 reported declarations depend only on `[propext, Classical.choice, Quot.sound]`.
CI (`.github/workflows/lean.yml`) repeats this on every push. It fails on any `declaration uses 'sorry'` warning, and `scripts/check_axioms.sh` fails on any axiom outside that list (so `sorryAx` and `Lean.ofReduceBool` are rejected).

## Related work (honest novelty assessment)

The leading-digit valuation lemma (`padicValRat_H`) is **not new**. It is the order-2 analogue of the standard argument for J(p) = {n : p | numerator of H_n} (Eswarathasan–Levine 1991, Boyd 1994, Kamano 2011, Sanna 2016, Wu–Chen 2017). Generalized harmonic numbers H_n^(r) are treated in the same framework by Ç. Altuntaş (Bull. Korean Math. Soc. 60 (2023) 933–955). Wolstenholme's congruence p | a(p-1) is classical (1862), and Glaisher (1900) gives the refinement mod p^2. We found no work applying these tools to the Eldar–Ordowski gcd conjecture. What is new here is (i) the reduction of that conjecture to the leading-digit criterion, (ii) the explicit infinite families, and (iii) the first machine-checked proofs of them.
