# Partial results on the Eldar–Ordowski gcd conjecture (OEIS A007406)

[![Lean build](https://github.com/het4rk/eldar-ordowski-a007406/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/eldar-ordowski-a007406/actions/workflows/lean.yml)

**Author:** Hetark Shah, AI-assisted by Grok  
**Date:** October 12, 2026

## Result

Let `a(n)` be the numerator of `Σ_{k≤n} 1/k²` ([A007406](https://oeis.org/A007406)). A. Eldar and T. Ordowski (2019) conjectured that `gcd(n, a(n−1)) = A089026(n)` for `n > 3`: that is, `n` for primes and `1` for composites. It is listed as `research open` in formal-conjectures (`FormalConjectures/OEIS/7406.lean`). We prove a leading-digit criterion (not new in substance; the order-2 analogue of the classical argument for harmonic numbers), formalize Wolstenholme's theorem, and derive the conjecture on explicit infinite families.

## Status

**Partial result. The full conjecture remains open.** Proved: every `n > 3` that is prime, 3-smooth, of the form `2q^k`, or `c·q^k` with `c ≥ 2` 3-smooth and prime `q > c`, `q ∤ a(c−1)`. Open: e.g. `n = q^k` (k ≥ 2) and general `pq`.

## Theorems and Lean names

| Lean name | Statement |
|---|---|
| `padicValRat_H`, `not_dvd_a` | leading-digit lemma: `q ∤ a(U) ⇒ v_q(H_m) = −2⌊log_q m⌋` |
| `conjecture_of_leading_digits` | general sufficient criterion for composite `n` |
| `coprime_six_a` | `gcd(6, a m) = 1` |
| `conjecture_smooth` | `n = 2^i 3^j` |
| `conjecture_smooth_mul_prime`, `conjecture_smooth_mul_prime_pow` | `n = c q`, `n = c q^k` |
| `conjecture_two/three/four_mul_prime`, `conjecture_two_mul_prime_pow` | `2q`, `3q` (q≥7), `4q` (q≥5, q≠7), `2q^k` |
| `conjecture_smooth_mul_large_prime` | `c q` for all large primes `q` |
| `prime_dvd_a`, `conjecture_prime` | Wolstenholme: `p ∣ a(p−1)`, prime case |
| `conjecture_on_families` | combined: prime, 3-smooth, or `2q^k` |

No `sorry`, no `native_decide`, no extra hypotheses.

## Build

Toolchain `leanprover/lean4:v4.35.0-rc4`; Mathlib `v4.35.0-rc4` (commit `1f414401f69059aa7eead47b53ee40bd38455eeb`, pinned in `lake-manifest.json`).

```bash
cd Wolst
lake exe cache get
lake build
lake env lean Axioms.lean
```

## Axioms output

```
'Wolst.padicValRat_H' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.not_dvd_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.coprime_six_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_smooth' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_smooth_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_two_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_three_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_four_mul_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_smooth_mul_large_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_of_leading_digits' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.prime_dvd_a' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_prime' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_smooth_mul_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_two_mul_prime_pow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Wolst.conjecture_on_families' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Machine-check attestation

- [`verification/`](verification/) holds `build-log.txt` (fresh-clone build), `axioms.txt`, and [`VERIFICATION.md`](verification/VERIFICATION.md) with the commit SHA, toolchain, Mathlib commit, reproduce commands, the no-sorry grep result and SHA-256 hashes of the Lean sources.
- [CI](https://github.com/het4rk/eldar-ordowski-a007406/actions/workflows/lean.yml) does a clean build on every push, fails on any `sorry`, and checks an axiom whitelist (`scripts/check_axioms.sh`). It uploads the build log and axiom report as the `lean-attestation` artifact and shows them in the job summary.

## Paper

[`paper/paper.tex`](paper/paper.tex) and [`paper/paper.pdf`](paper/paper.pdf).

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

## Citation

See [`CITATION.cff`](CITATION.cff):

> Hetark Shah (AI-assisted by Grok), *Partial results on the Eldar–Ordowski gcd conjecture (OEIS A007406)*, 2026. https://github.com/het4rk/eldar-ordowski-a007406

## License

Apache-2.0 (the same as Mathlib). See [`LICENSE`](LICENSE).
