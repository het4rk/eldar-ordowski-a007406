# Verification record

| Item | Value |
|---|---|
| Date | 2026-10-12 |
| Verified commit | `d0bb63d8d1078150488d0db7bd2235d76f4975a3` |
| Lean toolchain | `leanprover/lean4:v4.35.0-rc4` |
| Mathlib | `v4.35.0-rc4`, commit `1f414401f69059aa7eead47b53ee40bd38455eeb` |
| Build result | `Build completed successfully` (see [`build-log.txt`](build-log.txt)) |
| Axioms | 15 declarations, all `[propext, Classical.choice, Quot.sound]` (see [`axioms.txt`](axioms.txt)) |
| CI | [![Lean build](https://github.com/het4rk/eldar-ordowski-a007406/actions/workflows/lean.yml/badge.svg)](https://github.com/het4rk/eldar-ordowski-a007406/actions/workflows/lean.yml) |

## Reproduce

```bash
git clone https://github.com/het4rk/eldar-ordowski-a007406
cd eldar-ordowski-a007406
git checkout d0bb63d8d1078150488d0db7bd2235d76f4975a3
cd Wolst
lake exe cache get
lake build
lake env lean Axioms.lean
grep -rnw sorry Wolst --include=*.lean   # expect no output
```

## No-sorry check

`grep -rnw sorry Wolst/Wolst --include=*.lean` gave no matches (exit code 1), and the build log has no `declaration uses 'sorry'` warnings.

## SHA-256 of the Lean sources (at the verified commit)

```
b0259183446fcf23870cf7089885f48006c97284810d779a37847ed759477f46  ./Wolst/Axioms.lean
f1a8dbd56fd327b77603c7a42c7deaad17d5be890e5b3f72d20d9fd1a758d2a3  ./Wolst/Wolst.lean
6c7c48196a1edcaf1adca4172d725f8a5b2f1fa50ad7053b661579327d8127df  ./Wolst/Wolst/Basic.lean
f9ee183ca3109fb50801db7b59faf0b59ae9cb50d391dee49be1a744e8b691bc  ./Wolst/Wolst/Families.lean
292dabef8c45598dd4b8a9899755819ae5953975038655128e62b6b536b3d36f  ./Wolst/Wolst/Prime.lean
```

Commits after the verified one change only `verification/` (and the paper PDF). The Lean sources are unchanged, as the hashes above confirm.
