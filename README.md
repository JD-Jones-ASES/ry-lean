# ry-lean

A Lean 4 proof of Younis's lower-bound construction for sets of integers with no
configuration `{x, x + y, x + y²}`, and a new exponent.

**The problem.** Call `A ⊆ ℤ` *configuration-free* if there are no integers `x` and `y ≠ 0`
with `x`, `x + y`, `x + y²` all in `A`. This is the model case of the polynomial Szemerédi
theorem: configuration-free subsets of `{1, …, N}` have size `o(N)` (Bergelson–Leibman), in
fact at most `N (log N)^(−c)` (Peluse–Prendiville). How large can they be? Younis (2019)
constructed configuration-free subsets of `{1, …, N}` of size `N^(0.7685… − ε)`.

**What is proved.**

* **Younis's theorem, two-set form** (`younis_period_two`). Let `m ≥ 2` be square-free and
  let `R₁, R₂ ⊆ ℤ/m` be nonempty, with `R₁` square-difference-free and with no nonzero
  difference of `R₂` equal to the square of a difference of `R₁`. Then for every
  `ρ < 1/2 + log|R₁|/(3 log m) + log|R₂|/(6 log m)` there is `C > 0` such that every
  `{1, …, N}` contains a configuration-free set of size at least `C · N^ρ`.
* **The exponent `0.770287…`** (`record_pointwise`, `record_liminf`). At `m = 145 = 5 · 29`
  the residue sets

      R₁ = {0, 48, 55, 62, 69, 76, 117, 124, 131, 138}
      R₂ = {3, 12, 13, 16, 21, 24, 25, 34, 35, 38, 43, 46, 47, 56, 57, 60, 68, 69, 78, 79,
            82, 91, 100, 104, 113, 122, 123, 125, 126, 135, 136, 144}

  satisfy the hypotheses, so `liminf log D(N) / log N ≥ γ = 1/2 + log 3200 / (6 log 145) =
  0.770287…`, where `D(N)` is the largest size of a configuration-free subset of `{1, …, N}`.
* **The comparison** (`younis_lt_record`, `record_exponent_bounds`). Younis's exponent is
  `γ₀ = 1/2 + log 833 / (6 log 65) = 0.768503…` (his data: `m = 65`, `|R₁| = 7`, `|R₂| = 17`).
  Then `γ₀ < γ` and `0.7702 < γ < 0.77029`, each proved by exact comparisons of integer powers.

All five statements are unconditional theorems in Lean, checked by the kernel with no axioms
beyond `propext`, `Classical.choice`, `Quot.sound`. The mathematics is in [PROOF.md](PROOF.md).

## Files

* [Challenge.lean](Challenge.lean) — the five statements, using only Mathlib, with `sorry`
  placeholders; the surface a reader should audit.
* [Solution.lean](Solution.lean) — the same five statements, proved from the library `RY`.
* `RY/` — the development: digits and the digit congruence, the digit-set construction and
  its cardinality, the avoidance argument, the position-type rule with its periodic
  truncation and block counts, the passage to all `N` and to the liminf, the integer power
  comparisons, the finite checks at `m = 145`, and the assembly.
* [Test/Axioms.lean](Test/Axioms.lean) — the axiom audit over every declaration of `RY` and
  `NonlinearRoth`.
* [scripts/check_chain.py](scripts/check_chain.py) — a standalone Python check (standard
  library only) of the finite data and of the integer power comparisons.
* [PROOF.md](PROOF.md) — statements and proofs in ordinary mathematics.
* [VERIFICATION.md](VERIFICATION.md) — the checks performed at this snapshot and how to
  repeat them. [DISCLOSURE.md](DISCLOSURE.md) — authorship and the use of AI.
* [formalization.yaml](formalization.yaml), [comparator.json](comparator.json) — registry
  metadata and the statement-comparison configuration.

## Verify

Install [Elan](https://github.com/leanprover/elan); the toolchain is `leanprover/lean4:v4.33.0`
and Mathlib is pinned in `lake-manifest.json`. Then:

```sh
lake exe cache get
lake build
```

`lake build` compiles the library, `Challenge`, `Solution`, and `Test` (the axiom audit,
which fails the build on any unexpected axiom). `python3 scripts/check-source.py` rejects
`sorry`, `axiom`, `native_decide` and similar tokens in `RY/` and `Solution.lean`. The
standalone data check is

```sh
python3 scripts/check_chain.py
```

On Linux, `scripts/verify-comparator.sh` runs the registry's own statement comparison
(Comparator) and independent kernel replay (NanoDa) at their pinned revisions.

## Prior art

As of 2026-09-11, no search found any published or posted improvement of Younis's exponent
`0.768503…`, any other lower-bound construction in the integers for sets avoiding
`{x, x + y, x + y²}`, or any formalization of Younis's Theorem 1.1 or 1.5 in any proof
assistant. Venues searched: arXiv (abstracts, listings, ar5iv, and the API), the Semantic
Scholar and OpenAlex citation graphs of arXiv:1908.06058, Crossref, the Palomar registry
(every entry enumerated through its browse API), Google DeepMind's `formal-conjectures`
repository, Mathlib's source and its 100- and 1000-theorem lists, the Isabelle Archive of
Formal Proofs, the Coq/Rocq opam archives, the Lean Zulip archive, GitHub code search, and
the web (including Green's list of open problems, Tao's blog, and MathOverflow). Nearby but
non-overlapping: Roth's theorem for three-term arithmetic progressions is formalized in
Mathlib and in Isabelle/HOL (the linear configuration `{x, x + y, x + 2y}`, upper-bound
side); Szemerédi's theorem via density Hales–Jewett is registered at Palomar; a registry
entry on the Furstenberg–Sárközy lower bound (square-difference-free sets, the two-point
condition) formalizes a digit construction in Ruzsa's lineage but does not treat the
three-point configuration or Younis's theorem. The best Furstenberg–Sárközy exponent
published, Krachun's `0.7527…` (2026), transfers to this problem — every
square-difference-free set is configuration-free — and lies below both exponents compared
here. Lewko (2026) gives a `|F|^(2/3)` construction for this configuration in certain finite
fields, which does not transfer to the integers.

## Authorship

JD Jones is the human author and responsible maintainer. The theorem and construction are
Khalid Younis's; the residue sets were found by computer search; Anthropic's Claude models
wrote the Lean development and this documentation under JD Jones's direction — see
[DISCLOSURE.md](DISCLOSURE.md). No independent human expert review is recorded.

License: [MIT](LICENSE).
