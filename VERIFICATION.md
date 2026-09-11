# Verification

What was checked at this snapshot, and how to repeat it.

## Toolchain

* Lean `leanprover/lean4:v4.33.0` (`lean-toolchain`).
* Mathlib pinned in `lake-manifest.json` at `db584cd6d46c92f209a44c0f1c829460d327499d`
  (tag `v4.33.0`), with its own dependencies at the revisions the manifest records.
* No `lake update` is ever run; dependency changes would be deliberate, reviewed commits.

## Build

```sh
lake exe cache get
lake build
```

`lake build` compiles the four default targets: the library `RY`, `Challenge`, `Solution`,
and `Test`. Expected outcome: `Challenge.lean` reports five `declaration uses sorry`
warnings (its placeholders, by design); nothing else warns or errors.

At this snapshot `lake build` completed successfully (8,722 jobs; about two minutes with the
Mathlib cache in place, most of it the eight modules of `RY` at 13–16 s each). The only
warnings were the five intentional placeholders of `Challenge.lean`. `RY/` and `Solution.lean`
contain no `sorry`.

## Axioms

`Test/Axioms.lean` walks every constant whose name begins with `RY.`, `_private.RY.`, or
`NonlinearRoth.` and collects the axioms it depends on; the build fails if any axiom outside
`propext`, `Classical.choice`, `Quot.sound` appears.

At this snapshot the audit reported:

```
Audited 280 project constants; unexpected axiom dependencies: 0.
```

The finite checks at `m = 145` use ordinary `decide`; the one comparison `norm_num` does not
finish (`3200 ^ 230 < 145 ^ 373`) uses `decide +kernel`, which is a kernel evaluation and
does not introduce `Lean.ofReduceBool`. No `native_decide` anywhere.

## Source guard

```sh
python3 scripts/check-source.py
```

rejects `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`, and
`Lean.ofReduceBool` outside comments and strings in `RY/*.lean` and `Solution.lean`.
`Challenge.lean` is excluded: its placeholders are intentional.

## Statement identity

`Challenge.lean` and `Solution.lean` declare the same five theorem names in the namespace
`NonlinearRoth`, with the same statements, over the same five definitions (`ConfigFree`,
`exponent`, `younisExponent`, `recordExponent`, `D`). The definitions in `RY/Defs.lean` are
byte-for-byte those of the Challenge. Checked by printing each definition and the type of
each theorem with `pp.explicit` from `import Challenge` and from `import Solution`, and
comparing the outputs: identical. `Solution.lean` does not import `Challenge.lean`.

## Data

```sh
python3 scripts/check_chain.py
```

A standalone script (Python ≥ 3.9, standard library only) that re-derives from the
definitions: square-freeness of `145` and `65`; that the residue sets are distinct residues
in range; the hypotheses (H1) and (H2) for the sets at `145` and for Younis's sets at `65`;
the derived edges `R₂ → R₁` and `R₁ → R₁`; the exponents to thirty decimal places; the four
integer power comparisons behind the exponent inequalities; the block counts of the
truncated rule for depths `0` to `3` and the admissibility of every position pair; a direct
enumeration showing the three-digit set at `145` is configuration-free; and controls that
must fail (a corrupted `R₂`; a non-square-free modulus). It reports `51 checks, 0 failed`
and exits `0`.

## Registry checks

On Linux, `scripts/verify-comparator.sh` clones Comparator, lean4export, NanoDa and Landrun
at the revisions pinned in the script, builds them, runs `lake build` and `Test.Axioms`, and
then runs Comparator on `comparator.json`: it compares the five theorems and five
definitions between `Challenge` and `Solution`, checks the permitted axioms, and replays the
proof terms in NanoDa's independent kernel. The registry performs the same checks itself at
the submitted commit; this repository carries no continuous-integration configuration.

## Not checked here

* The optimality of the residue sets at `m = 145` (maximum `R₁`; largest compatible `R₂`)
  is a search result, not a theorem, and is not verified in Lean.
* The prior-art statements in `README.md` record searches on a date; they are not
  mechanically verifiable.
