# Verification

What was checked at this snapshot, and how to repeat it. The statements under check are the five
theorems of `Challenge.lean`; everything else exists to prove them unchanged.

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

At this snapshot `lake build` completed successfully; the only warnings were the five
intentional placeholders of `Challenge.lean`, and `RY/` and `Solution.lean` contain no `sorry`.
(Wall-clock time depends on the machine and on the state of the Mathlib cache: from two minutes
to several with the cache in place.) A from-scratch build in a fresh checkout reproduced the same
five warnings and the same audit line.

## Axioms

`Test/Axioms.lean` walks every constant whose name begins with `RY.`, `_private.RY.`, or
`NonlinearRoth.` and collects the axioms it depends on; the build fails if any axiom outside
`propext`, `Classical.choice`, `Quot.sound` appears. The audit also fails if it matches fewer than
250 constants (so a rename cannot make it pass vacuously) or if any of the five compared
theorems is missing from the environment. Mutation controls run at this snapshot: corrupting one
residue of either set makes the corresponding `decide` report the proposition false; replacing
`145` by `125` in the square-freeness claim leaves an unprovable goal; a `sorry` injected into
`RY/Rule.lean` compiles silently through `Solution.lean` and is caught by this audit (eleven
constants reported) and by the source guard.

At this snapshot the audit reported (reproduce with `lake build Test`; the line is logged by
`Test/Axioms.lean`):

```
Audited 271 project constants; unexpected axiom dependencies: 0.
```

The finite checks at `m = 145` use ordinary `decide`, under `set_option maxRecDepth 100000` and
`maxHeartbeats 2000000` (`RY/Instance.lean`); these raise elaboration limits only and do not affect
the kernel check. They are the only non-default options in the development. The one comparison
`norm_num` does not finish (`3200 ^ 230 < 145 ^ 373`) uses `decide +kernel`, which is a kernel
evaluation and does not introduce `Lean.ofReduceBool`. No `native_decide` anywhere.

## Source guard

```sh
python3 scripts/check-source.py
```

rejects `sorry`, `admit`, `axiom`, `unsafe`, `partial`, `native_decide`, `implemented_by`,
`extern`, `Lean.ofReduceBool` and the kernel-bypass options `debug.skipKernelTC` and
`debug.byAsSorry` outside comments and strings in `RY/*.lean`, `RY.lean`, `Solution.lean`,
`Test.lean` and `Test/*.lean`. `Challenge.lean` is checked only for the two kernel-bypass
options: its placeholders are intentional.

## Statement identity

`Challenge.lean` and `Solution.lean` declare the same five theorem names in the namespace
`NonlinearRoth`, with the same statements, over the same five definitions (`ConfigFree`,
`exponent`, `younisExponent`, `recordExponent`, `D`). The five `def` commands in `RY/Defs.lean` are character-for-character
those of the Challenge (the doc-comment on `D` is shorter; the definitions themselves are
identical). Checked by printing each definition and the type of each theorem with `pp.explicit`
from `import Challenge` and from `import Solution`, and comparing the outputs: identical.
`Solution.lean` does not import `Challenge.lean`. To repeat: run `lake env lean` on a scratch
file containing `import Challenge` (resp. `import Solution`), `set_option pp.explicit true`, and
`#print` of the five definitions and `#check @` of the five theorems, and diff the two outputs;
`scripts/verify-comparator.sh` performs the same comparison mechanically.

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
enumeration showing the three-digit set at `145` (position types `1, 0, 1`, so `R₁` and all
residues; 14,500 elements) is configuration-free — this depth reaches no type-`2` position, so
`R₂` enters only through the (H2) check; and controls that must fail (a corrupted `R₂`; a
non-square-free modulus). It reports `51 checks, 0 failed` and exits `0`.

## Registry checks

On Linux, `scripts/verify-comparator.sh` clones Comparator, lean4export, NanoDa and Landrun
at the revisions pinned in the script (Landrun is invoked through `scripts/landrun-wrapper.py`,
which preserves Comparator's command delimiter; `scripts/test-landrun-wrapper.py` is its test),
builds them, runs `lake build` and `Test.Axioms`, and
then runs Comparator on `comparator.json`: it compares the five theorems and five
definitions between `Challenge` and `Solution`, checks the permitted axioms, and replays the
proof terms in NanoDa's independent kernel. The registry performs the same checks itself at
the submitted commit; this repository carries no continuous-integration configuration.

## Not checked here

* The optimality of the residue sets at `m = 145` (maximum `R₁`; largest compatible `R₂`)
  is a search result, not a theorem, and is not verified in Lean.
* The prior-art statements in `README.md` record searches on a date; they are not
  mechanically verifiable.
