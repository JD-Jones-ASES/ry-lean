# Authorship and automation

JD Jones directed this project, chose its objective, and is its human author and
responsible maintainer. He is not a party to the mathematics: the theorem is Younis's, the
residue sets were found by computer search, and the Lean development was written by AI
agents under his direction. No independent human mathematical review is recorded.

## What the AI did

Anthropic's Claude models did the work, run through Claude Code:

* Claude Fable 5.1 planned the formalization (the truncated periodic counting, the digit
  congruence argument, the module layout, the statements in `Challenge.lean`), reviewed the
  subagents' output, and wrote the documentation.
* Claude Opus subagents, several in parallel, reviewed the statements against the source
  paper, ran the literature and formalization searches recorded in `README.md`, wrote the
  Lean proofs module by module, and audited the result (statement fidelity, axioms,
  documentation).
* Claude Opus subagents also found the residue sets: an exact search over square-free moduli
  for a maximum square-difference-free set and a largest compatible second set (a CP-SAT
  solver was used as a search tool; the resulting sets are verified in Lean by `decide` and
  in `scripts/check_chain.py` by direct enumeration, so the solver is not in the trust chain).

The Lean kernel checked every proof; `Test/Axioms.lean` audits axioms; no `native_decide`,
custom axiom, or `sorry` occurs in the library or in `Solution.lean`. Prompt, token, and
monetary accounting was not retained.

## Sources and credit

The construction and the theorem are Khalid Younis's (arXiv:1908.06058). The digit method
descends from Ruzsa; the search pattern for square-difference-free residue sets follows
Lewko and Beigel–Gasarch. All are cited in `PROOF.md` and `formalization.yaml`. The
contribution of this repository is the formal proof of the two-set form of Younis's theorem,
new data at modulus `145`, and the exact comparison of the two exponents.

## Limits

* The theorems are lower bounds; nothing is claimed about upper bounds or optimality.
* The optimality of the residue sets at `m = 145` (maximum `R₁`, largest compatible `R₂`)
  is a search result and not a theorem here.
* The prior-art statements in `README.md` record what was searched on the stated date; they
  are not a guarantee that nothing else exists.
* Registration at a formalization registry certifies statement matching and kernel replay
  at one commit; it does not certify novelty or significance.
