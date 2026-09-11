import Solution
import Lean.Util.CollectAxioms

/-!
# Axiom audit

Walks every constant in the environment whose name begins with `NonlinearRoth.` (every
declaration of this development), `RY.` or `_private.RY.` (private auxiliaries of the `RY.*`
modules), or `_private.Solution.`, and collects the axioms each depends on. Anything outside
`propext`, `Classical.choice`, `Quot.sound` is reported with `logError`, which fails `lake build`.
The audit also fails if it matched fewer than 250 constants (a floor below the 271 constants at the time
of writing, so a renamed namespace cannot make it pass vacuously) or if any of the five compared
theorems is missing from the environment. `Challenge.lean` is not imported, so its intentional
`sorry` placeholders are out of scope.
-/

open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let mut checked : Nat := 0
  let mut rejected : Nat := 0
  let allowed : Array Name := #[`propext, `Classical.choice, `Quot.sound]
  for (name, _) in env.constants.toList do
    let label := name.toString
    if label.startsWith "RY." || label.startsWith "_private.RY." ||
        label.startsWith "_private.Solution." || label.startsWith "NonlinearRoth." then
      checked := checked + 1
      let axs ← collectAxioms name
      for ax in axs do
        unless allowed.contains ax do
          rejected := rejected + 1
          logError m!"Unexpected axiom dependency: {name} -> {ax}"
  unless checked ≥ 250 do
    logError m!"Axiom audit matched only {checked} project constants; expected at least 250"
  for n in [`NonlinearRoth.younis_period_two, `NonlinearRoth.record_pointwise,
      `NonlinearRoth.record_liminf, `NonlinearRoth.younis_lt_record,
      `NonlinearRoth.record_exponent_bounds] do
    unless env.contains n do
      logError m!"Compared theorem is missing from the environment: {n}"
  logInfo m!"Audited {checked} project constants; unexpected axiom dependencies: {rejected}."
