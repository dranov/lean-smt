/-
Copyright (c) 2021-2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Pîrlea
-/

import cvc5

namespace Smt.Minimize

open cvc5

/-- Create an SMT constraint that the given sort has cardinality *at most* `n`.
    `∃c₁, ..., cₙ. ∀x. (x = c₁) ∨ ... ∨ (x = cₙ)` -/
def mkSortCardinalityConstraint (tm : TermManager) (s : cvc5.Sort) (n : Nat) : Env Term := do
  let existVars ← (List.range n).toArray.mapM fun i => tm.mkVar s s!"_card_{i}"
  let x ← tm.mkVar s "_card_x"
  let eqs ← existVars.mapM fun c => tm.mkTerm .EQUAL #[x, c]
  let disj ← if eqs.size == 1 then pure eqs[0]! else tm.mkTerm .OR eqs
  let forallBody ← tm.mkTerm .FORALL #[← tm.mkTerm .VARIABLE_LIST #[x], disj]
  tm.mkTerm .EXISTS #[← tm.mkTerm .VARIABLE_LIST existVars, forallBody]

/-- Find the minimum cardinality for a single sort using exponential + binary search.
    Returns `none` if minimization failed, or `some n` if minimized to cardinality `n`.
    We use exponential search to find bounds first, which is efficient when the minimum
    cardinality is small (common case). -/
partial def minimizeSortCardinality (slv : Solver) (tm : TermManager) (s : cvc5.Sort)
    (checkTimeout : Env Bool) : Env (Option Nat) := do
  let checkCard (n : Nat) : Env (Option Bool) := do
    if ← checkTimeout then return none
    let constraint ← mkSortCardinalityConstraint tm s n
    let result ← slv.checkSatAssuming #[constraint]
    if result.isUnknown then return none
    return some result.isSat

  -- Exponential search: test 1, 2, 4, 8, ... until SAT.
  -- Returns (lo, hi) where lo = prev+1 (first untested) and hi = n (first SAT).
  let rec findBounds (prev n : Nat) : Env (Option (Nat × Nat)) := do
    if n > 100 then return none
    match ← checkCard n with
    | none => return none
    | some true => return some (prev + 1, n)
    | some false => findBounds n (n * 2)

  -- Binary search for minimum in [lo, hi] where hi is known to succeed
  let rec binarySearch (lo hi : Nat) : Env (Option Nat) := do
    if lo >= hi then return some lo
    let mid := (lo + hi) / 2
    match ← checkCard mid with
    | none => return none
    | some true => binarySearch lo mid
    | some false => binarySearch (mid + 1) hi

  match ← findBounds 0 1 with
  | none => return none
  | some (lo, hi) =>
    match ← binarySearch lo hi with
    | none => return none
    | some n =>
      -- We minimised the sort; keep the constraint for further sort
      -- minimisations (if any)
      slv.assertFormula (← mkSortCardinalityConstraint tm s n)
      return some n

/-- Minimize sort cardinalities by iteratively finding the smallest cardinality for each sort.
    Takes an optional timeout in milliseconds for the overall minimization budget.
    Returns `true` if minimization succeeded (or there was nothing to minimize),
    `false` if minimization failed/timed out and the caller should use the original model. -/
def minimizeSorts (slv : Solver) (tm : TermManager)
    (uss : Array cvc5.Sort) (timeoutMs : Option Nat := none) : Env Bool := do
  let startTime ← IO.monoMsNow
  let checkTimeout : Env Bool := do
    if let some budget := timeoutMs then
      return (← IO.monoMsNow) - startTime > budget
    return false
  let uninterpSorts := uss.filter (·.isUninterpretedSort)
  let mut cardinalities : Array (cvc5.Sort × Nat) := #[]
  for s in uninterpSorts do
    match ← minimizeSortCardinality slv tm s checkTimeout with
    | some n => cardinalities := cardinalities.push (s, n)
    | none => return false
  dbg_trace "Minimized sort cardinalities: {cardinalities}"
  return true

end Smt.Minimize
