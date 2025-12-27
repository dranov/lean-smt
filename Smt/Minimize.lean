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
  -- Create n bound variables for the existential quantification
  let mut existVars : Array Term := #[]
  for i in [:n] do
    existVars := existVars.push (← tm.mkVar s s!"_card_{i}")

  -- Create bound variable x for the universal quantification
  let x ← tm.mkVar s "_card_x"

  -- Build disjunction: (x = c₁) ∨ (x = c₂) ∨ ... ∨ (x = cₙ)
  let mut eqs : Array Term := #[]
  for c in existVars do
    eqs := eqs.push (← tm.mkTerm .EQUAL #[x, c])

  let disj ← if eqs.size == 1 then
    pure eqs[0]!
  else
    tm.mkTerm .OR eqs

  -- Build ∀x. disj
  let forallVarList ← tm.mkTerm .VARIABLE_LIST #[x]
  let forallBody ← tm.mkTerm .FORALL #[forallVarList, disj]

  -- Build ∃c₁, ..., cₙ. (∀x. disj)
  let existsVarList ← tm.mkTerm .VARIABLE_LIST existVars
  tm.mkTerm .EXISTS #[existsVarList, forallBody]

/-- Minimize sort cardinalities by iteratively finding the smallest cardinality for each sort.
    Takes an optional timeout in milliseconds for the overall minimization budget.
    Returns `true` if minimization succeeded (or there was nothing to minimize),
    `false` if minimization failed/timed out and the caller should use the original model. -/
def minimizeSorts (slv : Solver) (tm : TermManager)
    (uss : Array cvc5.Sort) (timeoutMs : Option Nat := none) : Env Bool := do
  let startTime ← IO.monoMsNow
  for s in uss do
    -- Only minimize uninterpreted sorts
    if !s.isUninterpretedSort then
      continue

    let mut n := 1
    let mut found := false
    while !found do
      -- Check overall timeout budget
      if let some budget := timeoutMs then
        let elapsed := (← IO.monoMsNow) - startTime
        if elapsed > budget then
          return false

      let constraint ← mkSortCardinalityConstraint tm s n
      let result ← slv.checkSatAssuming #[constraint]

      if result.isSat then
        -- Found minimal cardinality, permanently add constraint
        slv.assertFormula constraint
        found := true
      else if result.isUnknown then
        -- Timeout or unknown during minimization, give up
        return false
      else
        -- UNSAT: need larger cardinality
        n := n + 1
        -- Safety bound to prevent infinite loop
        if n > 100 then
          return false

  return true

end Smt.Minimize
