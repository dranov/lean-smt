/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Nat

open Lean Expr
open Translator Term
open Smt (constPattern)

private def mkNat : Lean.Expr :=
  .const ``Nat []

/-- Patterns for translateNat: matches Nat literals and arithmetic operations. -/
def translateNatPatterns : Array Expr := #[
  constPattern ``OfNat.ofNat 3 1,   -- nat literals (1 universe param)
  mkConst ``Nat.zero,
  constPattern ``Nat.succ 1 0,
  constPattern ``HAdd.hAdd 6 3,     -- (3 universe params)
  constPattern ``HSub.hSub 6 3,
  constPattern ``HMul.hMul 6 3,
  constPattern ``HDiv.hDiv 6 3,
  constPattern ``HMod.hMod 6 3
]

@[smt_translate translateNatPatterns] def translateNat : Translator := fun e => do
  if let some n := e.natLitOf? mkNat then
    return literalT (toString n)
  else if let .const ``Nat.zero _ := e then
    return literalT "0"
  else if let some n := e.app1? ``Nat.succ then
    return mkApp2 (symbolT "+") (← applyTranslators! n) (literalT "1")
  else if let some (m, n) := e.hAddOf? mkNat mkNat then
    return mkApp2 (symbolT "+") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.hSubOf? mkNat mkNat then
    modify fun st => { st with depConstants := st.depConstants.insert ``Nat.sub }
    return mkApp2 (symbolT "Nat.sub") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.hMulOf? mkNat mkNat then
    return mkApp2 (symbolT "*") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.hDivOf? mkNat mkNat then
    return mkApp2 (symbolT "div") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.hModOf? mkNat mkNat then
    return mkApp2 (symbolT "mod") (← applyTranslators! m) (← applyTranslators! n)
  else
    return none

/-- Patterns for translateProp: matches comparison operators on Nat. -/
def translatePropPatterns : Array Expr := #[
  constPattern ``LT.lt 4 1,
  constPattern ``LE.le 4 1,
  constPattern ``GE.ge 4 1,
  constPattern ``GT.gt 4 1
]

@[smt_translate translatePropPatterns] def translateProp : Translator := fun e => do
  if let some (m, n) := e.ltOf? mkNat then
    return mkApp2 (symbolT "<") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.leOf? mkNat then
    return mkApp2 (symbolT "<=") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.geOf? mkNat then
    return mkApp2 (symbolT ">=") (← applyTranslators! m) (← applyTranslators! n)
  else if let some (m, n) := e.gtOf? mkNat then
    return mkApp2 (symbolT ">") (← applyTranslators! m) (← applyTranslators! n)
  else
    return none

/- Translates quantified expressions over natural numbers for with versions that
   ensure the quantified variables are greater than or equal to 0. For
   example, given `∀ x : Nat, p(x)`, this method returns the expr
   `∀ x : Nat, x ≥ 0 → p(x)`. -/
@[smt_translate] def translateForalls : Translator
  | e@(forallE n t@(const ``Nat _) b bi) => do
    if e.isArrow then return none
    let tmB ← Meta.withLocalDecl n bi t (translateBody b)
    let tmGeqZero := Term.mkApp2 (symbolT ">=") (symbolT n.toString) (literalT "0")
    let tmProp := Term.mkApp2 (symbolT "=>") tmGeqZero tmB
    return forallT n.toString (symbolT "Int") tmProp
  | _ => return none
where
  translateBody (b : Expr) (x : Expr) : TranslationM Term := do
    modify fun s => { s with localFVars := s.localFVars.insert x.fvarId! }
    let tmB ← applyTranslators! (b.instantiate #[x])
    modify fun s => { s with localFVars := s.localFVars.erase x.fvarId! }
    return tmB

end Smt.Translate.Nat
