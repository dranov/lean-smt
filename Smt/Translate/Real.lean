/-
Copyright (c) 2021-2023 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Smt.Recognizers
import Mathlib.Data.Real.Archimedean

import Smt.Translate

namespace Smt.Translate.Rat

open Lean Expr
open Translator Term
open Smt (constPattern)

private def mkReal : Lean.Expr :=
  .const ``Real []

/-- Patterns for translateType: matches `Real`. -/
def translateTypePatterns : Array Expr := #[mkConst ``Real]

@[smt_translate translateTypePatterns] def translateType : Translator := fun e => match e with
  | .const ``Real _  => return symbolT "Real"
  | _                => return none

/-- Patterns for translateInt: matches `Int.floor` on Real. -/
def translateIntPatterns : Array Expr := #[constPattern ``Int.floor 3 1]  -- 1 universe param

@[smt_translate translateIntPatterns] def translateInt : Translator := fun e => do
  if let some x := e.intFloorOf? mkReal then
    return appT (symbolT "to_int") (← applyTranslators! x)
  else
    return none

/-- Patterns for translateReal: matches Real literals and arithmetic operations. -/
def translateRealPatterns : Array Expr := #[
  constPattern ``OfNat.ofNat 3 1,   -- nat literals (1 universe param)
  constPattern ``Int.cast 3 1,      -- int cast (1 universe param)
  constPattern ``Neg.neg 3 1,       -- negation (1 universe param)
  constPattern ``abs 3 1,           -- absolute value (1 universe param)
  constPattern ``HAdd.hAdd 6 3,     -- (3 universe params)
  constPattern ``HSub.hSub 6 3,
  constPattern ``HMul.hMul 6 3,
  constPattern ``HDiv.hDiv 6 3
]

@[smt_translate translateRealPatterns] def translateReal : Translator := fun e => do
  if let some n := e.natLitOf? mkReal then
    return literalT s!"{n}.0"
  else if let some x := e.intCastOf? mkReal then
    return appT (symbolT "to_real") (← applyTranslators! x)
  else if let some x := e.negOf? mkReal then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some x := e.absOf? mkReal then
    return appT (symbolT "abs") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkReal mkReal then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkReal mkReal then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkReal mkReal then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkReal mkReal then
    return mkApp2 (symbolT "/") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

/-- Patterns for translateProp: matches comparison operators on Real. -/
def translatePropPatterns : Array Expr := #[
  constPattern ``LT.lt 4 1,
  constPattern ``LE.le 4 1,
  constPattern ``GE.ge 4 1,
  constPattern ``GT.gt 4 1
]

@[smt_translate translatePropPatterns] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkReal then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkReal then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkReal then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkReal then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Rat
