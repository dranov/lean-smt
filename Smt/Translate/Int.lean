/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Int

open Lean Expr
open Translator Term
open Smt (constPattern)

private def mkInt : Lean.Expr :=
  .const ``Int []

/-- Patterns for translateType: matches `Int`. -/
def translateTypePatterns : Array Expr := #[mkConst ``Int]

@[smt_translate translateTypePatterns] def translateType : Translator := fun e => match e with
  | .const ``Int _ => return symbolT "Int"
  | _              => return none

/-- Patterns for translateInt: matches Int literals and arithmetic operations. -/
def translateIntPatterns : Array Expr := #[
  constPattern ``OfNat.ofNat 3 1,   -- nat literals (1 universe param)
  constPattern ``Neg.neg 3 1,       -- negation (1 universe param)
  constPattern ``HAdd.hAdd 6 3,     -- addition (3 universe params)
  constPattern ``HSub.hSub 6 3,     -- subtraction (3 universe params)
  constPattern ``HMul.hMul 6 3,     -- multiplication (3 universe params)
  constPattern ``HDiv.hDiv 6 3,     -- division (3 universe params)
  constPattern ``HMod.hMod 6 3      -- modulo (3 universe params)
]

@[smt_translate translateIntPatterns] def translateInt : Translator := fun e => do
  if let some n := e.natLitOf? mkInt then
    return literalT (toString n)
  else if let some x := e.negOf? mkInt then
    return appT (symbolT "-") (← applyTranslators! x)
  else if let some (x, y) := e.hAddOf? mkInt mkInt then
    return mkApp2 (symbolT "+") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hSubOf? mkInt mkInt then
    return mkApp2 (symbolT "-") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hMulOf? mkInt mkInt then
    return mkApp2 (symbolT "*") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hDivOf? mkInt mkInt then
    return mkApp2 (symbolT "div") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.hModOf? mkInt mkInt then
    return mkApp2 (symbolT "mod") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

/-- Patterns for translateProp: matches comparison operators on Int. -/
def translatePropPatterns : Array Expr := #[
  constPattern ``LT.lt 4 1,   -- @LT.lt α inst x y (1 universe param)
  constPattern ``LE.le 4 1,   -- @LE.le α inst x y (1 universe param)
  constPattern ``GE.ge 4 1,   -- @GE.ge α inst x y (1 universe param)
  constPattern ``GT.gt 4 1    -- @GT.gt α inst x y (1 universe param)
]

@[smt_translate translatePropPatterns] def translateProp : Translator := fun e => do
  if let some (x, y) := e.ltOf? mkInt then
    return mkApp2 (symbolT "<") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.leOf? mkInt then
    return mkApp2 (symbolT "<=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.geOf? mkInt then
    return mkApp2 (symbolT ">=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (x, y) := e.gtOf? mkInt then
    return mkApp2 (symbolT ">") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

end Smt.Translate.Int
