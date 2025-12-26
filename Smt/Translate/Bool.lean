/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed, Wojciech Nawrocki
-/

import Smt.Recognizers
import Smt.Translate

namespace Smt.Translate.Bool

open Lean Expr
open Translator Term
open Smt (constPattern)

private def mkBool : Lean.Expr :=
  .const ``Bool []

/-- Patterns for translateType: matches `Bool`. -/
def translateTypePatterns : Array Expr := #[mkConst ``Bool]

@[smt_translate translateTypePatterns] def translateType : Translator := fun e => match e with
  | .const ``Bool _ => return symbolT "Bool"
  | _               => return none

/-- Patterns for translateBool: matches Bool literals and operations. -/
def translateBoolPatterns : Array Expr := #[
  mkConst ``true,
  mkConst ``false,
  constPattern ``not 1 0,
  constPattern ``and 2 0,
  constPattern ``or 2 0,
  constPattern ``xor 2 0,
  constPattern ``BEq.beq 4 1,  -- @BEq.beq α inst a b (1 universe param)
  constPattern ``bne 4 1       -- @bne α inst a b (1 universe param)
]

@[smt_translate translateBoolPatterns] def translateBool : Translator := fun e => do
  if let .const ``true _ := e then
    return symbolT "true"
  else if let .const ``false _ := e then
    return symbolT "false"
  else if let .some b := e.app1? ``not then
    return appT (symbolT "not") (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``and then
    return mkApp2 (symbolT "and") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``or then
    return mkApp2 (symbolT "or") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (a, b) := e.app2? ``xor then
    return mkApp2 (symbolT "xor") (← applyTranslators! a) (← applyTranslators! b)
  else if let some (_, x, y) := e.beq? then
    return mkApp2 (symbolT "=") (← applyTranslators! x) (← applyTranslators! y)
  else if let some (_, x, y) := e.bne? then
    return mkApp2 (symbolT "distinct") (← applyTranslators! x) (← applyTranslators! y)
  else
    return none

/-- Patterns for translateProp: matches `@Eq Bool _ _`. -/
def translatePropPatterns : Array Expr := #[constPattern ``Eq 3 1]  -- 1 universe param

@[smt_translate translatePropPatterns] def translateProp : Translator := fun e => do
  if let some (.const ``Bool _, a, b) := e.eq? then
    return mkApp2 (symbolT "=") (← applyTranslators! a) (← applyTranslators! b)
  else
    return none

end Smt.Translate.Bool
