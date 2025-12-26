/-
Copyright (c) 2021-2022 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Abdalrhman Mohamed
-/

import Lean

namespace Smt.Attribute

open Lean Elab

/-- An extension to Lean's runtime environment to support SMT attributes.
    Maintains a set of function declarations for the `smt` tactic to utilize
    while generating the SMT query. -/
abbrev SmtExtension := SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name (Std.HashSet Name))

/-- Adds a declaration to the set of function declarations maintained by the SMT
    environment extension. -/
def addSmtEntry (d : Std.HashMap Name (Std.HashSet Name)) (e : (Name × Name)) :=
  d.insert e.fst ((d.getD e.fst {}).insert e.snd)

initialize smtExt : SmtExtension ← registerSimpleScopedEnvExtension {
  name     := `SmtExt
  initial  := {}
  addEntry := addSmtEntry
}

/-- Extension that maps translator declaration names to their pattern declaration names.
    Translators without patterns are treated as "catch-all" translators. -/
abbrev TranslatorPatternsExtension := SimpleScopedEnvExtension (Name × Name) (Std.HashMap Name Name)

initialize translatorPatternsExt : TranslatorPatternsExtension ← registerSimpleScopedEnvExtension {
  name     := `TranslatorPatternsExt
  initial  := {}
  addEntry := fun m (translatorName, patternsName) => m.insert translatorName patternsName
}

/-- Throws unexpected type error. -/
def throwUnexpectedType (t : Name) (n : Name) : AttrM Unit :=
  throwError s!"unexpected type at '{n}', `{t}` expected"

/-- Validates the tagged declaration. -/
def validate (n : Name) (t : Name) : AttrM Unit := do
  match (← getEnv).find? n with
  | none      => throwError s!"unknown constant '{n}'"
  | some info =>
    match info.type with
    | Expr.const c .. => if c != t then throwUnexpectedType t n
    | _               => throwUnexpectedType t n

/-- Registers an SMT attribute with the provided name and description and links
    it against `ext`. -/
def registerSmtAttr (attrName : Name) (typeName : Name) (attrDescr : String)
  : IO Unit :=
  registerBuiltinAttribute {
    name  := attrName
    descr := attrDescr
    applicationTime := AttributeApplicationTime.afterTypeChecking
    add   := fun decl stx attrKind => do
      trace[smt.attr] s!"attrName: {attrName}, attrDescr: {attrDescr}"
      trace[smt.attr] s!"decl: {decl}, stx: {stx}, attrKind: {attrKind}"
      Attribute.Builtin.ensureNoArgs stx
      validate decl typeName
      setEnv (smtExt.addEntry (← getEnv) (typeName, decl))
    erase := fun declName => do
      let s := smtExt.getState (← getEnv)
      let s := s.erase declName
      modifyEnv fun env => smtExt.modifyState env fun _ => s
  }

/-- Validates that a patterns declaration has the correct type. -/
def validatePatterns (n : Name) : AttrM Unit := do
  match (← getEnv).find? n with
  | none => throwError s!"unknown constant '{n}'"
  | some info =>
    -- Check that patterns is of type `Array Expr`
    let expectedType := Expr.app (.const ``Array [.zero]) (.const ``Expr [])
    unless ← Meta.MetaM.run' (Meta.isDefEq info.type expectedType) do
      throwError s!"patterns declaration '{n}' should have type `Array Expr`, got `{info.type}`"

/-- Registers the smt_translate attribute with optional patterns support.
    Usage: @[smt_translate] or @[smt_translate myPatterns] -/
initialize registerBuiltinAttribute {
  name  := `smt_translate
  descr := "Utilize this function to translate Lean expressions to SMT terms."
  applicationTime := AttributeApplicationTime.afterTypeChecking
  add   := fun decl stx attrKind => do
    trace[smt.attr] s!"attrName: smt_translate"
    trace[smt.attr] s!"decl: {decl}, stx: {stx}, attrKind: {attrKind}"
    validate decl `Smt.Translator
    setEnv (smtExt.addEntry (← getEnv) (`Smt.Translator, decl))
    -- Parse optional patterns argument
    let args := stx[1].getArgs
    if h : args.size > 0 then
      let patternsIdent := args[0]
      let patternsName ← resolveGlobalConstNoOverload patternsIdent
      validatePatterns patternsName
      setEnv (translatorPatternsExt.addEntry (← getEnv) (decl, patternsName))
      trace[smt.attr] s!"registered patterns {patternsName} for translator {decl}"
  erase := fun declName => do
    let s := smtExt.getState (← getEnv)
    let s := s.erase declName
    modifyEnv fun env => smtExt.modifyState env fun _ => s
}

initialize registerSmtAttr `smt_sort_reconstruct `Smt.SortReconstructor
             "Utilize this function to translate cvc5 sorts to Lean expressions."

initialize registerSmtAttr `smt_term_reconstruct `Smt.TermReconstructor
             "Utilize this function to translate cvc5 terms to Lean expressions."

initialize registerSmtAttr `smt_proof_reconstruct `Smt.ProofReconstructor
             "Utilize this function to translate cvc5 proofs to Lean expressions."

end Smt.Attribute
