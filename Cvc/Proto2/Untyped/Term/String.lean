/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Env
import all Cvc.Proto2.Untyped.Term.Defs

public import Cvc.Proto2.Untyped.Term.Defs
public import Cvc.Proto2.Ext
public import Cvc.Proto2.Untyped.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.String



/-! # Generated String constructors, sort-erased -/
namespace Cvc.Proto2.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Proto2.Spec.String



/-! ## Values -/

@[inherit_doc T.isStringValue]
def isStringValue (term : Term) : Bool := T.isStringValue term.toUnsafe

/-- The string a term denotes, failing if it denotes none.

lean-cvc5 does not expose cvc5's string-value accessor, so this reads the term's own printed form,
which is the SMT-LIB string literal.
-/
def getStringValue (term : Term) : Res String :=
  if term.isStringValue then
    let s := toString term
    if s.startsWith '"' ∧ s.endsWith '"' then return s.drop 1 |>.dropEnd 1 |>.toString
    else throwUser s!"failed to retrieve string value of term `{s}`"
  else throwUser "cannot extract the string value of a term that denotes no string"

@[inherit_doc getStringValue]
def getStringValue? (term : Term) : Option String := term.getStringValue.toOption

instance : SrtLike String where
  valueToTerm s := mkString s false
  termToValue t := t.getStringValue
