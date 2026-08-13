/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Env
import all Cvc.Proto2.Untyped.Term.Defs
import all Cvc.Proto2.Typed.Term.Defs

public import Cvc.Proto2.Untyped.Term.String
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.String



/-! # Generated String constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.String



/-! ## Values -/

@[inherit_doc T.isStringValue]
def isStringValue (term : Term String) : Bool := T.isStringValue term
@[inherit_doc T.getStringValue]
def getStringValue (term : Term String) : Res String := T.getStringValue term
@[inherit_doc T.getStringValue?]
def getStringValue? (term : Term String) : Option String := T.getStringValue? term

instance : SrtLike String where
  valueToTerm s := mkString s false
  termToValue t := getStringValue t
