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
-- `import all` and not a plain `import`: delegation typechecks by `Typed.Term α` being
-- definitionally `Untyped.Term`, which a plain import keeps opaque

public import Cvc.Proto2.Untyped.Term.Bool
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Bool



/-! # Generated Boolean and sort-generic constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Bool

/-- A symbol of the sort `α` describes, naming `α` explicitly. -/
def mkSymbolAs (α : Type) [ToTyp α] (name : String) : Env (Term α) := mkSymbol name



/-! ## Values -/

@[inherit_doc T.isBoolValue]
def isBoolValue (term : Term Bool) : Bool := T.isBoolValue term
@[inherit_doc T.getBoolValue]
def getBoolValue (term : Term Bool) : Res Bool := T.getBoolValue term
@[inherit_doc T.getBoolValue?]
def getBoolValue? (term : Term Bool) : Option Bool := T.getBoolValue? term

instance : SrtLike Bool where
  valueToTerm := mkBool
  termToValue t := getBoolValue t
