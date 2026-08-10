/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Proto.Untyped.Term.Defs
import all Cvc.Proto.Typed.Term.Defs

public import Cvc.Proto.Types.Set
public import Cvc.Proto.Untyped.Term.Set
public import Cvc.Proto.Typed.Term.Defs
public import Cvc.Proto.Typed.Term.Value
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.Set



/-! # Generated Set constructors, typed -/
namespace Cvc.Proto.Typed.Term public section

open Cvc.Proto renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto.Spec.Set



/-! ## Values -/

@[inherit_doc T.isSetValue]
def isSetValue [Ord α] (term : Term (Cvc.Proto.Set α)) : Bool := T.isSetValue term


section variable [Ord α] [ToTyp α]

/-- The set term denoting a set of values. -/
def mkSetValue [ValueToTerm α] : (set : Cvc.Proto.Set α) → Env (Term (Cvc.Proto.Set α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkSetValue

/-- The set of values a constant set term denotes. -/
def getSetValue [TermToValue α] : Term (Cvc.Proto.Set α) → Env (Cvc.Proto.Set α) :=
  have := TermToValue.toUntyped (α := α)
  T.getSetValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Proto.Set α) := ⟨mkSetValue⟩
instance [TermToValue α] : TermToValue (Cvc.Proto.Set α) := ⟨getSetValue⟩

end
