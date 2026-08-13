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

public import Cvc.Proto2.Types.Set
public import Cvc.Proto2.Untyped.Term.Set
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Set



/-! # Generated Set constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Set



/-! ## Values -/

@[inherit_doc T.isSetValue]
def isSetValue [Ord α] (term : Term (Cvc.Proto2.Set α)) : Bool := T.isSetValue term


section variable [Ord α] [ToTyp α]

/-- The set term denoting a set of values. -/
def mkSetValue [ValueToTerm α] : (set : Cvc.Proto2.Set α) → Env (Term (Cvc.Proto2.Set α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkSetValue

/-- The set of values a constant set term denotes. -/
def getSetValue [TermToValue α] : Term (Cvc.Proto2.Set α) → Env (Cvc.Proto2.Set α) :=
  have := TermToValue.toUntyped (α := α)
  T.getSetValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Proto2.Set α) := ⟨mkSetValue⟩
instance [TermToValue α] : TermToValue (Cvc.Proto2.Set α) := ⟨getSetValue⟩

end
