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

public import Cvc.Proto2.Types.Array
public import Cvc.Proto2.Untyped.Term.Array
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Array



/-! # Generated Array constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Array



/-! ## Values -/

@[inherit_doc T.isConstArray]
def isConstArray [Ord α] (term : Term (Cvc.Proto2.TotalMap α β)) : Bool := T.isConstArray term


section variable [Ord α] [ToTyp α] [ToTyp β]

/-- The array term denoting a total map. -/
def mkArrayValue [ValueToTerm α] [ValueToTerm β]
: Cvc.Proto2.TotalMap α β → Env (Term (Cvc.Proto2.TotalMap α β)) :=
  have := ValueToTerm.toUntyped (α := α)
  have := ValueToTerm.toUntyped (α := β)
  T.mkArrayValue

/-- The total map a constant array term denotes. -/
def getArrayValue [TermToValue α] [TermToValue β]
: Term (Cvc.Proto2.TotalMap α β) → Env (Cvc.Proto2.TotalMap α β) :=
  have := TermToValue.toUntyped (α := α)
  have := TermToValue.toUntyped (α := β)
  T.getArrayValue

instance [ValueToTerm α] [ValueToTerm β] : ValueToTerm (Cvc.Proto2.TotalMap α β) := ⟨mkArrayValue⟩
instance [TermToValue α] [TermToValue β] : TermToValue (Cvc.Proto2.TotalMap α β) := ⟨getArrayValue⟩

end
