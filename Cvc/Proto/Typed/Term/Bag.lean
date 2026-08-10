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

public import Cvc.Proto.Types.Bag
public import Cvc.Proto.Untyped.Term.Bag
public import Cvc.Proto.Typed.Term.Defs
public import Cvc.Proto.Typed.Term.Value
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.Bag



/-! # Generated Bag constructors, typed -/
namespace Cvc.Proto.Typed.Term public section

open Cvc.Proto renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto.Spec.Bag



/-! ## Values -/

section variable [Ord α] [ToTyp α]

/-- The bag term denoting a bag of values. -/
def mkBagValue [ValueToTerm α] : (bag : Cvc.Proto.Bag α) → Env (Term (Cvc.Proto.Bag α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkBagValue

/-- The bag of values a constant bag term denotes. -/
def getBagValue [TermToValue α] : Term (Cvc.Proto.Bag α) → Env (Cvc.Proto.Bag α) :=
  have := TermToValue.toUntyped (α := α)
  T.getBagValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Proto.Bag α) := ⟨mkBagValue⟩
instance [TermToValue α] : TermToValue (Cvc.Proto.Bag α) := ⟨getBagValue⟩

end
