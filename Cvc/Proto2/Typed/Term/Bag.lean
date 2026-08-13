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

public import Cvc.Proto2.Types.Bag
public import Cvc.Proto2.Untyped.Term.Bag
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Bag



/-! # Generated Bag constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Bag



/-! ## Values -/

section variable [Ord α] [ToTyp α]

/-- The bag term denoting a bag of values. -/
def mkBagValue [ValueToTerm α] : (bag : Cvc.Proto2.Bag α) → Env (Term (Cvc.Proto2.Bag α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkBagValue

/-- The bag of values a constant bag term denotes. -/
def getBagValue [TermToValue α] : Term (Cvc.Proto2.Bag α) → Env (Cvc.Proto2.Bag α) :=
  have := TermToValue.toUntyped (α := α)
  T.getBagValue

instance [ValueToTerm α] : ValueToTerm (Cvc.Proto2.Bag α) := ⟨mkBagValue⟩
instance [TermToValue α] : TermToValue (Cvc.Proto2.Bag α) := ⟨getBagValue⟩

end
