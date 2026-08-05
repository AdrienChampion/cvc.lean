module

import all Cvc.Typed.Term

public import Cvc.Untyped.Types.Set
public import Cvc.Typed.Defs



namespace Cvc public section variable [Ω]

namespace Typed
export Cvc (Set)
end Typed

open Typed

namespace Set variable [Ord α] [ToTyp α]

def toTypedTerm [A : ValueToTerm α] : (bag : Set α) → Env (Term (Set α)) :=
  have : Untyped.ValueToTerm α := ⟨A.valueToTerm⟩
  Set.toTerm
instance [ValueToTerm α] : ValueToTerm (Set α) := ⟨toTypedTerm⟩

def ofTypedTerm [A : TermToValue α] : Term (Set α) → Env (Set α) :=
  have : Untyped.TermToValue α := ⟨A.termToValue⟩
  Set.ofTerm
instance [TermToValue α] : TermToValue (Set α) := ⟨ofTypedTerm⟩

end Set

namespace Typed.Term

protected abbrev Set (α : Type) [Ord α] := Term (Set α)

end Typed.Term
