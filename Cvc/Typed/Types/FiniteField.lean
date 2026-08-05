module

import all Cvc.Typed.Term

public import Cvc.Untyped.Types.FiniteField
public import Cvc.Typed.Defs



namespace Cvc public section variable [Ω]

namespace Typed
export Cvc (FiniteField)
end Typed

open Typed

namespace FiniteField variable [Ord α] [ToTyp α]

def toTypedTerm : (elem : FiniteField size) → Env (Term (FiniteField size)) :=
  FiniteField.toTerm
instance : ValueToTerm (FiniteField size) := ⟨toTypedTerm⟩

def ofTypedTerm : Term (FiniteField size) → Env (FiniteField size) := FiniteField.ofTerm
instance : TermToValue (FiniteField size) := ⟨ofTypedTerm⟩

end FiniteField
