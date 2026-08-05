module

import all Cvc.Typed.Term

public import Cvc.Untyped.Types.Float
public import Cvc.Typed.Defs



namespace Cvc public section variable [Ω]

namespace Typed
export Cvc (Float)
end Typed

open Typed

namespace Float variable [Ord α] [ToTyp α]

def toTypedTerm : (elem : Float exp sig) → Env (Term (Float exp sig)) :=
  Float.toTerm
instance : ValueToTerm (Float exp sig) := ⟨toTypedTerm⟩

def ofTypedTerm : Term (Float exp sig) → Env (Float exp sig) := Float.ofTerm
instance : TermToValue (Float exp sig) := ⟨ofTypedTerm⟩

end Float
