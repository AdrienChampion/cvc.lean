module

import all Cvc.Typed.Term

public import Cvc.Untyped.Types.Array
public import Cvc.Typed.Term



namespace Cvc public section variable [Ω]

namespace Typed
export Cvc (TotalMap)
end Typed

open Typed



namespace TotalMap variable [Ord α] [ToTyp α] [ToTyp β]

def toTypedTerm [A : Typed.ValueToTerm α] [B : Typed.ValueToTerm β]
: TotalMap α β → Env (Typed.Term (TotalMap α β)) :=
  let _ : Cvc.Untyped.ValueToTerm α := ⟨A.valueToTerm⟩
  let _ : Cvc.Untyped.ValueToTerm β := ⟨B.valueToTerm⟩
  TotalMap.toTerm
instance [Typed.ValueToTerm α] [Typed.ValueToTerm β] : Typed.ValueToTerm (TotalMap α β) :=
  ⟨toTypedTerm⟩

def ofTypedTerm [A : Typed.TermToValue α] [B : Typed.TermToValue β]
: Typed.Term (TotalMap α β) → Env (TotalMap α β) :=
  let _ : Cvc.Untyped.TermToValue α := ⟨A.termToValue⟩
  let _ : Cvc.Untyped.TermToValue β := ⟨B.termToValue⟩
  TotalMap.ofTerm
instance [Typed.TermToValue α] [Typed.TermToValue β] : Typed.TermToValue (TotalMap α β) :=
  ⟨ofTypedTerm⟩

end TotalMap

namespace Typed.Term open Cvc renaming Untyped.Term → T

protected abbrev Term.Array (α : Type) [Ord α] (β : Type) := Term (TotalMap α β)

/-- The array that associates a default value to all indices. -/
def mkArrayFrom
  (α : Type) [Ord α] [ToTyp α] [ToTyp β] (default : Term β)
: Env (Term.Array α β) := do
  T.mkArray (← Srt.of (TotalMap α β)) default

variable [Ord α] [A : ToTyp α] [B : ToTyp β]

@[inherit_doc mkArrayFrom]
def mkArray : (default : Term β) → Env (Term.Array α β) := mkArrayFrom α

def% store : (array : Term.Array α β) → (idx : Term α) → (elem : Term β) → Env (Term.Array α β)
def% select:  (array : Term.Array α β) → (idx : Term α) → Env (Term β)

end Typed.Term
