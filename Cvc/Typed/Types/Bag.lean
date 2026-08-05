module

import all Cvc.Typed.Term

public import Cvc.Untyped.Types.Bag
public import Cvc.Typed.Defs



namespace Cvc public section variable [Ω]

namespace Typed
export Cvc (Bag)
end Typed

open Typed



namespace Bag variable [Ord α] [ToTyp α]

def toTypedTerm [A : Typed.ValueToTerm α] : (bag : Bag α) → Env (Typed.Term (Bag α)) :=
  let _ : Untyped.ValueToTerm α := ⟨A.valueToTerm⟩
  Bag.toTerm
instance [Typed.ValueToTerm α] : Typed.ValueToTerm (Bag α) := ⟨toTypedTerm⟩

def ofTypedTerm [A : Typed.TermToValue α] : Typed.Term (Bag α) → Env (Bag α) :=
  let _ : Untyped.TermToValue α := ⟨A.termToValue⟩
  Bag.ofTerm
instance [Typed.TermToValue α] : Typed.TermToValue (Bag α) := ⟨ofTypedTerm⟩

end Bag

namespace Typed.Term open Cvc renaming Untyped.Term → T

protected abbrev Bag (α : Type) [Ord α] := Term (Bag α)

@[inherit_doc T.mkEmptyBag]
def mkEmptyBag' (α : Type) [Ord α] [A : ToTyp α] : Env (Term.Bag α) :=
  Srt.of α >>= T.mkEmptyBag

variable [Ord α] [A : ToTyp α]

@[inherit_doc mkEmptyBag']
def mkEmptyBag : Env (Term.Bag α) := mkEmptyBag' α

def% mkBagWith : (elem : Term α) → (count : Term Int) → Env (Term.Bag α)
def% bagCount : (bag : Term.Bag α) → (elem : Term α) → Env (Term Int)
def% bagUnionMax : (bag1 bag2 : Term.Bag α) → Env (Term.Bag α)
def% bagUnionDisjoint : (bag1 bag2 : Term.Bag α) → Env (Term.Bag α)
def% bagInterMin : (bag1 bag2 : Term.Bag α) → Env (Term.Bag α)

end Typed.Term
