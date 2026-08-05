module

import all Cvc.Untyped.Srt

public import Cvc.Untyped.Term
public import Std.Data.TreeMap.Basic



namespace Cvc public section variable [Ω]

open Untyped

abbrev Bag (α : Type) [Ord α] := Std.TreeMap α Int

namespace Bag variable [Ord α] (bag : Bag α)

def empty : Bag α := Std.TreeMap.empty

def alter (key : α) (f : Int → Int) : Bag α :=
  Std.TreeMap.alter bag key fun val? => match val?.getD 0 |> f with | 0 => none | n => n

def increment (key : α) := bag.alter key (· + 1)

def decrement (key : α) := bag.alter key (· - 1)

def add (key : α) (n : Int) := bag.alter key (· + n)

def sub (key : α) (n : Int) := bag.alter key (· - n)

def get? (key : α) : Option Int := Std.TreeMap.get? bag key

def get (key : α) : Int := bag.get? key |>.getD 0

def contains (key : α) : Bool := 0 < bag.get key

protected abbrev mem (key : α) : Prop := bag.contains key

instance : Membership α (Bag α) := ⟨Bag.mem⟩

omit [Ω] in
theorem mem_def {key : α} : (key ∈ bag) = bag.contains key := rfl

instance (key : α) : Decidable (key ∈ bag) :=
  bag.mem_def ▸ if h : bag.contains key then isTrue h else isFalse h

protected def toString [ToString α] (bag : Bag α) : String :=
  bag.foldl (init := "") fun
    | acc, _key, 0 => acc
    | acc, key, n => s!"{if acc.isEmpty then acc else acc ++ ", "}{key} ↦ {n}"

instance [ToString α] : ToString (Bag α) := ⟨Bag.toString⟩

instance [A : ToTyp α] : ToTyp (Bag α) := ⟨.bag A.typ⟩

section variable [A : ToTyp α] [Ord α]

def toTerm [ValueToTerm α] (set : Bag α) : Env Term := do
  let empty ← Srt.of (Bag α) >>= Term.mkEmptyBag
  set.foldlM (init := empty) fun bag elem count => do
    let elem ← Term.mkValue elem
    let count ← Term.mkInt count
    Term.mkBagWith elem count >>= bag.bagUnionMax

instance [ValueToTerm α] : ValueToTerm (Bag α) := ⟨toTerm⟩

partial def ofTerm [TermToValue α] (t : Term) : Env (Bag α) := do
  let k ← t.getKind
  match k with
  | .BAG_EMPTY => return Bag.empty
  | .BAG_MAKE =>
    let ⟨kids, _⟩ ← t.getSizedKids 2
    let elem ← Term.getValue kids[0]
    let count ← Term.getValue kids[1]
    return Bag.empty.insert elem count
  | .BAG_UNION_MAX
  | .BAG_UNION_DISJOINT
  | .BAG_INTER_MIN
  | .BAG_DIFFERENCE_SUBTRACT
  | .BAG_DIFFERENCE_REMOVE => throwTodo s!"bag-value reconstruction for term-kind `{k}`"
  | _ => throwUser s!"expected `{A.typ}`-bag"

instance [TermToValue α] : TermToValue (Bag α) := ⟨ofTerm⟩

end

end Bag
