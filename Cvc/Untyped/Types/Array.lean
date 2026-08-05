module

import all Cvc.Untyped.Srt

public import Cvc.Untyped.Term
public import Std.Data.TreeMap.Basic



namespace Cvc public section variable [Ω]

open Untyped

/-- A total map from `α` (the indices) to `β` (the elements), used to encode SMT-LIB arrays. -/
structure TotalMap (α β : Type) [Ord α] where
  /-- Default element that all indices not captured by `map` are mapped to. -/
  defaultElem : β
  /-- Maps indices to elements. -/
  map : Std.TreeMap α β := Std.TreeMap.empty

namespace TotalMap variable [Ord α]

def mkConst (defaultElem : β) : TotalMap α β where defaultElem

protected def default [Inhabited β] : TotalMap α β := mkConst default
instance [B : Nonempty β] : Nonempty (TotalMap α β) := B.elim (⟨· , Std.TreeMap.empty⟩)
instance [Inhabited β] : Inhabited (TotalMap α β) := ⟨TotalMap.default⟩

instance [ToTyp α] [ToTyp β] : ToTyp (TotalMap α β) := ⟨Typ.of α |>.arrayTo (Typ.of β)⟩

/-! #### Basic operations -/
section variable [Ord α] (map : TotalMap α β) (key : α)

def insert (val : β) : TotalMap α β :=
  {map with map := map.map.insert key val}

def get? : Option β := map.map.get? key

def get : β := map.get? key |>.getD map.defaultElem

end

/-! #### String representation -/

section variable [ToString α] [ToString β] (map : TotalMap α β)

def foldlStrings (f : γ → Bool → String → γ) (init : γ) : γ := Id.run do
  let mut acc := init
  for (key, val) in map.map do
    acc := f acc false s!"{key} ↦ {val}"
  f acc true s!"_ ↦ {map.defaultElem}"

def lines : Array String := map.foldlStrings (init := #[]) fun acc _ s => acc.push s

/-- String representation. -/
protected def toString : String := Id.run do
  map.foldlStrings (init := "{ ") fun acc isLast line =>
    s!"{acc}{line}{if isLast then " }" else ", "}"

instance : ToString (TotalMap α β) := ⟨TotalMap.toString⟩

end

section variable [ToTyp α] [ToTyp β]

def toTerm [ValueToTerm α] [ValueToTerm β] (map : TotalMap α β) : Env Term := do
  let srt ← Srt.of (TotalMap α β)
  let mut t ← Term.mkValue map.defaultElem >>= Term.mkArray srt
  for (idx, elem) in map.map do
    t ← t.store (← Term.mkValue idx) (← Term.mkValue elem)
  return t

instance [ValueToTerm α] [ValueToTerm β] : ValueToTerm (TotalMap α β) := ⟨toTerm⟩

private partial def ofTerm.peelStores [A : TermToValue α] [B : TermToValue β]
  (map : Std.TreeMap α β) (t : Term)
: Env (TotalMap α β) := do
  let k := t.getKind?
  if let some cvc5.Kind.STORE := k then
    let kids := t.getChildren
    if h : kids.size = 3 then
      let (array, idx, elm) := (kids[0], kids[1], kids[2])
      let idx ← A.termToValue idx
      let elm ← B.termToValue elm
      let map := if ¬ map.contains idx then map.insert idx elm else map
      peelStores map array
    else throwInternal s!"{cvc5.Kind.STORE}-term should have three kids, got {kids}"
  else if let some defaultVal := t.getConstArrayBase? then
    let defaultVal ← B.termToValue defaultVal
    return .mk defaultVal map
  else throwUser "expected a constant array-term"

def ofTerm [TermToValue α] [TermToValue β] (t : Term) : Env (TotalMap α β) := do
  ofTerm.peelStores Std.TreeMap.empty t

instance [TermToValue α] [TermToValue β] : TermToValue (TotalMap α β) := ⟨ofTerm⟩

def termsToValues (α β : Type) [Ord α] [TermToValue α] [TermToValue β]
  (map : TotalMap Term Term)
: Env (TotalMap α β) := do
  let defaultElem ← map.defaultElem.getValue
  let map ← map.map.foldlM (init := Std.TreeMap.empty) fun map key val =>
    return map.insert (← key.getValue) (← val.getValue)
  return {map, defaultElem}

end

end TotalMap

namespace Untyped.Term

def mkArrayValue [Ord α] [ToTyp α] [ToTyp β] [ValueToTerm α] [ValueToTerm β]
: TotalMap α β → Env Term :=
  TotalMap.toTerm

def getArrayValue : Term → Env (TotalMap Term Term) := TotalMap.ofTerm

end Untyped.Term
