module

import all Cvc.Basic.Env
import all Cvc.Untyped.Srt

public import Cvc.Untyped.Term
public import Std.Data.TreeSet.Basic



namespace Cvc public section variable [Ω]

open Untyped

/-- Alias for `Std.TreeSet`. -/
abbrev Set (α : Type) [Ord α] := Std.TreeSet α

namespace Set variable [Ord α]

open Std renaming TreeSet → S

@[inherit_doc S.empty] def empty : Set α := S.empty
@[inherit_doc S.ofArray] def ofArray := S.ofArray (α := α)

instance [A : ToTyp α] : ToTyp (Set α) := ⟨.set A.typ⟩

/-- String representation. -/
protected def toString [ToString α] (set : Set α) : String :=
  if set.isEmpty then "∅" else Id.run do
    let mut s := ""
    let mut sep := ""
    for elem in set do
      s := s!"{s}{sep}{elem}"
      sep := ", "
    s!"\{ {s} }"

instance [ToString α] : ToString (Set α) := ⟨Set.toString⟩

section variable [ToTyp α] [Ord α]

def toTerm [ValueToTerm α] (set : Set α) : Env Term := do
  let mut term ← Srt.of (Set α) >>= Term.mkEmptySet
  for elem in set do
    term ← Term.mkValue elem >>= term.setInsert
  return term

instance [ValueToTerm α] : ValueToTerm (Set α) := ⟨toTerm⟩

def ofTerm [TermToValue α] (t : Term) : Env (Set α) := do
  let elems ← t.getSetValue
  elems.foldlM (init := Set.empty) fun set term => set.insert <$> Term.getValue term

instance [TermToValue α] : TermToValue (Set α) := ⟨ofTerm⟩

end

end Set
