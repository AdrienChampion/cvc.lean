/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto.Srt

public import Cvc.Proto.Srt

import all Cvc.Basic.Env
import all Cvc.Proto.Untyped.Term.Defs

public import Cvc.Proto.Untyped.Term.Defs
public import Cvc.Proto.Ext
public import Cvc.Proto.Untyped.Term.Value
public import Cvc.Proto.Types.Set
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.Set



/-! # Generated Set constructors, sort-erased -/
namespace Cvc.Proto.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T

gen_untyped% from Cvc.Proto.Spec.Set



/-! ## Values

A `Cvc.Proto.Set` denotes an SMT set: the empty set, with each element inserted.
-/

@[inherit_doc T.isSetValue]
def isSetValue (term : Term) : Bool := T.isSetValue term.toUnsafe


/-- The elements a constant set term denotes. -/
def getSetElems (term : Term) : Env Terms := do
  let elems : Terms ← T.getSetValue term.toUnsafe |>.mapError Error.ofUnsafe
  return elems

section variable [Ord α] [ToTyp α]

/-- The set term denoting a set of values. -/
def mkSetValue [ValueToTerm α] (set : Cvc.Proto.Set α) : Env Term := do
  let mut term ← Srt.of (Cvc.Proto.Set α) >>= setEmpty
  for elem in set do
    term ← mkValue elem >>= (setInsert · term)
  return term

/-- The set of values a constant set term denotes. -/
def getSetValue [TermToValue α] (term : Term) : Env (Cvc.Proto.Set α) := do
  let elems ← term.getSetElems
  elems.foldlM (init := Cvc.Proto.Set.empty) fun set elem => set.insert <$> getValue elem

instance [ValueToTerm α] : ValueToTerm (Cvc.Proto.Set α) := ⟨mkSetValue⟩
instance [TermToValue α] : TermToValue (Cvc.Proto.Set α) := ⟨getSetValue⟩

end
