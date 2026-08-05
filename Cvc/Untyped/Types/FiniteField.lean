module

import all Cvc.Basic.Env
import all Cvc.Untyped.Srt

public import Cvc.Untyped.Term



namespace Cvc public section variable [Ω]

open Untyped

/-- An element of a finite field of size `size`. -/
structure FiniteField (size : Nat) where
  /-- Element representation. -/
  repr : Int
deriving DecidableEq, Hashable, Ord

namespace FiniteField

instance : ToTyp (FiniteField size) := ⟨.finiteField size⟩

/-- Erased version of `FiniteField`. -/
structure Erased where
  /-- The field's size. -/
  size : Nat
  /-- The actual finite field element. -/
  get : FiniteField size

/-- Erases a finite-field-element's size. -/
def erase (elem : FiniteField size) : Erased := {size, get := elem}

/-- String representation. -/
protected def toString (ff : FiniteField size) : String := toString ff.repr

instance : ToString (FiniteField size) := ⟨FiniteField.toString⟩

/-- Creates a constant finite-field-element term. -/
def toTerm (elem : FiniteField size) : Env Term :=
  Srt.of (FiniteField size) >>= Term.mkFiniteFieldElemOfValue elem.repr

namespace Erased
@[inherit_doc FiniteField.toString]
protected def toString (elem : Erased) := elem.get.toString

instance : ToString Erased := ⟨Erased.toString⟩

@[inherit_doc FiniteField.toTerm]
def toTerm (elem : Erased) : Env Term := elem.get.toTerm

/-- Retrieves the value of a constant finite-field-element term. -/
def ofTerm (t : Term) : Env Erased := do
  let srt ← t.getSort
  let size ← srt.getFiniteFieldSize
  let ff ← t.getFiniteFieldValue
  return {size, get := {repr := ff}}

instance : TermToValue Erased := ⟨ofTerm⟩
instance : ValueToTerm Erased := ⟨toTerm⟩
end Erased

/-- Retrieves the `FiniteField` value of a constant finite-field-element term. -/
def ofTerm (t : Term) : Env (FiniteField size) := do
  let ⟨size', elem⟩ ← Erased.ofTerm t
  if h : size' = size then return h ▸ elem
  else throwUser s!"expected finite-field-element of size {size}, got one of size {size'}: {t}"

instance : SrtLike (FiniteField size) where
  termToValue := ofTerm
  valueToTerm := toTerm

end FiniteField
