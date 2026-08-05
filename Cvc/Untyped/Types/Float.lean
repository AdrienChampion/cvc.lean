module

import all Cvc.Basic.Env
import all Cvc.Untyped.Srt

public import Cvc.Untyped.Term



namespace Cvc public section variable [Ω]

open Untyped

/-- Floats with exponent `exp` and significand `sig`. -/
inductive Float (exp sig : Nat)
/-- Positive infinity. -/
| posInf
/-- Negative infinity. -/
| negInf
/-- Not-a-number. -/
| nan
/-- Zero-right-limit. -/
| posZero
/-- zero-left-limit. -/
| negZero
/-- Bitvector representation of a floating point. -/
| ofBitVec (bv : BitVec (1 + exp + sig))
deriving DecidableEq, Hashable, Ord

@[inherit_doc Float.ofBitVec]
def BitVec.toFloat (exp sig : Nat) (bv : BitVec (1 + exp + sig)) : Float exp sig := .ofBitVec bv



namespace Float

instance : ToTyp (Float exp sig) := ⟨.float exp sig⟩

/-- Erased version of `Float`. -/
structure Erased where
  /-- Exponent. -/
  exp : Nat
  /-- Significand. -/
  sig : Nat
  /-- Actual floating-point value. -/
  get : Float exp sig

/-- Erases a floating-point's exponent and significand. -/
def erase (f : Float exp sig) : Erased := {exp, sig, get := f}

/-- String representation.-/
protected def toString (f : Float exp sig) : String :=
  let inner := match f with
  | posInf => "+∞"
  | negInf => "-∞"
  | nan => "NaN"
  | posZero => "+0"
  | negZero => "-0"
  | ofBitVec bv => toString bv
  s!"Float[{exp}, {sig}, {inner}]"

instance : ToString (Float exp sig) := ⟨Float.toString⟩

/-- Creates a constant floating-point term. -/
def toTerm : (f : Float exp sig) → Env Term
| .posInf => Term.mkFloatPosInf exp.toUInt32 sig.toUInt32
| .negInf => Term.mkFloatNegInf exp.toUInt32 sig.toUInt32
| .nan => Term.mkFloatNaN exp.toUInt32 sig.toUInt32
| .posZero => Term.mkFloatPosZero exp.toUInt32 sig.toUInt32
| .negZero => Term.mkFloatNegZero exp.toUInt32 sig.toUInt32
| .ofBitVec bv => Term.mkValue bv >>= Term.mkFloatOfBitVec exp.toUInt32 sig.toUInt32

namespace Erased
@[inherit_doc Float.toString]
protected def toString (f : Erased) := f.get.toString

instance : ToString Erased := ⟨Erased.toString⟩

@[inherit_doc Float.toTerm]
def toTerm (f : Erased) : Env Term := f.get.toTerm

/-- Retrieves the value of a constant floating-point term. -/
def ofTerm (t : Term) : Env Erased := do
  if let some (exp, sig, bvTerm) := t.getFloatingPointValue? then
    let bv ← Term.getValue bvTerm
    return {exp := exp.toNat, sig := sig.toNat, get := .ofBitVec bv}
  else
    let srt ← t.getSort
    let exp ← UInt32.toNat <$> srt.getFloatingPointExponentSize
    let sig ← UInt32.toNat <$> srt.getFloatingPointSignificandSize
    let mk (f : Float exp sig) : Env Erased := return {exp, sig, get := f}
    if t.isFloatingPointPosInf then mk .posInf
    else if t.isFloatingPointNegInf then mk .negInf
    else if t.isFloatingPointNaN then mk .nan
    else if t.isFloatingPointPosZero then mk .posZero
    else if t.isFloatingPointNegZero then mk .negZero
    else throwUser s!"expected constant floating-point term, got {t}"

instance : TermToValue Erased := ⟨ofTerm⟩
instance : ValueToTerm Erased := ⟨toTerm⟩
end Erased

/-- Retrieves the `BitVec` value of a constant bitvector term. -/
def ofTerm (t : Term) : Env (Float exp sig) := do
  let ⟨exp', sig', float⟩ ← Erased.ofTerm t
  if h : exp' = exp ∧ sig' = sig then return h.left ▸ h.right ▸ float
  else throwUser s!"expected floating-point constant with exp/sig of {exp}/{sig}, got {exp'}/{sig'}"

instance : SrtLike (Float exp sig) where
  termToValue := ofTerm
  valueToTerm := toTerm

end Float
