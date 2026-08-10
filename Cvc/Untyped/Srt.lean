/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module


import all Cvc.Basic
import all Cvc.Untyped.Defs

public import Cvc.Untyped.Defs
public import Cvc.Basic


namespace Cvc public section variable [Ω]



namespace Srt open cvc5 renaming TermManager → Tm, «Sort» → S

section

scoped macro "lift% " fn:ident args:(ppSpace ident)* : term =>
  `((runUnsafe fun tm => tm.$fn $[ $args]* : Env Srt))

scoped macro "def% " id:ident args:(ppSpace ident)* " := " fn:ident : command =>
  let fnId := ``Tm |>.append fn.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id := fun $[ $args]* => lift% $fn $[ $args]*)

def% bool := getBooleanSort
def% int := getIntegerSort
def% real := getRealSort
def% string := getStringSort
def% regex := getRegExpSort
def% roundingMode := getRoundingModeSort
def% bitVec size := mkBitVectorSort
def% float exp sig := mkFloatingPointSort
def% finiteField size := mkFiniteFieldSort

end

@[inherit_doc Tm.mkArraySort]
def arrayTo (idx elm : Srt) := lift% mkArraySort idx elm

@[inherit_doc arrayTo]
def arrayFrom (elm idx : Srt) := idx.arrayTo elm

/-- An array of `elm`-values indexed by `int`-values. -/
def array (elm : Srt) : Env Srt := int >>= elm.arrayFrom

def bag (elm : Srt) : Env Srt := lift% mkBagSort elm
def set (elm : Srt) : Env Srt := lift% mkSetSort elm
def seq (elm : Srt) : Env Srt := lift% mkSequenceSort elm

@[inherit_doc Tm.mkFunctionSort]
def function (dom : Array Srt) (cod : Srt)
  (domNonempty : 0 < dom.size := by (try grind) <;> fail "failed to prove the domain is nonempty")
: Env Srt :=
  let _ := domNonempty
  lift% mkFunctionSort dom cod

def abstract (a : Abstract) : Env Srt := lift% mkAbstractSort a.toKind

def Abstract.toSrt (a : Abstract) : Env Srt := abstract a

end Srt


/-! ## Lean types encoding cvc sorts and their values -/

namespace Typ

abbrev isArith : Typ → Bool
| int | real => true
| bool | string | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | seq _ | abstract _ | function _ _ => false

omit [Ω] in
theorem typs_of_isArith {typ : Typ} : typ.isArith → typ = int ∨ typ = real := by grind

abbrev hasConcat : Typ → Bool
| string | seq _ => true
| int | real
| bool | regex | roundingMode
| bitVec _ | float _ _ | finiteField _ | arrayTo _ _
| bag _ | set _ | abstract _ | function _ _ => false

omit [Ω] in
theorem typs_of_hasConcat {typ : Typ} : typ.hasConcat → typ = string ∨ ∃ t, typ = seq t := by grind

/-- Helper for `toSrt`, carries bits of termination-proof around. -/
def foldFunctionCod [Monad m] (srt' : Typ)
  (acc : α) (f : α → (s : Typ) → (sizeOf s < sizeOf srt') → m α)
: m (α × (cod : Typ) ×' sizeOf cod ≤ sizeOf srt') :=
  match h : srt' with
  | function dom cod => do
    let acc ← f acc dom (by grind only [= function.sizeOf_spec])
    let (acc, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
      f acc s (by grind only [= function.sizeOf_spec])
    return (acc, ⟨cod, by grind only [= function.sizeOf_spec]⟩)
  | cod => return (acc, ⟨cod, by grind only⟩)

/-- Conversion to `Srt`. -/
public def toSrt [Ω] : Typ → Env Srt
| bool => Srt.bool | int => Srt.int | real => Srt.real
| regex => Srt.regex | string => Srt.string
| roundingMode => Srt.roundingMode
| bitVec size => Srt.bitVec size.toUInt32
| float exp sig => Srt.float exp.toUInt32 sig.toUInt32
| finiteField size => Srt.finiteField size
| arrayTo idx elm => do elm.toSrt >>= (← idx.toSrt).arrayTo
| bag elm => elm.toSrt >>= Srt.bag
| set elm => elm.toSrt >>= Srt.set
| seq elm => elm.toSrt >>= Srt.seq
| abstract a => Srt.abstract a
| function dom cod => do
  let dom ← dom.toSrt
  /- non-empty array, required for `Srt.function` -/
  let acc : {a : Array Srt // 0 < a.size} := ⟨#[dom], by grind⟩
  let (dom, ⟨cod, h⟩) ← cod.foldFunctionCod acc fun acc s h =>
    /- push and update proof that array (`acc`) is non-empty -/
    return ⟨acc.val.push (← s.toSrt), by grind⟩
  let cod ← cod.toSrt
  Srt.function dom cod

end Typ


/-- The `Typ` associated to some type. -/
abbrev Typ.of (α : Type) [A : ToTyp α] : Typ := A.typ

/-- `Srt` associated to a type through `WithTyp`. -/
abbrev ToTyp.srt [ToTyp α] : Env Srt := Typ.of α |>.toSrt

@[inherit_doc ToTyp.srt]
abbrev Srt.of (α : Type) [A : ToTyp α] : Env Srt := A.srt

-- namespace WithTyp

-- @[default_instance]
-- instance : WithTyp Bool .bool := {}
-- @[default_instance]
-- instance : WithTyp Nat .int := {}
-- @[default_instance]
-- instance : WithTyp Int .int := {}
-- @[default_instance]
-- instance : WithTyp Rat .real := {}
-- @[default_instance]
-- instance : WithTyp String .string := {}
-- @[default_instance]
-- instance : WithTyp (BitVec size) (.bitVec size) := {}
-- @[default_instance]
-- instance : WithTyp Float.RoundingMode .roundingMode := {}
-- @[default_instance]
-- instance [A : ToTyp α] : WithTyp (Array α) (.seq A.typ) := {}

-- end WithTyp

namespace ToTyp

instance : ToTyp Bool := ⟨.bool⟩
instance : ToTyp Int := ⟨.int⟩
instance : ToTyp Rat := ⟨.real⟩
instance : ToTyp String := ⟨.string⟩
instance : ToTyp (BitVec size) := ⟨.bitVec size⟩
instance : ToTyp Cvc.Float.RoundingMode := ⟨.roundingMode⟩
instance [A : ToTyp α] : ToTyp (Array α) := ⟨.seq A.typ⟩

end ToTyp



class IsArith (α : Type) [A : ToTyp α] : Prop where
  valid_typ : A.typ.isArith := by simp [Typ.isArith, ToTyp.typ] <;> grind

instance : IsArith Int := {}
instance : IsArith Rat := {}

class HasConcat (α : Type) [A : ToTyp α] : Prop where
  valid_typ : A.typ.hasConcat := by simp [Typ.hasConcat, ToTyp.typ] <;> grind

instance : HasConcat String := {}
instance [ToTyp α] : HasConcat (Array α) := {}



/-! ### Regular expressions -/

structure Regex
deriving DecidableEq, Hashable, Ord

namespace Regex

instance : ToTyp Regex := ⟨.regex⟩

end Regex



/-! ### Functions -/

namespace ToTyp

instance [A : ToTyp α] [B : ToTyp β] : ToTyp (α → β) := ⟨.function A.typ B.typ⟩

example : ToTyp (Int → Bool → Int → Rat) := inferInstance

end ToTyp
