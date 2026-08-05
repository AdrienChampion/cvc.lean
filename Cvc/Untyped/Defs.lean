/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.BuiltinCommand

public import Cvc.Basic.Env



namespace Cvc



public meta section codeGen open Lean Syntax Elab Command

structure TypeGen where mk' ::
  mainId : Ident
  tParam? : Option Ident
  subId : Ident
  ofSubId : Ident
  toSubId : Ident
  idTerm : Term
  idSig : Term
  idDef : Term

namespace TypeGen variable (tg : TypeGen)

def mk (mainId : Ident) (subId : Ident)  (tParam? ofSubId? toSubId? : Option Ident)
: CommandElabM TypeGen := do
  let mut ofSubId := mkIdent `ofUnsafe
  let mut toSubId := mkIdent `toUnsafe
  if let (some ofSubId', some toSubId') := (ofSubId?, toSubId?) then
    ofSubId := ofSubId'
    toSubId := toSubId'
  let mut idDef ← `($subId)
  let mut idSig ← ``(Type)
  let mut idTerm ← `($mainId)
  if let some tParam := tParam? then
    idDef ← `(fun _ => $idDef)
    idSig ← `( (_ : Type) → $idSig )
    idTerm ← `($idTerm $tParam)
  return {
    mainId, tParam?, subId, ofSubId, toSubId
    idTerm, idSig, idDef
  }

def namespaced (code : CommandElabM α) : CommandElabM α :=
  Lean.Elab.Command.withNamespace tg.mainId.getId code

def elaborate (stx : CommandElabM (TSyntax `command)) : CommandElabM Unit := do
  let stx ← stx
  elabCommand stx

def elab0 : CommandElabM Unit := do
  elaborate `(
    @[inherit_doc $tg.subId]
    def $tg.mainId [Ω] : $tg.idSig := $tg.idDef
  )
  tg.namespaced do elaborate `(
    instance : Nonempty $tg.idTerm := inferInstanceAs (Nonempty $tg.subId)
    @[inline] private def $tg.ofSubId : $tg.subId → $tg.idTerm := id
    @[inline] private def $tg.toSubId : $tg.idTerm → $tg.subId := id
  )

def elab1 : CommandElabM Unit := do
  tg.elab0
  let toStringId := `toString |> mkIdent
  let toStringSubId := tg.subId.getId |>.append `toString |> mkIdent
  tg.namespaced do elaborate `(
    instance : ToString $tg.idTerm := inferInstanceAs (ToString $tg.subId)
    @[inherit_doc $toStringSubId]
    protected def $toStringId : $tg.idTerm → String := $toStringSubId
  )

def elab2 : CommandElabM Unit := do
  tg.elab1
  let beqId := `beq |> mkIdent
  let beqSubId := tg.subId.getId |>.append `beq |> mkIdent
  let hashId := `hash |> mkIdent
  let hashSubId := tg.subId.getId |>.append `hash |> mkIdent
  tg.namespaced do elaborate `(
    instance : BEq $tg.idTerm := inferInstanceAs (BEq $tg.subId)
    @[inherit_doc $beqSubId]
    protected def $beqId : $tg.idTerm → $tg.idTerm → Bool := $beqSubId
    instance : Hashable $tg.idTerm := inferInstanceAs (Hashable $tg.subId)
    @[inherit_doc $hashSubId]
    protected def $hashId : $tg.idTerm → UInt64 := $hashSubId
  )

def elab3 : CommandElabM Unit := do
  tg.elab2
  let bltId := `blt |> mkIdent
  let bltSrc := tg.subId.getId |>.append `blt |> mkIdent
  let bleId := `ble |> mkIdent
  let bleSrc := tg.subId.getId |>.append `ble |> mkIdent
  let bgtId := `bgt |> mkIdent
  let bgtSrc := tg.subId.getId |>.append `bgt |> mkIdent
  let bgeId := `bge |> mkIdent
  let bgeSrc := tg.subId.getId |>.append `bge |> mkIdent
  let compareId := `compare |> mkIdent
  let compareSrc := tg.subId.getId |>.append `compare |> mkIdent
  tg.namespaced do elaborate `(
    instance : LT $tg.idTerm := inferInstanceAs (LT $tg.subId)
    instance : DecidableLT $tg.idTerm := inferInstanceAs (DecidableLT $tg.subId)
    instance : LE $tg.idTerm := inferInstanceAs (LE $tg.subId)
    instance : DecidableLE $tg.idTerm := inferInstanceAs (DecidableLE $tg.subId)

    @[inherit_doc $bltSrc]
    protected def $bltId : $tg.idTerm → $tg.idTerm → Bool := $bltSrc
    @[inherit_doc $bleSrc]
    protected def $bleId : $tg.idTerm → $tg.idTerm → Bool := $bleSrc
    @[inherit_doc $bgtSrc]
    protected def $bgtId : $tg.idTerm → $tg.idTerm → Bool := $bgtSrc
    @[inherit_doc $bgeSrc]
    protected def $bgeId : $tg.idTerm → $tg.idTerm → Bool := $bgeSrc

    instance : Ord $tg.idTerm := inferInstanceAs (Ord $tg.subId)

    @[inherit_doc $compareSrc]
    protected def $compareId : $tg.idTerm → $tg.idTerm → Ordering := $compareSrc
  )

end TypeGen

declare_syntax_cat cvcCustomDefKw

syntax "def0% " : cvcCustomDefKw
syntax "def1% " : cvcCustomDefKw
syntax "def2% " : cvcCustomDefKw
syntax "def3% " : cvcCustomDefKw

syntax (name := cvcCustomDef)
  cvcCustomDefKw ident (ident)? " ← " ident
    ("( " ident " / " ident " )")?
: command

@[command_elab cvcCustomDef]
def elab_cvcCustomDef : CommandElab
| `( $kw:cvcCustomDefKw $id $[ $tParam? ]? ← $subId $[ ( $ofSubId? / $toSubId? ) ]? ) => do
  let tg ← TypeGen.mk id subId tParam? ofSubId? toSubId?
  match kw with
  | `(cvcCustomDefKw| def0%) => tg.elab0
  | `(cvcCustomDefKw| def1%) => tg.elab1
  | `(cvcCustomDefKw| def2%) => tg.elab2
  | `(cvcCustomDefKw| def3%) => tg.elab3
  | _ => throwUnsupportedSyntax
| _ => throwUnsupportedSyntax

end codeGen


public section variable [Ω]

def0% Proof ← cvc5.Proof

def1% Command ← cvc5.Command

def2% Datatype.Decl ← cvc5.DatatypeDecl
def2% Datatype ← cvc5.Datatype
def2% Datatype.Constructor.Decl ← cvc5.DatatypeConstructorDecl
def2% Datatype.Constructor ← cvc5.DatatypeConstructor
def2% Datatype.Selector ← cvc5.DatatypeSelector
def2% Grammar ← cvc5.Grammar



def3% Srt ← cvc5.Sort

namespace Srt

inductive Abstract
| array
| bitVec
| float
| finiteField
| function
| bag
| set
| seq
deriving Inhabited, DecidableEq, BEq, Ord, Hashable, Repr

namespace Abstract

protected def toString : (a : Srt.Abstract) → String
| array => "Array _ _"
| bitVec => "BitVec _"
| float => "Float _ _"
| finiteField => "FiniteField _"
| function => "_ → _"
| bag => "Bag _"
| set => "Set _"
| seq => "Seq _"

instance : ToString Srt.Abstract := ⟨Abstract.toString⟩

private def ofKind : (k : cvc5.SortKind) → Res Abstract
  | .ARRAY_SORT => return array
  | .BITVECTOR_SORT => return bitVec
  | .FLOATINGPOINT_SORT => return float
  | .FINITE_FIELD_SORT => return finiteField
  | .FUNCTION_SORT => return function
  | .BAG_SORT => return bag
  | k => throwInternal s!"sort kind `{k}` is not abstract-able"

def toKind : (a : Abstract) → cvc5.SortKind
  | array => .ARRAY_SORT
  | bitVec => .BITVECTOR_SORT
  | float => .FLOATINGPOINT_SORT
  | finiteField => .FINITE_FIELD_SORT
  | function => .FUNCTION_SORT
  | bag => .BAG_SORT
  | set => .SET_SORT
  | seq => .SEQUENCE_SORT

instance : Ord Abstract := ⟨fun a1 a2 => compare a1.ctorIdx a2.ctorIdx⟩

section variable (a1 a2 : Abstract)

protected def ble : Bool := a1.ctorIdx ≤ a2.ctorIdx
protected def blt : Bool := a1.ctorIdx < a2.ctorIdx

end

instance : LE Abstract := ⟨(Abstract.ble · ·)⟩
instance : DecidableLE Abstract := fun a1 a2 => if h : a1.ble a2 then isTrue h else isFalse h
instance : LT Abstract := ⟨(Abstract.blt · ·)⟩
instance : DecidableLT Abstract := fun a1 a2 => if h : a1.blt a2 then isTrue h else isFalse h

end Abstract
end Srt

/-- An array of `Srt`s. -/
abbrev Srts := Array Srt

namespace Srts

private def toUnsafe : Srts → Array cvc5.Sort := id
private def ofUnsafe : Array cvc5.Sort → Srts := id

end Srts



inductive Typ
| bool | int | real | string | regex | roundingMode
| bitVec (size : Nat)
| float (exp sig : Nat)
| finiteField (size : Nat)
| arrayTo (idx elm : Typ)
| bag (elm : Typ) | set (elm : Typ) | seq (elm : Typ)
| abstract (a : Srt.Abstract)
| function (dom : Typ) (cod : Typ)
deriving DecidableEq, Ord, Hashable

namespace Typ

protected def toString (t : Typ) (paren : Bool := false) : String :=
  let paren (s : String) := if paren then s!"({s})" else s
  match t with
  | bool => "Bool" | int => "Int" | real => "Real" | string => "String"
  | regex => "Regex" | roundingMode => "RoundingMode"
  | bitVec size => paren s!"BitVec {size}"
  | float exp sig => paren s!"Float {exp} {sig}"
  | finiteField size => paren s!"FiniteField {size}"
  | arrayTo idx elm => paren s!"Array {idx.toString true} {elm.toString true}"
  | bag elm => paren s!"Bag {elm.toString true}"
  | set elm => paren s!"Set {elm.toString true}"
  | seq elm => paren s!"Seq {elm.toString true}"
  | abstract a => paren s!"Abstract {a}"
  | function dom cod => paren s!"{dom.toString false} → {cod.toString false}"

instance : ToString Typ := ⟨Typ.toString⟩

end Typ

class ToTyp (α : Type) where
  /-- `Typ` associated to a type through `ToTyp`. -/
  typ : Typ



namespace Untyped

def3% Term ← cvc5.Term

/-- An array of `Srt`s. -/
abbrev Terms := Array Term

namespace Terms

private def toUnsafe : Terms → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms := id

end Terms

class TermToValue (α : Type) where
  termToValue : Term → Env α

namespace TermToValue
instance : TermToValue Term := ⟨pure⟩
end TermToValue

class ValueToTerm (α : Type) where
  valueToTerm : α → Env Term

namespace ValueToTerm
instance : ValueToTerm Term := ⟨pure⟩
end ValueToTerm

class abbrev SrtLike (α : Type) := ToTyp α, TermToValue α, ValueToTerm α

end Untyped
