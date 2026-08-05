/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Untyped.Defs
import all Cvc.Untyped.Srt

public import Cvc.Untyped.Srt
import Lean.Parser.Term



namespace Cvc public section open cvc5 renaming TermManager → Tm, Term → T variable [Ω]

local macro "lift% " fn:ident args:(ppSpace term:max)* : term =>
  `((runUnsafe fun tm =>tm.$fn $[ $args]* : Env Untyped.Term))

local macro "liftKind% " op:term:max args:(ppSpace term:max)* : term =>
  `((runUnsafe fun tm =>tm.mkTerm $op #[$[ $args],*] : Env Untyped.Term))


local macro "def% " id:ident args:(ppSpace ident)* " := " fn:ident : command =>
  let fnId := ``Tm |>.append fn.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id := fun $[ $args]* => (lift% $fn $[ $args]* : Env Untyped.Term))




namespace Untyped.Term

/-- Creates a constant value. -/
def mkValue [A : ValueToTerm α] : (value : α) → Env Term := A.valueToTerm
@[inherit_doc mkValue]
def mkValueAs (α : Type) [A : ValueToTerm α] : (value : α) → Env Term := mkValue

/-- Extracts an `α`-value from a constant term. -/
def getValue [A : TermToValue α] : Term → Env α := A.termToValue

@[inherit_doc getValue]
def getValueAs (α : Type) [A : TermToValue α] : Term → Env α := getValue



def% mkBool b := mkBoolean
def% mkInt i := mkInteger
def% mkReal r := mkRealOfRat
def% mkRealOfString s := mkRealOfString

@[inherit_doc Tm.mkConst]
def mkSymbolOfSrt (srt : Srt) (symbol : String) : Env Term := lift% mkConst srt symbol

@[inherit_doc Tm.mkConst]
def mkSymbol (symbol : String) (srt : Srt) : Env Term := mkSymbolOfSrt srt symbol

@[inherit_doc Tm.mkConst]
def mkSymbolAs (α : Type) [ToTyp α] (symbol : String) : Env Term :=
  Srt.of α >>= mkSymbol symbol

@[inherit_doc Tm.mkVar]
def mkVar (symbol : String) (srt : Srt) : Env Term := lift% mkVar srt symbol

@[inherit_doc Tm.mkString]
def mkString (s : String) (useEscSequences : Bool := false) : Env Term :=
  lift% mkString s useEscSequences

@[inherit_doc Tm.mkRoundingMode]
def mkRoundingMode (rm : Float.RoundingMode) : Env Term := lift% mkRoundingMode rm.toUnsafe

instance : Untyped.ValueToTerm Float.RoundingMode := ⟨mkRoundingMode⟩

@[inherit_doc Tm.mkBitVector]
def mkConstBitVec (size : UInt32) (val : UInt64 := 0) : Env Term := lift% mkBitVector size val

@[inherit_doc Tm.mkBitVectorOfString]
def mkBitVecOfString (size : UInt32) (s : String) (base : BitVec.Base := .bin) : Env Term :=
  lift% mkBitVectorOfString size s base.toUInt32

def mkBitVec (bv : BitVec size) : Env Term := mkConstBitVec size.toUInt32 bv.toNat.toUInt64

@[inherit_doc Tm.mkFloatingPoint]
def mkFloatOfBitVec (exp sig : UInt32) (bv : Term) : Env Term :=
  lift% mkFloatingPoint exp sig bv

@[inherit_doc Tm.mkFloatingPointPosInf]
def mkFloatPosInf (exp sig : UInt32) : Env Term :=
  lift% mkFloatingPointPosInf exp sig

@[inherit_doc Tm.mkFloatingPointNegInf]
def mkFloatNegInf (exp sig : UInt32) : Env Term :=
  lift% mkFloatingPointNegInf exp sig

@[inherit_doc Tm.mkFloatingPointNaN]
def mkFloatNaN (exp sig : UInt32) : Env Term :=
  lift% mkFloatingPointNaN exp sig

@[inherit_doc Tm.mkFloatingPointPosZero]
def mkFloatPosZero (exp sig : UInt32) : Env Term :=
  lift% mkFloatingPointPosZero exp sig

@[inherit_doc Tm.mkFloatingPointNegZero]
def mkFloatNegZero (exp sig : UInt32) : Env Term :=
  lift% mkFloatingPointNegZero exp sig

@[inherit_doc Tm.mkFiniteFieldElem]
def mkFiniteFieldElemOfValue (value : Int) (sort : Srt) : Env Term :=
  lift% mkFiniteFieldElem value sort

/-- The array that associates a default value to all indices.

- `srt`: the sort of the array being constructed, must be an array-sort.
- `default`: the default value all indices map to.
-/
def mkArray (srt : Srt) (default : Term) : Env Term := lift% mkConstArray srt default

/-- The empty set for set-sort `srt`. -/
def mkEmptySet (srt : Srt) := lift% mkEmptySet srt

/-- Set insertion. -/
def setInsert (set elem : Term) : Env Term := liftKind% .SET_INSERT set elem

section sequences
/-- The empty sequence with `srt` elements. -/
def mkEmptySeq (srt : Srt) := lift% mkEmptySequence srt

/-- Creates a sequence with one element. -/
def unitSeq (elm : Term) := liftKind% .SEQ_UNIT elm

/-- Sequence concatenation. -/
def mkSeqConcat (seqs : Terms) : (nempty : 0 < seqs.size := by grind) → Env Term := fun _ => do
  let seqs ← seqs.mapM unitSeq
  runUnsafe fun tm => tm.mkTerm .SEQ_CONCAT seqs

def seqConcatN (seqs : Terms)
: (at_least_2 : 1 < seqs.size := by grind) → Env Term := fun _ => do
  runUnsafe fun tm => tm.mkTerm .SEQ_CONCAT seqs

@[inherit_doc mkSeqConcat]
def seqConcat (seq1 seq2 : Term) : Env Term := liftKind% .SEQ_CONCAT seq1 seq2

def seqLength (seq : Term) : Env Term := liftKind% .SEQ_LENGTH seq

/-- Sequence indexing -/
def seqAt (seq idx : Term) : Env Term := liftKind% .SEQ_AT seq idx

/-- Adds an element at the end of a sequence. -/
def seqPush (seq elem : Term) : Env Term := elem.unitSeq >>= seq.seqConcat

def mkSeqValue [ToTyp α] [ValueToTerm α] (elems : Array α) : Env Term := do
  let elems ← elems.mapM mkValue
  if h : 0 < elems.size then mkSeqConcat elems
  else Srt.of α >>= mkEmptySeq

end sequences

section bags
/-- The empty bag for bag-sort `srt`. -/
def mkEmptyBag (srt : Srt) := lift% mkEmptyBag srt

/-- Creates a bag where `elem` maps to `count`. -/
def mkBagWith (elem count : Term) := liftKind% .BAG_MAKE elem count

/-- Creates the term for the count of `elem` in `bag`. -/
def bagCount (bag elem : Term) := liftKind% .BAG_COUNT bag elem

/-- Max-union between bag-terms. -/
def bagUnionMax (bag1 bag2 : Term) := liftKind% .BAG_UNION_MAX bag1 bag2
/-- Disjoint-union between bag-terms. -/
def bagUnionDisjoint (bag1 bag2 : Term) := liftKind% .BAG_UNION_DISJOINT bag1 bag2
/-- Min-intersection between bag-terms. -/
def bagInterMin (bag1 bag2 : Term) := liftKind% .BAG_INTER_MIN bag1 bag2
end bags




/-! ## Operators -/



/-! ### `Bool` operators -/

open Lean open Parser.Command (docComment) in

/-- Creates a `docComment` syntax node from a `String` docstring. -/
public meta def mkDocComment (s : String) : TSyntax ``docComment :=
  Lean.mkNode ``docComment #[mkAtom "/--", mkAtom (s ++ "-/")]

declare_syntax_cat def_2nary_defaults

syntax ", " "(" term ", " term ")" : def_2nary_defaults

local macro
  mods:declModifiers
  "def_2nary% " id:ident " := " kind:term defaults?:optional(def_2nary_defaults)
: command => do
  let (rawId, rawIdN, idN, rawIdN', idN') ← match id.getId with
    | .str base s =>
      let rawIdN := s!"{s}N"
      let rawIdN' := s!"{s}N'"
      pure (
        s,
        rawIdN, Lean.Name.str base rawIdN |> Lean.mkIdent,
        rawIdN', Lean.Name.str base rawIdN' |> Lean.mkIdent,
      )
    | _ => Lean.Macro.throwError ""
  let cmt := Id.run do
    let mut cmt := s!"N-ary version of `{rawId}`, requires at least two elements"
    if defaults?.isSome
    then cmt := s!"{cmt}; see also `{rawIdN'}`."
    else cmt := cmt ++ "."
    mkDocComment cmt
  let termsId := `terms |> mkIdent
  let validId := `atLeastTwoElements |> mkIdent
  let mainDefs ← `(
    $mods:declModifiers
    def $id (t1 t2 : Term) : Env Term := liftKind% $kind t1 t2
    $cmt:docComment
    def $idN ($termsId : Terms)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : Env Term :=
      let _ := $validId
      lift% mkTerm $kind $termsId
  )
  if let some defaults := defaults? then
    match defaults with
    | `(def_2nary_defaults| , ( $on0:term , $on1:term ) ) =>
      let cmt' := mkDocComment
        s!"N-ary version of `{rawId}` with defaults for zero- and one-element arrays; \
        see also `{rawIdN}`."
      `(
        $mainDefs
        $cmt':docComment
        def $idN' (terms : Terms)
          (on0 : Env Term := $on0) (on1 : Term → Env Term := $on1)
        : Env Term :=
          if terms.size = 0 then on0
          else if h : terms.size = 1 then on1 terms[0]
          else lift% mkTerm $kind terms
      )
    | _ => Lean.Macro.throwUnsupported
  else return mainDefs

/-- Binary equality. -/
def_2nary% equal := .EQUAL, (mkBool true, pure)
/-- Binary pairwise inequality. -/
def_2nary% distinct := .DISTINCT

/-- Logical negation. -/
def not (boolTerm : Term) := liftKind% .NOT boolTerm

/-- Binary implication. -/
def_2nary% implies := .IMPLIES
/-- Binary conjunction. -/
def_2nary% and := .AND, (mkBool true, pure)
/-- Binary disjunction. -/
def_2nary% or := .OR, (mkBool false, pure)
/-- Binary exclusive-disjunction. -/
def_2nary% xor := .XOR, (mkBool false, pure)

/-- If-then-else from condition/then-branch/else-branch. -/
def ite (cnd thn els : Term) := liftKind% .ITE cnd thn els
@[inherit_doc ite]
def thenElse := @ite

/-- Binary less-than operator. -/
def_2nary% lt := .LT
/-- Binary less-than-or-equal-to operator. -/
def_2nary% le := .LEQ
/-- Binary greater-than-or-equal-to operator. -/
def_2nary% ge := .GEQ
/-- Binary greater-than operator. -/
def_2nary% gt := .GT



/-! ### Arithmetic operators -/

/-- Arithmetic negation. -/
def neg (arith_term : Term) := liftKind% .NEG arith_term

/-- Binary addition. -/
def_2nary% add := .ADD, (mkInt 0, pure)

/-- Binary subtraction. -/
def_2nary% sub := .SUB

/-- Binary multiplication. -/
def_2nary% mul := .MULT, (mkInt 1, pure)

/-- Binary division over reals, division by `0` undefined, left associative. -/
def_2nary% real_div := .DIVISION
/-- Binary division over reals, division by `0` defined to be `0`, left associative. -/
def_2nary% real_div_total := .DIVISION_TOTAL

/-- Binary division over integers, division by `0` undefined, left associative. -/
def_2nary% int_div := .INTS_DIVISION
/-- Binary division over integers, division by `0` defined to be `0`, left associative. -/
def_2nary% int_div_total := .INTS_DIVISION_TOTAL

/-- Integer modulus, modulus by `0` undefined. -/
def_2nary% mod := .INTS_MODULUS

/-- Integer modulus, modulus by `0` defined to be `0`. -/
def_2nary% mod_total := .INTS_MODULUS_TOTAL

/-- Absolute value over arithmetic terms. -/
def abs (arith_term : Term) := liftKind% .ABS arith_term

/-- Arithmetic power; both terms must have the same sort: either `Int` or `Real`. -/
def pow (term exp : Term) := liftKind% .POW term exp

/-- Exponential over reals. -/
def exp (term : Term) := liftKind% .EXPONENTIAL term



-- /-! ### Array operators -/

/-- The array `a` where `a[i] = if i = idx then elm else array[i]`. -/
def store (array idx elm : Term) := liftKind% .STORE array idx elm

/-- The element associated with `idx` in `array`. -/
def select (array idx : Term) := liftKind% .SELECT array idx



/-! ## String operators -/

def stringConcat (str1 str2 : Term) := liftKind% .STRING_CONCAT str1 str2

def stringConcatN (strings : Terms)
: (at_least_2 : 1 < strings.size := by grind) → Env Term := fun _ => do
  runUnsafe fun tm => tm.mkTerm .STRING_CONCAT strings

def stringLength (str : Term) := liftKind% .STRING_LENGTH str



/-! ## Substitution -/

/-- Term substitution specification. -/
structure Subst where
/-- Creates a `∀ i, terms[i] ↦ replacements[i]` substitution. -/
mk ::
  /-- Terms to replace. -/
  ts : Terms
  /-- Terms to replace `ts` elements by. -/
  rs : Terms
  /-- Proof that they have the same size. -/
  same_size : ts.size = rs.size := by
    (try assumption) <;> (try grind) <;> fail "failed to prove term arrays have the same size"

namespace Subst

/-- A function taking a proof that both term arrays have the same size and producing `β`. -/
abbrev SameSize (ts1 ts2 : Terms) (β : Type) :=
  (same_size : ts1.size = ts2.size :=
    by (try assumption) <;> (try grind) <;> fail "failed to prove term arrays have the same size")
  → β

/-- Creates a `term ↦ replacement` substitution. -/
def mkOne (term : Term) (replacement : Term) : Subst := mk #[term] #[replacement]

/-- The empty substitution. -/
def empty : Subst := {ts := #[], rs := #[], same_size := rfl}

/-- Adds a `term ↦ replacement` substitution. -/
def push (s : Subst) (term : Term) (replacement : Term) : Subst := {s with
  ts := s.ts.push term
  rs := s.rs.push replacement
  same_size := by grind only [!Array.size_push, s.same_size]
}

/-- Augments a substitution with `∀ i, terms[i] ↦ replacements[i]`. -/
def extend (s : Subst)
  (terms : Terms) (replacements : Terms)
: SameSize terms replacements Subst := fun same_size => {s with
  ts := s.ts.append terms
  rs := s.rs.append replacements
  same_size := by
    simp only [Array.append_eq_append, Array.size_append, s.same_size, Nat.add_left_cancel_iff]
    assumption
}

end Subst

@[inherit_doc T.substitute]
def substitute (term : Term) (subst : Subst) : Env Term :=
  runUnsafe' do T.substitute term subst.ts subst.rs



/-! ### Accessors -/

/-- The `Kind` of a term. -/
def getKind (term : Term) : Res Kind := T.getKind term

/-- The sub-terms of a term. -/
def getKids (term : Term) : Array Term := term.getChildren

/-- Size-checked sub-terms of a term. -/
def getSizedKids (term : Term) (size : Nat) : Env {array : Array Term // array.size = size} := do
  let kids := term.getKids
  if h : kids.size = size then return ⟨kids, h⟩ else
    throwUser s!"expected {size} kid(s), got {kids.size} in term `{term}` of kind {term.getKind?}"

@[inherit_doc T.getSort]
def getSort (term : Term) : Env Srt := do
  let srt ← T.getSort term |>.mapError Error.ofUnsafe
  return by unfold Srt ; exact srt


-- /-! ### Value extraction -/

@[inherit_doc T.isBooleanValue]
def isBoolValue (term : Term) : Bool := T.isBooleanValue term
/-- If `term` is a boolean value, produces that value; fails otherwise. -/
def getBoolValue (term : Term) : Res Bool := T.getBooleanValue term |>.mapError Error.ofUnsafe
/-- If `term` is a boolean value, produces that value. -/
def getBoolValue? (term : Term) : Option Bool := T.getBooleanValue? term

@[inherit_doc T.isIntegerValue]
def isIntValue (term : Term) : Bool := T.isIntegerValue term
/-- If `term` is an integer value, produces that value; fails otherwise. -/
def getIntValue (term : Term) : Res Int := T.getIntegerValue term |>.mapError Error.ofUnsafe
/-- If `term` is an integer value, produces that value. -/
def getIntValue? (term : Term) : Option Int := T.getIntegerValue? term

@[inherit_doc T.isRealValue]
def isRealValue (term : Term) : Bool := T.isRealValue term
/-- If `term` is a real value, produces that value as a string; fails otherwise. -/
def getRealValue (term : Term) : Res String := T.getRealValue term |>.mapError Error.ofUnsafe
/-- If `term` is a real value, produces that value as a string. -/
def getRealValue? (term : Term) : Option String := T.getRealValue? term
/-- If `term` is a real value, produces that value as a `Rat`; fails otherwise. -/
def getRatValue (term : Term) : Res Rat := T.getRationalValue term |>.mapError Error.ofUnsafe
/-- If `term` is a real value, produces that value as a `Rat`. -/
def getRatValue? (term : Term) : Option Rat := T.getRationalValue? term

@[inherit_doc T.isStringValue]
def isStringValue (term : Term) : Bool := T.isStringValue term
/-- If `term` is an integer value, produces that value; fails otherwise. -/
def getStringValue (term : Term) : Res String :=
  if term.isStringValue then
    let s := term.toString
    if s.startsWith '"' ∧ s.endsWith '"' then return s.drop 1 |>.dropEnd 1 |>.toString
    else throwUser s!"failed to retrieve string value of term `{s}`"
  else throwUser "cannot extract string-value of of a non-string-value term"
/-- If `term` is an integer value, produces that value. -/
def getStringValue? (term : Term) : Option String := term.getStringValue.toOption

def getRegexValue (term : Term) : Env Regex :=
  throwTodo s!"regex value extraction from a constant term: {term}"

def getRoundingModeValue (term : Term) : Env Float.RoundingMode :=
  throwTodo s!"rounding mode value extraction from a constant term: {term}"

def getSeqValue [A : TermToValue α] (t : Term) : Env (Array α) := do
  let elms ← t.getSequenceValue |>.mapError Error.ofUnsafe
  elms.mapM getValue

def getSeqValueOf (α : Type) [A : TermToValue α] : (t : Term) → Env (Array α) := getSeqValue

def getBitVecValue (t : Term) : Env (BitVec size) := do
  let binRepr ← t.getBitVectorValue 2 |>.mapError Error.ofUnsafe
  let empty : (size : Nat) × BitVec size := ⟨0, BitVec.zero 0⟩
  let ⟨size', bv⟩ ← binRepr.chars.foldM (init := empty) fun
    | ⟨size, bv⟩, '0' => pure ⟨size + 1, bv.concat false⟩
    | ⟨size, bv⟩, '1' => pure ⟨size + 1, bv.concat true⟩
    | _, c => throwInternal
      s!"unexpected character `{c}` in binary representation `{binRepr}` for bitvec term `{t}`"
  if h : size' = size
  then return h ▸ bv
  else throwUser s!"expected bitvector term of size {size}, got size {size'}: {t}"


instance : SrtLike Bool where
  termToValue t := t.getBoolValue
  valueToTerm := mkBool

instance : SrtLike Int where
  termToValue t := t.getIntValue
  valueToTerm := mkInt

instance : ValueToTerm Nat where
  valueToTerm n := mkInt n

instance : SrtLike Rat where
  termToValue t := t.getRatValue
  valueToTerm := mkReal

instance : SrtLike String where
  termToValue t := t.getStringValue
  valueToTerm := mkString

instance : SrtLike Regex where
  termToValue t := t.getRegexValue
  valueToTerm _value := throwTodo s!"value-to-term for `Regex`"

instance : SrtLike Float.RoundingMode where
  termToValue t := t.getRoundingModeValue
  valueToTerm := mkRoundingMode

instance : SrtLike (BitVec size) where
  termToValue t := t.getBitVecValue
  valueToTerm := mkBitVec

section variable [ToTyp α]

instance [TermToValue α] : TermToValue (Array α) := ⟨getSeqValue⟩

instance [ValueToTerm α] : ValueToTerm (Array α) := ⟨mkSeqValue⟩
end
