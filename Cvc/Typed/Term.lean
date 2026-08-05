module

import all Cvc.Basic.Env
import all Cvc.Untyped.Term
import all Cvc.Typed.Defs

public import Cvc.Typed.Defs
public import Cvc.Untyped.Term



namespace Cvc.Typed public section variable [Ω]

open Cvc renaming Untyped.Term → T, Untyped.Terms → Ts



macro
  "def% " id:ident sig:optDeclSig " := " body:term
: command => do
  let fnId := ``T |>.append id.getId |> Lean.mkIdent
  `(@[inherit_doc $fnId] def $id $sig := $body)

macro
  "def% " id:ident sig:optDeclSig " ← " expl?:("@")? fnId:ident
: command => do
  let fnId := ``T |>.append fnId.getId |> Lean.mkIdent
  let fnTerm ← if expl?.isSome then `(@ $fnId _) else pure fnId
  `(@[inherit_doc $fnId] def $id $sig := $fnTerm)
macro
  "def% " expl?:("@")? id:ident sig:optDeclSig
: command => do
  if expl?.isSome then `(def% $id:ident $sig:optDeclSig ← @ $id)
  else `(def% $id:ident $sig:optDeclSig ← $id)



namespace Term

/-- Creates a value term. -/
def mkValue [A : ValueToTerm α] : (value : α) → Env (Term α) := A.valueToTerm

/-- Retrieves the value of a term. -/
def getValue [A : TermToValue α] : Term α → Env α := A.termToValue

@[inherit_doc getValue]
def getValueAs (α : Type) [A : TermToValue α] : Term α → Env α := getValue

/-- This term's sort. -/
def getSort [ToTyp α] (term : Term α) : Env Srt := do
  let srt' ← T.getSort term
  let srt ← Srt.of α
  if ¬ srt.beq srt' then throwInternal s!"expected sort {srt}, got {srt'} in term {term}"
  return srt

section variable [A : ToTyp α] [B : ToTyp β]

def% mkSymbol (symbol : String) : Env (Term α) := Srt.of α >>= T.mkSymbol symbol

@[inherit_doc mkSymbol]
def mkSymbolAs (α : Type) [ToTyp α] : (symbol : String) → Env (Term α) := mkSymbol

def% mkVar (symbol : String) : Env (Term α) := Srt.of α >>= T.mkVar symbol



/-! ## Substitution -/
section open Cvc.Untyped.Term renaming Subst → S

/-- `Srt`-preserving substitution specification. -/
structure Subst extends toUntyped : S where private ofUntyped ::

namespace Subst

@[inherit_doc S.SameSize]
abbrev SameSize (ts1 ts2 : Terms α) (β : Type) :=
  (same_size : ts1.size = ts2.size :=
    by (try assumption) <;> (try grind) <;> fail "failed to prove term arrays have the same size")
  → β

@[inherit_doc S.mk]
def mk (terms : Terms α) (replacements : Terms α) : SameSize terms replacements Subst :=
  (ofUntyped <| S.mk terms replacements ·)

@[inherit_doc S.mkOne]
def mkOne (term : Term α) (replacement : Term α) : Subst := ofUntyped <| S.mkOne term replacement

@[inherit_doc S.empty]
def empty : Subst := ofUntyped S.empty

@[inherit_doc S.push]
def push (s : Subst) (term : Term α) (replacement : Term α) : Subst :=
  S.push s.toUntyped term replacement |> ofUntyped

@[inherit_doc S.extend]
def extend (s : Subst) (terms : Terms α) (replacements : Terms α)
: SameSize terms replacements Subst :=
  (ofUntyped <| s.toUntyped.extend terms replacements ·)

end Subst

end

@[inherit_doc T.substitute]
def substitute (term : Term α) (subst : Subst) : Env (Term α) := T.substitute term subst.toUntyped



/-! ## Polymorphic -/

section poly

def% equal : (lft rgt : Term α) → Env (Term Bool)
def% @ equalN :
  (terms : Terms α)
  → (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
  → Env (Term Bool)
def% equalN' : (terms : Terms α) → Env (Term Bool)

def ite (cnd : Term Bool) (thn els : Term α) : Env (Term α) := T.ite cnd thn els

end poly



/-! ## Bool -/

section bool

def not (t : Term Bool) : Env (Term Bool) := T.not t

def and (lft rgt : Term Bool) : Env (Term Bool) := T.and lft rgt
def andN (terms : Terms Bool)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.andN terms (atLeastTwoElements := atLeastTwoElements)
def andN' (terms : Terms Bool) : Env (Term Bool) := T.andN' terms

def or (lft rgt : Term Bool) : Env (Term Bool) := T.or lft rgt
def orN (terms : Terms Bool)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.orN terms (atLeastTwoElements := atLeastTwoElements)
def orN' (terms : Terms Bool) : Env (Term Bool) := T.orN' terms

end bool



/-! ## Arithmetic -/

section variable [IsArith α]

def neg (t : Term Int) : Env (Term Int) := T.neg t

def lt (lft rgt : Term α) : Env (Term Bool) := T.lt lft rgt
def ltN (terms : Terms α)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.ltN terms (atLeastTwoElements := atLeastTwoElements)
def le (lft rgt : Term α) : Env (Term Bool) := T.le lft rgt
def leN (terms : Terms α)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.leN terms (atLeastTwoElements := atLeastTwoElements)
def gt (lft rgt : Term α) : Env (Term Bool) := T.gt lft rgt
def gtN (terms : Terms α)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.gtN terms (atLeastTwoElements := atLeastTwoElements)
def ge (lft rgt : Term α) : Env (Term Bool) := T.ge lft rgt
def geN (terms : Terms α)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term Bool) :=
  T.geN terms (atLeastTwoElements := atLeastTwoElements)

def add (lft rgt : Term α) : Env (Term α) := T.add lft rgt
def addN (terms : Terms α)
  (atLeastTwoElements : 1 < terms.size := by
    (try grind) <;> fail "failed to prove term array has at least two elements")
: Env (Term α) :=
  T.addN terms (atLeastTwoElements := atLeastTwoElements)
def addN' (terms : Terms α) : Env (Term α) := T.addN' terms

end



/-! ## Concat-enable -/
section variable [inst : HasConcat α]

def concatN (terms : Terms α) (at_least_two : 1 < terms.size := by grind) : Env (Term α) := do
  let valid := inst.valid_typ
  let h_typ := Typ.typs_of_hasConcat valid
  by
    simp [Typ.hasConcat] at valid
    cases h : ToTyp.typ α <;> try (
      rw [h] at h_typ
      revert h_typ
      simp
      grind only
    )
    case string => exact Untyped.Term.stringConcatN terms at_least_two
    case seq _ => exact Untyped.Term.seqConcatN terms at_least_two

def concat (lft rgt : Term α) : Env (Term α) := concatN #[lft, rgt]

end



def mkBool : Bool → Env (Term Bool) := T.mkValue
def getBoolValue : Term Bool → Env Bool := T.getValue

instance : SrtLike Bool where valueToTerm := mkBool ; termToValue := getBoolValue

def mkInt : Int → Env (Term Int) := T.mkValue
def getIntValue : Term Int → Env Int := T.getValue

instance : SrtLike Int where valueToTerm := mkInt ; termToValue := getIntValue

def mkRat : Rat → Env (Term Rat) := T.mkValue
def getRatValue : Term Rat → Env Rat := T.getValue

instance : SrtLike Rat where valueToTerm := mkRat ; termToValue := getRatValue

def mkString : String → Env (Term String) := T.mkValue
def getStringValue : Term String → Env String := T.getValue

instance : SrtLike String where valueToTerm := mkString ; termToValue := getStringValue

def mkRegex : Regex → Env (Term Regex) := T.mkValue
def getRegexValue : Term Regex → Env Regex := T.getValue

instance : SrtLike Regex where valueToTerm := mkRegex ; termToValue := getRegexValue

def mkRoundingMode : Float.RoundingMode → Env (Term Float.RoundingMode) := T.mkValue
def getRoundingModeValue : Term Float.RoundingMode → Env Float.RoundingMode := T.getValue

instance : SrtLike Float.RoundingMode where
  valueToTerm := mkRoundingMode
  termToValue := getRoundingModeValue

def mkBitVec : (BitVec size) → Env (Term (BitVec size)) := T.mkValue
def getBitVecValue : Term (BitVec size) → Env (BitVec size) := T.getValue

instance : SrtLike (BitVec size) where valueToTerm := mkBitVec ; termToValue := getBitVecValue



/-! ## Sequences -/
section sequences

protected abbrev Seq (α : Type) := Term (Array α)

def mkSeq [ToTyp α] [A : ValueToTerm α] : (seq : Array α) → Env (Term.Seq α) :=
  have : Untyped.ValueToTerm α := ⟨A.valueToTerm⟩
  T.mkValue

def getSeqValue [A : TermToValue α] : Term.Seq α → Env (Array α) :=
  have : Untyped.TermToValue α := ⟨A.termToValue⟩
  T.getValue

instance [ToTyp α] [ValueToTerm α] : ValueToTerm (Array α) := ⟨mkSeq⟩
instance [TermToValue α] : TermToValue (Array α) := ⟨getSeqValue⟩

def mkEmptySeq [A : ToTyp α] : Env (Term.Seq α) :=
  Srt.of α >>= T.mkEmptySeq

def mkEmptySeq' (α : Type) [A : ToTyp α] : Env (Term.Seq α) := mkEmptySeq

def unitSeq (elem : Term α) : Env (Term.Seq α) :=
  T.unitSeq elem

def unitSeqOfValue [ToTyp α] [A : ValueToTerm α] (elem : α) : Env (Term.Seq α) :=
  mkValue elem >>= unitSeq

def mkSeqConcat (seqs : Terms (Array α)) (nempty : 0 < seqs.size := by grind) : Env (Term α) :=
  T.mkSeqConcat seqs nempty

def seqConcat (seq1 seq2 : Term.Seq α) : Env (Term.Seq α) := T.seqConcat seq1 seq2

def seqPush [ToTyp α] (seq : Term.Seq α) (elem : Term α) : Env (Term.Seq α) :=
  T.seqPush seq elem

def seqPushValue [ToTyp α] [A : ValueToTerm α] (seq : Term.Seq α) (elem : α) : Env (Term α) :=
  mkValue elem >>= seq.seqPush

@[inherit_doc T.seqAt]
def seqAt [ToTyp α] (seq : Term.Seq α) (idx : Term Int) : Env (Term.Seq α) :=
  T.seqAt seq idx

end sequences
