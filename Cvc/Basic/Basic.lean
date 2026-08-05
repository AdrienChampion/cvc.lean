/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import cvc5



/-! # Basic helpers -/
namespace Cvc public section

export cvc5 (Kind SortKind)



/-- The constant combinator. -/
abbrev 𝕂 (val : α) (_ : β) : α := val



/-- Lazy string interpolation: `fun () => s!<interp>`. -/
macro:max "ls!" str:interpolatedStr(term) : term
  => `( (fun () => s!$str : Unit → String)  )



/-- Bit vector base. -/
inductive BitVec.Base
| bin | dec | hex
deriving DecidableEq, Hashable, Ord

namespace BitVec.Base

protected def default : Base := .bin
instance : Inhabited Base := ⟨Base.default⟩

def toUInt32 : Base → UInt32
| bin => 2
| dec => 10
| hex => 16

protected def toString : Base → String
  | bin => "0b"
  | dec => ""
  | hex => "0x"

instance : ToString Base := ⟨Base.toString⟩

end BitVec.Base



structure AtLeast (n : Nat) (α : Type) : Type where private privateMk ::
  private data : Array α
  private h_size : n ≤ data.size

namespace AtLeast

def mk (array : Array α) (h_size : n ≤ array.size := by grind) : AtLeast n α := ⟨array, h_size⟩

def toArray (a : AtLeast n α) : {a : Array α // n ≤ a.size} := ⟨a.data, a.h_size⟩

end AtLeast

inductive AtLeast' (n : Nat) (α : Type) : Type
| mk (array : Array α) (h_size : n ≤ array.size)

namespace AtLeast'

def toArray : (a : AtLeast' n α) → {a : Array α // n ≤ a.size}
| mk array h_size => ⟨array, h_size⟩

end AtLeast'



/-- A check-sat result.-/
inductive CheckSat
/-- Formulas asserted are satisfiable, *i.e.* a model exists. -/
| sat
/-- Formulas are unsatisfiable, no assignment of the symbols makes them true. -/
| unsat
/-- Solver returned unknown. -/
| unknown (desc : String)
/-- Solver returned some unexpected, non-error result. -/
| other (desc : String)

namespace CheckSat

/-- Conversion to a simple *is sat?* flag, `none` on unknown/unexpected results. -/
def isSat? : CheckSat → Option Bool
| sat => true
| unsat => false
| unknown _ | other _ => none

/-- True iff the result is sat. -/
def isSat (res : CheckSat) : Bool := res.isSat?.getD false

/-- Conversion to a simple *is unsat?* flag, `none` on unknown/unexpected results. -/
def isUnsat? (cs : CheckSat) : Option Bool :=
  Bool.not <$> cs.isSat?

/-- True iff the result is sat. -/
def isUnsat (res : CheckSat) : Bool := res.isUnsat?.getD false

/-- Conversion from a `cvc5` result. -/
private def ofUnsafe (result : cvc5.Result) : CheckSat :=
  if result.isSat then .sat
  else if result.isUnsat then .unsat
  else if let some unkTxt := result.getUnknownExplanation? then .unknown unkTxt.toString
  else .other s!"could not extract any information from cvc5 result"

/-- String representation. -/
protected def toString : CheckSat → String
| sat => "sat"
| unsat => "unsat"
| unknown msg => s!"unknown[{msg}]"
| other msg => s!"?[{msg}]?"

instance : ToString CheckSat := ⟨CheckSat.toString⟩

end CheckSat
