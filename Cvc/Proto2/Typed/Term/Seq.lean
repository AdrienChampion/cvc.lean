/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Env
import all Cvc.Proto2.Untyped.Term.Defs
import all Cvc.Proto2.Typed.Term.Defs

public import Cvc.Proto2.Untyped.Term.Seq
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Seq



/-! # Generated Seq constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.Seq



/-! ## Values -/

@[inherit_doc T.isSeqValue]
def isSeqValue (term : Term (Array α)) : Bool := T.isSeqValue term


/-- The elements a constant sequence term denotes. -/
def getSeqValue [TermToValue α] (term : Term (Array α)) : Env (Array α) :=
  have := TermToValue.toUntyped (α := α)
  T.getSeqValue term

@[inherit_doc getSeqValue]
def getSeqValueOf (α : Type) [TermToValue α] : (term : Term (Array α)) → Env (Array α) :=
  getSeqValue

/-- The sequence term denoting an array of values. -/
def mkSeqValue [ToTyp α] [ValueToTerm α] : (elems : Array α) → Env (Term (Array α)) :=
  have := ValueToTerm.toUntyped (α := α)
  T.mkSeqValue

instance [ToTyp α] [ValueToTerm α] : ValueToTerm (Array α) := ⟨mkSeqValue⟩
instance [TermToValue α] : TermToValue (Array α) := ⟨getSeqValue⟩
