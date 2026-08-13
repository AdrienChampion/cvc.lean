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

public import Cvc.Proto2.Types.FiniteField
public import Cvc.Proto2.Untyped.Term.FiniteField
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Ext
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.FiniteField



/-! # Generated FiniteField constructors, typed -/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.FiniteField



/-! ## Values -/

@[inherit_doc T.isFiniteFieldValue]
def isFiniteFieldValue (term : Term (Cvc.Proto2.FiniteField size)) : Bool :=
  T.isFiniteFieldValue term

@[inherit_doc T.getFiniteFieldRepr]
def getFiniteFieldRepr (term : Term (Cvc.Proto2.FiniteField size)) : Res Int :=
  T.getFiniteFieldRepr term


/-- The term denoting an element of a finite field. -/
def mkFiniteFieldValue
: (elem : Cvc.Proto2.FiniteField size) → Env (Term (Cvc.Proto2.FiniteField size)) :=
  T.FiniteField.toTerm

/-- The finite-field element a constant term denotes. -/
def getFiniteFieldValue
: Term (Cvc.Proto2.FiniteField size) → Env (Cvc.Proto2.FiniteField size) := T.FiniteField.ofTerm

instance : SrtLike (Cvc.Proto2.FiniteField size) where
  valueToTerm := mkFiniteFieldValue
  termToValue := getFiniteFieldValue
