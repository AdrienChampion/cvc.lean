/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Proto.Untyped.Term.Defs
import all Cvc.Proto.Typed.Term.Defs

public import Cvc.Proto.Types.FiniteField
public import Cvc.Proto.Untyped.Term.FiniteField
public import Cvc.Proto.Typed.Term.Defs
public import Cvc.Proto.Ext
public import Cvc.Proto.Typed.Term.Value
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.FiniteField



/-! # Generated FiniteField constructors, typed -/
namespace Cvc.Proto.Typed.Term public section

open Cvc.Proto renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto.Spec.FiniteField



/-! ## Values -/

@[inherit_doc T.isFiniteFieldValue]
def isFiniteFieldValue (term : Term (Cvc.Proto.FiniteField size)) : Bool :=
  T.isFiniteFieldValue term

@[inherit_doc T.getFiniteFieldRepr]
def getFiniteFieldRepr (term : Term (Cvc.Proto.FiniteField size)) : Res Int :=
  T.getFiniteFieldRepr term


/-- The term denoting an element of a finite field. -/
def mkFiniteFieldValue
: (elem : Cvc.Proto.FiniteField size) → Env (Term (Cvc.Proto.FiniteField size)) :=
  T.FiniteField.toTerm

/-- The finite-field element a constant term denotes. -/
def getFiniteFieldValue
: Term (Cvc.Proto.FiniteField size) → Env (Cvc.Proto.FiniteField size) := T.FiniteField.ofTerm

instance : SrtLike (Cvc.Proto.FiniteField size) where
  valueToTerm := mkFiniteFieldValue
  termToValue := getFiniteFieldValue
