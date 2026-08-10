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

public import Cvc.Proto.Untyped.Term.BitVec
public import Cvc.Proto.Typed.Term.Defs
public import Cvc.Proto.Typed.Term.Value
public import Cvc.Proto.Gen
public import Cvc.Proto.Spec.BitVec



/-! # Generated bit-vector constructors, typed

`bvConcat` is the entry whose result index is computed from its arguments': its Lean signature is
`Term (BitVec n) → Term (BitVec m) → Env (Term (BitVec (n + m)))`, matching `BitVec.append`.
-/
namespace Cvc.Proto.Typed.Term public section

open Cvc.Proto renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto.Spec.BitVec



/-! ## Values -/

@[inherit_doc T.isBitVecValue]
def isBitVecValue (term : Term (BitVec size)) : Bool := T.isBitVecValue term


@[inherit_doc T.getBitVecValue]
def getBitVecValue (term : Term (BitVec size)) : Env (BitVec size) := T.getBitVecValue term

instance : SrtLike (BitVec size) where
  valueToTerm bv := mkBitVec size bv.toNat.toUInt64
  termToValue := getBitVecValue
