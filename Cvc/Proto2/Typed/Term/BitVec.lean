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

public import Cvc.Proto2.Untyped.Term.BitVec
public import Cvc.Proto2.Typed.Term.Defs
public import Cvc.Proto2.Typed.Term.Value
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.BitVec



/-! # Generated bit-vector constructors, typed

`bvConcat` is the entry whose result index is computed from its arguments': its Lean signature is
`Term (BitVec n) → Term (BitVec m) → Env (Term (BitVec (n + m)))`, matching `BitVec.append`.
-/
namespace Cvc.Proto2.Typed.Term public section

open Cvc.Proto2 renaming Untyped.Term → T

variable [Ω]

gen_typed% from Cvc.Proto2.Spec.BitVec



/-! ## Values -/

@[inherit_doc T.isBitVecValue]
def isBitVecValue (term : Term (BitVec size)) : Bool := T.isBitVecValue term


@[inherit_doc T.getBitVecValue]
def getBitVecValue (term : Term (BitVec size)) : Env (BitVec size) := T.getBitVecValue term

instance : SrtLike (BitVec size) where
  valueToTerm bv := mkBitVec size bv.toNat.toUInt64
  termToValue := getBitVecValue
