/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Basic.Env
import all Cvc.Proto.Srt
import all Cvc.Proto.Untyped.Term.Defs

public import Cvc.Proto.Srt
public import Cvc.Proto.Types.Tuple
public import Cvc.Proto.Untyped.Term.Value



/-! # Tuples, sort-erased

A tuple is an SMT datatype with one constructor, so cvc5 builds one with a term-manager method
rather than a kind, and its components come back out of a *value* rather than off an arbitrary
term.

`tupleProject` is the one operator, and it answers a **tuple**: projecting a single index gives a
one-component tuple, not that component. Reading a component off a symbolic tuple needs the
datatype selector, which this layer does not wrap yet.
-/
namespace Cvc.Proto.Untyped.Term public section variable [Ω]

open cvc5 renaming Term → T



/-- The tuple whose components are the given terms, in order. -/
def mkTuple (terms : Terms) : Env Term :=
  Cvc.runUnsafe fun tm => tm.mkTuple terms

/-- The tuple of the components at the given indices, in the order given.

Indices count from zero. They need be neither increasing nor distinct, so this reorders and
duplicates as well as it selects: projecting `#[2, 0]` out of `(Tuple Int Bool Real)` gives
`(Tuple Real Int)`.
-/
def tupleProject (indices : Array Nat) (tuple : Term) : Env Term :=
  Cvc.runUnsafe fun tm => do
    tm.mkTermOfOp (← tm.mkOpOfIndices .TUPLE_PROJECT indices) #[tuple]



/-! ## Values -/

@[inherit_doc T.isTupleValue]
def isTupleValue (term : Term) : Bool := T.isTupleValue term.toUnsafe

/-- The components a constant tuple term denotes, failing if it denotes none. -/
def getTupleValue (term : Term) : Res Terms := do
  let components : Terms ← T.getTupleValue term.toUnsafe |>.mapError Error.ofUnsafe
  return components
