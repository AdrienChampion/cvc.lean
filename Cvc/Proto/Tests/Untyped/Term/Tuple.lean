/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Untyped.Term
import Cvc.Proto.Untyped.Solver

public meta import Cvc.Proto.Untyped.Term
public meta import Cvc.Proto.Untyped.Solver



/-! # Tuples, sort-erased -/
namespace Cvc.Proto.Tests.Untyped.Term.Tuple

open Cvc
open Cvc.Proto.Untyped



/-! ## Construction -/

/-- info:
pair   : (tuple 1 true)
sort   : (Tuple Int Bool)
triple : (tuple 1 true (/ 1 2))
sort   : (Tuple Int Bool Real)
nested : (tuple (tuple 1 true) (/ 1 2))
sort   : (Tuple (Tuple Int Bool) Real)
-/
#guard_msgs in #eval Env.runIO do
  let one ← Term.mkInt 1
  let tru ← Term.mkTrue
  let half ← Term.mkReal (1/2 : Rat)

  let pair ← Term.mkTuple #[one, tru]
  println! "pair   : {pair}"
  println! "sort   : {← pair.getSort}"

  let triple ← Term.mkTuple #[one, tru, half]
  println! "triple : {triple}"
  println! "sort   : {← triple.getSort}"

  -- a tuple is an ordinary term, so it nests as a component
  let nested ← Term.mkTuple #[pair, half]
  println! "nested : {nested}"
  println! "sort   : {← nested.getSort}"



/-! ## Projection

`tupleProject` answers a *tuple*, not a component: projecting one index gives a one-component
tuple. It reorders and duplicates as readily as it selects.
-/

/-- info:
[0]     : ((_ tuple.project 0) (tuple 1 true (/ 1 2))) : (Tuple Int)
[2, 0]  : ((_ tuple.project 2 0) (tuple 1 true (/ 1 2))) : (Tuple Real Int)
[1, 1]  : ((_ tuple.project 1 1) (tuple 1 true (/ 1 2))) : (Tuple Bool Bool)
[]      : (tuple.project (tuple 1 true (/ 1 2))) : UnitTuple
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  let show! (indices : Array Nat) (label : String) : Env Unit := do
    let projected ← Term.tupleProject indices triple
    println! "{label}: {projected} : {← projected.getSort}"
  show! #[0] "[0]     "
  show! #[2, 0] "[2, 0]  "
  show! #[1, 1] "[1, 1]  "
  -- projecting nothing is legal: the zero-component tuple
  show! #[] "[]      "



/-! ## Values -/

/-- info:
isTupleValue : true
components   : #[1, true, (/ 1 2)]
not a value  : false
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple #[← Term.mkInt 1, ← Term.mkTrue, ← Term.mkReal (1/2 : Rat)]
  println! "isTupleValue : {triple.isTupleValue}"
  println! "components   : {(← triple.getTupleValue).map toString}"

  -- a tuple over a symbol is tuple-sorted but is not a *value*
  let symbolic ← Term.mkTuple #[← Term.mkSymbol (← Srt.int) "x", ← Term.mkTrue]
  println! "not a value  : {symbolic.isTupleValue}"



/-! ## End to end

A tuple equality constrains the components, so the solver answers about them.
-/

/-- info: x = 4 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst "x" (← Srt.int)
  let lft ← Term.mkTuple #[x, ← Term.mkTrue]
  let rgt ← Term.mkTuple #[← Term.mkInt 4, ← Term.mkTrue]
  (do Term.equal lft rgt) >>= s.assert

  s.checkSat (ifSat := do println! "x = {← s.getValueAs Int x}")
