/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto2.Untyped.Term.Fun
import Cvc.Proto2.Untyped.Term.Arith
import Cvc.Proto2.Untyped.Term.Bool
import Cvc.Proto2.Untyped.Solver

public meta import Cvc.Proto2.Untyped.Term.Fun
public meta import Cvc.Proto2.Untyped.Term.Arith
public meta import Cvc.Proto2.Untyped.Term.Bool
public meta import Cvc.Proto2.Untyped.Solver



/-! # Generated function-application constructors, sort-erased

Construction is checked against the SMT-LIB cvc5 prints, and then end to end: an uninterpreted
function is declared, constrained, and its value read back out of a model. Getting the sort wrong
would be caught by the solver rather than by the term builder, so both halves matter.
-/
namespace Cvc.Proto2.Tests.Untyped.Term.Fun

open Cvc Cvc.Proto2
open Cvc.Proto2.Untyped.Term

/-- info:
apply           : (f i)
apply2          : (g i b)
apply3          : (h i b r)
applyHo         : (@ f i)
applyHo partial : (@ g i)
applyHo chained : (@ (@ g i) b)
higher-order    : (hof f)
-/
#guard_msgs in #eval Env.runIO do
  let f ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Bool) "f"
  let g ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Bool → Rat) "g"
  let h ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Bool → Rat → Int) "h"
  let hof ← Cvc.Proto2.Untyped.Term.mkSymbolAs ((Int → Bool) → Rat) "hof"
  let i ← Cvc.Proto2.Untyped.Term.mkSymbolAs Int "i"
  let b ← Cvc.Proto2.Untyped.Term.mkSymbolAs Bool "b"
  let r ← Cvc.Proto2.Untyped.Term.mkSymbolAs Rat "r"

  println! "apply           : {← apply f i}"
  println! "apply2          : {← apply2 g i b}"
  println! "apply3          : {← apply3 h i b r}"
  println! "applyHo         : {← applyHo f i}"
  println! "applyHo partial : {← applyHo g i}"
  println! "applyHo chained : {← applyHo (← applyHo g i) b}"
  println! "higher-order    : {← apply hof f}"



/-! ## End to end -/

/-- info: f(1) = 2 -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Proto2.Untyped.Solver.new
  solver.setOption "produce-models" "true"

  let f ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let one ← Cvc.Proto2.Untyped.Term.mkInt 1
  let two ← Cvc.Proto2.Untyped.Term.mkInt 2
  let three ← Cvc.Proto2.Untyped.Term.mkInt 3

  let fOne ← apply f one
  let fTwo ← apply f two
  equal fOne two >>= solver.assert
  equal fTwo three >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue fOne)
  println! "f(1) = {value}"

/-- info: g(1, 2) = 5 -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Proto2.Untyped.Solver.new
  solver.setOption "produce-models" "true"

  let g ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Int → Int) "g"
  let one ← Cvc.Proto2.Untyped.Term.mkInt 1
  let two ← Cvc.Proto2.Untyped.Term.mkInt 2
  let five ← Cvc.Proto2.Untyped.Term.mkInt 5

  let g12 ← apply2 g one two
  equal g12 five >>= solver.assert

  let value ← solver.checkSat (ifSat := solver.getValue g12)
  println! "g(1, 2) = {value}"

-- a function is a function: the same argument cannot map to two values
/-- info: f(x) = 1 ∧ f(x) = 2 → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Proto2.Untyped.Solver.new

  let f ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Proto2.Untyped.Term.mkSymbolAs Int "x"
  let one ← Cvc.Proto2.Untyped.Term.mkInt 1
  let two ← Cvc.Proto2.Untyped.Term.mkInt 2

  let fx ← apply f x
  equal fx one >>= solver.assert
  equal fx two >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "f(x) = 1 ∧ f(x) = 2 → {result}"

-- congruence: equal arguments give equal results, so this is unsat
/-- info: x = y ∧ f(x) ≠ f(y) → unsat -/
#guard_msgs in #eval Env.runIO do
  let solver ← Cvc.Proto2.Untyped.Solver.new

  let f ← Cvc.Proto2.Untyped.Term.mkSymbolAs (Int → Int) "f"
  let x ← Cvc.Proto2.Untyped.Term.mkSymbolAs Int "x"
  let y ← Cvc.Proto2.Untyped.Term.mkSymbolAs Int "y"

  equal x y >>= solver.assert
  (do distinct (← apply f x) (← apply f y)) >>= solver.assert

  let result ← solver.checkSat (ifSat := return "sat") (ifUnsat := return "unsat")
  println! "x = y ∧ f(x) ≠ f(y) → {result}"
