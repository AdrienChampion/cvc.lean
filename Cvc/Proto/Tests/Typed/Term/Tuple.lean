/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Typed.Term
import Cvc.Proto.Typed.Solver

public meta import Cvc.Proto.Typed.Term
public meta import Cvc.Proto.Typed.Solver



/-! # Tuples, typed -/
namespace Cvc.Proto.Tests.Typed.Term.Tuple

open Cvc
open Cvc.Proto
open Cvc.Proto.Typed



/-! ## The index says what the sort is

A product index flattens to the right, so `α × β × γ` is one three-component tuple. Each line below
prints the sort the term actually has beside the sort its index claims; the two agreeing is the
whole point of the constructor's shape.
-/

/-- info:
pair   : (Tuple Int Bool) / (Tuple Int Bool)
triple : (Tuple Int Bool Real) / (Tuple Int Bool Real)
quad   : (Tuple Int Bool Real Int) / (Tuple Int Bool Real Int)
nested : (Tuple (Tuple Int Bool) Real) / (Tuple (Tuple Int Bool) Real)
-/
#guard_msgs in #eval Env.runIO do
  let one ← Term.mkInt 1
  let tru ← Term.mkTrue
  let half ← Term.mkReal (1/2 : Rat)

  let pair ← Term.mkTuple one (.last tru)
  println! "pair   : {← pair.erase.getSort} / {← (Srt.of (Int × Bool) : Env Srt)}"

  let triple ← Term.mkTuple one (.cons tru (.last half))
  println! "triple : {← triple.erase.getSort} / {← (Srt.of (Int × Bool × Rat) : Env Srt)}"

  let quad ← Term.mkTuple one (.cons tru (.cons half (.last one)))
  println! "quad   : {← quad.erase.getSort} / {← (Srt.of (Int × Bool × Rat × Int) : Env Srt)}"

  -- a tuple *does* nest, to the left, and that index is exact too
  let nested ← Term.mkTuple pair (.last half)
  println! "nested : {← nested.erase.getSort} / {← (Srt.of ((Int × Bool) × Rat) : Env Srt)}"



/-! ## What the last component may be

`cons` takes any component, including a tuple, because a tuple there nests. `last` does not: a
product index would flatten its own components into the tuple being built, while the single term
it stands for would not, and the index would then lie about the sort.
-/

section discipline
variable [Ω] (i : Term Int) (b : Term Bool) (r : Term Rat) (p : Term (Bool × Rat))

/-- Any flat index ends a tuple. -/
example : Env (Term (Int × Bool)) := Term.mkTuple i (.last b)

/-- A container index is flat — only a *product* is not. -/
example (s : Term (Cvc.Proto.Set Int)) : Env (Term (Int × Cvc.Proto.Set Int)) :=
  Term.mkTuple i (.last s)

/-- A function index likewise. -/
example (f : Term (Int → Bool)) : Env (Term (Int × (Int → Bool))) := Term.mkTuple i (.last f)

/-- A tuple is fine anywhere but last, where it nests to the left. -/
example : Env (Term ((Bool × Rat) × Int)) := Term.mkTuple p (.last i)

/-- …and as an inner component. -/
example : Env (Term (Int × (Bool × Rat) × Int)) := Term.mkTuple i (.cons p (.last i))

/-- info: @Term.mkTuple : [inst : Ω] → {α β : Type} → [ToTyp α] → Term α → Term.Components β → Env (Term (α × β)) -/
#guard_msgs in #check @Cvc.Proto.Typed.Term.mkTuple

end discipline

-- and the rejection is a *type* error, not a runtime one: a product cannot end a tuple
/--
error: could not synthesize default value for parameter '_isFlat' using tactics
---
error: a tuple's last component cannot itself be a tuple: its components would flatten into the tuple being built. Nest to the left instead.
inst✝ : Ω
i : Term Int
p : Term (Bool × Rat)
⊢ False
-/
#guard_msgs in
example [Ω] (i : Term Int) (p : Term (Bool × Rat)) : Env (Term (Int × (Bool × Rat))) :=
  Term.mkTuple i (.last p)



/-! ## Projection and values

Both are sort-erased in their result: which components an index array selects is a runtime value,
and a tuple's components have as many indices as it has components.
-/

/-- info:
project : (Tuple Real Int)
isValue : true
values  : #[1, true, (/ 1 2)]
-/
#guard_msgs in #eval Env.runIO do
  let triple ← Term.mkTuple (← Term.mkInt 1) (.cons (← Term.mkTrue) (.last (← Term.mkReal (1/2 : Rat))))
  println! "project : {← (← Term.tupleProject #[2, 0] triple).getSort}"
  println! "isValue : {triple.isTupleValue}"
  println! "values  : {(← triple.getTupleValue).map toString}"



/-! ## End to end -/

/-- info: x = 4 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let x ← s.declareConst Int "x"
  let lft ← Term.mkTuple x (.last (← Term.mkTrue))
  let rgt ← Term.mkTuple (← Term.mkInt 4) (.last (← Term.mkTrue))
  (do Term.equal lft rgt) >>= s.assert

  s.checkSat (ifSat := do println! "x = {← s.getValue x}")
