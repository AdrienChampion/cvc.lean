/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Typed.Symbols
import Cvc.Typed.Core
import Cvc.Typed.Theory

public meta import Cvc.Typed.Symbols
public meta import Cvc.Typed.Core
public meta import Cvc.Typed.Theory



/-! # Symbols, typed

The same command as the sort-erased layer, selected by which layer is open. What differs is the
index every symbol carries — `Terms` holds a `Term α` per field rather than a sort-erased one — and
the two extra aliases this layer's `Sig` has, `Fun` and `Pred`.
-/
namespace Cvc.Tests.Typed.Symbols

open Cvc Typed

variable [Ω]

/-- Symbols for a little state machine. -/
structure.symbols Machine where
  /-- Whether the machine is running. -/
  running : Bool
  /-- How many steps it has taken. -/
  steps : Int

/-! ## What is generated -/

/-- info: @Machine.running : {W : Symbols.Wrap} → Machine W → W Bool -/
#guard_msgs in #check @Machine.running

/-- Each alias at its field's own index — this is what the typed layer buys, and the reason
`Terms` is not interchangeable with the sort-erased one. -/
example (i : Machine.Idents) (t : Machine.Terms) (v : Machine.Values)
: String × Term Bool × Term Int × Bool × Int :=
  (i.running, t.running, t.steps, v.running, v.steps)

/-- The two aliases only this layer has. -/
example (_f : Machine.Fun Int) (_p : Machine.Pred) : Nat := 0

/-! ## What is not generated -/

example (idents : Machine.Idents) : Env Machine.Terms := idents.declare
example (syms : Machine.Terms) (s : Solver) : Env (Option Machine.Values) := syms.findCex s

/-! ## End to end

A symbol's term carries its index, so it is an operand of that index's operators with nothing
ascribed and nothing re-typed.
-/

/-- info: running = true, steps = 3 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declareIn s
  (← smt! ![pure syms.steps] = 3) |> s.assert
  s.assert syms.running
  match ← syms.findCex s with
  | some v => println! "running = {v.running}, steps = {v.steps}"
  | none => println! "no model"
