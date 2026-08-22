/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Untyped.Symbols
import Cvc.Untyped.Core
import Cvc.Untyped.Theory

public meta import Cvc.Untyped.Symbols
public meta import Cvc.Untyped.Core
public meta import Cvc.Untyped.Theory



/-! # Symbols, sort-erased

`structure.symbols` generates the structure the `Symbols` class wants — parameterized by the
`Wrap`, every field wrapped in it — plus the `Idents`/`Terms`/`Values` aliases and the instance.
Everything else a symbol structure can do is generic over the `Sig`, so nothing else is generated.
-/
namespace Cvc.Tests.Untyped.Symbols

open Cvc Untyped

-- `structure.symbols` declares terms, so it needs `Ω` in scope exactly as any other
-- term-mentioning declaration does
variable [Ω]

/-- Symbols for a little state machine. -/
structure.symbols Machine where
  /-- Whether the machine is running. -/
  running : Bool
  /-- How many steps it has taken. -/
  steps : Int

/-! ## What is generated

The structure takes the `Wrap` the user never wrote, and each field's type is wrapped in it.
-/

/-- info: @Machine.running : [inst : Ω] → {W : Symbols.Wrap} → Machine W → W Bool -/
#guard_msgs in #check @Machine.running

/-- The three aliases, at the sorts the fields named. -/
example (i : Machine.Idents) (t : Machine.Terms) (v : Machine.Values)
: String × Untyped.Term × Bool := (i.running, t.running, v.running)

/-! ## What is *not* generated

`declare`, `getValues` and `findCex` are generic over the `Sig`, so the instance is a symbol
structure's whole obligation.
-/

example (idents : Machine.Idents) : Env Machine.Terms := idents.declare
example (syms : Machine.Terms) (s : Solver) : Env (Option Machine.Values) := syms.findCex s

/-! ## A symbol is named after its field -/

/-- info: running: running, steps: steps -/
#guard_msgs in #eval Env.runIO do
  let i : Machine.Idents := Symbols.Sig.idents ()
  println! "running: {i.running}, steps: {i.steps}"

/-! ## End to end -/

/-- info: running = true, steps = 3 -/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let syms ← (Symbols.Sig.idents () : Machine.Idents).declareIn s
  (← Term.equal syms.steps (← Term.mkInt 3)) |> s.assert
  s.assert syms.running
  match ← syms.findCex s with
  | some v => println! "running = {v.running}, steps = {v.steps}"
  | none => println! "no model"

/-! ## `symbols` is not a keyword

The command's leading token is `structure.symbols`, so an ordinary identifier of that name is
unaffected — which matters, since the hand-written examples bind one.
-/

example (symbols : Nat) : Nat := symbols
