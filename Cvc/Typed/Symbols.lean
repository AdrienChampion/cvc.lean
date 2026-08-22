/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Cvc.Gen.Symbols
public import Cvc.Untyped.Symbols
public import Cvc.Typed.Theory.Arith
public import Cvc.Typed.Solver

import all Cvc.Typed.Core.Defs



namespace Cvc.Typed public section

namespace Symbols

abbrev Wrap : Type 1 := (α : Type) → [ToTyp α] → [TermToValue α] → Type

abbrev Sig : Type 1 := Wrap → Type

namespace Sig variable (sig : Sig)

abbrev Idents : Type := sig (fun _α => String)

abbrev Terms [Ω] : Type := sig (Typed.Term ·)

abbrev Values : Type := sig (fun α => α)

abbrev Fun (α : Type) : Type := [Ω] → sig.Terms → Env (Term α)

abbrev Pred : Type := [Ω] → sig.Fun Bool

end Sig

end Symbols

class Symbols (S : Symbols.Sig) where
  InitData : Type := Unit
  idents : InitData → S.Idents
  mapM {W W' : Symbols.Wrap} [Monad m]
    (s : S W) (f : {α : Type} → [ToTyp α] → [TermToValue α] → W α → m (W' α)) : m (S W')

section variable {S : Symbols.Sig} [inst : Symbols S]

namespace Symbols

abbrev Idents [Symbols S] := Sig.Idents S
abbrev Terms [Ω] [Symbols S] := Sig.Terms S
abbrev Values [Symbols S] := Sig.Values S
abbrev Fun [Symbols S] := Sig.Fun S
abbrev Pred [Symbols S] := Sig.Pred S

namespace Sig
abbrev idents : inst.InitData → S.Idents := inst.idents
abbrev Idents.get := @Sig.idents

abbrev mapM := @inst.mapM

def Idents.declareIn [Ω] (idents : S.Idents) (solver : Solver) : Env S.Terms :=
  S.mapM idents solver.declareFun

def Idents.declare [Ω] (idents : S.Idents) : Env S.Terms :=
  S.mapM idents Term.mkSymbol

def Terms.getValues [Ω] (terms : S.Terms) (solver : Solver) : solver.EnvSat S.Values :=
  S.mapM terms solver.getValue

/-- Checks satisfiability and, where sat, reads every symbol's value out of the model.

Needs no per-`Sig` code: `mapM` is what makes it generic, so a user's symbol structure gets this
by instancing `Symbols` and nothing else.
-/
def Terms.findCex [Ω] (terms : S.Terms) (solver : Solver)
  (assuming : Option (Typed.Terms Bool) := none)
: Env (Option S.Values) :=
  solver.checkSat? assuming (ifSat := terms.getValues solver)

end Sig

end Symbols

def declareSymbols := @Symbols.Sig.Idents.declare

namespace Solver

def declareSymbols := @Symbols.Sig.Idents.declareIn

def getSymbolValues := @Symbols.Sig.Terms.getValues

end Solver



/-! ## The `symbols structure` command

Declared `scoped`, so `open Cvc.Typed` selects the typed spelling. It is the sort-erased command
with this layer's two extra aliases: `Fun`, which a typed `Sig` parameterizes by its codomain, and
`Pred`, which is `Fun Bool`.
-/

open Lean Elab Command in
meta section

/-- Declares a symbols structure and everything a `Symbols` instance needs. -/
scoped syntax (name := symbolsStructure) atomic((docComment)? "structure.symbols ") ident
  " where" withPosition((ppLine colGe Lean.Parser.Command.structSimpleBinder)+) : command

elab_rules : command
  | `($[$doc?:docComment]? structure.symbols $id where $fields*) =>
    Cvc.Ext.elabSymbols `Cvc.Typed #[
      fun id => `(command|
        abbrev $(mkIdent (id.getId ++ `Fun)) (α : Type) := Cvc.Typed.Symbols.Sig.Fun $id α),
      fun id => `(command|
        abbrev $(mkIdent (id.getId ++ `Pred)) := Cvc.Typed.Symbols.Sig.Pred $id)
    ] doc? id fields

end

end



/-! ## Example 1

`structure.symbols` writes everything a `Symbols` instance needs, so this is the whole of it.
-/
namespace Ex1


/-- User-defined symbol structure. -/
structure.symbols MySymbols where
  /-- A boolean symbol. -/
  myBoolVar : Bool
  /-- An integer symbol. -/
  myIntVar : Int
  /-- A real symbol. -/
  myRealVar : Rat

/-! That is all: the structure, the `Idents`/`Terms`/`Values` aliases and the `Symbols` instance
are generated, and `declare`/`getValues`/`findCex` are generic over the `Sig`, so they need no
per-structure definition either.

```lean
example (idents : MySymbols.Idents) : Env MySymbols.Terms := idents.declare
example (syms : MySymbols.Terms) (s : Solver) : Env (Option MySymbols.Values) := syms.findCex s
```
-/

end Ex1



/-! ## Example 2

Not everything fits `structure.symbols`, and this is what the hand-written path is for: a field
here is an *array* of symbols rather than one, and `InitData` is the identifiers themselves rather
than the default `Unit`. The command wraps each field in the `Wrap` and names each symbol after its
field, so neither is expressible with it.
-/
namespace Ex2

structure MySymbols (W : Symbols.Wrap) where
  boolVars : Array (W Bool)
  intVars : Array (W Int)
  realVars : Array (W Rat)

namespace MySymbols

abbrev Idents := Symbols.Sig.Idents MySymbols
abbrev Terms [Ω] := Symbols.Sig.Terms MySymbols
abbrev Values := Symbols.Sig.Values MySymbols
abbrev Fun (α : Type) := Symbols.Sig.Fun MySymbols α
abbrev Pred := Symbols.Sig.Pred MySymbols

instance : Symbols MySymbols where
  InitData := Idents
  idents := id
  mapM symbols f := return {
    boolVars := ← symbols.boolVars.mapM f
    intVars := ← symbols.intVars.mapM f
    realVars := ← symbols.realVars.mapM f
  }

/-! `declare` and `findCex` need no definition here at all — both are generic over the `Sig`, so
the `Symbols` instance above is the whole of what a symbol structure has to supply:

```lean
example (idents : MySymbols.Idents) : Env MySymbols.Terms := idents.declare
example (syms : MySymbols.Terms) (s : Solver) : Env (Option MySymbols.Values) := syms.findCex s
```
-/

end MySymbols

end Ex2
