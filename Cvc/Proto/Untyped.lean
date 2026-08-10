/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto.Untyped.Term
public import Cvc.Proto.Untyped.Solver
public import Cvc.Proto.Untyped.Datatype
public import Cvc.Proto.Untyped.Grammar
public import Cvc.Proto.Untyped.Synth



/-! # The sort-erased layer

One directory per part of the API being lifted; `Untyped/Term/` is term creation and
`Untyped/Solver.lean` is the solver.
-/
