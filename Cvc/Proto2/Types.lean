/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto2.Types.Set
public import Cvc.Proto2.Types.Bag
public import Cvc.Proto2.Types.Array
public import Cvc.Proto2.Types.Tuple
public import Cvc.Proto2.Types.Float
public import Cvc.Proto2.Types.FiniteField



/-! # The Lean types denoting SMT sorts

One module per container sort, each holding the Lean type, its `ToTyp` instance and whatever
operations and instances the type needs on the Lean side. They are layer-neutral: a sort is the
same whichever layer names it, so these sit beside the layers rather than inside one.

Turning a value into a term and back is *not* here. Those conversions need a theory's constructors,
so they live in that theory's module under `Cvc/Proto2/{Untyped,Typed}/Term/`.
-/
