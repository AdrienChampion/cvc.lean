/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Env
import all Cvc.Proto2.Untyped.Term.Defs

public import Cvc.Proto2.Untyped.Term.Defs
-- the plain theory, for the constructors backing the `N'` variants' unit elements; `nullableSome`
-- wraps one, since a lifted operator's unit is nullable too
public import Cvc.Proto2.Untyped.Term.Set
public import Cvc.Proto2.Untyped.Term.Nullable
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Spec.Set



/-! # Sets over nullables, sort-erased

One lifted constructor per liftable operator, `<id>?`, each answering `none` unless every argument
is `some`. That strictness is `nullable.lift`'s semantics and not a choice made here.

The set *term* becomes nullable, not its elements — `Option (Set α)`, not `Set (Option α)`. The
element type is untouched, so the `Ord` binders are the plain operators'.
-/
namespace Cvc.Proto2.Untyped.Term public section variable [Ω]

gen_untyped_nullable% from Cvc.Proto2.Spec.Set
