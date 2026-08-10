/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto.Spec.Decl



/-! # Function-application specification

Function sorts are curried, so `fn α (fn β γ)` is the SMT sort `(-> α β γ)`. Two ways to
apply one:

- `apply`/`apply2`/`apply3` are *saturating*: they consume the whole domain at once, which is
  what SMT-LIB's `APPLY_UF` requires. The arity is fixed by which one you pick.
- `applyHo` consumes a single argument and returns whatever the codomain is, so it can
  partially apply a multi-argument function. That needs a higher-order logic.
-/
namespace Cvc.Proto public section

/-- Application of a one-argument function. -/
op% apply {α β} (f : fn α β) (arg : α) : β := APPLY_UF

/-- Application of a two-argument function to both of its arguments. -/
op% apply2 {α β γ} (f : fn α (fn β γ)) (fst : α) (snd : β) : γ := APPLY_UF

/-- Application of a three-argument function to all three of its arguments. -/
op% apply3 {α β γ δ} (f : fn α (fn β (fn γ δ))) (fst : α) (snd : β) (thd : γ) : δ
  := APPLY_UF

/-- Application of a single argument, leaving any remaining ones unapplied. -/
op% applyHo {α β} (f : fn α β) (arg : α) : β := HO_APPLY
