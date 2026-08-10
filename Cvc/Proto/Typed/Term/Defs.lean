/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto.Untyped.Term.Defs
public import Cvc.Proto.Ext

public import Cvc.Proto.Untyped.Term

import all Cvc.Basic.Env
import all Cvc.Proto.Srt
import all Cvc.Proto.Untyped.Term.Defs
import all Cvc.Proto.Untyped.Term



/-! # The typed term type, and this layer's `smt!` entry point

A typed term is a sort-erased one carrying a phantom Lean index describing its sort. The index is
erased at runtime: `Term α` is definitionally `Untyped.Term`, and the conversions either way are
`id`, so stating a sort costs nothing.

`Cvc.Proto.Typed.Term` names both this type and the namespace holding the generated constructors,
so a signature can mention `Term α` without reaching outside the layer.
-/
namespace Cvc.Proto.Typed public section variable [Ω]

wrap3% Term α ← Cvc.Proto.Untyped.Term (ofUntypedUnsafe / toUntypedUnsafe)

namespace Term

/-- Erases its type. -/
def erase (t : Term α) : Untyped.Term := t

/-- Types an untyped term. -/
def ofUntyped' (t : Untyped.Term) (α : Type) [ToTyp α] : Env (Term α) := do
  let srt ← t.getSort
  let srt' ← Srt.of α
  if srt != srt' then
    throwUser s!"cannot type the following term as `{srt'}`, term has sort `{srt}`:\n{t}"
  return t

@[inherit_doc ofUntyped']
abbrev ofUntyped [ToTyp α] (t : Untyped.Term) : Env (Term α) := ofUntyped' t α

end Term

@[inherit_doc Typed.Term.ofUntyped']
def _root_.Cvc.Proto.Untyped.Term.typeCheckAs (t : Untyped.Term) (α : Type) [ToTyp α]
: Env (Term α) := Typed.Term.ofUntyped' t α

@[inherit_doc Untyped.Term.typeCheckAs]
def _root_.Cvc.Proto.Untyped.Term.typeCheck [ToTyp α] (t : Untyped.Term)
: Env (Term α) := t.typeCheckAs α

/-- An array of terms of the sort `α` describes. -/
abbrev Terms (α : Type) := Array (Term α)

namespace Terms

private def toUnsafe : Terms α → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms α := id

private example (ts : Terms α) : ofUnsafe ts.toUnsafe = ts := rfl

end Terms


/-- Typed `smt!`.

`scoped`, so that `open Cvc.Proto.Typed` selects this layer's DSL. It forwards to `smtT!`, which
expands to fully-qualified `Cvc.Proto.Typed.Term.…` calls; nothing needs to be in scope.

Opening both layers at once makes the two `smt!` parsers ambiguous — open the one you mean.
-/
scoped syntax "smt! " ppLine group(colGt protoSmtTerm) : term

macro_rules | `(smt! $t:protoSmtTerm) => `(smtT! $t)
