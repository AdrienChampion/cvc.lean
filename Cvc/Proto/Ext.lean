/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public meta import Lean.Parser.Term



/-! # The `smt!` term DSL, layer-parameterized

This module holds the parts of the DSL that do not depend on a theory: the `protoSmtTerm`
category, the forms that are not operators (literals, identifiers, `if`/`let`, escapes), the two
layer entry points, and the expander shared by both.

Operator grammar is *not* here. `gen_untyped%` emits one grammar rule per operator carrying a
notation, named `…smtOp.<shape>.<id>`, so a theory's notation is compiled with that theory and no
other. `expandSmt` dispatches on the last three components of a node's kind, which is what lets the
grammar be generated per theory while the expansion logic is written once.

There are two entry points rather than one because each expands to a *different* namespace:
`smtU!` builds `Cvc.Proto.Untyped.Term.…` and `smtT!` builds `Cvc.Proto.Typed.Term.…`, both
fully qualified. Nothing has to be in scope at the use site. Each layer additionally exposes a
`scoped` `smt!` alias, so opening one layer gives the short spelling.

The `protoSmtTerm` category is deliberately *not* declared with `behavior := symbol`: symbol
behavior breaks the longest match between an infix token and its bracket form (`∧` versus `∧[`).
Nothing is reserved by this, since the category's atoms are symbols rather than identifiers.
-/
namespace Cvc.Proto public meta section

open Lean Elab



-- syntax category names are global — they become `Lean.Parser.Category.<name>`, with no
-- namespace — so the name is prefixed to keep it collision-free
declare_syntax_cat protoSmtTerm

/-- Parenthesized SMT term. -/
syntax (name := smtParen) "(" protoSmtTerm ")" : protoSmtTerm
/-- Escape back into Lean: `![e]` splices the Lean term `e`, which must be an `Env`-term. -/
syntax (name := smtEscape) "![" term "]" : protoSmtTerm
/-- An identifier denotes an already-built term, lifted with `pure`. -/
syntax (name := smtIdent) ident : protoSmtTerm
/-- Integer literal. -/
syntax (name := smtNum) num : protoSmtTerm
/-- String literal. -/
syntax (name := smtStr) str : protoSmtTerm
/-- Conditional, expanding to the `ite` operator. -/
syntax (name := smtIte)
  withPosition(
    "if " protoSmtTerm (colGe " then " protoSmtTerm) (colGe " else " (colGe protoSmtTerm))
  )
: protoSmtTerm
/-- Binds an intermediate term. -/
syntax (name := smtLet) "let " ident " ← " protoSmtTerm "; " ppLine protoSmtTerm : protoSmtTerm

/-- Builds a sort-erased term. -/
syntax (name := smtUStx) "smtU! " ppLine group(colGt protoSmtTerm) : term
/-- Builds a typed term. -/
syntax (name := smtTStx) "smtT! " ppLine group(colGt protoSmtTerm) : term



/-- The layer an `smt!` expansion targets. -/
structure Layer where
  /-- Namespace holding the generated operator constructors. -/
  ops : Name
deriving Inhabited

namespace Layer

/-- The sort-erased layer. -/
def untyped : Layer where
  ops := `Cvc.Proto.Untyped.Term

/-- The typed layer. -/
def typed : Layer where
  ops := `Cvc.Proto.Typed.Term

/-- The identifier of an operator of this layer. -/
def op (layer : Layer) (id : Name) : Ident := mkIdent (layer.ops ++ id)

end Layer



/-- Decomposes a generated operator node kind into its shape and operator name.

Grammar rules are named `…smtOp.<shape>.<id>`, so the trailing three components identify the
operator regardless of the namespace the rule was generated in.
-/
def smtOpKind? : Name → Option (Name × Name)
  | .str (.str (.str _ "smtOp") shape) id => some (Name.mkSimple shape, Name.mkSimple id)
  | _ => Option.none

/-- Name of the n-ary function of an operator, `<id>N`. -/
def naryIdOf (id : Name) : Name := id.appendAfter "N"



/-- Binds every argument in order, then applies `mk` to the identifiers they were bound to.

Expansion goes through `>>=` rather than `do`-notation because an antiquotation in `doElem`
head position does not elaborate: `` `(do $fn (← $a) (← $b)) `` is rejected, whereas the bind
chain below is fine. Binder names are macro-scoped, so they cannot capture user identifiers.
-/
def bindArgs (args : Array (TSyntax `term)) (mk : Array Ident → MacroM (TSyntax `term))
: MacroM (TSyntax `term) := do
  let mut ids := #[]
  for i in [0:args.size] do
    ids := ids.push (mkIdent (← MonadQuotation.addMacroScope (Name.mkSimple s!"smtArg{i}")))
  let mut body ← mk ids
  for i in [0:args.size] do
    let j := args.size - 1 - i
    body ← `($(args[j]!) >>= fun $(ids[j]!) => $body)
  return body

/-- Expands one `protoSmtTerm` node into a term of the given layer.

Operator nodes are dispatched by kind; everything else is a fixed form declared above.
-/
partial def expandSmt (layer : Layer) (stx : Syntax) : MacroM (TSyntax `term) := do
  let kind := stx.getKind

  -- generated operators
  if let some (shape, id) := smtOpKind? kind then
    match shape with
    | `binary =>
      let fn := layer.op id
      let args ← #[stx[0], stx[2]].mapM (expandSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!) $(ids[1]!))
    | `prefix =>
      let fn := layer.op id
      let args ← #[stx[1]].mapM (expandSmt layer)
      bindArgs args fun ids => `($fn $(ids[0]!))
    | `nary =>
      let fn := layer.op (naryIdOf id)
      let args ← stx[1].getSepArgs.mapM (expandSmt layer)
      bindArgs args fun ids => `($fn #[ $ids,* ])
    | _ => Macro.throwErrorAt stx s!"unknown generated operator shape `{shape}`"
  else

  -- fixed forms
  match kind with
  | ``smtParen => expandSmt layer stx[1]
  | ``smtEscape => return ⟨stx[1]⟩
  | ``smtNum =>
    let n : TSyntax `term := ⟨stx[0]⟩
    `($(layer.op `mkInt) ($n : Int))
  | ``smtStr =>
    let s : TSyntax `term := ⟨stx[0]⟩
    `($(layer.op `mkString) $s false)
  | ``smtIdent =>
    let id : Ident := ⟨stx[0]⟩
    -- `true`/`false` parse as identifiers in this category
    match id.getId with
    | `true => `($(layer.op `mkTrue))
    | `false => `($(layer.op `mkFalse))
    | _ => `(pure $id)
  | ``smtIte =>
    let fn := layer.op `ite
    let args ← #[stx[1], stx[3], stx[5]].mapM (expandSmt layer)
    bindArgs args fun ids => `($fn $(ids[0]!) $(ids[1]!) $(ids[2]!))
  | ``smtLet =>
    let id : Ident := ⟨stx[1]⟩
    let value ← expandSmt layer stx[3]
    let body ← expandSmt layer stx[5]
    `($value >>= fun $id => $body)
  | _ => Macro.throwErrorAt stx s!"unsupported SMT term (kind `{kind}`)"

macro_rules
  | `(smtU! $t:protoSmtTerm) => expandSmt .untyped t
  | `(smtT! $t:protoSmtTerm) => expandSmt .typed t
