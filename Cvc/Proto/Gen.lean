/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command

public import Cvc.Proto.Spec.Defs
import all Cvc.Proto.Spec.Defs



/-! # Term-constructor generators

Two commands, each taking the identifiers of the specification entries to generate constructors
for. They are meant to be invoked from per-theory modules, so that a user compiles only the
theories and the layer they actually import.

```lean
-- Cvc/Proto/Untyped/BitVec.lean
namespace Cvc.Proto.Untyped.Term variable [Ω]
gen_untyped% bvAdd, bvSub, bvConcat

-- Cvc/Proto/Typed/BitVec.lean
namespace Cvc.Proto.Typed.Term open Cvc.Proto.Untyped renaming Term → T variable [Ω]
gen_typed% bvAdd, bvSub, bvConcat
```

`gen_untyped%` emits the sort-erased constructor, going straight to `runUnsafe`; `gen_typed%`
emits the re-typed constructor, delegating to its untyped counterpart through the alias `T`. The
alias keeps the generator independent of where the untyped constructors live.

Requirements on a generation site:

- both layers: `import all Cvc.Basic.Env`, since the emitted bodies use the private `runUnsafe`
  bridge;
- typed only: `import all Cvc.Proto.Typed.Term.Defs`, because delegation typechecks by
  `Typed.Term α` being definitionally `Untyped.Term`, and a plain `import` keeps that body opaque;
- typed only: an alias `T` bound to the untyped term namespace, as shown above.
-/
namespace Cvc.Proto public meta section

open Lean Elab Command



/-! ## Emitted names

Every name the generated code refers to is built with `mkIdent` rather than written literally
inside a quotation. Identifiers written literally are resolved against *this* module's environment
at quotation time, and this module deliberately imports neither layer, so such a reference would
be emitted unresolved and fail at the generation site.
-/

/-- `Cvc.Env`. -/
def envId : Ident := mkIdent `Cvc.Env
/-- `Cvc.runUnsafe`, the private bridge into lean-cvc5. -/
def runUnsafeId : Ident := mkIdent `Cvc.runUnsafe
/-- `Cvc.Proto.ToTyp`. -/
def toTypId : Ident := mkIdent `Cvc.Proto.ToTyp
/-- `Cvc.Proto.Untyped.Term`. -/
def untypedTermId : Ident := mkIdent `Cvc.Proto.Untyped.Term
/-- `Cvc.Proto.Untyped.Terms`. -/
def untypedTermsId : Ident := mkIdent `Cvc.Proto.Untyped.Terms
/-- `Cvc.Proto.Typed.Term`. -/
def typedTermId : Ident := mkIdent `Cvc.Proto.Typed.Term
/-- `Cvc.Proto.Typed.Terms`. -/
def typedTermsId : Ident := mkIdent `Cvc.Proto.Typed.Terms
/-- `Cvc.Proto.Srt`. -/
def srtId : Ident := mkIdent `Cvc.Proto.Srt
/-- `Cvc.Proto.Srt.of`, which turns a Lean index into the sort it denotes. -/
def srtOfId : Ident := mkIdent `Cvc.Proto.Srt.of



/-! ## Rendering shapes as Lean types -/

/-- Renders a size expression as a `Nat`-valued term. -/
partial def SizeExpr.render (arityStx : TSyntax `term) : SizeExpr → MacroM (TSyntax `term)
  | lit n => return Syntax.mkNumLit (toString n)
  | var n => return mkIdent n
  | add lft rgt => do `($(← lft.render arityStx) + $(← rgt.render arityStx))
  | sub lft rgt => do `($(← lft.render arityStx) - $(← rgt.render arityStx))
  | mul lft rgt => do `($(← lft.render arityStx) * $(← rgt.render arityStx))
  | .arity => return arityStx

/-- Renders a sort shape as the Lean type indexing a `Typed.Term`.

Names are emitted fully qualified so that generation sites are free to sit in whichever namespace
suits them. `arityStx` is what `SizeExpr.arity` renders to: a literal in a fixed-arity signature,
the term array's size in an n-ary one.
-/
partial def Shape.render (arityStx : TSyntax `term) : Shape → MacroM (TSyntax `term)
  | var n => return mkIdent n
  | bool => return mkIdent `Bool
  | int => return mkIdent `Int
  | real => return mkIdent `Rat
  | string => return mkIdent `String
  | regex => return mkIdent `Cvc.Proto.Regex
  | roundingMode => return mkIdent `Cvc.Float.RoundingMode
  | bitVec w => do `($(mkIdent `BitVec) $(← w.render arityStx))
  | float e s => do `($(mkIdent `Cvc.Proto.Float) $(← e.render arityStx) $(← s.render arityStx))
  | finiteField s => do `($(mkIdent `Cvc.Proto.FiniteField) $(← s.render arityStx))
  | seq e => do `($(mkIdent `Array) $(← e.render arityStx))
  | set e => do `($(mkIdent `Cvc.Proto.Set) $(← e.render arityStx))
  | bag e => do `($(mkIdent `Cvc.Proto.Bag) $(← e.render arityStx))
  | array i e => do `($(mkIdent `Cvc.Proto.TotalMap) $(← i.render arityStx) $(← e.render arityStx))
  | fn d c => do `($(← d.render arityStx) → $(← c.render arityStx))



/-! ## Shared pieces -/

/-- The `cvc5.Kind` constructor a specification builds its terms with. -/
def OpSpec.kindIdent (spec : OpSpec) : TSyntax `term :=
  mkIdent (`cvc5 ++ `Kind ++ spec.kind)

/-- Name of the n-ary variant of an operator: `<id>N`, or the spec's own choice. -/
def OpSpec.naryId (spec : OpSpec) : Ident :=
  mkIdent (spec.naryName.getD (spec.id.appendAfter "N"))

/-- Name of the defaulting n-ary variant of an operator, the n-ary name primed. -/
def OpSpec.naryPrimeId (spec : OpSpec) : Ident :=
  mkIdent ((spec.naryName.getD (spec.id.appendAfter "N")).appendAfter "'")

/-- Docstring for the `N` variant. -/
def OpSpec.naryDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.id}`, requires at least two elements."

/-- Docstring for the `N'` variant. -/
def OpSpec.naryPrimeDoc (spec : OpSpec) : String :=
  s!"N-ary version of `{spec.id}` with defaults for zero- and one-element arrays."

/-- Creates a `docComment` node from a docstring. -/
def mkDocComment (s : String) : TSyntax ``Lean.Parser.Command.docComment :=
  mkNode ``Lean.Parser.Command.docComment #[mkAtom "/--", mkAtom (s ++ " -/")]

/-- Looks a specification up, failing with a located error if it is not registered. -/
def getOpSpec (id : Ident) : CommandElabM OpSpec := do
  match ← findOpSpec? id.getId with
  | some spec => return spec
  | none => throwErrorAt id s!"no operator specification named `{id.getId}`; declare it with `op%`"



/-! ## Untyped generation -/

/-- Emits the sort-erased constructors for one specification entry.

Every argument and the result erase to `Untyped.Term`, so the shapes play no part beyond fixing
the arity: a pure operator kind infers its sort from its arguments, which `op%` checks.
-/
def genUntyped (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let kind := spec.kindIdent
  let argIds := spec.args.map (mkIdent ·.name)
  -- an antiquotation inside `$[ … ]*` is iterated, so a constant emitted there has to be an array
  -- of the same length as the one it is spliced alongside
  let argTys := argIds.map (fun _ => untypedTermId)
  let indexIds := spec.indices.map mkIdent
  let indexTys := indexIds.map (fun _ => mkIdent `Nat)
  let doc := mkDocComment spec.doc
  -- a constructor takes its own sort when that sort is not fixed by its arguments
  let srtIds := if spec.tmFn.isSome && !spec.unboundRetVars.isEmpty then #[mkIdent `srt] else #[]
  let srtTys := srtIds.map (fun _ => srtId)
  let valIds := spec.valArgs.map (mkIdent ·.name)
  let valTys := spec.valArgs.map (mkIdent ·.type)
  -- a `TermManager` method takes cvc5's sizes as `UInt32`, whereas `mkOpOfIndices` takes `Nat`
  let idxArgs ← indexIds.mapM fun id => `(($id).toUInt32)
  -- three ways to build: a `TermManager` method, an `Op` carrying indices, or the kind itself
  let body ← match spec.tmFn with
    | some fn =>
      let fnId := mkIdent (`cvc5.TermManager ++ fn)
      `($runUnsafeId fun tm => $fnId tm $[ $idxArgs ]* $[ $srtIds ]* $[ $valIds ]* $[ $argIds ]*)
    | none =>
      if spec.indices.isEmpty then
        `($runUnsafeId fun tm => tm.mkTerm $kind #[ $argIds,* ])
      else
        `($runUnsafeId fun tm => do
          tm.mkTermOfOp (← tm.mkOpOfIndices $kind #[ $indexIds,* ]) #[ $argIds,* ])
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(mkIdent spec.id):ident $[ ($indexIds : $indexTys) ]* $[ ($srtIds : $srtTys) ]*
        $[ ($valIds : $valTys) ]* $[ ($argIds : $argTys) ]*
      : $envId $untypedTermId :=
        $body
    )
  ]

  if spec.nary matches .never then return cmds

  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  let naryDoc := mkDocComment spec.naryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.naryId):ident ($termsId : $untypedTermsId)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId $untypedTermId :=
      let _ := $validId
      $runUnsafeId fun tm => tm.mkTerm $kind $termsId
  )

  if let .arrayWithUnit unit := spec.nary then
    let unitTerm ← match unit with
      | .bool b =>
        let lit := mkIdent (if b then `Bool.true else `Bool.false)
        `($(mkIdent `Cvc.Proto.Untyped.Term.mkBool) $lit)
      | .int i => `($(mkIdent `Cvc.Proto.Untyped.Term.mkInt) $(Syntax.mkNumLit (toString i)))
    let naryPrimeDoc := mkDocComment spec.naryPrimeDoc
    cmds := cmds.push <| ← `(
      $naryPrimeDoc:docComment
      def $(spec.naryPrimeId):ident ($termsId : $untypedTermsId)
        (on0 : $envId $untypedTermId := $unitTerm)
        (on1 : $untypedTermId → $envId $untypedTermId := pure)
      : $envId $untypedTermId :=
        if $(termsId).size = 0 then on0
        else if h : $(termsId).size = 1 then on1 $(termsId)[0]
        else $runUnsafeId fun tm => tm.mkTerm $kind $termsId
    )

  return cmds

/-! ## DSL grammar generation

The `protoSmtTerm` grammar rule of an operator is emitted alongside its *untyped* constructor,
and only there: the typed constructors delegate to the untyped ones, so a typed theory module
always imports its untyped counterpart and inherits the grammar. Emitting from both layers would
declare the same rule twice.

Rules are named `smtOp.<shape>.<id>`, which under the enclosing namespace becomes
`…Term.smtOp.binary.and` and so on. `Cvc.Proto.expandSmt` dispatches on those trailing
three components, so it needs no knowledge of where generation happened.
-/

/-- Name of an operator's generated grammar rule, relative to the generation site's namespace. -/
def smtRuleId (shape id : Name) : Ident :=
  mkIdent (`smtOp ++ shape ++ id)

/-- Emits the `protoSmtTerm` grammar rules for one specification entry's notation. -/
def genSmtSyntax (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let cat := mkIdent `protoSmtTerm
  match spec.smtNotation with
  | .none => return #[]
  | .pref sym prec argPrec =>
    let prec := Syntax.mkNumLit (toString prec)
    let argPrec := Syntax.mkNumLit (toString argPrec)
    let atom := Syntax.mkStrLit s!"{sym} "
    return #[← `(command|
      syntax:$prec (name := $(smtRuleId `prefix spec.id)) $atom:str $cat:ident:$argPrec : $cat
    )]
  | .inf sym prec assoc =>
    -- left-associative binds its right operand tighter, right-associative its left one
    let lftPrec := Syntax.mkNumLit (toString (if assoc matches .left then prec else prec + 1))
    let rgtPrec := Syntax.mkNumLit (toString (if assoc matches .left then prec + 1 else prec))
    let precStx := Syntax.mkNumLit (toString prec)
    let atom := Syntax.mkStrLit s!" {sym} "
    let mut cmds := #[← `(command|
      syntax:$precStx (name := $(smtRuleId `binary spec.id))
        $cat:ident:$lftPrec $atom:str $cat:ident:$rgtPrec : $cat
    )]
    -- the bracket form exists only when there is an n-ary function to expand to
    unless spec.nary matches .never do
      let bracket := Syntax.mkStrLit s!"{sym}["
      cmds := cmds.push <| ← `(command|
        syntax (name := $(smtRuleId `nary spec.id)) $bracket:str $cat:ident,+,? "]" : $cat
      )
    return cmds

/-- Emits the sort-erased constructors, and the DSL grammar, for one entry. -/
def emitUntyped (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genUntyped spec) do
    elabCommand cmd
  for cmd in ← liftMacroM (genSmtSyntax spec) do
    elabCommand cmd

/-- Generates the sort-erased constructors for the named specification entries. -/
syntax (name := genUntypedStx) "gen_untyped% " ident,+ : command

/-- Generates the sort-erased constructors for every entry a specification module declares. -/
syntax (name := genUntypedFromStx) "gen_untyped% " "from " ident : command

@[command_elab genUntypedStx]
def elabGenUntyped : CommandElab
  | `(gen_untyped% $ids,*) => do
    for id in ids.getElems do
      emitUntyped (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genUntypedFromStx]
def elabGenUntypedFrom : CommandElab
  | `(gen_untyped% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitUntyped spec
  | _ => throwUnsupportedSyntax



/-! ## Typed generation -/

/-- Emits the binders a typed constructor needs: type, size, `Ord` and refinement classes.

A type variable carrying refinement classes also gets a `ToTyp` binder, since a refinement such as
`IsArith` is stated over the variable's `Typ` and so takes `ToTyp` as an instance argument.
-/
def typedBinders (spec : OpSpec) : MacroM (Array (TSyntax ``Lean.Parser.Term.bracketedBinder)) := do
  let mut binders := #[]
  for tyVar in spec.tyVars do
    binders := binders.push <| ← `(bracketedBinder| { $(mkIdent tyVar.name) : Type })
  for sizeVar in spec.sizeVars do
    binders := binders.push <| ← `(bracketedBinder| { $(mkIdent sizeVar) : Nat })
  for ordVar in spec.ordVars do
    binders := binders.push <| ← `(bracketedBinder| [ $(mkIdent `Ord) $(mkIdent ordVar) ])
  -- a constructor computes its own sort with `Srt.of`, so it needs `ToTyp` on every variable
  let needsToTyp := spec.tmFn.isSome && !spec.unboundRetVars.isEmpty
  for tyVar in spec.tyVars do
    unless tyVar.classes.isEmpty && !needsToTyp do
      binders := binders.push <| ← `(bracketedBinder| [ $toTypId $(mkIdent tyVar.name) ])
    for cls in tyVar.classes do
      binders := binders.push <| ← `(bracketedBinder| [ $(mkIdent cls) $(mkIdent tyVar.name) ])
  return binders

/-- Emits the re-typed constructors for one specification entry, delegating to the untyped ones. -/
def genTyped (spec : OpSpec) : MacroM (Array (TSyntax `command)) := do
  let binders ← typedBinders spec
  let argIds := spec.args.map (mkIdent ·.name)
  -- `SizeExpr.arity` means the number of term arguments: a literal here, `terms.size` below
  let fixedArity := Syntax.mkNumLit (toString spec.args.size)
  let argTypes ← spec.args.mapM (Shape.render fixedArity ·.shape)
  let typedTermIds := argTypes.map (fun _ => typedTermId)
  let retType ← spec.ret.render fixedArity
  let untypedId := mkIdent (`T ++ spec.id)
  let indexIds := spec.indices.map mkIdent
  let indexTys := indexIds.map (fun _ => mkIdent `Nat)
  let doc := mkDocComment spec.doc
  -- a constructor whose sort is not fixed by its arguments recovers it from the result's index
  let valIds := spec.valArgs.map (mkIdent ·.name)
  let valTys := spec.valArgs.map (mkIdent ·.type)
  let sortType ← match spec.sortArg with
    | some shape => shape.render fixedArity
    | none => pure retType
  let body ← if spec.tmFn.isSome && !spec.unboundRetVars.isEmpty then
      `($srtOfId $sortType >>= fun srt => $untypedId srt $[ $valIds ]* $[ $argIds ]*)
    else
      `($untypedId $[ $indexIds ]* $[ $valIds ]* $[ $argIds ]*)
  let mut cmds := #[
    ← `(
      $doc:docComment
      def $(mkIdent spec.id):ident $[ ($indexIds : $indexTys) ]* $[ $binders ]*
        $[ ($valIds : $valTys) ]* $[ ($argIds : $typedTermIds $argTypes) ]*
      : $envId ($typedTermId $retType) :=
        $body
    )
  ]

  if spec.nary matches .never then return cmds

  -- the n-ary variants take a homogeneous term array, so they need every *argument* to share one
  -- shape; the result shape is free, which is what `equal`/`lt`/… (`α → α → bool`) rely on
  let some firstArg := spec.args[0]? | return cmds
  unless spec.args.all (·.shape == firstArg.shape) do
    return cmds
  let termsId := mkIdent `terms
  let validId := mkIdent `atLeastTwoElements
  -- in the n-ary signature the arity is the array's size, so a result that depends on it depends
  -- on a runtime value
  let naryArity ← `(($termsId).size)
  let naryRetType ← spec.ret.render naryArity
  let naryArgType ← firstArg.shape.render naryArity
  let naryDoc := mkDocComment spec.naryDoc
  cmds := cmds.push <| ← `(
    $naryDoc:docComment
    def $(spec.naryId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      ($validId : 2 ≤ $(termsId).size := by
        (try grind) <;> fail "failed to prove term array has at least two elements")
    : $envId ($typedTermId $naryRetType) :=
      $(mkIdent (`T ++ spec.naryId.getId)) $termsId $validId
  )

  if spec.nary matches .arrayWithUnit _ then
    let naryPrimeDoc := mkDocComment spec.naryPrimeDoc
    cmds := cmds.push <| ← `(
      $naryPrimeDoc:docComment
      def $(spec.naryPrimeId):ident $[ $binders ]* ($termsId : $typedTermsId $naryArgType)
      : $envId ($typedTermId $naryRetType) :=
        $(mkIdent (`T ++ spec.naryPrimeId.getId)) $termsId
    )

  return cmds

/-- Emits the re-typed constructors for one entry. -/
def emitTyped (spec : OpSpec) : CommandElabM Unit := do
  for cmd in ← liftMacroM (genTyped spec) do
    elabCommand cmd

/-- Generates the re-typed constructors for the named specification entries. -/
syntax (name := genTypedStx) "gen_typed% " ident,+ : command

/-- Generates the re-typed constructors for every entry a specification module declares. -/
syntax (name := genTypedFromStx) "gen_typed% " "from " ident : command

@[command_elab genTypedStx]
def elabGenTyped : CommandElab
  | `(gen_typed% $ids,*) => do
    for id in ids.getElems do
      emitTyped (← getOpSpec id)
  | _ => throwUnsupportedSyntax

@[command_elab genTypedFromStx]
def elabGenTypedFrom : CommandElab
  | `(gen_typed% from $mod:ident) => do
    let specs ← opSpecsOf mod.getId
    if specs.isEmpty then
      throwErrorAt mod s!"`{mod.getId}` declares no operator specification"
    for spec in specs do emitTyped spec
  | _ => throwUnsupportedSyntax
