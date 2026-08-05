/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public import Cvc.Basic.Env



namespace Cvc public section


syntax (name := patTreeStx)
  atomic(declModifiers ppLine "pat_tree")
  "[" ident ident ", " ident ", " term "]"
  ident ", " ident (
    group(
      (docComment)?
      ppLine "| " declModifiers rawIdent "[" term "]"
        ( "(" rawIdent " : " term " ← " doSeq ")" )*
        ppLine ppIndent("→ " doSeq)
    )
  )* : command

section
open Lean Elab Command


syntax "𝓢ub" : term
syntax "𝓡es" : term

@[command_elab patTreeStx]
public meta def elabPatTreeStx : CommandElab
| `(
  $mods:declModifiers
  pat_tree[$ofActual:ident $ofActualInput:ident, $toActual:ident, $actualTy:term]
  $patternId:ident, $treeId:ident $[
    $[ $variantDoc?:docComment ]?
    | $variantMods:declModifiers $variantId:ident [ $actualVariantId:term ]
      $[ ( $variantArgs:ident : $variantArgsTy:term ← $variantArgsOfActual:doSeq ) ]*
      → $variantToActual:doSeq
  ]*
) => do
  let toStringId := mkIdent `toString
  let envId := mkIdent ``Env
  let patId := mkIdent `Pat
  let patTyParam := mkIdent `α
  let patTy ← `( $patId $patTyParam )
  let binderss ← variantArgs.zip variantArgsTy |>.mapM fun (args, tys) => do
    let binders : Array _ ← args.zip tys |>.mapM fun (args, ty) => do
      let raw ← ty.raw |> Lean.Syntax.replaceM fun
        | `(𝓢ub) => return some patTyParam.raw
        | `(𝓡es) => return some patTy.raw
        | _ => return none
      let ty := {ty with raw}
      `(bracketedBinder| ( $args:ident : $ty ) )
    return binders
  let stx ← `(
    $mods:declModifiers
    inductive $patId:ident ($patTyParam : Type) $[
      $[ $variantDoc?:docComment ]?
      | $variantMods:declModifiers $variantId:ident $[ $binderss:bracketedBinder ]*
    ]*
    deriving Inhabited, BEq, Ord, Hashable, Repr

    namespace $patId
    instance [Repr $patTyParam] : ToString ($patId $patTyParam) := ⟨(s!"{reprPrec · 0}")⟩

    /-- String representation. -/
    protected def $toStringId [Repr $patTyParam] : $patId $patTyParam → String := $toStringId
    end $patId
  )
  -- logInfo s!"elaborating consultation:\n{← liftCoreM <| Lean.PrettyPrinter.formatTerm stx}"
  elabCommand stx

  let stx ← `(
    $mods:declModifiers
    abbrev $patternId := $patId $actualTy
  )
  elabCommand stx

  let treeIntroId := mkIdent `intro
  let patToStringId := patId.getId.append toStringId.getId |> mkIdent
  let treeToStringId := treeId.getId.append toStringId.getId |> mkIdent
  let stx ← `(
    $mods:declModifiers
    inductive $treeId
    | $treeIntroId:ident : $patId $treeId → $treeId
    deriving Inhabited, BEq, Ord, Hashable, Repr

    namespace $treeId
    /-- String representation. -/
    protected def $toStringId : $treeId → String
      | .$treeIntroId pat => $patToStringId pat
    instance : ToString $treeId := ⟨$treeToStringId⟩
    end $treeId
  )
  elabCommand stx

  let variants :=
    variantDoc?.zip <| variantId.zip <| variantArgs
  for (variantDoc?, variantId, args) in variants do
    let patternVariantId := patId.getId.append variantId.getId |> mkIdent
    let stx ← `(
      namespace $treeId
      $[ $variantDoc?:docComment ]?
      @[match_pattern]
      abbrev $variantId:ident $[$args:ident]* :=
        ( $treeIntroId <| $patternVariantId:ident $[ $args:ident ]* )
      end $treeId
    )
    elabCommand stx

  let patToActualId := patId.getId.append toActual.getId |> mkIdent
  let ofPatternId := mkIdent `ofPattern
  let ofTreeId := mkIdent `ofTree
  let patternToActualId := patternId.getId.append toActual.getId |> mkIdent
  let treeToActualId := treeId.getId.append toActual.getId |> mkIdent
  let stx ← `(
    namespace $patId
    def $toActual ($toActual : $patTyParam → $envId $actualTy)
    : $patId $patTyParam → $envId $actualTy
      $[ | $variantId:ident $[ $variantArgs:ident]* => do $variantToActual:doSeq ]*
    end $patId

    namespace $patternId
    def $toActual : (pat : $patternId) → $envId $actualTy := $patToActualId pure
    end $patternId

    def $ofPatternId := $patternToActualId

    namespace $treeId
    partial def $toActual : (tree : $treeId) → $envId $actualTy
      | $treeIntroId pat => $patToActualId $toActual pat
    end $treeId

    def $ofTreeId := $treeToActualId
  )
  elabCommand stx

  let patOfActualId := patId.getId.append ofActual.getId |> mkIdent
  let toPatternId := mkIdent `toPattern
  let toTreeId := mkIdent `toTree
  let patternOfActualId := patternId.getId.append ofActual.getId |> mkIdent
  let treeOfActualId := treeId.getId.append ofActual.getId |> mkIdent
  let variantArgs' := variantArgs
  let stx ← `(
    namespace $patId
    def $ofActual
      ($ofActual : $actualTy → $envId $patTyParam) ($ofActualInput : $actualTy)
    : $envId ($patId $patTyParam) := do
      match ← ($ofActualInput |>.getKind) with
      $[ | $actualVariantId =>
        $[ let $variantArgs ← do $variantArgsOfActual ]*
        return $variantId $[ $variantArgs' ]*
      ]*
      | k => throwInternal s!"unsupported kind {k}"
    end $patId

    namespace $patternId
    def $ofActual : ($ofActualInput : $actualTy) → $envId $patternId := $patOfActualId pure
    end $patternId

    def $toPatternId := $patternOfActualId

    namespace $treeId
    partial def $ofActual ($ofActualInput : $actualTy) : $envId $treeId :=
      $treeIntroId <$> $patOfActualId $ofActual $ofActualInput
    end $treeId

    def $toTreeId := $treeOfActualId
  )
  elabCommand stx

| _ => throwUnsupportedSyntax

end
