/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Elab.Command
public import Cvc.Basic.Env

import all Cvc.Srt
import all Cvc.Term

public import Cvc.Term



namespace Cvc public section variable [Ω]


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



namespace Srt

/-- A pattern-matchable version of `Srt`. -/
pat_tree[ofSrt srt, toSrt, Srt] Pattern, Tree

| bool [.BOOLEAN_SORT] → Srt.bool
| int [.INTEGER_SORT] → Srt.int
| real [.REAL_SORT] → Srt.real
| regex [.REGLAN_SORT] → Srt.regex
| roundingMode [.ROUNDINGMODE_SORT] → Srt.roundingMode
| string [.STRING_SORT] → Srt.string

| abstract [.ABSTRACT_SORT]
  (a : Abstract ← Abstract.ofKind (← srt.getAbstractedKind))
→ a.toSrt

| bag [.BAG_SORT]
  (elm : 𝓢ub ← srt.getBagElementSort >>= ofSrt)
→ toSrt elm >>= Srt.bag

| array [.ARRAY_SORT]
  (idx : 𝓢ub ← srt.getArrayIndexSort >>= ofSrt)
  (elm : 𝓢ub ← srt.getArrayElementSort >>= ofSrt)
→ (← toSrt idx).arrayTo (← toSrt elm)

| bitVec [.BITVECTOR_SORT]
  (size : UInt32 ← srt.getBitVectorSize)
→ Srt.bitVec size

| float [.FLOATINGPOINT_SORT]
  (exp : UInt32 ← srt.getFloatingPointExponentSize)
  (sig : UInt32 ← srt.getFloatingPointSignificandSize)
→ Srt.float exp sig

| finiteField [.FINITE_FIELD_SORT]
  (size : Nat ← srt.getFiniteFieldSize)
→ Srt.finiteField size

| function [.FUNCTION_SORT]
  (dom : Array 𝓢ub ← srt.getFunctionDomainSorts >>= Array.mapM ofSrt)
  (cod : 𝓢ub ← srt.getFunctionCodomainSort >>= ofSrt)
→ let dom ← dom.mapM toSrt
  if h : 0 < dom.size then toSrt cod >>= Srt.function dom
  else throwInternal "ill-formed pattern: function with empty domain"

end Srt



namespace Term

/-- A pattern-matchable version of `Term`. -/
pat_tree[ofTerm term, toTerm, Term] Pattern, Tree
| bool [.CONST_BOOLEAN]
  (b : Bool ← term.getBoolValue)
→ Term.mkBool b

| int [.CONST_INTEGER]
  (i : Int ← term.getIntValue)
→ Term.mkInt i

| string [.CONST_STRING]
  (s : String ← term.getStringValue)
→ Term.mkString s

end Term
