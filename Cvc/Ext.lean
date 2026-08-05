/-
Copyright (c) 2025 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public meta import Lean.Parser.Term

-- import Cvc.Term



namespace Cvc

declare_syntax_cat smtTerm

meta def mkValueId := Lean.mkIdent `Term.mkValue

scoped syntax "![" term "]" : smtTerm

scoped syntax "(" smtTerm ")" : smtTerm

scoped syntax ident : smtTerm
scoped syntax name : smtTerm
scoped syntax num : smtTerm
scoped syntax str : smtTerm

scoped syntax "?[" term " : " term "]" : smtTerm

scoped syntax:25 smtTerm:26 " → " smtTerm:25 : smtTerm
scoped syntax "→[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:35 smtTerm:36 " ∧ " smtTerm:35 : smtTerm
scoped syntax "∧[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:30 smtTerm:31 " ∨ " smtTerm:30 : smtTerm
scoped syntax "∨[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:30 smtTerm:30 " ⊻ " smtTerm:31 : smtTerm
scoped syntax "⊻[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:max "¬ " smtTerm:40 : smtTerm

scoped syntax
  withPosition("if " smtTerm (colGe " then " smtTerm) (colGe " else " (colGe smtTerm)))
: smtTerm
scoped syntax "let " ident " ← " smtTerm "; " ppLine smtTerm : smtTerm

scoped syntax:50 smtTerm:51 " = " smtTerm:50 : smtTerm
scoped syntax "=[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≠ " smtTerm:50 : smtTerm
scoped syntax "≠[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≤ " smtTerm:50 : smtTerm
scoped syntax "≤[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " ≥ " smtTerm:50 : smtTerm
scoped syntax "≥[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " < " smtTerm:50 : smtTerm
scoped syntax "<[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:50 smtTerm:51 " > " smtTerm:50 : smtTerm
scoped syntax ">[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm

scoped syntax:62 smtTerm:63 " ++ " smtTerm:62 : smtTerm

scoped syntax:70 smtTerm:70 " * " smtTerm:71 : smtTerm
scoped syntax "*[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:70 smtTerm:70 " /! " smtTerm:71 : smtTerm
scoped syntax "/![" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:70 smtTerm:70 " / " smtTerm:71 : smtTerm
scoped syntax:70 smtTerm:70 " % " smtTerm:71 : smtTerm
scoped syntax:65 smtTerm:65 " + " smtTerm:66 : smtTerm
scoped syntax "+[" smtTerm ", " smtTerm (", " smtTerm)* ","? "]" : smtTerm
scoped syntax:65 smtTerm:65 " - " smtTerm:66 : smtTerm
scoped syntax:75 "- " smtTerm : smtTerm

scoped syntax:100 smtTerm:100 group(colGt smtTerm:101) : smtTerm

scoped syntax "smt! " ppLine group(colGt smtTerm) : term



section open Lean.Parser.Term

scoped syntax
  (("smt! " "fun ") <|> "smtFun! ")
    (ppSpace funBinder)+ optType " => " ppLine group(colGt smtTerm)
: term
scoped syntax
  ("smtPred! " <|> "smtPredicate! ")
    (ppSpace funBinder) optType " => " ppLine group(colGt smtTerm)
: term
scoped syntax
  ("smtRel! " <|> "smtRelation! ")
    (ppSpace funBinder) (ppSpace funBinder) optType " => " ppLine group(colGt smtTerm)
: term

end

macro_rules
| `(smt! fun $[$binders]* $[ : $ty:term ]? => $t:smtTerm ) =>
  `(fun $[$binders]* $[ : $ty ]? => smt! $t)
| `(smt! fun $[$binders]* => $t:smtTerm ) =>
  `(fun $[$binders]* => smt! $t)
| `(smtFun! $[$binders]* $[ : $ty:term ]? => $t:smtTerm ) =>
  `(fun $[$binders]* $[ : $ty:term ]? => smt! $t)
| `(smtFun! $[$binders]* => $t:smtTerm ) =>
  `(fun $[$binders]* => smt! $t)
| `(smtPredicate! $binder:funBinder $[ : $ty:term ]? => $t:smtTerm ) =>
  `(fun $binder:funBinder $[ : $ty:term ]? => smt! $t)
| `(smtPred! $binder:funBinder $[ : $ty:term ]? => $t:smtTerm ) =>
  `(fun $binder:funBinder $[ : $ty:term ]? => smt! $t)
| `(smtRel! $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => $t:smtTerm) =>
  `(fun $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => smt! $t)
| `(smtRelation! $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => $t:smtTerm) =>
  `(fun $currBinder:funBinder $nextBinder:funBinder $[ : $ty:term ]? => smt! $t)

-- | `(smt! [| $t:term |]) => `((pure $t))
| `(smt! ![ $t:term ]) => `($t)
| `(smt! ($t:smtTerm)) => `(smt! $t)
-- | `(smt! ?[ $t:term : $ty:term ]) => ``($t >>= fun eTerm => Cvc.ETerm.as eTerm $ty)

| `(smt! false) => `($mkValueId false)
| `(smt! true) => `($mkValueId true)
| `(smt! $n:num) => `($mkValueId ($n : Int))
| `(smt! - $n:num) => `($mkValueId (- $n : Int))
| `(smt! $s:str) => `($mkValueId $s)
| `(smt! $n:ident) =>
  -- let termId := Lean.mkIdent `Term
  -- ``(pure ($n : $termId))
  ``(pure $n)
| `(smt! $n:name) =>
  -- let termId := Lean.mkIdent `Term
  -- ``(pure ($n : $termId))
  ``(pure $n)

| `(smt! $lft → $rgt) =>
  `( (do (← smt! $lft).implies (← smt! $rgt)) )
| `(smt! →[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let impliesN := `Term.impliesN |> Lean.mkIdent
  `( (do $impliesN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft ∧ $rgt) =>
  `( (do (← smt! $lft).and (← smt! $rgt)) )
| `(smt! ∧[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let andN := `Term.andN |> Lean.mkIdent
  `( (do $andN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft ∨ $rgt) =>
  let mkOr := `Term.or |> Lean.mkIdent
  `( (do $mkOr:ident (← smt! $lft) (← smt! $rgt)) )
| `(smt! ∨[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let orN := `Term.orN |> Lean.mkIdent
  `( (do $orN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft ⊻ $rgt) =>
  `( (do (← smt! $lft).xor (← smt! $rgt)) )
| `(smt! ⊻[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let xorN := `Term.xorN |> Lean.mkIdent
  `( (do $xorN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! ¬ $t) =>
  `( (do (← smt! $t).not) )

| `(smt! if $cnd then $thn else $els) =>
  let ite := `Term.ite |> Lean.mkIdent
  `( (do $ite:ident (← smt! $cnd) (← smt! $thn) (← smt! $els)) )

| `(smt! let $id ← $idDef ; $tail) => `( ( do
  let $id ← smt! $idDef
  smt! $tail
) )

| `(smt! $lft = $rgt) =>
  let equal := `Term.equal |> Lean.mkIdent
  `( (do $equal:ident (← smt! $lft) (← smt! $rgt)) )
| `(smt! =[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let equalN := `Term.equalN |> Lean.mkIdent
  `( (do $equalN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $lft ≠ $rgt) =>
  `( (do (← smt! $lft).distinct (← smt! $rgt)) )
| `(smt! ≠[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let distinctN := `Term.distinctN |> Lean.mkIdent
  `( (do $distinctN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $lft ≤ $rgt) => `( (do (← smt! $lft).le (← smt! $rgt)) )
| `(smt! ≤[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let leN := `Term.leN |> Lean.mkIdent
  `( (do $leN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $lft ≥ $rgt) => `( (do (← smt! $lft).ge (← smt! $rgt)) )
| `(smt! ≥[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let geN := `Term.geN |> Lean.mkIdent
  `( (do $geN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $lft < $rgt) => `( (do (← smt! $lft).lt (← smt! $rgt)) )
| `(smt! <[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let ltN := `Term.ltN |> Lean.mkIdent
  `( (do $ltN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $lft > $rgt) => `( (do (← smt! $lft).gt (← smt! $rgt)) )
| `(smt! >[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let gtN := `Term.gtN |> Lean.mkIdent
  `( (do $gtN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )

| `(smt! $f:smtTerm $arg:smtTerm) =>
  let apply := `Term.apply |> Lean.mkIdent
  `( (do $apply:ident (← smt! $f) (← smt! $arg)) )

| `(smt! $lft * $rgt) =>
  `( (do (← smt! $lft).mul (← smt! $rgt)) )
| `(smt! *[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let mulN := `Term.mulN |> Lean.mkIdent
  `( (do $mulN:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft / $rgt) =>
  let divTotal := `Term.divTotal |> Lean.mkIdent
  `( (do $divTotal:ident (← smt! $lft) (← smt! $rgt)) )
| `(smt! $lft /! $rgt) =>
  let div! := `Term.div! |> Lean.mkIdent
  `( (do $div!:ident (← smt! $lft) (← smt! $rgt)) )
| `(smt! /![ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let mkDiv! := `Term.mkDiv! |> Lean.mkIdent
  `( (do $mkDiv!:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! $lft + $rgt) =>
  let add := `Term.add |> Lean.mkIdent
  `( (do $add:ident (← smt! $lft) (← smt! $rgt)) )
| `(smt! +[ $fst:smtTerm, $snd:smtTerm $[ , $tail:smtTerm ]* $[,]? ]) =>
  let mkAdd := `Term.mkAdd |> Lean.mkIdent
  `( (do $mkAdd:ident #[(← smt! ($fst)), (← smt! ($snd)), $[(← smt! ($tail)) ],* ]) )
| `(smt! - $t) =>
  let mkNeg := `Term.neg |> Lean.mkIdent
  `( (do $mkNeg:ident (← smt! $t)) )
| `(smt! $lft - $rgt) =>
  let sub := `Term.sub |> Lean.mkIdent
  `( (do $sub:ident (← smt! $lft) (← smt! $rgt)) )
