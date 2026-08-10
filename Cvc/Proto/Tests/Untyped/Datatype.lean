/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Untyped.Datatype
import Cvc.Proto.Untyped.Term

public meta import Cvc.Proto.Untyped.Datatype
public meta import Cvc.Proto.Untyped.Term



/-! # Datatypes, sort-erased -/
namespace Cvc.Proto.Tests.Untyped.Datatype

open Cvc
open Cvc.Proto
open Cvc.Proto.Untyped



/-! ## Declaring, reflecting, and using

The full cycle on a one-constructor datatype: declare it, read it back out of its sort, build a
value with the constructor's term, and take it apart with a selector's.
-/

/-- info:
sort      : Pair, isDatatype true
name      : Pair, ctors 1
ctor      : mk, selectors 2
  sel     : fst : Int
  sel     : snd : Bool
value     : (mk 7 true)
fst       : (fst (mk 7 true))
is mk     : ((_ is mk) (mk 7 true))
updated   : ((_ update fst) (mk 7 true) 9)
model fst : 7
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"

  let mk ← Proto.Datatype.Constructor.Decl.mk "mk"
  let mk ← mk.addSelector "fst" (← Srt.int)
  let mk ← mk.addSelector "snd" (← Srt.bool)
  let pair ← s.declareDatatype "Pair" #[mk]
  println! "sort      : {pair}, isDatatype {pair.isDatatype}"

  let dt ← pair.getDatatype
  println! "name      : {← dt.getName}, ctors {dt.countConstructors}"
  let ctor ← dt.getConstructor "mk"
  println! "ctor      : {← ctor.getName}, selectors {ctor.countSelectors}"
  -- a constructor iterates over its selectors
  for sel in ctor do
    println! "  sel     : {← sel.getName} : {← sel.getCodomainSort}"

  let p ← Term.applyConstructor (← ctor.getTerm) #[← Term.mkInt 7, ← Term.mkTrue]
  println! "value     : {p}"
  let fst ← ctor.getSelector "fst"
  println! "fst       : {← Term.applySelector (← fst.getTerm) p}"
  println! "is mk     : {← Term.applyTester (← ctor.getTesterTerm) p}"
  println! "updated   : {← Term.applyUpdater (← fst.getUpdaterTerm) p (← Term.mkInt 9)}"

  let x ← s.declareConst "x" pair
  (do Term.equal x p) >>= s.assert
  let xFst ← Term.applySelector (← fst.getTerm) x
  s.checkSat (ifSat := do println! "model fst : {← s.getValueAs Int xFst}")



/-! ## A declared sort is fresh, never nominal

Two declarations of the same datatype give two *different* sorts that print identically, and cvc5
refuses to mix them. This is what stops `ToTyp` having a datatype case: it maps a Lean type to a
`Typ` that `Typ.toSrt` rebuilds on demand, and rebuilding does not give back the same sort.
-/

/-- info:
same name  : Pair / Pair
equal      : false
mixing     : rejected
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let declare : Env Srt := do
    let mk ← Proto.Datatype.Constructor.Decl.mk "mk"
    let mk ← mk.addSelector "fst" (← Srt.int)
    s.declareDatatype "Pair" #[mk]

  let a ← declare
  let b ← declare
  println! "same name  : {a} / {b}"
  println! "equal      : {a == b}"

  let x ← s.declareConst "x" a
  let y ← s.declareConst "y" b
  let outcome ←
    try
      let _ ← Term.equal x y
      pure "accepted"
    catch _ => pure "rejected"
  println! "mixing     : {outcome}"



/-! ## Recursion

A datatype referring to itself uses `addSelectorSelf`, and needs the general `Srt.datatype` rather
than `Solver.declareDatatype`.
-/

/-- info:
sort   : Lst
ctors  : 2
value  : (cons 1 (cons 2 nil))
head   : (head (cons 1 (cons 2 nil)))
is nil : ((_ is nil) (cons 1 (cons 2 nil)))
-/
#guard_msgs in #eval Env.runIO do
  let nil ← Proto.Datatype.Constructor.Decl.mk "nil"
  let cons ← Proto.Datatype.Constructor.Decl.mk "cons"
  let cons ← cons.addSelector "head" (← Srt.int)
  let cons ← cons.addSelectorSelf "tail"

  let decl ← Proto.Datatype.Decl.mk "Lst"
  let decl ← decl.addConstructor nil
  let decl ← decl.addConstructor cons
  let lst ← Srt.datatype decl
  println! "sort   : {lst}"

  let dt ← lst.getDatatype
  println! "ctors  : {dt.countConstructors}"
  let nilC ← dt.getConstructor "nil"
  let consC ← dt.getConstructor "cons"

  let nilT ← Term.applyConstructor (← nilC.getTerm)
  let one ← Term.applyConstructor (← consC.getTerm) #[← Term.mkInt 2, nilT]
  let two ← Term.applyConstructor (← consC.getTerm) #[← Term.mkInt 1, one]
  println! "value  : {two}"
  println! "head   : {← Term.applySelector (← (← consC.getSelector "head").getTerm) two}"
  println! "is nil : {← Term.applyTester (← nilC.getTesterTerm) two}"



/-! ## Mutual recursion

Members of a group refer to each other by name through `addSelectorUnresolved`, and the names are
resolved only by `Srt.datatypes`, which declares the whole group at once.
-/

/-- info:
sorts : #[A, B]
A     : ctors 1, isWellFounded true
B     : ctors 2
value : (mkA (mkB (mkA stop)))
-/
#guard_msgs in #eval Env.runIO do
  let mkA ← Proto.Datatype.Constructor.Decl.mk "mkA"
  let mkA ← mkA.addSelectorUnresolved "toB" "B"
  let declA ← Proto.Datatype.Decl.mk "A"
  let declA ← declA.addConstructor mkA

  let mkB ← Proto.Datatype.Constructor.Decl.mk "mkB"
  let mkB ← mkB.addSelectorUnresolved "toA" "A"
  let stop ← Proto.Datatype.Constructor.Decl.mk "stop"
  let declB ← Proto.Datatype.Decl.mk "B"
  let declB ← declB.addConstructor mkB
  let declB ← declB.addConstructor stop

  let srts ← Srt.datatypes #[declA, declB]
  println! "sorts : {srts.map toString}"

  let some srtA := srts[0]? | throwUser "no first sort"
  let some srtB := srts[1]? | throwUser "no second sort"
  let dtA ← srtA.getDatatype
  let dtB ← srtB.getDatatype
  println! "A     : ctors {dtA.countConstructors}, isWellFounded {dtA.isWellFounded}"
  println! "B     : ctors {dtB.countConstructors}"

  let stopT ← Term.applyConstructor (← (← dtB.getConstructor "stop").getTerm)
  let a ← Term.applyConstructor (← (← dtA.getConstructor "mkA").getTerm) #[stopT]
  let b ← Term.applyConstructor (← (← dtB.getConstructor "mkB").getTerm) #[a]
  let a2 ← Term.applyConstructor (← (← dtA.getConstructor "mkA").getTerm) #[b]
  println! "value : {a2}"



/-! ## Predicates on a datatype -/

/-- info:
tuple is a datatype : true / isTuple true / isRecord false
plain datatype      : isTuple false / isParametric false / isCoDatatype false
finite              : true
-/
#guard_msgs in #eval Env.runIO do
  -- a tuple *is* a datatype, which is how its components will eventually be reached
  let tup ← Srt.tuple #[← Srt.int, ← Srt.bool]
  let tupDt ← tup.getDatatype
  println! "tuple is a datatype : {tup.isDatatype} / isTuple {tupDt.isTuple} / \
isRecord {tupDt.isRecord}"

  let s ← Solver.new
  let mk ← Proto.Datatype.Constructor.Decl.mk "mk"
  let mk ← mk.addSelector "b" (← Srt.bool)
  let dt ← (← s.declareDatatype "Wrap" #[mk]).getDatatype
  println! "plain datatype      : isTuple {dt.isTuple} / isParametric {dt.isParametric} / \
isCoDatatype {dt.isCoDatatype}"
  println! "finite              : {← dt.isFinite}"
