/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto2.Typed.Term
import Cvc.Proto2.Typed.Solver

public meta import Cvc.Proto2.Typed.Term
public meta import Cvc.Proto2.Typed.Solver



/-! # Relations, typed

A relation is indexed by `Rel α β`: a set of tuples with components `α ++ [β]`. Splitting the last
component off is what makes it matchable, so `relJoin`'s "drop the left's last, drop the right's
first" is unification rather than a type-level program.

This module imports `Typed.Term` plainly, **not** `import all`, so `Term`'s index is opaque here
exactly as it is for a user. That is what makes the rejections below meaningful.
-/
namespace Cvc.Proto2.Tests.Typed.Term.Relation

open Cvc
open Cvc.Proto2
open Cvc.Proto2.Typed (Term Solver)
open Cvc.Proto2.Typed.Term



/-! ## The index says what the sort is

Each line prints the sort a term has beside the sort its index claims. The last two are the point
of the encoding: a nested tuple stays nested, where a product index would have flattened it.
-/

/-- info:
Rel [] Int          : (Set (Tuple Int))
Rel [Int] Bool      : (Set (Tuple Int Bool))
Rel [Int, Bool] Rat : (Set (Tuple Int Bool Real))
Tup [Int] (Tup [Bool] Rat) : (Tuple Int (Tuple Bool Real))
Rel [Int] (Tup [Bool] Rat) : (Set (Tuple Int (Tuple Bool Real)))
-/
#guard_msgs in #eval Env.runIO do
  println! "Rel [] Int          : {← (Srt.of (Rel [] Int) : Env Srt)}"
  println! "Rel [Int] Bool      : {← (Srt.of (Rel [Int] Bool) : Env Srt)}"
  println! "Rel [Int, Bool] Rat : {← (Srt.of (Rel [Int, Bool] Rat) : Env Srt)}"
  println! "Tup [Int] (Tup [Bool] Rat) : {← (Srt.of (Tup [Int] (Tup [Bool] Rat)) : Env Srt)}"
  println! "Rel [Int] (Tup [Bool] Rat) : {← (Srt.of (Rel [Int] (Tup [Bool] Rat)) : Env Srt)}"



/-! ## Relational operators

The claimed index and the sort agree at every arity.
-/

/-- info:
join      : (Set (Tuple Int Bool String Bool))
product   : (Set (Tuple Int Bool Real Real String Bool))
transpose : (Set (Tuple Real Bool Int))
tclosure  : (Set (Tuple Int Int))
iden      : (Set (Tuple Int Int))
joinImage : (Set (Tuple Int))
group     : (Set (Set (Tuple Int Bool Real)))
-/
#guard_msgs in #eval Env.runIO do
  let sortOf (t : Untyped.Term) : Env String := do return s!"{← t.getSort}"
  let s ← Solver.new
  let abc ← s.declareConst (Rel [Int, Bool] Rat) "A"
  let cde ← s.declareConst (Rel [Rat, String] Bool) "B"
  let rr ← s.declareConst (Rel [Int] Int) "R"
  let u ← s.declareConst (Rel [] Int) "U"

  println! "join      : {← sortOf (← relJoin abc cde).erase}"
  println! "product   : {← sortOf (← relProduct abc cde).erase}"
  println! "transpose : {← sortOf (← relTranspose abc).erase}"
  println! "tclosure  : {← sortOf (← relTclosure rr).erase}"
  println! "iden      : {← sortOf (← relIden u).erase}"
  println! "joinImage : {← sortOf (← relJoinImage rr (← mkInt 2)).erase}"
  println! "group     : {← sortOf (← relGroup #[0] abc).erase}"

section indices
variable [Ω]
  (ab  : Term (Rel [Int] Bool)) (bc : Term (Rel [Bool] Rat))
  (abc : Term (Rel [Int, Bool] Rat)) (cde : Term (Rel [Rat, String] Bool))
  (u : Term (Rel [] Int)) (n : Term Int)

/-- Join drops the shared component from both sides. -/
example : Env (Term (Rel [Int] Rat)) := relJoin ab bc
/-- …at any arity. -/
example : Env (Term (Rel [Int, Bool, String] Bool)) := relJoin abc cde
/-- Product appends. -/
example : Env (Term (Rel [Int, Bool, Rat, Rat, String] Bool)) := relProduct abc cde
/-- Transpose reverses. -/
example : Env (Term (Rel [Rat, Bool] Int)) := relTranspose abc
/-- `Rel [] α` is the unary relation, so identity needs no separate one-tuple type. -/
example : Env (Term (Rel [Int] Int)) := relIden u
/-- Join image answers a unary relation. -/
example : Env (Term (Rel [] Int)) := relJoinImage ab n

-- non-joinable relations are rejected: `Bool :: ?α'` cannot match `[Rat, String]`
#guard_msgs(drop error) in example := relJoin ab cde
-- and a wrong result index is rejected too
#guard_msgs(drop error) in
example : Env (Term (Rel [Int, Bool, Rat, String] Bool)) := relProduct abc cde

end indices



/-! ## The set operators, at a relation's index

A relation never has to be read as a set to be built or constrained.
-/

/-- info:
member    : Bool
union     : (Set (Tuple Int Bool))
insert    : (Set (Tuple Int Bool))
card      : Int
choose    : (Tuple Int Bool)
empty     : (Set (Tuple Int Bool))
singleton : (Set (Tuple Int Bool))
-/
#guard_msgs in #eval Env.runIO do
  let sortOf (t : Untyped.Term) : Env String := do return s!"{← t.getSort}"
  let s ← Solver.new
  let a ← s.declareConst (Rel [Int] Bool) "A"
  let b ← s.declareConst (Rel [Int] Bool) "B"
  let pair ← mkTup (.cons (← mkInt 1) (.last (← mkTrue)))

  println! "member    : {← sortOf (← relMember pair a).erase}"
  println! "union     : {← sortOf (← relUnion a b).erase}"
  println! "insert    : {← sortOf (← relInsert pair a).erase}"
  println! "card      : {← sortOf (← relCard a).erase}"
  println! "choose    : {← sortOf (← relChoose a).erase}"
  let empty : Term (Rel [Int] Bool) ← relEmpty
  println! "empty     : {← sortOf empty.erase}"
  println! "singleton : {← sortOf (← relSingleton pair).erase}"



/-! ## Solving -/

/-- info:
1,true ∈ singleton : unsat (so it is a member)
join ⊆ product     : unsat
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let pair ← mkTup (.cons (← mkInt 1) (.last (← mkTrue)))
  let single ← relSingleton pair
  (do not (← relMember pair single)) >>= s.assert
  println! "1,true ∈ singleton : {if ← s.checkIsSat then "SAT" else "unsat (so it is a member)"}"

  let s2 ← Solver.new
  let a ← s2.declareConst (Rel [Int] Bool) "A"
  let b ← s2.declareConst (Rel [Bool] Rat) "B"
  let joined ← relTableJoin #[(1, 0)] a b
  let product ← relProduct a b
  (do not (← relSubset joined product)) >>= s2.assert
  println! "join ⊆ product     : {if ← s2.checkIsSat then "SAT" else "unsat"}"



/-! ## Reading a tuple apart

`mkTup` builds one; these read it. The index is a list, so a position is either a constructor
pattern (`tupFst`) or a computed length (`tupLast`) — no type-level program, and no side condition.
-/

/-- info:
tuple    : (Tuple Int Bool Real)
tupFst   : ((_ tuple.select 0) (tuple 1 true (/ 1 2))) : Int
tupLast  : ((_ tuple.select 2) (tuple 1 true (/ 1 2))) : Real
tupRest  : ((_ tuple.project 1 2) (tuple 1 true (/ 1 2))) : (Tuple Bool Real)
rest.fst : Bool
rest.last: Real
-/
#guard_msgs in #eval Env.runIO do
  let t : Term (Tup [Int, Bool] Rat) ←
    mkTup (.cons (← mkInt 1) (.cons (← mkTrue) (.last (← mkReal (1/2 : Rat)))))
  println! "tuple    : {← t.erase.getSort}"
  println! "tupFst   : {(← tupFst t).erase} : {← (← tupFst t).erase.getSort}"
  println! "tupLast  : {(← tupLast t).erase} : {← (← tupLast t).erase.getSort}"
  let rest ← tupRest t
  println! "tupRest  : {rest.erase} : {← rest.erase.getSort}"
  -- composing reaches a middle component
  println! "rest.fst : {← (← tupFst rest).erase.getSort}"
  println! "rest.last: {← (← tupLast rest).erase.getSort}"

/-! A one-component tuple has no first-and-rest, only a last — which `tupLast` gives, at position
zero.
-/

/-- info: single : ((_ tuple.select 0) (tuple 7)) : Int -/
#guard_msgs in #eval Env.runIO do
  let t : Term (Tup [] Int) ← mkTup (.last (← mkInt 7))
  println! "single : {(← tupLast t).erase} : {← (← tupLast t).erase.getSort}"

section indices
variable [Ω] (t : Term (Tup [Int, Bool] Rat)) (single : Term (Tup [] Int))

/-- The first component's index comes from the head of the list. -/
example : Env (Term Int) := tupFst t
/-- The last one's from the split-off `β`. -/
example : Env (Term Rat) := tupLast t
/-- The rest is a tuple one component shorter. -/
example : Env (Term (Tup [Bool] Rat)) := tupRest t
/-- Composing reaches the middle. -/
example : Env (Term Bool) := do tupFst (← tupRest t)
/-- A one-component tuple has only a last. -/
example : Env (Term Int) := tupLast single

-- `tupFst` needs a component before the last, so a one-component tuple is rejected
#guard_msgs(drop error) in example := tupFst single

end indices

/-! The components really are what the indices claim: a model reads each back. -/

/-- info:
fst  : 1
last : 2
mid  : true
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let t : Term (Tup [Int, Bool] Rat) ←
    mkTup (.cons (← mkInt 1) (.cons (← mkTrue) (.last (← mkReal (2/1 : Rat)))))
  let fst ← tupFst t
  let last ← tupLast t
  let mid ← tupFst (← tupRest t)
  s.checkSat (ifSat := do
    println! "fst  : {← s.getValue fst}"
    println! "last : {← s.getValue last}"
    println! "mid  : {← s.getValue mid}")



/-! ## Aggregating

`relAggregate` folds each group into one value, so its answer is a `Set gamma` — the accumulator's
index, not the relation's. `gamma` is fixed by `init` and by the folding function's codomain
together, and the function is an ordinary term of arrow index, which `BVars.lambda` builds.
-/

section aggregate
open Cvc.Proto2.Typed (BVar BVars)

/-- Sums a relation's first component, taking the accumulator second, as `relAggregate` wants. -/
def sumFst [Ω] : Env (Term (Tup [Int] Bool → Int → Int)) := do
  let t ← BVar.mk (α := Tup [Int] Bool) "t"
  let acc ← BVar.mk (α := Int) "acc"
  BVars.lambda (BVars.push acc (BVars.push t [])) (← add (← tupFst t.toTerm) acc.toTerm)

/-- info:
f       : (-> (Tuple Int Bool) Int Int)
aggr    : (Set Int)
aggrAll : (Set Int)
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let a ← s.declareConst (Rel [Int] Bool) "A"
  let f ← sumFst
  let zero ← mkInt 0
  println! "f       : {← f.erase.getSort}"
  println! "aggr    : {← (← relAggregate #[1] f zero a).erase.getSort}"
  -- with no index every tuple is in one group, which is a fold over the whole relation
  println! "aggrAll : {← (← relAggregate #[] f zero a).erase.getSort}"

section indices
variable [Ω]
  (f : Term (Tup [Int] Bool → Int → Int)) (zero : Term Int) (a : Term (Rel [Int] Bool))

/-- The result is a set of accumulators, not of tuples. -/
example : Env (Term (Set Int)) := relAggregate #[1] f zero a

-- the folding function's domain is the relation's tuple, so another relation is rejected
#guard_msgs(drop error) in
example [Ω] (b : Term (Rel [Bool] Int)) := relAggregate #[1] f zero b

-- and `init` has the accumulator's index, not the tuple's
#guard_msgs(drop error) in
example [Ω] (t : Term (Tup [Int] Bool)) := relAggregate #[1] f t a

end indices

/-! The fold really runs: `{(1, true), (2, true), (10, false)}` sums to `3` and `10` grouped by its
second component, and to `13` ungrouped.
-/

/-- info:
aggr    : { 3, 10 }
aggrAll : { 13 }
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let a ← s.declareConst (Rel [Int] Bool) "A"
  let f ← sumFst
  let zero ← mkInt 0
  let aggr ← relAggregate #[1] f zero a
  let aggrAll ← relAggregate #[] f zero a

  let tuple (i : Int) (b : Bool) : Env (Term (Rel [Int] Bool)) := do
    relSingleton (← mkTup (.cons (← mkInt i) (.last (← mkBool b))))
  let value ← relUnion (← tuple 1 true) (← relUnion (← tuple 2 true) (← tuple 10 false))
  (do equal a value) >>= s.assert

  s.checkSat (ifSat := do
    println! "aggr    : {← s.getValue aggr}"
    println! "aggrAll : {← s.getValue aggrAll}")

end aggregate



/-! ## The n-ary spellings

`relUnionN`, `relInterN` and `relMinusN` are the set operators' n-ary variants at a relation's
index, carrying the same `2 ≤ size` autoparam. The array is homogeneous, so the index is the one
every element shares.
-/

/-- info:
unionN : (Set (Tuple Int Bool))
interN : (Set (Tuple Int Bool))
minusN : (Set (Tuple Int Bool))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let a ← s.declareConst (Rel [Int] Bool) "A"
  let b ← s.declareConst (Rel [Int] Bool) "B"
  let c ← s.declareConst (Rel [Int] Bool) "C"
  println! "unionN : {← (← relUnionN #[a, b, c]).erase.getSort}"
  println! "interN : {← (← relInterN #[a, b, c]).erase.getSort}"
  println! "minusN : {← (← relMinusN #[a, b, c]).erase.getSort}"

section indices
variable [Ω] (a b : Term (Rel [Int] Bool)) (r : Term (Rel [Bool] Int))

/-- The result is a relation at the shared index. -/
example : Env (Term (Rel [Int] Bool)) := relUnionN #[a, b]

-- fewer than two elements: the autoparam has nothing to prove it from
#guard_msgs(drop error) in example := relUnionN #[a]

-- and the array is homogeneous, so a relation of another shape does not belong in it
#guard_msgs(drop error) in example := relUnionN #[a, r]

end indices

/-! Three relations really are unioned, not two — which the cardinality shows, a relation itself
having no value conversion to read back.
-/

/-- info:
card of unionN #[a, b, c] : 3
card of unionN #[a, b]    : 2
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let tuple (i : Int) (b : Bool) : Env (Term (Rel [Int] Bool)) := do
    relSingleton (← mkTup (.cons (← mkInt i) (.last (← mkBool b))))
  let (a, b, c) := (← tuple 1 true, ← tuple 2 true, ← tuple 3 false)
  let three ← relCard (← relUnionN #[a, b, c])
  let two ← relCard (← relUnionN #[a, b])
  s.checkSat (ifSat := do
    println! "card of unionN #[a, b, c] : {← s.getValue three}"
    println! "card of unionN #[a, b]    : {← s.getValue two}")
