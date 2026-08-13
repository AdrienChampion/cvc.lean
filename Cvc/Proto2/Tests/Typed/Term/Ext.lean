/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto2.Typed.Term
import Cvc.Proto2.Typed.Term.Bool
import Cvc.Proto2.Types.Set
-- the `match` notation expands to `Cvc.Proto2.Typed.…` names that live here, and a macro's names
-- resolve at the use site
import Cvc.Proto2.Typed.Datatype

public meta import Cvc.Proto2.Typed.Datatype
public meta import Cvc.Proto2.Typed.Term
public meta import Cvc.Proto2.Typed.Term.Bool
public meta import Cvc.Proto2.Types.Set



/-! # The `smt!` DSL, typed

Same generated grammar as the sort-erased layer — it is emitted once, alongside the untyped
constructors, and inherited here because a typed theory module imports its untyped counterpart.
Only the expansion differs: `open Cvc.Proto2.Typed` selects a `smt!` that expands to
fully-qualified `Cvc.Proto2.Typed.Term.…` calls, so the resulting terms carry their Lean index.
-/
namespace Cvc.Proto2.Tests.Typed.Term.Ext

open Cvc
open Cvc.Proto2.Typed

/-- info:
and      : (and a b)
or       : (or a b)
xor      : (xor a b)
implies  : (=> a b)
not      : (not a)
nested   : (not (or a b))
equal    : (= i j)
distinct : (distinct i j)
nary and : (and a b a)
nary eq  : (and (= i j) (= j i))
add      : (+ i j)
prec     : (+ i (* j i))
paren    : (* (+ i j) i)
unary -  : (- i)
rat neg  : (- r)
literals : (+ 3 i)
bool lit : (and a true)
compare  : (< i j)
ite      : (ite a i j)
let      : (< (+ i j) i)
escape   : (+ i j)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto2.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto2.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto2.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto2.Typed.Term.mkSymbolAs Int "j"
  let r ← Cvc.Proto2.Typed.Term.mkSymbolAs Rat "r"

  println! "and      : {← smt! a ∧ b}"
  println! "or       : {← smt! a ∨ b}"
  println! "xor      : {← smt! a ⊻ b}"
  println! "implies  : {← smt! a → b}"
  println! "not      : {← smt! ¬ a}"
  println! "nested   : {← smt! ¬ (a ∨ b)}"
  println! "equal    : {← smt! i = j}"
  println! "distinct : {← smt! i ≠ j}"
  println! "nary and : {← smt! ∧[a, b, a]}"
  println! "nary eq  : {← smt! =[i, j, i]}"
  println! "add      : {← smt! i + j}"
  println! "prec     : {← smt! i + j * i}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "unary -  : {← smt! - i}"
  println! "rat neg  : {← smt! - r}"
  println! "literals : {← smt! 3 + i}"
  println! "bool lit : {← smt! a ∧ true}"
  println! "compare  : {← smt! i < j}"
  println! "ite      : {← smt! if a then i else j}"
  println! "let      : {← smt! let x ← i + j; x < i}"
  println! "escape   : {← smt! ![Cvc.Proto2.Typed.Term.add i j]}"

-- associativity follows the `op%` entry: `∧` is `infixr`, `-` is `infixl`
/-- info:
right-assoc ∧ : (and a (and b a))
left-assoc  - : (- (- i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto2.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto2.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto2.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto2.Typed.Term.mkSymbolAs Int "j"
  println! "right-assoc ∧ : {← smt! a ∧ b ∧ a}"
  println! "left-assoc  - : {← smt! i - j - i}"



/-! ## The DSL carries the typed index

Each of these pins the index the expansion produces. They typecheck by delegation, with no
coercion.
-/

section indices
variable [Ω] (a b : Term Bool) (i j : Term Int) (r : Term Rat) (u v : Term (BitVec 4))

/-- A connective stays at `Bool`. -/
example : Env (Term Bool) := smt! a ∧ b
/-- A comparison drops from `Int` to `Bool`. -/
example : Env (Term Bool) := smt! i < j
/-- Arithmetic stays at its operands' index. -/
example : Env (Term Int) := smt! i + j * i
/-- …including over the reals. -/
example : Env (Term Rat) := smt! - r
/-- `ite` takes its index from its branches. -/
example : Env (Term Int) := smt! if a then i else j
/-- A `let` binding is indexed too. -/
example : Env (Term Bool) := smt! let x ← i + j; x < i
/-- An n-ary equality over `Int` still lands in `Bool`. -/
example : Env (Term Bool) := smt! =[i, j, i]
/-- Escaping keeps whatever index the Lean term has. -/
example : Env (Term (BitVec 4)) := smt! ![Cvc.Proto2.Typed.Term.bvAdd u v]

end indices

/-! ## Notation from the container theories

`∈`, `⊆`, `∪`, `∩`, `∖` and `++` come from the `op%` entries of the set and sequence theories, so
their grammar is compiled with those theories rather than with the DSL.
-/

/-- info:
member    : (set.member i s)
subset    : (set.subset s t)
union     : (set.union s t)
inter     : (set.inter s t)
minus     : (set.minus s t)
union prec: (set.union s (set.inter t s))
unionN    : (set.union (set.union s t) s)
interN    : (set.inter (set.inter s t) s)
seq concat: (seq.++ q r)
concatN   : (seq.++ q r q)
mixed     : (and (set.member i s) (set.subset s t))
-/
#guard_msgs in #eval Env.runIO do
  let i ← Cvc.Proto2.Typed.Term.mkSymbolAs Int "i"
  let s ← Cvc.Proto2.Typed.Term.mkSymbolAs (Cvc.Proto2.Set Int) "s"
  let t ← Cvc.Proto2.Typed.Term.mkSymbolAs (Cvc.Proto2.Set Int) "t"
  let q ← Cvc.Proto2.Typed.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Proto2.Typed.Term.mkSymbolAs (Array Int) "r"

  println! "member    : {← smt! i ∈ s}"
  println! "subset    : {← smt! s ⊆ t}"
  println! "union     : {← smt! s ∪ t}"
  println! "inter     : {← smt! s ∩ t}"
  println! "minus     : {← smt! s ∖ t}"
  println! "union prec: {← smt! s ∪ t ∩ s}"
  println! "unionN    : {← smt! ∪[s, t, s]}"
  println! "interN    : {← smt! ∩[s, t, s]}"
  println! "seq concat: {← smt! q ++ r}"
  println! "concatN   : {← smt! ++[q, r, q]}"
  println! "mixed     : {← smt! (i ∈ s) ∧ (s ⊆ t)}"



/-! ## Matching

The same notation as the sort-erased layer, expanding to `Datatype.Ctor.caseErased`, which checks
the arity and the variables' sorts. Each variable's **index is inferred from the body**, so a match
reads exactly as it does sort-erased while every bound variable carries its Lean type.

Every field is bound sort-erased, at the sort the declaration gives it, and only the ones the body
mentions are re-typed. So a field the body ignores — the tail of a list, most of the time —
costs nothing, though it has no index to infer one from.

A variable may state its sort, `| cons (h : Int) t => …`, which then becomes a check against the
declaration. That is what a variable the body mentions in a position that does not pin its index
down needs.
-/

/-- The Lean index standing for the SMT datatype `Lst`. -/
structure Lst where private mk ::
  deriving DecidableEq, Ord, Hashable

instance : ToTyp Lst := ⟨.datatype "Lst"⟩

/-- Declares the datatype the `Lst` index names, `nil | cons (head : Int) (tail : Lst)`. -/
def declareLst [Ω] : Env Srt := do
  let nil ← Cvc.Proto2.Datatype.Constructor.Decl.mk "nil"
  let cons ← Cvc.Proto2.Datatype.Constructor.Decl.mk "cons"
  let cons ← (← cons.addSelector "head" (← Srt.int)).addSelectorSelf "tail"
  let decl ← Cvc.Proto2.Datatype.Decl.mk "Lst"
  Srt.datatype (← (← decl.addConstructor nil).addConstructor cons)

/-- info:
match     : (match l (((cons h t) (+ (* h 2) 1)) (nil 0)))
head of l : 15
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  s.setOption "produce-models" "true"
  let _ ← declareLst
  let l ← s.declareConst Lst "l"

  -- `h` is a `Term Int` in the body, so the arithmetic operators apply and the match is `Term Int`;
  -- `t` is never mentioned and needs no index
  let m ← smt!
    match l with
    | cons h t => h * 2 + 1
    | nil => 0
  println! "match     : {m.erase}"

  let consC ← Datatype.ctor Lst "cons"
  let seven ← consC.apply2 (← Term.mkInt 7) (← (← Datatype.ctor Lst "nil").apply)
  (do Term.equal l seven) >>= s.assert
  s.checkSat (ifSat := do println! "head of l : {← s.getValue m}")

/-- info:
catch-all : (match l (((cons h t) h) (_ 0)))
nested    : (match l (((cons h t) (match t (((cons h t) h) (_ 0)))) (_ 0)))
ascribed  : (match l (((cons h t) (+ h 1)) (_ 0)))
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declareLst
  let l ← s.declareConst Lst "l"

  -- the index is stated here because nothing else says what it should be: the body is just `h`,
  -- so it takes the match's own expected type to pin it down
  let anyCase : Term Int ← smt!
    match l with
    | cons h t => h
    | _ => 0
  println! "catch-all : {anyCase.erase}"

  -- `t` states its index because the only thing mentioning it is the match that wants it; the
  -- inner `h` states its own because its index reaches it only through the outer match's expected
  -- type, which does not survive the nesting. The outer `h` states nothing and needs nothing: the
  -- inner pattern shadows it, so it is never referenced
  let nested : Term Int ← smt!
    match l with
    | cons h (t : Lst) =>
      match t with
      | cons (h : Int) t => h
      | _ => 0
    | _ => 0
  println! "nested    : {nested.erase}"

  -- an ascription is a check against the declaration
  println! "ascribed  : {(← smt!
    match l with
    | cons (h : Int) t => h + 1
    | _ => 0).erase}"

/-! The index a match carries, and what it rejects. -/

section indices
variable [Ω] (l : Term Lst) (b : Term Bool)

/-- A match answers at the index its bodies share. -/
example : Env (Term Int) := smt! match l with | cons h t => h | _ => 0
/-- …including at `Bool`. -/
example : Env (Term Bool) := smt! match l with | cons h t => ![pure b] | _ => true

-- a variable the body mentions is re-typed, so using it at the wrong index is a type error
/-- error: Application type mismatch: The argument
  smtArg0✝
has type
  Datatype.Case Lst Bool
but is expected to have type
  Datatype.Case Lst Int
in the application
  List.cons smtArg0✝
-/
#guard_msgs in
example : Env (Term Int) := smt! match l with | cons (h : Bool) t => h | _ => 0

end indices

/-- info:
wrong sort : caught: cannot type the following term as `Lst`, term has sort `Int`:
h
wrong width: caught: constructor `cons` takes 2 field(s), bound 1
-/
#guard_msgs in #eval Env.runIO do
  let s ← Solver.new
  let _ ← declareLst
  let l ← s.declareConst Lst "l"
  let caught (code : Env String) : Env String := try code catch e => pure s!"caught: {e}"

  -- an ascription disagreeing with the declaration is caught where the variable is re-typed
  println! "wrong sort : {← caught do pure s!"{(← smt!
    match l with
    | cons (h : Lst) t => 0
    | _ => 0).erase}"}"
  println! "wrong width: {← caught do pure s!"{(← smt!
    match l with
    | cons h => h
    | _ => 0).erase}"}"
