/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Typed.Term
import Cvc.Proto.Typed.Term.Bool
import Cvc.Proto.Types.Set

public meta import Cvc.Proto.Typed.Term
public meta import Cvc.Proto.Typed.Term.Bool
public meta import Cvc.Proto.Types.Set



/-! # The `smt!` DSL, typed

Same generated grammar as the sort-erased layer — it is emitted once, alongside the untyped
constructors, and inherited here because a typed theory module imports its untyped counterpart.
Only the expansion differs: `open Cvc.Proto.Typed` selects a `smt!` that expands to
fully-qualified `Cvc.Proto.Typed.Term.…` calls, so the resulting terms carry their Lean index.
-/
namespace Cvc.Proto.Tests.Typed.Term.Ext

open Cvc
open Cvc.Proto.Typed

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
  let a ← Cvc.Proto.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto.Typed.Term.mkSymbolAs Int "j"
  let r ← Cvc.Proto.Typed.Term.mkSymbolAs Rat "r"

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
  println! "escape   : {← smt! ![Cvc.Proto.Typed.Term.add i j]}"

-- associativity follows the `op%` entry: `∧` is `infixr`, `-` is `infixl`
/-- info:
right-assoc ∧ : (and a (and b a))
left-assoc  - : (- (- i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto.Typed.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto.Typed.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto.Typed.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto.Typed.Term.mkSymbolAs Int "j"
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
example : Env (Term (BitVec 4)) := smt! ![Cvc.Proto.Typed.Term.bvAdd u v]

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
  let i ← Cvc.Proto.Typed.Term.mkSymbolAs Int "i"
  let s ← Cvc.Proto.Typed.Term.mkSymbolAs (Cvc.Proto.Set Int) "s"
  let t ← Cvc.Proto.Typed.Term.mkSymbolAs (Cvc.Proto.Set Int) "t"
  let q ← Cvc.Proto.Typed.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Proto.Typed.Term.mkSymbolAs (Array Int) "r"

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
