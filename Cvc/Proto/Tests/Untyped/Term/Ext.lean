/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import Cvc.Proto.Untyped.Term
import Cvc.Proto.Untyped.Term.Bool
import Cvc.Proto.Types.Set

public meta import Cvc.Proto.Untyped.Term
public meta import Cvc.Proto.Untyped.Term.Bool
public meta import Cvc.Proto.Types.Set



/-! # The `smt!` DSL, sort-erased

The grammar here is *generated*: each operator's notation comes from its `op%` entry and is emitted
alongside its untyped constructor, in that operator's own theory module. `open Cvc.Proto.Untyped`
selects this layer's `smt!`, which expands to fully-qualified `Cvc.Proto.Untyped.Term.…` calls, so
nothing else has to be in scope.
-/
namespace Cvc.Proto.Tests.Untyped.Term.Ext

open Cvc
open Cvc.Proto.Untyped

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
nary or  : (or a b a)
nary eq  : (and (= i j) (= j i))
add      : (+ i j)
prec     : (+ i (* j i))
paren    : (* (+ i j) i)
unary -  : (- i)
literals : (+ 3 i)
bool lit : (and a true)
string   : "hello"
ite      : (ite a i j)
let      : (< (+ i j) i)
escape   : (+ i j)
bitvec   : (bvadd u u)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto.Untyped.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto.Untyped.Term.mkSymbolAs Int "j"
  let u ← Cvc.Proto.Untyped.Term.mkSymbolAs (BitVec 4) "u"

  println! "and      : {← smt! a ∧ b}"
  println! "or       : {← smt! a ∨ b}"
  println! "xor      : {← smt! a ⊻ b}"
  println! "implies  : {← smt! a → b}"
  println! "not      : {← smt! ¬ a}"
  println! "nested   : {← smt! ¬ (a ∨ b)}"
  println! "equal    : {← smt! i = j}"
  println! "distinct : {← smt! i ≠ j}"
  println! "nary and : {← smt! ∧[a, b, a]}"
  println! "nary or  : {← smt! ∨[a, b, a]}"
  println! "nary eq  : {← smt! =[i, j, i]}"
  println! "add      : {← smt! i + j}"
  println! "prec     : {← smt! i + j * i}"
  println! "paren    : {← smt! (i + j) * i}"
  println! "unary -  : {← smt! - i}"
  println! "literals : {← smt! 3 + i}"
  println! "bool lit : {← smt! a ∧ true}"
  println! "string   : {← smt! "hello"}"
  println! "ite      : {← smt! if a then i else j}"
  println! "let      : {← smt! let x ← i + j; x < i}"
  println! "escape   : {← smt! ![Cvc.Proto.Untyped.Term.add i j]}"
  println! "bitvec   : {← smt! ![Cvc.Proto.Untyped.Term.bvAdd u u]}"

-- associativity follows the `op%` entry: `∧` is `infixr`, `-` is `infixl`
/-- info:
right-assoc ∧ : (and a (and b a))
left-assoc  - : (- (- i j) i)
-/
#guard_msgs in #eval Env.runIO do
  let a ← Cvc.Proto.Untyped.Term.mkSymbolAs Bool "a"
  let b ← Cvc.Proto.Untyped.Term.mkSymbolAs Bool "b"
  let i ← Cvc.Proto.Untyped.Term.mkSymbolAs Int "i"
  let j ← Cvc.Proto.Untyped.Term.mkSymbolAs Int "j"
  println! "right-assoc ∧ : {← smt! a ∧ b ∧ a}"
  println! "left-assoc  - : {← smt! i - j - i}"

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
  let i ← Cvc.Proto.Untyped.Term.mkSymbolAs Int "i"
  let s ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.Set Int) "s"
  let t ← Cvc.Proto.Untyped.Term.mkSymbolAs (Cvc.Proto.Set Int) "t"
  let q ← Cvc.Proto.Untyped.Term.mkSymbolAs (Array Int) "q"
  let r ← Cvc.Proto.Untyped.Term.mkSymbolAs (Array Int) "r"

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
