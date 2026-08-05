module

import Cvc.Untyped.Symbols
import Cvc.Ext

import Cvc.Tests.TestBasic



namespace Cvc.Untyped.Tests variable [Ω]

open Cvc.Tests

structure MySymbols (Sym : Type → Type) where
  b1 : Sym Bool
  b2 : Sym Bool
  i1 : Sym Int
  str1 : Sym String
  seq1 : Sym (Array String)

namespace MySymbols

instance : Symbols MySymbols where
  foldM
  | {b1, b2, i1, str1, seq1}, f, init =>
    f init b1 >>= (f · b2) >>= (f · i1) >>= (f · str1) >>= (f · seq1)
  mapM
  | {b1, b2, i1, str1, seq1}, f =>
    return { b1 := ← f b1, b2 := ← f b2, i1 := ← f i1, str1 := ← f str1, seq1 := ← f seq1 }

abbrev Idents := Symbols.Idents MySymbols
abbrev Terms := Symbols.Terms MySymbols
abbrev Values := Symbols.Values MySymbols

def idents : MySymbols.Idents where
  b1 := Symbol.mk "b1"
  b2 := Symbol.mk "b2"
  i1 := Symbol.mk "i1"
  str1 := Symbol.mk "str1"
  seq1 := Symbol.mk "seq1"

end MySymbols

def idents := MySymbols.idents

/-- info:
values:
  b1 ↦ true
  b2 ↦ true
  i1 ↦ 1
  str1 ↦ neko
  seq1 ↦ #[, , , ]
-/
#test symbols.declareAndValues do
  let vars ← idents.declare
  let solver ← Solver.new
  solver.setOption "produce-models" "true"

  smt! vars.b1 ∨ 0 < - vars.i1
    >>= solver.assert

  let myAssertion ← smt! vars.b1 ∨ 0 < - vars.i1
  solver.assert myAssertion


  let myAssertion' ← smt! 1 = if vars.b2 then vars.i1 else 5 * vars.i1
  solver.assert myAssertion'

  let str1 ← smt! "ne"
  let str2 ← smt! "ko"
  let strConcat ← str1.stringConcat str2
  let constraint ← smt! vars.str1 = strConcat
  solver.assert constraint

  let seq1Len ← vars.seq1.get.seqLength
  let str1Len ← vars.str1.get.stringLength
  smt! seq1Len = str1Len >>= solver.assert

  let some {b1, b2, i1, str1, seq1} ← solver.checkSat? (ifSat := some <$> vars.getValues solver)
    | throwUser "expected sat result"

  println! "values:"
  println! "  b1 ↦ {b1.get}"
  println! "  b2 ↦ {b2.get}"
  println! "  i1 ↦ {i1.get}"
  println! "  str1 ↦ {str1.get}"
  println! "  seq1 ↦ {seq1.get}"
