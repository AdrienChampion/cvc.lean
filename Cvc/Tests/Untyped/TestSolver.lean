module

import Cvc.Untyped.Term
import Cvc.Untyped.Solver

import Cvc.Tests.TestBasic



namespace Cvc.Untyped.Tests



/--
info: s1 : (Seq Int) := s1
→ (seq.++ (seq.unit 0) (seq.unit 1) (seq.unit 2))
→ #[0, 1, 2]
-/
#test array.getValue do
  let solver ← Solver.new
  solver.setOption "produce-models" "true"
  -- let bool ← Srt.bool
  let int ← Srt.int
  let seqBool ← int.seq
  let s1 ← Term.mkSymbol "s1" seqBool
  println! "s1 : {← s1.getSort} := {s1}"
  let i0 ← Term.mkValue 0
  let i1 ← Term.mkValue 1
  let i2 ← Term.mkValue 2
  -- let tru ← Term.mkValue true
  -- let fls ← Term.mkValue false
  let atEq (idx val : Term) : Env Term := do
    let tAt ← s1.seqAt idx
    val.unitSeq >>= tAt.equal
  atEq i0 i0 >>= solver.assert
  atEq i1 i1 >>= solver.assert
  atEq i2 i2 >>= solver.assert
  let val ← solver.checkSat (ifSat := do
    let value ← solver.getValue s1
    return value)
  println! "→ {val}"
  let v ← val.getSeqValue (α := Int)
  println! "→ {v}"
