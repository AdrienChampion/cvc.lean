module

import Cvc.Untyped.Types.Array

import Cvc.Tests.TestBasic



namespace Cvc.Untyped.Tests

/-- info:
((as const (Array Bool Int)) 7)
→ { _ ↦ 7 }
(store ((as const (Array Bool Int)) 7) true 13)
→ { true ↦ 13, _ ↦ 7 }
(store (store ((as const (Array Bool Int)) 7) true 13) false 5)
→ { true ↦ 13, false ↦ 5, _ ↦ 7 }
(store (store (store ((as const (Array Bool Int)) 7) true 13) false 5) true 7)
→ { true ↦ 7, false ↦ 5, _ ↦ 7 }
→ { false ↦ 5, true ↦ 7, _ ↦ 7 }
-/
#test basic.array.creation do
  let int ← Srt.int
  let bool ← Srt.bool
  let five ← Term.mkInt 5
  let seven ← Term.mkInt 7
  let thirteen ← Term.mkInt 13
  let tru ← Term.mkValue true
  let fls ← Term.mkValue false
  let arraySrt ← bool.arrayTo int
  let array ← Term.mkArray arraySrt (default := seven)
  println! "{array}"
  println! "→ {← array.getArrayValue}"
  let array ← array.store tru thirteen
  println! "{array}"
  println! "→ {← array.getArrayValue}"
  let array ← array.store fls five
  println! "{array}"
  println! "→ {← array.getArrayValue}"
  let array ← array.store tru seven
  println! "{array}"
  let arrayValue ← array.getArrayValue
  println! "→ {arrayValue}"
  let tMap ← arrayValue.termsToValues Bool Int
  println! "→ {tMap}"
