module

import Cvc.Typed.Types.Array

import Cvc.Tests.TestBasic



namespace Cvc.Typed.Tests

/-- info:
((as const (Array Bool Int)) 7)
→ { _ ↦ 7 }
(store ((as const (Array Bool Int)) 7) true 13)
→ { true ↦ 13, _ ↦ 7 }
(store (store ((as const (Array Bool Int)) 7) true 13) false 5)
→ { false ↦ 5, true ↦ 13, _ ↦ 7 }
(store (store (store ((as const (Array Bool Int)) 7) true 13) false 5) true 7)
→ { false ↦ 5, true ↦ 7, _ ↦ 7 }
-/
#test basic.array.creation do
  let five ← Term.mkInt 5
  let seven ← Term.mkInt 7
  let thirteen ← Term.mkInt 13
  let tru ← Term.mkValue true
  let fls ← Term.mkValue false

  let array : Term (TotalMap Bool Int) ← Term.mkArrayFrom Bool (default := seven)
  println! "{array}"
  println! "→ {← array.getValue}"
  let array ← array.store tru thirteen
  println! "{array}"
  println! "→ {← array.getValue}"
  let array ← array.store fls five
  println! "{array}"
  println! "→ {← array.getValue}"
  let array ← array.store tru seven
  println! "{array}"
  println! "→ {← array.getValue}"
