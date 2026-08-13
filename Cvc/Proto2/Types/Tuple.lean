/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

import all Cvc.Proto2.Srt

public import Cvc.Proto2.Srt



namespace Cvc.Proto2 public section

namespace Typ

/-- Whether a sort is a single tuple component rather than a tuple of its own.

`Srt.prod` flattens to the right, so a product cannot be a tuple's *last* component: its own
components would flatten into the tuple being built. This is what the typed tuple constructor
checks.
-/
abbrev isFlat : Typ → Bool
  | prod _ => false
  | bool | int | real | string | regex | roundingMode
  | bitVec _ | float _ _ | finiteField _ | arrayTo _ _
  | bag _ | set _ | seq _ | nullable _
  | datatype _ | abstract _ | function _ _ => true

end Typ

namespace Srt

/-- The product of two sorts, flattening to the right.

`expose`d so the body crosses a plain `import`: the typed tuple constructor checks its last
component's index by reduction, and cannot if this stays opaque.
-/
@[expose]
def prod (α : Typ) : (β : Typ) → Typ
  | .prod args => .prod (α :: args)
  | β => .prod [α, β]

instance [A : ToTyp α] [B : ToTyp β] : ToTyp (α × β) where
  typ := Srt.prod A.typ B.typ

end Srt
