/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto.Defs
public import Cvc.Proto.Ext



/-! # The sort-erased term type

A term carries no sort on the Lean side: it is exactly a cvc5 term, so the wrapper is a zero-cost
`def` and the conversions either way are `id`. `wrap3%` derives the comparison and printing
instances from the underlying type.

`Cvc.Proto.Untyped.Term` names both this type and the namespace holding the generated
constructors. Being a *declaration* as well as a namespace is what lets a typed generation site
write

```lean
open Cvc.Proto renaming Untyped.Term → T
```

and have the generator's `T.<id>` delegation resolve.
-/
namespace Cvc.Proto.Untyped public section variable [Ω]

wrap3% Term ← cvc5.Term

/-- An array of sort-erased terms. -/
abbrev Terms := Array Term

namespace Terms

private def toUnsafe : Terms → Array cvc5.Term := id
private def ofUnsafe : Array cvc5.Term → Terms := id

private example (ts : Terms) : ofUnsafe ts.toUnsafe = ts := rfl

end Terms

/-- Sort-erased `smt!`.

`scoped`, so that `open Cvc.Proto.Untyped` selects this layer's DSL. It forwards to `smtU!`, which
expands to fully-qualified `Cvc.Proto.Untyped.Term.…` calls; nothing needs to be in scope.
-/
scoped syntax "smt! " ppLine group(colGt protoSmtTerm) : term

macro_rules | `(smt! $t:protoSmtTerm) => `(smtU! $t)
