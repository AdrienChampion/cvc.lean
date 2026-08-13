/-
Copyright (c) 2026 by the authors listed in the file AUTHORS and their
institutional affiliations. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Adrien Champion
-/

module

public import Cvc.Proto2.Defs
public import Cvc.Proto2.Srt
public import Cvc.Proto2.Types
public import Cvc.Proto2.Spec
public import Cvc.Proto2.Gen
public import Cvc.Proto2.Ext
public import Cvc.Proto2.Untyped
public import Cvc.Proto2.Typed



/-! # Generating term constructors from a single specification

A term constructor is described once, in the typed form, by an `op%` entry under
`Cvc/Proto2/Spec/`. Two commands then generate the constructors: `gen_untyped%` emits the
sort-erased one straight through `runUnsafe`, `gen_typed%` emits the re-typed one delegating to it.

The layers come first in the layout and the part of the API being lifted second, so term creation
is `Cvc/Proto2/Untyped/Term/` and `Cvc/Proto2/Typed/Term/`, and anything lifted later sits beside
them. Generation happens per theory within those, so a user compiles only the theories, and only
the layer, they import. The specification itself is compile-time data with no runtime footprint.

This root imports everything. Importing it is convenient, but it gives up the property above:
prefer importing the theory modules you actually use. The test suite, `Cvc.Proto2.Tests`, is
deliberately not imported here.
-/
