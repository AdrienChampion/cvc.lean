module

import Cvc.Untyped
meta import Cvc.Untyped


namespace Cvc.Untyped



#eval Env.runIO do
  let int ← Srt.int
  let bool ← Srt.bool
  let record ← Srt.record #[("intField", int), ("boolField", bool)]
  println! "record : {record}\n- is datatype := {record.isDatatype}"
