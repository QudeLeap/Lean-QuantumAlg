/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Frame.Work

/-!
# Exchanging two names for the same four actual working words

The product and temporary roles are exchanged while all physical storage
references remain the original ones. This lets the same actual three-slot
coordinate suffix and two destination writes describe either row family.
It performs no runtime operation and allocates no additional storage.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Work

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Exchange only the names of the original product and temporary cells. -/
def swapProductTemporary (work : Work ctx width) : Work ctx width where
  product := work.temporary
  inverse := work.inverse
  temporary := work.product
  slope := work.slope
  distinct := by
    have original := work.distinct
    simpa [List.nodup_cons, eq_comm, and_assoc, and_left_comm, and_comm] using original

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Work
