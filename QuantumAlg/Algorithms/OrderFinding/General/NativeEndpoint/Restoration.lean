/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.General.NativeEndpoint
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Full borrowed-base restoration across source sampling and recovery

The source starts with no borrowed quantum wire. Fresh quantum preparation,
the source word, measurements, retained cells, and finite recovery therefore
preserve the original borrowed classical value jointly with every external
reference. This proof concerns the actual connected circuit.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint

noncomputable section

open QuantumAlg.Execution

private theorem noBorrowedQuantum (width : Nat) :
    (pre width).borrowedQuantumWires = [] := by
  have subset := (pre width).borrowedQuantumWires_sublist
  rw [pre_quantumWires width] at subset
  exact List.sublist_nil.mp subset

/-- The complete run preserves every borrowed classical-reference correlation. -/
theorem code_borrowedRestored {N x r t width : Nat}
    (hinput : OrderFinding.Input N x r)
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference
      ((Sampling.Native.Framed.model access).HiddenState × History)) :
    (code hinput access).BorrowedRestored Reference state
      ((code hinput access).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code hinput access)
    (noBorrowedQuantum width) Reference state

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeEndpoint
