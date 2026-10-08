/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Core.Execution.Circuit.Restoration

/-!
# Preservation of an existing classical input and its reference

The complete source sample acts only on fresh owned qubits and writable
classical cells. The original borrowed classical values remain correlated
with any external quantum reference exactly as at input.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

private theorem noBorrowedQuantum (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) : ctx.borrowedQuantumWires = [] := by
  have subset := ctx.borrowedQuantumWires_sublist
  rw [noQuantum] at subset
  exact List.sublist_nil.mp subset

/-- Every actual source-sample execution preserves the full borrowed joint state. -/
public theorem code_borrowedRestored (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) {Reference : Register}
    {History : Type} [Fintype History]
    (state : State ctx Reference ((model access).HiddenState × History)) :
    (code ctx noQuantum access).BorrowedRestored Reference state
      ((code ctx noQuantum access).execute Reference state) :=
  Circuit.borrowedRestored_of_noBorrowedQuantum (code ctx noQuantum access)
    (noBorrowedQuantum ctx noQuantum) Reference state

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
