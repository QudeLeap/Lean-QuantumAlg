/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Operator
import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Core.Execution.Local.Marginals
import all QuantumAlg.Core.Base.State.Density

/-!
# Coherent state of the actual selected source word

Acting with the interpreter's physically placed native program on the
prepared zero vector gives the exact declared-query Born vector, transported
through the same certified binary coordinates. No output distribution or
measurement result is assumed as an input to this equality.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

/-- The native framed unitary produces the exact source Born state. -/
theorem nativeProgram_zero_density (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    DensityOperator.applyUnitary (nativeProgram ctx noQuantum access).matrix
      ((DensityOperator.ofPure (OrderFinding.Native.zeroInput t width)).reindex
        (S := (preparedContext ctx noQuantum t width).register)
        (preparedBasisEquiv ctx noQuantum t width).symm) =
      (DensityOperator.ofPure (OrderFinding.Native.evolvedVector access)).reindex
        (S := (preparedContext ctx noQuantum t width).register)
        (preparedBasisEquiv ctx noQuantum t width).symm := by
  rw [nativeProgram_matrix_binary]
  rw [← DensityOperator.applyUnitary_reindex]
  rw [← DensityOperator.ofPure_apply]
  rfl

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
