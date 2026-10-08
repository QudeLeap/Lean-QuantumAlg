/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
public import QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Measurement.Cells.Laws

/-!
# Binary coordinates of the actual framed source register

The prepared native word uses the same ordered physical wires as the fresh
register. Retained classical cells do not change its quantum basis. These
equivalences identify the exact basis used by the interpreter and the source
Born calculation, including a caller-owned classical input frame.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

open QuantumAlg.Execution

/-- Binary labels on the actual prepared context's physical systems. -/
public def preparedBasisEquiv (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat) :
    (preparedContext ctx noQuantum t width).register.Index ≃
      (Qubits (t + width)).Index :=
  (Execution.basisOfEqualWires (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width)).symm.trans
      (QuantumSignature.qubitsIndexEquiv (t + width))

/-- The measured cells leave all source systems in the same binary basis. -/
public def outputBasisEquiv (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat) :
    (post ctx noQuantum t width).register.Index ≃
      (Qubits (t + width)).Index :=
  (MeasurementCells.basisEquiv (resultContext ctx noQuantum t width) 2 t).symm.trans
    (preparedBasisEquiv ctx noQuantum t width)

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
