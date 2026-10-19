/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Context
public import QuantumAlg.Algorithms.OrderFinding.Native.Matrix
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Native.Matrix
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex
import all QuantumAlg.Core.Execution.Context.Layout.Unitary

/-!
# Actual framed source word in binary coordinates

The interpreter's selected native word has the same complete operator as
the source circuit after the certified physical-wire basis change. This
equality includes its declared modular-exponentiation query and all native
phase gates; it introduces no replacement gate.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

private lemma reindex_binary_bridge {R S T : Register}
    (physical : R.Index ≃ S.Index) (binary : R.Index ≃ T.Index)
    (operator : UnitaryOperator R) :
    UnitaryOperator.reindex physical operator =
      UnitaryOperator.reindex (physical.symm.trans binary).symm
        (UnitaryOperator.reindex binary operator) := by
  have basis : (physical.symm.trans binary).symm = binary.symm.trans physical := by
    ext value
    rfl
  rw [basis, ← UnitaryOperator.unitaryOperator_reindex_trans,
    UnitaryOperator.unitaryOperator_reindex_cancel]

/-- The interpreter executes exactly the native source operator in its frame. -/
public lemma nativeProgram_matrix_binary (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) (t width : Nat)
    (environment : (OrderFinding.Native.sourceModel t width).Interpretation) :
    (nativeProgram ctx noQuantum t width).matrix environment =
      UnitaryOperator.reindex (preparedBasisEquiv ctx noQuantum t width).symm
        ((OrderFinding.Native.circuit t width).binaryMatrix environment) := by
  let physical := QuantumAlg.Execution.basisOfEqualWires
    (Sampling.Native.runtimeLayout t width)
    (preparedContext ctx noQuantum t width).quantumLayout
    (prepared_wires ctx noQuantum t width)
  let binary := QuantumSignature.qubitsIndexEquiv (t + width)
  calc
    _ = UnitaryOperator.reindex physical ((OrderFinding.Native.circuit t width).matrix
      environment) := by
      simpa only [nativeProgram] using
        (QuantumAlg.Execution.unitaryOfEqualWires_matrix
          (Sampling.Native.runtimeLayout t width)
          (preparedContext ctx noQuantum t width).quantumLayout
          (prepared_wires ctx noQuantum t width) environment
          (OrderFinding.Native.circuit t width))
    _ = _ := by
      have basisEq : preparedBasisEquiv ctx noQuantum t width =
          physical.symm.trans binary := rfl
      have matrixEq : ((OrderFinding.Native.circuit t width).binaryMatrix environment) =
          UnitaryOperator.reindex binary
            ((OrderFinding.Native.circuit t width).matrix environment) := rfl
      rw [basisEq, matrixEq]
      exact reindex_binary_bridge
        (R := (QuantumSignature.qubits (t + width)).register)
        (S := (preparedContext ctx noQuantum t width).register)
        (T := Qubits (t + width)) physical binary
        ((OrderFinding.Native.circuit t width).matrix environment)

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
