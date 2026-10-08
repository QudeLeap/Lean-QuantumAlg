/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.WalshHadamard.Pipeline

import all QuantumAlg.Primitives.WalshHadamard.Readout.Context
import all QuantumAlg.Primitives.WalshHadamard.Readout.Storage
import all QuantumAlg.Primitives.WalshHadamard.Initialization.Matrix
import all QuantumAlg.Core.Execution.Context.Layout
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# The Walsh native word on the actual prepared wires

The preparation assembly and the native-word placement preserve the same
physical wire identities and values. Their exact basis agreement transports
the complete zero-input native matrix to the actual execution context.
-/

namespace QuantumAlg.WalshHadamard.Readout

noncomputable section

open QuantumAlg.Execution

private theorem preparedPosition_eq (n : Nat) (index : Fin (n + 1)) :
    positionsOfEqualWires (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) index = preparedWire n index := by
  apply (preparedContext n).quantumLayout.identityInjective
  exact congrArg QuantumWire.identity
    ((wireAtCorrespondingPosition (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) index).trans (preparedWire_preserved n index).symm)

/-- The native embedding uses exactly the basis supplied by real zero preparation. -/
theorem preparedLayoutEquiv_equalWires (n : Nat) :
    basisOfEqualWires (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) = preparedLayoutEquiv n := by
  apply Equiv.ext
  intro basis
  funext position
  obtain ⟨index, rfl⟩ :=
    (positionsOfEqualWires (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n)).surjective position
  apply Fin.ext
  rw [basisOfEqualWires_value, preparedPosition_eq]
  exact (preparedLayoutEquiv_value n basis index).symm

/-- The exact native matrix on the prepared context in the original binary labels. -/
theorem program_matrix {n : Nat} (function : WalshHadamard.Oracle n) :
    (program function).matrix =
      UnitaryOperator.reindex (preparedBasisEquiv n).symm
        (Native.zeroInputProgram function).binaryMatrix := by
  rw [program, unitaryOfEqualWires_matrix (runtimeLayout n)
    (preparedContext n).quantumLayout (runtime_wires n) (Native.zeroInputProgram function),
    preparedLayoutEquiv_equalWires]
  apply Subtype.ext
  ext row column
  change (Native.zeroInputProgram function).matrix
    ((preparedLayoutEquiv n).symm row) ((preparedLayoutEquiv n).symm column) =
      (Native.zeroInputProgram function).matrix
        ((layout n).binaryIndexEquiv.symm ((preparedBasisEquiv n) row))
        ((layout n).binaryIndexEquiv.symm ((preparedBasisEquiv n) column))
  simp only [preparedBasisEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

end

end QuantumAlg.WalshHadamard.Readout
