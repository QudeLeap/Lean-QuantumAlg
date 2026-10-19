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

private lemma preparedPosition_eq (n : Nat) (index : Fin (n + 1)) :
    positionsOfEqualWires (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) index = preparedWire n index := by
  apply (preparedContext n).quantumLayout.identityInjective
  exact congrArg QuantumWire.identity
    ((wireAtCorrespondingPosition (runtimeLayout n) (preparedContext n).quantumLayout
      (runtime_wires n) index).trans (preparedWire_preserved n index).symm)

/-- The native embedding uses exactly the basis supplied by real zero preparation. -/
lemma preparedLayoutEquiv_equalWires (n : Nat) :
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
lemma program_matrix (n : Nat) (environment : (XorOracle.model n).Interpretation) :
    ((program n).matrix environment) =
      UnitaryOperator.reindex (preparedBasisEquiv n).symm
        ((Native.zeroInputProgram n).binaryMatrix environment) := by
  rw [program, unitaryOfEqualWires_matrix (runtimeLayout n)
    (preparedContext n).quantumLayout (runtime_wires n) environment (Native.zeroInputProgram n),
    preparedLayoutEquiv_equalWires]
  apply Subtype.ext
  ext row column
  change ((Native.zeroInputProgram n).matrix environment)
    ((preparedLayoutEquiv n).symm row) ((preparedLayoutEquiv n).symm column) =
      ((Native.zeroInputProgram n).matrix environment)
        ((layout n).binaryIndexEquiv.symm ((preparedBasisEquiv n) row))
        ((layout n).binaryIndexEquiv.symm ((preparedBasisEquiv n) column))
  simp only [preparedBasisEquiv, Equiv.trans_apply, Equiv.symm_apply_apply]

end

end QuantumAlg.WalshHadamard.Readout
