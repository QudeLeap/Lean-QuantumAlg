/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Bank.Placement
import all QuantumAlg.Components.Encoded.BitGates.Realization
import all QuantumAlg.Util.FinPow.BinaryBasis

/-!
# Actual zero and reload seed coordinates for Shor

The zero label produced by whole-bank reset is exactly binary zero under the
physical wire correspondence. The shared constant-X program therefore maps
that actual reset label to the original zero-phase, unit-power, zero-auxiliary
seed. This is the real reload circuit's basis action, not an input premise.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement

noncomputable section

variable {ctx : RuntimeCtx .quantum} (N : Nat)
  (sameWires : ctx.quantumWires = (NativeQuantum.runtimeLayout N).wires)

/-- Wirewise zero and the binary zero word describe the same actual basis label. -/
theorem basis_zero : (basisEquiv N sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (wireEquiv N sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (NativeQuantum.runtimeLayout N)
    ctx.quantumLayout (layoutWires N sameWires)
    ((OrderFinding.layout (phaseBits N) (modulusBits N + modulusBits N)).binaryIndexEquiv.symm 0)
    source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ NativeQuantum.totalQubits N)).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- The actual shared X loader maps the established reset state to the exact original seed. -/
theorem reload_apply_zero :
    (reloadProgram N sameWires).applyNormalized
      (NormalizedVector.ket (R := ctx.register) ctx.quantumLayout.zeroLabel) =
        NormalizedVector.ket (R := ctx.register)
          ((basisEquiv N sameWires).symm (NativeQuantum.seedLabel N)) := by
  have actual := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
    (R := Qubits (NativeQuantum.totalQubits N)) (S := ctx.register)
    (basisEquiv N sameWires).symm
    (EncodedBit.Word.BasisLoad.program (NativeQuantum.seedLabel N))
    0 (NativeQuantum.seedLabel N)
    (EncodedBit.Word.BasisLoad.basisLoad_apply_zero (NativeQuantum.seedLabel N))
  rw [basis_zero] at actual
  exact actual

/-- The selected native member uses the identical source labels for both matrix coordinates. -/
theorem member_matrix_entry (parameter : CShape.Value (ParameterShape (modulusBits N)))
    (row column : ctx.register.Index) :
    (memberProgram N sameWires parameter).matrix row column =
      (NativeQuantum.program parameter).matrix
        (basisEquiv N sameWires row) (basisEquiv N sameWires column) := rfl

end

end QuantumAlg.Factoring.ShorStyle.Canonical.NativePlacement
