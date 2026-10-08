/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Context
import all QuantumAlg.Algorithms.OrderFinding.Native.Born
import all QuantumAlg.Util.FinPow.BinaryBasis.Zero
import all QuantumAlg.Core.Base.State.Basis
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Zero preparation in the actual source basis

The selected prepare-zero instruction initializes the same full phase and
target word as the Born calculation, including the empty-width case. Existing
classical cells do not add an uninitialized quantum system.
-/

namespace QuantumAlg.OrderFinding.Sampling.Native.Framed

noncomputable section

/-- A caller with no quantum wires has no old quantum systems. -/
theorem input_systemCount (ctx : RuntimeCtx .quantum)
    (noQuantum : ctx.quantumWires = []) : ctx.systemCount = 0 := by
  change ctx.quantumWires.length = 0
  rw [noQuantum]
  rfl

/-- Physical all-zero labels have binary integer value zero. -/
theorem sourceZero_label (t width : Nat) :
    (QuantumSignature.qubitsIndexEquiv (t + width))
      (Sampling.Native.runtimeLayout t width).zeroLabel = 0 := by
  change BinaryBasis.bigEndianEquiv (t + width)
    (fun _ : Fin (t + width) => (0 : Fin 2)) = 0
  exact BinaryBasis.bigEndianEquiv_zero (t + width)

/-- The actual prepare-zero vector is the source Born model's complete zero input. -/
theorem preparedZero_vector (t width : Nat) :
    NormalizedVector.reindex (QuantumSignature.qubitsIndexEquiv (t + width))
      (BasisPreparation.zero (Sampling.Native.runtimeLayout t width)).normalized =
      OrderFinding.Native.zeroInput t width := by
  let binary := QuantumSignature.qubitsIndexEquiv (t + width)
  have zero : binary (Sampling.Native.runtimeLayout t width).zeroLabel = 0 :=
    sourceZero_label t width
  apply NormalizedVector.ext
  intro basis
  simp only [NormalizedVector.reindex_apply, BasisPreparation.normalized,
    BasisPreparation.zero, OrderFinding.Native.zeroInput, NormalizedVector.ket_apply]
  change (if binary.symm basis = (Sampling.Native.runtimeLayout t width).zeroLabel
    then (1 : ℂ) else 0) = (if basis = 0 then 1 else 0)
  have same : binary.symm basis = (Sampling.Native.runtimeLayout t width).zeroLabel ↔
      basis = 0 := by
    constructor
    · intro equal
      calc
        basis = binary (binary.symm basis) := (binary.apply_symm_apply basis).symm
        _ = binary (Sampling.Native.runtimeLayout t width).zeroLabel := congrArg binary equal
        _ = 0 := zero
    · intro equal
      subst basis
      rw [← zero]
      exact binary.symm_apply_apply _
  by_cases value : basis = 0
  · subst basis
    have selected : binary.symm 0 =
        (Sampling.Native.runtimeLayout t width).zeroLabel := same.mpr rfl
    simp only [selected, if_true]
  · have rejected : binary.symm basis ≠
        (Sampling.Native.runtimeLayout t width).zeroLabel :=
      fun selected => value (same.mp selected)
    simp only [rejected, value, if_false]

end

end QuantumAlg.OrderFinding.Sampling.Native.Framed
