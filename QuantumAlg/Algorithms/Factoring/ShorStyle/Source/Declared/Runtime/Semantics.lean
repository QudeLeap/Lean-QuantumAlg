/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Placement

/-!
# Exact source coordinates of the actual selected Shor member

Equal-wire transport preserves every complex matrix entry on arbitrary target
words. The correspondence is the binary basis of the same declared bank.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

noncomputable section

/-- The actual placed member retains the original complete source matrix. -/
theorem member_binaryMatrix_entry {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) (input : Input N)
    (parameter : (ParameterShape (modulusBits N)).Value)
    (row column : ctx.register.Index) :
    (member N sameWires input parameter).matrix row column =
      (DeclaredSource.circuit (sourceBounds input) (phaseBits N)
        (selectedBase parameter)).binaryMatrix
          (basisEquiv N sameWires row) (basisEquiv N sameWires column) := by
  rw [member_matrix, UnitaryCircuit.binaryMatrix_eq_reindex]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply]
  exact congrArg₂
    (fun left right =>
      (DeclaredSource.circuit (sourceBounds input) (phaseBits N)
        (selectedBase parameter)).matrix left right)
    (by
      exact (Equiv.symm_apply_apply
        (QuantumSignature.qubitsIndexEquiv (phaseBits N + modulusBits N)) _).symm)
    (by
      exact (Equiv.symm_apply_apply
        (QuantumSignature.qubitsIndexEquiv (phaseBits N + modulusBits N)) _).symm)

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
