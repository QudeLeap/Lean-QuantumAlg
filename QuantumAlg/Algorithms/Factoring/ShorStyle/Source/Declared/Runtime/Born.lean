/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Source.Declared.Runtime.Semantics

/-!
# Actual zero-prepared Shor bank and its complete Born state

The placed member evolves the physical zero into exactly the source state on
all phase and target coordinates. No caller-supplied evolved state is used.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime

noncomputable section

private theorem bornLayoutWires {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) :
    (layout N).wires = ctx.quantumLayout.wires :=
  (ctx.quantumLayout_wires.trans sameWires).symm

/-- The physical zero has precisely the source binary zero label. -/
theorem basis_zero {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) :
    (basisEquiv N sameWires).symm 0 = ctx.quantumLayout.zeroLabel := by
  funext target
  obtain ⟨source, rfl⟩ := (wireEquiv N sameWires).surjective target
  apply Fin.ext
  have corresponding := Execution.basisOfEqualWires_value (layout N)
    ctx.quantumLayout (bornLayoutWires N sameWires)
    ((QuantumSignature.qubitsIndexEquiv (bankQubits N)).symm 0) source
  refine corresponding.trans ?_
  change (finTwoEquiv.symm
    ((0 : Fin (2 ^ bankQubits N)).val.testBit source.rev.val)).val = 0
  simp only [Fin.val_zero, Nat.zero_testBit]
  rfl

/-- The actual placed operator's zero column is the full declared Born vector. -/
theorem member_zero_amplitude {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (layout N).wires) (input : Input N)
    (parameter : (ParameterShape (modulusBits N)).Value) (row : ctx.register.Index) :
    (member N sameWires input parameter).matrix row ctx.quantumLayout.zeroLabel =
      (DeclaredSource.evolvedState (sourceBounds input) (phaseBits N)
        (selectedBase parameter)).normalized (basisEquiv N sameWires row) := by
  rw [← basis_zero N sameWires, member_binaryMatrix_entry, Equiv.apply_symm_apply]
  change (DeclaredSource.circuit (sourceBounds input) (phaseBits N)
      (selectedBase parameter)).binaryMatrix (basisEquiv N sameWires row)
        (prodEquiv ((0 : Fin (2 ^ phaseBits N)), (0 : Fin (2 ^ modulusBits N)))) =
      (DeclaredSource.circuit (sourceBounds input) (phaseBits N)
        (selectedBase parameter)).binaryMatrix.applyVec
          (OrderFinding.Native.zeroInput (phaseBits N) (modulusBits N))
          (basisEquiv N sameWires row)
  exact (HilbertOperator.applyVec_ket
    ((DeclaredSource.circuit (sourceBounds input) (phaseBits N)
      (selectedBase parameter)).binaryMatrix :
        HilbertOperator (Qubits (phaseBits N + modulusBits N)))
    (prodEquiv ((0 : Fin (2 ^ phaseBits N)), (0 : Fin (2 ^ modulusBits N))))
    (basisEquiv N sameWires row)).symm

end

end QuantumAlg.Factoring.ShorStyle.Canonical.DeclaredSource.Runtime
