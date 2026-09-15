/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Reflection
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Layout
import all QuantumAlg.Algorithms.AmplitudeEstimation.PhaseWorkspace
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Components.Oracle.ZeroReflection.Action
import all QuantumAlg.Components.Encoded.BitGates.BinaryLabelEncoding
import all QuantumAlg.Components.BinaryLabelEncoding

/-!
# Exact selected-branch operator of the elementary source reflection

The actual full-basis action is identified with the independent positive
zero-reflection operator at precisely the original selected phase bit.
Every phase and exceptional work value is retained; the equality is on
the complete operator, before restricting to any source input or invariant plane.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

private theorem control_read {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) :
    (BinaryLabelEncoding.finIdentityBit (phaseWidth t n) (controlWire n stage)).get phase =
      phase.val.testBit (extendedStage n stage).val := by
  change phase.val.testBit (WireAddress.bitIndex (controlWire n stage)).val = _
  congr 1
  change phaseWidth t n - 1 - qpeStagePrefixWidth stage = stage.val + helperWidth t n
  dsimp only [phaseWidth, qpeStagePrefixWidth]
  omega

private theorem expected_reflection_action {t : Nat} (n : Nat) (stage : Fin t)
    (phase : Fin (2 ^ phaseWidth t n)) (source : Fin (2 ^ n)) :
    (qpeControlledBitOp (phaseWidth t n) (ZeroReflection.zeroReflectionOperator n)
      (extendedStage n stage)).applyVec
        (NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec =
      if phase.val.testBit (extendedStage n stage).val then
        if source = 0 then
          (NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec
        else -(NormalizedVector.ket (R := Qubits (totalQubits t n)) (prodEquiv (phase, source))).vec
      else (NormalizedVector.ket (R := Qubits (totalQubits t n))
        (prodEquiv (phase, source))).vec := by
  ext row
  obtain ⟨⟨leftPhase, leftSource⟩, rfl⟩ :=
    (prodEquiv (m := phaseWidth t n) (n := n)).surjective row
  have packed : prodEquiv (leftPhase, leftSource) = prodEquiv (phase, source) ↔
      leftPhase = phase ∧ leftSource = source := by
    constructor
    · intro same
      exact Prod.mk.inj ((prodEquiv (m := phaseWidth t n) (n := n)).injective same)
    · rintro ⟨rfl, rfl⟩
      rfl
  have sourceEntry := congrArg (fun state : HilbertVector (Qubits n) => state leftSource)
    (ZeroReflection.zeroReflectionOperator_applyVec_ket n source)
  simp only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at sourceEntry
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    qpeControlledBitOp, qpeExponentOp_apply]
  simp only [Equiv.symm_apply_apply]
  by_cases equalPhase : leftPhase = phase
  · subst leftPhase
    cases active : phase.val.testBit (extendedStage n stage).val
    · simp [NormalizedVector.ket_apply, packed, Matrix.one_apply]
    · by_cases zeroSource : source = 0
      · simpa [active, zeroSource, NormalizedVector.ket_apply, packed] using sourceEntry
      · simpa [active, zeroSource, NormalizedVector.ket_apply, packed] using sourceEntry
  · cases active : phase.val.testBit (extendedStage n stage).val <;>
      by_cases zeroSource : source = 0 <;>
      simp [equalPhase, zeroSource, NormalizedVector.ket_apply, packed]

/-- The selected elementary sequence implements the exact full controlled source operator. -/
theorem reflection_matrix {t : Nat} (n : Nat) (stage : Fin t) :
    (reflection n stage).matrix = qpeControlledBitOp (phaseWidth t n)
      (ZeroReflection.zeroReflectionOperator n) (extendedStage n stage) := by
  apply Subtype.ext
  ext row column
  obtain ⟨⟨phase, source⟩, rfl⟩ :=
    (prodEquiv (m := phaseWidth t n) (n := n)).surjective column
  have actual := reflection_applyVec_pair n stage phase source
  rw [control_read] at actual
  have action := actual.trans (expected_reflection_action n stage phase source).symm
  simpa only [UnitaryCircuit.applyVec, UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
    using congrArg (fun state : HilbertVector (Qubits (totalQubits t n)) => state row) action

end

end QuantumAlg.AmplitudeEstimation.Elementary
