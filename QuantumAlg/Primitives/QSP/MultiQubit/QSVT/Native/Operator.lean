/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
public import QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Components.Oracle.ProjectedSignal.Circuit
import all QuantumAlg.Components.Oracle.SignalProcessing
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Components.Control

/-!
# Exact source semantics of the native alternating word

The native word simultaneously realizes the source sequences with phase lists
Phi and -Phi on the phase-ancilla branches. All source factors below are certified
operators; the executable implementation remains the independently constructed
native word [GSLW19, BlockHam.tex:738-745,851-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native

noncomputable section

/-- The source's metadata-free alternating phase product on its original signal space. -/
def sourceWord {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) : List ℝ → UnitaryOperator (Qubits width)
  | [] => 1
  | φ :: phases =>
      let even := (phases.length + 1) % 2 = 0
      projectorPhaseOp φ (if even then right else left) *
        ((if even then U⁻¹ else U) * sourceWord U left right phases)

/-- Two specified signal operators on the zero and one phase-ancilla branches. -/
def branchMatrix {width : Nat} (V0 V1 : HilbertOperator (Qubits width)) :
    HilbertOperator (Qubits (1 + width)) :=
  HilbertOperator.tensor HilbertOperator.proj0 V0 +
    HilbertOperator.tensor HilbertOperator.proj1 V1

private lemma projectors_sum : HilbertOperator.proj0 + HilbertOperator.proj1 =
    (1 : HilbertOperator (Qubits 1)) := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [HilbertOperator.proj0, HilbertOperator.proj1]

private lemma branchMatrix_mul {width : Nat} (V0 V1 W0 W1 : HilbertOperator (Qubits width)) :
    branchMatrix V0 V1 * branchMatrix W0 W1 = branchMatrix (V0 * W0) (V1 * W1) := by
  unfold branchMatrix
  rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add]
  repeat rw [HilbertOperator.tensor_mul_tensor]
  have h00 : HilbertOperator.proj0 * HilbertOperator.proj0 = HilbertOperator.proj0 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HilbertOperator.proj0, Matrix.mul_apply, Fin.sum_univ_two]
  have h01 : HilbertOperator.proj0 * HilbertOperator.proj1 =
      (0 : HilbertOperator (Qubits 1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HilbertOperator.proj0, HilbertOperator.proj1, Matrix.mul_apply, Fin.sum_univ_two]
  have h10 : HilbertOperator.proj1 * HilbertOperator.proj0 =
      (0 : HilbertOperator (Qubits 1)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HilbertOperator.proj0, HilbertOperator.proj1, Matrix.mul_apply, Fin.sum_univ_two]
  have h11 : HilbertOperator.proj1 * HilbertOperator.proj1 = HilbertOperator.proj1 := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [HilbertOperator.proj1, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  simp

private lemma branchMatrix_same {width : Nat} (V : HilbertOperator (Qubits width)) :
    branchMatrix V V = HilbertOperator.tensor (1 : HilbertOperator (Qubits 1)) V := by
  rw [branchMatrix, ← HilbertOperator.add_tensor, projectors_sum]

private lemma rotation_two (φ : ℝ) :
    (rotZStdOp (2 * φ) : HilbertOperator (Qubits 1)) =
      Complex.exp (-(φ * Complex.I)) • HilbertOperator.proj0 +
        Complex.exp (φ * Complex.I) • HilbertOperator.proj1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rotZStdOp, rotZOp, HilbertOperator.proj0, HilbertOperator.proj1]

/-- The concrete projector gadget is the direct sum of the positive and negative source phases. -/
lemma phase_branch_matrix {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (allowControlled useRight : Bool) (φ : ℝ) :
    (((phase (width := width) allowControlled useRight φ).binaryMatrix
      (ProjectedSignal.interpretation U left right allowControlled)) :
      HilbertOperator (Qubits (1 + width))) =
      branchMatrix (projectorPhaseOp φ (if useRight then right else left))
        (projectorPhaseOp (-φ) (if useRight then right else left)) := by
  rw [phase, ProjectorPhase.circuit_projector_matrix _ _
    (ProjectedSignal.interpretation U left right allowControlled)
    (ProjectedSignal.Circuit.projectorFlip_matrix
      AlgorithmGate.model width allowControlled U left right useRight)]
  have negative : -(2 * φ) = 2 * (-φ) := by ring
  rw [negative, rotation_two, rotation_two]
  simp only [branchMatrix, coe_projectorPhaseOp]
  have negExp : Complex.exp (((-φ : ℝ) : ℂ) * Complex.I) =
      Complex.exp (-(φ * Complex.I)) := by congr 1; push_cast; ring
  have negNegExp : Complex.exp (-(((-φ : ℝ) : ℂ) * Complex.I)) =
      Complex.exp (φ * Complex.I) := by congr 1; push_cast; ring
  rw [negExp, negNegExp]
  ext i j
  simp only [HilbertOperator.tensor_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  ring

set_option maxHeartbeats 800000 in
-- Each slot transports two full source operators through the canonical physical layout.
/-- The full native circuit realizes both original source phase products exactly. -/
lemma circuit_source_matrix {width : Nat} (U : UnitaryOperator (Qubits width))
    (left right : OrthogonalProjector width) (allowControlled : Bool) (phases : List ℝ) :
    (((circuit (width := width) allowControlled phases).binaryMatrix
      (ProjectedSignal.interpretation U left right allowControlled)) :
      HilbertOperator (Qubits (1 + width))) =
      branchMatrix (sourceWord U left right phases)
        (sourceWord U left right (phases.map fun φ => -φ)) := by
  induction phases with
  | nil =>
      simp only [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_identity, List.map_nil,
        sourceWord]
      rw [branchMatrix_same]
      change (1 : HilbertOperator (Qubits (1 + width))) =
        HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits width))
      exact HilbertOperator.one_tensor_one.symm
  | cons φ phases ih =>
      rw [circuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
        UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
      change _ * (_ * _) = _
      rw [phase_branch_matrix U left right allowControlled
        (decide ((phases.length + 1) % 2 = 0)) φ,
        signal_matrix U left right allowControlled (decide ((phases.length + 1) % 2 = 0)), ih]
      have identityMatrix : ((1 : UnitaryOperator (Qubits 1)) :
          HilbertOperator (Qubits 1)) = 1 := rfl
      simp only [UnitaryOperator.coe_tensor, identityMatrix]
      rw [← branchMatrix_same, branchMatrix_mul, branchMatrix_mul]
      by_cases even : (phases.length + 1) % 2 = 0 <;>
        simp [sourceWord, List.map_cons, List.length_map, even]

end

end QuantumAlg.QSP.MultiQubit.QSVT.Native
