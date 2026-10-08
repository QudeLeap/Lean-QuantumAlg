/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Operator
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.ProjectorPhase
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Average
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Source.Projected
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary

/-!
# Real projected QSVT from the actual alternating word

The two source branches give their arithmetic average on the phase ancilla's
plus state. Native Hadamard gates convert that block to a zero-state block,
with both gates included in the circuit's events and depth
[GSLW19, BlockHam.tex:851-887].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native
noncomputable section

variable {width : Nat} (U : UnitaryOperator (Qubits width))
  (left right : OrthogonalProjector width) (allowControlled : Bool)

/-- The actual alternating circuit is the intrinsic direct sum of its source branches. -/
theorem circuit_source_operator (phases : List ℝ) :
    (circuit U left right allowControlled phases).binaryMatrix =
      phaseControlledDirectSumOperator (sourceWord U left right phases)
        (sourceWord U left right (negPhases phases)) := by
  apply Subtype.ext
  rw [circuit_source_matrix, phaseControlledDirectSum_eq_tensor_decomp]
  rfl

/-- The actual circuit's plus-state block averages the two original source words. -/
theorem circuit_plus_block (phases : List ℝ) :
    phasePlusBlock (circuit U left right allowControlled phases).binaryMatrix =
      (1 / 2 : ℂ) • (sourceWord U left right phases : HilbertOperator (Qubits width)) +
        (1 / 2 : ℂ) •
          (sourceWord U left right (negPhases phases) : HilbertOperator (Qubits width)) := by
  rw [circuit_source_operator, phasePlusBlock_phaseControlledDirectSum]

/-- Two source polynomial equalities transfer to the same executed circuit. -/
theorem circuit_real_correctness (L : Nat) (P Pneg Preal : Polynomial ℂ)
    (phases : List ℝ)
    (hpos : SourceProjectedQSVTBlockCorrectness U left right L P phases)
    (hneg : SourceProjectedQSVTBlockCorrectness U left right L Pneg (negPhases phases))
    (havg :
      (1 / 2 : ℂ) • singularValuePolynomial right L P (projectedUnitaryBlock left right U) +
        (1 / 2 : ℂ) •
          singularValuePolynomial right L Pneg (projectedUnitaryBlock left right U) =
        singularValuePolynomial right L Preal (projectedUnitaryBlock left right U)) :
    projectedPhasePlusBlock (projectedOutputProjector left right L) right
      (circuit U left right allowControlled phases).binaryMatrix =
        singularValuePolynomial right L Preal (projectedUnitaryBlock left right U) := by
  unfold projectedPhasePlusBlock
  rw [circuit_plus_block, Matrix.mul_add, Matrix.add_mul]
  rw [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_smul, Matrix.smul_mul]
  exact (congrArg₂ (fun A B : HilbertOperator (Qubits width) =>
    (1 / 2 : ℂ) • A + (1 / 2 : ℂ) • B) hpos hneg).trans havg

/-- A genuine native Hadamard on the phase wire, preserving the entire suffix. -/
def hadamard :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  Gate.singleQubitAt (ProjectorPhase.layout width)
    (ProjectedSignal.model U left right allowControlled) Gate.HOp (0 : Fin (1 + width)) rfl

/-- Prepare and unprepare the plus phase state using two actual native gates. -/
def zeroBlockCircuit (phases : List ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  ((hadamard U left right allowControlled).seq
    (circuit U left right allowControlled phases)).seq (hadamard U left right allowControlled)

/-- The zero-block circuit has precisely the source Hadamard-conjugated operator. -/
theorem zeroBlockCircuit_matrix (phases : List ℝ) :
    (zeroBlockCircuit U left right allowControlled phases).binaryMatrix =
      phaseHadamardWrapperOperator
        (circuit U left right allowControlled phases).binaryMatrix := by
  rw [zeroBlockCircuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq]
  simp only [hadamard, Gate.singleQubitAt_first_binaryMatrix]
  apply Subtype.ext
  exact (Matrix.mul_assoc _ _ _).symm

/-- The two boundary Hadamards contribute two native events to the same circuit. -/
theorem zeroBlockCircuit_events (phases : List ℝ) :
    (zeroBlockCircuit U left right allowControlled phases).eventCost =
      (circuit U left right allowControlled phases).eventCost +
        2 • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model
            (ProjectedSignal.model U left right allowControlled)) (.gate .singleQubit) := by
  change (ResourcePool.singleton (model := .quantum AlgorithmGate.model
      (ProjectedSignal.model U left right allowControlled)) (.gate .singleQubit) +
    (circuit U left right allowControlled phases).eventCost) +
      ResourcePool.singleton (model := .quantum AlgorithmGate.model
        (ProjectedSignal.model U left right allowControlled)) (.gate .singleQubit) = _
  rw [two_smul]
  ac_rfl

/-- The sequential zero-block implementation has exact dependency depth 4L+2. -/
theorem zeroBlockCircuit_depth (phases : List ℝ) :
    (zeroBlockCircuit U left right allowControlled phases).evaluatedEventDepth (fun _ => 1) =
      4 * phases.length + 2 := by
  change (1 + (circuit U left right allowControlled phases).evaluatedEventDepth
    (fun _ => 1)) + 1 = _
  rw [circuit_depth]
  omega

end
end QuantumAlg.QSP.MultiQubit.QSVT.Native
