/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Native.Certificate
import all QuantumAlg.Primitives.QSP.MultiQubit.QSVT.Complement
import all QuantumAlg.Components.Oracle.ProjectedSignal.Circuit
import all QuantumAlg.Components.Gates.SingleQubit.First.Binary
import all QuantumAlg.Components.Gates.Rotation.Operator

/-!
# Boundary-balanced projected QSVT words

For odd degree, the direct phase-gadget expansion has one excess left-projector
query and one missing right-projector query. The phase ancilla is in `|+>` at
both projected boundaries, so a controlled projector NOT is invisible there.
Moving the outer left query to a right query at the input boundary therefore
preserves the projected block and realizes the source implementation lemma's
exact `L` queries to each projector [GSLW19, BlockHam.tex:883-889].
-/

namespace QuantumAlg.QSP.MultiQubit.QSVT.Native.Balanced
noncomputable section

private theorem ancillaBlock_controlledNot {N : Nat}
    (P : OrthogonalProjector N) (a b : Fin (2 ^ 1)) :
    ancillaBlock a b
        (OrthogonalProjector.controlledNotOp P :
          HilbertOperator (Qubits (1 + N))) =
      (Gate.XOp : HilbertOperator (Qubits 1)) a b • P.op +
        (1 : HilbertOperator (Qubits 1)) a b • OrthogonalProjector.complement P := by
  ext i j
  have hai := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := N)) (a, i)
  have hbj := Equiv.symm_apply_apply (prodEquiv (m := 1) (n := N)) (b, j)
  simp only [ancillaBlock, OrthogonalProjector.controlledNotOp,
    UnitaryOperator.coe_ofMatrix, Matrix.add_apply,
    HilbertOperator.tensor_apply, Matrix.smul_apply, smul_eq_mul]
  rw [hai, hbj]

private theorem ancillaBlock_unitary_mul {N : Nat} (a c : Fin (2 ^ 1))
    (V W : UnitaryOperator (Qubits (1 + N))) :
    ancillaBlock a c ((V * W : UnitaryOperator (Qubits (1 + N))) :
        HilbertOperator (Qubits (1 + N))) =
      ∑ b : Fin (2 ^ 1),
        ancillaBlock a b (V : HilbertOperator (Qubits (1 + N))) *
          ancillaBlock b c (W : HilbertOperator (Qubits (1 + N))) := by
  simpa using ancillaBlock_mul a c
    (V : HilbertOperator (Qubits (1 + N)))
    (W : HilbertOperator (Qubits (1 + N)))

private def blockSum {N : Nat} (V : HilbertOperator (Qubits (1 + N))) :
    HilbertOperator (Qubits N) :=
  ancillaBlock 0 0 V + ancillaBlock 0 1 V +
    ancillaBlock 1 0 V + ancillaBlock 1 1 V

private theorem phasePlusBlock_eq_smul_blockSum {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) :
    phasePlusBlock V =
      (NormalizedVector.invSqrt2 * NormalizedVector.invSqrt2) •
        blockSum (V : HilbertOperator (Qubits (1 + N))) := by
  rw [phasePlusBlock_eq_sum_ancillaBlock]
  simp only [Nat.reducePow, Fin.sum_univ_two, NormalizedVector.ketPlus_apply,
    smul_smul]
  have hstar :
      (starRingEnd ℂ) NormalizedVector.invSqrt2 =
        NormalizedVector.invSqrt2 :=
    NormalizedVector.star_invSqrt2
  rw [hstar]
  unfold blockSum
  module

private theorem controlledNot_row_sum {N : Nat} (P : OrthogonalProjector N)
    (a : Fin (2 ^ 1)) :
    ancillaBlock a 0
          (OrthogonalProjector.controlledNotOp P : HilbertOperator (Qubits (1 + N))) +
        ancillaBlock a 1
          (OrthogonalProjector.controlledNotOp P : HilbertOperator (Qubits (1 + N))) =
      1 := by
  rw [ancillaBlock_controlledNot, ancillaBlock_controlledNot]
  fin_cases a <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, Matrix.one_apply,
      OrthogonalProjector.complement]

private theorem controlledNot_column_sum {N : Nat} (P : OrthogonalProjector N)
    (b : Fin (2 ^ 1)) :
    ancillaBlock 0 b
          (OrthogonalProjector.controlledNotOp P : HilbertOperator (Qubits (1 + N))) +
        ancillaBlock 1 b
          (OrthogonalProjector.controlledNotOp P : HilbertOperator (Qubits (1 + N))) =
      1 := by
  rw [ancillaBlock_controlledNot, ancillaBlock_controlledNot]
  fin_cases b <;>
    simp [Gate.XOp, UnitaryOperator.ofPerm, Matrix.one_apply,
      OrthogonalProjector.complement]

private theorem blockSum_mul_controlledNot {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) (P : OrthogonalProjector N) :
    blockSum ((V * OrthogonalProjector.controlledNotOp P :
        UnitaryOperator (Qubits (1 + N))) : HilbertOperator (Qubits (1 + N))) =
      blockSum (V : HilbertOperator (Qubits (1 + N))) := by
  unfold blockSum
  simp_rw [ancillaBlock_unitary_mul]
  simp only [Nat.reducePow, Fin.sum_univ_two]
  calc
    _ = ancillaBlock 0 0 (V : HilbertOperator (Qubits (1 + N))) *
          (ancillaBlock 0 0
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N))) +
            ancillaBlock 0 1
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N)))) +
        ancillaBlock 0 1 (V : HilbertOperator (Qubits (1 + N))) *
          (ancillaBlock 1 0
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N))) +
            ancillaBlock 1 1
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N)))) +
        ancillaBlock 1 0 (V : HilbertOperator (Qubits (1 + N))) *
          (ancillaBlock 0 0
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N))) +
            ancillaBlock 0 1
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N)))) +
        ancillaBlock 1 1 (V : HilbertOperator (Qubits (1 + N))) *
          (ancillaBlock 1 0
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N))) +
            ancillaBlock 1 1
              (OrthogonalProjector.controlledNotOp P :
                HilbertOperator (Qubits (1 + N)))) := by
      simp only [Matrix.mul_add]
      ac_rfl
    _ = _ := by
      rw [controlledNot_row_sum, controlledNot_row_sum]
      simp

private theorem blockSum_controlledNot_mul {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) (P : OrthogonalProjector N) :
    blockSum ((OrthogonalProjector.controlledNotOp P * V :
        UnitaryOperator (Qubits (1 + N))) : HilbertOperator (Qubits (1 + N))) =
      blockSum (V : HilbertOperator (Qubits (1 + N))) := by
  unfold blockSum
  simp_rw [ancillaBlock_unitary_mul]
  simp only [Nat.reducePow, Fin.sum_univ_two]
  calc
    _ = (ancillaBlock 0 0
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N))) +
          ancillaBlock 1 0
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N)))) *
          ancillaBlock 0 0 (V : HilbertOperator (Qubits (1 + N))) +
        (ancillaBlock 0 0
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N))) +
          ancillaBlock 1 0
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N)))) *
          ancillaBlock 0 1 (V : HilbertOperator (Qubits (1 + N))) +
        (ancillaBlock 0 1
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N))) +
          ancillaBlock 1 1
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N)))) *
          ancillaBlock 1 0 (V : HilbertOperator (Qubits (1 + N))) +
        (ancillaBlock 0 1
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N))) +
          ancillaBlock 1 1
            (OrthogonalProjector.controlledNotOp P :
              HilbertOperator (Qubits (1 + N)))) *
          ancillaBlock 1 1 (V : HilbertOperator (Qubits (1 + N))) := by
      simp only [Matrix.add_mul]
      ac_rfl
    _ = _ := by
      rw [controlledNot_column_sum, controlledNot_column_sum]
      simp

private theorem phasePlusBlock_mul_controlledNot {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) (P : OrthogonalProjector N) :
    phasePlusBlock (V * OrthogonalProjector.controlledNotOp P) =
      phasePlusBlock V := by
  rw [phasePlusBlock_eq_smul_blockSum, phasePlusBlock_eq_smul_blockSum,
    blockSum_mul_controlledNot]

private theorem phasePlusBlock_controlledNot_mul {N : Nat}
    (V : UnitaryOperator (Qubits (1 + N))) (P : OrthogonalProjector N) :
    phasePlusBlock (OrthogonalProjector.controlledNotOp P * V) =
      phasePlusBlock V := by
  rw [phasePlusBlock_eq_smul_blockSum, phasePlusBlock_eq_smul_blockSum,
    blockSum_controlledNot_mul]

variable {width : Nat} (U : UnitaryOperator (Qubits width))
  (left right : OrthogonalProjector width) (allowControlled : Bool)

private def eventPool
    (event : Resource.Event
      (.quantum AlgorithmGate.model (ProjectedSignal.model U left right allowControlled))) :
    ResourcePool
      (.quantum AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)) :=
  ResourcePool.singleton event

/-- Exact whole-word budget with `L` calls to each projector-controlled NOT. -/
public def budget (L : Nat) :
    ResourcePool
      (.quantum AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)) :=
  ((L + 1) / 2) • eventPool U left right allowControlled
      (.oracle (.source .ordinary)) +
    (L / 2) • eventPool U left right allowControlled (.oracle (.source .inverse)) +
    L • eventPool U left right allowControlled (.oracle .leftNot) +
    L • eventPool U left right allowControlled (.oracle .rightNot) +
    L • eventPool U left right allowControlled (.gate .singleQubit)

/-- The balanced budget contains exactly `L` ordinary-or-inverse source calls. -/
public theorem budget_source_queries (L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model
          (ProjectedSignal.model U left right allowControlled))
        (.oracle (.source .ordinary))
        (budget U left right allowControlled L) +
      ResourcePool.count
        (model := .quantum AlgorithmGate.model
          (ProjectedSignal.model U left right allowControlled))
        (.oracle (.source .inverse))
        (budget U left right allowControlled L) = L := by
  have ordinaryNeInverse :
      (Resource.Event.oracle (.source .ordinary) :
          Resource.Event (.quantum AlgorithmGate.model
            (ProjectedSignal.model U left right allowControlled))) ≠
        .oracle (.source .inverse) := by
    intro same
    have coordinate := Resource.Event.oracle.inj same
    have source := ProjectedSignal.Coordinate.source.inj coordinate
    cases source
  have inverseNeOrdinary := Ne.symm ordinaryNeInverse
  simp [budget, eventPool, ordinaryNeInverse, inverseNeOrdinary]
  omega

/-- The balanced budget contains exactly `L` left-projector calls. -/
public theorem budget_left_projector_queries (L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model
          (ProjectedSignal.model U left right allowControlled))
        (.oracle .leftNot)
        (budget U left right allowControlled L) = L := by
  simp [budget, eventPool]

/-- The balanced budget contains exactly `L` right-projector calls. -/
public theorem budget_right_projector_queries (L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model
          (ProjectedSignal.model U left right allowControlled))
        (.oracle .rightNot)
        (budget U left right allowControlled L) = L := by
  simp [budget, eventPool]

/-- Every positive-degree balanced word has one native rotation per phase. -/
public theorem budget_single_qubit_count (L : Nat) :
    ResourcePool.count
        (model := .quantum AlgorithmGate.model
          (ProjectedSignal.model U left right allowControlled))
        (.gate .singleQubit)
        (budget U left right allowControlled L) = L := by
  simp [budget, eventPool]

private def projectorFlip (useRight : Bool) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  ProjectedSignal.Circuit.projectorFlip AlgorithmGate.model U left right
    allowControlled useRight

private def rotation (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  Gate.singleQubitAt (ProjectorPhase.layout width)
    (ProjectedSignal.model U left right allowControlled) (rotZStdOp (2 * angle))
    (0 : Fin (1 + width)) rfl

/-- The first projector call and rotation of one source phase gadget. -/
private def phasePrefix (useRight : Bool) (angle : ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  (projectorFlip U left right allowControlled useRight).seq
    (rotation U left right allowControlled angle)

private theorem phasePrefix_events (useRight : Bool) (angle : ℝ) :
    (phasePrefix U left right allowControlled useRight angle).eventCost =
      eventPool U left right allowControlled
          (.oracle (if useRight then .rightNot else .leftNot)) +
        eventPool U left right allowControlled (.gate .singleQubit) := by
  rw [phasePrefix, UnitaryCircuit.seq_eventCost,
    projectorFlip, ProjectedSignal.Circuit.projectorFlip_events]
  unfold rotation eventPool
  rfl

private theorem phasePrefix_depth (useRight : Bool) (angle : ℝ) :
    (phasePrefix U left right allowControlled useRight angle).evaluatedEventDepth
        (fun _ => 1) = 2 := by
  rw [phasePrefix, UnitaryCircuit.evaluatedEventDepth_seq,
    projectorFlip, ProjectedSignal.Circuit.projectorFlip_depth]
  unfold rotation
  rfl

private def oddCore (angle : ℝ) (tail : List ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  ((Native.circuit U left right allowControlled tail).seq
      (Native.signal U left right allowControlled false)).seq
    (phasePrefix U left right allowControlled false angle)

/-- Odd words move the final left query to a right query at the input boundary. -/
private def oddCircuit (angle : ℝ) (tail : List ℝ) :
    UnitaryCircuit AlgorithmGate.model (ProjectedSignal.model U left right allowControlled)
      (ProjectorPhase.layout width) :=
  (projectorFlip U left right allowControlled true).seq
    (oddCore U left right allowControlled angle tail)

private theorem oddCircuit_matrix (angle : ℝ) (tail : List ℝ) :
    (oddCircuit U left right allowControlled angle tail).binaryMatrix =
      (oddCore U left right allowControlled angle tail).binaryMatrix *
        OrthogonalProjector.controlledNotOp right := by
  rw [oddCircuit, UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    projectorFlip, ProjectedSignal.Circuit.projectorFlip_matrix]
  simp only [↓reduceIte]

private theorem native_cons_matrix (angle : ℝ) (tail : List ℝ)
    (odd : (tail.length + 1) % 2 ≠ 0) :
    (Native.circuit U left right allowControlled (angle :: tail)).binaryMatrix =
      OrthogonalProjector.controlledNotOp left *
        (oddCore U left right allowControlled angle tail).binaryMatrix := by
  simp only [Native.circuit, odd, decide_false, Bool.false_eq_true, ↓reduceIte,
    oddCore, Native.phase, ProjectorPhase.circuit, phasePrefix,
    projectorFlip, rotation,
    UnitaryCircuit.unitaryCircuit_binaryMatrix_seq,
    ProjectedSignal.Circuit.projectorFlip_matrix]
  rw [mul_assoc]

private theorem oddCircuit_phasePlusBlock (angle : ℝ) (tail : List ℝ)
    (odd : (tail.length + 1) % 2 ≠ 0) :
    phasePlusBlock (oddCircuit U left right allowControlled angle tail).binaryMatrix =
      phasePlusBlock
        (Native.circuit U left right allowControlled (angle :: tail)).binaryMatrix := by
  rw [oddCircuit_matrix, phasePlusBlock_mul_controlledNot,
    native_cons_matrix U left right allowControlled angle tail odd,
    phasePlusBlock_controlledNot_mul]

private theorem oddCircuit_projectedPhasePlusBlock (angle : ℝ) (tail : List ℝ)
    (odd : (tail.length + 1) % 2 ≠ 0)
      (output input : OrthogonalProjector width) :
    projectedPhasePlusBlock output input
        (oddCircuit U left right allowControlled angle tail).binaryMatrix =
      projectedPhasePlusBlock output input
        (Native.circuit U left right allowControlled (angle :: tail)).binaryMatrix := by
  unfold projectedPhasePlusBlock
  rw [oddCircuit_phasePlusBlock U left right allowControlled angle tail odd]

private theorem budget_eq_native_of_even (L : Nat) (even : L % 2 = 0) :
    budget U left right allowControlled L = Native.budget U left right allowControlled L := by
  have halfUpper : (L + 1) / 2 = L / 2 := by omega
  have twiceHalf : 2 * (L / 2) = L := by omega
  simp only [budget, Native.budget, eventPool, Native.eventPool,
    halfUpper, twiceHalf]

private theorem oddCircuit_events (angle : ℝ) (tail : List ℝ)
    (evenTail : tail.length % 2 = 0) :
    (oddCircuit U left right allowControlled angle tail).eventCost =
      budget U left right allowControlled (tail.length + 1) := by
  have halfSucc : (tail.length + 1) / 2 = tail.length / 2 := by omega
  have halfSuccSucc : (tail.length + 1 + 1) / 2 = tail.length / 2 + 1 := by omega
  have twiceHalf : 2 * (tail.length / 2) = tail.length := by omega
  simp only [oddCircuit, oddCore, UnitaryCircuit.seq_eventCost,
    Native.circuit_events, Native.signal_events, phasePrefix_events,
    projectorFlip, ProjectedSignal.Circuit.projectorFlip_events,
    Native.budget, budget, eventPool, Native.eventPool, halfSucc,
    halfSuccSucc, twiceHalf, Bool.false_eq_true, ↓reduceIte,
    one_nsmul, add_nsmul]
  ac_rfl

private theorem oddCircuit_depth (angle : ℝ) (tail : List ℝ) :
    (oddCircuit U left right allowControlled angle tail).evaluatedEventDepth
        (fun _ => 1) = 4 * (tail.length + 1) := by
  simp only [oddCircuit, oddCore, UnitaryCircuit.evaluatedEventDepth_seq,
    projectorFlip, ProjectedSignal.Circuit.projectorFlip_depth, Native.circuit_depth,
    Native.signal_depth, phasePrefix_depth]
  omega

/-- Matching-parity phases admit an actual word with the paper's exact balanced
projector-query counts, the same projected block, and the same full depth. -/
theorem exists_real_word {L : Nat} {PRe : Polynomial ℝ}
    (source : ReflectionQSPPhaseSynthesis.RealBoundedMatchingParity L PRe)
    (positive : 0 < L) :
    ∃ word : UnitaryCircuit AlgorithmGate.model
        (ProjectedSignal.model U left right allowControlled) (ProjectorPhase.layout width),
      projectedPhasePlusBlock (projectedOutputProjector left right L) right
          word.binaryMatrix =
        singularValuePolynomial right L (realPolynomialToComplex PRe)
          (projectedUnitaryBlock left right U) ∧
      word.eventCost = budget U left right allowControlled L ∧
      word.evaluatedEventDepth (fun _ => 1) = 4 * L := by
  obtain ⟨phases, length, block, events, depth⟩ :=
    Native.exists_native_real_word U left right allowControlled source positive
  by_cases even : L % 2 = 0
  · refine ⟨Native.circuit U left right allowControlled phases, block, ?_, depth⟩
    rw [events, ← budget_eq_native_of_even U left right allowControlled L even]
  · cases phases with
    | nil => simp at length; omega
    | cons angle tail =>
      have tailLength : tail.length + 1 = L := by simpa using length
      have oddTail : (tail.length + 1) % 2 ≠ 0 := by omega
      have evenTail : tail.length % 2 = 0 := by omega
      refine ⟨oddCircuit U left right allowControlled angle tail, ?_, ?_, ?_⟩
      · rw [oddCircuit_projectedPhasePlusBlock U left right allowControlled
          angle tail oddTail]
        exact block
      · rw [oddCircuit_events U left right allowControlled angle tail evenTail,
          tailLength]
      · rw [oddCircuit_depth U left right allowControlled angle tail, tailLength]

end
end QuantumAlg.QSP.MultiQubit.QSVT.Native.Balanced
