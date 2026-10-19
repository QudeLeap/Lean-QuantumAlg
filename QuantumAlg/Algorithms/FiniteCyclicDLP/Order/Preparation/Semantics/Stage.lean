/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Gap
public import QuantumAlg.Core.Base.UnitaryCircuit.Vector
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.Preparation.Semantics.Gap
import all QuantumAlg.Core.Base.UnitaryCircuit.Vector

/-!
# Literal native semantics of one positive-gap preparation stage

The circuit definitions in this module use the same physical wires and
native open-control words as the intrinsic Shukla--Vedula schedule.  Their
raw-vector equations form the local induction step used by the complete
range-preparation proof.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion

noncomputable section

variable {N : Nat}

private lemma oneQubitLabel_eq_one_of_testBit_true (bit : Fin (2 ^ 1))
    (set : bit.val.testBit 0 = true) : bit = 1 := by
  fin_cases bit <;> simp_all

/-- One literal open-controlled Hadamard at an increasing logical offset of
the selected gap. -/
public def gapHadamardAt (oracles : OracleModel)
    (b : PositiveGapExpansion N) (gap : Fin b.gaps)
    (offset : Fin (b.gapWidth gap)) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout :=
  UnitaryCircuit.onBinarySeparated (b.wire gap.succ)
    (b.gapTargetWire gap offset)
    (b.wire_succ_lt_gapTargetWire gap offset)
    (Gate.OpenControl.hadamard oracles)

/-- The actual gap-H instruction advances the explicit raw partial state by
one target. -/
public lemma gapHadamardAt_applyVec_gapHPartial (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) (processed : Nat)
    (notFinished : processed < b.gapWidth gap) :
    ((b.gapHadamardAt oracles gap ⟨processed, notFinished⟩).applyBinaryVec environment)
        (b.gapHPartial gap processed (Nat.le_of_lt notFinished)) =
      b.gapHPartial gap (processed + 1) (Nat.succ_le_of_lt notFinished) := by
  rw [b.gapHPartial_eq_hSeparated gap processed notFinished]
  unfold UnitaryCircuit.applyBinaryVec
  unfold gapHadamardAt
  rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_applyVec,
    Gate.OpenControl.hadamard_applyVec_ket0_tensor_ket0]
  exact (b.gapHPartial_succ_eq_hSeparatedPlus gap processed notFinished).symm

/-- A gap Hadamard is inactive on every residual block accepted before its
high source control. -/
public lemma gapHadamardAt_applyVec_residual_eq_self
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) (offset : Fin (b.gapWidth gap))
    {accepted : Fin (b.gaps + 1)}
    (acceptedBefore : accepted.val < gap.succ.val) :
    ((b.gapHadamardAt oracles gap offset).applyBinaryVec environment)
        (b.residualBlock accepted) = b.residualBlock accepted := by
  unfold gapHadamardAt
  apply UnitaryCircuit.unitaryCircuit_onBinarySeparated_applyVec_eq_self_of_basis_support
  intro leading first middle second suffix nonzero
  have support : b.residualSupport accepted
      (UnitaryCircuit.binarySeparatedBasisLabel
        (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset)
        leading first middle second suffix).val := by
    by_contra outside
    exact nonzero (b.residualBlock_apply_of_not_support accepted _ outside)
  have sourceBit := b.residualSupport_testBit_true_of_lt acceptedBefore support
  have controlBit :
      (UnitaryCircuit.binarySeparatedBasisLabel
        (b.wire gap.succ) (b.gapTargetWire gap offset)
        (b.wire_succ_lt_gapTargetWire gap offset)
        leading first middle second suffix).val.testBit
          (WireAddress.bitIndex (b.wire gap.succ)).val = true := by
    rw [b.bitIndex_wire gap.succ]
    exact sourceBit
  rw [UnitaryCircuit.binarySeparatedBasisLabel_testBit_first] at controlBit
  have firstOne := oneQubitLabel_eq_one_of_testBit_true first controlBit
  subst first
  rw [Gate.OpenControl.hadamard_binaryMatrix]
  change (UnitaryOperator.controlledQubitsOnZero Gate.HOp).applyVec
      ((NormalizedVector.ket1 : HilbertVector (Qubits 1)).tensor
        (NormalizedVector.ket (R := Qubits 1) second :
          HilbertVector (Qubits 1))) = _
  rw [UnitaryOperator.controlledQubitsOnZero_applyVec_ket1_tensor]
  rfl

/-- The literal increasing sweep of open-controlled Hadamards through one
strict binary gap. -/
public def gapHadamards (oracles : OracleModel)
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout :=
  .indexedProduct "sv24-intrinsic-gap-hadamards" (b.gapWidth gap)
    (.identity AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout)
    (b.gapHadamardAt oracles gap)

/-- The complete gap-H sweep is inactive on every previously accepted
residual block. -/
public lemma gapHadamards_applyVec_residual_eq_self
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) {accepted : Fin (b.gaps + 1)}
    (acceptedBefore : accepted.val < gap.succ.val) :
    ((b.gapHadamards oracles gap).applyBinaryVec environment) (b.residualBlock accepted) =
      b.residualBlock accepted := by
  unfold gapHadamards
  apply UnitaryCircuit.applyBinaryVec_indexedProduct_eq_self_of_each
  · exact UnitaryCircuit.applyBinaryVec_identity _ environment
  · intro offset
    exact b.gapHadamardAt_applyVec_residual_eq_self
      oracles gap offset acceptedBefore

/-- Every finite leading of the literal gap-H sweep advances the partial-state
index by its leading length. -/
public lemma gapHPartial_foldl_applyVec (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    ∀ (count : Nat) (bounded : count ≤ b.gapWidth gap),
      (List.ofFn (fun index : Fin count =>
        b.gapHadamardAt oracles gap (Fin.castLE bounded index))).foldl
          (fun state circuit => (circuit.applyBinaryVec environment) state)
          (b.gapHPartial gap 0 (Nat.zero_le _)) =
        b.gapHPartial gap count bounded := by
  intro count
  induction count with
  | zero =>
      intro _
      simp
  | succ count induction =>
      intro bounded
      have previous : count ≤ b.gapWidth gap := Nat.le_of_succ_le bounded
      have next : count < b.gapWidth gap := by omega
      have leading :
          (List.ofFn (fun index : Fin count =>
            b.gapHadamardAt oracles gap
              (Fin.castLE bounded index.castSucc))).foldl
              (fun state circuit => (circuit.applyBinaryVec environment) state)
              (b.gapHPartial gap 0 (Nat.zero_le _)) =
            b.gapHPartial gap count previous := by
          simpa using induction previous
      have last : Fin.castLE bounded (Fin.last count) =
          (⟨count, next⟩ : Fin (b.gapWidth gap)) := by
        apply Fin.ext
        rfl
      rw [List.ofFn_succ', List.concat_eq_append, List.foldl_concat,
        leading, last]
      simpa using b.gapHadamardAt_applyVec_gapHPartial
        oracles gap count next

/-- The complete actual gap-H sweep maps its newly opened zero branch to the
next aligned residual block. -/
public lemma gapHadamards_applyVec_active (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    ((b.gapHadamards oracles gap).applyBinaryVec environment)
        (b.gapHPartial gap 0 (Nat.zero_le _)) =
      b.residualBlock gap.succ := by
  unfold gapHadamards
  rw [UnitaryCircuit.applyBinaryVec_indexedProduct,
    UnitaryCircuit.applyBinaryVec_identity]
  calc
    (List.ofFn (b.gapHadamardAt oracles gap)).foldl
          (fun state circuit => (circuit.applyBinaryVec environment) state)
          (b.gapHPartial gap 0 (Nat.zero_le _)) =
        b.gapHPartial gap (b.gapWidth gap) (Nat.le_refl _) := by
          simpa using b.gapHPartial_foldl_applyVec oracles gap
            (b.gapWidth gap) (Nat.le_refl _)
    _ = b.residualBlock gap.succ :=
      b.gapHPartial_final_eq_residualBlock gap

/-- The one-qubit source rotation used by the first literal gap stage. -/
public def initialSourceRotation (oracles : OracleModel)
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout :=
  UnitaryCircuit.onBinaryWire (b.wire gap.succ)
    (OrderPreparation.Intrinsic.singleQubit oracles (rotYOp (b.sourceAngle gap)))

/-- The actual uncontrolled first source rotation has the same two-branch
equation as every later controlled source rotation on the active residual. -/
public lemma initialSourceRotation_applyVec_residual
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    ((b.initialSourceRotation oracles gap).applyBinaryVec environment)
        (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) •
          b.gapHPartial gap 0 (Nat.zero_le _) +
      (Real.cos (b.sourceAngle gap / 2) : ℂ) •
          b.residualBlock gap.castSucc := by
  rw [b.residualBlock_eq_rotationWire gap]
  unfold UnitaryCircuit.applyBinaryVec
  unfold initialSourceRotation
  rw [UnitaryCircuit.unitaryCircuit_onBinaryWire_applyVec,
    OrderPreparation.Intrinsic.singleQubit_binaryMatrix,
    rotYOp_applyVec_ket1]
  rw [UnitaryCircuit.binaryWireVec_add_active,
    UnitaryCircuit.binaryWireVec_smul_active,
    UnitaryCircuit.binaryWireVec_smul_active]
  rw [← b.gapHPartial_zero_eq_rotationWire gap,
    ← b.residualBlock_eq_rotationWire gap]

/-- The literal reoriented open-controlled source rotation for a noninitial
gap. -/
public def controlledSourceRotation (oracles : OracleModel)
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout :=
  UnitaryCircuit.onBinarySeparated (b.wire gap.succ) (b.wire gap.castSucc)
    (b.wire_succ_lt_wire gap)
    (Gate.OpenControl.rotYRight oracles (b.sourceAngle gap))

/-- The actual open-controlled source rotation splits the current residual
into its new zero branch and retained one branch with exact signed
coefficients. -/
public lemma controlledSourceRotation_applyVec_residual
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    ((b.controlledSourceRotation oracles gap).applyBinaryVec environment)
        (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) •
          b.gapHPartial gap 0 (Nat.zero_le _) +
      (Real.cos (b.sourceAngle gap / 2) : ℂ) •
          b.residualBlock gap.castSucc := by
  rw [b.residualBlock_eq_rotationSeparated gap]
  unfold UnitaryCircuit.applyBinaryVec
  unfold controlledSourceRotation
  rw [UnitaryCircuit.unitaryCircuit_onBinarySeparated_applyVec,
    Gate.OpenControl.rotYRight_applyVec_ket1_tensor_ket0]
  rw [UnitaryCircuit.binarySeparatedVec_add_active,
    UnitaryCircuit.binarySeparatedVec_smul_active,
    UnitaryCircuit.binarySeparatedVec_smul_active]
  rw [← b.gapHPartial_zero_eq_rotationSeparated gap,
    ← b.residualBlock_eq_rotationSeparated gap]

/-- A later controlled source rotation is inactive on every residual block
accepted before its trailing source control. -/
public lemma controlledSourceRotation_applyVec_residual_eq_self
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) {accepted : Fin (b.gaps + 1)}
    (acceptedBefore : accepted.val < gap.castSucc.val) :
    ((b.controlledSourceRotation oracles gap).applyBinaryVec environment)
        (b.residualBlock accepted) = b.residualBlock accepted := by
  unfold controlledSourceRotation
  apply UnitaryCircuit.unitaryCircuit_onBinarySeparated_applyVec_eq_self_of_basis_support
  intro leading first middle second suffix nonzero
  have support : b.residualSupport accepted
      (UnitaryCircuit.binarySeparatedBasisLabel
        (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap) leading first middle second suffix).val := by
    by_contra outside
    exact nonzero (b.residualBlock_apply_of_not_support accepted _ outside)
  have sourceBit := b.residualSupport_testBit_true_of_lt acceptedBefore support
  have controlBit :
      (UnitaryCircuit.binarySeparatedBasisLabel
        (b.wire gap.succ) (b.wire gap.castSucc)
        (b.wire_succ_lt_wire gap) leading first middle second suffix).val.testBit
          (WireAddress.bitIndex (b.wire gap.castSucc)).val = true := by
    rw [b.bitIndex_wire gap.castSucc]
    exact sourceBit
  rw [UnitaryCircuit.binarySeparatedBasisLabel_testBit_second] at controlBit
  have secondOne := oneQubitLabel_eq_one_of_testBit_true second controlBit
  subst second
  rw [Gate.OpenControl.rotYRight_binaryMatrix]
  change (Gate.OpenControl.rightControlledQubitsOnZero
      (rotYOp (b.sourceAngle gap))).applyVec
      ((NormalizedVector.ket (R := Qubits 1) first :
          HilbertVector (Qubits 1)).tensor
        (NormalizedVector.ket1 : HilbertVector (Qubits 1))) = _
  rw [Gate.OpenControl.rightControlledQubitsOnZero_applyVec_tensor_ket1]
  rfl

/-- One literal positive-gap stage: its source rotation followed by the
increasing open-controlled Hadamard sweep. -/
public def gapStage (oracles : OracleModel) (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) :
    UnitaryCircuit AlgorithmGate.model oracles
      (QuantumSignature.qubits b.width).canonicalPlacement.layout :=
  let rotation := if gap.val = 0 then
      b.initialSourceRotation oracles gap
    else b.controlledSourceRotation oracles gap
  rotation.seq (b.gapHadamards oracles gap)

/-- One actual stage splits the current residual into the next accepted block
and the retained residual with the exact rotation coefficients. -/
public lemma gapStage_applyVec_residual (oracles : OracleModel)
    {environment : oracles.Interpretation}
    (b : PositiveGapExpansion N) (gap : Fin b.gaps) :
    ((b.gapStage oracles gap).applyBinaryVec environment) (b.residualBlock gap.castSucc) =
      (-(Real.sin (b.sourceAngle gap / 2)) : ℂ) •
          b.residualBlock gap.succ +
        (Real.cos (b.sourceAngle gap / 2) : ℂ) •
          b.residualBlock gap.castSucc := by
  have retained :
      ((b.gapHadamards oracles gap).applyBinaryVec environment)
          (b.residualBlock gap.castSucc) = b.residualBlock gap.castSucc :=
    b.gapHadamards_applyVec_residual_eq_self
      oracles gap (accepted := gap.castSucc) (by simp)
  unfold gapStage
  split_ifs
  · rw [UnitaryCircuit.applyBinaryVec_seq,
      b.initialSourceRotation_applyVec_residual oracles gap,
      UnitaryCircuit.applyBinaryVec_add, UnitaryCircuit.applyBinaryVec_smul,
      UnitaryCircuit.applyBinaryVec_smul,
      b.gapHadamards_applyVec_active oracles gap, retained]
  · rw [UnitaryCircuit.applyBinaryVec_seq,
      b.controlledSourceRotation_applyVec_residual oracles gap,
      UnitaryCircuit.applyBinaryVec_add, UnitaryCircuit.applyBinaryVec_smul,
      UnitaryCircuit.applyBinaryVec_smul,
      b.gapHadamards_applyVec_active oracles gap, retained]

/-- Every later literal stage fixes each residual block accepted by an
earlier stage. -/
public lemma gapStage_applyVec_residual_eq_self
    (oracles : OracleModel)
    {environment : oracles.Interpretation} (b : PositiveGapExpansion N)
    (gap : Fin b.gaps) {accepted : Fin (b.gaps + 1)}
    (acceptedBefore : accepted.val < gap.castSucc.val) :
    ((b.gapStage oracles gap).applyBinaryVec environment) (b.residualBlock accepted) =
      b.residualBlock accepted := by
  unfold gapStage
  split_ifs with first
  · exfalso
    have gapZero : gap.castSucc.val = 0 := by simpa using first
    omega
  · rw [UnitaryCircuit.applyBinaryVec_seq,
      b.controlledSourceRotation_applyVec_residual_eq_self
        oracles gap acceptedBefore,
      b.gapHadamards_applyVec_residual_eq_self oracles gap
        (lt_trans acceptedBefore (by simp))]

end

end QuantumAlg.FiniteCyclicDLP.OrderExpansion.PositiveGapExpansion
