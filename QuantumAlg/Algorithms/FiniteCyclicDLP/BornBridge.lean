/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.BornBridge.Identity
import QuantumAlg.Init
import all QuantumAlg.Components.Gates
import all QuantumAlg.Core.Base
import all QuantumAlg.Util.FiniteCyclicDLP
import all QuantumAlg.Core.Algorithm.QuantumState
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Util.Complex
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Util.PMF
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Access

/-!
# Born bridge for canonical finite-cyclic DLP access

This bridge derives raw terminal measurement probabilities from the actual
caller-supplied `U_unif` and `U_x` circuit.  It does not normalize, decode, or
otherwise constrain the classical terminal outcome.
-/

section

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP
namespace Canonical
namespace BornBridge

universe u

variable {G : Type u} [Group G]

/-- The normalized quantum state obtained by applying the stored canonical
circuit to its sealed computational-basis input preparation. -/
def evolvedState {P : KnownOrderProblem G} (A : Access P) :
    QubitLayout.State (layout P) where
  state := PureState.ofNormalized
    ((quantumCircuit A).applyNormalized (inputPreparation A).normalized)
    (layout P).systemIdx
  system_idx_eq := rfl

@[simp] theorem evolvedState_normalized {P : KnownOrderProblem G}
    (A : Access P) :
    (evolvedState A).normalized =
      (quantumCircuit A).applyNormalized (inputPreparation A).normalized :=
  rfl

/-- The two source exponent states tensored with the encoded group identity,
immediately after the external `U_unif` calls. -/
def preparedVec {P : KnownOrderProblem G} (A : Access P) :
    HilbertVector (Qubits (totalQubits P)) :=
  HilbertVector.tensor
    (HilbertVector.tensor
      (exponentState P : HilbertVector (Qubits (orderWidth P)))
      (exponentState P : HilbertVector (Qubits (orderWidth P))))
    (NormalizedVector.ket (R := Qubits (orderWidth P)) (A.ux.encode 1) :
      HilbertVector (Qubits (orderWidth P)))

/-- The two externally supplied `U_unif` leaves prepare the source state from
the actual encoded-identity computational-basis input. -/
theorem uniformCircuit_apply_input {P : KnownOrderProblem G}
    (A : Access P) :
    (uniformCircuit A).applyVec
        ((inputPreparation A).normalized : HilbertVector (Qubits (totalQubits P))) =
      preparedVec A := by
  rw [inputPreparation_normalized]
  change (uniformCircuit A).applyVec
      (NormalizedVector.ket (R := Qubits (totalQubits P))
        (prodEquiv
          (prodEquiv
            ((0 : Fin (2 ^ orderWidth P)),
              (0 : Fin (2 ^ orderWidth P))),
            A.ux.encode 1)) : HilbertVector (Qubits (totalQubits P))) = _
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  change (uniformCircuit A).matrix.applyVec
      (HilbertVector.tensor
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P)))
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))))
        (NormalizedVector.ket (R := Qubits (orderWidth P)) (A.ux.encode 1) :
          HilbertVector (Qubits (orderWidth P)))) = _
  rw [uniformCircuit, withGroupWorkspace, UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((pairConsecutiveCircuit (uniformPreparationCircuit A) _).applyVec _)
      ((UnitaryCircuit.identity (Qubits (orderWidth P))
        (List.range' (orderWidth P + orderWidth P) (orderWidth P))
        List.nodup_range').applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  rw [pairConsecutiveCircuit, UnitaryCircuit.applyVec, UnitaryCircuit.tensorQubits_matrix,
    UnitaryCircuit.shiftPhysicalIdx_matrix, UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      (A.uniform.operator.applyVec
        (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
          HilbertVector (Qubits (orderWidth P))))
      (A.uniform.operator.applyVec
        (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
          HilbertVector (Qubits (orderWidth P)))) = _
  have hprepare :
      A.uniform.operator.applyVec
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))) =
        (exponentState P : HilbertVector (Qubits (orderWidth P))) :=
    congrArg (fun state : NormalizedVector (Qubits (orderWidth P)) =>
      (state : HilbertVector (Qubits (orderWidth P)))) A.uniform.apply_zero
  rw [hprepare]

/-- Raw post-oracle state before the two inverse-QFT readouts. -/
def postUxVec {P : KnownOrderProblem G} (A : Access P) :
    HilbertVector (Qubits (totalQubits P)) :=
  A.ux.operator.applyVec (preparedVec A)

@[simp] theorem preparedVec_apply {P : KnownOrderProblem G}
    (A : Access P) (left right workspace : Fin (2 ^ orderWidth P)) :
    preparedVec A (tripleIndex left right workspace) =
      if workspace = A.ux.encode 1 then
        if right.val < P.order then
          if left.val < P.order then
            invSqrtOrder P.order * invSqrtOrder P.order
          else
            0
        else
          0
      else
        0 := by
  simp [preparedVec, tripleIndex, exponentState_apply,
    NormalizedVector.ket_apply]

/-- The `U_x` action equation determines each matrix entry in the encoded
identity column used by the actual circuit. -/
theorem ux_matrix_entry_identity {P : KnownOrderProblem G}
    (A : Access P) (output : Fin (2 ^ totalQubits P))
    (left right : Fin (2 ^ orderWidth P)) :
    (A.ux.operator : HilbertOperator (Qubits (totalQubits P)))
        output (tripleIndex left right (A.ux.encode 1)) =
      if output = tripleIndex left right
          (A.ux.encode (P.toSourceScope.oracleMultiplier left.val right.val)) then
        1
      else
        0 := by
  have haction := congrArg
    (fun state : NormalizedVector (Qubits (totalQubits P)) =>
      (state : HilbertVector (Qubits (totalQubits P))) output)
    (A.ux.basisAction left right 1)
  simpa [UnitaryOperator.apply_coe, UnitaryOperator.applyVec,
    HilbertOperator.applyVec_ket, NormalizedVector.ket_apply] using haction

/-- The actual `U_x` call maps the prepared source support to its encoded
group-multiplier fibers while retaining both exponent labels. -/
theorem postUxVec_apply {P : KnownOrderProblem G}
    (A : Access P) (left right workspace : Fin (2 ^ orderWidth P)) :
    postUxVec A (tripleIndex left right workspace) =
      if right.val < P.order then
        if left.val < P.order then
          if workspace =
              A.ux.encode (P.toSourceScope.oracleMultiplier left.val right.val) then
            invSqrtOrder P.order * invSqrtOrder P.order
          else
            0
        else
          0
      else
        0 := by
  classical
  unfold postUxVec
  change (∑ source : Fin (2 ^ totalQubits P),
      (A.ux.operator : HilbertOperator (Qubits (totalQubits P)))
          (tripleIndex left right workspace) source * preparedVec A source) = _
  rw [← Equiv.sum_comp (prodEquiv
    (m := orderWidth P + orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  change (∑ sourceLeft : Fin (2 ^ orderWidth P),
      ∑ sourceRight : Fin (2 ^ orderWidth P),
      ∑ sourceWorkspace : Fin (2 ^ orderWidth P),
        (A.ux.operator : HilbertOperator (Qubits (totalQubits P)))
            (tripleIndex left right workspace)
            (tripleIndex sourceLeft sourceRight sourceWorkspace) *
          preparedVec A
            (tripleIndex sourceLeft sourceRight sourceWorkspace)) = _
  simp_rw [preparedVec_apply]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq']
  have hmatrix (sourceLeft sourceRight : Fin (2 ^ orderWidth P)) :
      (A.ux.operator : HilbertOperator (Qubits (totalQubits P)))
          (tripleIndex left right workspace)
          (tripleIndex sourceLeft sourceRight (A.ux.encode 1)) =
        if tripleIndex left right workspace =
            tripleIndex sourceLeft sourceRight
              (A.ux.encode (P.toSourceScope.oracleMultiplier
                sourceLeft.val sourceRight.val)) then
          1
        else
          0 :=
    ux_matrix_entry_identity A (tripleIndex left right workspace)
      sourceLeft sourceRight
  simp_rw [hmatrix]
  rw [Fintype.sum_eq_single left]
  · rw [Fintype.sum_eq_single right]
    · simp [tripleIndex]
    · intro sourceRight hne
      simp [tripleIndex, Ne.symm hne]
  · intro sourceLeft hne
    simp [tripleIndex, Ne.symm hne]

/-- The first two stored circuit stages produce the exact raw state used by
the analytical inverse-QFT readout formula. -/
theorem ux_apply_uniform {P : KnownOrderProblem G}
    (A : Access P) :
    (uxCircuit A).applyVec
        ((uniformCircuit A).applyVec
          ((inputPreparation A).normalized :
            HilbertVector (Qubits (totalQubits P)))) =
      postUxVec A := by
  rw [uniformCircuit_apply_input]
  rfl

/-- The source-compatible inverse-QFT amplitude obtained from the actual
post-`U_x` vector. -/
def circuitAmplitude {P : KnownOrderProblem G} (A : Access P)
    (left right workspace : Fin (2 ^ orderWidth P)) : ℂ :=
  ∑ sourceLeft : Fin (2 ^ orderWidth P),
    ∑ sourceRight : Fin (2 ^ orderWidth P),
      star (invSqrtN (orderWidth P) *
        ω (orderWidth P) ^ (sourceLeft.val * left.val)) *
      star (invSqrtN (orderWidth P) *
        ω (orderWidth P) ^ (sourceRight.val * right.val)) *
      postUxVec A (tripleIndex sourceLeft sourceRight workspace)

/-- Every final-basis amplitude is derived from the stored caller-supplied
prepare-query-readout circuit, rather than from an independent probability
kernel. -/
theorem circuit_amplitude {P : KnownOrderProblem G} (A : Access P)
    (left right workspace : Fin (2 ^ orderWidth P)) :
    (evolvedState A).normalized (tripleIndex left right workspace) =
      circuitAmplitude A left right workspace := by
  change UnitaryCircuit.applyVec (quantumCircuit A)
      (NormalizedVector.ket (R := Qubits (totalQubits P))
        (tripleIndex (0 : Fin (2 ^ orderWidth P))
          (0 : Fin (2 ^ orderWidth P)) (A.ux.encode 1)) :
          HilbertVector (Qubits (totalQubits P)))
      (tripleIndex left right workspace) = _
  rw [← inputPreparation_normalized A]
  rw [quantumCircuit, UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq,
    ux_apply_uniform]
  change HilbertOperator.applyVec
      ((inverseQFTCircuit P).matrix :
        HilbertOperator (Qubits (totalQubits P)))
      (postUxVec A) (tripleIndex left right workspace) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp (prodEquiv
      (m := orderWidth P + orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  simp only [inverseQFTCircuit, withGroupWorkspace, pairConsecutiveCircuit,
    UnitaryCircuit.tensorQubits_matrix, UnitaryCircuit.shiftPhysicalIdx_matrix,
    UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    UnitaryCircuit.dagger_matrix, QFTCircuit_matrix, Matrix.conjTranspose_apply,
    QFTOperator_entry, identityCircuit_entry]
  rw [circuitAmplitude]
  apply Finset.sum_congr rfl
  intro sourceLeft _
  apply Finset.sum_congr rfl
  intro sourceRight _
  rw [Finset.sum_eq_single workspace]
  · simp [tripleIndex, mul_assoc]
  · intro sourceWorkspace _ hne
    simp [tripleIndex, Ne.symm hne]
  · simp

@[simp] theorem terminalMeasurement_readout_triple {P : KnownOrderProblem G}
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P)))
    (workspace : Fin (2 ^ orderWidth P)) :
    (terminalMeasurement P).readout (prodEquiv (leftRight, workspace)) =
      measurementOutcome P leftRight := by
  funext outputIndex
  change (prodEquiv (leftRight, workspace)).val.testBit
      (totalQubits P - 1 - outputIndex.val) =
    leftRight.val.testBit
      (orderWidth P + orderWidth P - 1 - outputIndex.val)
  have hindex :
      totalQubits P - 1 - outputIndex.val =
        orderWidth P +
          (orderWidth P + orderWidth P - 1 - outputIndex.val) := by
    unfold totalQubits
    omega
  rw [hindex]
  exact prodEquiv_testBit_left leftRight workspace
    ⟨orderWidth P + orderWidth P - 1 - outputIndex.val, by omega⟩

theorem terminalMeasurement_readout_eq_outcome_iff {P : KnownOrderProblem G}
    (basis : Fin (2 ^ totalQubits P))
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    (terminalMeasurement P).readout basis = measurementOutcome P leftRight ↔
      (prodEquiv.symm basis).1 = leftRight := by
  have hself :
      (terminalMeasurement P).readout basis =
        measurementOutcome P (prodEquiv.symm basis).1 := by
    simpa using terminalMeasurement_readout_triple
      (P := P) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro equality
    exact measurementOutcome_injective P (hself.symm.trans equality)
  · intro equality
    exact hself.trans (congrArg (measurementOutcome P) equality)

/-- Embed the unmeasured encoded workspace basis into one raw terminal-outcome
fiber. -/
def measurementFiberEmbedding {P : KnownOrderProblem G}
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    Fin (2 ^ orderWidth P) ↪ Fin (2 ^ totalQubits P) where
  toFun := fun workspace => prodEquiv (leftRight, workspace)
  inj' := by
    intro left right equality
    cases prodEquiv.injective equality
    rfl

@[simp] theorem measurementFiberEmbedding_apply {P : KnownOrderProblem G}
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P)))
    (workspace : Fin (2 ^ orderWidth P)) :
    measurementFiberEmbedding leftRight workspace =
      prodEquiv (leftRight, workspace) := rfl

theorem terminalMeasurement_fiber {P : KnownOrderProblem G}
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ totalQubits P) =>
          (terminalMeasurement P).readout basis = measurementOutcome P leftRight) =
      Finset.univ.map (measurementFiberEmbedding leftRight) := by
  ext basis
  rw [Finset.mem_filter, terminalMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [measurementFiberEmbedding_apply, ← hleft]
    exact (Equiv.apply_symm_apply
      (prodEquiv (m := orderWidth P + orderWidth P) (n := orderWidth P)) basis)
  · intro hmem
    obtain ⟨workspace, _, hworkspace⟩ := Finset.mem_map.mp hmem
    change prodEquiv (leftRight, workspace) = basis at hworkspace
    rw [← hworkspace, Equiv.symm_apply_apply]

/-- The actual raw terminal Born probability is the workspace marginal of the
source-compatible amplitude derived above. -/
theorem bornOutcomeProbability_eq_sourceMarginal {P : KnownOrderProblem G}
    (A : Access P) (left right : Fin (2 ^ orderWidth P)) :
    (terminalMeasurement P).outcomePMF (evolvedState A)
        (measurementOutcome P (prodEquiv (left, right))) =
      ∑ workspace : Fin (2 ^ orderWidth P),
        ENNReal.ofReal (‖circuitAmplitude A left right workspace‖ ^ 2) := by
  classical
  rw [TerminalZMeasure.outcomePMF_apply,
    terminalMeasurement_fiber, Finset.sum_map]
  simp_rw [measurementFiberEmbedding_apply]
  change (∑ workspace : Fin (2 ^ orderWidth P),
      ENNReal.ofReal
        (‖(evolvedState A).normalized
          (tripleIndex left right workspace)‖ ^ 2)) = _
  simp_rw [circuit_amplitude]

end BornBridge
end Canonical
end FiniteCyclicDLP

end

end QuantumAlg

end
