/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.Circuit.Unitary
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation.State
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Algorithms.FiniteCyclicDLP.BornBridge.Identity
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.QFT.Construction
import all QuantumAlg.Util.Complex

/-!
# Concrete finite-cyclic terminal Born state

The evolved vector, inverse-Fourier amplitudes and terminal probability
are derived from the same encoded unitary experiment. The complete raw
tail is summed without introducing a preparation or repetition wrapper.
-/

namespace QuantumAlg

open NormalizedVector
open scoped BigOperators

noncomputable section

namespace FiniteCyclicDLP.Concrete.BornBridge

universe u

variable {G : Type u} [Group G]
variable {P : KnownOrderProblem G}

/-- Pack two Fourier labels and one raw implementation-tail basis label. -/
def fullIndex (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    Fin (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)) :=
  prodEquiv (prodEquiv (left, right), tail)

/-- Encoding a semantic triple uses the same packed basis index as the
concrete circuit. -/
theorem encoding_encode (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P)) (tail : A.Tail) :
    A.encoding.encode ((left, right), tail) =
      fullIndex A left right (A.tailEncoding.encode tail) :=
  rfl

/-- Actual normalized mathematical state produced by the concrete full circuit.

This deliberately carries no `PureState` resource metadata: the strict
code-native access and the legacy preparation-cost wrapper must not be joined
by a conversion API merely to state a Born probability. -/
def evolvedState (A : ConcreteCircuitAccess P) :
    NormalizedVector
      (Qubits (orderWidth P + orderWidth P + A.tailEncoding.width)) :=
  A.fullCircuit.applyNormalized A.preparation.normalized

/-- State immediately before the concrete implementation oracle: two exact
source-range superpositions and the encoded clean group identity. -/
def preparedVec (A : ConcreteCircuitAccess P) :
    HilbertVector
      (Qubits (orderWidth P + orderWidth P + A.tailEncoding.width)) :=
  HilbertVector.tensor
    (HilbertVector.tensor
      (exponentState P : HilbertVector (Qubits (orderWidth P)))
      (exponentState P : HilbertVector (Qubits (orderWidth P))))
    (NormalizedVector.ket
      (R := Qubits A.tailEncoding.width)
      (A.tailEncoding.encode (A.cleanTail 1)) :
      HilbertVector (Qubits A.tailEncoding.width))

/-- The concrete preparation circuit maps the canonical clean input to
`preparedVec`. -/
theorem preparation_apply_input (A : ConcreteCircuitAccess P) :
    A.preparationCircuit.applyVec
        (NormalizedVector.ket
          (R := Qubits
            (orderWidth P + orderWidth P + A.tailEncoding.width))
          (fullIndex A 0 0
            (A.tailEncoding.encode (A.cleanTail 1))) :
          HilbertVector
            (Qubits
              (orderWidth P + orderWidth P + A.tailEncoding.width))) =
      preparedVec A := by
  unfold fullIndex
  rw [← NormalizedVector.tensor_ket, ← NormalizedVector.tensor_ket]
  change A.preparationCircuit.matrix.applyVec
      (HilbertVector.tensor
        (HilbertVector.tensor
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P)))
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))))
        (NormalizedVector.ket (R := Qubits A.tailEncoding.width)
          (A.tailEncoding.encode (A.cleanTail 1)) :
          HilbertVector (Qubits A.tailEncoding.width))) = _
  rw [ConcreteCircuitAccess.preparationCircuit,
    ConcreteCircuitAccess.extendWithTail,
    UnitaryCircuit.tensorQubits_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  change HilbertVector.tensor
      ((ConcreteCircuitAccess.exponentPreparationCircuit P).applyVec _)
      ((UnitaryCircuit.identity (Qubits A.tailEncoding.width) _ _).applyVec _) = _
  rw [UnitaryCircuit.applyVec_identity]
  congr 1
  simp only [ConcreteCircuitAccess.exponentPreparationCircuit,
    ConcreteCircuitAccess.pairConsecutiveCircuit, UnitaryCircuit.applyVec,
    UnitaryCircuit.tensorQubits_matrix, UnitaryCircuit.shiftPhysicalIdx_matrix,
    UnitaryOperator.tensor_applyVec_tensor]
  rw [rangePreparationCircuit_matrix]
  have hprepare :
      (rangePreparationOperator P.order (orderWidth P) P.order_pos
          (order_le_fourierModulus P)).applyVec
          (NormalizedVector.ket (R := Qubits (orderWidth P)) 0 :
            HilbertVector (Qubits (orderWidth P))) =
        (exponentState P : HilbertVector (Qubits (orderWidth P))) :=
    congrArg
      (fun state : NormalizedVector (Qubits (orderWidth P)) =>
        (state : HilbertVector (Qubits (orderWidth P))))
      (rangePreparationOperator_apply_zero P.order (orderWidth P)
        P.order_pos (order_le_fourierModulus P))
  rw [hprepare]

/-- Raw state after the concrete implementation oracle and before inverse-QFT
readout. -/
def postOracleVec (A : ConcreteCircuitAccess P) :
    HilbertVector
      (Qubits (orderWidth P + orderWidth P + A.tailEncoding.width)) :=
  A.oracleCircuit.applyVec (preparedVec A)

@[simp] theorem preparedVec_apply (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    preparedVec A (fullIndex A left right tail) =
      if tail = A.tailEncoding.encode (A.cleanTail 1) then
        if right.val < P.order then
          if left.val < P.order then
            invSqrtOrder P.order * invSqrtOrder P.order
          else 0
        else 0
      else 0 := by
  simp [preparedVec, fullIndex, exponentState_apply,
    NormalizedVector.ket_apply]

/-- Matrix column forced by the concrete clean-tail basis action. -/
theorem oracle_matrix_entry_identity (A : ConcreteCircuitAccess P)
    (output : Fin
      (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)))
    (left right : Fin (2 ^ orderWidth P)) :
    A.oracleCircuit.matrix output
        (fullIndex A left right
          (A.tailEncoding.encode (A.cleanTail 1))) =
      if output = fullIndex A left right
          (A.tailEncoding.encode
            (A.cleanTail
              (P.toSourceScope.oracleMultiplier left.val right.val))) then
        1
      else 0 := by
  have haction := congrArg
    (fun state : NormalizedVector
        (Qubits
          (orderWidth P + orderWidth P + A.tailEncoding.width)) =>
      (state : HilbertVector
        (Qubits
          (orderWidth P + orderWidth P + A.tailEncoding.width))) output)
    (A.oracleCircuit_apply_clean left right 1)
  simp only [UnitaryOperator.apply_coe, UnitaryCircuit.applyNormalized,
    UnitaryOperator.applyVec, HilbertOperator.applyVec_ket,
    NormalizedVector.ket_apply,
    ConcreteCircuitAccess.cleanState] at haction
  unfold fullIndex
  convert haction using 1 <;>
    simp [ConcreteCircuitAccess.encoding,
      ConcreteCircuitAccess.exponentEncoding]

/-- Exact amplitude support after applying the concrete clean-tail oracle. -/
theorem postOracleVec_apply (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    postOracleVec A (fullIndex A left right tail) =
      if right.val < P.order then
        if left.val < P.order then
          if tail = A.tailEncoding.encode
              (A.cleanTail
                (P.toSourceScope.oracleMultiplier left.val right.val)) then
            invSqrtOrder P.order * invSqrtOrder P.order
          else 0
        else 0
      else 0 := by
  classical
  unfold postOracleVec
  change (∑ source : Fin
      (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)),
      A.oracleCircuit.matrix
          (fullIndex A left right tail) source * preparedVec A source) = _
  rw [← Equiv.sum_comp
    (prodEquiv
      (m := orderWidth P + orderWidth P)
      (n := A.tailEncoding.width)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  change (∑ sourceLeft : Fin (2 ^ orderWidth P),
      ∑ sourceRight : Fin (2 ^ orderWidth P),
      ∑ sourceTail : Fin (2 ^ A.tailEncoding.width),
        A.oracleCircuit.matrix (fullIndex A left right tail)
            (fullIndex A sourceLeft sourceRight sourceTail) *
          preparedVec A
            (fullIndex A sourceLeft sourceRight sourceTail)) = _
  simp_rw [preparedVec_apply]
  simp only [mul_ite, mul_zero, Fintype.sum_ite_eq']
  have hmatrix
      (sourceLeft sourceRight : Fin (2 ^ orderWidth P)) :
      A.oracleCircuit.matrix (fullIndex A left right tail)
          (fullIndex A sourceLeft sourceRight
            (A.tailEncoding.encode (A.cleanTail 1))) =
        if fullIndex A left right tail =
            fullIndex A sourceLeft sourceRight
              (A.tailEncoding.encode
                (A.cleanTail
                  (P.toSourceScope.oracleMultiplier
                    sourceLeft.val sourceRight.val))) then
          1
        else 0 :=
    oracle_matrix_entry_identity A
      (fullIndex A left right tail) sourceLeft sourceRight
  simp_rw [hmatrix]
  rw [Fintype.sum_eq_single left]
  · rw [Fintype.sum_eq_single right]
    · simp [fullIndex]
    · intro sourceRight hne
      simp [fullIndex, Ne.symm hne]
  · intro sourceLeft hne
    simp [fullIndex, Ne.symm hne]

/-- The first two concrete stages produce `postOracleVec`. -/
theorem oracle_apply_preparation (A : ConcreteCircuitAccess P) :
    A.oracleCircuit.applyVec
        (A.preparationCircuit.applyVec
          (NormalizedVector.ket
            (R := Qubits
              (orderWidth P + orderWidth P + A.tailEncoding.width))
            (fullIndex A 0 0
              (A.tailEncoding.encode (A.cleanTail 1))) :
            HilbertVector
              (Qubits
                (orderWidth P + orderWidth P + A.tailEncoding.width)))) =
      postOracleVec A := by
  rw [preparation_apply_input]
  rfl

/-- Final basis amplitude after the two inverse-QFT readouts. -/
def circuitAmplitude (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P))
    (tail : Fin (2 ^ A.tailEncoding.width)) : ℂ :=
  ∑ sourceLeft : Fin (2 ^ orderWidth P),
    ∑ sourceRight : Fin (2 ^ orderWidth P),
      star (invSqrtN (orderWidth P) *
        ω (orderWidth P) ^ (sourceLeft.val * left.val)) *
      star (invSqrtN (orderWidth P) *
        ω (orderWidth P) ^ (sourceRight.val * right.val)) *
      postOracleVec A (fullIndex A sourceLeft sourceRight tail)

/-- Every terminal basis amplitude is computed from the stored concrete
prepare-oracle-readout circuit. -/
theorem circuit_amplitude (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    evolvedState A (fullIndex A left right tail) =
      circuitAmplitude A left right tail := by
  change A.fullCircuit.applyVec
      (A.preparation.normalized :
        HilbertVector
          (Qubits
            (orderWidth P + orderWidth P + A.tailEncoding.width)))
      (fullIndex A left right tail) = _
  rw [show A.fullCircuit.applyVec
      (A.preparation.normalized :
        HilbertVector
          (Qubits
            (orderWidth P + orderWidth P + A.tailEncoding.width))) =
      A.readoutCircuit.applyVec (postOracleVec A) by
    rw [ConcreteCircuitAccess.fullCircuit, UnitaryCircuit.applyVec_seq,
      UnitaryCircuit.applyVec_seq]
    exact congrArg A.readoutCircuit.applyVec
      (oracle_apply_preparation A)]
  change HilbertOperator.applyVec
      (A.readoutCircuit.matrix :
        HilbertOperator
          (Qubits
            (orderWidth P + orderWidth P + A.tailEncoding.width)))
      (postOracleVec A) (fullIndex A left right tail) = _
  rw [HilbertOperator.applyVec_apply,
    ← Equiv.sum_comp
      (prodEquiv
        (m := orderWidth P + orderWidth P)
        (n := A.tailEncoding.width)),
    Fintype.sum_prod_type]
  simp_rw [← Equiv.sum_comp
    (prodEquiv (m := orderWidth P) (n := orderWidth P)),
    Fintype.sum_prod_type]
  simp only [ConcreteCircuitAccess.readoutCircuit,
    ConcreteCircuitAccess.extendWithTail,
    ConcreteCircuitAccess.exponentReadoutCircuit,
    ConcreteCircuitAccess.pairConsecutiveCircuit,
    UnitaryCircuit.tensorQubits_matrix, UnitaryCircuit.shiftPhysicalIdx_matrix,
    UnitaryOperator.tensor_apply, Equiv.symm_apply_apply,
    UnitaryCircuit.dagger_matrix, QFTCircuit_matrix, Matrix.conjTranspose_apply,
    QFTOperator_entry,
    QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.identityCircuit_entry]
  rw [circuitAmplitude]
  apply Finset.sum_congr rfl
  intro sourceLeft _
  apply Finset.sum_congr rfl
  intro sourceRight _
  rw [Finset.sum_eq_single tail]
  · simp [fullIndex, mul_assoc]
  · intro sourceTail _ hne
    simp [fullIndex, Ne.symm hne]
  · simp

/-! ## Concrete terminal outcomes and readout fibers -/

/-- Big-endian terminal outcome for one pair of Fourier-register labels. -/
def measurementOutcome (P : KnownOrderProblem G)
    (value : Fin (2 ^ (orderWidth P + orderWidth P))) :
    TerminalZMeasure.Outcome (orderWidth P + orderWidth P) :=
  QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.measurementOutcome P value

@[simp] theorem fullRegisterIndex_measurementOutcome
    (P : KnownOrderProblem G)
    (value : Fin (2 ^ (orderWidth P + orderWidth P))) :
    TerminalZMeasure.fullRegisterIndex (measurementOutcome P value) = value :=
  QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.fullRegisterIndex_measurementOutcome
    P value

theorem measurementOutcome_injective (P : KnownOrderProblem G) :
    Function.Injective (measurementOutcome P) :=
  QuantumAlg.FiniteCyclicDLP.Canonical.BornBridge.measurementOutcome_injective P

@[simp] theorem measurement_readout_fullIndex
    (A : ConcreteCircuitAccess P)
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P)))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    A.measurement.readout (prodEquiv (leftRight, tail)) =
      measurementOutcome P leftRight := by
  funext outputIndex
  change (prodEquiv (leftRight, tail)).val.testBit
      (orderWidth P + orderWidth P + A.tailEncoding.width - 1 -
        outputIndex.val) =
    leftRight.val.testBit
      (orderWidth P + orderWidth P - 1 - outputIndex.val)
  have hindex :
      orderWidth P + orderWidth P + A.tailEncoding.width - 1 -
          outputIndex.val =
        A.tailEncoding.width +
          (orderWidth P + orderWidth P - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left leftRight tail
    ⟨orderWidth P + orderWidth P - 1 - outputIndex.val, by omega⟩

theorem measurement_readout_eq_outcome_iff
    (A : ConcreteCircuitAccess P)
    (basis : Fin
      (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)))
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    A.measurement.readout basis = measurementOutcome P leftRight ↔
      (prodEquiv.symm basis).1 = leftRight := by
  have hself :
      A.measurement.readout basis =
        measurementOutcome P (prodEquiv.symm basis).1 := by
    simpa using measurement_readout_fullIndex A
      (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact measurementOutcome_injective P (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (measurementOutcome P) h)

/-- Embed the unmeasured raw implementation tail into one readout fiber. -/
def measurementFiberEmbedding (A : ConcreteCircuitAccess P)
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    Fin (2 ^ A.tailEncoding.width) ↪
      Fin (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)) where
  toFun := fun tail => prodEquiv (leftRight, tail)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] theorem measurementFiberEmbedding_apply
    (A : ConcreteCircuitAccess P)
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P)))
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    measurementFiberEmbedding A leftRight tail =
      prodEquiv (leftRight, tail) :=
  rfl

theorem measurement_fiber (A : ConcreteCircuitAccess P)
    (leftRight : Fin (2 ^ (orderWidth P + orderWidth P))) :
    Finset.univ.filter
        (fun basis : Fin
          (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width)) =>
          A.measurement.readout basis = measurementOutcome P leftRight) =
      Finset.univ.map (measurementFiberEmbedding A leftRight) := by
  ext basis
  rw [Finset.mem_filter, measurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [measurementFiberEmbedding_apply, ← hleft]
    exact Equiv.apply_symm_apply _ basis
  · intro hmem
    obtain ⟨tail, _, htail⟩ := Finset.mem_map.mp hmem
    change prodEquiv (leftRight, tail) = basis at htail
    rw [← htail, Equiv.symm_apply_apply]

/-! ## Born marginal of the concrete prepared attempt -/

/-- Computational-basis distribution of the metadata-free evolved state. -/
def basisPMF (A : ConcreteCircuitAccess P) :
    PMF (Fin
      (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width))) :=
  PMF.ofFintype
    (fun basis => ENNReal.ofReal (‖evolvedState A basis‖ ^ 2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      rw [← EuclideanSpace.norm_sq_eq, (evolvedState A).norm_eq_one]
      norm_num)

@[simp] theorem basisPMF_apply (A : ConcreteCircuitAccess P)
    (basis : Fin
      (2 ^ (orderWidth P + orderWidth P + A.tailEncoding.width))) :
    basisPMF A basis = ENNReal.ofReal (‖evolvedState A basis‖ ^ 2) :=
  rfl

/-- Terminal distribution obtained by reading the concrete evolved vector. -/
def outcomePMF (A : ConcreteCircuitAccess P) :
    PMF (TerminalZMeasure.Outcome (orderWidth P + orderWidth P)) :=
  PMF.map A.measurement.readout (basisPMF A)

@[simp] theorem outcomePMF_apply (A : ConcreteCircuitAccess P)
    (outcome : TerminalZMeasure.Outcome (orderWidth P + orderWidth P)) :
    outcomePMF A outcome =
      ∑ basis with A.measurement.readout basis = outcome,
        ENNReal.ofReal (‖evolvedState A basis‖ ^ 2) := by
  rw [outcomePMF, basisPMF, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply]
  refine Finset.sum_congr ?_ ?_
  · ext basis
    simp
  · intro basis _
    rfl

/-- The concrete terminal probability is the marginal over every raw
implementation-tail basis state of the same circuit amplitude. -/
theorem bornOutcomeProbability_eq_sourceMarginal
    (A : ConcreteCircuitAccess P)
    (left right : Fin (2 ^ orderWidth P)) :
    outcomePMF A
        (measurementOutcome P (prodEquiv (left, right))) =
      ∑ tail : Fin (2 ^ A.tailEncoding.width),
        ENNReal.ofReal (‖circuitAmplitude A left right tail‖ ^ 2) := by
  classical
  rw [outcomePMF_apply, measurement_fiber, Finset.sum_map]
  simp_rw [measurementFiberEmbedding_apply]
  change (∑ tail : Fin (2 ^ A.tailEncoding.width),
      ENNReal.ofReal
        (‖evolvedState A (fullIndex A left right tail)‖ ^ 2)) = _
  simp_rw [circuit_amplitude]

end FiniteCyclicDLP.Concrete.BornBridge

end

end QuantumAlg
