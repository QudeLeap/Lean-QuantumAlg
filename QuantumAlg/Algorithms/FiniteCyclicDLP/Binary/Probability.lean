/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Born
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Amplification
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Subgroup.Input
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Born
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Oracle
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.Probability
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Amplification.Model
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Binary.Subgroup.Input
import all QuantumAlg.Util.PMF

/-!
# Actual binary Born distribution and its source correspondence

The probability mass function is computed from the complete normalized output
of the implemented binary word. Its map through the actual exponent readout is
the proven finite-cyclic source law; no sample distribution is supplied as an
oracle or assumed by an endpoint [Sho95, source.tex:1784-1984].
-/

namespace QuantumAlg.FiniteCyclicDLP.Binary

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- Read the two exponent blocks of the real binary bank, leaving its group wires live. -/
public def readout (P : KnownOrderProblem G) (basis : (Oracle.layout P).Basis) :
    TerminalZMeasure.Outcome (OrderPreparation.width P + OrderPreparation.width P) :=
  OrderBornBridge.measurementOutcome P (prodEquiv (Oracle.basisEquiv P basis).1)

/-- Binary exponent decoding is exactly the value of each physical exponent wire. -/
public lemma binaryDLP_readout_apply (P : KnownOrderProblem G) (basis : (Oracle.layout P).Basis)
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P)) :
    readout P basis index = decide ((basis (Fin.castAdd (groupWidth P) index)).val = 1) := by
  rw [readout, OrderBornBridge.measurementOutcome_apply]
  let split := QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
    (Oracle.workspaceLayout P) (Oracle.binaryOracle_exponent_workspace_disjoint P) basis
  have packed : prodEquiv (OrderOracle.exponentBasisEquiv P split.1) =
      QuantumSignature.qubitsIndexEquiv
        (OrderPreparation.width P + OrderPreparation.width P) split.1 := by
    unfold OrderOracle.exponentBasisEquiv
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change decide (((BinaryBasis.bigEndianEquiv
    (OrderPreparation.width P + OrderPreparation.width P)).symm
      (prodEquiv (OrderOracle.exponentBasisEquiv P split.1)) index).val = 1) = _
  rw [packed]
  have decoded :
      (BinaryBasis.bigEndianEquiv (OrderPreparation.width P + OrderPreparation.width P)).symm
        (QuantumSignature.qubitsIndexEquiv
          (OrderPreparation.width P + OrderPreparation.width P) split.1) = split.1 :=
    (BinaryBasis.bigEndianEquiv
      (OrderPreparation.width P + OrderPreparation.width P)).symm_apply_apply split.1
  rw [decoded]
  rfl

/-- Encoding the group workspace never changes an exponent readout. -/
public lemma readout_source (P : KnownOrderProblem G)
    (basis : (OrderOracle.layout (subgroupProblem P)).Basis) :
    readout P (Oracle.sourceEmbedding P basis) =
      OrderBornBridge.readout (subgroupProblem P) basis := by
  have coordinates : Oracle.basisEquiv P (Oracle.sourceEmbedding P basis) =
      ((OrderOracle.basisEquiv (subgroupProblem P) basis).1,
        encodeGroup P (OrderOracle.basisEquiv (subgroupProblem P) basis).2) := by
    change Oracle.basisEquiv P ((Oracle.basisEquiv P).symm _) = _
    exact (Oracle.basisEquiv P).apply_symm_apply _
  rw [readout, coordinates]
  rfl

/-- Computational-basis law of the actual binary preparation-query-Fourier word. -/
@[expose] public def basisPMF (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    PMF (Oracle.layout P).Basis :=
  PMF.ofFintype
    (fun basis => ENNReal.ofReal (‖(Fourier.evolvedState P expansion).vec basis‖ ^ 2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      rw [← EuclideanSpace.norm_sq_eq, (Fourier.evolvedState P expansion).norm_eq_one]
      norm_num)

/-- The actual binary basis distribution is exactly the encoded original source distribution. -/
public lemma basisPMF_eq_map (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    basisPMF P expansion =
      (OrderBornBridge.basisPMF (subgroupProblem P) expansion).map
        (Oracle.sourceEmbedding P) := by
  classical
  apply PMF.ext
  intro basis
  rw [PMF.map_apply (Oracle.sourceEmbedding P)
    (OrderBornBridge.basisPMF (subgroupProblem P) expansion) basis, tsum_fintype]
  simp only [basisPMF, PMF.ofFintype_apply, evolvedState_extension]
  by_cases valid : basis ∈ Set.range (Oracle.sourceEmbedding P)
  · obtain ⟨source, rfl⟩ := valid
    rw [BasisEmbedding.vector_image]
    simp [(Oracle.sourceEmbedding P).injective.eq_iff]
    simpa using (OrderBornBridge.basisPMF_apply (subgroupProblem P) expansion source).symm
  · rw [BasisEmbedding.vector_unused (R := (Oracle.layout P).register)
      (S := (OrderOracle.layout (subgroupProblem P)).register) (Oracle.sourceEmbedding P)
      (OrderBornBridge.evolvedState (subgroupProblem P) expansion) basis valid]
    have different : ∀ source, basis ≠ Oracle.sourceEmbedding P source :=
      fun source same => valid ⟨source, same.symm⟩
    simp [different]

/-- The measured outcome law is derived from the actual binary output state. -/
public def outcomePMF (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    PMF (TerminalZMeasure.Outcome (OrderPreparation.width P + OrderPreparation.width P)) :=
  (basisPMF P expansion).map (readout P)

/-- The native binary sample has exactly the original subgroup Born law. -/
public lemma outcomePMF_eq_source (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) :
    outcomePMF P expansion = OrderBornBridge.outcomePMF (subgroupProblem P) expansion := by
  rw [outcomePMF, basisPMF_eq_map, PMF.map_comp]
  apply congrArg (fun observe =>
    (OrderBornBridge.basisPMF (subgroupProblem P) expansion).map observe)
  funext basis
  exact readout_source P basis

/-- Subgroup representation changes neither the full-family retry calibration nor its count. -/
public lemma sampleCount_subgroup (P : KnownOrderProblem G) :
    sampleCount (subgroupProblem P) = sampleCount P := rfl

/-- The useful Fourier event is numerical in the unchanged order and logarithm. -/
public lemma selectedOutcome_subgroup (P : KnownOrderProblem G) (secret : Input P)
    (outcome : TerminalZMeasure.Outcome
      (OrderPreparation.width P + OrderPreparation.width P)) :
    Probability.SelectedOutcome (subgroupProblem P) (subgroupInput secret) outcome ↔
      Probability.SelectedOutcome P secret outcome := Iff.rfl

/-- One actual binary sample has the full source floor used by its independent cycle protocol. -/
public lemma binary_selected_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : Input P) :
    ENNReal.ofReal (attemptFloor P) ≤
      (outcomePMF P expansion).toOuterMeasure
        {outcome | Probability.SelectedOutcome P secret outcome} := by
  rw [outcomePMF_eq_source]
  have floor : Probability.selectedOutcomeFamilyLowerBound (subgroupProblem P) =
      ENNReal.ofReal (attemptFloor P) :=
    Canonical.selectedRawOutcomeFamilyLowerBound_eq_ofReal_attemptFloor (subgroupProblem P)
  have events :
      {outcome : TerminalZMeasure.Outcome
          (OrderPreparation.width P + OrderPreparation.width P) |
        Probability.SelectedOutcome (subgroupProblem P) (subgroupInput secret) outcome} =
      {outcome | Probability.SelectedOutcome P secret outcome} := by
    ext outcome
    exact selectedOutcome_subgroup P secret outcome
  exact floor.symm.le.trans
    ((selected_probability (subgroupProblem P) expansion (subgroupInput secret)).trans_eq
      (congrArg (fun event : Set (TerminalZMeasure.Outcome
        (OrderPreparation.width P + OrderPreparation.width P)) =>
        (OrderBornBridge.outcomePMF (subgroupProblem P) expansion).toOuterMeasure event) events))

/-- The literal binary sample law admits the stronger complete-family amplification. -/
public lemma binary_selected_vector_probability (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (secret : Input P) :
    ENNReal.ofReal ((2 : Real) / 3) ≤
      (PMF.independentReplicateVector (outcomePMF P expansion)
        (sampleCount P)).toOuterMeasure
        {outcomes | ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
  rw [outcomePMF_eq_source]
  have source : ENNReal.ofReal ((2 : Real) / 3) ≤
      (PMF.independentReplicateVector (OrderBornBridge.outcomePMF (subgroupProblem P) expansion)
        (sampleCount P)).toOuterMeasure
        {outcomes : List.Vector (TerminalZMeasure.Outcome
            (OrderPreparation.width P + OrderPreparation.width P)) (sampleCount P) |
          ∃ index, Probability.SelectedOutcome (subgroupProblem P) (subgroupInput secret)
            (outcomes.get index)} :=
    binaryDLP_selected_vector_probability (subgroupProblem P) expansion (subgroupInput secret)
  have events :
      {outcomes : List.Vector (TerminalZMeasure.Outcome
          (OrderPreparation.width P + OrderPreparation.width P)) (sampleCount P) |
        ∃ index, Probability.SelectedOutcome (subgroupProblem P) (subgroupInput secret)
          (outcomes.get index)} =
      {outcomes | ∃ index, Probability.SelectedOutcome P secret (outcomes.get index)} := by
    ext outcomes
    exact exists_congr fun index => selectedOutcome_subgroup P secret (outcomes.get index)
  exact source.trans_eq (congrArg (fun event : Set (List.Vector (TerminalZMeasure.Outcome
    (OrderPreparation.width P + OrderPreparation.width P)) (sampleCount P)) =>
    (PMF.independentReplicateVector (OrderBornBridge.outcomePMF (subgroupProblem P) expansion)
      (sampleCount P)).toOuterMeasure event) events)

end

end QuantumAlg.FiniteCyclicDLP.Binary
