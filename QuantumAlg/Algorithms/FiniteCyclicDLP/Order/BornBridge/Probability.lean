/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Order.BornBridge.State
public import QuantumAlg.Core.Measure
public import QuantumAlg.Core.Measure.Distribution
public import QuantumAlg.Util.FinPow.BinaryBasis
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Core.Base.State.Normalized
import all QuantumAlg.Util.FinPow.BinaryBasis
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome

/-!
# Born distribution of the native-dimensional known-order experiment

The terminal observation reads the two binary exponent registers and marginalizes
the retained finite-group system.  The probability is derived from the normalized
state of the same circuit used for execution and resource accounting.
-/

namespace QuantumAlg.FiniteCyclicDLP.OrderBornBridge

noncomputable section

open scoped BigOperators

universe u

variable {G : Type u} [Group G] [Fintype G]

/-- Big-endian terminal outcome for one packed pair of Fourier labels. -/
public def measurementOutcome (P : KnownOrderProblem G)
    (value : Fin (2 ^ (OrderPreparation.width P + OrderPreparation.width P))) :
    TerminalZMeasure.Outcome
      (OrderPreparation.width P + OrderPreparation.width P) :=
  fun outputIndex => value.val.testBit
    (OrderPreparation.width P + OrderPreparation.width P - 1 - outputIndex.val)

omit [Fintype G] in
/-- The named big-endian outcome exposes the corresponding decoded binary
coordinate. -/
public theorem measurementOutcome_apply (P : KnownOrderProblem G)
    (value : Fin (2 ^ (OrderPreparation.width P + OrderPreparation.width P)))
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P)) :
    measurementOutcome P value index =
      decide (((BinaryBasis.bigEndianEquiv
        (OrderPreparation.width P + OrderPreparation.width P)).symm value index).val = 1) := by
  unfold measurementOutcome
  rw [BinaryBasis.bigEndianEquiv_symm_value]
  rw [show OrderPreparation.width P + OrderPreparation.width P - 1 - index.val =
      index.rev.val by
    rw [Fin.val_rev]
    omega]
  generalize value.val.testBit index.rev.val = bit
  cases bit <;> rfl

omit [Fintype G] in
@[simp] public theorem fullRegisterIndex_measurementOutcome
    (P : KnownOrderProblem G)
    (value : Fin (2 ^ (OrderPreparation.width P + OrderPreparation.width P))) :
    TerminalZMeasure.fullRegisterIndex (measurementOutcome P value) = value := by
  apply Fin.val_injective
  change Nat.ofBits ((measurementOutcome P value) ∘ Fin.rev) = value.val
  have bits :
      (measurementOutcome P value) ∘ Fin.rev =
        fun bit : Fin (OrderPreparation.width P + OrderPreparation.width P) =>
          value.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, measurementOutcome]
    apply congrArg value.val.testBit
    calc
      OrderPreparation.width P + OrderPreparation.width P - 1 - (Fin.rev bit).val =
          OrderPreparation.width P + OrderPreparation.width P - ((Fin.rev bit).val + 1) := by
        omega
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [bits, Nat.ofBits_testBit, Nat.mod_eq_of_lt value.isLt]

omit [Fintype G] in
public theorem measurementOutcome_injective (P : KnownOrderProblem G) :
    Function.Injective (measurementOutcome P) := by
  intro left right equality
  have same := congrArg TerminalZMeasure.fullRegisterIndex equality
  simpa using same

omit [Fintype G] in
/-- The runtime readout uses the source layer's original big-endian encoding. -/
public theorem measurementOutcome_eq_source (P : KnownOrderProblem G)
    (value : Fin (2 ^ (OrderPreparation.width P + OrderPreparation.width P))) :
    measurementOutcome P value =
      Canonical.BornBridge.measurementOutcome P value := by
  funext index
  rfl

/-- The actual terminal readout discards only the native group coordinate. -/
public def readout (P : KnownOrderProblem G) (basis : (OrderOracle.layout P).Basis) :
    TerminalZMeasure.Outcome
      (OrderPreparation.width P + OrderPreparation.width P) :=
  measurementOutcome P
    (prodEquiv (OrderOracle.basisEquiv P basis).1)

/-- The semantic readout is exactly the actual value on each exponent wire. -/
public theorem readout_apply (P : KnownOrderProblem G)
    (basis : (OrderOracle.layout P).Basis)
    (index : Fin (OrderPreparation.width P + OrderPreparation.width P)) :
    readout P basis index =
      decide ((basis (Fin.castAdd 1 index)).val = 1) := by
  rw [readout, measurementOutcome_apply]
  let split := QuantumLayout.appendBasisEquiv (OrderOracle.exponentLayout P)
    (OrderOracle.workspaceLayout P) (OrderOracle.exponent_workspace_disjoint P) basis
  have packed :
      prodEquiv (OrderOracle.exponentBasisEquiv P split.1) =
        QuantumSignature.qubitsIndexEquiv
          (OrderPreparation.width P + OrderPreparation.width P) split.1 := by
    unfold OrderOracle.exponentBasisEquiv
    rw [Equiv.trans_apply, Equiv.apply_symm_apply]
  change decide (((BinaryBasis.bigEndianEquiv
    (OrderPreparation.width P + OrderPreparation.width P)).symm
      (prodEquiv (OrderOracle.exponentBasisEquiv P split.1)) index).val = 1) = _
  rw [packed]
  have decoded :
      (BinaryBasis.bigEndianEquiv
        (OrderPreparation.width P + OrderPreparation.width P)).symm
          (QuantumSignature.qubitsIndexEquiv
            (OrderPreparation.width P + OrderPreparation.width P) split.1) = split.1 := by
    exact (BinaryBasis.bigEndianEquiv
      (OrderPreparation.width P + OrderPreparation.width P)).symm_apply_apply split.1
  rw [decoded]
  rfl

@[simp] public theorem readout_fullBasis (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    readout P (fullBasis P left right tail) =
      measurementOutcome P (prodEquiv (left, right)) := by
  simp [readout]

/-- The finite group coordinate embeds injectively into one terminal readout fibre. -/
@[expose] public def measurementFiberEmbedding (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) :
    G ↪ (OrderOracle.layout P).Basis where
  toFun := fullBasis P left right
  inj' := by
    intro first second same
    have semantic := congrArg (OrderOracle.basisEquiv P) same
    simpa using congrArg Prod.snd semantic

@[simp] public theorem measurementFiberEmbedding_apply (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) (tail : G) :
    measurementFiberEmbedding P left right tail = fullBasis P left right tail :=
  rfl

/-- A readout fibre contains every group label and no other basis state. -/
public theorem measurement_fiber (P : KnownOrderProblem G)
    (left right : Fin (2 ^ OrderPreparation.width P)) :
    Finset.univ.filter
        (fun basis : (OrderOracle.layout P).Basis =>
          readout P basis = measurementOutcome P (prodEquiv (left, right))) =
      Finset.univ.map (measurementFiberEmbedding P left right) := by
  ext basis
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro observed
    have packed := measurementOutcome_injective P observed
    have exponent : (OrderOracle.basisEquiv P basis).1 = (left, right) := by
      exact prodEquiv.injective packed
    apply Finset.mem_map.mpr
    refine ⟨(OrderOracle.basisEquiv P basis).2, Finset.mem_univ _, ?_⟩
    apply (OrderOracle.basisEquiv P).injective
    rw [measurementFiberEmbedding_apply, basisEquiv_fullBasis]
    exact Prod.ext exponent.symm rfl
  · intro present
    obtain ⟨tail, _, rfl⟩ := Finset.mem_map.mp present
    exact readout_fullBasis P left right tail

/-- Computational-basis distribution of the normalized circuit output. -/
@[expose] public def basisPMF (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
  PMF (OrderOracle.layout P).Basis :=
  PMF.ofFintype
    (fun basis => ENNReal.ofReal (‖(evolvedState P expansion).vec basis‖ ^ 2))
    (by
      rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
      rw [← EuclideanSpace.norm_sq_eq, (evolvedState P expansion).norm_eq_one]
      norm_num)

@[simp] public theorem basisPMF_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order) (basis : (OrderOracle.layout P).Basis) :
    basisPMF P expansion basis =
      ENNReal.ofReal (‖(evolvedState P expansion).vec basis‖ ^ 2) :=
  rfl

/-- Distribution of the two retained exponent-register outcomes. -/
public def outcomePMF (P : KnownOrderProblem G) (expansion : OrderExpansion P.order) :
    PMF (TerminalZMeasure.Outcome
      (OrderPreparation.width P + OrderPreparation.width P)) :=
  PMF.map (readout P) (basisPMF P expansion)

@[simp] public theorem outcomePMF_apply (P : KnownOrderProblem G)
    (expansion : OrderExpansion P.order)
    (outcome : TerminalZMeasure.Outcome
      (OrderPreparation.width P + OrderPreparation.width P)) :
    outcomePMF P expansion outcome =
      ∑ basis with readout P basis = outcome,
        ENNReal.ofReal (‖(evolvedState P expansion).vec basis‖ ^ 2) := by
  rw [outcomePMF, basisPMF, PMF.map_ofFintype]
  simp only [PMF.ofFintype_apply]
  refine Finset.sum_congr ?_ ?_
  · ext basis
    simp
  · intro basis _
    rfl

/-- Terminal probability is the exact marginal over the native group system. -/
public theorem bornOutcomeProbability_eq_groupMarginal
    (P : KnownOrderProblem G) (expansion : OrderExpansion P.order)
    (left right : Fin (2 ^ OrderPreparation.width P)) :
    outcomePMF P expansion (measurementOutcome P (prodEquiv (left, right))) =
      ∑ tail : G,
        ENNReal.ofReal (‖circuitAmplitude P expansion left right tail‖ ^ 2) := by
  classical
  rw [outcomePMF_apply, measurement_fiber, Finset.sum_map]
  simp_rw [measurementFiberEmbedding_apply]
  simp_rw [circuit_amplitude]

end

end QuantumAlg.FiniteCyclicDLP.OrderBornBridge
