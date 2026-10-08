/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Scalar.Spec
import all QuantumAlg.Algorithms.EllipticCurve.Resources.Space
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Coordinates
import all QuantumAlg.Components.GateModel.Algorithm.Resources

/-! # Scalar observations of actual arbitrary-width ECC quantum-round allowances -/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP ConcreteCircuitAccess
open PrimeFieldShortWeierstrass.ECDLP.Measured ScalarMultiplication.MeasuredPlacement

variable {p : Nat} (E : PrimeFieldShortWeierstrass p)
  (known : KnownOrderProblem E.GroupPoint)

/-- The actual original terminal layout has the symbolic qubit cardinality. -/
theorem terminal_systemCount_scalar :
    (PublicInput.terminal E (orderWidth known)).systemCount =
      Scalar.qubits p.size (orderWidth known) := by
  have allQubits := samplingReset_qubits E (orderWidth known)
  have systems : (PublicInput.terminal E (orderWidth known)).systemCount =
      (PublicInput.terminal E (orderWidth known)).residentSpace (.quantumSystems 2) := by
    rw [RuntimeCtx.residentSpace_quantumSystems]
    simp [QuantumLayout.dimensionCount, QuantumLayout.dimensions, allQubits,
      List.ofFn_const]
  rw [systems, terminal_residentSpace]
  simp [Scalar.qubits, readySpace, SpacePool.ofShape, OwnedQubits.space]

/-- The literal fixed load and every original zero preparation have a width-only ceiling. -/
theorem initializationTrace_length_scalar (modulus count : Nat) :
    (Allocation.initializationTrace modulus count).length ≤
      Scalar.initializationEvents modulus.size := by
  have load := congrArg Multiset.card
    ((UnitaryCircuit.ofList_eventTrace_eq_eventCost
      (MeasuredUncompute.InPlacePreparation.loadProgram modulus)).trans
        (load_pool modulus))
  simp only [ResourcePool.ofList, Multiset.coe_card, Multiset.card_nsmul,
    ResourcePool.singleton, Multiset.card_replicate, Nat.mul_one] at load
  have bounded := EncodedBit.Word.BasisLoad.basisLoad_count_le
    (MeasuredUncompute.InPlacePreparation.loadConstant modulus)
  rw [Allocation.initializationTrace, List.length_append, List.length_append,
    ZeroPreparation.zeroPreparation_event_count, ZeroPreparation.zeroPreparation_event_count,
    load]
  change MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth modulus.size + _ + 1 ≤ _
  change _ ≤ MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth modulus.size at bounded
  simpa only [Scalar.initializationEvents, Scalar.loadBits,
    MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth,
    MAU.Inversion.SharedEEA.InputPreparation.prefixWidth,
    MAU.Inversion.SharedEEA.InputPreparation.suffixWidth] using
    (show MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth modulus.size +
      EncodedBit.Word.BasisLoad.xCount
        (MeasuredUncompute.InPlacePreparation.loadConstant modulus) + 1 ≤
        2 * (modulus.size + 4 * modulus.size.size + 11) + 1 by
      unfold MAU.Inversion.SharedEEA.InputPreparation.auxiliaryWidth
        MAU.Inversion.SharedEEA.InputPreparation.prefixWidth
        MAU.Inversion.SharedEEA.InputPreparation.suffixWidth at bounded ⊢
      omega)

/-- Real reset, preparation, arithmetic and inverse-QFT gates share one scalar ceiling. -/
theorem samplingRound_singleQubit_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (samplingRoundBudget E known) ≤
      Scalar.roundSingle p.size (orderWidth known) := by
  have prep := (exponentPreparationCircuit_widthBounds known).1
  rw [samplingRoundBudget_singleQubit_count, samplingResetBudget_singleQubit_count,
    terminal_systemCount_scalar,
    MAU.Multiplication.Gidney.nativeBudget_singleQubit_count_symbolic,
    MeasuredPointAddition.events_singleQubit_count,
    exponentReadoutCircuit_event_count]
  simp only [↓reduceIte, mul_one, Resource.Event.gate.injEq, reduceCtorEq,
    mul_zero, add_zero, ge_iff_le]
  unfold Scalar.roundSingle Scalar.multiplierSingle Scalar.pointSingle Scalar.readoutSingle
  omega

/-- The complete actual CNOT allowance consumes the generic preparation theorem. -/
theorem samplingRound_cnot_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (samplingRoundBudget E known) ≤
      Scalar.roundCnot p.size (orderWidth known) := by
  have prep := (exponentPreparationCircuit_widthBounds known).2.1
  rw [samplingRoundBudget_cnot_count,
    MAU.Multiplication.Gidney.nativeBudget_cnot_count_symbolic,
    MeasuredPointAddition.events_cnot_count, exponentReadoutCircuit_event_count]
  simp only [Resource.Event.gate.injEq, reduceCtorEq, ↓reduceIte,
    mul_zero, mul_one, zero_add, ge_iff_le]
  unfold Scalar.roundCnot Scalar.multiplierCnot Scalar.multiplierSingle Scalar.pointCnot
    Scalar.readoutCnot
  omega

/-- Toffoli accounting remains exact at every symbolic field and sample width. -/
theorem samplingRound_toffoli_scalar :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (samplingRoundBudget E known) =
      Scalar.roundToffoli p.size (orderWidth known) := by
  rw [samplingRoundBudget_toffoli_count,
    MAU.Multiplication.Gidney.nativeBudget_toffoli_count_symbolic,
    MeasuredPointAddition.events_toffoli_count]
  rfl

/-- The actual two-register preparation has a width-only total native-event allowance. -/
theorem exponentPreparation_events_scalar :
    (exponentPreparationCircuit known).eventCost.card ≤ 28 * orderWidth known := by
  rcases exponentPreparationCircuit_widthBounds known with ⟨single, cnot, _depth⟩
  rw [AlgorithmGate.algorithmGate_unitaryEventCost_card,
    exponentPreparationCircuit_toffoli_count]
  omega

/-- The same generated inverse QFT words have their exact scalar event cardinality. -/
theorem exponentReadout_events_scalar :
    (exponentReadoutCircuit known).eventCost.card =
      Scalar.readoutSingle (orderWidth known) + Scalar.readoutCnot (orderWidth known) := by
  rw [AlgorithmGate.algorithmGate_unitaryEventCost_card,
    exponentReadoutCircuit_toffoli_count,
    exponentReadoutCircuit_event_count, exponentReadoutCircuit_event_count]
  simp [Scalar.readoutSingle, Scalar.readoutCnot]

/-- Total cardinality of the three-coordinate independent multiplier allowance. -/
theorem multiplierBudget_events_scalar (width : Nat) :
    (MAU.Multiplication.Gidney.nativeBudget width).card = Scalar.multiplierEvents width := by
  simp [MAU.Multiplication.Gidney.nativeBudget,
    MAU.Multiplication.Gidney.wordSwapBudget,
    MAU.Multiplication.Accumulate.Gidney.nativeBudget,
    MAU.Multiplication.Accumulate.Gidney.nativeAlphabet,
    EncodedBit.GateSpec.primitiveAlphabet, Scalar.multiplierEvents, Scalar.multiplierSingle,
    ResourcePool.ofList]
  ring

/-- The full original round pool is reduced to parameter arithmetic before specialization. -/
theorem samplingRound_events_scalar :
    (samplingRoundBudget E known).card ≤ Scalar.roundEvents p.size (orderWidth known) := by
  have prep := exponentPreparation_events_scalar E known
  rw [samplingRoundBudget_card, terminal_systemCount_scalar,
    multiplierBudget_events_scalar, MeasuredPointAddition.measuredPointAddition_budget_card,
    exponentReadout_events_scalar]
  change _ ≤ Scalar.roundEvents p.size (orderWidth known)
  unfold Scalar.roundEvents Scalar.pointEvents
  omega

end

end QuantumAlg.EllipticCurve.LogicalResources
