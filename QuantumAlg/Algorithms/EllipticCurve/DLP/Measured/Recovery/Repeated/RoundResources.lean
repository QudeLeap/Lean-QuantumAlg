/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Reset.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Sampling.Readout.Resources

/-!
# Actual reused ECDLP sampling-round resources

Every round first measures, corrects and seeds all existing quantum systems,
then executes original exponent preparation, four conversions, all original
point calls, inverse QFT and terminal Z measurements. Exact duration keeps
the selected reset and scalar paths. No new input or clean-state condition
is required by these actual-code resource theorems.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion ScalarMultiplication.MeasuredPlacement
open FiniteCyclicDLP ConcreteCircuitAccess GenericPointAddition.InPlace

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size) (fits : p < 2 ^ fieldTail.succ)
  (odd : Odd p) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)

/-- The complete reset branch allowance precedes all original sampling and readout events. -/
def samplingRoundBudget : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  samplingResetBudget E (orderWidth problem) +
    ((exponentPreparationCircuit problem).eventCost +
      (ResourcePool.scale 4 (MAU.Multiplication.Gidney.nativeBudget p.size) +
        ResourcePool.scale (2 * orderWidth problem) (MeasuredPointAddition.events p.size)) +
      (exponentReadoutCircuit problem).eventCost +
      (2 * orderWidth problem) • ResourcePool.singleton (Circuit.zEvent 2))

omit [Fact p.Prime] in
/-- Exact cardinality of the independent round allowance, keeping the actual
range-preparation and arithmetic pools instead of the former two-event shortcut. -/
theorem samplingRoundBudget_card :
    (samplingRoundBudget E problem).card =
      2 * (PublicInput.terminal E (orderWidth problem)).systemCount +
      (exponentPreparationCircuit problem).eventCost.card +
      4 * (MAU.Multiplication.Gidney.nativeBudget p.size).card +
      (2 * orderWidth problem) * (MeasuredPointAddition.events p.size).card +
      (exponentReadoutCircuit problem).eventCost.card +
      2 * orderWidth problem := by
  simp only [samplingRoundBudget, Multiset.card_add, ResourcePool.scale,
    Multiset.card_nsmul, samplingResetBudget_card, ResourcePool.singleton,
    Multiset.card_replicate]
  omega

omit [Fact p.Prime] in
/-- Project the actual complete-round allowance onto any one native event coordinate. -/
theorem samplingRoundBudget_count
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty)) :
    ResourcePool.count focus (samplingRoundBudget E problem) =
      ResourcePool.count focus (samplingResetBudget E (orderWidth problem)) +
      ResourcePool.count focus (exponentPreparationCircuit problem).eventCost +
      4 * ResourcePool.count focus (MAU.Multiplication.Gidney.nativeBudget p.size) +
      (2 * orderWidth problem) *
        ResourcePool.count focus (MeasuredPointAddition.events p.size) +
      ResourcePool.count focus (exponentReadoutCircuit problem).eventCost +
      (2 * orderWidth problem) * ResourcePool.count focus
        (ResourcePool.singleton (Circuit.zEvent 2)) := by
  simp only [samplingRoundBudget, ResourcePool.count_add, ResourcePool.count_scale,
    ResourcePool.count_nsmul]
  omega

omit [Fact p.Prime] in
/-- Terminal Z measurements contribute no single-qubit gates to the native round. -/
theorem samplingRoundBudget_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (samplingRoundBudget E problem) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (samplingResetBudget E (orderWidth problem)) +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (exponentPreparationCircuit problem).eventCost +
      4 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (MAU.Multiplication.Gidney.nativeBudget p.size) +
      (2 * orderWidth problem) *
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (MeasuredPointAddition.events p.size) +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (exponentReadoutCircuit problem).eventCost := by
  rw [samplingRoundBudget_count]
  simp [ResourcePool.count_singleton, Circuit.zEvent]

omit [Fact p.Prime] in
/-- Reset and terminal Z measurements contribute no CNOT gates to a native round. -/
theorem samplingRoundBudget_cnot_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (samplingRoundBudget E problem) =
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (exponentPreparationCircuit problem).eventCost +
      4 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (MAU.Multiplication.Gidney.nativeBudget p.size) +
      (2 * orderWidth problem) *
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
          (MeasuredPointAddition.events p.size) +
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (exponentReadoutCircuit problem).eventCost := by
  rw [samplingRoundBudget_count]
  simp [samplingResetBudget_cnot_count, ResourcePool.count_singleton, Circuit.zEvent]

omit [Fact p.Prime] in
/-- Only the multiplier and point-addition allowances contribute native Toffoli gates. -/
theorem samplingRoundBudget_toffoli_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (samplingRoundBudget E problem) =
      4 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
        (.gate .toffoli) (MAU.Multiplication.Gidney.nativeBudget p.size) +
      (2 * orderWidth problem) *
        ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
          (.gate .toffoli) (MeasuredPointAddition.events p.size) := by
  rw [samplingRoundBudget_count]
  simp [samplingResetBudget_toffoli_count,
    exponentPreparationCircuit_toffoli_count,
    exponentReadoutCircuit_toffoli_count, ResourcePool.count_singleton, Circuit.zEvent]

/-- Unit depth allows the actual measurement and optional native X on each reset wire. -/
def samplingRoundUnitDepth : Nat :=
  2 * (PublicInput.terminal E (orderWidth problem)).systemCount +
    ((exponentPreparationCircuit problem).evaluatedEventDepth (fun _ => 1) +
      (4 * MAU.Multiplication.Gidney.eventBound p.size +
        (2 * orderWidth problem) * MeasuredPointAddition.depthBound p.size) +
      (exponentReadoutCircuit problem).evaluatedEventDepth (fun _ => 1) +
      2 * orderWidth problem)

/-- Every native reset, original exponent/arithmetic gate and terminal readout is included. -/
theorem samplingRound_pool_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).resourcePool path ≤
      samplingRoundBudget E problem := by
  change ResourcePool.ofList (_ ++ _) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (samplingReset_pool_le E fieldTail (orderWidth problem) sameWidth fits seed path.1)
    (samplingReadout_budget E fieldTail odd problem points path.2)

/-- The same selected reset history and scalar execution path determine arbitrary duration. -/
theorem samplingRound_duration
    (duration : Resource.Event (.quantum AlgorithmGate.model .empty) → Nat)
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).depth duration path =
      (∑ wire, (QuditShift.resetWireToBasis wire
        (samplingResetImplementations E (orderWidth problem) wire)
        (samplingResetCells E (orderWidth problem) wire)
        (samplingResetLabel E (orderWidth problem) fieldTail sameWidth fits seed wire)).depth
          duration (Circuit.forRangeComponentPath
            (PublicInput.terminal E (orderWidth problem)).systemCount _ path.1 wire)) +
        ((exponentPreparationCircuit problem).evaluatedEventDepth duration +
          (Encoding.placedConvertedCascade E points (List.finRange (2 * orderWidth problem))
            (Semantics.radixUnit p fieldTail.succ odd)).depth duration
              (samplingReadoutOriginalPath E fieldTail odd problem points path.2).1.2 +
          (exponentReadoutCircuit problem).evaluatedEventDepth duration +
          (2 * orderWidth problem) * duration (Circuit.zEvent 2)) :=
  congrArg₂ Nat.add
    (samplingReset_duration E fieldTail (orderWidth problem) sameWidth fits seed duration path.1)
    (samplingReadout_duration E fieldTail odd problem points duration path.2)

/-- The original unit-depth allowance follows actual reset and sampling sequentially. -/
theorem samplingRound_unitDepth_le
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).depth (fun _ => 1) path ≤
      samplingRoundUnitDepth E problem :=
  Nat.add_le_add
    (samplingReset_unitDepth_le E fieldTail (orderWidth problem) sameWidth fits seed path.1)
    (samplingReadout_depth E fieldTail odd problem points path.2)

/-- Both stages reuse exactly the complete original terminal resident context. -/
theorem samplingRound_resident
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).peakResidentSpace path =
      (PublicInput.terminal E (orderWidth problem)).residentSpace :=
  (Circuit.peakResidentSpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (samplingReset_resident E fieldTail (orderWidth problem) sameWidth fits seed path.1)
      (samplingReadout_resident E fieldTail odd problem points path.2)).trans
        (SpacePool.max_self _))

/-- Every original auxiliary role and result cell remains counted in the reused context. -/
theorem samplingRound_auxiliary
    (path : (samplingRound E fieldTail sameWidth fits odd problem points seed).Path) :
    (samplingRound E fieldTail sameWidth fits odd problem points seed).peakAuxiliarySpace path =
      (PublicInput.terminal E (orderWidth problem)).auxiliarySpace :=
  (Circuit.peakAuxiliarySpace_seq _ _ path).trans
    ((congrArg₂ SpacePool.max
      (samplingReset_auxiliary E fieldTail (orderWidth problem) sameWidth fits seed path.1)
      (samplingReadout_auxiliary E fieldTail odd problem points path.2)).trans
        (SpacePool.max_self _))

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
