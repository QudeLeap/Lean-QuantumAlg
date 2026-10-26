/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Program
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback
import all QuantumAlg.Primitives.QFT.Semiclassical.Construction
import all QuantumAlg.Components.QuditShift.Qubit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting
import all QuantumAlg.Core.Execution.Circuit.Weighted
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Actual retained-feedback and reset resources of a Fourier window

Every selected earlier result pays its native phase. Each measured head pays
its Hadamard, its actual selected tail word and its physical identity/X reset.
The duration bound is an upper bound on the actual dependency expression.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window

noncomputable section

open Execution

local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

attribute [local implicit_reducible] Feedback.one Feedback.selected feedbackAt priorFeedback
  afterHead stage readout inverseCode

variable {ctx : RuntimeCtx .quantum} {totalBits active : Nat}
    {operations : ClassicalOpModel} {services : ClassicalOracleModel}

/-- Literal number of potentially selected earlier-result phase instructions. -/
def priorPhaseCount (ports : Ports ctx totalBits active)
    (previous : List (BitPosition totalBits)) : Nat := by
  classical
  exact (previous.map fun position => if ports.past position then 1 else 0).sum

private lemma earlierPositions_sum (count start : Nat) (within : start ≤ count) :
    ((List.finRange count).map fun position => if position.val < start then 1 else 0).sum =
      start := by
  induction count generalizing start with
  | zero =>
      have empty : start = 0 := by omega
      subst start
      rfl
  | succ count ih =>
      cases start with
      | zero => simp
      | succ start =>
          simp only [List.finRange_succ, List.map_cons, List.sum_cons, List.map_map,
            Function.comp_def, Fin.val_zero, Nat.zero_lt_succ, ↓reduceIte, Fin.val_succ,
            Nat.succ_lt_succ_iff]
          rw [ih start (by omega)]
          omega

/-- Exactly the original start positions of one stream can contribute earlier-window phases. -/
lemma priorPhaseCount_complete (ports : Ports ctx totalBits active) :
    priorPhaseCount ports (previousPositions totalBits) = ports.start := by
  have within : ports.start ≤ totalBits := by have bounded := ports.within; omega
  have streamSum (stream : Fin 2) :
      ((List.finRange totalBits).map fun position =>
        if ports.past (stream, position) then 1 else 0).sum =
          if stream = ports.stream then ports.start else 0 := by
    by_cases selected : stream = ports.stream
    · simp only [Ports.past, selected, true_and]
      exact earlierPositions_sum totalBits ports.start within
    · simp only [Ports.past, selected, false_and, ↓reduceIte, List.map_const',
        List.length_finRange, List.sum_replicate, smul_zero]
  have streams : ports.stream = 0 ∨ ports.stream = 1 := by
    by_cases zero : ports.stream = 0
    · exact Or.inl zero
    · right
      apply Fin.ext
      have positive : ports.stream.val ≠ 0 := fun same => zero (Fin.ext same)
      have bounded := ports.stream.isLt
      change ports.stream.val = 1
      omega
  simp only [priorPhaseCount, previousPositions, List.finRange_succ, List.finRange_zero,
    List.map_cons, List.map_nil, List.flatMap_cons, List.flatMap_nil, List.append_nil,
    List.map_append, List.map_map, Function.comp_def, List.sum_append]
  change ((List.finRange totalBits).map fun position =>
      if ports.past (0, position) then 1 else 0).sum +
    ((List.finRange totalBits).map fun position =>
      if ports.past (1, position) then 1 else 0).sum = _
  rw [streamSum 0, streamSum 1]
  rcases streams with first | second
  · simp [first]
  · simp [second]

private lemma phasePrefix_pool (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    (count : Nat) (bounded : count ≤ n) :
    (phasePrefix inverse wires qubits count bounded).eventCost operations services =
      count • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phasePrefix]
      change (phasePrefix inverse wires qubits count (Nat.le_of_succ_le bounded)).eventCost
        operations services + ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate .singleQubit) = _
      rw [ih]
      rw [succ_nsmul]

private lemma selectedPhase_pool_le (inverse : Bool) {n : Nat}
    (wires : Fin n ↪ Fin ctx.systemCount)
    (qubits : ∀ index, (ctx.quantumLayout.wire (wires index)).dimension = 2)
    {dimension : ℕ+} (value : CShape.Value (.finite dimension)) :
    (selectedPhase inverse wires qubits value).eventCost operations services ≤
      n • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  cases value with
  | finite bit =>
      change (if bit.val = 1 then phaseLayer inverse wires qubits
        else UnitaryCircuit.identity AlgorithmGate.model .empty ctx.quantumLayout).eventCost
          operations services ≤ _
      split_ifs
      · exact (phasePrefix_pool (operations := operations) (services := services)
          inverse wires qubits n le_rfl).le
      · exact zero_le

private lemma shift_pool_le (wire : Fin ctx.systemCount)
    (qubit : (ctx.quantumLayout.wire wire).dimension = 2)
    (amount : Fin (ctx.quantumLayout.wire wire).dimension) :
    (QuditShift.qubitShiftCircuit ctx.quantumLayout wire qubit .empty amount).eventCost
        operations services ≤
      ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
    QuditShift.qubitShiftCircuit_events ctx.quantumLayout wire qubit .empty amount
      operations services]
  split_ifs
  · exact zero_le
  · exact le_rfl

lemma feedbackOne_pool_le (ports : Ports ctx totalBits active)
    (previous : BitPosition totalBits) (current : Fin active) :
    ∀ path : (Feedback.one (operations := operations) (services := services)
      ports previous current).Path,
    (Feedback.one (operations := operations) (services := services)
      ports previous current).resourcePool path ≤
      (if ports.past previous then 1 else 0) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  classical
  by_cases prior : ports.past previous
  · rw [Feedback.one_of_past ports previous current prior, if_pos prior]
    intro path
    change ResourcePool.ofList
      ((Feedback.phaseProgram ports previous current path.1).eventTrace operations services) ≤ _
    rw [Feedback.phaseProgram_eventTrace]
    split_ifs
    · simp only [one_nsmul]; exact le_rfl
    · exact zero_le
  · have skipped : Feedback.one (operations := operations) (services := services)
        ports previous current = Circuit.id
          (model := .quantum AlgorithmGate.model .empty operations services)
          (allowAllocation := false) ctx := by
      rw [Feedback.one, if_neg prior]
    rw [skipped, if_neg prior]
    intro path
    exact le_rfl

lemma feedbackAt_pool_le (ports : Ports ctx totalBits active) (current : Fin active)
    (previous : List (BitPosition totalBits))
    (path : (feedbackAt (operations := operations) (services := services)
      ports current previous).Path) :
    (feedbackAt (operations := operations) (services := services)
      ports current previous).resourcePool path ≤
      priorPhaseCount ports previous • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  induction previous with
  | nil => exact le_rfl
  | cons previous rest ih =>
      have head := feedbackOne_pool_le (operations := operations) (services := services)
        ports previous current path.1
      have tail := ih path.2
      change (Feedback.one (operations := operations) (services := services)
        ports previous current).resourcePool path.1 +
          (feedbackAt (operations := operations) (services := services)
            ports current rest).resourcePool path.2 ≤ _
      refine (add_le_add head tail).trans_eq ?_
      simp only [priorPhaseCount, List.map_cons, List.sum_cons, add_nsmul]

lemma priorFeedback_pool_le (ports : Ports ctx totalBits active)
    (currents : List (Fin active))
    (path : (priorFeedback (operations := operations) (services := services)
      ports currents).Path) :
    (priorFeedback (operations := operations) (services := services)
      ports currents).resourcePool path ≤
      (currents.length * priorPhaseCount ports (previousPositions totalBits)) •
        ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate .singleQubit) := by
  induction currents with
  | nil =>
      simp only [List.length_nil, Nat.zero_mul, zero_nsmul]
      exact zero_le
  | cons current rest ih =>
      have head := feedbackAt_pool_le (operations := operations) (services := services)
        ports current (previousPositions totalBits) path.1
      have tail := ih path.2
      change (feedbackAt (operations := operations) (services := services)
        ports current (previousPositions totalBits)).resourcePool path.1 +
          (priorFeedback (operations := operations) (services := services)
            ports rest).resourcePool path.2 ≤ _
      refine (add_le_add head tail).trans_eq ?_
      simp only [List.length_cons, Nat.add_mul, one_mul, add_nsmul]
      ac_rfl

lemma afterHead_pool_le (ports : Ports ctx totalBits (active + 1))
    (value : CShape.Value (.finite (ctx.quantumLayout.wire (ports.wires 0)).dimension)) :
    (afterHead ports value).eventCost operations services ≤
      (active + 1) • ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.gate .singleQubit) := by
  have tail := selectedPhase_pool_le (operations := operations) (services := services)
    true ports.tail.wires ports.tail.qubits value
  have reset := shift_pool_le (operations := operations) (services := services)
    (ports.wires 0) (ports.qubits 0) (-value.toFin)
  change (selectedPhase true ports.tail.wires ports.tail.qubits value).eventCost
    operations services +
      (QuditShift.qubitShiftCircuit ctx.quantumLayout (ports.wires 0) (ports.qubits 0)
        .empty (-value.toFin)).eventCost operations services ≤ _
  refine (add_le_add tail reset).trans_eq ?_
  rw [succ_nsmul]

lemma stage_pool_le (ports : Ports ctx totalBits (active + 1))
    (path : (stage (operations := operations) (services := services) ports).Path) :
    (stage (operations := operations) (services := services) ports).resourcePool path ≤
      (active + 2) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate .singleQubit) +
        ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.measurement (2 : ℕ+)) := by
  have correction := afterHead_pool_le (operations := operations) (services := services)
    ports path.2.2.1
  have measured : ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (ctx.quantumLayout.wire (ports.wires 0)).dimension) =
        ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.measurement (2 : ℕ+)) := by rw [ports.qubits 0]
  change ResourcePool.ofList
      ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp (ports.wires 0)
        (ports.qubits 0)).eventTrace operations services) +
    (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (ctx.quantumLayout.wire (ports.wires 0)).dimension) +
      ResourcePool.ofList ((afterHead ports path.2.2.1).eventTrace operations services)) ≤ _
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services, measured]
  change ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty operations services) (.gate .singleQubit) +
    (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+)) +
        (afterHead ports path.2.2.1).eventCost operations services) ≤ _
  refine (add_le_add (le_refl (ResourcePool.singleton
    (model := .quantum AlgorithmGate.model .empty operations services) (.gate .singleQubit)))
    (add_le_add (le_refl (ResourcePool.singleton
      (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (2 : ℕ+)))) correction)).trans_eq ?_
  simp only [show active + 2 = (active + 1) + 1 from rfl, succ_nsmul]
  ac_rfl

lemma readout_pool_le : ∀ (count : Nat) (ports : Ports ctx totalBits count)
    (path : (readout (operations := operations) (services := services) count ports).Path),
    (readout (operations := operations) (services := services) count ports).resourcePool path ≤
      (count.choose 2 + 2 * count) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate .singleQubit) +
        count • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.measurement (2 : ℕ+)) := by
  intro count
  induction count with
  | zero => intro ports path; exact le_rfl
  | succ count ih =>
      intro ports path
      have head := stage_pool_le (operations := operations) (services := services) ports path.1
      have tail := ih ports.tail path.2
      change (stage (operations := operations) (services := services) ports).resourcePool path.1 +
        (readout (operations := operations) (services := services) count ports.tail).resourcePool
          path.2 ≤ _
      refine (add_le_add head tail).trans_eq ?_
      rw [show (count + 1).choose 2 = count + count.choose 2 by
        simpa using Nat.choose_succ_succ count 1]
      rw [show count + count.choose 2 + 2 * (count + 1) =
        (count + 2) + (count.choose 2 + 2 * count) by omega]
      simp only [add_nsmul, succ_nsmul]
      ac_rfl

/-- Independent allowance follows the actual earlier-result tests and every reset branch. -/
lemma inverseCode_pool_le (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (inverseCode (operations := operations) (services := services) ports).resourcePool path ≤
      (active * priorPhaseCount ports (previousPositions totalBits) +
        active.choose 2 + 2 * active) • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.gate .singleQubit) +
        active • ResourcePool.singleton
          (model := .quantum AlgorithmGate.model .empty operations services)
          (.measurement (2 : ℕ+)) := by
  have prior := priorFeedback_pool_le (operations := operations) (services := services)
    ports (List.finRange active) path.1
  have current := readout_pool_le (operations := operations) (services := services)
    active ports path.2
  change (priorFeedback (operations := operations) (services := services)
      ports (List.finRange active)).resourcePool path.1 +
    (readout (operations := operations) (services := services) active ports).resourcePool path.2 ≤ _
  refine (add_le_add prior current).trans_eq ?_
  simp only [List.length_finRange, add_nsmul]
  ac_rfl

lemma inverseCode_quantumTime_le (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (inverseCode (operations := operations) (services := services) ports).depth
      Resource.Event.quantumDuration path ≤
      active * priorPhaseCount ports (previousPositions totalBits) +
        active.choose 2 + 2 * active := by
  refine (Circuit.depth_le_weightedCount_of_pool_le _ Resource.Event.quantumDuration _ path
    (inverseCode_pool_le (operations := operations) (services := services) ports path)).trans_eq ?_
  simp [ResourcePool.weightedCount_add, ResourcePool.weightedCount_nsmul,
    ResourcePool.weightedCount_singleton, Resource.Event.quantumDuration]

/-- Closed independent window allowance: each prior bit, each internal pair, and H/X per head. -/
lemma inverseCode_quantumTime_start_le (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    (inverseCode (operations := operations) (services := services) ports).depth
      Resource.Event.quantumDuration path ≤
        active * ports.start + active.choose 2 + 2 * active := by
  have actual := inverseCode_quantumTime_le ports path
  rw [priorPhaseCount_complete] at actual
  exact actual

private lemma stage_measurement_count (ports : Ports ctx totalBits (active + 1))
    (path : (stage (operations := operations) (services := services) ports).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (2 : ℕ+))
      ((stage (operations := operations) (services := services) ports).resourcePool path) = 1 := by
  have measured : ResourcePool.count
      (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+))
      (ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.measurement (ctx.quantumLayout.wire (ports.wires 0)).dimension)) = 1 := by
    rw [ports.qubits 0]
    simp only [ResourcePool.count_singleton, ↓reduceIte]
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+))
      (ResourcePool.ofList ((Gate.singleQubitAt ctx.quantumLayout .empty Gate.HOp
        (ports.wires 0) (ports.qubits 0)).eventTrace operations services) +
      (ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.measurement (ctx.quantumLayout.wire (ports.wires 0)).dimension) +
        ResourcePool.ofList ((afterHead ports path.2.2.1).eventTrace operations services))) = 1
  rw [ResourcePool.count_add, ResourcePool.count_add]
  rw [UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost _ operations services,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context,
    UnitaryCircuit.unitaryCircuit_event_count_classical_context]
  change 0 + (ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+))
      (ResourcePool.singleton
        (model := .quantum AlgorithmGate.model .empty operations services)
        (.measurement (ctx.quantumLayout.wire (ports.wires 0)).dimension)) + 0) = 1
  simpa only [Nat.zero_add, Nat.add_zero] using measured

private lemma readout_measurement_count : ∀ (count : Nat) (ports : Ports ctx totalBits count)
    (path : (readout (operations := operations) (services := services) count ports).Path),
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (2 : ℕ+))
      ((readout (operations := operations) (services := services) count ports).resourcePool path) =
        count := by
  intro count
  induction count with
  | zero => intro ports path; rfl
  | succ count ih =>
      intro ports path
      change ResourcePool.count
        (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+))
        ((stage (operations := operations) (services := services) ports).resourcePool path.1 +
          (readout (operations := operations) (services := services) count
            ports.tail).resourcePool path.2) = count + 1
      rw [ResourcePool.count_add]
      rw [stage_measurement_count, ih]
      omega

/-- The actual adaptive inverse measures each active physical system exactly once. -/
lemma inverseCode_measurement_count (ports : Ports ctx totalBits active)
    (path : (inverseCode (operations := operations) (services := services) ports).Path) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty operations services)
      (.measurement (2 : ℕ+))
      ((inverseCode (operations := operations) (services := services) ports).resourcePool path) =
        active := by
  have prior := priorFeedback_pool_le (operations := operations) (services := services)
    ports (List.finRange active) path.1
  have counts := ResourcePool.le_iff_count.mp prior
  have noPrior := counts (.measurement (2 : ℕ+))
  simp only [ResourcePool.count_nsmul, ResourcePool.count_singleton, reduceCtorEq,
    ↓reduceIte, Nat.mul_zero] at noPrior
  change ResourcePool.count
    (model := .quantum AlgorithmGate.model .empty operations services) (.measurement (2 : ℕ+))
      ((priorFeedback (operations := operations) (services := services)
        ports (List.finRange active)).resourcePool path.1 +
        (readout (operations := operations) (services := services) active ports).resourcePool
          path.2) = active
  rw [ResourcePool.count_add]
  rw [Nat.eq_zero_of_le_zero noPrior, readout_measurement_count, Nat.zero_add]

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window
