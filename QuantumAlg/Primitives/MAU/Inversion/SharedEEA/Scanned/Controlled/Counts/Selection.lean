/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Counts.Source
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Preparation
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Addition
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.PrefixAddition
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Address.Phase
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Scan.Resources
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Controlled.Selection
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Full
import all QuantumAlg.Components.GateModel.Algorithm.Adjoint.Resources.Empty
import all QuantumAlg.Core.Base.UnitaryCircuit.Accounting.QuantumTime

/-!
# Native resources of actual selected address preparation and Sign selection

The complete metadata address uses both full TTK additions and the
actual parallel copy. Every retained selector callback and every X mask
is charged, together with the full native preparation adjoint and both
externally selected enables.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPreparation

noncomputable section

open EncodedBit NumberTheory.SharedEEA

private lemma copy_counts (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (AddressCopy.program width).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (AddressCopy.program width).eventCost = ScanMetadata.addressWidth width ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (AddressCopy.program width).eventCost = 0 := by
  have pool : (AddressCopy.program width).eventCost =
      ResourcePool.ofList (List.replicate (ScanMetadata.addressWidth width)
        (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty))) :=
    (UnitaryCircuit.ofList_eventTrace_eq_eventCost _).symm.trans
      (congrArg ResourcePool.ofList (AddressCopy.program_eventTrace width))
  simp [pool, ResourcePool.count_ofList, List.count_replicate, beq_iff_eq]

private lemma addition_pool (width : Nat) :
    (AddressAddition.program width).eventCost =
      (Addition.TTK.lowRippleProgram (ScanMetadata.addressWidth width)).eventCost := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, AddressAddition.program_eventTrace,
    UnitaryCircuit.ofList_eventTrace_eq_eventCost, Addition.TTK.ttkParallelLowRipple_eventCost]

private lemma prefix_pool (width : Nat) :
    (PrefixAddition.program width).eventCost =
      (Addition.TTK.lowRippleProgram (ScanMetadata.addressWidth width)).eventCost :=
  (PrefixAddition.placement width).program_eventCost

private lemma phase_counts (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (AddressPhase.program width).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (AddressPhase.program width).eventCost = 1 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (AddressPhase.program width).eventCost = 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [AddressPhase.program, GateSpec.programList_toffoli_count_eq_sum]
    rfl
  · rw [AddressPhase.program, GateSpec.programList_cnot_count_eq_sum]
    rfl
  · rw [AddressPhase.program, GateSpec.programList_x_count_eq_sum]
    rfl

private lemma p256_ttk_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (Addition.TTK.lowRippleProgram (ScanMetadata.addressWidth 256)).eventCost = 0 := by
  simpa using Addition.TTK.ttkLowRipple_native_count (ScanMetadata.addressWidth 256)
    (.gate .singleQubit)

/-- All five actual address components retain their complete native multiplicities. -/
lemma p256_program_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program 256).eventCost = 36 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program 256).eventCost = 100 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program 256).eventCost = 4 := by
  simp only [program, UnitaryCircuit.seq_eventCost, ResourcePool.count_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [(copy_counts 256).1, addition_pool, prefix_pool,
      Addition.TTK.ttkLowRipple_toffoli_count, (phase_counts 256).1]
    decide
  · rw [(copy_counts 256).2.1, addition_pool, prefix_pool,
      Addition.TTK.ttkLowRipple_cnot_count, (phase_counts 256).2.1]
    decide
  · rw [(copy_counts 256).2.2, addition_pool, prefix_pool,
      p256_ttk_singleQubit_count, (phase_counts 256).2.2]

private lemma copy_quantumTime (width : Nat) :
    (AddressCopy.program width).evaluatedEventDepth Resource.Event.quantumDuration = 1 :=
  (UnitaryCircuit.unitaryCircuit_quantumDuration_eq_unit_depth
    (AddressCopy.program width) .empty .empty).trans (AddressCopy.program_unitDepth width)

private lemma phase_quantumTime (width : Nat) :
    (AddressPhase.program width).evaluatedEventDepth Resource.Event.quantumDuration = 3 := by
  rw [AddressPhase.program, GateSpec.programList_quantumTime]
  rfl

/-- The actual parallel copy and both native TTK schedules remain in the complete address bound. -/
lemma p256_program_quantumTime_le :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration ≤ 97 := by
  have addition := Addition.TTK.ttkParallelLowRipple_quantumTime_le
    (ScanMetadata.addressWidth 256) (by decide)
  have prefixSchedule := addition
  rw [← AddressAddition.program_evaluatedEventDepth] at addition
  rw [← (PrefixAddition.placement 256).program_evaluatedEventDepth] at prefixSchedule
  change (PrefixAddition.program 256).evaluatedEventDepth Resource.Event.quantumDuration ≤ _
    at prefixSchedule
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq,
    copy_quantumTime, phase_quantumTime]
  have numeric : 5 * ScanMetadata.addressWidth 256 - 5 = 45 := by decide
  rw [numeric] at addition prefixSchedule
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressPreparation

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

noncomputable section

open EncodedBit WindowLookup

private lemma callback_singleQubit_count (width : Nat)
    (label : Fin (2 ^ NumberTheory.SharedEEA.ScanMetadata.addressWidth width)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (callback width label).eventCost = 0 := by
  rw [← UnitaryCircuit.ofList_eventTrace_eq_eventCost, callback_trace]
  split <;> simp [ResourcePool.ofList_cons, ResourcePool.ofList_nil]

/-- All actual selector-fork masks remain charged; every retained Fredkin callback has zero X. -/
lemma p256_singleQubit_count :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256).eventCost = 532 := by
  rw [program, SelectorFrame.program_event_count]
  simp only [callback_singleQubit_count, SelectorTrie.leafSum,
    SelectorTrie.leafSumAt_const, Nat.mul_zero, Nat.add_zero]
  simp [selectorForkCount, p256_tree_counts.1]

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionScan

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionBody

noncomputable section

/-- Actual preparation, scan and full native adjoint retain all original resource occurrences. -/
lemma p256_program_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program 256).eventCost = 863 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program 256).eventCost = 984 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program 256).eventCost = 540 := by
  simp only [program, UnitaryCircuit.seq_eventCost,
    AlgorithmGate.algorithmGate_emptyAdjoints_eventCost, ResourcePool.count_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [AddressPreparation.p256_program_counts.1, SelectionScan.p256_toffoli_count]
  · rw [AddressPreparation.p256_program_counts.2.1, SelectionScan.p256_cnot_count]
  · rw [AddressPreparation.p256_program_counts.2.2, SelectionScan.p256_singleQubit_count]

/-- The complete actual prepare/scan/adjoint duration retains both parallel metadata schedules. -/
lemma p256_program_quantumTime_le :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration ≤ 2301 := by
  have preparation := AddressPreparation.p256_program_quantumTime_le
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq,
    AlgorithmGate.algorithmGate_emptyAdjoints_quantumTime, SelectionScan.p256_quantumTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelectionBody

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelection

noncomputable section

/-- Both selected enables and the complete actual Sign-selection body retain every native gate. -/
lemma p256_program_counts :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program 256).eventCost = 867 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program 256).eventCost = 984 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program 256).eventCost = 540 := by
  simp only [program, UnitaryCircuit.seq_eventCost, ControlledFrame.liftProgram_eventCost,
    ResourcePool.count_add]
  refine ⟨?_, ?_, ?_⟩
  · rw [ControlledSelectionEnable.program_toffoli_count,
      ControlledSelectionBody.p256_program_counts.1]
  · rw [(ControlledSelectionEnable.program_other_counts 256).1,
      ControlledSelectionBody.p256_program_counts.2.1]
  · rw [(ControlledSelectionEnable.program_other_counts 256).2,
      ControlledSelectionBody.p256_program_counts.2.2]

/-- The actual selected Sign word retains both enable durations and the full paid body schedule. -/
lemma p256_program_quantumTime_le :
    (program 256).evaluatedEventDepth Resource.Event.quantumDuration ≤ 2305 := by
  have body := ControlledSelectionBody.p256_program_quantumTime_le
  simp only [program, UnitaryCircuit.evaluatedEventDepth_seq,
    ControlledFrame.liftProgram_quantumTime, ControlledSelectionEnable.program_quantumTime]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ControlledSelection
