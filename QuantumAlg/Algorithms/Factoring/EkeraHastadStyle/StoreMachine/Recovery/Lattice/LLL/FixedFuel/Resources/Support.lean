/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.LLL.FixedFuel.Resources
import all QuantumAlg.Components.Classical.NumberTheory.SignedWord.Support

/-!
# Independent native coordinate budgets for fixed-fuel LLL

Support is proved once for each structural instruction formula. Iteration
selects one such formula at each index without enumerating complete paths.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine

open Execution ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private theorem swap_supported (width : Nat) :
    NativeTraceSupported width (LatticeSwap.pointSwapTrace (kind := kind) width) := by
  intro event present
  have same := (List.mem_replicate.mp present).2
  subst event
  simp [nativeAlphabet, ResourcePool.ofList]

private theorem selectedSwap_supported (width : Nat) (passes : Bool) :
    NativeTraceSupported width
      (if passes then [] else LatticeSwap.pointSwapTrace (kind := kind) width) := by
  cases passes
  · exact swap_supported width
  · simp [NativeTraceSupported]

private theorem comparison_supported (width : Nat) :
    NativeTraceSupported width
      (ClassicalRoutines.Comparison.Doubled.comparisonTrace (kind := kind) width) := by
  simp [ClassicalRoutines.Comparison.Doubled.comparisonTrace, NativeTraceSupported,
    nativeAlphabet, ResourcePool.ofList]

private theorem gram_supported (width : Nat) :
    NativeTraceSupported width (LatticeMetricMachine.gramTrace (kind := kind) width) := by
  apply nativeTraceSupported_replicate
  simp [NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

private theorem firstPair_supported (width : Nat)
    (magnitude correction restore passes : Bool) :
    NativeTraceSupported width
      (LatticeFirstPairMachine.firstPairTrace (kind := kind) width magnitude correction
        restore passes) := by
  simp only [LatticeFirstPairMachine.firstPairTrace, nativeTraceSupported_append, and_assoc]
  refine ⟨roundedDivBodyTrace_nativeSupported width magnitude correction restore, ?_,
    comparison_supported width, selectedSwap_supported width passes⟩
  simp [LatticeFirstPairMachine.reductionTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private theorem dot_supported (width : Nat) :
    NativeTraceSupported width (LatticeSecondPairMachine.dotTrace (kind := kind) width) := by
  simp [LatticeSecondPairMachine.dotTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private theorem reduction_supported (width : Nat) :
    NativeTraceSupported width
      (LatticeSecondPairMachine.reductionTrace (kind := kind) width) := by
  simp [LatticeSecondPairMachine.reductionTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private theorem secondPrefix_supported (width : Nat) (magnitude correction restore : Bool) :
    NativeTraceSupported width
      (LatticeSecondPairMachine.secondPairPrefixTrace (kind := kind) width magnitude correction
        restore) := by
  simp only [LatticeSecondPairMachine.secondPairPrefixTrace, nativeTraceSupported_append,
    and_assoc]
  refine ⟨dot_supported width, dot_supported width, ?_,
    roundedDivBodyTrace_nativeSupported width magnitude correction restore,
    reduction_supported width⟩
  simp [LatticeSecondReductionInputs.secondReductionInputsTrace, ProductDifference.operationTrace,
    NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

private theorem postReduction_supported (width : Nat) (magnitude correction restore : Bool) :
    NativeTraceSupported width
      (LatticeSecondPairPostReduction.postReductionTrace (kind := kind) width magnitude
        correction restore) := by
  simp only [LatticeSecondPairPostReduction.postReductionTrace, nativeTraceSupported_append]
  exact ⟨dot_supported width,
    roundedDivBodyTrace_nativeSupported width magnitude correction restore,
    reduction_supported width⟩

private theorem area_supported (width : Nat) :
    NativeTraceSupported width (LatticeAreaRefresh.phaseTrace (kind := kind) width) := by
  simp [LatticeAreaRefresh.phaseTrace, NativeTraceSupported, nativeAlphabet, ResourcePool.ofList]

private theorem secondPair_supported (width : Nat)
    (magnitude32 correction32 restore32 magnitude31 correction31 restore31 passes : Bool) :
    NativeTraceSupported width
      (LatticeSecondPairFullMachine.secondPairTrace (kind := kind) width magnitude32 correction32
        restore32 magnitude31 correction31 restore31 passes) := by
  simp only [LatticeSecondPairFullMachine.secondPairTrace, LatticeSecondLovaszBranch.branchTrace,
    nativeTraceSupported_append, and_assoc]
  exact ⟨secondPrefix_supported width magnitude32 correction32 restore32,
    postReduction_supported width magnitude31 correction31 restore31,
    area_supported width, area_supported width, comparison_supported width,
    selectedSwap_supported width passes⟩

private theorem firstAdvance_supported (width : Nat) (advance : Bool) :
    NativeTraceSupported width (firstAdvanceTrace (kind := kind) advance) := by
  cases advance <;> simp [firstAdvanceTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

private theorem secondAdvance_supported (width : Nat) (finish : Bool) :
    NativeTraceSupported width (secondAdvanceTrace (kind := kind) finish) := by
  cases finish <;> simp [secondAdvanceTrace, NativeTraceSupported, nativeAlphabet,
    ResourcePool.ofList]

/-- Every selected LLL step formula belongs to one independent finite native alphabet. -/
theorem stepTrace_nativeSupported (width : Nat) (decisions : StepDecisions) :
    NativeTraceSupported width (stepTrace (kind := kind) width decisions) := by
  cases decisions with
  | done => simp [stepTrace, NativeTraceSupported]
  | first magnitude correction restore passes advance =>
      simp only [stepTrace, nativeTraceSupported_append]
      exact ⟨firstPair_supported width magnitude correction restore passes,
        firstAdvance_supported width advance, gram_supported width⟩
  | second magnitude32 correction32 restore32 magnitude31 correction31 restore31 passes finish =>
      simp only [stepTrace, nativeTraceSupported_append]
      exact ⟨secondPair_supported width magnitude32 correction32 restore32 magnitude31 correction31
        restore31 passes, secondAdvance_supported width finish, gram_supported width⟩

/-- Chronological iteration preserves the per-step alphabet for every sequence of decisions. -/
theorem fixedFuelTrace_nativeSupported (fuel width : Nat)
    (decisions : Fin fuel → StepDecisions) :
    NativeTraceSupported width (fixedFuelTrace (kind := kind) fuel width decisions) := by
  intro event present
  obtain ⟨trace, member, present⟩ := List.mem_flatten.mp present
  obtain ⟨index, rfl⟩ := List.mem_ofFn.mp member
  exact stepTrace_nativeSupported width (decisions index) event present

/-- Independent coordinatewise allowance for the prescribed number of native LLL steps. -/
def fixedFuelEventEnvelope (fuel width : Nat) : ResourcePool kind :=
  (130 * fuel) • nativeAlphabet width

/-- Every actual fixed-fuel LLL path satisfies the independent native coordinate allowance. -/
theorem fixedFuelInto_pool_le (fuel : Nat) (refs : Refs ctx width)
    (path : (fixedFuelInto fuel refs).Path) :
    (fixedFuelInto fuel refs).resourcePool path ≤ fixedFuelEventEnvelope fuel width := by
  apply ResourcePool.le_scaled_of_support_card_le
  · intro event present
    rw [fixedFuelInto_resourcePool] at present
    exact fixedFuelTrace_nativeSupported fuel width
      (fun index => stepDecisions refs (path index)) event present
  · exact fixedFuelInto_eventCount_le fuel refs path

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeFixedFuelMachine
