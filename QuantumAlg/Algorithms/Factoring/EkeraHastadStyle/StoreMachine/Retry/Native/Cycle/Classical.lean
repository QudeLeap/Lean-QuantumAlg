/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Core.Execution.CycleSchedule
import all QuantumAlg.Core.Execution.Trace.Composition
import all QuantumAlg.Core.Execution.Circuit.Restoration
import all QuantumAlg.Core.Algorithm.Borrowed
import all QuantumAlg.Core.Execution.Retained.Distribution
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Resources
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Retry.Native.Selection.Correctness

/-!
# The actual empty suffix and final classical selection protocols

The empty retry suffix performs the real identity operation. The final selector
returns exactly the first populated value in its original chronological inputs.
Its independent native envelope contains only classical operations. Both are
complete standalone classical sections, with the ordinary borrowed-restoration
and resource obligations retained.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles

noncomputable section

open Execution ShortDLP.CompiledMAU
open ClassicalRoutines.FirstAccepted.Direct

local instance {α : Type} : DecidableEq α := Classical.decEq α

namespace Idle

variable (ctx : RuntimeCtx .quantum)

/-- An empty classical continuation returns unit and uses no native event. -/
def problem : Problem RuntimeRound.model ctx ctx .unit where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ _ => True
  successLB := ⟨1, le_rfl⟩
  states := []
  resources := { events := 0, resident := ctx.residentSpace, auxiliary := ctx.auxiliarySpace }
  depth :=
    { duration := fun _ => 1
      limit := 0
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- The actual terminal identity keeps the full live context. -/
def algorithm : Algorithm RuntimeRound.model ctx ctx .unit :=
  ⟨{ code := Circuit.id (model := RuntimeRound.model) ctx
     output := Output.all ctx .unit }⟩

/-- The terminal identity has no quantum or classical event. -/
theorem onlyClassical : Circuit.IsClassical (Circuit.id (model := RuntimeRound.model) ctx) := by
  intro path event present
  exact False.elim (List.not_mem_nil present)

/-- The real empty suffix meets its independent empty-continuation specification. -/
theorem solves : Algorithm.Solves (algorithm ctx) (problem ctx) := by
  constructor
  · intro Reference input _valid _initialized
    apply le_of_eq
    symm
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => True.intro)
  · intro Reference input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact Circuit.borrowedRestored_id (model := RuntimeRound.model) state
  · intro _Reference _input _valid _initialized path _supported
    exact le_rfl
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (Circuit.peakResidentSpace_id path)
  · intro _Reference _input _valid _initialized path _supported
    exact le_of_eq (Circuit.peakAuxiliarySpace_id path)
  · intro _Reference _input _valid _initialized path _supported
    exact le_rfl

/-- The empty suffix is a certified standalone classical leaf. -/
def schedule : Circuit.CycleSchedule (.classical (problem ctx))
    (Circuit.id (model := RuntimeRound.model) ctx) :=
  .classical _ { output := (algorithm ctx).run.output, certified := solves ctx }
    (onlyClassical ctx)

end Idle

namespace Selection

variable {source : RuntimeCtx .quantum} {N length : Nat}
  (inputs : Fin length → CInputRef source (LatticeBatchRecoveryOutput.OutputShape N))

/-- The classical protocol selects precisely the first actual chronological populated value. -/
def problem : Problem RuntimeRound.model source (NativeRetrySelection.context source N)
    (LatticeBatchRecoveryOutput.OutputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun before output => output =
    NativeRetrySelection.firstValue (before.read (.fixedVector inputs))
  successLB := ⟨1, le_rfl⟩
  states := []
  resources :=
    { events := NativeRetrySelection.selectionEnvelope N length
      resident := source.residentSpace + NativeRetrySelection.tailAdditionalSpace N
      auxiliary := source.auxiliarySpace + NativeRetrySelection.tailAdditionalSpace N }
  depth :=
    { duration := fun _ => 1
      limit := 3 * length + 1
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

/-- The real selector tail reads its own retained output cell. -/
def algorithm : Algorithm RuntimeRound.model source (NativeRetrySelection.context source N)
    (LatticeBatchRecoveryOutput.OutputShape N) :=
  ⟨{ code := NativeRetrySelection.tail inputs
     output := Output.all (NativeRetrySelection.context source N)
       (.read (.storage (NativeRetrySelection.resultRef source N).toCStorageRef)) }⟩

private theorem relational {Reference : Register}
    (input : OracleInput RuntimeRound.model.classicalOracles source Reference) :
    (algorithm inputs).relationalDistribution input =
      (input.state.toPMF input.normalized).map (fun entry =>
        (entry.1, NativeRetrySelection.firstValue (entry.1.read (.fixedVector inputs)))) := by
  have mapped := AlgorithmRun.relationalDistribution_retained_eq_map
    (model := RuntimeRound.model) source (NativeRetrySelection.resultKey source)
    (LatticeBatchRecoveryOutput.OutputShape N) source.canonicalFreshKey_fresh
    (NativeRetrySelection.body inputs) (algorithm inputs).run.output
    (NativeRetrySelection.bodyStep inputs) (NativeRetrySelection.body_execute inputs) input
  refine mapped.trans ?_
  apply congrArg ((input.state.toPMF input.normalized).map)
  funext entry
  exact congrArg (Prod.mk entry.1) (NativeRetrySelection.tail_output inputs entry.1 entry.2)

private theorem envelope_classical (event : Resource.Event RuntimeRound.model)
    (present : event ∈ NativeRetrySelection.selectionEnvelope N length) :
    (∃ coordinate, event = .classicalOperation coordinate) ∨
      (∃ coordinate, event = .classicalQuery coordinate) := by
  cases event with
  | classicalOperation coordinate => exact Or.inl ⟨coordinate, rfl⟩
  | classicalQuery coordinate => exact Or.inr ⟨coordinate, rfl⟩
  | gate coordinate =>
      simp [NativeRetrySelection.selectionEnvelope, Optional.Allocation.eventEnvelope,
        Optional.eventEnvelope, copyTrace, ResourcePool.scale,
        ResourcePool.singleton, ResourcePool.ofList] at present
  | oracle coordinate =>
      simp [NativeRetrySelection.selectionEnvelope, Optional.Allocation.eventEnvelope,
        Optional.eventEnvelope, copyTrace, ResourcePool.scale,
        ResourcePool.singleton, ResourcePool.ofList] at present
  | preparation dimension =>
      simp [NativeRetrySelection.selectionEnvelope, Optional.Allocation.eventEnvelope,
        Optional.eventEnvelope, copyTrace, ResourcePool.scale,
        ResourcePool.singleton, ResourcePool.ofList] at present
  | measurement dimension =>
      simp [NativeRetrySelection.selectionEnvelope, Optional.Allocation.eventEnvelope,
        Optional.eventEnvelope, copyTrace, ResourcePool.scale,
        ResourcePool.singleton, ResourcePool.ofList] at present

/-- The exact actual selection trace contains only native classical operations. -/
theorem onlyClassical : Circuit.IsClassical (NativeRetrySelection.tail inputs) := by
  intro path event present
  apply envelope_classical event
  apply Multiset.mem_of_le (NativeRetrySelection.tail_pool_le inputs path)
  exact present

/-- Real chronological selection completes its own deterministic result protocol. -/
theorem solves : Algorithm.Solves (algorithm inputs) (problem inputs) := by
  constructor
  · intro Reference input _valid _initialized
    change 1 ≤ ((algorithm inputs).relationalDistribution input).toOuterMeasure _
    rw [relational, PMF.toOuterMeasure_map_apply]
    apply le_of_eq
    symm
    exact (PMF.toOuterMeasure_apply_eq_one_iff _ _).mpr (fun _ _ => rfl)
  · intro Reference input _valid _initialized requirement present
    exact False.elim (List.not_mem_nil present)
  · intro Reference input _valid _initialized
    apply AlgorithmRun.restoresBorrowed_of_circuit
    intro reference history _ state
    exact NativeRetrySelection.tail_borrowedRestored inputs reference state
  · intro _Reference _input _valid _initialized path _supported
    exact NativeRetrySelection.tail_pool_le inputs path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeRetrySelection.tail_resident_le inputs path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeRetrySelection.tail_auxiliary_le inputs path
  · intro _Reference _input _valid _initialized path _supported
    exact NativeRetrySelection.tail_depth_le inputs path

/-- The final selector is a certified classical leaf on the original actual circuit. -/
def schedule : Circuit.CycleSchedule (.classical (problem inputs))
    (NativeRetrySelection.tail inputs) :=
  .classical _ { output := (algorithm inputs).run.output, certified := solves inputs }
    (onlyClassical inputs)

end Selection

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.NativeCycles
