/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Reusable.Program
import all QuantumAlg.Core.Execution.Classical.Composition.Range

/-!
# Fixed unordered-pair recovery fold

The sixteen terminal results determine `choose 16 2` pair invocations.  This
module folds an indexed family of literal reusable pair machines while keeping
their persistent entry data and all not-yet-consumed terminal bits live.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticePairRecoveryFold

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Exact number of unordered pairs in the fixed sixteen-sample batch. -/
@[implicit_reducible] def PairCount : Nat := Nat.choose 16 2

/-- Width of the persistent factor selector shared by every pair. -/
abbrev FactorWidth (N : Nat) : Nat :=
  QuadraticCandidateCheck.CandidateWidth (LatticePairCandidateRecovery.Width N)

/-- An indexed family of pair machines sharing one persistent factor selector. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Nested references for the pair stage. -/
  pair : Fin PairCount → LatticePairFactorRecovery.Refs ctx N
  /-- Nested references for the factor selection stage. -/
  factorSelection : FirstAccepted.Refs ctx (FactorWidth N)
  sharedFactorSelection : ∀ index,
    QuadraticRecoveryGuarded.factorSelection (pair index).quadratic = factorSelection

/-- Persistent inputs of a target pair avoid every write of a current pair. -/
structure InitialFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (current target : LatticePairFactorRecovery.Refs ctx N) : Prop where
  setupParameter : LatticePairReusableRecovery.CallerFrameAvoids current
    target.pair.setup.parameter
  setupBase : LatticePairReusableRecovery.CallerFrameAvoids current
    (LatticeCandidateModularSetup.parameterBaseInput target.pair.setup)
  quadraticModulus : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.candidates.quadraticPrefix.modulus
  firstOne : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.first.check.one
  firstModulus : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.first.check.positiveCheck.modulus
  firstZero : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.first.check.positiveCheck.zero
  secondOne : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.second.check.one
  secondModulus : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.second.check.positiveCheck.modulus
  secondZero : LatticePairReusableRecovery.CallerFrameAvoids current
    target.quadratic.quadratic.recovery.pair.second.check.positiveCheck.zero

/-- Terminal projections of a target pair avoid every write of a current pair. -/
structure SourceFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (current target : LatticePairFactorRecovery.Refs ctx N) : Prop where
  firstBits : ∀ index, LatticePairReusableRecovery.CallerFrameAvoids current
    (.bitsGet (LatticePairReusableRecovery.firstTerminal target) index)
  secondBits : ∀ index, LatticePairReusableRecovery.CallerFrameAvoids current
    (.bitsGet (LatticePairReusableRecovery.secondTerminal target) index)

/-- Per-pair local certificates and complete cross-pair frame conditions. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  each : ∀ index, LatticePairReusableRecovery.Separation (refs.pair index)
  initialFrames : ∀ current target,
    InitialFrameAvoids (refs.pair current) (refs.pair target)
  sourceFrames : ∀ current target,
    SourceFrameAvoids (refs.pair current) (refs.pair target)

/-- One arbitrary caller read avoids every pair invocation. -/
def CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) {shape : CShape} (other : CInputRef ctx shape) : Prop :=
  ∀ index, LatticePairReusableRecovery.CallerFrameAvoids (refs.pair index) other

/-- All indexed machines have their persistent entry facts. -/
def InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (input : Input N) (generator : (ZMod N)ˣ)
    (before : Store ctx) (refs : Refs ctx N) : Prop :=
  ∀ index, LatticePairReusableRecovery.InitialConditions
    input generator before (refs.pair index)

/-- Pure factor option recovered by one indexed pair. -/
def pairValue {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (before : Store ctx) (index : Fin PairCount) : Option Nat :=
  RSA.recoverFactorFromShortLogPair (shortLogBits N) (tradeoffBits N) generator
    (LatticePairNearestPlaneSavedTarget.sourceSamples
      (refs.pair index).pair.pair before)

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {N : Nat}

/-- Execute every indexed pair in canonical finite order, including after the first success. -/
def into (input : Input N) (refs : Refs ctx N) : Circuit model ctx ctx :=
  Circuit.forRange PairCount fun index =>
    LatticePairReusableRecovery.into input (refs.pair index)

/-- The mathematical sequence record follows the complete store through every actual pair. -/
noncomputable def step (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.forRangeStoreRecord PairCount
    (fun index => LatticePairReusableRecovery.into input (refs.pair index))
    (fun index => LatticePairReusableRecovery.step input (refs.pair index)) store

/-- All actual pair updates occur in increasing finite-index order. -/
theorem step_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (step input refs store).1 =
      (List.ofFn (fun index => fun current =>
        (LatticePairReusableRecovery.step input (refs.pair index) current).1)).foldl
          (fun current update => update current) store :=
  Circuit.forRangeStoreRecord_store _ _ _ store

/-- The indexed record is the complete actual execution, including all histories and references. -/
theorem into_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      let actual := step input refs entry.1
      (actual.1, (entry.2.1, (entry.2.2, actual.2)))) :=
  Circuit.execute_forRangeStoreRecord _ _ _
    (fun index => LatticePairReusableRecovery.into_execute input (refs.pair index)) Reference state

private theorem initialConditions_transport (input : Input N) (generator : (ZMod N)ˣ)
    (current target : LatticePairFactorRecovery.Refs ctx N) (store : Store ctx)
    (targetInitial : LatticePairReusableRecovery.InitialConditions input generator store target)
    (avoids : InitialFrameAvoids current target) :
    LatticePairReusableRecovery.InitialConditions input generator
      (LatticePairReusableRecovery.step input current store).1 target := by
  have parameterFrame := LatticePairReusableRecovery.into_callerFrame input current store
    target.pair.setup.parameter avoids.setupParameter
  have setup := LatticePairCandidateRecovery.setupInitial_transport input target.pair.setup
    store _ targetInitial.setup parameterFrame
  have generatorAtEntry : generator = parameterUnit
      ((LatticePairReusableRecovery.step input current store).1.read
        target.pair.setup.parameter) := by
    rw [parameterFrame]
    exact targetInitial.generatorAtEntry
  have firstOne := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.firstOne
  have firstModulus := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.firstModulus
  have firstZero := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.firstZero
  have secondOne := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.secondOne
  have secondModulus := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.secondModulus
  have secondZero := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.secondZero
  have modulus := LatticePairReusableRecovery.into_callerFrame input current store
    _ avoids.quadraticModulus
  refine ⟨setup, generatorAtEntry, ?_, ?_⟩
  · unfold QuadraticCandidatePairSelect.InitialConditions
      QuadraticCandidateCheck.TotalInitialConditions
    rw [firstOne, firstModulus, firstZero, secondOne, secondModulus, secondZero]
    exact targetInitial.quadratic.pair
  · exact (congrArg CShape.Value.toNat modulus).trans targetInitial.quadratic.modulusValue

private theorem sourceSamples_frame (input : Input N)
    (current target : LatticePairFactorRecovery.Refs ctx N) (store : Store ctx)
    (avoids : SourceFrameAvoids current target) :
    LatticePairNearestPlaneSavedTarget.sourceSamples target.pair.pair
        (LatticePairReusableRecovery.step input current store).1 =
      LatticePairNearestPlaneSavedTarget.sourceSamples target.pair.pair store := by
  have firstBits : BatchMachine.sourceBits N
      (LatticePairReusableRecovery.step input current store).1
      (LatticePairReusableRecovery.firstTerminal target) =
    BatchMachine.sourceBits N store (LatticePairReusableRecovery.firstTerminal target) := by
    funext index
    unfold BatchMachine.sourceBits
    exact congrArg CShape.Value.toBool
      (LatticePairReusableRecovery.into_callerFrame input current store _ (avoids.firstBits index))
  have secondBits : BatchMachine.sourceBits N
      (LatticePairReusableRecovery.step input current store).1
      (LatticePairReusableRecovery.secondTerminal target) =
    BatchMachine.sourceBits N store (LatticePairReusableRecovery.secondTerminal target) := by
    funext index
    unfold BatchMachine.sourceBits
    exact congrArg CShape.Value.toBool
      (LatticePairReusableRecovery.into_callerFrame input current store _ (avoids.secondBits index))
  change (BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N (LatticePairReusableRecovery.step input current store).1
        (LatticePairReusableRecovery.firstTerminal target)),
    BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N (LatticePairReusableRecovery.step input current store).1
        (LatticePairReusableRecovery.secondTerminal target))) =
    (BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N store (LatticePairReusableRecovery.firstTerminal target)),
    BatchRecovery.decodeTerminalSample (shortLogBits N) (tradeoffBits N)
      (BatchMachine.sourceBits N store (LatticePairReusableRecovery.secondTerminal target)))
  rw [firstBits, secondBits]

/-- Persistent initial facts and all original source pairs survive every prefix. -/
private def Invariant (input : Input N) (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (source current : Store ctx) : Prop :=
  InitialConditions input generator current refs ∧
    ∀ index, LatticePairNearestPlaneSavedTarget.sourceSamples (refs.pair index).pair.pair current =
      LatticePairNearestPlaneSavedTarget.sourceSamples (refs.pair index).pair.pair source

private theorem slot_correct (input : Input N) (generator : (ZMod N)ˣ)
    (refs : Refs ctx N) (separation : Separation refs) (source : Store ctx)
    (index : Fin PairCount) (store : Store ctx)
    (invariant : Invariant input generator refs source store) :
    Invariant input generator refs source
        (LatticePairReusableRecovery.step input (refs.pair index) store).1 ∧
      QuadraticCandidateSelect.selectedOption refs.factorSelection
          (LatticePairReusableRecovery.step input (refs.pair index) store).1 =
        FirstAccepted.retainFirst
          (QuadraticCandidateSelect.selectedOption refs.factorSelection store)
          (pairValue generator refs source index) := by
  have value := (LatticePairReusableRecovery.into_correct input generator (refs.pair index)
    (separation.each index) store (invariant.1 index)).selected
  rw [refs.sharedFactorSelection index, invariant.2 index] at value
  refine ⟨⟨?_, ?_⟩, value⟩
  · intro target
    exact initialConditions_transport input generator (refs.pair index) (refs.pair target) store
      (invariant.1 target) (separation.initialFrames index target)
  · intro target
    exact (sourceSamples_frame input (refs.pair index) (refs.pair target) store
      (separation.sourceFrames index target)).trans (invariant.2 target)

omit [BitWord.Selected model] in
private theorem forRange_invariant_fold (invariant : Store ctx → Prop)
    (selected : Store ctx → Option Nat) (count : Nat)
    (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    (checked : Fin count → Option Nat)
    (slots : ∀ index store, invariant store → invariant (records index store).1 ∧
      selected (records index store).1 =
        FirstAccepted.retainFirst (selected store) (checked index))
    (store : Store ctx) (initial : invariant store) :
    invariant (Circuit.forRangeStoreRecord count body records store).1 ∧
      selected (Circuit.forRangeStoreRecord count body records store).1 =
        (List.ofFn checked).foldl FirstAccepted.retainFirst (selected store) := by
  induction count generalizing store with
  | zero => exact ⟨initial, rfl⟩
  | succ count ih =>
      have headHolds := slots 0 store initial
      have tailHolds := ih (fun index => body index.succ) (fun index => records index.succ)
        (fun index => checked index.succ) (fun index => slots index.succ)
        (records 0 store).1 headHolds.1
      refine ⟨tailHolds.1, ?_⟩
      change selected (Circuit.forRangeStoreRecord count (fun index => body index.succ)
        (fun index => records index.succ) (records 0 store).1).1 = _
      rw [tailHolds.2, List.ofFn_succ, List.foldl_cons, headHolds.2]

omit [BitWord.Selected model] in
private theorem forRange_frame (count : Nat) (body : Fin count → Circuit model ctx ctx)
    (records : ∀ index, Store ctx → Store ctx × (body index).Path)
    {shape : CShape} (other : CInputRef ctx shape)
    (frames : ∀ index store, (records index store).1.read other = store.read other)
    (store : Store ctx) :
    (Circuit.forRangeStoreRecord count body records store).1.read other = store.read other := by
  induction count generalizing store with
  | zero => rfl
  | succ count ih =>
      exact (ih (fun index => body index.succ) (fun index => records index.succ)
        (fun index => frames index.succ) (records 0 store).1).trans (frames 0 store)

/-- Every caller read outside every pair body survives without numerical initial premises. -/
theorem into_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other :=
  forRange_frame PairCount _ _ other
    (fun index current => LatticePairReusableRecovery.into_callerFrame input (refs.pair index)
      current other (avoids index)) store

/-- Exact first-success fold, preserved persistent inputs, and complete caller frame. -/
structure Relation (input : Input N) (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  initial : InitialConditions input generator after refs
  sources : ∀ index,
    LatticePairNearestPlaneSavedTarget.sourceSamples (refs.pair index).pair.pair after =
      LatticePairNearestPlaneSavedTarget.sourceSamples (refs.pair index).pair.pair before
  selected : QuadraticCandidateSelect.selectedOption refs.factorSelection after =
    (List.ofFn (pairValue generator refs before)).foldl FirstAccepted.retainFirst
      (QuadraticCandidateSelect.selectedOption refs.factorSelection before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- Every literal pair executes and contributes its original source option in canonical order. -/
theorem into_correct (input : Input N) (generator : (ZMod N)ˣ) (refs : Refs ctx N)
    (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input generator store refs) :
    Relation input generator refs store (step input refs store).1 := by
  have folded := forRange_invariant_fold (Invariant input generator refs store)
    (QuadraticCandidateSelect.selectedOption refs.factorSelection) PairCount
    (fun index => LatticePairReusableRecovery.into input (refs.pair index))
    (fun index => LatticePairReusableRecovery.step input (refs.pair index))
    (pairValue generator refs store) (slot_correct input generator refs separation store)
    store ⟨initial, fun _ => rfl⟩
  exact ⟨folded.1.1, folded.1.2, folded.2, into_callerFrame input refs store⟩

/-- The independent allowance pays for all 120 complete reusable pair invocations. -/
def eventEnvelope (N : Nat) : ResourcePool model :=
  ResourcePool.scale PairCount (LatticePairReusableRecovery.eventEnvelope N)

/-- The independent sequential depth includes every pair, even after an earlier success. -/
def depthBound (N : Nat) : Nat := PairCount * LatticePairReusableRecovery.depthBound N

/-- Every actual native coordinate meets the independent full-batch allowance. -/
theorem into_pool_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N := by
  unfold into at path ⊢
  unfold eventEnvelope
  with_reducible
    exact Circuit.forRange_pool_le PairCount _ _
      (fun index => LatticePairReusableRecovery.into_pool_le input (refs.pair index)) path

/-- The actual complete ordered path meets the independent batch depth bound. -/
theorem into_depth_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N :=
  Circuit.forRange_depth_le PairCount _ _
    (fun index => LatticePairReusableRecovery.into_depth_le input (refs.pair index)) path

/-- Reuse keeps the resident peak at the context plus the actual native-power scope. -/
theorem into_resident_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤
      ctx.residentSpace + Modular.NativePower.powerSpace model.kind (modulusBits N) :=
  Circuit.forRange_resident_le PairCount _ _ (le_add_of_nonneg_right zero_le)
    (fun index => LatticePairReusableRecovery.into_resident_le input (refs.pair index)) path

/-- Auxiliary accounting follows the same actual reusable scope through every pair. -/
theorem into_auxiliary_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Modular.NativePower.powerSpace model.kind (modulusBits N) :=
  Circuit.forRange_auxiliary_le PairCount _ _ (le_add_of_nonneg_right zero_le)
    (fun index => LatticePairReusableRecovery.into_auxiliary_le input (refs.pair index)) path

/-- All pairs jointly restore borrowed systems in the presence of arbitrary external references. -/
theorem into_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History]
    (state : State ctx Reference (model.HiddenState × History)) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.forRange_borrowedRestored PairCount _ Reference
    (fun index =>
      LatticePairReusableRecovery.into_borrowedRestored input (refs.pair index) Reference)
    state

end

end LatticePairRecoveryFold
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
