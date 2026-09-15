/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Batch.Pairs
import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Selection.Seed

/-!
# Seeded fixed-batch recovery tail

This module composes the widened sampler early-factor seed with all 120
literal unordered-pair recovery invocations.  The final persistent selection
is proved equal to the pure fixed-batch recovery value over the same sixteen
retained terminal cells.
-/

section

namespace QuantumAlg
namespace Factoring
namespace EkeraHastadStyle
namespace Canonical
namespace LatticeBatchRecoveryTail

open Execution
open ClassicalRoutines

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

/-- Caller-owned seed, indexed pair fold, and their shared factor selector. -/
structure Refs {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) where
  /-- Input reference for the parameter value. -/
  parameter : CInputRef ctx (ParameterShape N)
  /-- The terminals component of this typed record. -/
  terminals : LatticePairRecoveryBatch.Terminals ctx N
  /-- Nested references for the seed stage. -/
  seed : LatticeEarlyFactorSeed.Refs ctx N
  /-- Nested references for the fold stage. -/
  fold : LatticePairRecoveryFold.Refs ctx N
  sharedSelection : seed.selection = fold.factorSelection
  aligned : LatticePairRecoveryBatch.Aligned fold terminals

/-- Pair-entry facts that must survive the early-factor seed. -/
structure SeedInitialFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (seed : LatticeEarlyFactorSeed.Refs ctx N)
    (pair : LatticePairFactorRecovery.Refs ctx N) : Prop where
  setupParameter : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.pair.setup.parameter
  setupBase : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    (LatticeCandidateModularSetup.parameterBaseInput pair.pair.setup)
  quadraticModulus : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.candidates.quadraticPrefix.modulus
  firstOne : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.first.check.one
  firstModulus : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.first.check.positiveCheck.modulus
  firstZero : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.first.check.positiveCheck.zero
  secondOne : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.second.check.one
  secondModulus : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.second.check.positiveCheck.modulus
  secondZero : LatticeEarlyFactorSeed.CallerFrameAvoids seed
    pair.quadratic.quadratic.recovery.pair.second.check.positiveCheck.zero

/-- Every retained terminal bit survives the early-factor seed. -/
structure SeedTerminalFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : Refs ctx N) : Prop where
  bit : ∀ terminalIndex bitIndex,
    LatticeEarlyFactorSeed.CallerFrameAvoids refs.seed
      (.bitsGet (refs.terminals terminalIndex) bitIndex)

/-- Local certificates and all seed-to-fold frame obligations. -/
structure Separation {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}
    (refs : Refs ctx N) : Prop where
  seed : LatticeEarlyFactorSeed.Separation refs.parameter refs.seed
  fold : LatticePairRecoveryFold.Separation refs.fold
  seedInitialFrames : ∀ index,
    SeedInitialFrameAvoids refs.seed (refs.fold.pair index)
  seedTerminalFrames : SeedTerminalFrameAvoids refs

/-- Entry facts for one sampler value and its clear shared factor selector. -/
structure InitialConditions {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (before : Store ctx) (refs : Refs ctx N) : Prop where
  parameterValue : before.read refs.parameter = parameterValue input sample
  fold : LatticePairRecoveryFold.InitialConditions input
    (preparedResidue sample).unit before refs.fold
  factorInitiallyClear :
    (before.read (FirstAccepted.cellRead
      refs.fold.factorSelection.accepted)).toBool = false

/-- Avoidance of both the seed and every pair invocation. -/
structure CallerFrameAvoids {kind : ProblemKind} {ctx : RuntimeCtx kind}
    {N : Nat} (refs : Refs ctx N) {shape : CShape}
    (other : CInputRef ctx shape) : Prop where
  seed : LatticeEarlyFactorSeed.CallerFrameAvoids refs.seed other
  fold : LatticePairRecoveryFold.CallerFrameAvoids refs.fold other

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Seed the early factor and execute every unordered terminal pair. -/
def into (input : Input N) (refs : Refs ctx N) : Circuit ctx ctx :=
  .seq (LatticeEarlyFactorSeed.into refs.parameter refs.seed)
    (LatticePairRecoveryFold.into input refs.fold)

/-- The complete actual store flows from seeding into the canonical pair sequence. -/
def step (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    Store ctx × (into input refs).Path :=
  Circuit.sequenceRecord (LatticeEarlyFactorSeed.into refs.parameter refs.seed)
    (LatticePairRecoveryFold.into input refs.fold)
    (LatticeEarlyFactorSeed.step refs.parameter refs.seed)
    (LatticePairRecoveryFold.step input refs.fold) store

/-- The complete pair sequence receives the actual store produced by the seed. -/
theorem step_store (input : Input N) (refs : Refs ctx N) (store : Store ctx) :
    (step input refs store).1 = (LatticePairRecoveryFold.step input refs.fold
      (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1).1 :=
  Circuit.sequenceRecord_store _ _ _ _ store

/-- The seed-and-fold record executes on arbitrary histories and external references. -/
theorem into_execute (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into input refs).execute Reference state = state.mapClassical (fun entry =>
      ((step input refs entry.1).1, (entry.2, (step input refs entry.1).2))) :=
  Circuit.execute_sequenceRecord _ _ _ _
    (LatticeEarlyFactorSeed.into_execute refs.parameter refs.seed)
    (LatticePairRecoveryFold.into_execute input refs.fold) Reference state

/-- All structural caller reads outside seed and fold survive on arbitrary numerical stores. -/
theorem into_callerFrame (input : Input N) (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : CallerFrameAvoids refs other) :
    (step input refs store).1.read other = store.read other := by
  rw [step_store]
  exact (LatticePairRecoveryFold.into_callerFrame input refs.fold _ other avoids.fold).trans
    (LatticeEarlyFactorSeed.into_callerFrame refs.parameter refs.seed store other avoids.seed)

private theorem pairInitial_afterSeed (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs ctx N)
    (store : Store ctx) (pair : LatticePairFactorRecovery.Refs ctx N)
    (initial : LatticePairReusableRecovery.InitialConditions input
      (preparedResidue sample).unit store pair)
    (avoids : SeedInitialFrameAvoids refs.seed pair) :
    LatticePairReusableRecovery.InitialConditions input (preparedResidue sample).unit
      (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1 pair := by
  have frame {shape : CShape} (other : CInputRef ctx shape)
      (otherAvoids : LatticeEarlyFactorSeed.CallerFrameAvoids refs.seed other) :
      (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1.read other =
        store.read other :=
    LatticeEarlyFactorSeed.into_callerFrame refs.parameter refs.seed store other otherAvoids
  have parameterFrame := frame _ avoids.setupParameter
  have setup := LatticePairCandidateRecovery.setupInitial_transport input pair.pair.setup
    store _ initial.setup parameterFrame
  have generatorAtEntry : (preparedResidue sample).unit = parameterUnit
      ((LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1.read
        pair.pair.setup.parameter) := by
    rw [parameterFrame]
    exact initial.generatorAtEntry
  have firstOne := frame _ avoids.firstOne
  have firstModulus := frame _ avoids.firstModulus
  have firstZero := frame _ avoids.firstZero
  have secondOne := frame _ avoids.secondOne
  have secondModulus := frame _ avoids.secondModulus
  have secondZero := frame _ avoids.secondZero
  have modulus := frame _ avoids.quadraticModulus
  refine ⟨setup, generatorAtEntry, ?_, ?_⟩
  · unfold QuadraticCandidatePairSelect.InitialConditions
      QuadraticCandidateCheck.TotalInitialConditions
    rw [firstOne, firstModulus, firstZero, secondOne, secondModulus, secondZero]
    exact initial.quadratic.pair
  · exact (congrArg CShape.Value.toNat modulus).trans initial.quadratic.modulusValue

private theorem foldInitial_afterSeed (input : Input N)
    (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs ctx N)
    (separation : Separation refs) (store : Store ctx)
    (initial : LatticePairRecoveryFold.InitialConditions input
      (preparedResidue sample).unit store refs.fold) :
    LatticePairRecoveryFold.InitialConditions input (preparedResidue sample).unit
      (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1 refs.fold := by
  intro index
  exact pairInitial_afterSeed input sample refs store (refs.fold.pair index)
    (initial index) (separation.seedInitialFrames index)

private theorem sourceBits_afterSeed (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (terminalIndex : Fin 16) :
    BatchMachine.sourceBits N (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1
        (refs.terminals terminalIndex) =
      BatchMachine.sourceBits N store (refs.terminals terminalIndex) := by
  funext bitIndex
  unfold BatchMachine.sourceBits
  exact congrArg CShape.Value.toBool
    (LatticeEarlyFactorSeed.into_callerFrame refs.parameter refs.seed store _
      (separation.seedTerminalFrames.bit terminalIndex bitIndex))

private theorem preparedSamples_afterSeed (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx) :
    LatticePairRecoveryBatch.preparedSamples (preparedResidue sample) refs.terminals
        (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1 =
      LatticePairRecoveryBatch.preparedSamples (preparedResidue sample) refs.terminals store := by
  unfold LatticePairRecoveryBatch.preparedSamples
  apply List.Vector.ext
  intro terminalIndex
  simp only [List.Vector.get_map, List.Vector.get_ofFn]
  exact congrArg (fun bits => (⟨preparedResidue sample, bits⟩ :
    BatchRecovery.PreparedSample N (shortLogBits N) (tradeoffBits N)))
    (sourceBits_afterSeed refs separation store terminalIndex)

/-- The exact fixed-batch value over the original terminal cells and complete caller frame. -/
structure Relation (sample : Fin (2 ^ residueSamplingBits N)) (refs : Refs ctx N)
    (before after : Store ctx) : Prop where
  selected : QuadraticCandidateSelect.selectedOption refs.fold.factorSelection after =
    BatchRecovery.batchValue N (shortLogBits N) (tradeoffBits N)
      (LatticePairRecoveryBatch.preparedSamples (preparedResidue sample) refs.terminals before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerFrameAvoids refs other → after.read other = before.read other

/-- The actual early-factor seed and full pair sequence realize the original pure batch value. -/
theorem into_correct (input : Input N) (sample : Fin (2 ^ residueSamplingBits N))
    (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (initial : InitialConditions input sample store refs) :
    Relation sample refs store (step input refs store).1 := by
  have seedHolds := LatticeEarlyFactorSeed.into_correct input sample refs.parameter refs.seed
    separation.seed store initial.parameterValue
  have seedInitiallyClear :
      (store.read (FirstAccepted.cellRead refs.seed.selection.accepted)).toBool = false := by
    rw [refs.sharedSelection]
    exact initial.factorInitiallyClear
  have seedInitialOption :
      QuadraticCandidateSelect.selectedOption refs.seed.selection store = none := by
    simp [QuadraticCandidateSelect.selectedOption, FirstAccepted.selectedOption, seedInitiallyClear]
  have seedOption : QuadraticCandidateSelect.selectedOption refs.fold.factorSelection
      (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1 =
        (preparedResidue sample).earlyFactor := by
    rw [← refs.sharedSelection, seedHolds.selected, seedInitialOption]
    rfl
  have foldInitial := foldInitial_afterSeed input sample refs separation store initial.fold
  have foldHolds := LatticePairRecoveryFold.into_correct input (preparedResidue sample).unit
    refs.fold separation.fold (LatticeEarlyFactorSeed.step refs.parameter refs.seed store).1
    foldInitial
  refine ⟨?_, into_callerFrame input refs store⟩
  rw [step_store, foldHolds.selected, seedOption]
  rw [LatticePairRecoveryBatch.selectedFold_eq_batchValue
    (preparedResidue sample) refs.fold refs.terminals refs.aligned]
  rw [preparedSamples_afterSeed sample refs separation store]

/-- The independent native allowance pays for the seed and every complete reusable pair. -/
def eventEnvelope (N : Nat) : ResourcePool kind :=
  LatticeEarlyFactorSeed.eventEnvelope N + LatticePairRecoveryFold.eventEnvelope N

/-- The independent sequential depth includes seeding and the complete pair fold. -/
def depthBound (N : Nat) : Nat := 5 + LatticePairRecoveryFold.depthBound N

private theorem sequence_pool_le (first second : Circuit ctx ctx)
    (firstBound secondBound : ResourcePool kind)
    (firstLe : ∀ path, first.resourcePool path ≤ firstBound)
    (secondLe : ∀ path, second.resourcePool path ≤ secondBound)
    (path : (Circuit.seq first second).Path) :
    (Circuit.seq first second).resourcePool path ≤ firstBound + secondBound := by
  change ResourcePool.ofList (first.eventTrace path.1 ++ second.eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (firstLe path.1) (secondLe path.2)

/-- Every actual native coordinate is bounded by the independent seed-and-fold allowance. -/
theorem into_pool_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).resourcePool path ≤ eventEnvelope N := by
  unfold into at path ⊢
  unfold eventEnvelope
  with_reducible
    exact sequence_pool_le _ _ _ _
      (LatticeEarlyFactorSeed.into_pool_le refs.parameter refs.seed)
      (LatticePairRecoveryFold.into_pool_le input refs.fold) path

/-- The actual complete sequential path meets the independent dependency-depth bound. -/
theorem into_depth_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).depth (fun _ => 1) path ≤ depthBound N :=
  Nat.add_le_add (LatticeEarlyFactorSeed.into_depth_le refs.parameter refs.seed path.1)
    (LatticePairRecoveryFold.into_depth_le input refs.fold path.2)

/-- Seeding and pair reuse retain the context plus the actual native-power resident peak. -/
theorem into_resident_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakResidentSpace path ≤
      ctx.residentSpace + Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakResidentSpace_seq (LatticeEarlyFactorSeed.into refs.parameter refs.seed)
    (LatticePairRecoveryFold.into input refs.fold) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeEarlyFactorSeed.into_resident_le refs.parameter refs.seed path.1).trans
      (le_add_of_nonneg_right zero_le))
    (LatticePairRecoveryFold.into_resident_le input refs.fold path.2)

/-- Auxiliary accounting follows the same actual scopes and retained context roles. -/
theorem into_auxiliary_le (input : Input N) (refs : Refs ctx N) (path : (into input refs).Path) :
    (into input refs).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + Modular.NativePower.powerSpace kind (modulusBits N) := by
  refine (Circuit.peakAuxiliarySpace_seq (LatticeEarlyFactorSeed.into refs.parameter refs.seed)
    (LatticePairRecoveryFold.into input refs.fold) path).le.trans ?_
  exact SpacePool.max_le
    ((LatticeEarlyFactorSeed.into_auxiliary_le refs.parameter refs.seed path.1).trans
      (le_add_of_nonneg_right zero_le))
    (LatticePairRecoveryFold.into_auxiliary_le input refs.fold path.2)

/-- Seed and full recovery jointly restore all borrowed systems with arbitrary references. -/
theorem into_borrowedRestored (input : Input N) (refs : Refs ctx N) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference History) :
    (into input refs).BorrowedRestored Reference state
      ((into input refs).execute Reference state) :=
  Circuit.borrowedRestored_seq _ _ state
    (LatticeEarlyFactorSeed.into_borrowedRestored refs.parameter refs.seed Reference state)
    (LatticePairRecoveryFold.into_borrowedRestored input refs.fold Reference _)

end

end LatticeBatchRecoveryTail
end Canonical
end EkeraHastadStyle
end Factoring
end QuantumAlg

end
