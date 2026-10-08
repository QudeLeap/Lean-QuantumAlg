/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Terminal.Program.Correctness

/-!
# Exact sequential decoding of both original terminal samples

The first actual decoder preserves the second sample's stored source. The
second actual decoder preserves all four first-decoder results. Consequently
both complete output packages refer to the original incoming store, with a
complete frame outside the eight original write identities.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Read one of the four actual original decoder output words as a natural value. -/
def outputNat (refs : Refs ctx N) (store : Store ctx) : PairOutputSlot → Nat
  | .full => (store.read (.storage refs.full.toCStorageRef)).toNat
  | .scratch => (store.read (.storage refs.scratch.toCStorageRef)).toNat
  | .j => (store.read (.storage refs.j.toCStorageRef)).toNat
  | .k => (store.read (.storage refs.k.toCStorageRef)).toNat

/-- Independent original source value of each supplied decoder output identity. -/
def sourceOutputNat (N : Nat) (store : Store ctx)
    (input : CInputRef ctx (.bits (measurementBits N))) : PairOutputSlot → Nat
  | .full => (BatchRecovery.decodeFullRegisterIndex (shortLogBits N) (tradeoffBits N)
      (sourceBits N store input)).val
  | .scratch => (sourceSample N store input).1.val
  | .j => (sourceSample N store input).1.val
  | .k => (sourceSample N store input).2.val

/-- The actual single decoder materializes the independent source value of every output. -/
theorem decodeInto_outputs {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (slot : PairOutputSlot) :
    outputNat refs (decodeStep refs store).1 slot =
      sourceOutputNat N store (terminalInput refs) slot := by
  have correct := decodeInto_correct refs separation store
  cases slot with
  | full => exact correct.full
  | scratch => exact correct.scratch
  | j => exact correct.j
  | k => exact correct.k

/-- The first actual decoder preserves the complete second stored terminal source. -/
theorem decodePair_first_source {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PairRefs ctx N) (separation : PairSeparation refs)
    (store : Store ctx) :
    sourceBits N (decodeStep refs.first store).1 (terminalInput refs.second) =
      sourceBits N store (terminalInput refs.second) :=
  sourceBits_of_read_eq _ _ _
    (decodeInto_callerFrame refs.first store _ separation.secondInputAvoidsFirst)

/-- The second actual decoder preserves every original first-decoder output word. -/
theorem decodePair_second_frame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PairRefs ctx N) (separation : PairSeparation refs)
    (store : Store ctx) (slot : PairOutputSlot) :
    outputNat refs.first (decodeStep refs.second store).1 slot =
      outputNat refs.first store slot := by
  have preserved {shape : CShape} (other : CInputRef ctx shape)
      (sameKey : other.storageKeys = [pairOutputKey refs.first slot]) :
      (decodeStep refs.second store).1.read other = store.read other := by
    apply decodeInto_callerFrame refs.second store other
    intro secondSlot
    rw [sameKey, List.mem_singleton]
    exact (separation.firstOutputsAvoidSecond slot secondSlot).symm
  cases slot with
  | full =>
    exact congrArg CShape.Value.toNat (preserved (.storage refs.first.full.toCStorageRef) rfl)
  | scratch =>
    exact congrArg CShape.Value.toNat (preserved (.storage refs.first.scratch.toCStorageRef) rfl)
  | j => exact congrArg CShape.Value.toNat (preserved (.storage refs.first.j.toCStorageRef) rfl)
  | k => exact congrArg CShape.Value.toNat (preserved (.storage refs.first.k.toCStorageRef) rfl)

/-- Sequential decoding preserves every actual read outside the eight original write cells. -/
theorem decodePairInto_callerFrame {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PairRefs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (first : CallerSeparated refs.first other) (second : CallerSeparated refs.second other) :
    (decodePairStep refs store).1.read other = store.read other := by
  change (decodeStep refs.second (decodeStep refs.first store).1).1.read other = _
  rw [decodeInto_callerFrame refs.second _ other second,
    decodeInto_callerFrame refs.first _ other first]

/-- Both complete actual decoder packages match the original sources and retain the caller frame. -/
structure DecodePairOutcome (refs : PairRefs ctx N) (before after : Store ctx) : Prop where
  first : ∀ slot, outputNat refs.first after slot =
    sourceOutputNat N before (terminalInput refs.first) slot
  second : ∀ slot, outputNat refs.second after slot =
    sourceOutputNat N before (terminalInput refs.second) slot
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    CallerSeparated refs.first other → CallerSeparated refs.second other →
      after.read other = before.read other

/-- Two actual sequential decoders recover both original samples without initial-value premises. -/
theorem decodePairInto_correct {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} (refs : PairRefs ctx N) (separation : PairSeparation refs)
    (store : Store ctx) : DecodePairOutcome refs store (decodePairStep refs store).1 := by
  refine ⟨?_, ?_, decodePairInto_callerFrame refs store⟩
  · intro slot
    change outputNat refs.first (decodeStep refs.second (decodeStep refs.first store).1).1 slot = _
    rw [decodePair_second_frame refs separation,
      decodeInto_outputs refs.first separation.first]
  · intro slot
    change outputNat refs.second (decodeStep refs.second (decodeStep refs.first store).1).1 slot = _
    rw [decodeInto_outputs refs.second separation.second]
    have same := decodePair_first_source refs separation store
    cases slot <;> simp only [sourceOutputNat, sourceSample, same]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.BatchMachine
