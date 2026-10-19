/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Input.WideBasis

/-!
# Actual wide decoder and basis cross-stage frames

The original decoder/raw separation preserves all nine raw coordinates during
decoding and every decoder result during basis loading. The complete actual
prefix preserves all reads outside the thirteen original written identities.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- Each actual first-decoder output belongs to the original eight-cell decoder footprint. -/
lemma firstDecoderKey_mem (pair : BatchMachine.PairRefs ctx N)
    (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.pairOutputKey pair.first slot ∈ decoderKeys pair := by
  cases slot <;> simp [BatchMachine.pairOutputKey, decoderKeys]

/-- Each actual second-decoder output belongs to the original eight-cell decoder footprint. -/
lemma secondDecoderKey_mem (pair : BatchMachine.PairRefs ctx N)
    (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.pairOutputKey pair.second slot ∈ decoderKeys pair := by
  cases slot <;> simp [BatchMachine.pairOutputKey, decoderKeys]

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Both actual decoders preserve every raw coordinate from the original nine-cell basis. -/
lemma decoder_rawFrame (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (output : CWriteRef ctx (.unsignedWord (Width N))) (member : output.key ∈ rawKeys refs.raw) :
    (BatchMachine.decodePairStep refs.pair store).1.read (.storage output.toCStorageRef) =
      store.read (.storage output.toCStorageRef) := by
  apply BatchMachine.decodePairInto_callerFrame
  · intro slot
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      separation.decoderRaw _ (firstDecoderKey_mem refs.pair slot) output.key member
  · intro slot
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      separation.decoderRaw _ (secondDecoderKey_mem refs.pair slot) output.key member

/-- Actual decoding preserves all four original zero coordinates needed by the basis loader. -/
lemma decoder_initialZeros (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    (zeros : BasisInitialZero store refs) :
    LatticeBasis.InitialZeros refs.raw (BatchMachine.decodePairStep refs.pair store).1 := by
  have frame (cell : LatticeBasis.ZeroCell) :
      (BatchMachine.decodePairStep refs.pair store).1.read
        (LatticeBasis.zeroCellInput refs.raw cell) =
        store.read (LatticeBasis.zeroCellInput refs.raw cell) := by
    cases cell <;> apply decoder_rawFrame refs separation store <;> simp [rawKeys]
  intro cell
  rw [frame cell]
  exact zeros cell

/-- Actual basis loading preserves every output word of both original decoder packages. -/
lemma basis_decoderFrame (refs : Refs ctx N) (separation : Separation refs) (store : Store ctx)
    {shape : CShape} (output : CWriteRef ctx shape) (member : output.key ∈ decoderKeys refs.pair) :
    (LatticeBasis.basisStep (shortLogBits N) (tradeoffBits N) refs.pair refs.raw store).1.read
      (.storage output.toCStorageRef) = store.read (.storage output.toCStorageRef) := by
  have avoids (key : StorageKey) (raw : key ∈ rawKeys refs.raw) :
      key ∉ (CInputRef.storage output.toCStorageRef).storageKeys := by
    simpa only [CInputRef.storageKeys, List.mem_singleton] using
      (separation.decoderRaw output.key member key raw).symm
  exact LatticeBasis.loadBasisInto_callerFrame _ _ _ _ store _
    (avoids _ (by simp [rawKeys])) (avoids _ (by simp [rawKeys]))
    (avoids _ (by simp [rawKeys])) (avoids _ (by simp [rawKeys])) (avoids _ (by simp [rawKeys]))

/-- The complete actual prefix retains every decoder word through its subsequent basis load. -/
lemma decodeBasis_decoderFrame (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) {shape : CShape} (output : CWriteRef ctx shape)
    (member : output.key ∈ decoderKeys refs.pair) :
    (decodeBasisStep refs store).1.read (.storage output.toCStorageRef) =
      (BatchMachine.decodePairStep refs.pair store).1.read (.storage output.toCStorageRef) :=
  basis_decoderFrame refs separation _ output member

/-- Every caller read outside the original thirteen writes is preserved by the actual prefix. -/
lemma decodeBasisInto_callerFrame (refs : Refs ctx N) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (avoids : ∀ key ∈ writtenKeys refs, key ∉ other.storageKeys) :
    (decodeBasisStep refs store).1.read other = store.read other := by
  change (LatticeBasis.basisStep (shortLogBits N) (tradeoffBits N) refs.pair refs.raw
    (BatchMachine.decodePairStep refs.pair store).1).1.read other = _
  rw [LatticeBasis.loadBasisInto_callerFrame _ _ _ _ _ other
    (avoids _ (by simp [writtenKeys])) (avoids _ (by simp [writtenKeys]))
    (avoids _ (by simp [writtenKeys])) (avoids _ (by simp [writtenKeys]))
    (avoids _ (by simp [writtenKeys]))]
  apply BatchMachine.decodePairInto_callerFrame
  · intro slot
    exact avoids _ (List.mem_append_left _ (firstDecoderKey_mem refs.pair slot))
  · intro slot
    exact avoids _ (List.mem_append_left _ (secondDecoderKey_mem refs.pair slot))

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
