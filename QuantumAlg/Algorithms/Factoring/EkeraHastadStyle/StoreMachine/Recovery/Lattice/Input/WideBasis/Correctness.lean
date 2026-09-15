/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Input.WideBasis.Frames

/-!
# Actual wide source-basis correctness from both original samples

Both complete decoder packages remain equal to their original source values.
The actual raw nine-cell basis is exactly the original two-sample source basis,
and its unchanged workspace view supplies the actual Gram/LLL representation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix

open Execution
open ClassicalRoutines
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The complete actual prefix preserves every original first-sample decoder output. -/
theorem decodeBasisInto_firstOutputs (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.outputNat refs.pair.first (decodeBasisStep refs store).1 slot =
      BatchMachine.sourceOutputNat N store (BatchMachine.terminalInput refs.pair.first) slot := by
  have decoded := BatchMachine.decodePairInto_correct refs.pair separation.decoder store
  cases slot with
  | full =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.first.full (by simp [decoderKeys]))).trans (decoded.first .full)
  | scratch =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.first.scratch (by simp [decoderKeys]))).trans (decoded.first .scratch)
  | j =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.first.j (by simp [decoderKeys]))).trans (decoded.first .j)
  | k =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.first.k (by simp [decoderKeys]))).trans (decoded.first .k)

/-- The complete actual prefix preserves every original second-sample decoder output. -/
theorem decodeBasisInto_secondOutputs (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (slot : BatchMachine.PairOutputSlot) :
    BatchMachine.outputNat refs.pair.second (decodeBasisStep refs store).1 slot =
      BatchMachine.sourceOutputNat N store (BatchMachine.terminalInput refs.pair.second) slot := by
  have decoded := BatchMachine.decodePairInto_correct refs.pair separation.decoder store
  cases slot with
  | full =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.second.full (by simp [decoderKeys]))).trans (decoded.second .full)
  | scratch =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.second.scratch (by simp [decoderKeys]))).trans (decoded.second .scratch)
  | j =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.second.j (by simp [decoderKeys]))).trans (decoded.second .j)
  | k =>
    exact (congrArg CShape.Value.toNat (decodeBasis_decoderFrame refs separation store
      refs.pair.second.k (by simp [decoderKeys]))).trans (decoded.second .k)

/-- Actual decoding and native loading construct the original nine-cell source basis. -/
theorem decodeBasisInto_rawBasis (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (zeros : BasisInitialZero store refs) :
    LatticeRepresentation.BasisRawRepresents (decodeBasisStep refs store).1 refs.raw
      (sourceBasis refs store) := by
  have decoded := BatchMachine.decodePairInto_correct refs.pair separation.decoder store
  have loaded := LatticeBasis.loadBasisInto_correct (shortLogBits N) (tradeoffBits N)
    refs.pair refs.raw separation.basis (BatchMachine.decodePairStep refs.pair store).1
    (decoder_initialZeros refs separation store zeros)
  have firstJ :
      ((BatchMachine.decodePairStep refs.pair store).1.read
        (.storage refs.pair.first.j.toCStorageRef)).toNat = (sourceSamples refs store).1.1.val :=
    decoded.first .j
  have secondJ :
      ((BatchMachine.decodePairStep refs.pair store).1.read
        (.storage refs.pair.second.j.toCStorageRef)).toNat = (sourceSamples refs store).2.1.val :=
    decoded.second .j
  unfold LatticeRepresentation.BasisRawRepresents sourceBasis RSA.shortLogLatticeBasis
  refine ⟨?_, ?_, loaded.b13, ?_, loaded.zeros .b22, loaded.zeros .b23,
    loaded.zeros .b31, ?_, loaded.zeros .b33⟩
  · have first := loaded.b11
    rw [firstJ] at first
    exact first
  · have second := loaded.b12
    rw [secondJ] at second
    exact second
  · simp only [RSA.shortLogLatticeModulus, Nat.cast_pow, Nat.cast_ofNat]
    exact loaded.b21
  · simp only [RSA.shortLogLatticeModulus, Nat.cast_pow, Nat.cast_ofNat]
    exact loaded.b32

/-- Complete original decoded outputs, actual source basis, and full thirteen-write caller frame. -/
structure DecodeBasisOutcome (refs : Refs ctx N) (before after : Store ctx) : Prop where
  first : ∀ slot, BatchMachine.outputNat refs.pair.first after slot =
    BatchMachine.sourceOutputNat N before (BatchMachine.terminalInput refs.pair.first) slot
  second : ∀ slot, BatchMachine.outputNat refs.pair.second after slot =
    BatchMachine.sourceOutputNat N before (BatchMachine.terminalInput refs.pair.second) slot
  basis : LatticeRepresentation.BasisRawRepresents after refs.raw (sourceBasis refs before)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    (∀ key ∈ writtenKeys refs, key ∉ other.storageKeys) → after.read other = before.read other

/-- The actual wide prefix realizes its entire original source-basis boundary. -/
theorem decodeBasisInto_correct (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (zeros : BasisInitialZero store refs) :
    DecodeBasisOutcome refs store (decodeBasisStep refs store).1 :=
  ⟨decodeBasisInto_firstOutputs refs separation store,
    decodeBasisInto_secondOutputs refs separation store,
    decodeBasisInto_rawBasis refs separation store zeros, decodeBasisInto_callerFrame refs store⟩

/-- The actual wide source basis has exactly the original mutable view required by Gram and LLL. -/
theorem decodeBasisInto_metricBasis (refs : Refs ctx N) (separation : Separation refs)
    (store : Store ctx) (zeros : BasisInitialZero store refs) :
    LatticeMetricMachine.BasisRawRepresents (decodeBasisStep refs store).1
      (LatticeRepresentation.basisRefs refs.raw refs.roles) (sourceBasis refs store) :=
  (LatticeRepresentation.basisRawRepresents_iff_metricBasis _ refs.raw refs.roles _).mp
    (decodeBasisInto_rawBasis refs separation store zeros)

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideInitializationPrefix
