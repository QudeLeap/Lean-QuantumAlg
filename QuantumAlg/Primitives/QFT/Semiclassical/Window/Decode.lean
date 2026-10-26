/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Ports
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Native.Decode

/-!
# Paid decoding of the original chronological Fourier result cells

The existing generic decoder executes one real finite-bit pack and the
literal big-endian shift-and-increment word. Its input selects reversed
positions of the same real stored cells; no writable reference is renamed.
This is the original negative Fourier source's frequency convention at
arbitrary count, including zero. Every quantum/reference/history block is
retained by the actual classical interpreter.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Decode

noncomputable section

open Execution ClassicalRoutines.FiniteCyclicDLP.RawRecovery

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {count : Nat} {services : ClassicalOracleModel}

/-- Actual input references in the order consumed by the paid big-endian decoder. -/
def input (results : BitPosition count → CWriteRef ctx (.finite 2)) (stream : Fin 2) :
    CInputRef ctx (.fixedVector count (.finite 2)) :=
  .fixedVector fun position => .storage (results (stream, position.rev)).toCStorageRef

/-- The same existing native packing scope and decoder, with all real instructions retained. -/
def circuit (results : BitPosition count → CWriteRef ctx (.finite 2)) (stream : Fin 2)
    (decoded : CWriteRef ctx (.unsignedWord count)) :
    Circuit (.quantum AlgorithmGate.model .empty BitWord.model services) ctx ctx true :=
  Native.measuredDecodeInto (input results stream) decoded

/-- Exact complete original Store, service-state, History and Reference execution. -/
lemma windowDecode_execute (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (decoded : CWriteRef ctx (.unsignedWord count))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    (circuit results stream decoded).execute environment Reference state =
      state.mapClassical (fun entry =>
        let next := Native.measuredDecodeStep (model :=
          .quantum AlgorithmGate.model .empty BitWord.model services)
          (input results stream) decoded entry.1
        (next.1, (entry.2.1, (entry.2.2, next.2)))) :=
  Native.measuredDecodeInto_execute
    (model := .quantum AlgorithmGate.model .empty BitWord.model services)
    (environment := environment) (input results stream) decoded Reference state

/-- Physical low-frequency-bit-first outcomes supply exactly the original canonical frequency. -/
lemma windowDecode_frequency_input (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (store : Store ctx) (frequency : Fin (2 ^ count))
    (recorded : ∀ position, store.read
      (.storage (results (stream, position)).toCStorageRef) =
        .finite (tupleCoordinates count (frequencyBits count frequency) position)) :
    Native.measuredDecodeInput (store.read (input results stream)) =
      ({ order := .bigEndian,
         bits := ClassicalAlgorithms.TerminalDecode.encodeBits .bigEndian frequency } :
        ClassicalAlgorithms.TerminalDecode.Input count) := by
  apply congrArg (ClassicalAlgorithms.TerminalDecode.Input.mk .bigEndian)
  funext position
  change decide ((store.read
    (.storage (results (stream, position.rev)).toCStorageRef)).toFin.val = 1) =
      frequency.val.testBit position.rev.val
  rw [recorded, Partner.qftPartner_frequency_reversed_coordinate]
  change decide (((finTwoEquiv.symm (frequency.val.testBit position.rev.val)) : Fin 2).val = 1) = _
  generalize frequency.val.testBit position.rev.val = value
  cases value <;> rfl

/-- The real paid decoder writes the canonical source frequency, with no truncation. -/
lemma windowDecode_frequency_output (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx)
    (frequency : Fin (2 ^ count))
    (recorded : ∀ position, store.read
      (.storage (results (stream, position)).toCStorageRef) =
        .finite (tupleCoordinates count (frequencyBits count frequency) position)) :
    ((Native.measuredDecodeStep (model :=
      .quantum AlgorithmGate.model .empty BitWord.model services)
        (input results stream) decoded store).1.read
          (ClassicalRoutines.TerminalDecode.writeInput decoded)).toNat = frequency.val := by
  refine (Native.measuredDecodeInto_read_output (model :=
    .quantum AlgorithmGate.model .empty BitWord.model services)
      (input results stream) decoded store).trans ?_
  rw [windowDecode_frequency_input results stream store frequency recorded,
    ClassicalAlgorithms.TerminalDecode.eval_encodeBits]

/-- This label is extracted from the actual complete original stream of retained cells. -/
def storedStream (results : BitPosition count → CWriteRef ctx (.finite 2)) (stream : Fin 2)
    (store : Store ctx) : Bits count :=
  (binaryEquiv count).symm (BinaryBasis.bigEndianEquiv count
    (fun position => (store.read (.storage (results (stream, position)).toCStorageRef)).toFin))

lemma windowDecode_storedStream_coordinate
    (results : BitPosition count → CWriteRef ctx (.finite 2)) (stream : Fin 2)
    (store : Store ctx) (position : Fin count) :
    tupleCoordinates count (storedStream results stream store) position =
      (store.read (.storage (results (stream, position)).toCStorageRef)).toFin := by
  simp only [tupleCoordinates, storedStream, Equiv.apply_symm_apply]
  exact congrFun ((BinaryBasis.bigEndianEquiv count).symm_apply_apply _) position

/-- Canonical frequency decoded from those real chronological bits, including their reversal. -/
def storedFrequency (results : BitPosition count → CWriteRef ctx (.finite 2)) (stream : Fin 2)
    (store : Store ctx) : Fin (2 ^ count) :=
  qftReverseBits count (binaryEquiv count (storedStream results stream store))

/-- On every original Store, the actual paid decoder returns its own true retained frequency. -/
lemma windowDecode_stored_frequency (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (decoded : CWriteRef ctx (.unsignedWord count)) (store : Store ctx) :
    ((Native.measuredDecodeStep (model :=
      .quantum AlgorithmGate.model .empty BitWord.model services)
        (input results stream) decoded store).1.read
          (ClassicalRoutines.TerminalDecode.writeInput decoded)).toNat =
      (storedFrequency results stream store).val := by
  apply windowDecode_frequency_output
  intro position
  rw [storedFrequency, Partner.qftPartner_frequencyBits_decode,
    windowDecode_storedStream_coordinate]
  generalize store.read (.storage (results (stream, position)).toCStorageRef) = value
  cases value
  rfl

/-- Actual decoding changes no quantum or external-reference marginal. -/
lemma windowDecode_quantumMarginal (results : BitPosition count → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (decoded : CWriteRef ctx (.unsignedWord count))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (Reference : Register) {History : Type} [Fintype History]
    (state : State ctx Reference (services.HiddenState × History)) :
    ((circuit results stream decoded).execute environment Reference state).quantumMarginal =
      state.quantumMarginal := by
  rw [windowDecode_execute]
  exact ExecutionState.mapClassical_quantumMarginal _ _

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Decode
