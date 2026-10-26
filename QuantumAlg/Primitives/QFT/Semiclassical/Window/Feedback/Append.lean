/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Prefix
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Feedback.Prefix
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Decode

/-!
# Exact retained prefixes after a real chronological readout

The prefix is extracted from the original result cells. Past-cell retention
and the actual current outcome reads prove its append equation; the complete
prefix is exactly the label consumed by the existing paid frequency decoder.
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback

noncomputable section

open Execution

variable {ctx : RuntimeCtx .quantum} {total active : Nat}

/-- A mathematical prefix read from the original complete family of result cells. -/
def retainedPrefix (results : BitPosition total → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (count : Nat) (bounded : count ≤ total) (stored : Store ctx) : Bits count :=
  Partner.prefixBits count bounded (Decode.storedStream results stream stored)

/-- Every retained prefix coordinate reads its own original cell. -/
lemma retainedPrefix_coordinate (results : BitPosition total → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (count : Nat) (bounded : count ≤ total) (stored : Store ctx)
    (position : Fin count) :
    tupleCoordinates count (retainedPrefix results stream count bounded stored) position =
      (stored.read (.storage
        (results (stream, Fin.castLE bounded position)).toCStorageRef)).toFin := by
  rw [retainedPrefix, Partner.prefixBits_coordinate, Decode.windowDecode_storedStream_coordinate]

/-- Equal reads of original cells preserve every retained prefix label. -/
lemma retainedPrefix_congr (results : BitPosition total → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (count : Nat) (bounded : count ≤ total) (before after : Store ctx)
    (reads : ∀ position : Fin count,
      after.read (.storage (results (stream, Fin.castLE bounded position)).toCStorageRef) =
        before.read (.storage (results (stream, Fin.castLE bounded position)).toCStorageRef)) :
    retainedPrefix results stream count bounded after =
      retainedPrefix results stream count bounded before := by
  apply tupleCoordinates_injective count
  funext position
  rw [retainedPrefix_coordinate, retainedPrefix_coordinate]
  exact congrArg CShape.Value.toFin (reads position)

/-- At the actual incoming cursor this is precisely the existing native feedback label. -/
lemma retainedPrefix_before (ports : Ports ctx total active) (stored : Store ctx) :
    retainedPrefix ports.results ports.stream ports.start (start_bound ports) stored =
      storedPrefix ports stored := by
  apply tupleCoordinates_injective ports.start
  funext position
  rw [retainedPrefix_coordinate, window_storedPrefix_coordinate]
  rfl

/-- At the full cursor the same original cells give the paid decoder's complete stream. -/
lemma retainedPrefix_all (results : BitPosition total → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (stored : Store ctx) :
    retainedPrefix results stream total (Nat.le_refl total) stored =
      Decode.storedStream results stream stored :=
  Partner.prefixBits_all total (Decode.storedStream results stream stored)

/-- The complete retained row is exactly the frequency returned by the original decoder. -/
lemma retainedPrefix_fullRows (inverse : Bool)
    (results : BitPosition total → CWriteRef ctx (.finite 2))
    (stream : Fin 2) (stored : Store ctx) (source : Bits total) :
    Partner.fourierRows inverse total
        (retainedPrefix results stream total (Nat.le_refl total) stored)
        (Partner.prefixBits total (Nat.le_refl total) source) =
      Partner.fullRows inverse total (Decode.storedFrequency results stream stored) source := by
  rw [retainedPrefix_all, Partner.prefixBits_all, Partner.qftPartner_fullRows_physical,
    Decode.storedFrequency, Partner.qftPartner_frequencyBits_decode]

/-- Every real current readout appends its outcome to the unchanged earlier original cells. -/
lemma retainedPrefix_append (ports : Ports ctx total active) (before after : Store ctx)
    (outcome : Bits active)
    (pastReads : ∀ previous : BitPosition total, ports.past previous →
      after.read (.storage (ports.results previous).toCStorageRef) =
        before.read (.storage (ports.results previous).toCStorageRef))
    (currentReads : ∀ bit : Fin active,
      (after.read (.storage (ports.output bit).toCStorageRef)).toFin =
        tupleCoordinates active outcome bit) :
    retainedPrefix ports.results ports.stream (active + ports.start)
        (by have := ports.within; omega) after =
      Partner.blockBits ports.start active (storedPrefix ports before) outcome := by
  apply Partner.blockBits_eq_of_coordinates
  · intro previous
    rw [retainedPrefix_coordinate, window_storedPrefix_coordinate]
    have original : Fin.castLE (by have := ports.within; omega)
        (Partner.prefixPosition ports.start active previous) =
      previousIndex ports previous := Fin.ext rfl
    rw [original]
    exact congrArg CShape.Value.toFin
      (pastReads (ports.stream, previousIndex ports previous) ⟨rfl, previous.isLt⟩)
  · intro bit
    rw [retainedPrefix_coordinate]
    have original : Fin.castLE (by have := ports.within; omega)
        (Partner.suffixPosition ports.start active bit) = ports.position bit := Fin.ext rfl
    rw [original]
    exact currentReads bit

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Window.Feedback
