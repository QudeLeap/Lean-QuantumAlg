/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Layout
import all QuantumAlg.Primitives.MAU.Addition.HRS.Controlled.BorrowedIncrement.Resources
import all QuantumAlg.Components.Encoded.BitGates.Realization

/-!
# Actual controlled suffix increments inside the two quantum words

The most significant selected target bits form the incremented suffix of
the little-endian arithmetic word. Equally many existing addend bits are
borrowed and restored. The original reduction flag supplies the preserved
quantum control. Neither operand is converted into a classical parameter.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition

noncomputable section

open QuantumAlg.EncodedBit GateSpec

private lemma source_onto (length : Nat) :
    Function.Surjective (MAU.Addition.TTK.overflowEncoding length).encode := by
  intro label
  obtain ⟨⟨words, flag⟩, rfl⟩ :=
    (prodEquiv (m := length + length) (n := 1)).surjective label
  obtain ⟨⟨left, right⟩, rfl⟩ := (prodEquiv (m := length) (n := length)).surjective words
  fin_cases flag
  · exact ⟨((left, right), false), rfl⟩
  · exact ⟨((left, right), true), rfl⟩

/-- Actual borrowed, target and control positions within the original 513-wire frame. -/
def suffixPosition (length : Nat) (fits : length ≤ width)
    (index : Fin (MAU.Addition.TTK.overflowEncoding length).width) : Fin encoding.width :=
  ⟨if index.val < length then index.val
    else if index.val < length + length then width + (index.val - length)
    else width + width, by
      have bounded := index.isLt
      change index.val < length + length + 1 at bounded
      change (if index.val < length then index.val
        else if index.val < length + length then width + (index.val - length)
        else width + width) < width + width + 1
      split_ifs <;> omega⟩

lemma suffixPosition_injective (length : Nat) (fits : length ≤ width) :
    Function.Injective (suffixPosition length fits) := by
  intro left right same
  have positions := congrArg Fin.val same
  have leftBound := left.isLt
  have rightBound := right.isLt
  change left.val < length + length + 1 at leftBound
  change right.val < length + length + 1 at rightBound
  apply Fin.ext
  dsimp only [suffixPosition] at positions
  split_ifs at positions <;> omega

def suffixSubsystem (length : Nat) (fits : length ≤ width) :
    WireSubsystem (MAU.Addition.TTK.overflowEncoding length) encoding where
  wires := ⟨suffixPosition length fits, suffixPosition_injective length fits⟩

/-- Every emitted native gate addresses only these existing physical systems. -/
def suffixIncrementGates (length : Nat) (fits : length ≤ width) : List (GateSpec encoding) :=
  (MAU.Addition.HRS.controlledBorrowedIncrementGates length).map
    ((suffixSubsystem length fits).placeGate (source_onto length) encoding_onto)

def suffixIncrementProgram (length : Nat) (fits : length ≤ width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (suffixIncrementGates length fits)

/-- The actual HRS increment acts on its selected two-word subsystem and retains the complement. -/
def suffixIncrementStep (length : Nat) (fits : length ≤ width) (state : Registers) : Registers :=
  ((suffixSubsystem length fits).full (source_onto length) encoding_onto).step
    (fun pair => (MAU.Addition.HRS.controlledBorrowedIncrementOutput pair.1, pair.2)) state

lemma suffixIncrementGates_step (length : Nat) (fits : length ≤ width) (state : Registers) :
    stepList (suffixIncrementGates length fits) state = suffixIncrementStep length fits state := by
  simpa only [suffixIncrementGates, suffixIncrementStep,
    MAU.Addition.HRS.hrsControlledBorrowedIncrement_step] using
      (suffixSubsystem length fits).placeGates_step (source_onto length) encoding_onto
        (MAU.Addition.HRS.controlledBorrowedIncrementGates length) state

/-- Exact phases and every borrowed bit are inherited from the actual HRS program. -/
lemma suffixIncrement_realizes (length : Nat) (fits : length ≤ width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (suffixIncrementProgram length fits) environment
      (suffixIncrementStep length fits) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (suffixIncrementGates_step length fits) environment

lemma suffixIncrement_events (length : Nat) (fits : length ≤ width) :
    (suffixIncrementGates length fits).map (event .empty) =
      (MAU.Addition.HRS.controlledBorrowedIncrementGates length).map (event .empty) := by
  simp only [suffixIncrementGates, List.map_map]
  apply List.map_congr_left
  intro gate _present
  exact (suffixSubsystem length fits).placeGate_event (source_onto length) encoding_onto .empty gate

lemma suffixIncrement_eventCost (length : Nat) (fits : length ≤ width) :
    (suffixIncrementProgram length fits).eventCost =
      (MAU.Addition.HRS.controlledBorrowedIncrementProgram length).eventCost := by
  rw [suffixIncrementProgram, MAU.Addition.HRS.controlledBorrowedIncrementProgram,
    programList_eventCost, programList_eventCost, suffixIncrement_events]

/-- The actual selected-word increment uses two CNOTs per borrowed bit. -/
lemma suffixIncrement_cnot_count (length : Nat) (fits : length ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (suffixIncrementProgram length fits).eventCost = 2 * length := by
  rw [suffixIncrement_eventCost, MAU.Addition.HRS.hrsControlledBorrowedIncrement_cnot_count]

/-- Every lower control, borrowed-wire repair and inverse addition is included. -/
lemma suffixIncrement_toffoli_count (length : Nat) (fits : length ≤ width)
    (atLeastTwo : 2 ≤ length) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (suffixIncrementProgram length fits).eventCost = 26 * length - 28 := by
  rw [suffixIncrement_eventCost, MAU.Addition.HRS.hrsControlledBorrowedIncrement_toffoli_count]
  omega

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.ModularAddition
