/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.ModularAddition.Suffix

/-!
# Native high-word increments controlled by the original target low bit

The selected high word excludes the original least significant target bit.
That original bit supplies the quantum control, while the original source
word supplies all dirty borrowing. The reduction flag remains outside this
selected subsystem. No physical wire is assigned to two virtual positions.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

/-- Place the high-word increment and its control on distinct original wires. -/
def evenSuffixPosition (length : Nat) (fits : length < width)
    (index : Fin (MAU.Addition.TTK.overflowEncoding length).width) : Fin encoding.width :=
  ⟨if index.val < length then index.val
    else if index.val < length + length then width + (index.val - length)
    else width + width - 1, by
      have bounded := index.isLt
      change index.val < length + length + 1 at bounded
      change (if index.val < length then index.val
        else if index.val < length + length then width + (index.val - length)
        else width + width - 1) < width + width + 1
      split_ifs <;> omega⟩

lemma evenSuffixPosition_injective (length : Nat) (fits : length < width) :
    Function.Injective (evenSuffixPosition length fits) := by
  intro left right same
  have positions := congrArg Fin.val same
  have leftBound := left.isLt
  have rightBound := right.isLt
  change left.val < length + length + 1 at leftBound
  change right.val < length + length + 1 at rightBound
  apply Fin.ext
  dsimp only [evenSuffixPosition] at positions
  split_ifs at positions <;> omega

def evenSuffixSubsystem (length : Nat) (fits : length < width) :
    WireSubsystem (MAU.Addition.TTK.overflowEncoding length) encoding where
  wires := ⟨evenSuffixPosition length fits, evenSuffixPosition_injective length fits⟩

/-- Every original dirty-bit restoration instruction is placed on the same subsystem. -/
def evenSuffixGates (length : Nat) (fits : length < width) : List (GateSpec encoding) :=
  (MAU.Addition.HRS.controlledBorrowedIncrementGates length).map
    ((evenSuffixSubsystem length fits).placeGate (ModularAddition.source_onto length)
      encoding_onto)

def evenSuffixProgram (length : Nat) (fits : length < width) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty (evenSuffixGates length fits)

/-- The literal selected action retains the complete unused physical complement. -/
def evenSuffixStep (length : Nat) (fits : length < width) (state : Registers) : Registers :=
  ((evenSuffixSubsystem length fits).full (ModularAddition.source_onto length)
    encoding_onto).step
    (fun pair => (MAU.Addition.HRS.controlledBorrowedIncrementOutput pair.1, pair.2)) state

lemma evenSuffixGates_step (length : Nat) (fits : length < width) (state : Registers) :
    stepList (evenSuffixGates length fits) state = evenSuffixStep length fits state := by
  simpa only [evenSuffixGates, evenSuffixStep,
    MAU.Addition.HRS.hrsControlledBorrowedIncrement_step] using
      (evenSuffixSubsystem length fits).placeGates_step (ModularAddition.source_onto length)
        encoding_onto (MAU.Addition.HRS.controlledBorrowedIncrementGates length) state

/-- The actual native action retains phases on the entire original frame. -/
lemma evenSuffix_realizes (length : Nat) (fits : length < width)
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding (evenSuffixProgram length fits) environment
      (evenSuffixStep length fits) :=
  realizesList_congrStep (QubitLayout.canonical _) .empty _
    (evenSuffixGates_step length fits) environment

lemma evenSuffix_events (length : Nat) (fits : length < width) :
    (evenSuffixGates length fits).map (event .empty) =
      (MAU.Addition.HRS.controlledBorrowedIncrementGates length).map (event .empty) := by
  simp only [evenSuffixGates, List.map_map]
  apply List.map_congr_left
  intro gate _present
  exact (evenSuffixSubsystem length fits).placeGate_event
    (ModularAddition.source_onto length) encoding_onto .empty gate

/-- The selected low-bit control is actual native lowering, including all borrowed repairs. -/
lemma evenSuffix_eventCost (length : Nat) (fits : length < width) :
    (evenSuffixProgram length fits).eventCost =
      (MAU.Addition.HRS.controlledBorrowedIncrementProgram length).eventCost := by
  rw [evenSuffixProgram, MAU.Addition.HRS.controlledBorrowedIncrementProgram,
    programList_eventCost, programList_eventCost, evenSuffix_events]

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling
