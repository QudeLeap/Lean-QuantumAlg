/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Doubling.Cleanup.Layout
import all QuantumAlg.Components.Encoded.BitGates.Dirty.Control

/-! # Native high-word comparison controlled by the actual original low target bit -/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup

noncomputable section

open QuantumAlg.EncodedBit GateSpec ModularAddition

def comparisonGates : List (GateSpec encoding) :=
  (MAU.Addition.HRS.carryGates highWidth comparisonConstant).map
    (comparisonSubsystem.placeGate high_onto encoding_onto)

def comparisonStep (state : Registers) : Registers :=
  (comparisonSubsystem.full high_onto encoding_onto).step
    (fun pair => (MAU.Addition.HRS.carryOutput highWidth comparisonConstant pair.1, pair.2))
    state

lemma doublingCleanupComparisonGates_step (state : Registers) :
    stepList comparisonGates state = comparisonStep state := by
  simpa only [comparisonGates, comparisonStep, MAU.Addition.HRS.hrsCarry_step] using
    comparisonSubsystem.placeGates_step high_onto encoding_onto
      (MAU.Addition.HRS.carryGates highWidth comparisonConstant) state

private lemma placed_gate_disjoint (observed : EncodedBit encoding)
    (outside : observed.wire ∉ Set.range comparisonSubsystem.wires)
    (gate : GateSpec (MAU.Addition.HRS.carryEncoding highWidth)) :
    bitDisjoint observed (comparisonSubsystem.placeGate high_onto encoding_onto gate) := by
  have different (bit : EncodedBit (MAU.Addition.HRS.carryEncoding highWidth)) :
      (comparisonSubsystem.placeBit high_onto encoding_onto bit).wire ≠ observed.wire := by
    rw [comparisonSubsystem.placeBit_wire high_onto encoding_onto]
    intro same
    exact outside ⟨bit.wire, same⟩
  cases gate with
  | x bit => exact different bit
  | cnot source target separated => exact ⟨different source, different target⟩
  | toffoli first second target fs ft st =>
      exact ⟨different first, different second, different target⟩

private lemma low_disjoint (gate : GateSpec encoding) (present : gate ∈ comparisonGates) :
    bitDisjoint targetLow gate := by
  obtain ⟨original, _present, rfl⟩ := List.mem_map.mp present
  exact placed_gate_disjoint targetLow low_outside original

private lemma work_disjoint (gate : GateSpec encoding) (present : gate ∈ comparisonGates) :
    bitDisjoint controlWork gate := by
  obtain ⟨original, _present, rfl⟩ := List.mem_map.mp present
  exact placed_gate_disjoint controlWork work_outside original

/-- Four-Toffoli lowering restores the original arbitrary source work bit at every use. -/
def selectedComparisonGates : List (GateSpec encoding) :=
  listWithDirtyControl targetLow controlWork comparisonGates low_disjoint work_disjoint
    low_work_ne

/-- Actual native control, with no initialization premise for any source bit. -/
lemma selectedComparisonGates_step (state : Registers) :
    stepList selectedComparisonGates state =
      if targetLow.get state then comparisonStep state else state := by
  rw [selectedComparisonGates, listWithDirtyControl_step, doublingCleanupComparisonGates_step]

private lemma low_reduction_ne : targetLow.wire ≠ reductionBit.wire := by
  intro same
  have positions := congrArg Fin.val same
  change width + (width - 1 - 0) = width + width at positions
  have positive : 0 < width := by decide
  omega

/-- Complement the upper-word overflow under the retained original low-bit control. -/
def cleanupGates : List (GateSpec encoding) :=
  selectedComparisonGates ++ [.cnot targetLow reductionBit low_reduction_ne]

def cleanupProgram : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical encoding.width).toQuantum :=
  programList (QubitLayout.canonical _) .empty cleanupGates

def cleanupStep : Registers → Registers := stepList cleanupGates

/-- Exact full-frame unitary realization retains arbitrary external Reference correlations. -/
lemma cleanup_realizes (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes encoding cleanupProgram environment cleanupStep :=
  realizesList (QubitLayout.canonical _) .empty cleanupGates environment

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Doubling.Cleanup
