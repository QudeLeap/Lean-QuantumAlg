/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Length.Alignment
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Permutation.Barrel.Binary

/-!
# Native counts and duration of the actual terminal readout alignment

The complete metadata barrel pays all common-control Fredkin stages.
Only the divisor source has the extra public rotation; its unconditional
three-CNOT exchanges are charged separately. No fresh quantum system or
parallelization of shared-control instructions is assumed.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment

noncomputable section

open EncodedBit LengthCoordinates

private lemma barrel_resources (width : Nat) (field : Field) (first : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (GateSpec.programList (QubitLayout.canonical _) .empty
          (barrelGates width field first)).eventCost ≤ (width + 3) * width.size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (GateSpec.programList (QubitLayout.canonical _) .empty
          (barrelGates width field first)).eventCost ≤ 2 * (width + 3) * width.size ∧
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (barrelGates width field first)).evaluatedEventDepth Resource.Event.quantumDuration ≤
          3 * (width + 3) * width.size :=
  (ArithmeticAlignment.barrel width first (metadataField field)).binary_resources
    (permutation width field) (QubitLayout.canonical _) .empty

/-- Extra paid public exchanges occur only in the divisor source direction. -/
def publicBudget (width : Nat) (field : Field) : Nat :=
  if field = .divisor then 3 * (width + 3) else 0

private lemma public_resources (width : Nat) (field : Field) (first : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (GateSpec.programList (QubitLayout.canonical _) .empty
          (publicGates width field first)).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (GateSpec.programList (QubitLayout.canonical _) .empty
          (publicGates width field first)).eventCost ≤ publicBudget width field ∧
      (GateSpec.programList (QubitLayout.canonical _) .empty
        (publicGates width field first)).evaluatedEventDepth Resource.Event.quantumDuration ≤
          publicBudget width field := by
  cases field with
  | coefficient => simp [publicGates, publicBudget, GateSpec.programList]
  | divisor =>
      exact (ArithmeticRotation.frame width first (SharedEEA.controlBit width)
        (by rw [SharedEEA.controlBit_wire]; omega)).uncontrolled_resources
          (QubitLayout.canonical _) .empty (finRotate (width + 3))

/-- These are bounds on the same actual native program, including its extra paid rotation. -/
lemma program_resources (width : Nat) (field : Field) (first : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program width field first).eventCost ≤ (width + 3) * width.size ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width field first).eventCost ≤
          2 * (width + 3) * width.size + publicBudget width field ∧
      (program width field first).evaluatedEventDepth Resource.Event.quantumDuration ≤
        3 * (width + 3) * width.size + publicBudget width field := by
  have barrel := barrel_resources width field first
  have extra := public_resources width field first
  constructor
  · have base := barrel.1
    have load := extra.1
    rw [GateSpec.programList_toffoli_count_eq_sum] at base load
    rw [program, GateSpec.programList_toffoli_count_eq_sum, gates, List.map_append,
      List.sum_append, load, Nat.add_zero]
    exact base
  constructor
  · have base := barrel.2.1
    have load := extra.2.1
    rw [GateSpec.programList_cnot_count_eq_sum] at base load
    rw [program, GateSpec.programList_cnot_count_eq_sum, gates, List.map_append,
      List.sum_append]
    exact Nat.add_le_add base load
  · have base := barrel.2.2
    have load := extra.2.2
    rw [GateSpec.programList_quantumTime] at base load
    rw [program, GateSpec.programList_quantumTime, gates, List.length_append]
    exact Nat.add_le_add base load

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.LengthAlignment
