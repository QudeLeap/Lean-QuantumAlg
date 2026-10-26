/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Arithmetic.Guard.Phase
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Counts

/-! # Exact native P-256 coordinates of the four original arithmetic phase predicates -/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard

noncomputable section

open EncodedBit

private lemma phase_counts (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((phaseGates width count.succ bound expected).map GateSpec.toffoliMultiplicity).sum =
        Word.OneDirtyLayout.gateCount (count.succ + 1) ∧
      ((phaseGates width count.succ bound expected).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((phaseGates width count.succ bound expected).map GateSpec.xMultiplicity).sum =
        2 * (Word.OneDirtyLayout.patternMaskIndices
          (Word.OneDirtyLayout.controlledPatternValues expected)).length := by
  unfold phaseGates Word.OneDirtyLayout.controlledPatternGates
  exact Word.OneDirtyLayout.patternGates_native_counts _ (by omega) _

private lemma divisor_counts (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((zeroDivisorGates width count.succ bound expected).map GateSpec.toffoliMultiplicity).sum =
        Word.OneDirtyLayout.gateCount (count.succ + width.size + 1) ∧
      ((zeroDivisorGates width count.succ bound expected).map GateSpec.cnotMultiplicity).sum = 0 ∧
      ((zeroDivisorGates width count.succ bound expected).map GateSpec.xMultiplicity).sum =
        2 * (Word.OneDirtyLayout.patternMaskIndices
          (Word.OneDirtyLayout.controlledPatternValues
            (Fin.append expected (fun _ : Fin width.size => false)))).length := by
  unfold zeroDivisorGates Word.OneDirtyLayout.controlledPatternGates
  exact Word.OneDirtyLayout.patternGates_native_counts _ (by omega) _

private lemma phase_toffoli_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((phaseGates width count.succ bound expected).map GateSpec.toffoliMultiplicity).sum =
      Word.OneDirtyLayout.gateCount (count.succ + 1) := (phase_counts width count bound expected).1

private lemma phase_cnot_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((phaseGates width count.succ bound expected).map GateSpec.cnotMultiplicity).sum = 0 :=
  (phase_counts width count bound expected).2.1

private lemma phase_x_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((phaseGates width count.succ bound expected).map GateSpec.xMultiplicity).sum =
      2 * (Word.OneDirtyLayout.patternMaskIndices
        (Word.OneDirtyLayout.controlledPatternValues expected)).length :=
  (phase_counts width count bound expected).2.2

private lemma divisor_toffoli_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((zeroDivisorGates width count.succ bound expected).map GateSpec.toffoliMultiplicity).sum =
      Word.OneDirtyLayout.gateCount (count.succ + width.size + 1) :=
  (divisor_counts width count bound expected).1

private lemma divisor_cnot_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((zeroDivisorGates width count.succ bound expected).map GateSpec.cnotMultiplicity).sum = 0 :=
  (divisor_counts width count bound expected).2.1

private lemma divisor_x_sum (width count : Nat) (bound : count.succ ≤ 3)
    (expected : Fin count.succ → Bool) :
    ((zeroDivisorGates width count.succ bound expected).map GateSpec.xMultiplicity).sum =
      2 * (Word.OneDirtyLayout.patternMaskIndices
        (Word.OneDirtyLayout.controlledPatternValues
          (Fin.append expected (fun _ : Fin width.size => false)))).length :=
  (divisor_counts width count bound expected).2.2

/-- Actual small native conjunction counts, including the complete nine-bit divisor test. -/
def p256_phaseToffoli (signed coefficient : Bool) : Nat :=
  if signed then if coefficient then 1 else 65
  else if coefficient then 30 else 270

/-- Both real negative-control masks are paid in each original phase/divisor pattern. -/
def p256_phaseSingleQubit (signed coefficient : Bool) : Nat :=
  if signed then if coefficient then 0 else 22
  else if coefficient then 6 else 82

/-- These counts evaluate the same literal small predicate word used by the actual source guard. -/
lemma p256_program_toffoli_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
      (program 256 signed coefficient).eventCost = p256_phaseToffoli signed coefficient := by
  rw [program, GateSpec.programList_toffoli_count_eq_sum]
  cases signed <;> cases coefficient <;>
    simp only [gates, signedGates, lowGates, nonzeroGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, phase_toffoli_sum, divisor_toffoli_sum] <;> decide

/-- Every retained-control conjunction has at least two controls and emits no CNOT. -/
lemma p256_program_cnot_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (program 256 signed coefficient).eventCost = 0 := by
  rw [program, GateSpec.programList_cnot_count_eq_sum]
  cases signed <;> cases coefficient <;>
    simp only [gates, signedGates, lowGates, nonzeroGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, phase_cnot_sum, divisor_cnot_sum]

/-- Exact single-qubit counts include all complete original negative phase and divisor masks. -/
lemma p256_program_singleQubit_count (signed coefficient : Bool) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (program 256 signed coefficient).eventCost = p256_phaseSingleQubit signed coefficient := by
  rw [program, GateSpec.programList_x_count_eq_sum]
  cases signed <;> cases coefficient <;>
    simp only [gates, signedGates, lowGates, nonzeroGates, Bool.false_eq_true, if_false, if_true,
      List.map_append, List.sum_append, phase_x_sum, divisor_x_sum] <;> decide

/-- The true small native duration is its actual Toffolis plus its actual mask X instructions. -/
lemma p256_program_quantumTime (signed coefficient : Bool) :
    (program 256 signed coefficient).evaluatedEventDepth Resource.Event.quantumDuration =
      p256_phaseToffoli signed coefficient + p256_phaseSingleQubit signed coefficient := by
  have native := GateSpec.primitiveEventCount_programList
    (layout := QubitLayout.canonical _) (oracles := .empty) (gates 256 signed coefficient)
  change GateSpec.primitiveEventCount (program 256 signed coefficient) = _ at native
  rw [GateSpec.primitiveEventCount, p256_program_toffoli_count, p256_program_cnot_count,
    p256_program_singleQubit_count] at native
  rw [program, GateSpec.programList_quantumTime, ← native]
  omega

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.ArithmeticGuard
