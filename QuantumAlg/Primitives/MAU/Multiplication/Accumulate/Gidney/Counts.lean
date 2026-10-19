/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.Gates
import all QuantumAlg.Primitives.MAU.Multiplication.Accumulate.Gidney.ControlPushdown

/-!
# Native single-qubit count of selected modular accumulation

Every modular offset is coherently selected by a source bit. The small-width
literal paths and the large-width comparison-control construction both emit
only CNOT and Toffoli gates. The latter uses the genuine zero-X bi-flip law
[G17, paper.tex:276-293,319-334].
-/

namespace QuantumAlg.MAU.Multiplication.Accumulate.Gidney

noncomputable section

open EncodedBit.GateSpec

private lemma canonicalStage_singleQubit_count (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (canonicalProgram extra modulus constant).eventCost = 0 := by
  rw [canonicalProgram, programList_x_count_eq_sum]
  simpa only [canonicalGates, ControlPushdown.xCount] using
    ControlPushdown.canonical_xCount extra modulus constant

/-- The actual canonical stage obeys its independently derived CNOT allowance. -/
lemma gidneyCanonicalStage_cnot_count_bound (extra : Nat)
    (modulus : Fin (2 ^ (extra + 3) + 1)) (constant : Fin (modulus.val + 1)) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
      (canonicalProgram extra modulus constant).eventCost ≤
        ControlPushdown.canonicalCnotBound (extra + 3) := by
  rw [canonicalProgram, programList_cnot_count_eq_sum]
  simpa only [canonicalGates, ControlPushdown.cCount] using
    ControlPushdown.canonical_cCount_bound extra modulus constant

/-- Every actual selected-add stage has zero single-qubit events. -/
lemma gidneyStage_singleQubit_count : (width : Nat) → (selected : Fin width) →
    (modulus : Fin (2 ^ width + 1)) → (constant : Fin (modulus.val + 1)) →
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (stageProgram width selected modulus constant).eventCost = 0
  | 0, selected, _, _ => Fin.elim0 selected
  | 1, selected, modulus, constant =>
      (gidneySmallStage_native_bounds 1 (by decide) selected modulus constant).1
  | 2, selected, modulus, constant =>
      (gidneySmallStage_native_bounds 2 (by decide) selected modulus constant).1
  | extra + 3, selected, modulus, constant => by
      change ResourcePool.count _ (placedStageProgram extra selected modulus constant).eventCost = 0
      rw [(gidneyPlacedStage_resources extra selected modulus constant (fun _ => 1)).1]
      exact canonicalStage_singleQubit_count extra modulus constant

private lemma accumulatePrefix_singleQubit_count (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
      (prefixProgram width modulus coefficient count within).eventCost = 0 := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change ResourcePool.count _ ((prefixProgram width modulus coefficient index (by omega)).seq
        (stageProgram width ⟨index, by omega⟩ modulus
          (Nat.FixedWidth.accumulateConstant modulus coefficient index))).eventCost = 0
      rw [UnitaryCircuit.seq_eventCost, ResourcePool.count_add,
        ih (by omega), gidneyStage_singleQubit_count, Nat.zero_add]

/-- The complete actual accumulator emits no X gates. -/
lemma gidneyAccumulateGates_xMultiplicity_sum (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    ((gates width modulus coefficient).map xMultiplicity).sum = 0 := by
  rw [← programList_x_count_eq_sum (QubitLayout.canonical _) .empty,
    programList_eventCost, gidneyAccumulateGates_eventCost]
  exact accumulatePrefix_singleQubit_count width modulus coefficient width (Nat.le_refl width)

end

end QuantumAlg.MAU.Multiplication.Accumulate.Gidney
