/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Stage
import all QuantumAlg.Util.Nat.FixedWidth.VariableWord.Accumulate

/-!
# Actual variable modular multiplication on three words

Both quantum inputs remain unchanged while their product is accumulated
into the third word. The static two-level binary scan is built from actual
controlled Gidney MAC programs [VBE95, 9511018.tex:333-367;
G17, paper.tex:319-334]. Its exact all-label action has no initialization
premise on any hidden quantum system, because there is no additional word.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open Nat.FixedWidth

/-- The independent complete output of an increasing-bit prefix. -/
def prefixOutput {width : Nat} (modulus : Fin (2 ^ width + 1)) (count : Nat)
    (state : Registers width) : Registers width :=
  (state.1, state.2.1, variableWordPrefix modulus state.1 state.2.1 state.2.2 count)

/-- Execute every selected first-input stage without allocating an additional system. -/
def prefixProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (count : Nat) → count ≤ width → UnitaryCircuit (Qubits (encoding width).width)
  | 0, _ => .identity (Qubits (encoding width).width) [] (by simp)
  | index + 1, within => .seq (prefixProgram width modulus index (by omega))
      (stageProgram width modulus ⟨index, by omega⟩)

/-- Every actual prefix realizes the exact three-word action on all basis labels. -/
theorem variableGidney_prefix_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    UnitaryCircuit.Realizes (encoding width) (prefixProgram width modulus count within)
      (prefixOutput modulus count) := by
  induction count with
  | zero =>
      apply (UnitaryCircuit.Realizes.identity (encoding width)).congrStep
      rintro ⟨first, second, target⟩
      rfl
  | succ index inductionHypothesis =>
      apply ((inductionHypothesis (by omega)).seq
        (variableGidney_stage_realizes width modulus ⟨index, by omega⟩)).congrStep
      rintro ⟨first, second, target⟩
      change (first, if first.val.testBit index then
        (second, accumulateWordPrefix modulus (2 ^ index) second
          (variableWordPrefix modulus first second target index) width)
        else (second, variableWordPrefix modulus first second target index)) =
        (first, second, if first.val.testBit index then
          accumulateWordPrefix modulus (2 ^ index) second
            (variableWordPrefix modulus first second target index) width
          else variableWordPrefix modulus first second target index)
      split_ifs <;> rfl

theorem variableGidney_prefix_physical (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).physical_idx ⊆
      List.range (encoding width).width := by
  induction count with
  | zero => exact List.nil_subset _
  | succ index inductionHypothesis =>
      exact UnitaryCircuit.seq_physical_idx_subset _ _ (inductionHypothesis (by omega))
        (variableGidney_stage_physical width modulus ⟨index, by omega⟩)

/-- The complete literal program retains the entire three-word physical carrier. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  .seq (prefixProgram width modulus width (Nat.le_refl width))
    (.identity (Qubits (encoding width).width) (List.range (encoding width).width)
      List.nodup_range)

/-- Exact all-label coherent correctness of the actual complete three-word program. -/
theorem variableGidney_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width modulus)
      (prefixOutput modulus width) := by
  apply ((variableGidney_prefix_realizes width modulus width (Nat.le_refl width)).seq
    (UnitaryCircuit.Realizes.identityAt (encoding width) (List.range (encoding width).width)
      List.nodup_range)).congrStep
  intro state
  rfl

/-- Every original quantum wire is retained, and there are exactly three input-sized words. -/
theorem variableGidney_physical (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).physical_idx = List.range (3 * width) := by
  have retained : (program width modulus).physical_idx = List.range (encoding width).width :=
    (variableGidney_prefix_physical width modulus width (Nat.le_refl width)).union_eq_right
  have count : (encoding width).width = 3 * width := by
    change width + (width + width) = 3 * width
    omega
  exact retained.trans (congrArg List.range count)

/-- Canonical accumulators receive the exact product while both quantum inputs are preserved. -/
theorem variableGidney_valid (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Registers width) (valid : state.2.2.val < modulus.val) :
    (prefixOutput modulus width state).1 = state.1 ∧
      (prefixOutput modulus width state).2.1 = state.2.1 ∧
      (prefixOutput modulus width state).2.2.val =
        (state.2.2.val + state.1.val * state.2.1.val) % modulus.val :=
  ⟨rfl, rfl, variableWordPrefix_full modulus state.1 state.2.1 state.2.2 valid⟩

end

end QuantumAlg.MAU.Multiplication.VariableGidney
