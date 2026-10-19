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

variable {environment : OracleModel.empty.Interpretation}

open Nat.FixedWidth

/-- The independent complete output of an increasing-bit prefix. -/
def prefixOutput {width : Nat} (modulus : Fin (2 ^ width + 1)) (count : Nat)
    (state : Registers width) : Registers width :=
  (state.1, state.2.1, variableWordPrefix modulus state.1 state.2.1 state.2.2 count)

/-- Execute every selected first-input stage without allocating an additional system. -/
def prefixProgram (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (count : Nat) → count ≤ width → UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum
  | 0, _ => UnitaryCircuit.identity AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum
  | index + 1, within => (prefixProgram width modulus index (by omega)).seq
      (stageProgram width modulus ⟨index, by omega⟩)

/-- Every actual prefix realizes the exact three-word action on all basis labels. -/
lemma variableGidney_prefix_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    UnitaryCircuit.Realizes (encoding width) (prefixProgram width modulus count within) environment
      (prefixOutput modulus count) := by
  induction count with
  | zero =>
      apply (UnitaryCircuit.Realizes.identityAt AlgorithmGate.model .empty
        (encoding width) (QubitLayout.canonical (encoding width).width) environment).congrStep
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

/-- The complete literal program retains the original three-word carrier. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  prefixProgram width modulus width (Nat.le_refl width)

/-- Exact all-label coherent correctness of the actual complete three-word program. -/
lemma variableGidney_realizes (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width modulus) environment
      (prefixOutput modulus width) :=
  variableGidney_prefix_realizes width modulus width (Nat.le_refl width)

/-- Every original quantum wire is retained, with exactly three input-sized words. -/
lemma variableGidney_interface (width : Nat) :
    (encoding width).width = 3 * width ∧
      (QubitLayout.canonical (encoding width).width).systemIdx = List.range (3 * width) :=
  variableGidney_stage_interface width

/-- Canonical accumulators receive the exact product while both quantum inputs are preserved. -/
lemma variableGidney_valid (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Registers width) (valid : state.2.2.val < modulus.val) :
    (prefixOutput modulus width state).1 = state.1 ∧
      (prefixOutput modulus width state).2.1 = state.2.1 ∧
      (prefixOutput modulus width state).2.2.val =
        (state.2.2.val + state.1.val * state.2.1.val) % modulus.val :=
  ⟨rfl, rfl, variableWordPrefix_full modulus state.1 state.2.1 state.2.2 valid⟩

end

end QuantumAlg.MAU.Multiplication.VariableGidney
