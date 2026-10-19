/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Resources

/-!
# Literal instructions of the three-word variable product

Concatenation exposes the same stage instructions in their original order.
Both the complete basis action and the ordered native trace agree with the
existing composed program, permitting subsequent physical gate control.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open EncodedBit GateSpec Nat.FixedWidth

/-- The literal first-input stages, in increasing bit order. -/
def prefixGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (count : Nat) → count ≤ width → List (GateSpec
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity width)
        (Accumulate.Gidney.encoding width)))
  | 0, _ => []
  | index + 1, within => prefixGates width modulus index (by omega) ++
      stageGates width modulus ⟨index, by omega⟩

/-- Every source label, including both unchanged inputs, has the original prefix action. -/
lemma variableGidney_prefixGates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) (state : Registers width) :
    stepList (prefixGates width modulus count within) state =
      prefixOutput modulus count state := by
  induction count with
  | zero => rfl
  | succ index ih =>
      rw [prefixGates, stepList_append, ih (by omega), variableGidney_stageGates_step]
      rcases state with ⟨first, second, target⟩
      change (first, if first.val.testBit index then
        (second, accumulateWordPrefix modulus (2 ^ index) second
          (variableWordPrefix modulus first second target index) width)
        else (second, variableWordPrefix modulus first second target index)) =
        (first, second, if first.val.testBit index then
          accumulateWordPrefix modulus (2 ^ index) second
            (variableWordPrefix modulus first second target index) width
          else variableWordPrefix modulus first second target index)
      split_ifs <;> rfl

/-- Flattening retains every emitted instruction in the exact execution order. -/
lemma variableGidney_prefixGates_trace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixGates width modulus count within).map (event .empty) =
      (prefixProgram width modulus count within).eventTrace := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change ((prefixGates width modulus index (by omega) ++
        stageGates width modulus ⟨index, by omega⟩).map (event .empty)) =
          ((prefixProgram width modulus index (by omega)).seq
            (stageProgram width modulus ⟨index, by omega⟩)).eventTrace
      rw [List.map_append, ih (by omega), UnitaryCircuit.seq_eventTrace]
      exact congrArg (fun trace =>
        (prefixProgram width modulus index (by omega)).eventTrace ++ trace)
        (programList_eventTrace (QubitLayout.canonical (encoding width).width) .empty
          (stageGates width modulus ⟨index, by omega⟩)).symm

/-- All actual native instructions of the complete three-word product. -/
def gates (width : Nat) (modulus : Fin (2 ^ width + 1)) : List (GateSpec (encoding width)) :=
  prefixGates width modulus width (Nat.le_refl width)

/-- Exact all-label action of the complete literal instruction list. -/
lemma variableGidney_gates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Registers width) :
    stepList (gates width modulus) state = prefixOutput modulus width state :=
  variableGidney_prefixGates_step width modulus width (Nat.le_refl width) state

/-- The complete list and existing program have identical ordered native traces. -/
lemma variableGidney_gates_trace (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).map (event .empty) = (program width modulus).eventTrace :=
  variableGidney_prefixGates_trace width modulus width (Nat.le_refl width)

/-- Exposing the list does not alter any coordinate of the actual resource pool. -/
lemma variableGidney_gates_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    ResourcePool.ofList ((gates width modulus).map (event .empty)) =
      (program width modulus).eventCost := by
  rw [variableGidney_gates_trace, UnitaryCircuit.ofList_eventTrace_eq_eventCost]

/-- The original independent product bound applies to its literal instructions. -/
lemma variableGidney_gates_length_bound (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).length ≤ eventBound width := by
  have count := congrArg Multiset.card (variableGidney_gates_eventCost width modulus)
  simp only [ResourcePool.ofList, Multiset.coe_card, List.length_map] at count
  rw [count]
  exact variableGidney_event_count width modulus

end

end QuantumAlg.MAU.Multiplication.VariableGidney
