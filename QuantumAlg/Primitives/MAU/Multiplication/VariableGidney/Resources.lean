/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.Program
import all QuantumAlg.Components.Encoded.BitGates.Resources
import all QuantumAlg.Core.Base.Accounting.Support

/-!
# Independent native resources of three-word variable multiplication

Each first-input bit controls one literal MAC gate list. The small-width
branch emits one native gate per source gate; the larger-width branch uses
at most four native gates per source gate, borrowing only existing wires.
Every stage restores its borrowed work and retains both input words.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney

noncomputable section

open EncodedBit.GateSpec

/-- Independent numerical cap for one addressed MAC stage. -/
def stageEventBound (width : Nat) : Nat :=
  4 * (width * Accumulate.Gidney.stageEventBound width)

/-- Independent native-coordinate budget for one selected MAC. -/
def stageBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  stageEventBound width • primitiveAlphabet

/-- Independent coordinatewise budget for the complete bit-pair program. -/
def nativeBudget (width : Nat) : ResourcePool (.quantum AlgorithmGate.model .empty) :=
  width • stageBudget width

/-- Explicit native-event and serial unit-depth upper bound. -/
def eventBound (width : Nat) : Nat := width * stageEventBound width

/-- Every native single-qubit allowance in the variable multiplier comes from its stage pool. -/
lemma nativeBudget_singleQubit_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .singleQubit) (nativeBudget width) = eventBound width := by
  simp [nativeBudget, stageBudget, eventBound, primitiveAlphabet]

/-- The same independent stage cap applies to the CNOT coordinate. -/
lemma nativeBudget_cnot_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .cnot) (nativeBudget width) = eventBound width := by
  simp [nativeBudget, stageBudget, eventBound, primitiveAlphabet]

/-- The same independent stage cap applies to the Toffoli coordinate. -/
lemma nativeBudget_toffoli_count (width : Nat) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty)
      (.gate .toffoli) (nativeBudget width) = eventBound width := by
  simp [nativeBudget, stageBudget, eventBound, primitiveAlphabet]

/-- The 256-bit variable multiplier's independent cap at each native coordinate. -/
lemma eventBound_256 : eventBound 256 = 3096220532736 := by decide

/-- The literal controlled list satisfies the independent per-stage envelope. -/
lemma variableGidney_stageGates_length_bound (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (index : Fin width) :
    (stageGates width modulus index).length ≤ stageEventBound width := by
  have source := Accumulate.Gidney.gidneyAccumulateGates_length_bound
    width modulus (2 ^ index.val)
  by_cases small : width ≤ 1
  · simp only [stageGates, dif_pos small, List.length_map]
    unfold stageEventBound
    omega
  · simp only [stageGates, dif_neg small]
    have controlled := controlRightList_length_bound
      (BinaryLabelEncoding.finIdentityBit width) (bodyBits width)
      (inputBits_wire width) (bodyBits_wire width)
      (by change 5 ≤ width + (width + width); omega)
      (inputBit width index)
      (Accumulate.Gidney.gates width modulus (2 ^ index.val))
    unfold stageEventBound
    omega

/-- All emitted coordinates belong to the default-model native alphabet. -/
lemma variableGidney_stage_native_support (width : Nat)
    (modulus : Fin (2 ^ width + 1)) (index : Fin width)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (present : focus ∈ (stageProgram width modulus index).eventCost) :
    focus ∈ primitiveAlphabet :=
  programList_native_support _ (stageGates width modulus index) focus present

/-- The actual number of emitted native instructions obeys the stage cap. -/
lemma variableGidney_stage_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).eventCost.card ≤ stageEventBound width := by
  simp only [stageProgram, encoding, programList_eventCost_card]
  exact variableGidney_stageGates_length_bound width modulus index

/-- The same actual list gives the stage's exact serial unit depth. -/
lemma variableGidney_stage_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).evaluatedEventDepth (fun _ => 1) =
      (stageProgram width modulus index).eventCost.card := by
  simp only [stageProgram, encoding, programList_evaluatedEventDepth_unit,
    programList_eventCost_card]

/-- Every native coordinate has a separate independent upper bound. -/
lemma variableGidney_stage_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (index : Fin width) :
    (stageProgram width modulus index).eventCost ≤ stageBudget width :=
  ResourcePool.le_scaled_of_support_card_le _ _ _
    (variableGidney_stage_native_support width modulus index)
    (variableGidney_stage_count width modulus index)

lemma variableGidney_prefix_budget (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).eventCost ≤ count • stageBudget width := by
  induction count with
  | zero => exact le_of_eq (zero_nsmul _).symm
  | succ index ih =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).eventCost ≤ _
      rw [UnitaryCircuit.seq_eventCost, add_nsmul, one_nsmul]
      exact add_le_add (ih (by omega))
        (variableGidney_stage_budget width modulus ⟨index, by omega⟩)

lemma variableGidney_prefix_count (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).eventCost.card ≤
      count * stageEventBound width := by
  induction count with
  | zero => exact Nat.zero_le _
  | succ index ih =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).eventCost.card ≤ _
      rw [UnitaryCircuit.seq_eventCost, Multiset.card_add, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega))
        (variableGidney_stage_count width modulus ⟨index, by omega⟩)

lemma variableGidney_prefix_depth (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).evaluatedEventDepth (fun _ => 1) =
      (prefixProgram width modulus count within).eventCost.card := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).evaluatedEventDepth (fun _ => 1) =
          ((prefixProgram width modulus index (by omega)).seq
            (stageProgram width modulus ⟨index, by omega⟩)).eventCost.card
      rw [UnitaryCircuit.evaluatedEventDepth_seq, UnitaryCircuit.seq_eventCost,
        Multiset.card_add, ih, variableGidney_stage_depth]

/-- Complete circuit satisfies the independent default-model resource budget. -/
lemma variableGidney_native_budget (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost ≤ nativeBudget width :=
  variableGidney_prefix_budget width modulus width (Nat.le_refl width)

/-- The actual complete event count has the explicit polynomial upper bound. -/
lemma variableGidney_event_count (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).eventCost.card ≤ eventBound width :=
  variableGidney_prefix_count width modulus width (Nat.le_refl width)

/-- The actual sequential critical path counts the controlled native events. -/
lemma variableGidney_unit_depth (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (program width modulus).evaluatedEventDepth (fun _ => 1) ≤ eventBound width := by
  have depth := variableGidney_prefix_depth width modulus width (Nat.le_refl width)
  rw [program] at *
  exact depth.trans_le (variableGidney_event_count width modulus)

end

end QuantumAlg.MAU.Multiplication.VariableGidney
