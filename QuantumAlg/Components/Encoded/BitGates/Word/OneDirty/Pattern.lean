/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.MultiControl
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Exact pattern equality with one arbitrary restored work bit

A fixed pattern selects negative source controls by actual X masks. The
existing arbitrary-work conjunction then toggles the output, and the
literal inverse masks restore all source bits. The complete encoded
state is unchanged apart from that exact predicate-controlled output
flip. The one borrowed work bit has no initialization or separation
requirement [G17, paper.tex:278-293].

The pattern is a compile-time finite selector parameter; no unknown
input value is prepared or supplied by a classical execution channel.
The actual gate count includes every mask and every conjunction gate.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}

/-- Equality with a fixed pattern on the actual complete source bit coordinates. -/
abbrev PatternMatches (layout : OneDirtyLayout (encoding := encoding) controls)
    (expected : Fin controls → Bool) (state : Data) : Prop :=
  ∀ index, (layout.source.bit index).get state = expected index

/-- Only zero pattern bits need actual X masks before an all-ones conjunction. -/
def patternMaskIndices (expected : Fin controls → Bool) : List (Fin controls) :=
  (List.ofFn fun index : Fin controls => index).filter fun index => !expected index

private theorem patternMaskIndices_nodup (expected : Fin controls → Bool) :
    (patternMaskIndices expected).Nodup :=
  (List.nodup_ofFn_ofInjective (fun _ _ same => same)).filter _

private theorem patternMaskIndices_member (expected : Fin controls → Bool)
    (index : Fin controls) :
    decide (index ∈ patternMaskIndices expected) = !expected index := by
  have allIndices : index ∈ (List.ofFn fun index : Fin controls => index) :=
    List.mem_ofFn.mpr ⟨index, rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, patternMaskIndices, List.mem_filter, allIndices, true_and]

variable (layout : OneDirtyLayout (encoding := encoding) controls)

/-- Literal X gates on the negative-control source positions. -/
def patternMaskGates (expected : Fin controls → Bool) : List (GateSpec encoding) :=
  (patternMaskIndices expected).map fun index => .x (layout.source.bit index)

private theorem patternMask_step (expected : Fin controls → Bool) (state : Data) :
    GateSpec.stepList (layout.patternMaskGates expected) state =
      xorConstantIndicesStep layout.source (patternMaskIndices expected) state := by
  rw [patternMaskGates, GateSpec.stepList_eq_foldl, List.foldl_map]
  rfl

private theorem patternMask_get (expected : Fin controls → Bool) (state : Data)
    (index : Fin controls) :
    (layout.source.bit index).get (GateSpec.stepList (layout.patternMaskGates expected) state) =
      ((layout.source.bit index).get state ^^ !expected index) := by
  rw [patternMask_step, xorConstantIndicesStep_get_target _ _
    (patternMaskIndices_nodup expected) index
    (fun other different same => different (layout.source_injective same)),
    patternMaskIndices_member]

private theorem masked_all_iff (expected : Fin controls → Bool) (state : Data) :
    (∀ index, (layout.source.bit index).get
      (GateSpec.stepList (layout.patternMaskGates expected) state) = true) ↔
        layout.PatternMatches expected state := by
  apply forall_congr'
  intro index
  rw [patternMask_get]
  cases (layout.source.bit index).get state <;> cases expected index <;> decide

private theorem patternMask_disjoint_output (expected : Fin controls → Bool)
    (gate : GateSpec encoding) (present : gate ∈ layout.patternMaskGates expected) :
    GateSpec.bitDisjoint layout.output gate := by
  obtain ⟨index, _, rfl⟩ := List.mem_map.mp present
  exact layout.source_output_ne index

/-- Negative-control masks, actual arbitrary-work conjunction, and exact inverse masks. -/
def patternGates (expected : Fin controls → Bool) : List (GateSpec encoding) :=
  layout.patternMaskGates expected ++ layout.gates ++ (layout.patternMaskGates expected).reverse

/-- Exact complete pattern-selection action with all original source and arbitrary work restored. -/
theorem patternGates_step (expected : Fin controls → Bool) (state : Data) :
    GateSpec.stepList (layout.patternGates expected) state =
      if layout.PatternMatches expected state then layout.output.flip state else state := by
  rw [patternGates, GateSpec.stepList_append, GateSpec.stepList_append, gates_step]
  simp only [masked_all_iff]
  split
  · rw [GateSpec.stepList_flip_comm_of_bitDisjoint (layout.patternMaskGates expected).reverse
      layout.output (fun gate present => layout.patternMask_disjoint_output expected gate
        (List.mem_reverse.mp present)), GateSpec.stepList_reverse_stepList]
  · exact GateSpec.stepList_reverse_stepList (layout.patternMaskGates expected) state

/-- Flipping the actual output cannot change any of the actual pattern-source values. -/
theorem patternMatches_flip_output (expected : Fin controls → Bool) (state : Data) :
    layout.PatternMatches expected (layout.output.flip state) ↔
      layout.PatternMatches expected state := by
  apply forall_congr'
  intro index
  rw [get_flip_of_wire_ne layout.output (layout.source.bit index)
    (layout.source_output_ne index).symm]

/-- The literal reverse list has the same full-state predicate flip action. -/
theorem patternGates_reverse_step (expected : Fin controls → Bool) (state : Data) :
    GateSpec.stepList (layout.patternGates expected).reverse state =
      if layout.PatternMatches expected state then layout.output.flip state else state := by
  let toggled := if layout.PatternMatches expected state then layout.output.flip state else state
  have forward : GateSpec.stepList (layout.patternGates expected) toggled = state := by
    dsimp only [toggled]
    by_cases selected : layout.PatternMatches expected state
    · rw [if_pos selected, patternGates_step,
        if_pos ((layout.patternMatches_flip_output expected state).mpr selected), flip_flip]
    · rw [if_neg selected, patternGates_step, if_neg selected]
  calc
    GateSpec.stepList (layout.patternGates expected).reverse state =
        GateSpec.stepList (layout.patternGates expected).reverse
          (GateSpec.stepList (layout.patternGates expected) toggled) :=
      congrArg (GateSpec.stepList (layout.patternGates expected).reverse) forward.symm
    _ = toggled := GateSpec.stepList_reverse_stepList (layout.patternGates expected) toggled

/-- The existing borrowed bit keeps its actual value for every initial pattern and work value. -/
theorem patternGates_work_restored (expected : Fin controls → Bool) (state : Data) :
    layout.work.get (GateSpec.stepList (layout.patternGates expected) state) =
      layout.work.get state := by
  rw [patternGates_step]
  split
  · exact get_flip_of_wire_ne layout.output layout.work layout.work_output_ne.symm state
  · rfl

/-- The actual list realizes the complete predicate flip without discarded relative phase. -/
theorem patternGates_realizes (expected : Fin controls → Bool) :
    UnitaryCircuit.Realizes encoding (GateSpec.programList (layout.patternGates expected))
      (fun state => if layout.PatternMatches expected state
        then layout.output.flip state else state) :=
  GateSpec.realizesList_congrStep _ (layout.patternGates_step expected)

/-- Exact actual elementary length, including both source masks. -/
theorem patternGates_length (expected : Fin controls → Bool) :
    (layout.patternGates expected).length =
      2 * (patternMaskIndices expected).length + layout.gates.length := by
  simp only [patternGates, List.length_append, List.length_reverse,
    patternMaskGates, List.length_map]
  omega

/-- Each actual source bit contributes at most one gate to a mask. -/
theorem patternMaskIndices_length_le (expected : Fin controls → Bool) :
    (patternMaskIndices expected).length ≤ controls := by
  simpa only [patternMaskIndices, List.length_ofFn] using
    (List.length_filter_le (l := List.ofFn fun index : Fin controls => index)
      (p := fun index => !expected index))

/-- Linear actual elementary length holds uniformly, including an empty pattern. -/
theorem patternGates_length_le (expected : Fin controls → Bool) :
    (layout.patternGates expected).length ≤ 10 * controls + 1 := by
  rw [patternGates_length]
  have masks := patternMaskIndices_length_le expected
  have conjunction := layout.gates_length_le
  omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
