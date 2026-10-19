/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.Gates
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Frame.Controlled

/-!
# Native controlled multiplication on the existing measured frame

The supplied control occupies the last position after the complete arithmetic
frame. Each source X becomes a CNOT, each source CNOT becomes a Toffoli, and
each source Toffoli becomes four Toffolis with an existing borrowed wire.
The frame includes enough positions at every width, and each borrowed wire
is restored for every initial value. No additional clean system is required.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame.Controlled

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open MAU.Multiplication ProductPlacement EncodedBit GateSpec

/-- The complete original frame followed by its supplied quantum control. -/
abbrev encoding := NativeFrameControl.encoding

private abbrev bits := NativeFrameControl.bits
private abbrev bits_wire := NativeFrameControl.nativeFrameControl_bits_wire
private abbrev control := NativeFrameControl.control
private abbrev capacity := NativeFrameControl.nativeFrameControl_capacity

private def originalGates (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    List (GateSpec (BinaryLabelEncoding.prod (frameEncoding width) BinaryLabelEncoding.bool)) :=
  (NativeProductFrame.gates width modulus).map (GateSpec.prodLeft BinaryLabelEncoding.bool)

private lemma originalGates_disjoint (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    ∀ gate, gate ∈ originalGates width modulus → bitDisjoint (control width) gate := by
  intro gate present
  obtain ⟨source, _, rfl⟩ := List.mem_map.mp present
  exact bitDisjoint_prodLeft_rightBit (frameEncoding width) BinaryLabelEncoding.bool
    BinaryLabelEncoding.boolBit source

private lemma originalGates_eventCost (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    (programList layout .empty (originalGates width modulus)).eventCost =
      (NativeProductFrame.program width modulus).eventCost := by
  have lifted := map_event_prodLeft (oracles := .empty) (left := frameEncoding width)
    BinaryLabelEncoding.bool (NativeProductFrame.gates width modulus)
  exact (programList_eventCost layout .empty (originalGates width modulus)).trans
    ((congrArg ResourcePool.ofList
      (lifted.trans (nativeProductFrame_gates_trace width modulus))).trans
      (UnitaryCircuit.ofList_eventTrace_eq_eventCost
        (NativeProductFrame.program width modulus)))

/-- Real native control expansion, with every borrowed position inside the original carrier. -/
def gates (width : Nat) (modulus : Fin (2 ^ width + 1)) : List (GateSpec (encoding width)) :=
  NativeFrameControl.positiveGates width (NativeProductFrame.gates width modulus)

/-- Both quantum sectors retain the supplied control and the entire arithmetic frame. -/
def step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width × Bool) : Frame width × Bool :=
  (if state.2 then NativeProductFrame.step width modulus state.1 else state.1, state.2)

/-- Exact all-label action also restores any temporarily borrowed history or arithmetic bit. -/
lemma nativeProductControlled_gates_step (width : Nat) (modulus : Fin (2 ^ width + 1))
    (state : Frame width × Bool) :
    stepList (gates width modulus) state = step width modulus state := by
  have lifted := stepList_prodLeft (left := frameEncoding width) BinaryLabelEncoding.bool
    (NativeProductFrame.gates width modulus) state
  have active : stepList (originalGates width modulus) state =
      (NativeProductFrame.step width modulus state.1, state.2) :=
    lifted.trans (congrArg (fun frame => (frame, state.2))
      (nativeProductFrame_gates_step width modulus state.1))
  refine (controlWithin_step (bits width) (bits_wire width) (capacity width)
    (control width) (originalGates width modulus) (originalGates_disjoint width modulus)
    state).trans ?_
  change (if state.2 then stepList (originalGates width modulus) state else state) = _
  rw [active]
  rcases state with ⟨original, selected⟩
  cases selected <;> rfl

/-- The literal native list executes on the supplied complete layout without allocating a wire. -/
def program (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit AlgorithmGate.model .empty layout.toQuantum :=
  programList layout .empty (gates width modulus)

/-- Exact coherent action includes the relative phase between both control sectors. -/
lemma nativeProductControlled_realizes (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    UnitaryCircuit.Realizes (layout := layout) (encoding width) (program width modulus layout)
      environment
      (step width modulus) :=
  realizesList_congrStep layout .empty _ (nativeProductControlled_gates_step width modulus)
    environment

/-- The control is the original final frame position, including at the smallest width. -/
lemma nativeProductControlled_control_position (width : Nat) :
    (control width).wire.val = (frameEncoding width).width := by
  change (frameEncoding width).width + 0 = _
  omega

/-- The actual emitted trace is the expanded native instruction sequence. -/
lemma nativeProductControlled_trace (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    (program width modulus layout).eventTrace = (gates width modulus).map (event .empty) :=
  programList_eventTrace layout .empty _

/-- Exact native multiplicities include all four Toffolis needed for arbitrary dirty work. -/
lemma nativeProductControlled_counts (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
        (program width modulus layout).eventCost = 0 ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
        (program width modulus layout).eventCost =
          ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .singleQubit)
            (NativeProductFrame.program width modulus).eventCost ∧
      ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
        (program width modulus layout).eventCost =
          ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .cnot)
            (NativeProductFrame.program width modulus).eventCost +
              4 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
                (NativeProductFrame.program width modulus).eventCost := by
  rw [← originalGates_eventCost width modulus layout]
  unfold program
  rw [programList_x_count_eq_sum layout .empty (gates width modulus),
    programList_cnot_count_eq_sum layout .empty (gates width modulus),
    programList_toffoli_count_eq_sum layout .empty (gates width modulus),
    programList_x_count_eq_sum layout .empty (originalGates width modulus),
    programList_cnot_count_eq_sum layout .empty (originalGates width modulus),
    programList_toffoli_count_eq_sum layout .empty (originalGates width modulus)]
  exact controlWithin_native_counts (bits width) (bits_wire width) (capacity width) (control width)
    (originalGates width modulus) (originalGates_disjoint width modulus)

/-- The actual length charges each source instruction's complete native control expansion. -/
lemma nativeProductControlled_length (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).length = ((originalGates width modulus).map dirtyControlCount).sum :=
  controlWithin_length (bits width) (bits_wire width) (capacity width) (control width)
    (originalGates width modulus) (originalGates_disjoint width modulus)

/-- Three extra native events per original Toffoli are the exact dirty-control overhead. -/
lemma nativeProductControlled_event_card (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    (program width modulus layout).eventCost.card =
      (NativeProductFrame.program width modulus).eventCost.card +
        3 * ResourcePool.count (model := .quantum AlgorithmGate.model .empty) (.gate .toffoli)
          (NativeProductFrame.program width modulus).eventCost := by
  have sourceCard := (programList_eventCost_card layout .empty
    (originalGates width modulus)).symm.trans
      (congrArg Multiset.card (originalGates_eventCost width modulus layout))
  have sourceToffoli := programList_toffoli_count_eq_sum layout .empty
    (originalGates width modulus)
  rw [originalGates_eventCost width modulus layout] at sourceToffoli
  have sourceLength := length_eq_multiplicity_sums (originalGates width modulus)
  have expandedLength := length_eq_multiplicity_sums (gates width modulus)
  have counts := controlWithin_native_counts (bits width) (bits_wire width) (capacity width)
    (control width) (originalGates width modulus) (originalGates_disjoint width modulus)
  change ((gates width modulus).map xMultiplicity).sum = 0 ∧
    ((gates width modulus).map cnotMultiplicity).sum =
      ((originalGates width modulus).map xMultiplicity).sum ∧
    ((gates width modulus).map toffoliMultiplicity).sum =
      ((originalGates width modulus).map cnotMultiplicity).sum +
        4 * ((originalGates width modulus).map toffoliMultiplicity).sum at counts
  change (programList layout .empty (gates width modulus)).eventCost.card = _
  rw [programList_eventCost_card layout .empty (gates width modulus)]
  rw [← sourceCard, sourceToffoli, expandedLength, counts.1, counts.2.1,
    counts.2.2]
  dsimp only [encoding] at sourceLength ⊢
  rw [sourceLength]
  omega

/-- All remaining resource coordinates have zero multiplicity outside the actual native alphabet. -/
lemma nativeProductControlled_count_zero (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width)
    (focus : Resource.Event (.quantum AlgorithmGate.model .empty))
    (outside : focus ∉ primitiveAlphabet) :
    ResourcePool.count focus (program width modulus layout).eventCost = 0 :=
  programList_count_zero_of_not_mem_primitiveAlphabet layout (gates width modulus) focus outside

/-- Gate-local control multiplies the unchanged independent product count by at most four. -/
lemma nativeProductControlled_length_bound (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    (gates width modulus).length ≤ 4 * VariableGidney.eventBound width := by
  have bound := controlWithin_length_bound (bits width) (bits_wire width) (capacity width)
    (control width) (originalGates width modulus) (originalGates_disjoint width modulus)
  have source := nativeProductFrame_gates_length_bound width modulus
  have originalLength : (originalGates width modulus).length =
      (NativeProductFrame.gates width modulus).length :=
    length_prodLeft (left := frameEncoding width) BinaryLabelEncoding.bool
      (NativeProductFrame.gates width modulus)
  exact bound.trans (Nat.mul_le_mul_left 4 (originalLength.le.trans source))

/-- Actual event count and serial unit depth use the same expanded list. -/
lemma nativeProductControlled_resources (width : Nat) (modulus : Fin (2 ^ width + 1))
    (layout : QubitLayout (encoding width).width) :
    (program width modulus layout).eventCost.card ≤ 4 * VariableGidney.eventBound width ∧
      (program width modulus layout).evaluatedEventDepth (fun _ => 1) ≤
        4 * VariableGidney.eventBound width := by
  simp only [program, programList_eventCost_card, programList_evaluatedEventDepth_unit]
  exact ⟨nativeProductControlled_length_bound width modulus,
    nativeProductControlled_length_bound width modulus⟩

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame.Controlled
