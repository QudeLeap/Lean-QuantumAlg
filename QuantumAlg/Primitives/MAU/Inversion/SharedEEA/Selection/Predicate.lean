/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Selection.Layout
import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Native.Predicate
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor

/-!
# Native equality predicates for the dynamic Sign exchange

Each selector compares the actual coefficient/quotient length bits and
both actual phases with one finite, fixed pattern. The pattern is a
compile-time selector parameter; no input-dependent value is prepared or
passed in from a classical execution channel. The actual X masks surround
the verified arbitrary-work zero test and are reversed completely.

Only Ctrl is xored with the exact equality predicate. Both shared words,
every length and phase, and all other correlations are retained by the
full-register equation. The same statement applies to the reversed native
list, even after unrelated Work1/Sign values have changed. The source
dynamic exchange is [LYL+26, sec_EEA/sub_opt.tex:52-59]; this explicit
equality decomposition is the circuit refinement proved here.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.SelectionPredicate

noncomputable section

open EncodedBit SelectionLayout NativePredicate

/-- A fixed selector pattern over the complete actual length/phase readout. -/
abbrev Pattern (width : Nat) := Fin (2 * width.size + 2) → Bool

/-- The selected source coordinates must equal every fixed pattern bit. -/
abbrev Matches {width : Nat} (expected : Pattern width) (state : Registers width) : Prop :=
  ∀ index, ((layout width).source.bit index).get state = expected index

/-- The exact equality value is xored into the existing Ctrl. -/
def condition {width : Nat} (expected : Pattern width) (state : Registers width) : Bool :=
  decide (Matches expected state)

/-- Every set pattern bit produces one actual source X in its physical source order. -/
def maskIndices (width : Nat) (expected : Pattern width) : List (Fin (2 * width.size + 2)) :=
  (List.ofFn fun index : Fin (2 * width.size + 2) => index).filter expected

private theorem maskIndices_nodup (width : Nat) (expected : Pattern width) :
    (maskIndices width expected).Nodup :=
  (List.nodup_ofFn_ofInjective (fun _ _ same => same)).filter _

private theorem maskIndices_member (width : Nat) (expected : Pattern width)
    (index : Fin (2 * width.size + 2)) :
    decide (index ∈ maskIndices width expected) = expected index := by
  have allIndices : index ∈ (List.ofFn fun index : Fin (2 * width.size + 2) => index) :=
    List.mem_ofFn.mpr ⟨index, rfl⟩
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq, maskIndices, List.mem_filter, allIndices, true_and]

/-- The actual X-mask list, using only the retained source coordinates. -/
def maskGates (width : Nat) (expected : Pattern width) : List (GateSpec (encoding width)) :=
  (maskIndices width expected).map fun index => .x ((layout width).source.bit index)

private theorem maskStep_eq (width : Nat) (expected : Pattern width) (state : Registers width) :
    GateSpec.stepList (maskGates width expected) state =
      Word.xorConstantIndicesStep (layout width).source (maskIndices width expected) state := by
  rw [maskGates, GateSpec.stepList_eq_foldl, List.foldl_map]
  rfl

private theorem mask_get (width : Nat) (expected : Pattern width)
    (state : Registers width) (index : Fin (2 * width.size + 2)) :
    ((layout width).source.bit index).get (GateSpec.stepList (maskGates width expected) state) =
      (((layout width).source.bit index).get state ^^ expected index) := by
  rw [maskStep_eq, Word.xorConstantIndicesStep_get_target _ _ (maskIndices_nodup width expected)
    index (fun other different => (layout width).source_source_ne other index different),
    maskIndices_member]

private theorem masked_zero_iff (width : Nat) (expected : Pattern width)
    (state : Registers width) :
    (∀ index, ((layout width).source.bit index).get
      (GateSpec.stepList (maskGates width expected) state) = false) ↔ Matches expected state := by
  apply forall_congr'
  intro index
  rw [mask_get]
  cases ((layout width).source.bit index).get state <;> cases expected index <;> decide

private theorem mask_disjoint_output (width : Nat) (expected : Pattern width)
    (gate : GateSpec (encoding width)) (present : gate ∈ maskGates width expected) :
    GateSpec.bitDisjoint (layout width).output gate := by
  obtain ⟨index, _present, rfl⟩ := List.mem_map.mp present
  exact (layout width).source_output_ne index

/-- Actual source masks, borrowed-work zero test, and complete inverse source masks. -/
def gates (width : Nat) (expected : Pattern width) : List (GateSpec (encoding width)) :=
  maskGates width expected ++ Word.ZeroTestLayout.borrowedZeroGates (layout width) ++
    (maskGates width expected).reverse

private theorem gates_step_if (width : Nat) (expected : Pattern width) (state : Registers width) :
    GateSpec.stepList (gates width expected) state =
      if Matches expected state then (layout width).output.flip state else state := by
  rw [gates, GateSpec.stepList_append, GateSpec.stepList_append,
    Word.ZeroTestLayout.borrowedZeroGates_step]
  simp only [masked_zero_iff]
  split
  · rw [GateSpec.stepList_flip_comm_of_bitDisjoint (maskGates width expected).reverse
      (layout width).output (fun gate present => mask_disjoint_output width expected gate
        (List.mem_reverse.mp present)), GateSpec.stepList_reverse_stepList]
  · exact GateSpec.stepList_reverse_stepList (maskGates width expected) state

/-- Full actual equality computation restores arbitrary source and work, changing only Ctrl. -/
theorem gates_step (width : Nat) (expected : Pattern width) (state : Registers width) :
    GateSpec.stepList (gates width expected) state = xorControl (condition expected state) state :=
  (gates_step_if width expected state).trans
    (NativePredicate.conditional_flip_xor (Matches expected state) state)

private theorem condition_xorControl (width : Nat) (expected : Pattern width)
    (value : Bool) (state : Registers width) :
    condition expected (xorControl value state) = condition expected state := by
  have retained : ∀ index, ((layout width).source.bit index).get (xorControl value state) =
      ((layout width).source.bit index).get state := by
    intro index
    rw [layout_source_get, layout_source_get, sourceBit_get, sourceBit_get]
    rfl
  simp only [condition, Matches, retained]

/-- The literal reverse predicate has the same xor action for arbitrary incoming work and Ctrl. -/
theorem reverse_step (width : Nat) (expected : Pattern width) (state : Registers width) :
    GateSpec.stepList (gates width expected).reverse state =
      xorControl (condition expected state) state := by
  let toggled := xorControl (condition expected state) state
  have forward : GateSpec.stepList (gates width expected) toggled = state := by
    rw [gates_step]
    change xorControl (condition expected (xorControl (condition expected state) state))
      (xorControl (condition expected state) state) = state
    rw [condition_xorControl, xorControl_twice]
  calc
    GateSpec.stepList (gates width expected).reverse state =
        GateSpec.stepList (gates width expected).reverse
          (GateSpec.stepList (gates width expected) toggled) :=
      congrArg (GateSpec.stepList (gates width expected).reverse) forward.symm
    _ = toggled := GateSpec.stepList_reverse_stepList (gates width expected) toggled

/-- Compile exactly the equality list used in the full-register proof. -/
def program (width : Nat) (expected : Pattern width) :
    UnitaryCircuit (Qubits (encoding width).width) := GateSpec.programList (gates width expected)

/-- Exact all-label equality-predicate realization with no discarded relative phase. -/
theorem program_realizes (width : Nat) (expected : Pattern width) :
    UnitaryCircuit.Realizes (encoding width) (program width expected)
      (fun state => xorControl (condition expected state) state) :=
  GateSpec.realizesList_congrStep _ (gates_step width expected)

/-- Exact count of every source mask and every native borrowed-work zero-test event. -/
theorem gates_length (width : Nat) (expected : Pattern width) :
    (gates width expected).length =
      2 * (maskIndices width expected).length + gateCount (2 * width.size) := by
  have testCount := Word.ZeroTestLayout.borrowedZeroGates_length (layout width)
  change (Word.ZeroTestLayout.borrowedZeroGates (layout width)).length =
    gateCount (2 * width.size) at testCount
  simp only [gates, List.length_append, List.length_reverse, maskGates, List.length_map, testCount]
  omega

/-- The mask occurrence bound is derived from its actual finite source enumeration. -/
theorem maskIndices_length_le (width : Nat) (expected : Pattern width) :
    (maskIndices width expected).length ≤ 2 * width.size + 2 := by
  simpa only [maskIndices, List.length_ofFn] using
    (List.length_filter_le (l := List.ofFn fun index : Fin (2 * width.size + 2) => index)
      (p := expected))

/-- Unit event depth counts the very same complete native list. -/
theorem program_unitDepth (width : Nat) (expected : Pattern width) :
    (program width expected).evaluatedEventDepth (fun _ => 1) =
      2 * (maskIndices width expected).length + gateCount (2 * width.size) := by
  rw [program, GateSpec.programList_evaluatedEventDepth_unit, gates_length]

end

end QuantumAlg.MAU.Inversion.SharedEEA.SelectionPredicate
