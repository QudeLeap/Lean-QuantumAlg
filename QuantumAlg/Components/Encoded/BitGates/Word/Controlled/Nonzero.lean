/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.Controlled.Pattern
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Pattern.Counts
import all QuantumAlg.Components.Encoded.BitGates.QuantumTime

/-!
# A retained control and a complete nonzero word

An actual control-to-output CNOT is followed by the existing controlled
zero-pattern circuit. Their output XOR is control AND word-nonzero. Every
source and the same arbitrary dirty work bit are restored on every label.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data} {controls : Nat}
variable (layout : OneDirtyLayout (encoding := encoding) controls) (control : EncodedBit encoding)
variable (sources : ∀ index, control.wire ≠ (layout.source.bit index).wire)
variable (output : control.wire ≠ layout.output.wire) (work : control.wire ≠ layout.work.wire)

/-- The predicate describes actual source bits and performs no runtime host computation. -/
def controlledNonzero (state : Data) : Bool :=
  control.get state && !decide (layout.PatternMatches (fun _ => false) state)

def controlledNonzeroStep (state : Data) : Data :=
  if layout.controlledNonzero control state then layout.output.flip state else state

/-- The emitted CNOT and masked conjunction use only the existing supplied systems. -/
def controlledNonzeroGates : List (GateSpec encoding) :=
  [.cnot control layout.output output] ++
    layout.controlledPatternGates control sources output work (fun _ => false)

lemma controlledNonzeroGates_step (state : Data) :
    GateSpec.stepList (layout.controlledNonzeroGates control sources output work) state =
      layout.controlledNonzeroStep control state := by
  rw [controlledNonzeroGates, GateSpec.stepList_append]
  change GateSpec.stepList
    (layout.controlledPatternGates control sources output work (fun _ => false))
      (cnotStep control layout.output state) = _
  rw [controlledPatternGates_step]
  have retained : control.get (cnotStep control layout.output state) = control.get state :=
    cnotStep_get_of_target_ne _ _ _ output.symm state
  have matched : layout.PatternMatches (fun _ => false) (cnotStep control layout.output state) ↔
      layout.PatternMatches (fun _ => false) state := by
    apply forall_congr'
    intro index
    rw [cnotStep_get_of_target_ne control layout.output (layout.source.bit index)
      (layout.source_output_ne index).symm]
  rw [retained]
  simp only [matched]
  unfold controlledNonzeroStep controlledNonzero
  cases active : control.get state
  · simp [cnotStep, active]
  · rw [if_pos rfl]
    by_cases zero : layout.PatternMatches (fun _ => false) state
    · rw [if_pos zero, decide_eq_true zero]
      change layout.output.flip (cnotStep control layout.output state) = state
      unfold cnotStep
      rw [active, if_pos rfl, flip_flip]
    · rw [if_neg zero, decide_eq_false zero]
      change cnotStep control layout.output state = layout.output.flip state
      unfold cnotStep
      rw [active, if_pos rfl]

include output in
lemma controlledNonzero_flip_output (state : Data) :
    layout.controlledNonzero control (layout.output.flip state) =
      layout.controlledNonzero control state := by
  unfold controlledNonzero
  simp only [get_flip_of_wire_ne layout.output control output.symm,
    layout.patternMatches_flip_output]

include output in
lemma controlledNonzeroStep_step (state : Data) :
    layout.controlledNonzeroStep control (layout.controlledNonzeroStep control state) = state := by
  unfold controlledNonzeroStep
  cases selected : layout.controlledNonzero control state
  · simp only [Bool.false_eq_true, if_false, selected]
  · rw [if_pos rfl, controlledNonzero_flip_output layout control output,
      selected, if_pos rfl, flip_flip]

/-- The literal inverse has the same total-label predicate action. -/
lemma controlledNonzeroGates_reverse_step (state : Data) :
    GateSpec.stepList (layout.controlledNonzeroGates control sources output work).reverse state =
      layout.controlledNonzeroStep control state := by
  have forward := layout.controlledNonzeroGates_step control sources output work
    (layout.controlledNonzeroStep control state)
  rw [controlledNonzeroStep_step layout control output] at forward
  exact (congrArg
    (GateSpec.stepList (layout.controlledNonzeroGates control sources output work).reverse)
    forward.symm).trans (GateSpec.stepList_reverse_stepList _ _)

/-- Every actual physical coordinate except the supplied output is unchanged. -/
lemma controlledNonzeroStep_other (observed : EncodedBit encoding)
    (outside : layout.output.wire ≠ observed.wire) (state : Data) :
    observed.get (layout.controlledNonzeroStep control state) = observed.get state := by
  unfold controlledNonzeroStep
  split
  · exact get_flip_of_wire_ne layout.output observed outside state
  · rfl

lemma controlledNonzeroStep_output (state : Data) :
    layout.output.get (layout.controlledNonzeroStep control state) =
      (layout.output.get state ^^ layout.controlledNonzero control state) := by
  unfold controlledNonzeroStep
  cases selected : layout.controlledNonzero control state <;>
    simp only [Bool.false_eq_true, if_false, if_true, get_flip_self,
      Bool.xor_false, Bool.xor_true]

lemma controlledNonzeroGates_realizes (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList physical oracles
        (layout.controlledNonzeroGates control sources output work)) environment
      (layout.controlledNonzeroStep control) :=
  GateSpec.realizesList_congrStep physical oracles _
    (layout.controlledNonzeroGates_step control sources output work) environment

lemma controlledNonzeroGates_reverse_realizes (physical : QubitLayout encoding.width)
    (oracles : OracleModel) (environment : oracles.Interpretation) :
    UnitaryCircuit.Realizes encoding
      (GateSpec.programList physical oracles
        (layout.controlledNonzeroGates control sources output work).reverse) environment
      (layout.controlledNonzeroStep control) :=
  GateSpec.realizesList_congrStep physical oracles _
    (layout.controlledNonzeroGates_reverse_step control sources output work) environment

private lemma controlledZeroMask_length :
    (patternMaskIndices (controlledPatternValues (fun _ : Fin controls => false))).length =
      controls := by
  unfold patternMaskIndices controlledPatternValues
  rw [List.ofFn_succ]
  change (List.filter (fun index : Fin (controls + 1) => !Fin.cases true (fun _ => false) index)
    (List.ofFn fun index : Fin controls => index.succ)).length = controls
  rw [List.filter_eq_self.mpr ?_, List.length_ofFn]
  intro index present
  obtain ⟨original, rfl⟩ := List.mem_ofFn.mp present
  rfl

lemma controlledNonzeroGates_native_counts (positive : 1 ≤ controls) :
    ((layout.controlledNonzeroGates control sources output work).map
      GateSpec.toffoliMultiplicity).sum = gateCount (controls + 1) ∧
      ((layout.controlledNonzeroGates control sources output work).map
        GateSpec.cnotMultiplicity).sum = 1 ∧
      ((layout.controlledNonzeroGates control sources output work).map
        GateSpec.xMultiplicity).sum = 2 * controls := by
  have actual := patternGates_native_counts
    (layout.controlledPatternLayout control sources output work) (by omega)
    (controlledPatternValues (fun _ => false))
  rw [controlledZeroMask_length] at actual
  refine ⟨?_, ?_, ?_⟩
  · simpa only [controlledNonzeroGates, controlledPatternGates, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, GateSpec.toffoliMultiplicity,
      Nat.add_zero, Nat.zero_add] using actual.1
  · simp only [controlledNonzeroGates, controlledPatternGates, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, GateSpec.cnotMultiplicity,
      Nat.add_zero, actual.2.1]
  · simpa only [controlledNonzeroGates, controlledPatternGates, List.map_append, List.sum_append,
      List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, GateSpec.xMultiplicity,
      Nat.add_zero, Nat.zero_add] using actual.2.2

lemma controlledNonzeroGates_length :
    (layout.controlledNonzeroGates control sources output work).length =
      2 * controls + gateCount (controls + 1) + 1 := by
  rw [controlledNonzeroGates, List.length_append, List.length_singleton,
    controlledPatternGates_length, gates_length, controlledZeroMask_length]
  omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
