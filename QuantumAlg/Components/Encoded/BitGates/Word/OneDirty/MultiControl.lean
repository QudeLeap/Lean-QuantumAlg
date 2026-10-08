/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Conjunction
import all QuantumAlg.Components.Encoded.BitGates.Word.OneDirty.Layout
import all QuantumAlg.Components.Encoded.BitGates.Basic
import all QuantumAlg.Components.Encoded.BitGates.GateSpec
import all QuantumAlg.Components.Encoded.Circuit

/-!
# Elementary multi-control X with one restored arbitrary work bit

Zero, one and two controls use one X, CNOT or Toffoli gate respectively.
Larger control sets use the actual balanced F, G, F, G construction. The
gate list acts on every encoded input, restores the external work bit and
all original controls, and has linear elementary length. The small cases
do not touch the work wire.
-/

namespace QuantumAlg.EncodedBit.Word.OneDirtyLayout

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}

/-- A literal elementary gate list at every control width. -/
def gates : {controls : Nat} → OneDirtyLayout (encoding := encoding) controls →
    List (GateSpec encoding)
  | 0, layout => [.x layout.output]
  | 1, layout => [.cnot (layout.source.bit 0) layout.output (layout.source_output_ne 0)]
  | 2, layout => [.toffoli (layout.source.bit 0) (layout.source.bit 1) layout.output
      (fun same => (by decide : (0 : Fin 2) ≠ 1) (layout.source_injective same))
      (layout.source_output_ne 0) (layout.source_output_ne 1)]
  | controls + 3, layout => layout.balancedGates (by omega)

variable {controls : Nat} (layout : OneDirtyLayout (encoding := encoding) controls)
variable (physical : QubitLayout encoding.width) (oracles : OracleModel)

/-- The exact complete encoded action xors the conjunction into the output at every width. -/
theorem gates_step (state : Data) :
    GateSpec.stepList layout.gates state =
      if ∀ index, (layout.source.bit index).get state = true
        then layout.output.flip state else state := by
  cases controls with
  | zero =>
    have allBits : ∀ index : Fin 0, (layout.source.bit index).get state = true :=
      fun index => Fin.elim0 index
    change layout.output.flip state = _
    rw [if_pos allBits]
  | succ controls =>
    cases controls with
    | zero =>
      have allBits : (∀ index : Fin 1, (layout.source.bit index).get state = true) ↔
          (layout.source.bit 0).get state = true := by
        constructor
        · intro present
          exact present 0
        · intro present index
          have same : index = 0 := Subsingleton.elim _ _
          simpa only [same] using present
      change (if (layout.source.bit 0).get state then layout.output.flip state else state) = _
      simp only [allBits]
    | succ controls =>
      cases controls with
      | zero =>
        have allBits : (∀ index : Fin 2, (layout.source.bit index).get state = true) ↔
            (layout.source.bit 0).get state = true ∧ (layout.source.bit 1).get state = true := by
          constructor
          · intro present
            exact ⟨present 0, present 1⟩
          · rintro ⟨first, second⟩ index
            fin_cases index
            · exact first
            · exact second
        change (if (layout.source.bit 0).get state && (layout.source.bit 1).get state
          then layout.output.flip state else state) = _
        simp only [Bool.and_eq_true_iff, allBits]
      | succ controls => exact layout.balancedGates_step (by omega) state

/-- Every other actual encoded wire keeps its complete value, including arbitrary dirty work. -/
theorem gates_get_of_output_ne (observed : EncodedBit encoding)
    (different : layout.output.wire ≠ observed.wire) (state : Data) :
    observed.get (GateSpec.stepList layout.gates state) = observed.get state := by
  rw [gates_step]
  split
  · exact get_flip_of_wire_ne layout.output observed different state
  · rfl

/-- The external borrowed work bit is restored without any initialization premise. -/
theorem gates_work_restored (state : Data) :
    layout.work.get (GateSpec.stepList layout.gates state) = layout.work.get state :=
  layout.gates_get_of_output_ne layout.work layout.work_output_ne.symm state

/-- Every original control is restored, including those temporarily borrowed by a subcall. -/
theorem gates_source_restored (state : Data) (index : Fin controls) :
    (layout.source.bit index).get (GateSpec.stepList layout.gates state) =
      (layout.source.bit index).get state :=
  layout.gates_get_of_output_ne (layout.source.bit index)
    (layout.source_output_ne index).symm state

/-- The actual elementary circuit realizes the exact all-input multi-control action. -/
theorem gates_realizes :
    UnitaryCircuit.Realizes encoding (GateSpec.programList physical oracles layout.gates)
      (fun state => if ∀ index, (layout.source.bit index).get state = true
        then layout.output.flip state else state) :=
  GateSpec.realizesList_congrStep physical oracles layout.gates layout.gates_step

/-- Below three controls the actual list contains just the corresponding elementary gate. -/
theorem gates_length_of_small (small : controls < 3) : layout.gates.length = 1 := by
  cases controls with
  | zero => rfl
  | succ controls =>
    cases controls with
    | zero => rfl
    | succ controls =>
      cases controls with
      | zero => rfl
      | succ controls => omega

/-- The larger cases use exactly the two copies of each balanced subcall. -/
theorem gates_length_of_large (large : 3 ≤ controls) :
    layout.gates.length =
      2 * ((if firstWidth controls - 2 = 0 then 1 else 4 * (firstWidth controls - 2)) +
        (if secondWidth controls - 1 = 0 then 1 else 4 * (secondWidth controls - 1))) := by
  cases controls with
  | zero => omega
  | succ controls =>
    cases controls with
    | zero => omega
    | succ controls =>
      cases controls with
      | zero => omega
      | succ controls => exact layout.balancedGates_length large

/-- Linear length bounds the literal elementary program at all control widths. -/
theorem gates_length_le : layout.gates.length ≤ 8 * controls + 1 := by
  by_cases small : controls < 3
  · rw [gates_length_of_small layout small]
    omega
  · have large : 3 ≤ controls := Nat.le_of_not_gt small
    rw [gates_length_of_large layout large]
    have actual := layout.balancedGates_length_le large
    rw [balancedGates_length] at actual
    omega

end

end QuantumAlg.EncodedBit.Word.OneDirtyLayout
