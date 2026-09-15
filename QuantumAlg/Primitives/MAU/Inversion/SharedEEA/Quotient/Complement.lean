/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor

/-!
# Actual phase-controlled complement of quotient length

The source chooses increment or decrement from Phase1
[LYL+26, sec_EEA/sub_opt.tex:52-59]. Complementing the target before and
after one increment gives decrement by an exact finite-word identity.
This owner implements each complement with one actual Phase1-controlled
CNOT per quotient bit and proves the complete register action. This
specific elementary decomposition is a refinement proved here, rather
than a gate list asserted to occur verbatim in the source.

Every other field, including the complete arbitrary Work1, Work2, shift,
and Ctrl, is retained. The width-zero case executes the empty native list.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.QuotientComplement

noncomputable section

open EncodedBit

private def source (width : Nat) : Word (encoding width) width.size :=
  ⟨fun _ => phase1Bit width⟩

private def target (width : Nat) : Word (encoding width) width.size :=
  ⟨quotientLengthBit width⟩

private theorem separate (width : Nat) (index : Fin width.size) :
    ((source width).bit index).wire ≠ ((target width).bit index).wire := by
  intro same
  have values := congrArg Fin.val same
  change (phase1Bit width).wire.val = (quotientLengthBit width index).wire.val at values
  rw [phase1Bit_wire, quotientLengthBit_wire] at values
  have within := index.isLt
  omega

private theorem distinct (width : Nat) (left right : Fin width.size) (different : left ≠ right) :
    ((target width).bit left).wire ≠ ((target width).bit right).wire := by
  intro same
  have values := congrArg Fin.val same
  change (quotientLengthBit width left).wire.val =
    (quotientLengthBit width right).wire.val at values
  rw [quotientLengthBit_wire, quotientLengthBit_wire] at values
  exact different (Fin.ext (by omega))

/-- One literal CNOT from the original Phase1 to every actual quotient position. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.xorIntoGates (source width) (target width) (separate width)

private def withoutQuotient {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength := 0#width.size }

private theorem gates_preserve_complement (width : Nat) (state : Registers width) :
    withoutQuotient (GateSpec.stepList (gates width) state) = withoutQuotient state :=
  Word.xorIntoStep_preserves_projection (source width) (target width) (separate width)
    withoutQuotient (fun _ _ => rfl) state

private theorem gates_quotient (width : Nat) (state : Registers width) :
    (GateSpec.stepList (gates width) state).quotientLength =
      if state.flags.first then ~~~state.quotientLength else state.quotientLength := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have entry := Word.xorIntoStep_get_target (source width) (target width) (separate width)
    ⟨index, within⟩ (fun other different => distinct width other _ different)
    (fun other => (separate width other).symm) state
  change (quotientLengthBit width ⟨index, within⟩).get (GateSpec.stepList (gates width) state) =
    ((quotientLengthBit width ⟨index, within⟩).get state ^^ state.flags.first) at entry
  rw [quotientLengthBit_get, quotientLengthBit_get] at entry
  cases selected : state.flags.first <;>
    simpa only [selected, Bool.false_eq_true, if_false, if_true, Bool.xor_false, Bool.xor_true,
      BitVec.getMsbD_not, within, decide_true, Bool.true_and] using entry

/-- The complete frame action changes only quotient bits selected by the retained Phase1. -/
def step {width : Nat} (state : Registers width) : Registers width :=
  { state with quotientLength :=
      if state.flags.first then ~~~state.quotientLength else state.quotientLength }

/-- Full actual CNOT-list correctness, without any assumptions on the remaining registers. -/
theorem gates_step (width : Nat) (state : Registers width) :
    GateSpec.stepList (gates width) state = step state := by
  let result := GateSpec.stepList (gates width) state
  calc
    result = { withoutQuotient result with quotientLength := result.quotientLength } := rfl
    _ = _ := by
      rw [gates_preserve_complement, gates_quotient]
      rfl

/-- Compile those actual CNOT gates at the original supplied quotient/Phase1 coordinates. -/
def program (width : Nat) : UnitaryCircuit (Qubits (encoding width).width) :=
  GateSpec.programList (gates width)

/-- Exact all-label realization of the same native complement circuit. -/
theorem program_realizes (width : Nat) :
    UnitaryCircuit.Realizes (encoding width) (program width) step :=
  GateSpec.realizesList_congrStep _ (gates_step width)

/-- Two complements restore every field, including the complete finite quotient word. -/
theorem step_twice {width : Nat} (state : Registers width) : step (step state) = state := by
  cases selected : state.flags.first <;>
    simp only [step, selected, Bool.false_eq_true, if_false, if_true, BitVec.not_not]

/-- Exact finite arithmetic identity used to select decrement with one native incrementer. -/
theorem complement_increment (width : Nat) (word : BitVec width) :
    ~~~(~~~word + 1) = word - 1 := by
  change ~~~(~~~word + 1#width) = word - 1#width
  rw [← BitVec.neg_eq_not_add, BitVec.not_eq_neg_add, BitVec.neg_neg]

/-- Every quotient bit contributes one actual CNOT occurrence, including unused control branches. -/
theorem program_eventTrace (width : Nat) :
    (program width).eventTrace =
      List.replicate width.size (.gate (.builtin "cnot")) := by
  rw [program, GateSpec.programList_eventTrace]
  simp only [gates, Word.xorIntoGates, List.map_ofFn, Function.comp_def, GateSpec.event,
    List.ofFn_const]

/-- The actual complement uses only the already allocated complete frame. -/
theorem program_physical_idx_subset (width : Nat) :
    (program width).physical_idx ⊆ List.range (encoding width).width :=
  GateSpec.programList_physical_idx_subset_range _

end

end QuantumAlg.MAU.Inversion.SharedEEA.QuotientComplement
