/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Layout
import all QuantumAlg.Components.Encoded.BitGates.Word.ConstantXor
import all QuantumAlg.Util.Nat.FixedWidth

/-!
# Reload the actual short-DLP seed after register reset

The source clean input has zero exponent words, the unit seed in its power
word and zero arithmetic auxiliary. This module loads that fixed basis label
using actual X gates on its set bits. Low integer bit indices are translated
to the existing physical big-endian wire order explicitly. The full register
is retained by a zero-event identity carrier, including at width zero.

This is a unitary component used after the actual reset proof. It performs no
new preparation or allocation and does not impose a clean-state premise on
an external caller. Its exact native count follows the literal gate list.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU

noncomputable section

open BinaryLabelEncoding
open EncodedBit.GateSpec

private def reloadBit (width : Nat) (bit : Fin width) : EncodedBit (finIdentity width) :=
  finIdentityBit width (WireAddress.littleEndianWire bit)

private def reloadWord (width : Nat) : EncodedBit.Word (finIdentity width) width :=
  ⟨reloadBit width⟩

private theorem reloadBit_get (width : Nat) (bit : Fin width) (state : Fin (2 ^ width)) :
    (reloadBit width bit).get state = state.val.testBit bit.val := by
  change state.val.testBit (WireAddress.bitIndex (WireAddress.littleEndianWire bit)).val = _
  rw [WireAddress.bitIndex_littleEndianWire]

private theorem reloadBit_disjoint (width : Nat) (left right : Fin width)
    (different : left ≠ right) :
    (reloadBit width left).wire ≠ (reloadBit width right).wire := by
  intro same
  have values := congrArg Fin.val same
  change width - 1 - left.val = width - 1 - right.val at values
  apply different
  apply Fin.ext
  omega

/-- The original clean unit seed label in the complete physical word. -/
def reloadLabel (m ell width N : Nat) : Fin (2 ^ totalQubits (registerParameters m ell width)) :=
  tripleIndex (registerParameters m ell width) 0 0 (cleanUnitLabel width N 1)

/-- Literal X gates on the set bits of the original clean unit seed. -/
def reloadGates (m ell width N : Nat) :
    List (EncodedBit.GateSpec (finIdentity (totalQubits (registerParameters m ell width)))) :=
  EncodedBit.Word.xorConstantGates
    (reloadWord (totalQubits (registerParameters m ell width))) (reloadLabel m ell width N)

/-- Load the seed on the existing complete bank, without allocating another system. -/
def reloadProgram (m ell width N : Nat) :
    UnitaryCircuit (Qubits (totalQubits (registerParameters m ell width))) :=
  .seq (programList (reloadGates m ell width N))
    (.identity (Qubits (totalQubits (registerParameters m ell width)))
      (List.range (totalQubits (registerParameters m ell width))) List.nodup_range)

private theorem reload_step_zero (m ell width N : Nat) :
    stepList (reloadGates m ell width N) 0 = reloadLabel m ell width N := by
  apply Nat.FixedWidth.word_eq_of_testBit_eq
  intro bit
  have action := EncodedBit.Word.xorConstantStep_get_target
    (reloadWord (totalQubits (registerParameters m ell width))) (reloadLabel m ell width N) bit
    (fun other different => reloadBit_disjoint _ other bit different) 0
  change (reloadBit _ bit).get (stepList (reloadGates m ell width N) 0) =
    ((reloadBit _ bit).get 0 ^^ (reloadLabel m ell width N).val.testBit bit.val) at action
  simpa only [reloadBit_get, Fin.val_zero, Nat.zero_testBit, Bool.false_xor] using action

/-- The actual X list maps the internally established zero basis state to the original seed. -/
theorem shortDLP_reload_apply_zero (m ell width N : Nat) :
    (reloadProgram m ell width N).applyNormalized
      (NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width))) 0) =
      NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width)))
        (reloadLabel m ell width N) := by
  rw [reloadProgram, UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity]
  have action := (realizesList (reloadGates m ell width N)).apply_encoded_ket 0
  change (programList (reloadGates m ell width N)).applyNormalized
      (NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width))) 0) =
      NormalizedVector.ket
        (R := Qubits (totalQubits (registerParameters m ell width)))
        (stepList (reloadGates m ell width N) 0) at action
  rw [reload_step_zero] at action
  exact action

/-- Every original physical wire remains in the advertised complete register. -/
theorem shortDLP_reload_physical_idx (m ell width N : Nat) :
    (reloadProgram m ell width N).physical_idx =
      List.range (totalQubits (registerParameters m ell width)) := by
  change UnitaryCircuit.unionPhysicalIdx (programList (reloadGates m ell width N)).physical_idx
    (List.range (totalQubits (registerParameters m ell width))) = _
  exact UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset _ _
    (programList_physical_idx_subset_range (reloadGates m ell width N))

/-- The selected positions are independently determined by the fixed source seed. -/
def reloadXCount (m ell width N : Nat) : Nat :=
  (EncodedBit.Word.constantOneIndices (reloadLabel m ell width N)).length

/-- The entire native ledger consists of exactly one X per selected seed bit. -/
theorem shortDLP_reload_eventCost (m ell width N : Nat) :
    (reloadProgram m ell width N).eventCost =
      reloadXCount m ell width N • ResourcePool.singleton (.gate (.builtin "x")) := by
  rw [reloadProgram, UnitaryCircuit.seq_eventCost, UnitaryCircuit.identity_eventCost, add_zero,
    programList_eventCost]
  have events : (reloadGates m ell width N).map event =
      List.replicate (reloadXCount m ell width N) (.gate (.builtin "x")) := by
    simp [reloadGates, EncodedBit.Word.xorConstantGates, reloadXCount, Function.comp_def, event]
  rw [events, ResourcePool.ofList_replicate]
  rfl

/-- The literal serial X list has its exact set-bit count as unit-duration depth. -/
theorem shortDLP_reload_unitDepth (m ell width N : Nat) :
    (reloadProgram m ell width N).evaluatedEventDepth (fun _ => 1) =
      reloadXCount m ell width N := by
  rw [reloadProgram, UnitaryCircuit.evaluatedEventDepth_seq,
    programList_evaluatedEventDepth_unit]
  change (reloadGates m ell width N).length + 0 = _
  rw [Nat.add_zero]
  exact EncodedBit.Word.xorConstantGates_length _ _

/-- The exact seed count is bounded independently by the actual bank width. -/
theorem shortDLP_reload_count_le (m ell width N : Nat) :
    reloadXCount m ell width N ≤ totalQubits (registerParameters m ell width) :=
  EncodedBit.Word.constantOneIndices_length_le _

end

end QuantumAlg.ShortDLP.CompiledMAU
