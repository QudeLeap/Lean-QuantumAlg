/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Frame
import all QuantumAlg.Components.Encoded.BitGates.Controlled.Fredkin

/-!
# One-Toffoli leaves of the full metadata-address scan

Every retained leaf exchanges Sign with one original Work1 position. The
actual final prefix controls the Fredkin decomposition. Its ideal payload
protects the complete address and stack, and ignores every temporary prefix.
These laws apply to arbitrary source data and all inactive controls.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA SelectionFrame

/-- Sign remains at its original source position. -/
def left (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (SharedEEA.signBit width)

/-- The leaf payload addresses one original Work1 position. -/
def right (width : Nat) (index : Fin (width + 3)) : EncodedBit (encoding width) :=
  sourceBit width (SharedEEA.firstWordBit width index)

private lemma source_sign_word (width : Nat) (index : Fin (width + 3)) :
    (SharedEEA.signBit width).wire ≠ (SharedEEA.firstWordBit width index).wire := by
  intro same
  have equal := congrArg Fin.val same
  rw [SharedEEA.signBit_wire, SharedEEA.firstWordBit_wire] at equal
  have := index.isLt
  omega

private lemma source_sign_control (width : Nat) :
    (SharedEEA.signBit width).wire ≠ (SharedEEA.controlBit width).wire := by
  intro same
  have equal := congrArg Fin.val same
  rw [SharedEEA.signBit_wire, SharedEEA.controlBit_wire] at equal
  omega

private lemma source_word_control (width : Nat) (index : Fin (width + 3)) :
    (SharedEEA.firstWordBit width index).wire ≠ (SharedEEA.controlBit width).wire := by
  intro same
  have equal := congrArg Fin.val same
  rw [SharedEEA.firstWordBit_wire, SharedEEA.controlBit_wire] at equal
  have := index.isLt
  omega

private lemma targets_ne (width : Nat) (index : Fin (width + 3)) :
    (left width).wire ≠ (right width index).wire :=
  source_source_ne width _ _ (source_sign_word width index)

/-- The ideal leaf exchanges only its two payload coordinates. -/
def action (width : Nat) (index : Fin (width + 3)) (state : Data width) : Data width :=
  swapStep (left width) (right width index) (targets_ne width index) state

/-- No address or selector stack coordinate is modified by the ideal payload. -/
lemma action_preserves (width : Nat) (index : Fin (width + 3)) :
    (frame width).Preserves (action width index) := by
  constructor
  · intro position state
    exact swapStep_get_observed_of_swap_ne _ _ _ (targets_ne width index)
      (source_address_ne width _ position) (source_address_ne width _ position) state
  · intro position state
    change (stack width position).get (action width index state) =
      (stack width position).get state
    unfold stack
    split
    · exact swapStep_get_observed_of_swap_ne _ _ _ (targets_ne width index)
        (source_source_ne width _ _ (source_sign_control width))
        (source_source_ne width _ _ (source_word_control width index)) state
    · exact swapStep_get_observed_of_swap_ne _ _ _ (targets_ne width index)
        (source_prefix_ne width _ _) (source_prefix_ne width _ _) state

private lemma stack_succ (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (frame width).stack index.succ = prefixBit width index := by
  change stack width index.succ = _
  unfold stack
  rw [dif_neg (by change index.val + 1 ≠ 0; omega)]
  rfl

/-- Prefix flips commute with every ideal payload on complete arbitrary labels. -/
lemma action_independent (width : Nat) (index : Fin (width + 3)) :
    (frame width).IndependentPrefixes (action width index) := by
  intro position state
  rw [stack_succ]
  apply GateSpec.stepList_flip_comm_of_bitDisjoint
  intro gate present
  simp only [swapGates, List.mem_cons, List.not_mem_nil, or_false] at present
  rcases present with rfl | rfl | rfl
  · exact ⟨source_prefix_ne width _ position, source_prefix_ne width _ position⟩
  · exact ⟨source_prefix_ne width _ position, source_prefix_ne width _ position⟩
  · exact ⟨source_prefix_ne width _ position, source_prefix_ne width _ position⟩

/-- The actual final traversal prefix controls this retained leaf. -/
def control (width : Nat) : EncodedBit (encoding width) :=
  prefixBit width ⟨ScanMetadata.addressWidth width - 1, by
    unfold ScanMetadata.addressWidth
    omega⟩

private lemma control_left (width : Nat) : (control width).wire ≠ (left width).wire :=
  (source_prefix_ne width _ _).symm

private lemma control_right (width : Nat) (index : Fin (width + 3)) :
    (control width).wire ≠ (right width index).wire :=
  (source_prefix_ne width _ _).symm

/-- Exactly three native gates implement the prefix-controlled exchange. -/
def program (width : Nat) (index : Fin (width + 3)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  fredkinProgram (QubitLayout.canonical _) .empty (control width) (left width) (right width index)
    (control_left width) (control_right width index) (targets_ne width index)

/-- The native leaf is the conditional ideal payload on every encoded input. -/
lemma program_realizes (width : Nat) (index : Fin (width + 3))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width index) environment
      (conditionalAction (control width) (action width index)) :=
  fredkin_realizes (QubitLayout.canonical _) .empty _ _ _ _ _ _ environment

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.SelectionExchange
