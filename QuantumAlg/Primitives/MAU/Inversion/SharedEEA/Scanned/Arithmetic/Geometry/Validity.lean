/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Selection.Frame
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Address.BitVec
import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Selector.Resources

/-!
# Actual finite geometry predicate with arbitrary Iter

A pruned native unary traversal toggles the original arbitrary Iter wire
for a positive in-range address. The separate conjunction position is its
root and every prefix position is restored. A surrounding actual negative
root mask can use this same circuit for the complete temporary geometry
word. No source metadata tuple is enumerated and no input value selects a
host-generated circuit.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity

noncomputable section

open EncodedBit WindowLookup NumberTheory.SharedEEA

/-- The original arbitrary Iter is the predicate output, rather than a fresh clean bit. -/
def output (width : Nat) : EncodedBit (encoding width) :=
  sourceBit width (SharedEEA.iterationBit width)

/-- The full temporary carry supplies the root; the existing prefix supplies all later levels. -/
def stack (width : Nat) (index : Fin (ScanMetadata.addressWidth width + 1)) :
    EncodedBit (encoding width) :=
  if zero : index.val = 0 then conjunctionBit width
  else prefixBit width ⟨index.val - 1, by have := index.isLt; omega⟩

private lemma stack_distinct (width : Nat) :
    Function.Injective (fun index => (stack width index).wire) := by
  intro left right same
  dsimp only [stack] at same
  split_ifs at same with first second
  · exact Fin.ext (first.trans second.symm)
  · exact False.elim ((prefix_conjunction_ne width _).symm same)
  · exact False.elim (prefix_conjunction_ne width _ same)
  · apply Fin.ext
    have equal := congrArg Fin.val same
    simp only [prefixBit_wire] at equal
    omega

private lemma address_stack_ne (width : Nat) (address : Fin (ScanMetadata.addressWidth width))
    (level : Fin (ScanMetadata.addressWidth width + 1)) :
    (addressBit width address).wire ≠ (stack width level).wire := by
  unfold stack
  split
  · exact address_conjunction_ne width address
  · exact address_prefix_ne width address _

/-- Every original full address and prefix position has its actual nonoverlapping role. -/
def frame (width : Nat) : SelectorFrame (encoding width) (ScanMetadata.addressWidth width) where
  address := addressBit width
  stack := stack width
  addressDistinct := by
    intro left right same
    by_contra different
    exact address_address_ne width left right different same
  stackDistinct := stack_distinct width
  separate := address_stack_ne width

private lemma output_address_ne (width : Nat) (index : Fin (ScanMetadata.addressWidth width)) :
    (output width).wire ≠ ((frame width).address index).wire :=
  source_address_ne width _ index

private lemma output_stack_ne (width : Nat)
    (index : Fin (ScanMetadata.addressWidth width + 1)) :
    (output width).wire ≠ ((frame width).stack index).wire := by
  change (output width).wire ≠ (stack width index).wire
  unfold stack
  split
  · exact source_conjunction_ne width _
  · exact source_prefix_ne width _ _

/-- Only positive addresses within the complete original physical work word retain a leaf. -/
def active (width : Nat) (label : Fin (2 ^ ScanMetadata.addressWidth width)) : Bool :=
  decide (0 < label.val ∧ label.val ≤ width + 3)

/-- The physical validity predicate is a static pruned native tree. -/
def tree (width : Nat) : SelectorTrie (ScanMetadata.addressWidth width) :=
  .prune (ScanMetadata.addressWidth width) (active width)

private def leafGate (width : Nat) : GateSpec (encoding width) :=
  .cnot ((frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩) (output width)
    (output_stack_ne width _).symm

/-- One actual CNOT toggles the arbitrary original Iter at each retained leaf. -/
def callback (width : Nat) (_label : Fin (2 ^ ScanMetadata.addressWidth width)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  (leafGate width).program (QubitLayout.canonical _) .empty

private lemma callback_realizes (width : Nat)
    (label : Fin (2 ^ ScanMetadata.addressWidth width))
    (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (callback width label) environment
      (conditionalAction ((frame width).stack ⟨ScanMetadata.addressWidth width, by omega⟩)
        (output width).flip) :=
  GateSpec.realizes (QubitLayout.canonical _) .empty (leafGate width) environment

private lemma preserves (width : Nat) : (frame width).Preserves (output width).flip :=
  ⟨fun index => get_flip_of_wire_ne _ _ (output_address_ne width index),
    fun index => get_flip_of_wire_ne _ _ (output_stack_ne width index)⟩

private lemma independent (width : Nat) :
    (frame width).IndependentPrefixes (output width).flip := by
  intro index state
  exact EncodedBit.flip_comm _ _ state

private lemma clean (width : Nat) (state : Data width)
    (zero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (frame width).CleanFrom 0 state := by
  intro index _present
  have nonzero : index.succ.val ≠ 0 := by change index.val + 1 ≠ 0; omega
  change (stack width index.succ).get state = false
  unfold stack
  rw [dif_neg nonzero, prefixBit_get, zero, BitVec.getMsbD_zero]

private lemma address_label (width : Nat) (state : Data width) :
    (frame width).addressLabelAt (ScanMetadata.addressWidth width)
      0 (by omega) 0 (by omega) state = state.2.1.toFin :=
  (frame width).addressLabelAt_bitVec state.2.1 state
    (fun index => addressBit_get width index state)

/-- Every actual prefix operation and retained callback acts on the same original full frame. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  (frame width).program (QubitLayout.canonical _) .empty (callback width) (tree width)

/-- The coherent predicate flips only the original output, retaining the complete complement. -/
def step (width : Nat) (state : Data width) : Data width :=
  if state.2.2.2 && decide (0 < state.2.1.toNat ∧ state.2.1.toNat ≤ width + 3) then
    (output width).flip state else state

/-- Exact clean-prefix ket semantics include arbitrary incoming Iter and every finite address. -/
lemma program_apply_encoded_ket (width : Nat) (environment : OracleModel.empty.Interpretation)
    (state : Data width) (zero : state.2.2.1 = 0#(ScanMetadata.addressWidth width)) :
    (program width).applyNormalized environment
      (NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode state))) =
      NormalizedVector.ket ((QubitLayout.canonical _).basisEquiv.symm
        ((encoding width).encode (step width state))) := by
  have actual := SelectorFrame.program_apply_encoded_ket_clean (frame width)
    (QubitLayout.canonical _) .empty (callback width) (fun _ => (output width).flip) environment
    (fun label => callback_realizes width label environment) (fun _ => preserves width)
    (fun _ => independent width) (tree width) state (clean width state zero)
  change (program width).applyNormalized environment _ = _ at actual
  have selected : conditionalAction ((frame width).stack ⟨0, by omega⟩)
      ((frame width).selectedActionAt (fun _ => (output width).flip) (tree width)
        0 (by omega) 0 (by omega)) state = step width state := by
    change (if state.2.2.2 then
      (frame width).selectedActionAt (fun _ => (output width).flip) (tree width)
        0 (by omega) 0 (by omega) state else state) = _
    rw [tree, SelectorFrame.selectedActionAt_prune, address_label]
    change (if state.2.2.2 then
      (if decide (0 < state.2.1.toFin.val ∧ state.2.1.toFin.val ≤ width + 3) then
        (output width).flip state else state) else state) = _
    rw [BitVec.val_toFin]
    unfold step
    cases state.2.2.2 <;> rfl
  rw [selected] at actual
  exact actual

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.GeometryValidity
