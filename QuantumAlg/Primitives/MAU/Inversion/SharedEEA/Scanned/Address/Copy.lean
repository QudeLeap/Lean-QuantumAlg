/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Scanned.Registers.Coordinates
import all QuantumAlg.Components.Encoded.BitGates.Word.Xor
import all QuantumAlg.Components.Encoded.BitGates.Parallel

/-!
# Native full-carry address copy

The complete coefficient-length word is copied beside one existing prefix
bit. That bit supplies the high padding coordinate and is restored. Every
copy is an actual CNOT between distinct existing systems; no length label
is read by a classical callback. The all-label law retains arbitrary target,
prefix and conjunction contents. Later address preparation proves the
required zero padding at its own clean-pool boundary.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressCopy

noncomputable section

open EncodedBit NumberTheory.SharedEEA

/-- The first prefix bit supplies the explicit high padding coordinate. -/
def padding (width : Nat) : EncodedBit (encoding width) :=
  prefixBit width ⟨0, by unfold ScanMetadata.addressWidth; omega⟩

/-- The full high-bit-plus-coefficient source, in physical big-endian order. -/
def source (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) where
  bit index := if zero : index.val = 0 then padding width
    else sourceBit width (coefficientLengthBit width
      ⟨index.val - 1, by
        have within := index.isLt
        unfold ScanMetadata.addressWidth at within
        omega⟩)

/-- The complete target includes its actual high carry coordinate. -/
def target (width : Nat) : Word (encoding width) (ScanMetadata.addressWidth width) :=
  ⟨addressBit width⟩

private lemma source_target_ne (width : Nat)
    (left right : Fin (ScanMetadata.addressWidth width)) :
    ((source width).bit left).wire ≠ ((target width).bit right).wire := by
  unfold source
  dsimp only
  split
  · exact (address_prefix_ne width right _).symm
  · exact source_address_ne width _ right

private lemma source_source_ne (width : Nat)
    (left right : Fin (ScanMetadata.addressWidth width)) (different : left ≠ right) :
    ((source width).bit left).wire ≠ ((source width).bit right).wire := by
  unfold source
  dsimp only
  split_ifs with first second
  · exact False.elim (different (Fin.ext (first.trans second.symm)))
  · exact (source_prefix_ne width _ _).symm
  · exact source_prefix_ne width _ _
  · intro same
    apply different
    apply Fin.ext
    have values := congrArg Fin.val same
    simp only [Scanned.sourceBit_wire, coefficientLengthBit_wire] at values
    omega

/-- Concrete full-address CNOT list. -/
def gates (width : Nat) : List (GateSpec (encoding width)) :=
  Word.xorIntoGates (source width) (target width) (fun index => source_target_ne width index index)

private lemma gates_independent (width : Nat) (physical : QubitLayout (encoding width).width) :
    (gates width).Pairwise (fun first second =>
      Disjoint (GateSpec.physicalSupport physical first)
        (GateSpec.physicalSupport physical second)) := by
  rw [gates, Word.xorIntoGates, List.pairwise_ofFn]
  intro left right before
  rw [GateSpec.physicalSupport_cnot, GateSpec.physicalSupport_cnot]
  simp only [Finset.disjoint_insert_left, Finset.disjoint_singleton_left,
    Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨⟨source_source_ne width left right (ne_of_lt before),
    source_target_ne width left right⟩,
    ⟨(source_target_ne width right left).symm,
      address_address_ne width left right (ne_of_lt before)⟩⟩

/-- The original source word includes the actual padding bit, even when it is dirty. -/
def value (width : Nat) (state : Data width) : BitVec (ScanMetadata.addressWidth width) :=
  BitVec.cons ((padding width).get state) state.1.coefficientLength

private lemma source_get (width : Nat) (state : Data width)
    (index : Fin (ScanMetadata.addressWidth width)) :
    ((source width).bit index).get state = (value width state).getMsbD index.val := by
  change ((source width).bit index).get state =
    (BitVec.cons ((padding width).get state) state.1.coefficientLength :
      BitVec (width.size + 1)).getMsbD index.val
  unfold source
  dsimp only
  split
  · rename_i zero
    simp only [zero, BitVec.getMsbD_cons_zero]
  · rename_i nonzero
    have successor : index.val = (index.val - 1) + 1 := by omega
    rw [sourceBit_get, coefficientLengthBit_get]
    change state.1.coefficientLength.getMsbD (index.val - 1) = _
    conv_rhs => rw [successor, BitVec.getMsbD_cons_succ]

private def withoutAddress (width : Nat) (state : Data width) : Data width :=
  (state.1, (0#(ScanMetadata.addressWidth width), state.2.2))

private lemma complement_preserved (width : Nat) (state : Data width) :
    withoutAddress width (GateSpec.stepList (gates width) state) = withoutAddress width state :=
  Word.xorIntoStep_preserves_projection (source width) (target width)
    (fun index => source_target_ne width index index) (withoutAddress width)
    (fun _ _ => rfl) state

private lemma address_result (width : Nat) (state : Data width) :
    (GateSpec.stepList (gates width) state).2.1 = state.2.1 ^^^ value width state := by
  apply BitVec.eq_of_getMsbD_eq
  intro index within
  have read := Word.xorIntoStep_get_target (source width) (target width)
    (fun index => source_target_ne width index index) ⟨index, within⟩
    (fun other different => address_address_ne width other _ different)
    (fun other => (source_target_ne width _ other).symm) state
  change (addressBit width ⟨index, within⟩).get (GateSpec.stepList (gates width) state) =
    ((addressBit width ⟨index, within⟩).get state ^^
      ((source width).bit ⟨index, within⟩).get state)
      at read
  simpa only [addressBit_get, source_get, BitVec.getMsbD_xor] using read

/-- Independent full-frame XOR action, preserving all source, prefix and conjunction fields. -/
def step (width : Nat) (state : Data width) : Data width :=
  (state.1, (state.2.1 ^^^ value width state, state.2.2))

/-- The actual list implements that action on every complete finite label. -/
lemma gates_step (width : Nat) (state : Data width) :
    GateSpec.stepList (gates width) state = step width state := by
  let result := GateSpec.stepList (gates width) state
  calc
    result = ((withoutAddress width result).1,
      (result.2.1, (withoutAddress width result).2.2)) := rfl
    _ = _ := by rw [complement_preserved, address_result]; rfl

/-- Compile the literal native copy on the full unchanged physical frame. -/
def program (width : Nat) : UnitaryCircuit AlgorithmGate.model .empty
    (QubitLayout.canonical (encoding width).width).toQuantum :=
  GateSpec.parallelProgramList (QubitLayout.canonical _) .empty (gates width)
    (gates_independent width _)

/-- Exact coherent semantics of the native full-carry copy, including arbitrary dirty fields. -/
lemma program_realizes (width : Nat) (environment : OracleModel.empty.Interpretation) :
    UnitaryCircuit.Realizes (encoding width) (program width) environment (step width) where
  apply_encoded_ket := by
    intro state
    simpa only [program, UnitaryCircuit.applyNormalized,
      GateSpec.parallelProgramList_matrix] using
      (GateSpec.realizesList_congrStep (QubitLayout.canonical _) .empty
        (gates width) (gates_step width) environment).apply_encoded_ket state

/-- Every copied coordinate is charged as one native CNOT. -/
lemma program_eventTrace (width : Nat) :
    (program width).eventTrace =
      List.replicate (ScanMetadata.addressWidth width) (.gate .cnot) := by
  rw [program, GateSpec.parallelProgramList_eventTrace, GateSpec.programList_eventTrace]
  simp only [gates, Word.xorIntoGates, List.map_ofFn, Function.comp_def]
  change (List.ofFn fun _ : Fin (ScanMetadata.addressWidth width) =>
    (.gate .cnot : Resource.Event (.quantum AlgorithmGate.model .empty))) = _
  exact List.ofFn_const _ _

/-- The complete full-carry copy is one actual disjoint-support layer. -/
lemma program_unitDepth (width : Nat) :
    (program width).evaluatedEventDepth (fun _ => 1) = 1 := by
  rw [program, GateSpec.parallelProgramList_unitDepth]
  have nonempty : gates width ≠ [] := by
    intro empty
    have length := congrArg List.length empty
    simp only [gates, Word.xorIntoGates_length, List.length_nil] at length
    unfold ScanMetadata.addressWidth at length
    omega
  exact if_neg nonempty

end

end QuantumAlg.MAU.Inversion.SharedEEA.Scanned.AddressCopy
