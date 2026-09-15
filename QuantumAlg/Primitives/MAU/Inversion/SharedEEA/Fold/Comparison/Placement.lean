/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MAU.Inversion.SharedEEA.Fold.Comparison.Focus
import all QuantumAlg.Components.Encoded.BitGates.CircuitLifting

/-!
# Actual comparison on the complete shared-EEA frame

The real comparison is tensored with Work1 and with the existing length and
phase fields. Their insertion places Work2/Iter/Ctrl at exactly the source
positions [LYL+26, sec_EEA/sub_regshare.tex:16-26]. The final basis transport
only reassociates the very same binary label, as proved by its full numeric
encoding formula. Every native event remains an event of the actual Gidney
comparison [G17, paper.tex:380-389].

The complete state statement includes arbitrary spectator values and an
arbitrary incoming Iter and Ctrl. This owner neither initializes an
input-dependent predicate nor changes the caller domain for the later fold.
-/

namespace QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonPlacement

noncomputable section

/-- Exactly the four lengths and the first three source flags between Work2 and Iter. -/
abbrev Middle (width : Nat) :=
  ((BitVec width.size × BitVec width.size) × (BitVec width.size × BitVec width.size)) ×
    ((Bool × Bool) × Bool)

private def middleEncoding (width : Nat) : BinaryLabelEncoding (Middle width) :=
  BinaryLabelEncoding.prod (lengthEncoding width)
    (BinaryLabelEncoding.prod flagPairEncoding BinaryLabelEncoding.bool)

private def pairEncoding : BinaryLabelEncoding (Bool × Bool) :=
  BinaryLabelEncoding.prod BinaryLabelEncoding.bool BinaryLabelEncoding.bool

/-- The literal tensor grouping used to insert all untouched fields. -/
abbrev Packed (width : Nat) :=
  BitVec (width + 3) × ((Fin (2 ^ (width + 3)) × Middle width) × (Bool × Bool))

private def packedEncoding (width : Nat) : BinaryLabelEncoding (Packed width) :=
  BinaryLabelEncoding.prod (wordEncoding (width + 3))
    (BinaryLabelEncoding.prod
      (BinaryLabelEncoding.prod (BinaryLabelEncoding.finIdentity (width + 3))
        (middleEncoding width)) pairEncoding)

private def packedEquiv (width : Nat) : Registers width ≃ Packed width where
  toFun state :=
    (state.firstWord, ((BitVec.equivFin state.secondWord,
      (((state.coefficientLength, state.quotientLength), (state.divisorLength, state.shift)),
        ((state.flags.first, state.flags.second), state.flags.sign))),
      (state.flags.iteration, state.control)))
  invFun state :=
    { firstWord := state.1
      secondWord := BitVec.equivFin.symm state.2.1.1
      coefficientLength := state.2.1.2.1.1.1
      quotientLength := state.2.1.2.1.1.2
      divisorLength := state.2.1.2.1.2.1
      shift := state.2.1.2.1.2.2
      flags := ⟨state.2.1.2.2.1.1, state.2.1.2.2.1.2, state.2.1.2.2.2, state.2.2.1⟩
      control := state.2.2.2 }
  left_inv := by
    rintro ⟨word1, word2, lengthT, lengthQ, lengthR, shift, ⟨p1, p2, sign, iter⟩, control⟩
    rfl
  right_inv := by
    rintro ⟨word1, ⟨⟨word2, ⟨⟨⟨lengthT, lengthQ⟩, ⟨lengthR, shift⟩⟩,
      ⟨⟨p1, p2⟩, sign⟩⟩⟩, ⟨iter, control⟩⟩⟩
    rfl

private theorem packed_width (width : Nat) :
    (packedEncoding width).width = (encoding width).width := by
  change (width + 3) +
      (((width + 3) +
        (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + 1))) +
          (1 + 1)) =
    ((width + 3) + (width + 3)) +
      (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + (1 + 1) + 1))
  omega

private theorem middle_width (width : Nat) :
    (middleEncoding width).width = 4 * width.size + 3 := by
  change ((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + 1) = _
  omega

/-- Compose the actual focus relabeling, middle insertion, and Work1 prefix address maps. -/
def nativePhysicalIndex (width index : Nat) : Nat :=
  (width + 3) + UnitaryCircuit.insertMiddlePhysicalIndex (width + 3)
    (middleEncoding width).width (FoldComparisonFocus.physicalIndex (width + 3) index)

/-- Every original native address agrees with the actual selected source-register coordinate. -/
theorem nativePhysicalIndex_eq (width : Nat) (index : Fin (width + 5)) :
    nativePhysicalIndex width index.val = FoldRegisters.physicalIndex width index.val := by
  have within := index.isLt
  unfold nativePhysicalIndex FoldComparisonFocus.physicalIndex
    UnitaryCircuit.insertMiddlePhysicalIndex FoldRegisters.physicalIndex
  rw [middle_width]
  split <;> split
  all_goals try split
  all_goals omega

private def packedIndex (width : Nat) :
    (Qubits (packedEncoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  finCongr (congrArg (fun count : Nat => 2 ^ count) (packed_width width))

/-- The complete integer basis label is unchanged, including all spectator fields. -/
private theorem packedIndex_encode (width : Nat) (state : Registers width) :
    packedIndex width ((packedEncoding width).encode (packedEquiv width state)) =
      (encoding width).encode state := by
  let lengthLabel := (lengthEncoding width).encode
    ((state.coefficientLength, state.quotientLength), (state.divisorLength, state.shift))
  let phaseLabel := flagPairEncoding.encode (state.flags.first, state.flags.second)
  let signLabel := BinaryLabelEncoding.bool.encode state.flags.sign
  let iterLabel := BinaryLabelEncoding.bool.encode state.flags.iteration
  let controlLabel := BinaryLabelEncoding.bool.encode state.control
  apply Fin.ext
  change
    (controlLabel.val + 2 ^ 1 * iterLabel.val) +
        2 ^ (1 + 1) *
          (((signLabel.val + 2 ^ 1 * phaseLabel.val) +
              2 ^ ((1 + 1) + 1) * lengthLabel.val) +
            2 ^ ((lengthEncoding width).width + ((1 + 1) + 1)) * state.secondWord.toNat) +
        2 ^ (((width + 3) + ((lengthEncoding width).width + ((1 + 1) + 1))) + (1 + 1)) *
          state.firstWord.toNat =
      (controlLabel.val + 2 ^ 1 *
          ((iterLabel.val + 2 ^ 1 * signLabel.val) + 2 ^ (1 + 1) * phaseLabel.val)) +
        2 ^ (((1 + 1) + (1 + 1)) + 1) * lengthLabel.val +
        2 ^ ((lengthEncoding width).width + (((1 + 1) + (1 + 1)) + 1)) *
          (state.secondWord.toNat + 2 ^ (width + 3) * state.firstWord.toNat)
  simp only [pow_add, pow_one]
  ring

private def rawFocus (width : Nat)
    (body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width)) :
    UnitaryCircuit (Qubits (packedEncoding width).width) :=
  UnitaryCircuit.prodRight (m := width + 3)
    (UnitaryCircuit.insertMiddle
      (leftWidth := width + 3) (middleWidth := (middleEncoding width).width)
      (rightWidth := 1 + 1) body)

private theorem inserted_prefix_trace (width : Nat)
    (body : UnitaryCircuit (Qubits ((width + 3) + (1 + 1)))) :
    (UnitaryCircuit.prodRight (m := width + 3)
      (UnitaryCircuit.insertMiddle (leftWidth := width + 3)
        (middleWidth := (middleEncoding width).width) (rightWidth := 1 + 1) body)).eventTrace =
      body.eventTrace := by
  rw [UnitaryCircuit.prodRight_eventTrace, UnitaryCircuit.insertMiddle_eventTrace]

private def rawStep {width : Nat}
    (action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3))
    (state : Packed width) : Packed width :=
  let result := action (state.2.1.1, state.2.2)
  (state.1, ((result.1, state.2.1.2), result.2))

private theorem rawFocus_realizes (width : Nat)
    {body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width)}
    {action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3)}
    (realizes : UnitaryCircuit.Realizes (FoldComparisonFocus.encoding (width + 3)) body
      action) :
    UnitaryCircuit.Realizes (packedEncoding width) (rawFocus width body) (rawStep action) :=
  (realizes.insertMiddle (middle := middleEncoding width)).prodRight
    (left := wordEncoding (width + 3))

private theorem rawFocus_range (width : Nat)
    (body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width))
    (within : body.physical_idx ⊆ List.range ((width + 3) + (1 + 1))) :
    (rawFocus width body).physical_idx ⊆ List.range (packedEncoding width).width := by
  exact UnitaryCircuit.prodRight_physical_idx_subset_range
    (UnitaryCircuit.insertMiddle (middleWidth := (middleEncoding width).width) body)
    (UnitaryCircuit.insertMiddle_physical_idx_subset_range _ within)

/-- Place an existing word/Iter/Ctrl program among the exact original spectator fields. -/
def placeFocus (width : Nat)
    (body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  (UnitaryCircuit.reindex (packedIndex width) (rawFocus width body)).seq
    (UnitaryCircuit.identity (Qubits (encoding width).width)
      (List.range (encoding width).width) List.nodup_range)

/-- Named-field action of the actual program, keeping every complementary field unchanged. -/
def focusStep {width : Nat}
    (action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3))
    (state : Registers width) : Registers width :=
  (FoldRegisters.grouping width).symm
    ((FoldComparisonFocus.fieldEquiv (width + 3)).symm
      (action (FoldComparisonFocus.fieldEquiv (width + 3)
        (FoldRegisters.grouping width state).1)), (FoldRegisters.grouping width state).2)

/-- Actual tensor insertion and exact binary regrouping preserve the full certified action. -/
theorem placeFocus_realizes (width : Nat)
    {body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width)}
    {action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3)}
    (realizes : UnitaryCircuit.Realizes (FoldComparisonFocus.encoding (width + 3)) body
      action) :
    UnitaryCircuit.Realizes (encoding width) (placeFocus width body) (focusStep action) where
  apply_encoded_ket := by
    intro state
    have raw := (rawFocus_realizes width realizes).apply_encoded_ket (packedEquiv width state)
    have output : rawStep action (packedEquiv width state) =
        packedEquiv width (focusStep action state) := by
      rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
        ⟨p1, p2, sign, iter⟩, control⟩
      rfl
    rw [output] at raw
    have placed := UnitaryCircuit.Realizes.applyNormalized_reindex_ket_of_eq
      (R := Qubits (packedEncoding width).width) (S := Qubits (encoding width).width)
      (packedIndex width) (rawFocus width body) _ _ raw
    rw [packedIndex_encode, packedIndex_encode] at placed
    unfold placeFocus
    rw [UnitaryCircuit.applyNormalized_seq, UnitaryCircuit.applyNormalized_identity]
    exact placed

/-- The actual physical footprint is the complete original frame, with no extra wire. -/
theorem placeFocus_physical (width : Nat)
    (body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width))
    (within : body.physical_idx ⊆ List.range ((width + 3) + (1 + 1))) :
    (placeFocus width body).physical_idx = List.range (encoding width).width := by
  change UnitaryCircuit.unionPhysicalIdx (rawFocus width body).physical_idx
    (List.range (encoding width).width) = _
  apply UnitaryCircuit.unionPhysicalIdx_eq_right_of_subset
  simpa only [packed_width] using rawFocus_range width body within

/-- Spectator tensor insertion and regrouping retain every actual native event in order. -/
theorem placeFocus_eventTrace (width : Nat)
    (body : UnitaryCircuit (Qubits (FoldComparisonFocus.encoding (width + 3)).width)) :
    (placeFocus width body).eventTrace = body.eventTrace := by
  have empty : (UnitaryCircuit.identity (Qubits (encoding width).width)
      (List.range (encoding width).width) List.nodup_range).eventTrace = [] := rfl
  rw [placeFocus, UnitaryCircuit.seq_eventTrace, empty, List.append_nil,
    UnitaryCircuit.reindex_eventTrace]
  exact inserted_prefix_trace width body

/-- The same actual comparison occupies its original full canonical source frame. -/
def program (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    UnitaryCircuit (Qubits (encoding width).width) :=
  placeFocus width (FoldComparisonFocus.program (width + 3) pivot)

/-- Only Iter changes, by comparison with the actual Work2 value; every spectator is retained. -/
theorem program_realizes (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width pivot)
      (FoldRegisters.comparisonStep width pivot.val) :=
  (placeFocus_realizes width (FoldComparisonFocus.program_realizes (width + 3) pivot)).congrStep
    (by
      rintro ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
        ⟨p1, p2, sign, iter⟩, control⟩
      rfl)

/-- The declared physical footprint is exactly the complete original encoding. -/
theorem program_physical (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    (program width pivot).physical_idx = List.range (encoding width).width :=
  placeFocus_physical width (FoldComparisonFocus.program (width + 3) pivot)
    (FoldComparisonFocus.program_physical_range (width + 3) pivot)

/-- Every actual native event is retained; adding untouched fields adds no arithmetic event. -/
theorem program_eventTrace (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    (program width pivot).eventTrace =
      (Addition.Gidney.comparisonProgram (width + 3) pivot).eventTrace :=
  (placeFocus_eventTrace width (FoldComparisonFocus.program (width + 3) pivot)).trans
    (FoldComparisonFocus.program_eventTrace (width + 3) pivot)

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonPlacement
