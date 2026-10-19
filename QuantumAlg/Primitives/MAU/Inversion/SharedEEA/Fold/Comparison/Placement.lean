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

variable {environment : OracleModel.empty.Interpretation}

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

private lemma packed_width (width : Nat) :
    (packedEncoding width).width = (encoding width).width := by
  change (width + 3) +
      (((width + 3) +
        (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + 1))) +
          (1 + 1)) =
    ((width + 3) + (width + 3)) +
      (((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + (1 + 1) + 1))
  omega

private lemma middle_width (width : Nat) :
    (middleEncoding width).width = 4 * width.size + 3 := by
  change ((width.size + width.size) + (width.size + width.size)) + ((1 + 1) + 1) = _
  omega

/-- Compose the actual focus relabeling, middle insertion, and Work1 prefix address maps. -/
def nativePhysicalIndex (width index : Nat) : Nat :=
  (width + 3) + UnitaryCircuit.binaryMiddleIndex (width + 3)
    (middleEncoding width).width (FoldComparisonFocus.physicalIndex (width + 3) index)

/-- Every original native address agrees with the actual selected source-register coordinate. -/
lemma nativePhysicalIndex_eq (width : Nat) (index : Fin (width + 5)) :
    nativePhysicalIndex width index.val = FoldRegisters.physicalIndex width index.val := by
  have within := index.isLt
  unfold nativePhysicalIndex FoldComparisonFocus.physicalIndex
    UnitaryCircuit.binaryMiddleIndex FoldRegisters.physicalIndex
  rw [middle_width]
  split <;> split
  all_goals try split
  all_goals omega

private def packedIndex (width : Nat) :
    (Qubits (packedEncoding width).width).Index ≃ (Qubits (encoding width).width).Index :=
  finCongr (congrArg (fun count : Nat => 2 ^ count) (packed_width width))

/-- The complete integer basis label is unchanged, including all spectator fields. -/
private lemma packedIndex_encode (width : Nat) (state : Registers width) :
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
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (FoldComparisonFocus.encoding (width + 3)).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (packedEncoding width).width).toQuantum :=
  UnitaryCircuit.prodRight (m := width + 3)
    (UnitaryCircuit.insertMiddle
      (leftWidth := width + 3) (middleWidth := (middleEncoding width).width)
      (rightWidth := 1 + 1) body)

private lemma inserted_prefix_trace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical ((width + 3) + (1 + 1))).toQuantum) :
    (UnitaryCircuit.prodRight (m := width + 3)
      (UnitaryCircuit.insertMiddle (leftWidth := width + 3)
        (middleWidth := (middleEncoding width).width) (rightWidth := 1 + 1) body)).eventTrace =
      body.eventTrace := by
  simp only [UnitaryCircuit.prodRight, UnitaryCircuit.insertMiddle,
    UnitaryCircuit.onBinarySuffix, UnitaryCircuit.onBinaryMiddle,
    UnitaryCircuit.embed_eventTrace, UnitaryCircuit.relabel_eventTrace]
  exact UnitaryCircuit.relabel_eventTrace body
    (UnitaryCircuit.binaryMiddleShift (width + 3) (middleEncoding width).width)

private def rawStep {width : Nat}
    (action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3))
    (state : Packed width) : Packed width :=
  let result := action (state.2.1.1, state.2.2)
  (state.1, ((result.1, state.2.1.2), result.2))

private lemma rawFocus_realizes (width : Nat)
    {body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (FoldComparisonFocus.encoding (width + 3)).width).toQuantum}
    {action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3)}
    (realizes : UnitaryCircuit.Realizes (FoldComparisonFocus.encoding (width + 3)) body environment
      action) :
    UnitaryCircuit.Realizes (packedEncoding width) (rawFocus width body) environment (rawStep
      action) :=
  (realizes.onBinaryMiddle (middle := middleEncoding width)).onBinarySuffix
    (left := wordEncoding (width + 3))

/-- Place an existing word/Iter/Ctrl program among the exact original spectator fields. -/
def placeFocus (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (FoldComparisonFocus.encoding (width + 3)).width).toQuantum) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  UnitaryCircuit.castCanonicalQubitWidth (packed_width width) (rawFocus width body)

/-- Named-field action of the actual program, keeping every complementary field unchanged. -/
def focusStep {width : Nat}
    (action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3))
    (state : Registers width) : Registers width :=
  (FoldRegisters.grouping width).symm
    ((FoldComparisonFocus.fieldEquiv (width + 3)).symm
      (action (FoldComparisonFocus.fieldEquiv (width + 3)
        (FoldRegisters.grouping width state).1)), (FoldRegisters.grouping width state).2)

/-- Actual tensor insertion and exact binary regrouping preserve the full certified action. -/
lemma placeFocus_realizes (width : Nat)
    {body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (FoldComparisonFocus.encoding (width + 3)).width).toQuantum}
    {action : FoldComparisonFocus.Data (width + 3) → FoldComparisonFocus.Data (width + 3)}
    (realizes : UnitaryCircuit.Realizes (FoldComparisonFocus.encoding (width + 3)) body environment
      action) :
    UnitaryCircuit.Realizes (encoding width) (placeFocus width body) environment (focusStep
      action) where
  apply_encoded_ket := by
    intro state
    let input := packedEquiv width state
    let output := rawStep action input
    have run := (rawFocus_realizes width realizes).apply_encoded_ket input
    have result : output = packedEquiv width (focusStep action state) := by
      rcases state with ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
        ⟨p1, p2, sign, iter⟩, control⟩
      rfl
    have inputCast : packed_width width ▸ NormalizedVector.ket
        ((QubitLayout.canonical (packedEncoding width).width).basisEquiv.symm
          ((packedEncoding width).encode input)) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode state)) := by
      rw [UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg
        (fun label => NormalizedVector.ket
          ((QubitLayout.canonical (encoding width).width).basisEquiv.symm label))
        (by simpa only [input, packedIndex, UnitaryCircuit.castQubitWidthIndex] using
          packedIndex_encode width state)
    have outputCast : packed_width width ▸ NormalizedVector.ket
        ((QubitLayout.canonical (packedEncoding width).width).basisEquiv.symm
          ((packedEncoding width).encode output)) =
      NormalizedVector.ket
        ((QubitLayout.canonical (encoding width).width).basisEquiv.symm
          ((encoding width).encode (focusStep action state))) := by
      rw [result, UnitaryCircuit.castCanonicalQubitWidth_ket]
      exact congrArg
        (fun label => NormalizedVector.ket
          ((QubitLayout.canonical (encoding width).width).basisEquiv.symm label))
        (by simpa only [packedIndex, UnitaryCircuit.castQubitWidthIndex] using
          packedIndex_encode width (focusStep action state))
    calc
      _ = (placeFocus width body).applyNormalized environment
          (packed_width width ▸ NormalizedVector.ket
            ((QubitLayout.canonical (packedEncoding width).width).basisEquiv.symm
              ((packedEncoding width).encode input))) :=
        congrArg ((placeFocus width body).applyNormalized environment) inputCast.symm
      _ = packed_width width ▸ (rawFocus width body).applyNormalized environment
          (NormalizedVector.ket
            ((QubitLayout.canonical (packedEncoding width).width).basisEquiv.symm
              ((packedEncoding width).encode input))) :=
        UnitaryCircuit.castCanonicalQubitWidth_applyNormalized
          (packed_width width) (rawFocus width body) _ environment
      _ = packed_width width ▸ NormalizedVector.ket
          ((QubitLayout.canonical (packedEncoding width).width).basisEquiv.symm
            ((packedEncoding width).encode output)) := congrArg (fun vector =>
        packed_width width ▸ vector) run
      _ = _ := outputCast

/-- Spectator tensor insertion and regrouping retain every actual native event in order. -/
lemma placeFocus_eventTrace (width : Nat)
    (body : UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (FoldComparisonFocus.encoding (width + 3)).width).toQuantum) :
    (placeFocus width body).eventTrace = body.eventTrace := by
  exact (UnitaryCircuit.castCanonicalQubitWidth_eventTrace
    (packed_width width) (rawFocus width body)).trans
      (inserted_prefix_trace width body)

/-- The same actual comparison occupies its original full canonical source frame. -/
def program (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    UnitaryCircuit AlgorithmGate.model .empty
      (QubitLayout.canonical (encoding width).width).toQuantum :=
  placeFocus width (FoldComparisonFocus.program (width + 3) pivot)

/-- Only Iter changes, by comparison with the actual Work2 value; every spectator is retained. -/
lemma program_realizes (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    UnitaryCircuit.Realizes (encoding width) (program width pivot) environment
      (FoldRegisters.comparisonStep width pivot.val) :=
  (placeFocus_realizes width (FoldComparisonFocus.program_realizes (width + 3) pivot)).congrStep
    (by
      rintro ⟨word1, word2, lengthT, lengthQ, lengthR, shift,
        ⟨p1, p2, sign, iter⟩, control⟩
      rfl)

/-- Every actual native event is retained; adding untouched fields adds no arithmetic event. -/
lemma program_eventTrace (width : Nat) (pivot : Fin (2 ^ (width + 3) + 1)) :
    (program width pivot).eventTrace =
      (Addition.Gidney.comparisonProgram (width + 3) pivot).eventTrace :=
  (placeFocus_eventTrace width (FoldComparisonFocus.program (width + 3) pivot)).trans
    (FoldComparisonFocus.program_eventTrace (width + 3) pivot)

end

end QuantumAlg.MAU.Inversion.SharedEEA.FoldComparisonPlacement
