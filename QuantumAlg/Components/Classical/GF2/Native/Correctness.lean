/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native.Semantics
import all QuantumAlg.Components.Classical.GF2.Native.State.Decision
import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Traversal
import all QuantumAlg.Components.Classical.GF2.Native.Validation.Traversal

/-!
# Original recovery at the actual seven-cell body boundary

The actual stored decision controls all three original branches. When there
is one free column, the real candidate traversal, nonzero test and validation
produce the original back-substitution result. Otherwise all three original
identity arms are taken. The last real packOption writes precisely recover?.
The original input may share storage with the final output; structural caller
reads outside that final destination survive every internal workspace stage.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution ClassicalWorkspace

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {rowCount width : Nat}

private theorem bit_value (value : CShape.Value .bit) (bit : Bool)
    (same : value.toBool = bit) : value = .bit bit := by
  cases value with
  | bit value => exact congrArg CShape.Value.bit same

private theorem when_true (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (store : Store ctx)
    (value : (store.read (.storage success.toCStorageRef)).toBool = true) :
    (whenSuccessfulStep success body record store).1 = (record store).1 := by
  unfold whenSuccessfulStep
  rw [bit_value _ true value]
  rfl

private theorem when_false (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path) (store : Store ctx)
    (value : (store.read (.storage success.toCStorageRef)).toBool = false) :
    (whenSuccessfulStep success body record store).1 = store := by
  unfold whenSuccessfulStep
  rw [bit_value _ false value]
  rfl

private theorem when_read (success : CWriteRef ctx .bit) (body : Circuit ctx ctx)
    (record : Store ctx → Store ctx × body.Path) {shape : CShape}
    (other : CInputRef ctx shape)
    (preserves : ∀ store, (record store).1.read other = store.read other) (store : Store ctx) :
    (whenSuccessfulStep success body record store).1.read other = store.read other := by
  cases value : store.read (.storage success.toCStorageRef) with
  | bit bit =>
    cases bit
    · rw [when_false success body record store (by rw [value]; rfl)]
    · rw [when_true success body record store (by rw [value]; rfl)]
      exact preserves store

private theorem into_store
    (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
    (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
    (used : CWriteRef ctx (.unsignedWord rowCount))
    (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
    (columns candidate zero : CWriteRef ctx (.unsignedWord width))
    (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))
    (store : Store ctx) :
    let reduced := (loadAndReduceStep matrix used rows columns input store).1
    let enabled := (reduced.applyOp (complementPivotMaskOp columns)).applyOp (pivotFoundOp success)
    let decided := (selectUniqueFreeStep columns zero success enabled).1
    let built := (whenSuccessfulStep success _
      (buildCandidateStep matrix rows columns candidate zero) decided).1
    let checked := (whenSuccessfulStep success _
      (checkCandidateNonzeroStep candidate zero success) built).1
    let validated := (whenSuccessfulStep success _
      (validateSamplesStep input candidate success) checked).1
    (intoStep input matrix used rows columns candidate zero success output store).1 =
      (packOutputStep success candidate output validated).1 := rfl

private theorem caller_keys {outer : RuntimeCtx kind}
    (cells : Cells ctx (stateShapes rowCount width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) {shape : CShape}
    (other : CInputRef outer shape) :
    (cells.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.tail.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.tail.tail.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.tail.tail.tail.head.ref.key ∉ (transport.liftInput other).storageKeys) ∧
    (cells.tail.tail.tail.tail.tail.tail.head.ref.key ∉
      (transport.liftInput other).storageKeys) := by
  cases cells with
  | cons success tail0 =>
    cases tail0 with
    | cons zero tail1 =>
      cases tail1 with
      | cons candidate tail2 =>
        cases tail2 with
        | cons columns tail3 =>
          cases tail3 with
          | cons used tail4 =>
            cases tail4 with
            | cons matrix tail5 =>
              cases tail5 with
              | cons rows tail6 =>
                  exact ⟨separated.1 other, separated.2.2.1 other,
                    separated.2.2.2.1 other, separated.2.2.2.2.1 other,
                    separated.2.2.2.2.2.1 other, separated.2.2.2.2.2.2.1 other⟩

/-- The actual initialized body writes the original optional recovery of the caller's samples. -/
theorem gf2Into_cellOutput {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (output : CWriteRef outer (.option (.unsignedWord width)))
    (cells : Cells ctx (stateShapes rowCount width)) (distinct : cells.Distinct)
    (transport : Transport outer ctx) (separated : cells.TransportSeparated transport)
    (store : Store ctx) (initialized : cells.Initialized store)
    (samples : ClassicalAlgorithms.GF2.Samples rowCount width)
    (inputValues : ∀ row, ClassicalAlgorithms.TerminalDecode.eval
      (TerminalDecode.decodeInput .bigEndian ((store.read (transport.liftInput input)).get row)) =
        samples row) :
    (intoStep (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
      (transport.liftWrite output) store).1.read
        (.storage (transport.liftWrite output).toCStorageRef) =
      match ClassicalAlgorithms.GF2.recover? samples with
      | none => .optionNone
      | some word => .optionSome (.unsignedWord word) := by
  let matrix := cells.tail.tail.tail.tail.tail.head.ref
  let used := cells.tail.tail.tail.tail.head.ref
  let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
  let columns := cells.tail.tail.tail.head.ref
  let candidate := cells.tail.tail.head.ref
  let zero := cells.tail.head.ref
  let success := cells.head.ref
  let original := transport.liftInput input
  let result := ClassicalAlgorithms.GF2.reduce samples
  let reduced := (loadAndReduceStep matrix used rows columns original store).1
  let enabled := (reduced.applyOp (complementPivotMaskOp columns)).applyOp (pivotFoundOp success)
  let decided := (selectUniqueFreeStep columns zero success enabled).1
  have decision := gf2Decision_cellValues input cells distinct transport separated store
    initialized samples inputValues
  have keys := caller_keys cells transport separated input
  have candidateSuccess := typed_avoid candidate success (by intro same; cases same)
  have successCandidate := typed_avoid success candidate (by intro same; cases same)
  have candidateZero : candidate.key ≠ zero.key := by
    cases cells with
    | cons success tail0 =>
      cases tail0 with
      | cons zero tail1 =>
        cases tail1 with
        | cons candidate tail2 => exact distinct.2.1.1
  rw [into_store]
  change (packOutputStep success candidate (transport.liftWrite output)
    (whenSuccessfulStep success _ (validateSamplesStep original candidate success)
      (whenSuccessfulStep success _ (checkCandidateNonzeroStep candidate zero success)
        (whenSuccessfulStep success _
          (buildCandidateStep matrix rows columns candidate zero) decided).1).1).1).1.read _ = _
  cases choice : ClassicalAlgorithms.GF2.soleFreeColumn? result with
  | none =>
      have rejected : (decided.read (.storage success.toCStorageRef)).toBool = false := by
        apply Bool.eq_false_iff.mpr
        intro accepted
        obtain ⟨column, impossible⟩ := decision.1.mp accepted
        rw [choice] at impossible
        contradiction
      rw [when_false success _ _ decided rejected, when_false success _ _ decided rejected,
        when_false success _ _ decided rejected, gf2PackOutput_value]
      have pureNone : ClassicalAlgorithms.GF2.recover? samples = none := by
        have originalChoice : ClassicalAlgorithms.GF2.soleFreeColumn?
            (ClassicalAlgorithms.GF2.reduce samples) = none := choice
        simp only [ClassicalAlgorithms.GF2.recover?, originalChoice]
      rw [pureNone]
      change CShape.packOption (.product (decided.read (.storage success.toCStorageRef))
        (decided.read (.storage candidate.toCStorageRef))) = _
      rw [bit_value _ false rejected]
      rfl
  | some selected =>
      let word := ClassicalAlgorithms.GF2.backSubstitute result selected
      have accepted : (decided.read (.storage success.toCStorageRef)).toBool = true :=
        decision.1.mpr ⟨selected, choice⟩
      let built := (buildCandidateStep matrix rows columns candidate zero decided).1
      have builtCandidate : built.read (.storage candidate.toCStorageRef) =
          .unsignedWord word :=
        gf2BuildCandidate_cellValue cells distinct decided result selected choice
          decision.2.1 decision.2.2.1 decision.2.2.2.1 decision.2.2.2.2.1
      have builtSuccess : (built.read (.storage success.toCStorageRef)).toBool = true := by
        rw [gf2BuildCandidate_read_other matrix rows columns candidate zero decided _
          candidateSuccess]
        exact accepted
      have builtZero : built.read (.storage zero.toCStorageRef) = CShape.wordOfNat width 0 :=
        (gf2BuildCandidate_read_other matrix rows columns candidate zero decided _
          (avoids candidate zero candidateZero)).trans decision.2.2.2.2.1
      have builtInput : built.read original = store.read original :=
        (gf2BuildCandidate_read_other matrix rows columns candidate zero decided original
          keys.2.1).trans (decision.2.2.2.2.2.2 input)
      have nonzero : word ≠ 0 := ClassicalAlgorithms.GF2.backSubstitute_ne_zero result selected
      have different : (built.read (.storage candidate.toCStorageRef)).toNat ≠
          (built.read (.storage zero.toCStorageRef)).toNat := by
        rw [builtCandidate, builtZero]
        change word.val ≠ 0 % 2 ^ width
        rw [Nat.zero_mod]
        exact fun same => nonzero (Fin.ext same)
      let checked := (checkCandidateNonzeroStep candidate zero success built).1
      have checkedSuccess : (checked.read (.storage success.toCStorageRef)).toBool = true := by
        rw [gf2CandidateNonzero_success candidate zero success built]
        simp only [builtSuccess, different, decide_false, Bool.not_false, Bool.and_self]
      have checkedCandidate : checked.read (.storage candidate.toCStorageRef) =
          .unsignedWord word :=
        (gf2CandidateNonzero_read_other candidate zero success built _
          successCandidate).trans builtCandidate
      have checkedInput : checked.read original = store.read original :=
        (gf2CandidateNonzero_read_other candidate zero success built original keys.1).trans
          builtInput
      have equations : ClassicalAlgorithms.GF2.satisfies? samples word = true :=
        (ClassicalAlgorithms.GF2.satisfies?_eq_true samples word).mpr
          (ClassicalAlgorithms.GF2.backSubstitute_satisfies_of_lookup_none samples selected
            (ClassicalAlgorithms.GF2.soleFreeColumn_lookup_none choice))
      let validated := (validateSamplesStep original candidate success checked).1
      have validatedSuccess :
          (validated.read (.storage success.toCStorageRef)).toBool = true := by
        have actual := gf2ValidationSamples_cellSuccess input cells transport separated checked
        have decoded : (fun row => ClassicalAlgorithms.TerminalDecode.eval
            (TerminalDecode.decodeInput .bigEndian ((checked.read original).get row))) = samples :=
          funext (fun row => by rw [checkedInput]; exact inputValues row)
        have decodedWord : (⟨(checked.read (.storage candidate.toCStorageRef)).toNat,
            (checked.read (.storage candidate.toCStorageRef)).toNat_lt⟩ :
              ClassicalAlgorithms.Word width) = word := by
          apply Fin.ext
          exact congrArg CShape.Value.toNat checkedCandidate
        change (validated.read (.storage success.toCStorageRef)).toBool =
          ((checked.read (.storage success.toCStorageRef)).toBool &&
            ClassicalAlgorithms.GF2.satisfies? (fun row => ClassicalAlgorithms.TerminalDecode.eval
              (TerminalDecode.decodeInput .bigEndian ((checked.read original).get row)))
                ⟨(checked.read (.storage candidate.toCStorageRef)).toNat,
                  (checked.read (.storage candidate.toCStorageRef)).toNat_lt⟩) at actual
        simpa only [checkedSuccess, decoded, decodedWord, equations, Bool.and_self] using actual
      have validatedCandidate : validated.read (.storage candidate.toCStorageRef) =
          .unsignedWord word :=
        (gf2ValidationSamples_read_other original candidate success checked _
          successCandidate).trans checkedCandidate
      rw [when_true success _ _ decided accepted, when_true success _ _ built builtSuccess,
        when_true success _ _ checked checkedSuccess, gf2PackOutput_value,
        ClassicalAlgorithms.GF2.recover?_of_soleFreeColumn samples choice]
      change CShape.packOption (.product (validated.read (.storage success.toCStorageRef))
        (validated.read (.storage candidate.toCStorageRef))) = _
      rw [bit_value _ true validatedSuccess, validatedCandidate]
      rfl

/-- Only the final output destination can change a transported structural caller read. -/
theorem gf2Into_cellFrame {outer : RuntimeCtx kind}
    (input : CInputRef outer (.fixedVector rowCount (.bits width)))
    (output : CWriteRef outer (.option (.unsignedWord width)))
    (cells : Cells ctx (stateShapes rowCount width)) (transport : Transport outer ctx)
    (separated : cells.TransportSeparated transport) (store : Store ctx)
    {shape : CShape} (other : CInputRef outer shape) (outputFree : output.key ∉ other.storageKeys) :
    (intoStep (transport.liftInput input) cells.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.tail.head.ref cells.tail.tail.tail.tail.tail.tail.head.ref
      cells.tail.tail.tail.head.ref cells.tail.tail.head.ref cells.tail.head.ref cells.head.ref
      (transport.liftWrite output) store).1.read (transport.liftInput other) =
        store.read (transport.liftInput other) := by
  let matrix := cells.tail.tail.tail.tail.tail.head.ref
  let used := cells.tail.tail.tail.tail.head.ref
  let rows := cells.tail.tail.tail.tail.tail.tail.head.ref
  let columns := cells.tail.tail.tail.head.ref
  let candidate := cells.tail.tail.head.ref
  let zero := cells.tail.head.ref
  let success := cells.head.ref
  let original := transport.liftInput input
  let observed := transport.liftInput other
  have keys := caller_keys cells transport separated other
  have finalFree : (transport.liftWrite output).key ∉ observed.storageKeys := by
    simpa only [observed, Transport.liftWrite_key, Transport.liftInput_storageKeys] using outputFree
  rw [into_store]
  refine (Store.read_applyOp_of_not_mem_storageKeys _
    (.packOption ctx (.product (.storage success.toCStorageRef)
      (.storage candidate.toCStorageRef)) (transport.liftWrite output)) observed finalFree).trans ?_
  rw [when_read success _ (validateSamplesStep original candidate success) observed
    (fun current => gf2ValidationSamples_read_other original candidate success current observed
      keys.1)]
  rw [when_read success _ (checkCandidateNonzeroStep candidate zero success) observed
    (fun current => gf2CandidateNonzero_read_other candidate zero success current observed keys.1)]
  rw [when_read success _ (buildCandidateStep matrix rows columns candidate zero) observed
    (fun current => gf2BuildCandidate_read_other matrix rows columns candidate zero current
      observed keys.2.1)]
  refine (gf2UniqueFree_read_other columns zero success _ observed keys.1).trans ?_
  refine (Store.read_applyOp_of_not_mem_storageKeys _ (pivotFoundOp success)
    observed keys.1).trans ?_
  refine (gf2ComplementPivotMask_read_other columns _ observed keys.2.2.1).trans ?_
  exact gf2LoadAndReduce_read_other matrix used rows columns original store observed
    keys.2.2.2.2.1 keys.2.2.2.1 keys.2.2.2.2.2 keys.2.2.1

end

end QuantumAlg.ClassicalRoutines.GF2.Native
