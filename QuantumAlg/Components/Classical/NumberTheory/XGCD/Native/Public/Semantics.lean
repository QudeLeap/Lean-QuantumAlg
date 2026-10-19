/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Public
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.Packing.Placement
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Semantics
import all QuantumAlg.Components.Classical.NumberTheory.XGCD.Native.RawEngine.Correctness

/-!
# Exact public XGCD values from the actual raw engine and packing

Public narrowing preserves the original signed values because the finished
raw coefficients satisfy the original public range. Three fresh raw-result
cells supply distinctness internally. Their allocation, actual arithmetic,
five packing instructions and release yield one complete caller write, with
all quantum-reference blocks and chronological paths retained.
-/

namespace QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native

open Execution ClassicalWorkspace ClassicalAlgorithms.NumberTheory

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

private lemma public_signed_value
    (word : CShape.Word (PureXGCD.executionCoefficientWidth width))
    (value : BoundedSigned (coefficientWidth width))
    (decoded : decodeRawSignedWord word = value.toInt) :
    CShape.packBoundedSignedWord (coefficientWidth width)
      (CShape.wordResize (coefficientWidth width) word) = encodeSigned value := by
  have represented : RawSignedRepresents word (decodeRawSignedWord word) := by
    have actual := ofInt_rawSignedRepresents (PureXGCD.executionCoefficientWidth width)
      (decodeRawSignedWord word)
    simpa only [decodeRawSignedWord, BoundedSigned.ofInt_toInt, BoundedSigned.encode_decode,
      fixedWidthEncode_decode_word] using actual
  rw [decoded] at represented
  rw [wordResize_eq_ofInt_of_rawSignedRepresents
    (ClassicalAlgorithms.NumberTheory.XGCD.coefficientWidth_le_executionCoefficientWidth width)
    word value.toInt represented,
    BoundedSigned.ofInt_toInt]
  rfl

/-- Public narrowing and nominal packing return the original deterministic mathematical result. -/
lemma xgcdNativePackedRawValue_finalState (outputs : RawOutputs ctx width)
    (store : Store ctx) (input : PureXGCD.Input width)
    (stateMatches : outputs.MatchesState store (PureXGCD.finalState input)) :
    packedRawValue (store.read (GCD.cellRead outputs.gcd))
      (store.read (GCD.cellRead outputs.leftCoefficient))
      (store.read (GCD.cellRead outputs.rightCoefficient)) =
      encodeXGCDTuple ((PureXGCD.eval input).gcd,
        ((PureXGCD.eval input).leftCoefficient, (PureXGCD.eval input).rightCoefficient)) := by
  have values := xgcdNativeRawOutputs_finalState_values outputs store input
    stateMatches.1 stateMatches.2.1 stateMatches.2.2
  have gcdValue : store.read (GCD.cellRead outputs.gcd) = encodeWord (PureXGCD.eval input).gcd := by
    cases actual : store.read (GCD.cellRead outputs.gcd) with
    | unsignedWord bits =>
        apply congrArg CShape.Value.unsignedWord
        apply Fin.ext
        simpa only [actual, CShape.Value.toNat] using values.1
  rw [packedRawValue, gcdValue, public_signed_value _ _ values.2.1,
    public_signed_value _ _ values.2.2]
  rfl

/-- The public entry writes the original result and preserves the complete remaining store. -/
lemma xgcdNativePublicIntoResult_actualRecord
    {model : ExecutionModel}
      {environment : model.Environment} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}
    (input : CInputRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (result : CWriteRef ctx (XGCDOutputShape width)) :
    ∃ record : Store ctx × model.HiddenState → (Store ctx × model.HiddenState) × (publicIntoResult
      (model := model) input result).Path,
      (∀ (Reference : Register) {History : Type} [Fintype History]
        (state : State ctx Reference (model.HiddenState × History)),
        (publicIntoResult (model := model) input result).execute environment Reference state =
          state.mapClassical (fun entry =>
            let actual := record (entry.1, entry.2.1)
            (actual.1.1, (actual.1.2, (entry.2.2, actual.2))))) ∧
      ∀ before : Store ctx × model.HiddenState, (record before).1.1 = before.1.write result
        (encodeXGCDTuple ((PureXGCD.eval (GCD.decodeOperands (before.1.read input))).gcd,
          ((PureXGCD.eval (GCD.decodeOperands (before.1.read input))).leftCoefficient,
            (PureXGCD.eval (GCD.decodeOperands (before.1.read input))).rightCoefficient))) := by
  let Post (before after : Store ctx) : Prop :=
    after = before.write result
      (encodeXGCDTuple ((PureXGCD.eval (GCD.decodeOperands (before.read input))).gcd,
        ((PureXGCD.eval (GCD.decodeOperands (before.read input))).leftCoefficient,
          (PureXGCD.eval (GCD.decodeOperands (before.read input))).rightCoefficient)))
  apply withCells_actualRecord_post (environment := environment) ctx (publicRawShapes width)
    (fun cells _ transport _ => publicBody (model := model) (transport.liftInput input)
      (publicRawOutputs cells) (transport.liftWrite result)) Post
  intro inner cells distinct transport separated
  let outputs := publicRawOutputs cells
  let lifted := transport.liftInput input
  let target := transport.liftWrite result
  obtain ⟨rawRecord, rawEquation, rawCorrect⟩ := xgcdNativeRawEngine_actualRecord lifted outputs
    (xgcdNativePublicRawOutputs_distinct cells distinct)
  obtain ⟨packRecord, packEquation, packCorrect⟩ :=
    xgcdNativePackRawOutputs_actualRecord outputs target
  let record := Circuit.sequenceRecord (rawEngine (model := model) lifted outputs)
    (packRawOutputs (model := model) outputs target) rawRecord packRecord
  refine ⟨record, ?_, ?_⟩
  · intro reference history historyFinite state
    exact Circuit.execute_sequenceRecord
      (environment := environment) (rawEngine (model := model) lifted outputs)
      (packRawOutputs (model := model) outputs target) rawRecord packRecord rawEquation
        packEquation reference state
  · intro source before reads
    let rawAfter := (rawRecord before).1.1
    let final := (record before).1.1
    let returned := transport.restrict final
    have returnedReads : transport.ReadsAs returned final :=
      transport.workspaceTransport_restrict_readsAs final
    have finalValue : final = rawAfter.write target
        (encodeXGCDTuple ((PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).gcd,
          ((PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).leftCoefficient,
            (PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).rightCoefficient))) := by
      have packed := packCorrect (rawRecord before).1
      rw [xgcdNativePackedRawValue_finalState outputs rawAfter
        (GCD.decodeOperands (before.1.read lifted)) (rawCorrect before).2] at packed
      exact packed
    have rawFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
        rawAfter.read (transport.liftInput other) = before.1.read (transport.liftInput other) := by
      intro shape other
      have free : outputs.gcd.key ∉ (transport.liftInput other).storageKeys ∧
          outputs.leftCoefficient.key ∉ (transport.liftInput other).storageKeys ∧
          outputs.rightCoefficient.key ∉ (transport.liftInput other).storageKeys := by
        cases cells with
        | cons right rest =>
          cases rest with
          | cons left rest =>
            cases rest with
            | cons gcd rest =>
              cases rest
              exact ⟨separated.2.2.1 other, separated.2.1 other, separated.1 other⟩
      exact (rawCorrect before).1 (transport.liftInput other) free.1 free.2.1 free.2.2
    refine ⟨returned, ?_, returnedReads⟩
    apply Store.store_eq_write_of_read_frame source returned result
    · have resultRead : final.read (GCD.cellRead target) =
          returned.read (GCD.cellRead result) := returnedReads (GCD.cellRead result)
      have written := Store.read_write_same rawAfter target
        (encodeXGCDTuple ((PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).gcd,
          ((PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).leftCoefficient,
            (PureXGCD.eval (GCD.decodeOperands (before.1.read lifted))).rightCoefficient)))
      exact resultRead.symm.trans (by
        rw [finalValue]
        exact written.trans (by rw [show before.1.read lifted = source.read input from reads
          input]))
    · intro shape other resultFree
      let liftedOther := transport.liftInput (.storage other)
      have unchanged : final.read liftedOther = rawAfter.read liftedOther := by
        rw [finalValue]
        apply Store.read_write_of_not_mem_storageKeys
        rw [transport.liftInput_storageKeys]
        simpa only [target, transport.liftWrite_key, CInputRef.storageKeys,
          List.mem_singleton] using resultFree
      exact (returnedReads (.storage other)).symm.trans
        (unchanged.trans ((rawFrame (.storage other)).trans (reads (.storage other))))

end

end QuantumAlg.ClassicalRoutines.NumberTheory.XGCD.Native
