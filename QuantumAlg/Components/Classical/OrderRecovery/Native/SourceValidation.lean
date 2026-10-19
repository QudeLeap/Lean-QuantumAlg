/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan.Geometry
import all QuantumAlg.Util.Classical.OrderRecovery.CursorBounds

/-!
# Source validation from actual base and candidate reads

The already verified modular-power program reads the actual original base
and the actual materialized candidate. Its stored validation bit equals the
source's fitted-positive-modular-return predicate. Least order remains a
separate source theorem and is not claimed for arbitrary accepted samples.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth phaseBits : Nat}

/-- A fitted actual word with the stated natural value is its unique finite source encoding. -/
private lemma actual_candidate_word
    (value : CShape.Word (phaseBits + 1)) (candidate : Nat)
    (fits : candidate < 2 ^ (phaseBits + 1)) (actual : value.toNat = candidate) :
    value = .unsignedWord ⟨candidate, fits⟩ := by
  cases value with
  | unsignedWord word => exact congrArg CShape.Value.unsignedWord (Fin.ext actual)

/-- The real validation bit equals the original source predicate on its represented candidate. -/
lemma nativeScan_validation_matches_source
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (input : ClassicalAlgorithms.OrderRecovery.Input spec)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth (phaseBits + 1)) (separated : cells.Separated)
    (store : Store ctx) (candidate : Nat) (fits : candidate < 2 ^ (phaseBits + 1))
    (baseValue : store.read base = .canonicalResidue input.base)
    (candidateValue : (store.read (cellRead cells.cursor.candidate)).toNat = candidate)
    (zeroValue : (store.read cells.zero).toNat = 0)
    (oneValue : (store.read cells.one).toNat = 1) :
    (validateStep (model := model) spec.modulusSpec base (cellRead cells.cursor.candidate)
      cells.zero cells.one
      cells.power cells.positive cells.valid store).1.read (cellRead cells.valid) =
      .bit
        (ClassicalAlgorithms.OrderRecovery.validateCandidate spec input candidate) := by
  let powerInput : Pow.Input spec.modulusSpec (phaseBits + 1) :=
    ⟨input.baseResidue, ⟨candidate, fits⟩⟩
  have represented : Modular.NativePower.InputRepresents spec.modulusSpec base
      (cellRead cells.cursor.candidate) store powerInput := by
    refine ⟨?_, actual_candidate_word _ candidate fits candidateValue⟩
    exact baseValue
  have actual := nativeValidation_result (model := model) spec.modulusSpec base
    (cellRead cells.cursor.candidate)
    cells.zero cells.one cells.power cells.positive cells.valid
    (nativeScan_separated_keys cells separated 10 9 (by decide))
    (nativeScan_separated_keys cells separated 9 8 (by decide))
    (separated.oneFree _ (by simp [ScanCells.writeKeys]))
    (fun present => nativeScan_separated_keys cells separated 8 4 (by decide)
      (List.mem_singleton.mp present))
    (separated.zeroFree _ (by simp [ScanCells.writeKeys]))
    (separated.oneFree _ (by simp [ScanCells.writeKeys])) store powerInput represented
    zeroValue oneValue
  refine actual.trans ?_
  change CShape.Value.bit
    (decide (0 < candidate) && decide (input.base.val ^ candidate % spec.modulusSpec.modulus = 1)) =
      .bit (ClassicalAlgorithms.OrderRecovery.validateCandidate spec input candidate)
  apply congrArg CShape.Value.bit
  simp only [ClassicalAlgorithms.OrderRecovery.validateCandidate, fits,
    true_and, Nat.ModEq, Nat.mod_eq_of_lt (modulusSpec_one_lt spec.modulusSpec), Bool.decide_and]

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
