/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget

/-!
# Actual finite order-recovery unit depth

The serial dependency bound includes decoding, literal initialization, the
real native modular powers and the selected updates, followed by result packing.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open ClassicalAlgorithms.Modular

variable {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {modulusWidth width phaseBits : Nat}

/-- Whichever actual selection arm is taken has at most five dependent instructions. -/
lemma nativeRecovery_selection_unitDepth_le (cells : ScanCells ctx modulusWidth width)
    (remainder : CInputRef ctx (.unsignedWord width))
    (path : (selectCandidate (model := model) cells remainder).Path) :
    (selectCandidate (model := model) cells remainder).depth (fun _ => 1) path ≤ 5 := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change (advanceCursor (model := model) cells.cursor remainder cells.zero).Path at path
        change (advanceCursor (model := model) cells.cursor remainder cells.zero).depth
          (fun _ => 1) path ≤ 5
        rw [nativeCursor_advance_unitDepth]
      · change (acceptCursor (model := model) (cellRead cells.cursor.candidate)
          (cellRead cells.valid) cells.selected cells.accepted cells.cursor.active).Path at path
        change (acceptCursor (model := model) (cellRead cells.cursor.candidate)
          (cellRead cells.valid) cells.selected cells.accepted cells.cursor.active).depth
          (fun _ => 1) path ≤ 5
        rw [nativeCursor_accept_unitDepth]
        decide

/-- Candidate materialization, modular validation and selection all contribute to visit depth. -/
lemma nativeRecovery_visit_unitDepth_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (path : (visitWithDivision (model := model) spec base cells division).Path) :
    (visitWithDivision (model := model) spec base cells division).depth (fun _ => 1) path ≤
      2 * modulusWidth + 16 + 6 * width := by
  change (candidatePrefix (model := model) (cellRead cells.cursor.numerator)
    (cellRead cells.cursor.denominator)
    (cellRead cells.cursor.previous) (cellRead cells.cursor.older) division
    cells.cursor.candidate).depth (fun _ => 1) path.1 +
    ((validate (model := model) spec base (cellRead cells.cursor.candidate)
      cells.zero cells.one cells.power
      cells.positive cells.valid).depth (fun _ => 1) path.2.1 +
      (selectCandidate (model := model) cells
        (.second (cellRead division))).depth (fun _ => 1) path.2.2) ≤ _
  rw [nativeCandidatePrefix_unitDepth, nativeValidation_unitDepth]
  have powered := Modular.NativePower.nativePower_into_unitDepth_le (model := model)
    spec base
    (cellRead cells.cursor.candidate) cells.power path.2.1.1
  have selected := nativeRecovery_selection_unitDepth_le (model := model)
    cells (.second (cellRead division))
    path.2.2
  omega

/-- Lexical allocation adds no depth to the actual active visit. -/
lemma nativeRecovery_activeVisit_unitDepth_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (path : (activeVisit (model := model) spec base cells).Path) :
    (activeVisit (model := model) spec base cells).depth (fun _ => 1) path ≤
      2 * modulusWidth + 16 + 6 * width :=
  nativeRecovery_visit_unitDepth_le spec
    (base.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape width)
      ctx.canonicalFreshKey_fresh)
    (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape width)
      ctx.canonicalFreshKey_fresh) (scanDivisionCell ctx width) path

/-- Only the actual active branch contributes visit depth. -/
lemma nativeRecovery_slot_unitDepth_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (path : (scanSlot (model := model) spec base cells).Path) :
    (scanSlot (model := model) spec base cells).depth (fun _ => 1) path ≤
      2 * modulusWidth + 16 + 6 * width := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact Nat.zero_le _
      · exact nativeRecovery_activeVisit_unitDepth_le spec base cells path

/-- The actual finite path vector has the sum of its slot dependency depths. -/
lemma nativeRecovery_scan_unitDepth_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (count : Nat)
    (path : (scan (model := model) spec base cells count).Path) :
    (scan (model := model) spec base cells count).depth (fun _ => 1) path ≤
      count * (2 * modulusWidth + 16 + 6 * width) := by
  change 0 + ∑ index : Fin count,
    (scanSlot (model := model) spec base cells).depth (fun _ => 1) (path index) ≤ _
  rw [Nat.zero_add]
  calc
    _ ≤ ∑ _index : Fin count, (2 * modulusWidth + 16 + 6 * width) :=
      Finset.sum_le_sum fun index _ => nativeRecovery_slot_unitDepth_le spec base cells (path index)
    _ = _ := by simp

/-- Actual padded decoding, dyadic loading and three initialization writes are all charged. -/
lemma nativeRecovery_initialization_unitDepth_le (sample : CInputRef ctx (.bits phaseBits))
    (path : (initializeScan (model := model) ctx modulusWidth phaseBits sample).Path) :
    (initializeScan (model := model) ctx modulusWidth phaseBits sample).depth (fun _ => 1) path ≤
      4 * (phaseBits + 1) + 3 := by
  have decoded := TerminalDecode.terminalDecode_intoFromBitRefs_depth_le (model := model)
    .bigEndian
    (initialPhaseBitRefs ctx modulusWidth phaseBits sample)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator (fun _ => 1) path.1
  have loaded := ConstantWord.constantWord_depth_le (model := model)
    (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator (2 ^ phaseBits)
    (fun _ => 1) path.2.1
  change (decodeInitialNumerator (model := model) ctx modulusWidth phaseBits sample).depth
    (fun _ => 1) path.1 +
    ((ConstantWord.circuit (model := model)
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
      (2 ^ phaseBits)).depth (fun _ => 1) path.2.1 + (1 + (1 + 1))) ≤ _
  change (decodeInitialNumerator (model := model) ctx modulusWidth phaseBits sample).depth
    (fun _ => 1) path.1 ≤
    (phaseBits + 1) * (1 + 1) at decoded
  omega

/-- Complete actual recovery obeys its independent setup, scan and packing duration bound. -/
lemma nativeRecovery_into_unitDepth_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into (model := model) spec base sample output).Path) :
    (into (model := model) spec base sample output).depth (fun _ => 1) path ≤
      unitDepthBound modulusWidth phaseBits := by
  change (initializeScan (model := model) ctx modulusWidth phaseBits sample).depth
    (fun _ => 1) path.1 +
    ((scan (model := model) spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits)).depth
        (fun _ => 1) path.2.1 + 1) ≤ _
  have initialized := nativeRecovery_initialization_unitDepth_le (model := model)
    sample path.1
  have scanned := nativeRecovery_scan_unitDepth_le (model := model)
    spec.modulusSpec
    (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
    (recoveryCells ctx modulusWidth (phaseBits + 1))
    (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits) path.2.1
  unfold unitDepthBound
  change _ ≤ 2 * (phaseBits + 1) * (2 * modulusWidth + 16 + 6 * (phaseBits + 1)) at scanned
  omega

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
