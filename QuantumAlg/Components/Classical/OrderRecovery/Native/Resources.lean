/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget

/-!
# Actual finite order-recovery native event bounds

Every bound is proved against the actual interpreter path. Inactive slots
emit no arithmetic; active slots charge the selected cursor update and real
square-and-multiply validation. The full allowance is independent of inputs.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open ClassicalAlgorithms.Modular

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth width phaseBits : Nat}

/-- Either stored validation result fits the same coordinatewise selection budget. -/
theorem nativeRecovery_selection_pool_le (cells : ScanCells ctx modulusWidth width)
    (remainder : CInputRef ctx (.unsignedWord width))
    (path : (selectCandidate cells remainder).Path) :
    (selectCandidate cells remainder).resourcePool path ≤ selectionEnvelope kind width := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change ResourcePool.ofList (rejectionEvents kind width) ≤ _
        exact ResourcePool.le_max_left _ _
      · change ResourcePool.ofList (acceptanceEvents kind width) ≤ _
        exact ResourcePool.le_max_right _ _

/-- Actual division and validation compose with the selected cursor update. -/
theorem nativeRecovery_visit_pool_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (path : (visitWithDivision spec base cells division).Path) :
    (visitWithDivision spec base cells division).resourcePool path ≤
      visitEnvelope kind modulusWidth width := by
  change ResourcePool.ofList
    ((candidatePrefix (cellRead cells.cursor.numerator) (cellRead cells.cursor.denominator)
      (cellRead cells.cursor.previous) (cellRead cells.cursor.older) division
      cells.cursor.candidate).eventTrace path.1 ++
      ((validate spec base (cellRead cells.cursor.candidate) cells.zero cells.one
        cells.power cells.positive cells.valid).eventTrace path.2.1 ++
        (selectCandidate cells (.second (cellRead division))).eventTrace path.2.2)) ≤ _
  rw [nativeCandidatePrefix_eventTrace, nativeValidation_eventTrace]
  simp only [ResourcePool.ofList_append, visitEnvelope]
  exact add_le_add le_rfl (add_le_add
    (add_le_add (Modular.NativePower.nativePower_into_pool_le spec base
      (cellRead cells.cursor.candidate) cells.power path.2.1.1) le_rfl)
    (nativeRecovery_selection_pool_le cells (.second (cellRead division)) path.2.2))

/-- The lexical division pair adds no event beyond its real visit. -/
theorem nativeRecovery_activeVisit_pool_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (path : (activeVisit spec base cells).Path) :
    (activeVisit spec base cells).resourcePool path ≤ visitEnvelope kind modulusWidth width :=
  nativeRecovery_visit_pool_le spec
    (base.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape width)
      ctx.canonicalFreshKey_fresh)
    (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape width)
      ctx.canonicalFreshKey_fresh) (scanDivisionCell ctx width) path

/-- A real inactive slot emits nothing; an active slot uses one visit allowance. -/
theorem nativeRecovery_slot_pool_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (path : (scanSlot spec base cells).Path) :
    (scanSlot spec base cells).resourcePool path ≤ visitEnvelope kind modulusWidth width := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact zero_le
      · exact nativeRecovery_activeVisit_pool_le spec base cells path

/-- Actual finite iteration consumes at most one independent allowance per slot. -/
theorem nativeRecovery_scan_pool_le (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (count : Nat) :
    ∀ path : (scan spec base cells count).Path,
      (scan spec base cells count).resourcePool path ≤
        ResourcePool.scale count (visitEnvelope kind modulusWidth width) := by
  induction count with
  | zero => intro path; exact le_rfl
  | succ count ih =>
      intro path
      change ResourcePool.ofList ((List.ofFn (fun index : Fin (count + 1) =>
        (scanSlot spec base cells).eventTrace (path index))).flatten) ≤ _
      rw [List.ofFn_succ, List.flatten_cons, ResourcePool.ofList_append, ResourcePool.scale_succ]
      exact add_le_add (nativeRecovery_slot_pool_le spec base cells (path 0))
        (ih (fun index => path index.succ))

/-- The actual padded decoder, constant loader and three initialization writes fit their ledger. -/
theorem nativeRecovery_initialization_pool_le (sample : CInputRef ctx (.bits phaseBits))
    (path : (initializeScan ctx modulusWidth phaseBits sample).Path) :
    (initializeScan ctx modulusWidth phaseBits sample).resourcePool path ≤
      initializationEnvelope kind modulusWidth (phaseBits + 1) := by
  change ResourcePool.ofList
    ((decodeInitialNumerator ctx modulusWidth phaseBits sample).eventTrace path.1 ++
      ((ConstantWord.circuit (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
        (2 ^ phaseBits)).eventTrace path.2.1 ++
        [.classicalOperation (.wordUnary .increment (phaseBits + 1)),
          .classicalOperation (.wordUnary .increment modulusWidth),
          .classicalOperation (.bit .not)])) ≤ _
  simp only [ResourcePool.ofList_append, initializationEnvelope]
  exact add_le_add
    (TerminalDecode.terminalDecode_intoFromBitRefs_pool_le .bigEndian
      (initialPhaseBitRefs ctx modulusWidth phaseBits sample)
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator path.1)
    (add_le_add (ConstantWord.constantWord_pool_le
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator (2 ^ phaseBits)
      path.2.1) le_rfl)

/-- The complete native body satisfies the fixed source-width budget on every path. -/
theorem nativeRecovery_body_pool_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (recoveryBody spec base sample output).Path) :
    (recoveryBody spec base sample output).resourcePool path ≤
      eventEnvelope kind modulusWidth phaseBits := by
  change ResourcePool.ofList
    ((initializeScan ctx modulusWidth phaseBits sample).eventTrace path.1 ++
      ((scan spec.modulusSpec
        (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
        (recoveryCells ctx modulusWidth (phaseBits + 1))
        (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits)).eventTrace
          path.2.1 ++
        [.classicalOperation (.nominalEncoding (.packOption (phaseBits + 1)))])) ≤ _
  simp only [ResourcePool.ofList_append, eventEnvelope]
  exact add_le_add (nativeRecovery_initialization_pool_le sample path.1)
    (add_le_add (nativeRecovery_scan_pool_le spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits) path.2.1) le_rfl)

/-- Matching scopes add no hidden native event to the complete actual recovery program. -/
theorem nativeRecovery_into_pool_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into spec base sample output).Path) :
    (into spec base sample output).resourcePool path ≤ eventEnvelope kind modulusWidth phaseBits :=
  nativeRecovery_body_pool_le spec base sample output path

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
