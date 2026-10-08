/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.GF2.Native
import all QuantumAlg.Components.Classical.GF2.Native.Echelon.Space
import all QuantumAlg.Components.Classical.GF2.Native.Candidate.Space
import all QuantumAlg.Components.Classical.GF2.Native.Validation.Space

/-!
# Actual simultaneous space of complete same-context GF(2) recovery

The existing loading, search, decision, candidate and validation scopes have
sequential lives. Their proven space allowances combine by a maximum, while
every original caller-context cell remains present. These are safe bounds
for every actual path, not claims of a tight reachable global maximum.
-/

namespace QuantumAlg.ClassicalRoutines.GF2.Native

open Execution

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {rowCount width : Nat}

/-- The original search and candidate scratch allowances share their sequential lifetime. -/
def intoScratchSpace (model : ExecutionModel)
    (rowCount width : Nat) : SpacePool model.kind :=
  SpacePool.max (pivotMaskSpace (model := model) rowCount width +
    (SpacePool.ofShape .bit + SpacePool.ofShape .bit))
      (SpacePool.ofShape (.unsignedWord width) +
        (SpacePool.ofShape .bit + SpacePool.ofShape (.unsignedWord width)))

omit [BitWord.Selected model] in
private theorem when_resident (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (budget : SpacePool model.kind) (entry : ctx.residentSpace ≤ budget)
    (bound : ∀ path, body.peakResidentSpace path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).peakResidentSpace path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (SpacePool.max_zero _).le.trans entry
      · exact bound path

omit [BitWord.Selected model] in
private theorem serial_resident (first second : Circuit model ctx ctx)
    (budget : SpacePool model.kind)
    (left : ∀ path, first.peakResidentSpace path ≤ budget)
    (right : ∀ path, second.peakResidentSpace path ≤ budget)
    (path : (first.seq second).Path) : (first.seq second).peakResidentSpace path ≤ budget :=
  (Circuit.peakResidentSpace_seq first second path).le.trans
    (SpacePool.max_le (left path.1) (right path.2))

omit [BitWord.Selected model] in
private theorem when_auxiliary (success : CWriteRef ctx .bit) (body : Circuit model ctx ctx)
    (budget : SpacePool model.kind) (entry : ctx.auxiliarySpace ≤ budget)
    (bound : ∀ path, body.peakAuxiliarySpace path ≤ budget)
    (path : (whenSuccessful success body).Path) :
    (whenSuccessful success body).peakAuxiliarySpace path ≤ budget := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · exact (SpacePool.max_zero _).le.trans entry
      · exact bound path

omit [BitWord.Selected model] in
private theorem serial_auxiliary (first second : Circuit model ctx ctx)
    (budget : SpacePool model.kind)
    (left : ∀ path, first.peakAuxiliarySpace path ≤ budget)
    (right : ∀ path, second.peakAuxiliarySpace path ≤ budget)
    (path : (first.seq second).Path) : (first.seq second).peakAuxiliarySpace path ≤ budget :=
  (Circuit.peakAuxiliarySpace_seq first second path).le.trans
    (SpacePool.max_le (left path.1) (right path.2))

variable (input : CInputRef ctx (.fixedVector rowCount (.bits width)))
  (matrix : CWriteRef ctx (.fixedVector rowCount (.unsignedWord width)))
  (used : CWriteRef ctx (.unsignedWord rowCount))
  (rows : CWriteRef ctx (.fixedVector width (.unsignedWord rowCount)))
  (columns candidate zero : CWriteRef ctx (.unsignedWord width))
  (success : CWriteRef ctx .bit) (output : CWriteRef ctx (.option (.unsignedWord width)))

/-- Sequential scopes share space while retaining the full resident context. -/
theorem gf2Into_resident_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).peakResidentSpace path ≤
      intoScratchSpace model rowCount width + ctx.residentSpace := by
  have entry : ctx.residentSpace ≤ intoScratchSpace model rowCount width + ctx.residentSpace :=
    fun _axis => Nat.le_add_left _ _
  have search : ∀ current,
      (loadAndReduce input matrix used rows columns).peakResidentSpace current ≤
      intoScratchSpace model rowCount width + ctx.residentSpace := by
    intro current
    refine (gf2LoadAndReduce_resident_le input matrix used rows columns current).trans ?_
    intro axis
    change pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis)) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.residentSpace axis
    omega
  have decision : ∀ current, (selectUniqueFree columns zero success).peakResidentSpace current ≤
      intoScratchSpace model rowCount width + ctx.residentSpace := by
    intro current
    refine (gf2UniqueFree_resident columns zero success current).le.trans ?_
    intro axis
    change SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.residentSpace axis
    omega
  have candidateBound : ∀ current,
      (buildCandidate matrix rows columns candidate zero).peakResidentSpace current ≤
        intoScratchSpace model rowCount width + ctx.residentSpace := by
    intro current
    refine (gf2BuildCandidate_resident_le matrix rows columns candidate zero current).trans ?_
    intro axis
    change SpacePool.ofShape (.unsignedWord width) axis +
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis)) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.residentSpace axis
    omega
  have nonzero : ∀ current,
      (checkCandidateNonzero candidate zero success).peakResidentSpace current ≤
      intoScratchSpace model rowCount width + ctx.residentSpace := by
    intro current
    refine (gf2CandidateNonzero_resident candidate zero success current).le.trans ?_
    intro axis
    change SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.residentSpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.residentSpace axis
    omega
  have validation : ∀ current,
      (validateSamples input candidate success).peakResidentSpace current ≤
      intoScratchSpace model rowCount width + ctx.residentSpace := by
    intro current
    refine (gf2ValidationSamples_resident_le input candidate success current).trans ?_
    intro axis
    change SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.residentSpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.residentSpace axis
    omega
  exact (serial_resident _ _ _ search (serial_resident _ _ _
    (fun current => (Circuit.peakResidentSpace_classical _ current).le.trans entry)
    (serial_resident _ _ _
      (fun current => (Circuit.peakResidentSpace_classical _ current).le.trans entry)
      (serial_resident _ _ _ decision
        (serial_resident _ _ _ (when_resident success _ _ entry candidateBound)
          (serial_resident _ _ _ (when_resident success _ _ entry nonzero)
            (serial_resident _ _ _ (when_resident success _ _ entry validation)
              (fun current => (Circuit.peakResidentSpace_classical _ current).le.trans
                entry)))))))) path

/-- Sequential scopes share space while retaining the full auxiliary context. -/
theorem gf2Into_auxiliary_le
    (path : (into input matrix used rows columns candidate zero success output).Path) :
    (into input matrix used rows columns candidate zero success output).peakAuxiliarySpace path ≤
      intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
  have entry : ctx.auxiliarySpace ≤ intoScratchSpace model rowCount width + ctx.auxiliarySpace :=
    fun _axis => Nat.le_add_left _ _
  have search : ∀ current,
      (loadAndReduce input matrix used rows columns).peakAuxiliarySpace current ≤
      intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
    intro current
    refine (gf2LoadAndReduce_auxiliary_le input matrix used rows columns current).trans ?_
    intro axis
    change pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis)) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.auxiliarySpace axis
    omega
  have decision : ∀ current, (selectUniqueFree columns zero success).peakAuxiliarySpace current ≤
      intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
    intro current
    refine (gf2UniqueFree_auxiliary columns zero success current).le.trans ?_
    intro axis
    change SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.auxiliarySpace axis
    omega
  have candidateBound : ∀ current,
      (buildCandidate matrix rows columns candidate zero).peakAuxiliarySpace current ≤
        intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
    intro current
    refine (gf2BuildCandidate_auxiliary_le matrix rows columns candidate zero current).trans ?_
    intro axis
    change SpacePool.ofShape (.unsignedWord width) axis +
        (SpacePool.ofShape .bit axis +
          (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis)) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.auxiliarySpace axis
    omega
  have nonzero : ∀ current,
      (checkCandidateNonzero candidate zero success).peakAuxiliarySpace current ≤
      intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
    intro current
    refine (gf2CandidateNonzero_auxiliary candidate zero success current).le.trans ?_
    intro axis
    change SpacePool.ofShape .bit axis +
        (SpacePool.ofShape (.unsignedWord width) axis + ctx.auxiliarySpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.auxiliarySpace axis
    omega
  have validation : ∀ current,
      (validateSamples input candidate success).peakAuxiliarySpace current ≤
      intoScratchSpace model rowCount width + ctx.auxiliarySpace := by
    intro current
    refine (gf2ValidationSamples_auxiliary_le input candidate success current).trans ?_
    intro axis
    change SpacePool.ofShape .bit axis + (SpacePool.ofShape .bit axis + ctx.auxiliarySpace axis) ≤
      max (pivotMaskSpace (model := model) rowCount width axis +
        (SpacePool.ofShape .bit axis + SpacePool.ofShape .bit axis))
        (SpacePool.ofShape (.unsignedWord width) axis + (SpacePool.ofShape .bit axis +
          SpacePool.ofShape (.unsignedWord width) axis)) + ctx.auxiliarySpace axis
    omega
  exact (serial_auxiliary _ _ _ search (serial_auxiliary _ _ _
    (fun current => (Circuit.peakAuxiliarySpace_classical _ current).le.trans entry)
    (serial_auxiliary _ _ _
      (fun current => (Circuit.peakAuxiliarySpace_classical _ current).le.trans entry)
      (serial_auxiliary _ _ _ decision
        (serial_auxiliary _ _ _ (when_auxiliary success _ _ entry candidateBound)
          (serial_auxiliary _ _ _ (when_auxiliary success _ _ entry nonzero)
            (serial_auxiliary _ _ _ (when_auxiliary success _ _ entry validation)
              (fun current => (Circuit.peakAuxiliarySpace_classical _ current).le.trans
                entry)))))))) path

end QuantumAlg.ClassicalRoutines.GF2.Native
