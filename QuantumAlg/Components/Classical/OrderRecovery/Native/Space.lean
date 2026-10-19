/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Construction
import all QuantumAlg.Components.Classical.OrderRecovery.Native.Budget
import all QuantumAlg.Components.Classical.Modular.NativePower.Full.Space

/-!
# Simultaneously live storage of native finite order recovery

Thirteen cursor fields persist across the scan. Each active visit adds one
division pair; its continuant product and modular-power scratch are used in
sequence. The proof follows actual visited contexts, retaining every original
quantum and classical coordinate and counting no execution-history label.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open ClassicalAlgorithms.Modular

noncomputable section

variable {kind : ProblemKind} {modulusWidth width phaseBits : Nat}

private def Fits (outer inner : RuntimeCtx kind) (bits : Nat) : Prop :=
  inner.residentSpace ≤ outer.residentSpace + SpacePool.ofShape (.bits bits) ∧
    inner.auxiliarySpace ≤ outer.auxiliarySpace + SpacePool.ofShape (.bits bits)

private lemma fits_self (ctx : RuntimeCtx kind) (bits : Nat) : Fits ctx ctx bits := by
  constructor <;> intro axis <;> cases axis <;> simp [SpacePool.ofShape]

private lemma fits_mono {outer inner : RuntimeCtx kind} {small large : Nat}
    (fit : Fits outer inner small) (bounded : small ≤ large) : Fits outer inner large := by
  constructor
  · intro axis
    have actual := fit.1 axis
    cases axis <;> simp [SpacePool.ofShape] at * <;> omega
  · intro axis
    have actual := fit.2 axis
    cases axis <;> simp [SpacePool.ofShape] at * <;> omega

private lemma fits_trans {outer middle inner : RuntimeCtx kind} {first second : Nat}
    (left : Fits outer middle first) (right : Fits middle inner second) :
    Fits outer inner (first + second) := by
  constructor
  · intro axis
    have a := left.1 axis
    have b := right.1 axis
    cases axis <;> simp [SpacePool.ofShape] at * <;> omega
  · intro axis
    have a := left.2 axis
    have b := right.2 axis
    cases axis <;> simp [SpacePool.ofShape] at * <;> omega

private lemma fits_workspace (ctx : RuntimeCtx kind) (key : StorageKey) (shape : CShape)
    (fresh : key ∉ ctx.keys) :
    Fits ctx (ctx.addWorkspace key shape fresh) shape.bitWidth := by
  constructor <;> intro axis <;> cases axis <;> simp [SpacePool.ofShape] <;> omega

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

private lemma candidate_visited_fit
    (numerator denominator previous older : CInputRef ctx (.unsignedWord width))
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (candidate : CWriteRef ctx (.unsignedWord width))
    (path : (candidatePrefix (model := model) numerator denominator previous older division
      candidate).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈
      (candidatePrefix (model := model) numerator denominator previous older division
        candidate).visitedContexts
        path) :
    Fits ctx visited width := by
  have member : visited ∈ [ctx, ctx,
      ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh,
      ctx.addWorkspace ctx.canonicalFreshKey (.unsignedWord width) ctx.canonicalFreshKey_fresh,
      ctx] := by
    simpa only [candidatePrefix, scopedContinuant, continuantBody, BitWord.instruction,
      Circuit.visitedContexts,
      List.cons_append, List.nil_append] using present
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl
  all_goals first | exact fits_self _ width | exact fits_workspace _ _ _ _

private lemma validation_visited_fit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (candidate zero : CInputRef ctx (.unsignedWord width))
    (one : CInputRef ctx (.unsignedWord modulusWidth))
    (power : CWriteRef ctx (.unsignedWord modulusWidth)) (positive valid : CWriteRef ctx .bit)
    (path : (validate (model := model) spec base candidate zero one power positive valid).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈
      (validate (model := model) spec base candidate zero one power positive valid).visitedContexts
      path) : Fits ctx visited (8 * modulusWidth + 2) := by
  have member : visited ∈ (Modular.NativePower.into (model := model) spec base candidate
    power).visitedContexts
      path.1 ++ [ctx, ctx, ctx] := by
    simpa only [validate, validationChecks, BitWord.instruction,
      Circuit.visitedContexts, List.cons_append,
      List.nil_append] using present
  rcases List.mem_append.mp member with powered | unchanged
  · have choices := Modular.NativePower.nativePower_into_visited spec base candidate power
      path.1 visited powered
    simp only [List.mem_cons, List.not_mem_nil, or_false] at choices
    rcases choices with rfl | rfl | rfl | rfl | rfl | rfl
    all_goals
      constructor <;> intro axis <;> cases model <;> cases axis <;>
        simp [Modular.NativePower.modulusCtx, Modular.NativePower.baseCtx,
          Modular.NativePower.powerCtx, Modular.NativePower.productCtx,
          Modular.NativePower.divisionCtx, Modular.NativePower.divisionShape,
          SpacePool.ofShape] <;> omega
  · have same : visited = ctx := by simpa using unchanged
    subst visited
    exact fits_self _ _

private lemma selection_visited_same (cells : ScanCells ctx modulusWidth width)
    (remainder : CInputRef ctx (.unsignedWord width))
    (path : (selectCandidate (model := model) cells remainder).Path) (visited : RuntimeCtx
      model.kind)
    (present : visited ∈ (selectCandidate (model := model) cells remainder).visitedContexts path) :
    visited = ctx := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · change visited ∈ [ctx, ctx, ctx, ctx, ctx] at present
        simpa using present
      · change visited ∈ [ctx, ctx, ctx] at present
        simpa using present

private lemma visit_visited_fit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width)
    (division : CWriteRef ctx (.product (.unsignedWord width) (.unsignedWord width)))
    (path : (visitWithDivision (model := model) spec base cells division).Path) (visited :
      RuntimeCtx model.kind)
    (present : visited ∈ (visitWithDivision (model := model) spec base cells
      division).visitedContexts path) :
    Fits ctx visited (max width (8 * modulusWidth + 2)) := by
  change visited ∈
    (candidatePrefix (model := model) (cellRead cells.cursor.numerator) (cellRead
      cells.cursor.denominator)
      (cellRead cells.cursor.previous) (cellRead cells.cursor.older) division
      cells.cursor.candidate).visitedContexts path.1 ++
    ((validate (model := model) spec base (cellRead cells.cursor.candidate) cells.zero cells.one
      cells.power
      cells.positive cells.valid).visitedContexts path.2.1 ++
      (selectCandidate (model := model) cells (.second (cellRead division))).visitedContexts
        path.2.2) at present
  rcases List.mem_append.mp present with first | rest
  · exact fits_mono (candidate_visited_fit _ _ _ _ _ _ path.1 visited first) (Nat.le_max_left _ _)
  · rcases List.mem_append.mp rest with validated | selected
    · exact fits_mono (validation_visited_fit _ _ _ _ _ _ _ _ path.2.1 visited validated)
        (Nat.le_max_right _ _)
    · rw [selection_visited_same cells (.second (cellRead division)) path.2.2 visited selected]
      exact fits_self _ _

private lemma active_visited_fit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (path : (activeVisit (model := model) spec base
      cells).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (activeVisit (model := model) spec base cells).visitedContexts path) :
    Fits ctx visited (2 * width + max width (8 * modulusWidth + 2)) := by
  change visited ∈ ctx :: ((placedVisit (model := model) spec base cells).visitedContexts path ++
    [ctx]) at present
  rcases List.mem_cons.mp present with rfl | later
  · exact fits_self _ _
  · rcases List.mem_append.mp later with inner | released
    · have divisionFit : Fits ctx (scanDivisionCtx ctx width) (2 * width) := by
        simpa [scanDivisionCtx, cursorDivisionShape, Nat.two_mul] using
          fits_workspace ctx ctx.canonicalFreshKey (cursorDivisionShape width)
            ctx.canonicalFreshKey_fresh
      exact fits_trans divisionFit (visit_visited_fit spec _ _ _ path visited inner)
    · have same := List.mem_singleton.mp released
      subst visited
      exact fits_self _ _

private lemma slot_visited_fit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (path : (scanSlot (model := model) spec base
      cells).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (scanSlot (model := model) spec base cells).visitedContexts path) :
    Fits ctx visited (2 * width + max width (8 * modulusWidth + 2)) := by
  rcases path with ⟨value, path⟩
  cases value with
  | bit value =>
      cases value
      · have same : visited = ctx := List.mem_singleton.mp present
        subst visited
        exact fits_self _ _
      · exact active_visited_fit spec base cells path visited present

private lemma scan_visited_fit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth width) (count : Nat)
    (path : (scan (model := model) spec base cells count).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (scan (model := model) spec base cells count).visitedContexts path) :
    Fits ctx visited (2 * width + max width (8 * modulusWidth + 2)) := by
  change visited ∈ ctx :: (List.ofFn (fun index : Fin count =>
    (scanSlot (model := model) spec base cells).visitedContexts (path index))).flatten at present
  rcases List.mem_cons.mp present with rfl | repeated
  · exact fits_self _ _
  · rcases List.mem_flatten.mp repeated with ⟨contexts, member, contains⟩
    rcases List.mem_ofFn.mp member with ⟨index, rfl⟩
    exact slot_visited_fit spec base cells (path index) visited contains

private lemma initialization_visited_same (sample : CInputRef ctx (.bits phaseBits))
    (path : (initializeScan (model := model) ctx modulusWidth phaseBits sample).Path) (visited :
      RuntimeCtx model.kind)
    (present : visited ∈ (initializeScan (model := model) ctx modulusWidth phaseBits
      sample).visitedContexts path) :
    visited = recoveryContext ctx modulusWidth (phaseBits + 1) := by
  have member : visited ∈ (decodeInitialNumerator (model := model) ctx modulusWidth phaseBits
    sample).visitedContexts
      path.1 ++
      ((ConstantWord.circuit (model := model) (recoveryCells ctx modulusWidth (phaseBits +
        1)).cursor.denominator
        (2 ^ phaseBits)).visitedContexts path.2.1 ++
        [recoveryContext ctx modulusWidth (phaseBits + 1),
          recoveryContext ctx modulusWidth (phaseBits + 1),
          recoveryContext ctx modulusWidth (phaseBits + 1)]) := by
    simpa only [initializeScan, BitWord.instruction, Circuit.visitedContexts,
      List.cons_append, List.nil_append]
      using present
  rcases List.mem_append.mp member with decoded | later
  · exact TerminalDecode.terminalDecode_fold_visited
      (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.numerator
      (List.ofFn (fun index => initialPhaseBitRefs ctx modulusWidth phaseBits sample
        (TerminalDecode.sourceIndex .bigEndian index))) path.1 visited decoded
  · rcases List.mem_append.mp later with loaded | initialized
    · exact ConstantWord.constantWord_fold_visited
        (recoveryCells ctx modulusWidth (phaseBits + 1)).cursor.denominator
        (List.ofFn (ConstantWord.constantBits (phaseBits + 1) (2 ^ phaseBits)))
        path.2.1 visited loaded
    · simpa using initialized

private lemma body_visited_fit
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (recoveryBody (model := model) spec base sample output).Path) (visited : RuntimeCtx
      model.kind)
    (present : visited ∈ (recoveryBody (model := model) spec base sample output).visitedContexts
      path) :
    Fits (recoveryContext ctx modulusWidth (phaseBits + 1)) visited
      (2 * (phaseBits + 1) + max (phaseBits + 1) (8 * modulusWidth + 2)) := by
  change visited ∈ (initializeScan (model := model) ctx modulusWidth phaseBits
    sample).visitedContexts path.1 ++
    ((scan (model := model) spec.modulusSpec
      (underRecoveryFields modulusWidth (phaseBits + 1) recoveryFields base)
      (recoveryCells ctx modulusWidth (phaseBits + 1))
      (ClassicalAlgorithms.OrderRecovery.finiteCandidateFuel phaseBits)).visitedContexts
        path.2.1 ++ [recoveryContext ctx modulusWidth (phaseBits + 1)]) at present
  rcases List.mem_append.mp present with initialized | later
  · rw [initialization_visited_same sample path.1 visited initialized]
    exact fits_self _ _
  · rcases List.mem_append.mp later with scanned | packed
    · exact scan_visited_fit spec.modulusSpec _ _ _ path.2.1 visited scanned
    · rw [List.mem_singleton.mp packed]
      exact fits_self _ _

private def fieldBits (modulusWidth width : Nat) (fields : List RecoveryField) : Nat :=
  (fields.map (fun field => (recoveryFieldShape modulusWidth width field).bitWidth)).sum

omit [BitWord.Selected model] in
private lemma scope_visited_fit (ctx : RuntimeCtx model.kind) (modulusWidth width : Nat)
    (fields : List RecoveryField)
    (body : Circuit model (fieldsContext ctx modulusWidth width fields)
      (fieldsContext ctx modulusWidth width fields)) (extra : Nat)
    (bounded : ∀ (path : body.Path) (visited : RuntimeCtx model.kind),
      visited ∈ body.visitedContexts path →
        Fits (fieldsContext ctx modulusWidth width fields) visited extra)
    (path : (scopeRecoveryFields (model := model) ctx modulusWidth width fields body).Path)
    (visited : RuntimeCtx model.kind)
    (present : visited ∈ (scopeRecoveryFields (model := model) ctx modulusWidth width fields
      body).visitedContexts
      path) : Fits ctx visited (fieldBits modulusWidth width fields + extra) := by
  induction fields generalizing ctx with
  | nil =>
      change Fits ctx visited (0 + extra)
      rw [Nat.zero_add]
      exact bounded path visited present
  | cons field rest ih =>
      change visited ∈ ctx ::
        ((scopeRecoveryFields
          (ctx.addWorkspace ctx.canonicalFreshKey (recoveryFieldShape modulusWidth width field)
            ctx.canonicalFreshKey_fresh) modulusWidth width rest body).visitedContexts path ++
          [ctx]) at present
      rcases List.mem_cons.mp present with same | later
      · rw [same]
        exact fits_self _ _
      · rcases List.mem_append.mp later with inside | released
        · have inner := ih _ body bounded path inside
          have combined := fits_trans
            (fits_workspace ctx ctx.canonicalFreshKey (recoveryFieldShape modulusWidth width field)
              ctx.canonicalFreshKey_fresh) inner
          simpa only [fieldBits, List.map_cons, List.sum_cons, Nat.add_assoc] using combined
        · rw [List.mem_singleton.mp released]
          exact fits_self _ _

/-- Every actually visited context respects the fixed simultaneous classical scratch allowance. -/
lemma nativeRecovery_into_visited_space_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into (model := model) spec base sample output).Path) (visited : RuntimeCtx model.kind)
    (present : visited ∈ (into (model := model) spec base sample output).visitedContexts path) :
    visited.residentSpace ≤ ctx.residentSpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) ∧
      visited.auxiliarySpace ≤ ctx.auxiliarySpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) := by
  have actual := scope_visited_fit ctx modulusWidth (phaseBits + 1) recoveryFields
    (recoveryBody (model := model) spec base sample output)
    (2 * (phaseBits + 1) + max (phaseBits + 1) (8 * modulusWidth + 2))
    (body_visited_fit spec base sample output) path visited present
  have budgetEq : fieldBits modulusWidth (phaseBits + 1) recoveryFields +
      (2 * (phaseBits + 1) + max (phaseBits + 1) (8 * modulusWidth + 2)) =
        extraClassicalBits modulusWidth phaseBits := by
    simp [fieldBits, recoveryFieldShape, extraClassicalBits]
    omega
  rw [budgetEq] at actual
  exact actual

/-- The complete native recovery peak retains original storage and adds only the stated bits. -/
lemma nativeRecovery_into_resident_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into (model := model) spec base sample output).Path) :
    (into (model := model) spec base sample output).peakResidentSpace path ≤
      ctx.residentSpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) := by
  apply Circuit.peakResidentSpace_le_of_visited
  intro visited present
  exact (nativeRecovery_into_visited_space_le spec base sample output path visited present).1

/-- The same actual execution gives the auxiliary peak, without counting history as live memory. -/
lemma nativeRecovery_into_auxiliary_le
    (spec : ClassicalAlgorithms.OrderRecovery.Spec modulusWidth phaseBits)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (sample : CInputRef ctx (.bits phaseBits)) (output : CWriteRef ctx (outputShape phaseBits))
    (path : (into (model := model) spec base sample output).Path) :
    (into (model := model) spec base sample output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace +
        SpacePool.ofShape (.bits (extraClassicalBits modulusWidth phaseBits)) := by
  apply Circuit.peakAuxiliarySpace_le_of_visited
  intro visited present
  exact (nativeRecovery_into_visited_space_le spec base sample output path visited present).2

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
