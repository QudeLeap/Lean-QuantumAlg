/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Persistent
import all QuantumAlg.Core.Execution.Local.Retained
import all QuantumAlg.Core.Execution.Local.Retained.Sequence
import all QuantumAlg.Core.Execution.Local.Retained.Cleanup

/-!
# Local execution beside the existing persistent recovery cells

The original seven recovery cells remain resident while the same local
quantum sampling instructions run. Their actual accepted, selected, inverse,
candidate, reconstruction, target-acceptance and scalar roles use the original
context and keys. This extension emits no allocation; the caller retains the
cells once before entering its finite sampling and candidate-check loop.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

noncomputable section

open Execution ClassicalAlgorithms.EllipticCurve

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind}

private def besideCell (localCode : { code : Circuit model ctx ctx // code.IsLocal })
    (shape : CShape) :
    { code : Circuit model
        (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh)
        (ctx.addRetained ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh) //
      code.IsLocal } :=
  ⟨Circuit.underRetained localCode.val localCode.property ctx.canonicalFreshKey shape
    ctx.canonicalFreshKey_fresh,
    Circuit.underRetained_isLocal localCode.val localCode.property ctx.canonicalFreshKey shape
      ctx.canonicalFreshKey_fresh⟩

/-- One verified local reset remains a physical reset beside one retained cell. -/
private theorem besideCell_restartCleanup
    (localCode : { code : Circuit model ctx ctx // code.IsLocal })
    (shape : CShape) (cleanup : Circuit.RestartCleanup localCode.val)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (besideCell localCode shape).val :=
  Circuit.underRetained_restartCleanup localCode.val localCode.property
    ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh cleanup noBorrowed

/-- One persistent classical cell preserves a caller-selected quantum seed. -/
private theorem besideCell_reinitializedAt
    (localCode : { code : Circuit model ctx ctx // code.IsLocal })
    (shape : CShape)
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt localCode.val seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (besideCell localCode shape).val seed :=
  Circuit.underRetained_reinitializedAt localCode.val localCode.property
    ctx.canonicalFreshKey shape ctx.canonicalFreshKey_fresh seed fixed noBorrowed

private theorem besideCell_seq {outer : RuntimeCtx model.kind}
    (whole left right : { code : Circuit model outer outer // code.IsLocal })
    (same : whole.val = left.val.seq right.val) (shape : CShape) :
    (besideCell whole shape).val =
      (besideCell left shape).val.seq (besideCell right shape).val := by
  have aligned : whole = ⟨left.val.seq right.val, ⟨left.property, right.property⟩⟩ :=
    Subtype.ext same
  subst whole
  exact Circuit.underRetained_seq left.val right.val left.property right.property
    ⟨left.property, right.property⟩ outer.canonicalFreshKey shape
      outer.canonicalFreshKey_fresh

private def besidePersistent (code : Circuit model ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    { extended : Circuit model (persistentCtx ctx width scalarWidth)
        (persistentCtx ctx width scalarWidth) // extended.IsLocal } :=
  let accepted := besideCell ⟨code, supported⟩ .bit
  let selected := besideCell accepted (.unsignedWord scalarWidth)
  let inverse := besideCell selected .bit
  let candidate := besideCell inverse (.unsignedWord scalarWidth)
  let reconstruction := besideCell candidate .bit
  let verified := besideCell reconstruction .bit
  besideCell verified (PointShape width)

/-- Run the same local instructions beside all seven existing recovery destinations. -/
def underPersistent (code : Circuit model ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    Circuit model (persistentCtx ctx width scalarWidth) (persistentCtx ctx width scalarWidth) :=
  (besidePersistent code supported width scalarWidth).val

/-- Persistent classical cells preserve the original ordered local sequence. -/
theorem underPersistent_seq (first second : Circuit model ctx ctx)
    (firstLocal : first.IsLocal) (secondLocal : second.IsLocal)
    (width scalarWidth : Nat) :
    underPersistent (first.seq second) ⟨firstLocal, secondLocal⟩ width scalarWidth =
      (underPersistent first firstLocal width scalarWidth).seq
        (underPersistent second secondLocal width scalarWidth) := by
  let whole₀ : { code : Circuit model ctx ctx // code.IsLocal } :=
    ⟨first.seq second, ⟨firstLocal, secondLocal⟩⟩
  let left₀ : { code : Circuit model ctx ctx // code.IsLocal } := ⟨first, firstLocal⟩
  let right₀ : { code : Circuit model ctx ctx // code.IsLocal } := ⟨second, secondLocal⟩
  let whole₁ := besideCell whole₀ .bit
  let left₁ := besideCell left₀ .bit
  let right₁ := besideCell right₀ .bit
  have step₁ : whole₁.val = left₁.val.seq right₁.val :=
    besideCell_seq whole₀ left₀ right₀ rfl .bit
  let whole₂ := besideCell whole₁ (.unsignedWord scalarWidth)
  let left₂ := besideCell left₁ (.unsignedWord scalarWidth)
  let right₂ := besideCell right₁ (.unsignedWord scalarWidth)
  have step₂ : whole₂.val = left₂.val.seq right₂.val :=
    besideCell_seq whole₁ left₁ right₁ step₁ (.unsignedWord scalarWidth)
  let whole₃ := besideCell whole₂ .bit
  let left₃ := besideCell left₂ .bit
  let right₃ := besideCell right₂ .bit
  have step₃ : whole₃.val = left₃.val.seq right₃.val :=
    besideCell_seq whole₂ left₂ right₂ step₂ .bit
  let whole₄ := besideCell whole₃ (.unsignedWord scalarWidth)
  let left₄ := besideCell left₃ (.unsignedWord scalarWidth)
  let right₄ := besideCell right₃ (.unsignedWord scalarWidth)
  have step₄ : whole₄.val = left₄.val.seq right₄.val :=
    besideCell_seq whole₃ left₃ right₃ step₃ (.unsignedWord scalarWidth)
  let whole₅ := besideCell whole₄ .bit
  let left₅ := besideCell left₄ .bit
  let right₅ := besideCell right₄ .bit
  have step₅ : whole₅.val = left₅.val.seq right₅.val :=
    besideCell_seq whole₄ left₄ right₄ step₄ .bit
  let whole₆ := besideCell whole₅ .bit
  let left₆ := besideCell left₅ .bit
  let right₆ := besideCell right₅ .bit
  have step₆ : whole₆.val = left₆.val.seq right₆.val :=
    besideCell_seq whole₅ left₅ right₅ step₅ .bit
  let whole₇ := besideCell whole₆ (PointShape width)
  let left₇ := besideCell left₆ (PointShape width)
  let right₇ := besideCell right₆ (PointShape width)
  have step₇ : whole₇.val = left₇.val.seq right₇.val :=
    besideCell_seq whole₆ left₆ right₆ step₆ (PointShape width)
  exact step₇

/-- The extension keeps the complete persistent context throughout each actual instruction. -/
theorem underPersistent_isLocal (code : Circuit model ctx ctx) (supported : code.IsLocal)
    (width scalarWidth : Nat) :
    (underPersistent code supported width scalarWidth).IsLocal :=
  (besidePersistent code supported width scalarWidth).property

/-- Physical cleanup survives all seven retained recovery cells. Each step
transports the complete output block, including the existing cell and history. -/
theorem underPersistent_restartCleanup (code : Circuit model ctx ctx)
    (supported : code.IsLocal) (width scalarWidth : Nat)
    (cleanup : Circuit.RestartCleanup code)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.RestartCleanup (underPersistent code supported width scalarWidth) := by
  let original : { code : Circuit model ctx ctx // code.IsLocal } := ⟨code, supported⟩
  have emptyAt (outer : RuntimeCtx model.kind)
      (empty : outer.borrowedQuantumWires = []) (shape : CShape) :
      (outer.addRetained outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh).borrowedQuantumWires = [] := by
    simpa only [RuntimeCtx.borrowedQuantumWires_addRetained] using empty
  let accepted := besideCell original .bit
  have clean₁ : Circuit.RestartCleanup accepted.val :=
    besideCell_restartCleanup original .bit cleanup noBorrowed
  have empty₁ := emptyAt ctx noBorrowed .bit
  let selected := besideCell accepted (.unsignedWord scalarWidth)
  have clean₂ : Circuit.RestartCleanup selected.val :=
    besideCell_restartCleanup accepted (.unsignedWord scalarWidth) clean₁ empty₁
  have empty₂ := emptyAt _ empty₁ (.unsignedWord scalarWidth)
  let inverse := besideCell selected .bit
  have clean₃ : Circuit.RestartCleanup inverse.val :=
    besideCell_restartCleanup selected .bit clean₂ empty₂
  have empty₃ := emptyAt _ empty₂ .bit
  let candidate := besideCell inverse (.unsignedWord scalarWidth)
  have clean₄ : Circuit.RestartCleanup candidate.val :=
    besideCell_restartCleanup inverse (.unsignedWord scalarWidth) clean₃ empty₃
  have empty₄ := emptyAt _ empty₃ (.unsignedWord scalarWidth)
  let reconstruction := besideCell candidate .bit
  have clean₅ : Circuit.RestartCleanup reconstruction.val :=
    besideCell_restartCleanup candidate .bit clean₄ empty₄
  have empty₅ := emptyAt _ empty₄ .bit
  let verified := besideCell reconstruction .bit
  have clean₆ : Circuit.RestartCleanup verified.val :=
    besideCell_restartCleanup reconstruction .bit clean₅ empty₅
  have empty₆ := emptyAt _ empty₅ .bit
  have clean₇ : Circuit.RestartCleanup (besideCell verified (PointShape width)).val :=
    besideCell_restartCleanup verified (PointShape width) clean₆ empty₆
  exact clean₇

/-- The original fixed reset label survives all seven actual persistent
recovery cells, rather than being replaced by an existential witness. -/
theorem underPersistent_reinitializedAt (code : Circuit model ctx ctx)
    (supported : code.IsLocal) (width scalarWidth : Nat)
    (seed : ctx.quantumLayout.SelectedBasis ctx.borrowedSelectionᶜ)
    (fixed : Circuit.ReinitializedAt code seed)
    (noBorrowed : ctx.borrowedQuantumWires = []) :
    Circuit.ReinitializedAt (underPersistent code supported width scalarWidth) seed := by
  let original : { code : Circuit model ctx ctx // code.IsLocal } := ⟨code, supported⟩
  have emptyAt (outer : RuntimeCtx model.kind)
      (empty : outer.borrowedQuantumWires = []) (shape : CShape) :
      (outer.addRetained outer.canonicalFreshKey shape
        outer.canonicalFreshKey_fresh).borrowedQuantumWires = [] := by
    simpa only [RuntimeCtx.borrowedQuantumWires_addRetained] using empty
  let accepted := besideCell original .bit
  have fixed₁ : Circuit.ReinitializedAt accepted.val seed :=
    besideCell_reinitializedAt original .bit seed fixed noBorrowed
  have empty₁ := emptyAt ctx noBorrowed .bit
  let selected := besideCell accepted (.unsignedWord scalarWidth)
  have fixed₂ : Circuit.ReinitializedAt selected.val seed :=
    besideCell_reinitializedAt accepted (.unsignedWord scalarWidth) seed fixed₁ empty₁
  have empty₂ := emptyAt _ empty₁ (.unsignedWord scalarWidth)
  let inverse := besideCell selected .bit
  have fixed₃ : Circuit.ReinitializedAt inverse.val seed :=
    besideCell_reinitializedAt selected .bit seed fixed₂ empty₂
  have empty₃ := emptyAt _ empty₂ .bit
  let candidate := besideCell inverse (.unsignedWord scalarWidth)
  have fixed₄ : Circuit.ReinitializedAt candidate.val seed :=
    besideCell_reinitializedAt inverse (.unsignedWord scalarWidth) seed fixed₃ empty₃
  have empty₄ := emptyAt _ empty₃ (.unsignedWord scalarWidth)
  let reconstruction := besideCell candidate .bit
  have fixed₅ : Circuit.ReinitializedAt reconstruction.val seed :=
    besideCell_reinitializedAt candidate .bit seed fixed₄ empty₄
  have empty₅ := emptyAt _ empty₄ .bit
  let verified := besideCell reconstruction .bit
  have fixed₆ : Circuit.ReinitializedAt verified.val seed :=
    besideCell_reinitializedAt reconstruction .bit seed fixed₅ empty₅
  have empty₆ := emptyAt _ empty₅ .bit
  exact besideCell_reinitializedAt verified (PointShape width) seed fixed₆ empty₆

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
