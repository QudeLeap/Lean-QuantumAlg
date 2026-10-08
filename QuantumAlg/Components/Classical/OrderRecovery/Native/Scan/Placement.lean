/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.OrderRecovery.Native.Scan
import all QuantumAlg.Core.Execution.Classical.Workspace

/-!
# One actual lexical division pair per active recovery visit

All original source and scan references are lifted through one real workspace
head. The same head holds the quotient and remainder throughout validation
and selection, then its matching lexical instruction releases it. No later
visit retains a previous visit's division pair.
-/

namespace QuantumAlg.ClassicalRoutines.OrderRecovery.Native

open Execution ClassicalAlgorithms.Modular

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {modulusWidth candidateWidth : Nat}

/-- The actual quotient and remainder words used by one active visit. -/
def cursorDivisionShape (width : Nat) : CShape :=
  .product (.unsignedWord width) (.unsignedWord width)

/-- The real context while that visit's division pair is live. -/
@[reducible] def scanDivisionCtx (ctx : RuntimeCtx kind) (width : Nat) : RuntimeCtx kind :=
  ctx.addWorkspace ctx.canonicalFreshKey (cursorDivisionShape width) ctx.canonicalFreshKey_fresh

/-- Lift every cursor cell through the same real classical allocation. -/
def CursorCells.underWorkspace (cells : CursorCells ctx candidateWidth)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    CursorCells (ctx.addWorkspace key shape fresh) candidateWidth where
  numerator := cells.numerator.underWorkspace key shape fresh
  denominator := cells.denominator.underWorkspace key shape fresh
  older := cells.older.underWorkspace key shape fresh
  previous := cells.previous.underWorkspace key shape fresh
  candidate := cells.candidate.underWorkspace key shape fresh
  active := cells.active.underWorkspace key shape fresh

/-- Every scan reference still names the same physical storage under the new head. -/
def ScanCells.underWorkspace (cells : ScanCells ctx modulusWidth candidateWidth)
    (key : StorageKey) (shape : CShape) (fresh : key ∉ ctx.keys) :
    ScanCells (ctx.addWorkspace key shape fresh) modulusWidth candidateWidth where
  cursor := cells.cursor.underWorkspace key shape fresh
  selected := cells.selected.underWorkspace key shape fresh
  accepted := cells.accepted.underWorkspace key shape fresh
  zero := cells.zero.underWorkspace key shape fresh
  one := cells.one.underWorkspace key shape fresh
  power := cells.power.underWorkspace key shape fresh
  positive := cells.positive.underWorkspace key shape fresh
  valid := cells.valid.underWorkspace key shape fresh

/-- The actual fresh division head of an active visit. -/
def scanDivisionCell (ctx : RuntimeCtx kind) (width : Nat) :
    CWriteRef (scanDivisionCtx ctx width) (cursorDivisionShape width) :=
  CWriteRef.workspaceHead ctx ctx.canonicalFreshKey (cursorDivisionShape width)
    ctx.canonicalFreshKey_fresh

variable {model : ExecutionModel} [BitWord.Selected model] {ctx : RuntimeCtx model.kind}

/-- The full actual visit operates under its own quotient/remainder allocation. -/
def placedVisit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) :
    Circuit model (scanDivisionCtx ctx candidateWidth) (scanDivisionCtx ctx candidateWidth) :=
  visitWithDivision (model := model) spec
    (base.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
      ctx.canonicalFreshKey_fresh)
    (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
      ctx.canonicalFreshKey_fresh)
    (scanDivisionCell ctx candidateWidth)

/-- A single active visit allocates and releases exactly its own real division pair. -/
def activeVisit (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) : Circuit model ctx ctx :=
  .workspace ctx ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
    ctx.canonicalFreshKey_fresh (placedVisit (model := model) spec base cells)

/-- Concrete outer storage and the actual visit path after its matching lexical release. -/
def activeVisitStep (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (store : Store ctx) :
    Store ctx × (activeVisit (model := model) spec base cells).Path :=
  let visited := visitWithDivisionStep (model := model) spec
    (base.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
      ctx.canonicalFreshKey_fresh)
    (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
      ctx.canonicalFreshKey_fresh)
    (scanDivisionCell ctx candidateWidth)
    (store.pushWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
      ctx.canonicalFreshKey_fresh)
  (Store.popWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
    ctx.canonicalFreshKey_fresh visited.1, visited.2)

/-- The actual workspace interpreter returns the exact outer store and same internal visit path. -/
theorem nativeScan_activeVisit_execute (spec : ModulusSpec modulusWidth)
    (base : CInputRef ctx (.canonicalResidue modulusWidth))
    (cells : ScanCells ctx modulusWidth candidateWidth) (Reference : Register)
    {History : Type} [Fintype History] (state : State ctx Reference (model.HiddenState × History)) :
    (activeVisit (model := model) spec base cells).execute Reference state =
      state.mapClassical (fun entry =>
        ((activeVisitStep (model := model) spec base cells entry.1).1,
          (entry.2.1, (entry.2.2,
            (activeVisitStep (model := model) spec base cells entry.1).2)))) := by
  refine (Circuit.execute_workspace_mapClassical ctx.canonicalFreshKey
    (cursorDivisionShape candidateWidth) ctx.canonicalFreshKey_fresh
    (placedVisit (model := model) spec base cells)
    (fun entry =>
      let next := visitWithDivisionStep (model := model) spec
        (base.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
          ctx.canonicalFreshKey_fresh)
        (cells.underWorkspace ctx.canonicalFreshKey (cursorDivisionShape candidateWidth)
          ctx.canonicalFreshKey_fresh)
        (scanDivisionCell ctx candidateWidth) entry.1
      ((next.1, entry.2), next.2))
    (nativeScan_visitWithDivision_execute spec _ _ _) Reference state).trans ?_
  congr 1

/-- The actual quotient/remainder scope adds no quantum system or physical identity. -/
theorem nativeScan_division_quantumWires {kind : ProblemKind}
    (ctx : RuntimeCtx kind) (width : Nat) :
    (scanDivisionCtx ctx width).quantumWires = ctx.quantumWires := rfl

end

end QuantumAlg.ClassicalRoutines.OrderRecovery.Native
