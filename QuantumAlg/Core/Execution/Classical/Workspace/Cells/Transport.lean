/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
public import QuantumAlg.Core.Execution.Classical.Workspace.Transport
import all QuantumAlg.Core.Execution.Classical.Workspace.Cells.Index
import all QuantumAlg.Core.Execution.Classical.Workspace.Transport

/-!
# Structural transport of actual heterogeneous workspace cells
-/

namespace QuantumAlg.Execution.ClassicalWorkspace

/-- Lift a heterogeneous cell collection along one structural scope transport. -/
public def transportCells {kind : ProblemKind} {outer inner : RuntimeCtx kind}
    {shapes : List CShape} (transport : Transport outer inner) :
    Cells outer shapes → Cells inner shapes
  | .nil => .nil
  | .cons head tail =>
      .cons
        { ref := transport.liftWrite head.ref
          role := by
            rw [transport.liftWrite_role head.ref]
            exact head.role }
        (transportCells transport tail)

/-- Transporting cells preserves their physical-key list. -/
public lemma workspaceCells_transportCells_keys {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shapes : List CShape}
    (transport : Transport outer inner) (cells : Cells outer shapes) :
    (transportCells transport cells).keys = cells.keys := by
  induction cells with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [transportCells, Cells.keys]
      rw [transport.liftWrite_key head.ref, inductionHypothesis]

/-- Transporting cells preserves avoidance of every physical key. -/
public lemma workspaceCells_transportCells_avoidsKey {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shapes : List CShape}
    (transport : Transport outer inner) (cells : Cells outer shapes)
    (key : StorageKey) :
    (transportCells transport cells).AvoidsKey key ↔ cells.AvoidsKey key := by
  induction cells with
  | nil => rfl
  | cons head tail inductionHypothesis =>
      simp only [transportCells, Cells.AvoidsKey]
      rw [transport.liftWrite_key head.ref, inductionHypothesis]

/-- Transporting a heterogeneous workspace preserves pairwise distinctness. -/
public lemma workspaceCells_transportCells_distinct {kind : ProblemKind}
    {outer inner : RuntimeCtx kind} {shapes : List CShape}
    (transport : Transport outer inner) (cells : Cells outer shapes)
    (distinct : cells.Distinct) :
    (transportCells transport cells).Distinct := by
  induction cells with
  | nil => trivial
  | cons head tail inductionHypothesis =>
      rcases distinct with ⟨tailAvoids, tailDistinct⟩
      constructor
      · rw [workspaceCells_transportCells_avoidsKey]
        simpa only [transport.liftWrite_key head.ref] using tailAvoids
      · exact inductionHypothesis tailDistinct


end QuantumAlg.Execution.ClassicalWorkspace
