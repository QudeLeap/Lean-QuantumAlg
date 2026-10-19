/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
public import QuantumAlg.Primitives.QFT.Semiclassical.Refined.Construction
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Core.Base.Accounting.Context.Embedding.Construction
public import QuantumAlg.Core.Execution.Time
import all QuantumAlg.Primitives.QFT.Semiclassical.Endpoint.Context
import all QuantumAlg.Primitives.QFT.Semiclassical.Refined.Construction
import all QuantumAlg.Core.Execution.Measurement.Cells
import all QuantumAlg.Core.Execution.Trace
import all QuantumAlg.Core.Base.Accounting.ResourcePool

/-!
# Complete semiclassical Fourier execution

First allocate the actual retained binary results, then call the original
allocation-free adaptive circuit on the same physical bank and those cells.
Identity placement changes neither the child program nor its path or native
events. The complete output accounts for every bank system and result cell
[GN96, 9511007.tex:214-244].
-/

namespace QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint

open Execution

noncomputable section

/-- The original native adaptive child on the output bank and its real measurement cells. -/
public def body (inverse : Bool) (n : Nat) :
    Circuit model (outputContext n) (outputContext n) false :=
  Refined.code inverse n (wires n) (qftSemiclassical_wires_qubits n) (resultCell n)

/-- Allocate the n result bits, then execute the unchanged child in its complete context. -/
public def completeCode (inverse : Bool) (n : Nat) :
    Circuit model (inputContext n) (outputContext n) :=
  .seq (MeasurementCells.allocate (model := model) (inputContext n) 2 n)
    (.embed (ContextEmbedding.identity (outputContext n)) (body inverse n))

/-- Project the child's actual path from the sole allocation-then-execution path. -/
public def bodyPath (inverse : Bool) (n : Nat) (path : (completeCode inverse n).Path) :
    (body inverse n).Path := by
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).Path ×
    (body inverse n).Path at path
  exact path.2

/-- The complete run reads the actual retained vector and keeps every live physical resource. -/
public def algorithm (inverse : Bool) (n : Nat) :
    Algorithm model (inputContext n) (outputContext n) (.fixedVector n (.finite 2)) where
  run := { code := completeCode inverse n, output := output n }

/-- Retaining real output bits adds no native event to the original adaptive child. -/
public lemma qftSemiclassical_complete_eventTrace (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).eventTrace path =
      (body inverse n).eventTrace (bodyPath inverse n path) := by
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).eventTrace path.1 ++
    (body inverse n).eventTrace path.2 = _
  rw [MeasurementCells.allocate_eventTrace, List.nil_append]
  rfl

/-- Actual native multiplicities are those of the same child path, after real allocation. -/
public lemma qftSemiclassical_complete_resourcePool (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).resourcePool path =
      (body inverse n).resourcePool (bodyPath inverse n path) := by
  unfold Circuit.resourcePool
  rw [qftSemiclassical_complete_eventTrace]

/-- Real result-cell allocation and identity placement preserve the child's quantum time. -/
public lemma qftSemiclassical_complete_quantumTime (inverse : Bool) (n : Nat)
    (path : (completeCode inverse n).Path) :
    (completeCode inverse n).quantumTime path =
      (body inverse n).quantumTime (bodyPath inverse n path) := by
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).quantumTime path.1 +
    (body inverse n).quantumTime path.2 = _
  change (MeasurementCells.allocate (model := model) (inputContext n) 2 n).depth
    Resource.Event.quantumDuration path.1 + _ = _
  rw [MeasurementCells.allocate_depth, Nat.zero_add]
  rfl

end

end QuantumAlg.QuantumFourierTransform.Semiclassical.Endpoint
