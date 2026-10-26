/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Outer.Program
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Resources.Complete
import all QuantumAlg.Components.Classical.ConstantWord.Resources
import all QuantumAlg.Core.Execution.Classical.Workspace.Allocate.Induction
import all QuantumAlg.Core.Base.Depth.WeightedCost

/-!
# Independent native-classical accounting of actual window lifetimes

The weights below project the real code, including every public constant
loader and every runtime AND/XOR operation. Lexical scope contributes no
event; actual bodies retain all their native operations. Quantum CNOT
counts remain a separate coordinate of each original query program.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer

open Execution ClassicalWorkspace ClassicalAlgorithms.Modular

noncomputable section

namespace Accounting

variable {model : ExecutionModel} {ctx : RuntimeCtx model.kind} {allocate : Bool}

/-- The two chronological actual path pools contribute their independent weights. -/
lemma seq_weight_le (first second : Circuit model ctx ctx allocate)
    (weight : Resource.Event model → Nat) (firstBound secondBound : Nat)
    (path : (first.seq second).Path)
    (firstActual : ResourcePool.weightedCount weight (first.resourcePool path.1) ≤ firstBound)
    (secondActual : ResourcePool.weightedCount weight (second.resourcePool path.2) ≤ secondBound) :
    ResourcePool.weightedCount weight ((first.seq second).resourcePool path) ≤
      firstBound + secondBound := by
  change ResourcePool.weightedCount weight (ResourcePool.ofList (_ ++ _)) ≤ _
  rw [ResourcePool.ofList_append, ResourcePool.weightedCount_add]
  exact Nat.add_le_add firstActual secondActual

/-- Every original finite-index component retains its actual selected path. -/
lemma range_weight_le (count : Nat) (body : Fin count → Circuit model ctx ctx allocate)
    (weight : Resource.Event model → Nat) (bound : Nat)
    (bounded : ∀ index path,
      ResourcePool.weightedCount weight ((body index).resourcePool path) ≤ bound)
    (path : (Circuit.forRange count body).Path) :
    ResourcePool.weightedCount weight ((Circuit.forRange count body).resourcePool path) ≤
      count * bound := by
  induction count with
  | zero =>
      change ResourcePool.weightedCount weight (0 : ResourcePool model) ≤ 0 * bound
      rw [ResourcePool.weightedCount_zero]
      exact Nat.zero_le _
  | succ count ih =>
      have current := bounded 0 path.1
      have rest := ih (fun index => body index.succ)
        (fun index => bounded index.succ) path.2
      exact (seq_weight_le _ _ weight bound (count * bound) path current rest).trans_eq
        (by rw [Nat.succ_mul, Nat.add_comm])

/-- Real workspace allocation/release preserves the native weight of every enclosed actual path. -/
lemma allocation_weight_le {outer : RuntimeCtx model.kind}
    (transport : Transport outer ctx) (shapes : List CShape)
    (body : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes), cells.Distinct →
      (lift : Transport outer inner) → cells.TransportSeparated lift → Circuit model inner inner)
    (weight : Resource.Event model → Nat) (bound : Nat)
    (bounded : ∀ {inner : RuntimeCtx model.kind} (cells : Cells inner shapes)
      (distinct : cells.Distinct) (lift : Transport outer inner)
      (separated : cells.TransportSeparated lift)
      (path : (body cells distinct lift separated).Path),
      ResourcePool.weightedCount weight ((body cells distinct lift separated).resourcePool path) ≤
        bound)
    (path : (withCellsFrom transport shapes body).Path) :
    ResourcePool.weightedCount weight ((withCellsFrom transport shapes body).resourcePool path) ≤
      bound := by
  have actual := withCellsFrom_property transport shapes body
    (fun _ code => ∀ selected : code.Path,
      ResourcePool.weightedCount weight (code.resourcePool selected) ≤ bound)
    (fun _ _ _ _ _ available => available) bounded
  exact actual path

end Accounting

namespace Frame

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width : Nat} (frame : Frame ctx width)

/-- Actual loaders pay two operations per bit and one increment for the initially zero one-cell. -/
lemma initializeConstants_classical_weight_le (spec : ModulusSpec width) (coefficient : Nat)
    (path : (frame.initializeConstants (model := model) spec coefficient).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.initializeConstants (model := model) spec coefficient).resourcePool path) ≤
        4 * width + 3 := by
  have loader {size : Nat} (output : CWriteRef ctx (.unsignedWord size)) (constant : Nat)
      (selected : (ConstantWord.circuit (model := model) output constant).Path) :
      ResourcePool.weightedCount Resource.Event.classicalOperationWeight
        ((ConstantWord.circuit (model := model) output constant).resourcePool selected) ≤
          2 * size := by
    have actual := ResourcePool.weightedCount_mono Resource.Event.classicalOperationWeight
      (ConstantWord.constantWord_pool_le output constant selected)
    simpa [ConstantWord.envelope, ConstantWord.bitEnvelope, ConstantWord.shiftEvent,
      ConstantWord.incrementEvent, ResourcePool.scale, Resource.Event.classicalOperationWeight,
      two_mul]
      using actual
  have modulus := loader frame.modulus spec.modulus path.1
  have curve := loader frame.curveA coefficient path.2.1
  have one := WindowTables.Accounting.classical_weight_le_eventCount
    (BitWord.instruction (execution := model) (ConstantWord.incrementOp frame.one)) path.2.2
  rw [WindowTables.Accounting.instruction_eventCount] at one
  have rest := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
    (2 * width) 1 path.2 curve one
  have total := Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight
    (2 * (width + 1)) (2 * width + 1) path modulus rest
  exact total.trans_eq (by omega)

/-- Both actual seventeen-row families pay sixteen original sixteen-doubling transitions each. -/
lemma preparePairedBases_classical_weight_le (spec : ModulusSpec width)
    (firstX firstY secondX secondY : CInputRef ctx (.unsignedWord width))
    (path : (frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).Path) :
    ResourcePool.weightedCount Resource.Event.classicalOperationWeight
      ((frame.preparePairedBases (model := model) spec firstX firstY secondX secondY).resourcePool
        path) ≤ 2 * (2 + 16 * (16 * (30 * width + 127))) := by
  have first := frame.coordinates.prepareBasesAt_classical_weight_le spec firstX firstY
    (@firstBaseRows 16) path.1
  have second := frame.coordinates.prepareBasesAt_classical_weight_le spec secondX secondY
    (@secondBaseRows 16) path.2
  exact (Accounting.seq_weight_le _ _ Resource.Event.classicalOperationWeight _ _ path
    first second).trans_eq (by omega)

end Frame

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.Outer
