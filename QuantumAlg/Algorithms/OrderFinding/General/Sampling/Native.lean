/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Input
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Resources
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Space
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Depth
public import QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Restoration
import all QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Space
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Depth
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Native.Framed.Restoration
import all QuantumAlg.Core.Execution.Borrowed.Classical

/-!
# Native source sample with the actual borrowed canonical base

The declared modular-exponentiation query, native phase gates, retained Z
results and packed output run while the original caller-owned residue cell
remains live. This layer ends before continued-fraction recovery.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling

noncomputable section

open QuantumAlg.Execution

/-- The input's borrowed base and all fresh sample systems and cells remain live. -/
@[expose] public def post (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Native.Framed.post (pre width) (pre_quantumWires width) t width

/-- Execute the framed source sample on the original borrowed-base context. -/
public def code (t width : Nat) :
    Circuit (Sampling.Native.Framed.model t width) (pre width) (post t width) :=
  Sampling.Native.Framed.code (pre width) (pre_quantumWires width) t width

/-- The actual packed phase word retained by the source sample. -/
public def sampleRef (t width : Nat) : CInputRef (post t width) (.bits t) :=
  .storage (Sampling.Native.Framed.resultRef (pre width)
    (pre_quantumWires width) t width).toCStorageRef

/-- Return the stored phase word while listing all live output cells. -/
@[expose] public def run (t width : Nat) :
    AlgorithmRun (Sampling.Native.Framed.model t width)
      (pre width) (post t width) (.bits t) :=
  Sampling.Native.Framed.run (pre width) (pre_quantumWires width) t width

/-- The result is read from the same packed output cell as the code writes. -/
public lemma run_result (t width : Nat)
    (record : (run t width).Record) :
    (run t width).result record = record.1.read (sampleRef t width) :=
  Sampling.Native.Framed.run_result (pre width) (pre_quantumWires width) t width record

/-- The complete output manifest includes the original borrowed base. -/
public lemma run_output_listing (t width : Nat) :
    (run t width).output.listing = (post t width).keys := rfl

/-- The original caller-owned classical cell retains its identity and storage role. -/
lemma borrowedCells (t width : Nat) :
    (post t width).borrowedClassicalCells =
      (pre width).borrowedClassicalCells :=
  (code t width).borrowedClassicalCells_preserved

/-- The actual sampler preserves all correlations of the borrowed base and reference. -/
public lemma borrowedRestored (t width : Nat)
    (environment : (Sampling.Native.Framed.model t width).Environment)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference
      ((Sampling.Native.Framed.model t width).HiddenState × History)) :
    (code t width).BorrowedRestored Reference state
      ((code t width).execute environment Reference state) :=
  Sampling.Native.Framed.code_borrowedRestored (pre width)
    (pre_quantumWires width) t width environment state

/-- Exact events of the actual sample use the independent native source budget. -/
public lemma events (t width : Nat)
    (path : (code t width).Path) :
    (code t width).resourcePool path = Sampling.Native.eventBudget t width :=
  Sampling.Native.Framed.code_events (pre width) (pre_quantumWires width) t width path

/-- One actual source query occurs on every sample path. -/
public lemma modExpCount (t width : Nat) (path : (code t width).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model t width)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code t width).resourcePool path) = 1 :=
  Sampling.Native.Framed.code_modExpCount (pre width)
    (pre_quantumWires width) t width path

/-- Complete source-sample unit-event depth includes every Z write and packing. -/
public lemma depth (t width : Nat)
    (path : (code t width).Path) :
    (code t width).depth (fun _ => 1) path = Sampling.Native.depthBudget t width :=
  Sampling.Native.Framed.code_depth (pre width) (pre_quantumWires width) t width path

/-- Resident input capacity and fresh sample capacity stay separately visible. -/
public lemma residentSpace (t width : Nat) (path : (code t width).Path) :
    (code t width).peakResidentSpace path ≤
      Sampling.Native.spaceBudget t width + (pre width).residentSpace :=
  Sampling.Native.Framed.code_residentSpace (pre width)
    (pre_quantumWires width) t width path

/-- Auxiliary capacity charges fresh storage while retaining the borrowed input. -/
public lemma auxiliarySpace (t width : Nat) (path : (code t width).Path) :
    (code t width).peakAuxiliarySpace path ≤
      Sampling.Native.spaceBudget t width + (pre width).auxiliarySpace :=
  Sampling.Native.Framed.code_auxiliarySpace (pre width)
    (pre_quantumWires width) t width path

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
