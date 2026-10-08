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
public def code {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    Circuit (Sampling.Native.Framed.model access) (pre width) (post t width) :=
  Sampling.Native.Framed.code (pre width) (pre_quantumWires width) access

/-- The actual packed phase word retained by the source sample. -/
public def sampleRef (t width : Nat) : CInputRef (post t width) (.bits t) :=
  .storage (Sampling.Native.Framed.resultRef (pre width)
    (pre_quantumWires width) t width).toCStorageRef

/-- Return the stored phase word while listing all live output cells. -/
@[expose] public def run {N x t width : Nat} (access : ModExpOracleAccess N x t width) :
    AlgorithmRun (Sampling.Native.Framed.model access)
      (pre width) (post t width) (.bits t) :=
  Sampling.Native.Framed.run (pre width) (pre_quantumWires width) access

/-- The result is read from the same packed output cell as the code writes. -/
public theorem run_result {N x t width : Nat} (access : ModExpOracleAccess N x t width)
    (record : (run access).Record) :
    (run access).result record = record.1.read (sampleRef t width) :=
  Sampling.Native.Framed.run_result (pre width) (pre_quantumWires width) access record

/-- The complete output manifest includes the original borrowed base. -/
public theorem run_output_listing {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (run access).output.listing = (post t width).keys := rfl

/-- The original caller-owned classical cell retains its identity and storage role. -/
theorem borrowedCells {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) :
    (post t width).borrowedClassicalCells =
      (pre width).borrowedClassicalCells :=
  (code access).borrowedClassicalCells_preserved

/-- The actual sampler preserves all correlations of the borrowed base and reference. -/
public theorem borrowedRestored {N x t width : Nat}
    (access : ModExpOracleAccess N x t width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference
      ((Sampling.Native.Framed.model access).HiddenState × History)) :
    (code access).BorrowedRestored Reference state
      ((code access).execute Reference state) :=
  Sampling.Native.Framed.code_borrowedRestored (pre width)
    (pre_quantumWires width) access state

/-- Exact events of the actual sample use the independent native source budget. -/
public theorem events {N x t width : Nat} (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).resourcePool path = Sampling.Native.eventBudget access :=
  Sampling.Native.Framed.code_events (pre width) (pre_quantumWires width) access path

/-- One actual source query occurs on every sample path. -/
public theorem modExpCount {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    ResourcePool.count (model := Sampling.Native.Framed.model access)
      (.oracle UnitarySource.Coordinate.ordinary)
      ((code access).resourcePool path) = 1 :=
  Sampling.Native.Framed.code_modExpCount (pre width)
    (pre_quantumWires width) access path

/-- Complete source-sample unit-event depth includes every Z write and packing. -/
public theorem depth {N x t width : Nat} (access : ModExpOracleAccess N x t width)
    (path : (code access).Path) :
    (code access).depth (fun _ => 1) path = Sampling.Native.depthBudget t width :=
  Sampling.Native.Framed.code_depth (pre width) (pre_quantumWires width) access path

/-- Resident input capacity and fresh sample capacity stay separately visible. -/
public theorem residentSpace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    (code access).peakResidentSpace path ≤
      Sampling.Native.spaceBudget t width + (pre width).residentSpace :=
  Sampling.Native.Framed.code_residentSpace (pre width)
    (pre_quantumWires width) access path

/-- Auxiliary capacity charges fresh storage while retaining the borrowed input. -/
public theorem auxiliarySpace {N x t width : Nat}
    (access : ModExpOracleAccess N x t width) (path : (code access).Path) :
    (code access).peakAuxiliarySpace path ≤
      Sampling.Native.spaceBudget t width + (pre width).auxiliarySpace :=
  Sampling.Native.Framed.code_auxiliarySpace (pre width)
    (pre_quantumWires width) access path

end

end QuantumAlg.OrderFinding.ShorSourceJoint.SourceNativeSampling
