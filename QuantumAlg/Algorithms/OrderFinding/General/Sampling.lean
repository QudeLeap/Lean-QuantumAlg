/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.General.Input
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Distribution
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Resources
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Space
import all QuantumAlg.Algorithms.OrderFinding.Sampling.Framed.Restoration

/-!
# Actual source sampling with the original borrowed modular base

The general-order endpoint keeps the caller's original canonical-residue
cell at its original identity. The common sampler allocates its own phase
and target registers, applies the source query and inverse QFT, writes real
Z outcomes, and packs those same bits. This layer ends before continued-
fraction recovery; its probability statement concerns the actual retained
sample and imposes no condition on an external reference.
-/

namespace QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling

noncomputable section

open QuantumAlg.Execution

/-- The original borrowed base and all actual quantum and classical sample results. -/
def post (t width : Nat) : RuntimeCtx .quantum :=
  Sampling.Framed.post (pre width) (pre_quantumWires width) t width

/-- The same native sampler, entered with the original borrowed-base context. -/
def code {N x t width : Nat} (A : ModExpOracleAccess N x t width) :
    Circuit (pre width) (post t width) :=
  Sampling.Framed.code (pre width) (pre_quantumWires width) A

/-- The actual packed bits are the sample consumed by native continued-fraction recovery. -/
def sampleRef (t width : Nat) : CInputRef (post t width) (.bits t) :=
  .storage (Sampling.Framed.resultRef (pre width) (pre_quantumWires width) t width).toCStorageRef

/-- A complete intermediate run, retaining the original borrowed base as well as every result. -/
def run {N x t width : Nat} (A : ModExpOracleAccess N x t width) :
    AlgorithmRun (pre width) (post t width) (.bits t) :=
  Sampling.Framed.run (pre width) (pre_quantumWires width) A

theorem run_result {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (record : (run A).Record) :
    (run A).result record = record.1.read (sampleRef t width) := rfl

theorem run_output_listing {N x t width : Nat} (A : ModExpOracleAccess N x t width) :
    (run A).output.listing = (post t width).keys := rfl

/-- Actual source sampling never removes or changes the identity of the original borrowed cell. -/
theorem borrowedCells {N x t width : Nat} (A : ModExpOracleAccess N x t width) :
    (post t width).borrowedClassicalCells = (pre width).borrowedClassicalCells :=
  (code A).borrowedClassicalCells_preserved

/-- The original source Born marginal is the distribution of these actual stored bits. -/
theorem distribution {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    {Reference : Register} (input : Execution.Input (pre width) Reference) :
    (run A).outputDistribution input =
      ((measurement t width).outcomePMF (BornBridge.evolvedState A)).map CShape.Value.bits :=
  Sampling.Framed.outputDistribution_eq (pre width) (pre_quantumWires width) A input

/-- The original borrowed classical value and its full external-reference correlations survive. -/
theorem borrowedRestored {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (pre width) Reference History) :
    (code A).BorrowedRestored Reference state ((code A).execute Reference state) :=
  Sampling.Framed.code_borrowedRestored (pre width) (pre_quantumWires width) A state

/-- The actual sample uses the original native event budget, without a base-reconstruction call. -/
theorem events {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (path : (code A).Path) :
    (code A).resourcePool path = Sampling.eventBudget N x t width :=
  Sampling.Framed.code_events (pre width) (pre_quantumWires width) A path

theorem depth {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (path : (code A).Path) :
    (code A).depth (fun _ => 1) path = Sampling.depthBudget t :=
  Sampling.Framed.code_depth (pre width) (pre_quantumWires width) A path

/-- Existing borrowed storage and newly live sampling storage have distinct resident roles. -/
theorem residentSpace {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (path : (code A).Path) :
    (code A).peakResidentSpace path ≤ Sampling.spaceBudget t width + (pre width).residentSpace :=
  Sampling.Framed.code_residentSpace (pre width) (pre_quantumWires width) A path

theorem auxiliarySpace {N x t width : Nat} (A : ModExpOracleAccess N x t width)
    (path : (code A).Path) :
    (code A).peakAuxiliarySpace path ≤ Sampling.spaceBudget t width + (pre width).auxiliarySpace :=
  Sampling.Framed.code_auxiliarySpace (pre width) (pre_quantumWires width) A path

end

end QuantumAlg.OrderFinding.ShorSourceJoint.NativeSampling
