/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord.Selection
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained
public import QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Output
public import Mathlib.Probability.Distributions.Uniform
public import Mathlib.Data.Nat.Log
import all QuantumAlg.Core.Algorithm.Problem
import all QuantumAlg.Core.Algorithm.Solves
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Requirement
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Success
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Borrowed
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Retained.Space

/-!
# Complete native residue sampling endpoint

The actual sampler retains its finite source and complete RSA parameter,
including early-factor information. It implements the independent source
distribution with full caller/reference preservation. The native allowances
include all real allocation scopes, random sampling and expanded arithmetic.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained

noncomputable section

local instance {α : Type} : DecidableEq α := Classical.decEq α

variable {model : ExecutionModel} [BitWord.Selected model]

private def samplerDepth (model : ExecutionModel) (N : Nat) : DepthBudget model where
  duration := fun _ => 1
  limit := 44 * modulusBits N + 161
  classicalQuery_unit := fun _ => rfl
  quantumQuery_unit := fun _ => rfl

/-- Independent exact preparation by the complete finite residue sampler.

**Input.**
- A compile-time modulus `N > 1`, with any incoming caller storage and any
  quantum-reference correlations, in a model granting the built-in width-indexed
  bit/word operations. The incoming hidden service state is explicit and unrestricted.
**Output.**
- The actual `16 * clog 2 N` source bits and their complete unit/factor
  parameter, retaining every caller key and both real result cells.
- The exact output distribution is the independent uniform source mapped
  through the deterministic sixteen-proposal preparation.
**Resource budget.**
- An independent native coordinate allowance of capacity `44 * clog 2 N + 163`.
- At most `27 * clog 2 N + 15` additional live classical bits, counted in both
  resident and auxiliary budgets. Every original quantum dimension is preserved.
- Abstract unit-duration depth is at most `44 * clog 2 N + 161` in either model kind.
**Success.**
- Exact agreement of the retained source and complete parameter has probability
  one. The full incoming quantum-reference density is promised on every system,
  and all borrowed classical-quantum-reference correlations are restored.
- This exact preparation statement does not assert probability-one factoring.
**Source.**
- [Sho95, source.tex:1132-1140] supplies the random-residue and Euclidean-GCD
  reduction. The fixed sixteen-proposal adapter and native allowances are the
  concrete finite implementation of the independently specified residue source.
-/
public def problem (ctx : RuntimeCtx model.kind) (N : Nat) (nontrivial : 1 < N) :
    Problem model ctx (context ctx N) (outputShape N) where
  valid := fun _ => True
  initialization := fun _ => True
  accepts := fun _ result => correctOutput ⟨nontrivial⟩ result
  successLB := ⟨1, le_rfl⟩
  states := [requirement ctx N]
  resources :=
    { events := nativeEnvelope model N
      resident := ctx.residentSpace + additionalSpace model.kind (modulusBits N)
      auxiliary := ctx.auxiliarySpace + additionalSpace model.kind (modulusBits N) }
  depth := samplerDepth model N

/-- Execute the actual retained sampler and read its complete live-key Output. -/
public def algorithm (ctx : RuntimeCtx model.kind) (N : Nat) :
    Algorithm model ctx (context ctx N) (outputShape N) where
  run := run (model := model) ctx N

/-- The complete manifest lists every actual final live key. -/
public theorem samplerNative_output_listing (ctx : RuntimeCtx model.kind) (N : Nat) :
    (algorithm (model := model) ctx N).run.output.listing = (context ctx N).keys := (rfl)

omit [BitWord.Selected model] in
/-- Classical retention preserves every actual incoming quantum wire and its dimension. -/
public theorem samplerNative_quantumWires {kind : ProblemKind} (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := (rfl)

/-- The independent resident allowance includes all live caller entries and classical work. -/
public theorem samplerNative_resident_budget (ctx : RuntimeCtx model.kind) (N : Nat)
    (nontrivial : 1 < N) :
    (problem (model := model) ctx N nontrivial).resources.resident .classicalBits =
      ctx.residentSpace .classicalBits + (27 * Nat.clog 2 N + 15) := (rfl)

/-- The actual public algorithm has the exact original independent source distribution. -/
public theorem samplerNative_outputDistribution (ctx : RuntimeCtx model.kind) (N : Nat)
    (nontrivial : 1 < N) {Reference : Register}
        (input : Execution.OracleInput model.classicalOracles ctx Reference) :
    (algorithm (model := model) ctx N).outputDistribution input =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (outputValue ⟨nontrivial⟩) :=
  samplerRetained_run_outputDistribution ctx ⟨nontrivial⟩ input

/-- The same native run meets exact preparation, full-state and independent resource obligations. -/
public theorem main (ctx : RuntimeCtx model.kind) (N : Nat) (nontrivial : 1 < N) :
    ∃ candidate, Algorithm.Solves candidate (problem (model := model) ctx N nontrivial) := by
  refine ⟨algorithm (model := model) ctx N, ?_⟩
  constructor
  · intro Reference input _valid _initialization
    exact samplerRetained_success ctx ⟨nontrivial⟩ input
  · intro Reference input _valid _initialization promised present
    change promised ∈ [requirement ctx N] at present
    obtain rfl := List.mem_singleton.mp present
    exact samplerRetainedRequirement_holds ctx ⟨nontrivial⟩ input
  · intro Reference input _valid _initialization
    change Execution.observeBorrowedAfter (circuit (model := model) ctx N) Reference
      ((circuit (model := model) ctx N).execute Reference
        (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))) =
      Execution.observeBorrowed Reference input.state
    refine (samplerRetained_borrowedRestored ctx N Reference
      (input.state.mapClassical (fun value => (value.1, (value.2, value.1))))).trans ?_
    refine Eq.trans ?_ (Execution.observeBorrowed_mapClassical input.state
      (fun value => (value.1, (value.2, value.1))) (fun _ => rfl))
    apply congrArg (Execution.observeBorrowed Reference)
    exact mapClassical_congr_decision _ _ _ (fun _ => rfl) _ _
  · intro _Reference _input _valid _initialization path _supported
    exact samplerRetained_pool_le ctx N path
  · intro _Reference _input _valid _initialization path _supported
    exact samplerRetained_resident_le ctx N path
  · intro _Reference _input _valid _initialization path _supported
    exact samplerRetained_auxiliary_le ctx N path
  · intro _Reference _input _valid _initialization path _supported
    exact samplerRetained_unit_depth_le ctx N path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
