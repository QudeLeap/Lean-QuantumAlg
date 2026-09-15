/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm
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

variable {kind : ProblemKind}

private def samplerDepth (kind : ProblemKind) (N : Nat) : DepthBudget kind :=
  match kind with
  | .classical => .classical
  | .quantum => .quantum (fun _ => 1) (44 * modulusBits N + 161)

/-- Independent exact preparation by the complete finite residue sampler.

**Input.**
- A compile-time modulus `N > 1`, with any incoming caller storage and any
  quantum-reference correlations. There is no initialization requirement.
**Output.**
- The actual `16 * clog 2 N` source bits and their complete unit/factor
  parameter, retaining every caller key and both real result cells.
- The exact output distribution is the independent uniform source mapped
  through the deterministic sixteen-proposal preparation.
**Resource budget.**
- An independent native coordinate allowance of capacity `44 * clog 2 N + 163`.
- At most `27 * clog 2 N + 15` additional live classical bits, counted in both
  resident and auxiliary budgets. Every original quantum dimension is preserved.
- For quantum execution, unit-duration depth is at most `44 * clog 2 N + 161`.
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
public def problem (ctx : RuntimeCtx kind) (N : Nat) (nontrivial : 1 < N) :
    Problem kind ctx (context ctx N) (outputShape N) where
  valid := fun _ => True
  accepts := fun _ result => correctOutput ⟨nontrivial⟩ result
  successLB := ⟨1, le_rfl⟩
  states := [requirement ctx N]
  resources :=
    { events := nativeEnvelope kind N
      resident := ctx.residentSpace + additionalSpace kind (modulusBits N)
      auxiliary := ctx.auxiliarySpace + additionalSpace kind (modulusBits N) }
  depth := samplerDepth kind N

/-- Execute the actual retained sampler and read its complete live-key Output. -/
public def algorithm (ctx : RuntimeCtx kind) (N : Nat) :
    Algorithm kind ctx (context ctx N) (outputShape N) where
  run := run ctx N

/-- The complete manifest lists every actual final live key. -/
public theorem samplerNative_output_listing (ctx : RuntimeCtx kind) (N : Nat) :
    (algorithm ctx N).run.output.listing = (context ctx N).keys := (rfl)

/-- Classical retention preserves every actual incoming quantum wire and its dimension. -/
public theorem samplerNative_quantumWires (ctx : RuntimeCtx kind) (N : Nat) :
    (context ctx N).quantumWires = ctx.quantumWires := (rfl)

/-- The independent resident allowance includes all live caller entries and classical work. -/
public theorem samplerNative_resident_budget (ctx : RuntimeCtx kind) (N : Nat)
    (nontrivial : 1 < N) :
    (problem ctx N nontrivial).resources.resident .classicalBits =
      ctx.residentSpace .classicalBits + (27 * Nat.clog 2 N + 15) := (rfl)

/-- The actual public algorithm has the exact original independent source distribution. -/
public theorem samplerNative_outputDistribution (ctx : RuntimeCtx kind) (N : Nat)
    (nontrivial : 1 < N) {Reference : Register} (input : Execution.Input ctx Reference) :
    (algorithm ctx N).outputDistribution input =
      (PMF.uniformOfFintype (Fin (2 ^ residueSamplingBits N))).map
        (outputValue ⟨nontrivial⟩) :=
  samplerRetained_run_outputDistribution ctx ⟨nontrivial⟩ input

/-- The same native run meets exact preparation, full-state and independent resource obligations. -/
public theorem main (ctx : RuntimeCtx kind) (N : Nat) (nontrivial : 1 < N) :
    ∃ candidate, Algorithm.Solves candidate (problem ctx N nontrivial) := by
  refine ⟨algorithm ctx N, ?_⟩
  constructor
  · intro Reference input _valid
    exact samplerRetained_success ctx ⟨nontrivial⟩ input
  · intro Reference input _valid promised present
    change promised ∈ [requirement ctx N] at present
    obtain rfl := List.mem_singleton.mp present
    exact samplerRetainedRequirement_holds ctx ⟨nontrivial⟩ input
  · intro Reference input _valid
    exact samplerRetained_borrowedRestored ctx N Reference
      (input.state.mapClassical (fun store => (store, store)))
  · intro _Reference _input _valid path _supported
    exact samplerRetained_pool_le ctx N path
  · intro _Reference _input _valid path _supported
    exact samplerRetained_resident_le ctx N path
  · intro _Reference _input _valid path _supported
    exact samplerRetained_auxiliary_le ctx N path
  · intro _Reference _input _valid path _supported
    cases kind with
    | classical => trivial
    | quantum => exact samplerRetained_unit_depth_le ctx N path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Retained
