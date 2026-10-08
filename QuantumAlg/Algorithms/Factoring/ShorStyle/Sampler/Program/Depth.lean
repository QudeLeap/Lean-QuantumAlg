/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Depth
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Depth
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Actual unit-duration depth of the complete scoped sampler program

The sum follows the literal loader, the original sixteen serial proposal
slots and the actual selected decision path. Real lexical allocation and
release add no event duration. The enclosing random-bit draw is a separate
operation beyond this deterministic program.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- The real public-modulus load and source scan satisfy their explicit serial-depth sum. -/
theorem samplerScan_unit_depth_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (path : (Scan.circuit (model := model) N sample).Path) :
    (Scan.circuit (model := model) N sample).depth (fun _ => 1) path ≤
      2 * (modulusBits N + 1) + residueProposalCount * (2 * modulusBits N + 8) := by
  have loaded := ConstantWord.constantWord_depth_le (model := model)
    (Layout.modulusCell ctx (modulusBits N))
    N (fun _ => 1) path.1
  change (Scan.loader (model := model) ctx N).depth (fun _ => 1) path.1 ≤
    (modulusBits N + 1) * (1 + 1) at loaded
  have scanned := Proposal.proposalScan_unit_depth_le (model := model)
    (Layout.underRead sample (modulusBits N))
    (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N)) path.2
  change (Scan.loader (model := model) ctx N).depth (fun _ => 1) path.1 +
    (Proposal.scan (model := model) (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))).depth
        (fun _ => 1) path.2 ≤ _
  omega

/-- The real inner program counts only the result arm that its stored condition executes. -/
theorem samplerInner_unit_depth_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (inner (model := model) N sample output).Path) :
    (inner (model := model) N sample output).depth (fun _ => 1) path ≤
      44 * modulusBits N + 160 := by
  have scanned := samplerScan_unit_depth_le (model := model) N sample path.1
  have decided := Decision.decision_depth_le (model := model) (Layout.shared ctx (modulusBits N))
    (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
    (Layout.underWrite output (modulusBits N)) (fun _ => 1) path.2
  rw [Decision.decisionNativeDepthLimit_unit] at decided
  change (Scan.circuit (model := model) N sample).depth (fun _ => 1) path.1 +
    (Decision.circuit (model := model) (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N))).depth (fun _ => 1) path.2 ≤ _
  simp only [residueProposalCount] at scanned
  omega

/-- The complete eleven-scope program has the same actual unit-duration bound. -/
theorem samplerProgram_unit_depth_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (circuit (model := model) N sample output).Path) :
    (circuit (model := model) N sample output).depth (fun _ => 1) path ≤ 44 * modulusBits N + 160 :=
  samplerInner_unit_depth_le (model := model) N sample output path

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
