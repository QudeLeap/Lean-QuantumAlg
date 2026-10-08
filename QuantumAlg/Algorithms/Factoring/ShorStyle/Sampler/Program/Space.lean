/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Scope.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Space
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Space
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Complete live-space allowance of actual scoped residue preparation

The eleven sampler cells occupy `5 * width + 9` classical bits. The accepted
arm temporarily adds the real lexical GCD work, `4 * (width + 1) + 1` bits.
Thus `9 * width + 14` bounds the additional live space on every actual path.
The caller's retained sample and parameter cell are counted by its context;
all quantum systems keep their original native dimensions and roles.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open ClassicalRoutines

noncomputable section

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind}

/-- Independent capacity of the real sampler scopes and simultaneously live GCD work. -/
def additionalSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.bits (9 * width + 14))

/-- Loading and scanning reuse exactly the already present resident context. -/
theorem samplerScan_resident_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (path : (Scan.circuit (model := model) N sample).Path) :
    (Scan.circuit (model := model) N sample).peakResidentSpace path ≤
      (Layout.context ctx (modulusBits N)).residentSpace := by
  refine (Circuit.peakResidentSpace_seq (Scan.loader (model := model) ctx N)
    (Proposal.scan (model := model) (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))) path).le.trans ?_
  exact SpacePool.max_le
    (ConstantWord.constantWord_resident_le (model := model)
        (Layout.modulusCell ctx (modulusBits N)) N path.1)
    (Proposal.proposalScan_resident_le (model := model) (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N)) path.2)

/-- The actual loader and scan add no auxiliary storage beyond their existing cells. -/
theorem samplerScan_auxiliary_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (path : (Scan.circuit (model := model) N sample).Path) :
    (Scan.circuit (model := model) N sample).peakAuxiliarySpace path ≤
      (Layout.context ctx (modulusBits N)).auxiliarySpace := by
  refine (Circuit.peakAuxiliarySpace_seq (Scan.loader (model := model) ctx N)
    (Proposal.scan (model := model) (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))) path).le.trans ?_
  exact SpacePool.max_le
    (ConstantWord.constantWord_auxiliary_le (model := model)
        (Layout.modulusCell ctx (modulusBits N)) N path.1)
    (Proposal.proposalScan_auxiliary_le (model := model) (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N)) path.2)

/-- The complete inner resident peak adds only the real selected Euclidean work. -/
theorem samplerInner_resident_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (inner (model := model) N sample output).Path) :
    (inner (model := model) N sample output).peakResidentSpace path ≤
      (Layout.context ctx (modulusBits N)).residentSpace +
        NumberTheory.GCD.lexicalAdditionalSpace model.kind (modulusBits N + 1) := by
  refine (Circuit.peakResidentSpace_seq (Scan.circuit (model := model) N sample)
    (Decision.circuit (model := model) (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (samplerScan_resident_le (model := model)
      N sample path.1).trans (fun axis => Nat.le_add_right _ _)
  · exact Decision.decision_resident_le (model := model) (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N)) path.2

/-- The complete inner auxiliary peak includes every actually allocated Euclidean cell. -/
theorem samplerInner_auxiliary_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (inner (model := model) N sample output).Path) :
    (inner (model := model) N sample output).peakAuxiliarySpace path ≤
      (Layout.context ctx (modulusBits N)).auxiliarySpace +
        NumberTheory.GCD.lexicalAdditionalSpace model.kind (modulusBits N + 1) := by
  refine (Circuit.peakAuxiliarySpace_seq (Scan.circuit (model := model) N sample)
    (Decision.circuit (model := model) (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N))) path).le.trans ?_
  apply SpacePool.max_le
  · exact (samplerScan_auxiliary_le (model := model)
      N sample path.1).trans (fun axis => Nat.le_add_right _ _)
  · exact Decision.decision_auxiliary_le (model := model) (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N)) path.2

private theorem resident_budget {kind : ProblemKind} {ctx : RuntimeCtx kind} (width : Nat) :
    (Layout.context ctx width).residentSpace +
      NumberTheory.GCD.lexicalAdditionalSpace kind (width + 1) =
        ctx.residentSpace + additionalSpace kind width := by
  rw [Layout.samplerLayout_residentSpace]
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [Layout.cellSpace, NumberTheory.GCD.lexicalAdditionalSpace,
      additionalSpace, SpacePool.ofShape]; omega

private theorem auxiliary_budget {kind : ProblemKind} {ctx : RuntimeCtx kind} (width : Nat) :
    (Layout.context ctx width).auxiliarySpace +
      NumberTheory.GCD.lexicalAdditionalSpace kind (width + 1) =
        ctx.auxiliarySpace + additionalSpace kind width := by
  rw [Layout.samplerLayout_auxiliarySpace]
  apply SpacePool.ext
  intro axis
  cases axis <;>
    simp [Layout.cellSpace, NumberTheory.GCD.lexicalAdditionalSpace,
      additionalSpace, SpacePool.ofShape]; omega

/-- The actual scoped program has the complete independent additional resident allowance. -/
theorem samplerProgram_resident_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (circuit (model := model) N sample output).Path) :
    (circuit (model := model) N sample output).peakResidentSpace path ≤
      ctx.residentSpace + additionalSpace model.kind (modulusBits N) := by
  exact (samplerScopes_resident_le (modulusBits N) (inner (model := model) N sample output) path _
    (fun axis => Nat.le_add_right _ _)
    (samplerInner_resident_le (model := model) N sample output path)).trans_eq
      (resident_budget (ctx := ctx) (modulusBits N))

/-- The same path accounts for all live workspace roles throughout entry, body and release. -/
theorem samplerProgram_auxiliary_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (circuit (model := model) N sample output).Path) :
    (circuit (model := model) N sample output).peakAuxiliarySpace path ≤
      ctx.auxiliarySpace + additionalSpace model.kind (modulusBits N) := by
  exact (samplerScopes_auxiliary_le (modulusBits N) (inner (model := model) N sample output) path _
    (fun axis => Nat.le_add_right _ _)
    (samplerInner_auxiliary_le (model := model) N sample output path)).trans_eq
      (auxiliary_budget (ctx := ctx) (modulusBits N))

end

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
