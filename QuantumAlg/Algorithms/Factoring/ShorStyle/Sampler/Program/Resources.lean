/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Program
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Decision.Resources
import all QuantumAlg.Algorithms.Factoring.ShorStyle.Sampler.Proposal.Resources
import all QuantumAlg.Components.Classical.ConstantWord.Resources

/-!
# Independent native budget of the complete scoped residue program

The allowance sums the literal public-modulus loader, the original sixteen
proposal capacities and the expanded decision budget. Actual lexical scopes
add no events. This is the deterministic program following an already stored
sample; the enclosing random draw has its own additional native event.
-/

namespace QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program

open ClassicalRoutines

variable {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Independent native coordinates of loading, all original proposals and the complete decision. -/
def nativeEnvelope (kind : ProblemKind) (N : Nat) : ResourcePool kind :=
  (ConstantWord.envelope kind (modulusBits N + 1) +
    Proposal.scanEnvelope kind (modulusBits N) residueProposalCount) +
      Decision.nativeEnvelope kind (modulusBits N)

/-- The real loader and ordered scan respect their two independent native allowances. -/
theorem samplerScan_pool_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (path : (Scan.circuit N sample).Path) :
    (Scan.circuit N sample).resourcePool path ≤
      ConstantWord.envelope kind (modulusBits N + 1) +
        Proposal.scanEnvelope kind (modulusBits N) residueProposalCount := by
  change ResourcePool.ofList ((Scan.loader ctx N).eventTrace path.1 ++
    (Proposal.scan (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N))).eventTrace
        path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add
    (ConstantWord.constantWord_pool_le (Layout.modulusCell ctx (modulusBits N)) N path.1)
    (Proposal.proposalScan_pool_le (Layout.underRead sample (modulusBits N))
      (Layout.shared ctx (modulusBits N)) (Layout.scratch ctx (modulusBits N)) path.2)

/-- Every actual inner path includes its selected decision's exact native coordinates. -/
theorem samplerInner_pool_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (inner N sample output).Path) :
    (inner N sample output).resourcePool path ≤ nativeEnvelope kind N := by
  change ResourcePool.ofList ((Scan.circuit N sample).eventTrace path.1 ++
    (Decision.circuit (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N))).eventTrace path.2) ≤ _
  rw [ResourcePool.ofList_append]
  exact add_le_add (samplerScan_pool_le N sample path.1)
    (Decision.decision_pool_le (Layout.shared ctx (modulusBits N))
      (Layout.scratch ctx (modulusBits N)) (Layout.gcdResultCell ctx (modulusBits N))
      (Layout.underWrite output (modulusBits N)) path.2)

/-- The actual eleven allocations and releases leave the inner event trace unchanged. -/
theorem samplerScopes_eventTrace (width : Nat)
    (body : Circuit (Layout.context ctx width) (Layout.context ctx width))
    (path : (scopes ctx width body).Path) :
    (scopes ctx width body).eventTrace path = body.eventTrace path := rfl

/-- Every full scoped execution satisfies the independently stated native coordinate budget. -/
theorem samplerProgram_pool_le (N : Nat)
    (sample : CInputRef ctx (.bits (residueSamplingBits N)))
    (output : CWriteRef ctx (ParameterShape (modulusBits N)))
    (path : (circuit N sample output).Path) :
    (circuit N sample output).resourcePool path ≤ nativeEnvelope kind N :=
  samplerInner_pool_le N sample output path

/-- The deterministic allowance contains exactly this many native event slots. -/
theorem samplerProgramEnvelope_card (kind : ProblemKind) (N : Nat) :
    (nativeEnvelope kind N).card = 44 * modulusBits N + 162 := by
  have loaderCard : (ConstantWord.envelope kind (modulusBits N + 1)).card =
      2 * (modulusBits N + 1) := by
    simp [ConstantWord.envelope, ConstantWord.bitEnvelope, ResourcePool.scale,
      ResourcePool.singleton, Nat.mul_comm]
  simp only [nativeEnvelope, Multiset.card_add, loaderCard,
    Proposal.proposalScanEnvelope_card, Decision.decisionNativeEnvelope_card, residueProposalCount]
  omega

end QuantumAlg.Factoring.ShorStyle.Canonical.Sampler.Program
