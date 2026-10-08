/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Candidate.Power.Setup.Resources

/-!
# Basic actual cardinality bounds for lattice recovery

The independent arithmetic budgets count the canonical literal constant
loaders and native modular power. Every bridge uses the corresponding actual
execution path, including all modulus loads and scoped arithmetic operations.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources

open Execution ClassicalRoutines

noncomputable section

/-- A coordinatewise branch allowance has cardinality at most the sum of its two arms. -/
theorem poolMax_card_le_add {model : ExecutionModel} (left right : ResourcePool model) :
    (ResourcePool.max left right).card ≤ left.card + right.card := by
  simpa only [ResourcePool.max, Multiset.card_add] using
    Multiset.card_le_card (Multiset.union_le_add left right)

/-- Reusing one coordinate allowance as both branch bounds leaves it unchanged. -/
theorem poolMax_self {model : ExecutionModel} (pool : ResourcePool model) :
    ResourcePool.max pool pool = pool := by
  rw [Multiset.ext]
  intro event
  simp [ResourcePool.max]

/-- Independent complete native-power event ceiling includes the literal extended modulus. -/
def powerCardBound (width exponentWidth : Nat) : Nat :=
  2 * width + 5 + 6 * exponentWidth

/-- The independent native-power coordinate formula has the stated exact cardinality. -/
theorem powerEventEnvelope_card_eq {model : ExecutionModel} [BitWord.Selected model]
    (width exponentWidth : Nat) :
    (Modular.NativePower.eventEnvelope model width exponentWidth).card =
      powerCardBound width exponentWidth := by
  simp [Modular.NativePower.eventEnvelope, Modular.NativePower.exponentEnvelope,
    Modular.NativePower.bitEnvelope, Modular.NativePower.multiplyEnvelope,
    ConstantWord.envelope, ConstantWord.bitEnvelope, ResourcePool.scale,
    ResourcePool.singleton, powerCardBound]
  omega

/-- Actual native-power paths satisfy the complete independent count bound. -/
theorem nativePower_eventCount_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind}
    {width exponentWidth : Nat} (spec : ClassicalAlgorithms.Modular.ModulusSpec width)
    (base : CInputRef ctx (.canonicalResidue width))
    (exponent : CInputRef ctx (.unsignedWord exponentWidth))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (Modular.NativePower.into spec base exponent output).Path) :
    ((Modular.NativePower.into spec base exponent output).eventTrace path).length ≤
      powerCardBound width exponentWidth := by
  change ((Modular.NativePower.into spec base exponent output).resourcePool path).card ≤ _
  exact (Multiset.card_le_card
    (Modular.NativePower.nativePower_into_pool_le spec base exponent output path)).trans
      (powerEventEnvelope_card_eq width exponentWidth).le

/-- Independent full shared setup ceiling includes both constants and the original target power. -/
def modularSetupCardBound (modulusWidth : Nat) : Nat := 12 * modulusWidth + 8

/-- The original shared setup's independent coordinate allowance has the stated cardinality. -/
theorem modularSetupEventEnvelope_card_eq {model : ExecutionModel} [BitWord.Selected model]
    (modulusWidth : Nat) :
    (LatticeCandidateModularSetup.setupEventEnvelope model modulusWidth).card =
      modularSetupCardBound modulusWidth := by
  unfold LatticeCandidateModularSetup.setupEventEnvelope
  rw [Multiset.card_add, powerEventEnvelope_card_eq]
  simp [LatticeCandidateModularSetup.prepareEnvelope, ConstantWord.envelope,
    ConstantWord.bitEnvelope, ResourcePool.singleton, ResourcePool.scale,
    powerCardBound, modularSetupCardBound]
  omega

/-- Every actual shared setup path satisfies the independent public-modulus-width event bound. -/
theorem modularSetup_eventCount_le {model : ExecutionModel} [BitWord.Selected model]
    {ctx : RuntimeCtx model.kind} {N : Nat}
    (input : Input N) (refs : LatticeCandidateModularSetup.Refs ctx N)
    (path : (LatticeCandidateModularSetup.setupInto input refs).Path) :
    ((LatticeCandidateModularSetup.setupInto input refs).eventTrace path).length ≤
      modularSetupCardBound (modulusBits N) := by
  change ((LatticeCandidateModularSetup.setupInto input refs).resourcePool path).card ≤ _
  exact (Multiset.card_le_card
    (LatticeCandidateModularSetup.setupInto_pool_le input refs path)).trans
      (modularSetupEventEnvelope_card_eq (modulusBits N)).le

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeRecoveryResources
