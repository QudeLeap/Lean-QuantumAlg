/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Pair.Candidate.Program.Layout

/-!
# The original sampled parameter and its actual retained generator
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery

open Execution

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {N : Nat}

/-- The original sampled-parameter entry facts survive preservation of its actual read. -/
theorem setupInitial_transport (input : Input N)
    (refs : LatticeCandidateModularSetup.Refs ctx N) (before after : Store ctx)
    (initial : LatticeCandidateModularSetup.InitialConditions input before refs)
    (parameterFrame : after.read refs.parameter = before.read refs.parameter) :
    LatticeCandidateModularSetup.InitialConditions input after refs := by
  rcases initial with ⟨⟨sample, sampled⟩, baseLt⟩
  refine ⟨⟨sample, parameterFrame.trans sampled⟩, ?_⟩
  change (after.read refs.parameter).first.toNat < N
  rw [parameterFrame]
  exact baseLt

/-- The actual framed base is the canonical value of the retained original generator. -/
theorem parameterBase_eq_generatorValue (input : Input N) (generator : (ZMod N)ˣ)
    (refs : Refs ctx N) (before after : Store ctx)
    (initial : InitialConditions input generator before refs)
    (parameterFrame : after.read refs.setup.parameter = before.read refs.setup.parameter) :
    LatticeCandidateModularSetup.parameterBase refs.setup after = (generator : ZMod N).val := by
  rcases initial.setup.sampled with ⟨sample, sampled⟩
  have generatorUnit : generator = (preparedResidue sample).unit := by
    calc
      generator = parameterUnit (before.read refs.setup.parameter) := initial.generatorAtEntry
      _ = parameterUnit (parameterValue input sample) := congrArg parameterUnit sampled
      _ = (preparedResidue sample).unit := parameterUnit_parameterValue input sample
  calc
    LatticeCandidateModularSetup.parameterBase refs.setup after =
        (parameterValue input sample).first.toNat := by
      change (after.read refs.setup.parameter).first.toNat = _
      rw [parameterFrame, sampled]
    _ = ((preparedResidue sample).unit : ZMod N).val := parameterValue_unit_toNat input sample
    _ = (generator : ZMod N).val :=
      congrArg (fun unit : (ZMod N)ˣ => (unit : ZMod N).val) generatorUnit.symm

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticePairCandidateRecovery
