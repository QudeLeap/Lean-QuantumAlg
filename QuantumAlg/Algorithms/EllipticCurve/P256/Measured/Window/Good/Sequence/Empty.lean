/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.Scalar
import all QuantumAlg.Primitives.QFT.Semiclassical.Window.Source.Sequence.Quadratic.Scalar

/-!
# Zero mass for an empty original good component

The original complete vector is zero when no good branch exists. Both the
completion sum and the actual retained suffix therefore contribute zero,
without conditioning or a nonemptiness assumption on the public result.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- An empty original good component has zero complete-output weight at every cursor. -/
lemma completionWeight_empty (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) [IsEmpty (GoodBranch I)]
    (first second : Nat) (firstBound : first ≤ 260) (secondBound : second ≤ 260)
    (original : Store ctx) (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) (event : Sampling.SourceRegister.Index → Bool) :
    completionWeight parameters I first second firstBound secondBound
      original amplitude reference event = 0 := by
  unfold completionWeight
  apply Finset.sum_eq_zero
  intro complete _
  split_ifs
  · rw [coherentPrefix_of_isEmpty, norm_zero]
    norm_num
  · rfl

/-- Every actual suffix maps an empty original good component to zero event mass. -/
lemma suffixValue_empty (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) [IsEmpty (GoodBranch I)]
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (processed : Nat) (within : processed ≤ 34)
    {Reference : Register} {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) (reference : HilbertVector Reference)
    (event : Sampling.SourceRegister.Index → Bool) :
    suffixValue parameters I environment processed within
      original amplitude reference event = 0 := by
  simp only [suffixValue, coherentPrefix_of_isEmpty, Stage.quadraticSum_zero]

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
