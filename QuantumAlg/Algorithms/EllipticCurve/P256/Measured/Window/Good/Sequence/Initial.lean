/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Sequence.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.Initial
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Sequence.Quadratic

/-!
# The actual source effect starts at the same complete coherent boundary

The mathematical source retains the original branch and Reference amplitudes.
Factoring the common physical seed ket introduces no new hardware or program.
The boundedness premise is used only to construct its original subnormalized
density; the quadratic observation and coherent vector stay unconditioned.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

/-- The original full source labels with every admissible branch and raw Reference amplitude. -/
def coherentSource (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) :
    HilbertVector (Sampling.SourceRegister.prod Reference) :=
  ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
    (amplitude branch * reference ref) •
      (NormalizedVector.ket (R := Sampling.SourceRegister.prod Reference)
        (sourceBranch I branch.val, ref)).vec

/-- The actual source effect is exactly its original complete coherent initial suffix. -/
lemma sourceEffect_suffix_initial (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) {History : Type} [Finite History]
    (original : Store ctx × (services.HiddenState × History))
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference)
    (bounded : ‖coherentSource I amplitude reference‖ ≤ 1)
    (event : Sampling.SourceRegister.Index → Bool) :
    (parameters.sourceEffect Sampling.schedule Reference environment
      (fun record => recordEventEffect (ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (fun store => event (storedComplete parameters store)) record.1)
      original
      (parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).weight
        (DensityOperator.ofSubnormalizedVector (coherentSource I amplitude reference) bounded) =
      suffixValue parameters I environment 0 (Nat.zero_le 34)
        original amplitude reference event := by
  have actual := Sampling.sourceEffect_vector_quadraticSum (services := services)
    parameters Sampling.schedule environment original
    (parameters.physicalLabel
      (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        (FullRange.chronologicalFixedSeed I) (false, false, false) 0))
    (coherentSource I amplitude reference) bounded
    (fun store => event (storedComplete parameters store))
  refine actual.trans ?_
  have boundary := congrArg
    (fun vector : HilbertVector (ctx.register.prod (Sampling.SourceRegister.prod Reference)) =>
      Stage.quadraticSum environment (parameters.sourceStages Sampling.schedule Reference)
        (parameters.sourceCertificates Reference environment Sampling.schedule)
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference))
          (fun store => event (storedComplete parameters store)) record.1)
        original vector)
    (coherentPrefix_initial parameters I amplitude reference)
  refine boundary.symm.trans ?_
  simp only [suffixValue, firstCount_zero, secondCount_zero, consumedCount_zero,
    prefixAmplitude_initial]
  exact congrArg
    (fun indices : List Sampling.WindowIndex =>
      Stage.quadraticSum environment (parameters.sourceStages indices Reference)
        (parameters.sourceCertificates Reference environment indices)
        (fun record => recordEventEffect
          (ctx.register.prod (Sampling.SourceRegister.prod Reference))
          (fun store => event (storedComplete parameters store)) record.1)
        original (coherentPrefix parameters I 0 (Nat.zero_le 34) 0 amplitude reference))
    (show Sampling.schedule.drop 0 = Sampling.schedule from List.drop_zero).symm

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
