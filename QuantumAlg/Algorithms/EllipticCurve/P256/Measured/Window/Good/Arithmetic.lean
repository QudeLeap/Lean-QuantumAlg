/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Action
import all QuantumAlg.Core.Execution.Instrument.Recorded.Scalar

/-!
# Normalization of the actual point instrument's common arithmetic factor

The original driver has the same arithmetic scalar on every actual outcome
of each admissible column. Its complete interpreter and mass preservation
normalize this factor. Fourier readout is not part of this identity; its
source-dependent amplitudes remain in the coherent sequence separately.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine

/-- The real arithmetic outcomes have total squared common scalar one. -/
lemma point_scalar_sum_norm_sq (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance)
    (sameSpec : parameters.modulus = (actualCurveSpec I).field)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34)
    (assigned : Driver.driverScratchReferences
      (parameters.pointParameters (Sampling.chronologicalIndex position)) scratch
      (fun bit => Fin.castLE (Sampling.chronologicalIndex position).lowCapacity bit))
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (before : Store ctx) (hidden : services.HiddenState)
    (values : Driver.driverInputValues parameters.frame (actualCurveSpec I)
      (chronologicalBasePoint I position) (Sampling.chronologicalIndex position).row before) :
    let index := Sampling.chronologicalIndex position
    let point := Driver.namedDriverInstrument (services := services)
      (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
    letI : Fintype point.1 := point.2.1
    (∑ _outcome : point.1, ‖NormalizedVector.invSqrt2 ^ 2048‖ ^ 2) = 1 := by
  dsimp only
  let index := Sampling.chronologicalIndex position
  let point := Driver.namedDriverInstrument (services := services)
    (parameters.pointParameters index) parameters.frame parameters.modulus index.row environment
  let : Fintype point.1 := point.2.1
  have action := point_prefix_action parameters I sameSpec scratch branch good position assigned
    environment before values (Qubits 0) 0
  have physical := Sampling.namedDriverKetAction_physical parameters index environment before
    _ _ (Qubits 0) 0 action
  exact point.2.2.common_scalar_sum_norm_sq (Qubits 0) (before, hidden)
    _ _
    (NormalizedVector.invSqrt2 ^ 2048) (physical hidden)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
