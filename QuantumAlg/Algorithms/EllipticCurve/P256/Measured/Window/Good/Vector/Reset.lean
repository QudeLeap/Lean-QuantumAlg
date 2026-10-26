/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Reset.Action
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Reset

/-!
# The actual reset on a whole coherent good boundary

Every good physical prefix has a zero active stream/address bank. The
specified actual reset therefore retains this entire vector on its literal
all-zero outcome and annihilates every other outcome. The component is not
conditioned or renormalized, and all Reference amplitudes remain coherent.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
open QuantumFourierTransform.Semiclassical.Window.Source
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

variable {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}

attribute [local irreducible] branchGood prefixAffine

private lemma driverAffineBlank_zero_bank (parameters : Sampling.Parameters ctx)
    (index : Sampling.WindowIndex) (curve : ClassicalAlgorithms.EllipticCurve.CurveSpec 256)
    (same : curve.field.modulus = PrimeFieldShortWeierstrass.Arithmetic.P256.modulus)
    (point : AffinePoint curve.curve) :
    (QuantumFourierTransform.Semiclassical.bankCoordinates
      (parameters.ports index).wires (parameters.ports index).qubits
      (parameters.physicalLabel
        (Driver.driverAffineBlank curve same point (false, false, false) 0))).1 =
      QuantumFourierTransform.Semiclassical.Partner.zeroBits (index.lowerWidth + 1) := by
  unfold Driver.driverAffineBlank
  exact sourceBlank_zero_bank parameters index _ _

attribute [local irreducible] Driver.driverAffineBlank sourceBlank

private lemma double_sum_eigenvalue {R : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] (operator : HilbertOperator R) (scalar : Complex)
    (vectors : Branch → Ref → HilbertVector R) (coefficient : Branch → Ref → Complex)
    (columns : ∀ branch ref,
      operator.applyVec (vectors branch ref) = scalar • vectors branch ref) :
    operator.applyVec (∑ branch, ∑ ref, coefficient branch ref • vectors branch ref) =
      scalar • ∑ branch, ∑ ref, coefficient branch ref • vectors branch ref := by
  simp_rw [HilbertOperator.applyVec_sum, HilbertOperator.applyVec_smul, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro branch _
  apply Finset.sum_congr rfl
  intro ref _
  rw [columns, smul_smul, smul_smul, mul_comm]

/-- The actual active-bank reset preserves exactly the complete zero-outcome good component. -/
lemma coherentPrefix_reset (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) (index : Sampling.WindowIndex)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model
      services).Environment) (store : Store ctx)
    (outcome : Sampling.Reset.Outcome (index.lowerWidth + 1) (parameters.wire index))
    (amplitude : GoodBranch I → Complex)
    {Reference : Register} (reference : HilbertVector Reference) :
    HilbertOperator.applyVec
      (Instrument.referenceLift (Sampling.SourceRegister.prod Reference)
        ((Sampling.Reset.instrument parameters index environment).operator store outcome))
      (coherentPrefix parameters I processed within consumed amplitude reference) =
    (if outcome = Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
      then (1 : Complex) else 0) •
      coherentPrefix parameters I processed within consumed amplitude reference := by
  unfold coherentPrefix
  refine double_sum_eigenvalue
    (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
    (Branch := GoodBranch I) (Ref := Reference.Index)
    (Instrument.referenceLift (Sampling.SourceRegister.prod Reference)
      ((Sampling.Reset.instrument parameters index environment).operator store outcome))
    (if outcome = Sampling.Reset.zeroOutcome (index.lowerWidth + 1) (parameters.wire index)
      then (1 : Complex) else 0)
    (fun branch ref =>
      (NormalizedVector.ket (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (coherentLabel parameters I processed within consumed branch ref)).vec)
    (fun branch ref => amplitude branch * reference ref) ?_
  intro branch ref
  let label := coherentLabel parameters I processed within consumed branch ref
  let physical := label.1
  have blank : (QuantumFourierTransform.Semiclassical.bankCoordinates
      (parameters.ports index).wires
      (parameters.ports index).qubits physical).1 =
        QuantumFourierTransform.Semiclassical.Partner.zeroBits (index.lowerWidth + 1) := by
    exact driverAffineBlank_zero_bank parameters index _ _ _
  have column := Sampling.Reset.zero_column parameters index environment store outcome
    physical ((window_source_bank_zero_iff (parameters.ports index).wires
      (parameters.ports index).qubits physical).mp blank)
    (Reference := Sampling.SourceRegister.prod Reference)
    label.2
  exact column

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
