/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Endpoints
import all QuantumAlg.Core.Base.Tensor.Linear
import Batteries.Tactic.GeneralizeProofs

/-!
# The same initial physical seed beside the complete original good source

Before the first window, every original good branch has the same physical
point workspace. The mathematical source retains both complete unsigned
exponents and all Reference amplitudes. Factoring out the common physical
ket neither normalizes the good component nor prepares another system.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

attribute [local irreducible] branchGood prefixAffine FullRange.chronologicalFixedSeed
  Sampling.Parameters.physicalLabel Driver.driverAffineBlank

private lemma tensor_ket_double_sum {R S : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] (physical : R.Index)
    (labels : Branch → Ref → S.Index) (coefficient : Branch → Ref → ℂ) :
    (∑ branch, ∑ ref, coefficient branch ref •
      (NormalizedVector.ket (R := R.prod S) (physical, labels branch ref)).vec) =
      HilbertVector.prodTensor (NormalizedVector.ket (R := R) physical).vec
        (∑ branch, ∑ ref,
          coefficient branch ref • (NormalizedVector.ket (R := S) (labels branch ref)).vec) := by
  simp only [HilbertVector.prodTensor_sum_right, HilbertVector.prodTensor_smul_right,
    HilbertVector.prodTensor_ket]

private lemma coherentLabel_initial {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (branch : GoodBranch I)
    {Reference : Register} (ref : Reference.Index) :
    coherentLabel (ctx := ctx) parameters I 0 (Nat.zero_le 34) 0 branch
      (Reference := Reference) ref =
      (parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (FullRange.chronologicalFixedSeed I) (false, false, false) 0),
       sourceBranch I branch.val, ref) := by
  unfold coherentLabel
  congr 1
  · congr 1
    congr 1
    change @Eq (AffinePoint (DomainParameters.curve I.curveCert)) _ _
    generalize_proofs certificate good within
    have certificateSame : certificate = I.curveCert := Subsingleton.elim _ _
    subst certificate
    exact prefixAffine_initial I branch.val good within
  · exact congrArg (fun source : Sampling.SourceRegister.Index => (source, ref))
      (Sampling.remainingSource_initial (sourceBranch I branch.val))

private def initialStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference),
    coherentPrefix parameters I 0 (Nat.zero_le 34) 0 amplitude reference =
      HilbertVector.prodTensor
        (NormalizedVector.ket (R := ctx.register)
          (parameters.physicalLabel
            (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
              (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).vec
        (∑ branch : GoodBranch I, ∑ ref : Reference.Index,
          (amplitude branch * reference ref) •
            (NormalizedVector.ket (R := Sampling.SourceRegister.prod Reference)
              (sourceBranch I branch.val, ref)).vec)

private lemma initialStatement_proof : initialStatement := by
  intro ctx parameters I amplitude Reference reference
  unfold coherentPrefix
  simp_rw [coherentLabel_initial]
  exact tensor_ket_double_sum
    (R := ctx.register) (S := Sampling.SourceRegister.prod Reference)
    (Branch := GoodBranch I) (Ref := Reference.Index)
    (parameters.physicalLabel
      (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        (FullRange.chronologicalFixedSeed I) (false, false, false) 0))
    (fun branch ref => (sourceBranch I branch.val, ref))
    (fun branch ref => amplitude branch * reference ref)

/-- The initial whole good vector has the original seed and its unchanged complete source. -/
lemma coherentPrefix_initial {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) :
    coherentPrefix parameters I 0 (Nat.zero_le 34) 0 amplitude reference =
      HilbertVector.prodTensor
        (NormalizedVector.ket (R := ctx.register)
          (parameters.physicalLabel
            (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
              (FullRange.chronologicalFixedSeed I) (false, false, false) 0))).vec
        (∑ branch : GoodBranch I, ∑ ref : Reference.Index,
          (amplitude branch * reference ref) •
            (NormalizedVector.ket (R := Sampling.SourceRegister.prod Reference)
              (sourceBranch I branch.val, ref)).vec) :=
  initialStatement_proof parameters I amplitude reference

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
