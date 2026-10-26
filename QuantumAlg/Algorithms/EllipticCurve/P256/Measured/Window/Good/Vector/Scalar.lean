/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State

/-!
# Common scalars of the complete coherent good component

A branch-independent arithmetic scalar factors out of the entire vector.
All branch collisions and external Reference amplitudes remain in the same
coherent sum.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window

variable {ctx : RuntimeCtx .quantum}

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

attribute [local irreducible] branchGood prefixAffine

private lemma double_sum_amplitude_smul {R : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] (vectors : Branch → Ref → HilbertVector R)
    (amplitude : Branch → ℂ) (reference : Ref → ℂ) (scalar : ℂ) :
    (∑ branch, ∑ ref, ((scalar * amplitude branch) * reference ref) • vectors branch ref) =
      scalar • ∑ branch, ∑ ref, (amplitude branch * reference ref) • vectors branch ref := by
  simp only [Finset.smul_sum, smul_smul]
  apply Finset.sum_congr rfl
  intro branch _
  apply Finset.sum_congr rfl
  intro ref _
  rw [mul_assoc]

private lemma double_sum_amplitude_zero {R : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] (vectors : Branch → Ref → HilbertVector R)
    (reference : Ref → ℂ) :
    (∑ branch, ∑ ref, ((0 : ℂ) * reference ref) • vectors branch ref) = 0 := by
  simp only [zero_mul, zero_smul, Finset.sum_const_zero]

private lemma double_sum_amplitude_empty {R : Register} {Branch Ref : Type}
    [Fintype Branch] [Fintype Ref] [IsEmpty Branch]
    (vectors : Branch → Ref → HilbertVector R)
    (amplitude : Branch → ℂ) (reference : Ref → ℂ) :
    (∑ branch, ∑ ref, (amplitude branch * reference ref) • vectors branch ref) = 0 := by
  exact Finset.sum_eq_zero fun branch _ => isEmptyElim branch

private def amplitudeSmulStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum} (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) (amplitude : GoodBranch I → ℂ) (scalar : ℂ)
    {Reference : Register} (reference : HilbertVector Reference),
    coherentPrefix parameters I processed within consumed
        (fun branch => scalar * amplitude branch) reference =
      scalar • coherentPrefix parameters I processed within consumed amplitude reference

private lemma amplitudeSmulStatement_proof : amplitudeSmulStatement := by
  intro ctx parameters I processed within consumed amplitude scalar Reference reference
  exact double_sum_amplitude_smul
    (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
    (Branch := GoodBranch I) (Ref := Reference.Index)
    (fun branch ref =>
      (NormalizedVector.ket (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
        (coherentLabel parameters I processed within consumed branch ref)).vec)
    amplitude (fun ref => reference ref) scalar

/-- One common arithmetic coefficient multiplies the whole original coherent vector. -/
lemma coherentPrefix_amplitude_smul (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) (amplitude : GoodBranch I → ℂ) (scalar : ℂ)
    {Reference : Register} (reference : HilbertVector Reference) :
    coherentPrefix parameters I processed within consumed
        (fun branch => scalar * amplitude branch) reference =
      scalar • coherentPrefix parameters I processed within consumed amplitude reference :=
  amplitudeSmulStatement_proof parameters I processed within consumed amplitude scalar reference

/-- An identically zero branch family contributes no complete quantum vector. -/
lemma coherentPrefix_amplitude_zero (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) (processed : Nat) (within : processed ≤ 34)
    (consumed : Nat) {Reference : Register} (reference : HilbertVector Reference) :
    coherentPrefix parameters I processed within consumed (fun _ => 0) reference = 0 := by
  exact double_sum_amplitude_zero
    (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
    (Branch := GoodBranch I) (Ref := Reference.Index) _ (fun ref => reference ref)

/-- An empty original good component is the zero vector, with no conditioning required. -/
lemma coherentPrefix_of_isEmpty (parameters : Sampling.Parameters ctx)
    (I : DomainParameters.PublicKeyInstance) [IsEmpty (GoodBranch I)]
    (processed : Nat) (within : processed ≤ 34) (consumed : Nat)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) :
    coherentPrefix parameters I processed within consumed amplitude reference = 0 := by
  exact double_sum_amplitude_empty
    (R := ctx.register.prod (Sampling.SourceRegister.prod Reference))
    (Branch := GoodBranch I) (Ref := Reference.Index) _ amplitude (fun ref => reference ref)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
