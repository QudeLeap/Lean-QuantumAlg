/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.FullRange.Geometry.Expansion

/-!
# The unchanged original good-vector expansion with its explicit finite enumeration

Predicate equality and Fintype equality are eliminated
at an abstract finite-family boundary. No concrete finite universe is computed,
and the accepted original goodVector_expansion proof remains unchanged.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open scoped BigOperators

private lemma subtype_double_sum_eq {Input Ref : Type} [Fintype Ref]
    {Value : Type*} [AddCommMonoid Value] {firstPredicate lastPredicate : Input → Prop}
    (same : ∀ input, firstPredicate input ↔ lastPredicate input)
    (first : Fintype {input // firstPredicate input})
    (last : Fintype {input // lastPredicate input}) (family : Input → Ref → Value) :
    (letI := first
      ∑ input : {input // firstPredicate input}, ∑ ref : Ref, family input.val ref) =
      (letI := last
        ∑ input : {input // lastPredicate input}, ∑ ref : Ref, family input.val ref) := by
  have predicates : firstPredicate = lastPredicate := funext fun input => propext (same input)
  cases predicates
  have enumerations : first = last := Subsingleton.elim _ _
  cases enumerations
  rfl

/-- The current good-branch predicate is precisely the original admissible support. -/
lemma branchGood_iff_original (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I)) :
    branchGood I branch ↔
      branch ∈ EllipticCurve.FullRange.admissibleBranches (Cascade.exponentWidth I) 34
        (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
        (FullRange.chronologicalFixedSeed I).toGroupPoint := Iff.rfl

attribute [local irreducible] branchGood

/-- The original complete good vector uses the same amplitudes under the current enumeration. -/
lemma original_goodVector_expansion (I : DomainParameters.PublicKeyInstance)
    {Reference : Register} (reference : NormalizedVector Reference) :
    EllipticCurve.FullRange.Geometry.goodVector (Cascade.exponentWidth I) 34
        (FullRange.chronologicalSelected I) (FullRange.chronologicalAddend I)
        (FullRange.chronologicalFixedSeed I).toGroupPoint reference =
      ∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch.val *
          reference ref) •
          (NormalizedVector.ket
            (R := (EllipticCurve.FullRange.Geometry.branchRegister
              (Cascade.exponentWidth I)).prod Reference) (branch.val, ref)).vec := by
  refine (EllipticCurve.FullRange.Geometry.goodVector_expansion
    (Cascade.exponentWidth I) 34 (FullRange.chronologicalSelected I)
    (FullRange.chronologicalAddend I) (FullRange.chronologicalFixedSeed I).toGroupPoint
    reference).trans ?_
  exact subtype_double_sum_eq (fun branch => (branchGood_iff_original I branch).symm)
    inferInstance (goodBranchFintype I) (fun branch ref =>
      (EllipticCurve.FullRange.branchAmplitude (Cascade.exponentWidth I) branch *
        reference ref) •
        (NormalizedVector.ket
          (R := (EllipticCurve.FullRange.Geometry.branchRegister
            (Cascade.exponentWidth I)).prod Reference) (branch, ref)).vec)

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
