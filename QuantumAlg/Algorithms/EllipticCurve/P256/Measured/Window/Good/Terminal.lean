/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Vector.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Endpoints
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Row.Injective
import all
QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Driver.Specification.Injective
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Recovery.Fourier.Effects
import all QuantumAlg.Core.Base.State.Vector.Gram.Coherent
import Batteries.Tactic.GeneralizeProofs

/-!
# Exact terminal collisions of the complete coherent good component

At the final cursor the mathematical source is fully consumed. The actual
blank point workspace and the original ideal group-output label identify
exactly the same pairs of admissible branches. Their coherent sums therefore
have the same norm, including all collisions and Reference cross terms.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open Execution PrimeFieldShortWeierstrass ECDLP.Measured
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open scoped BigOperators

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label
local instance (proposition : Prop) : Decidable proposition := Classical.propDecidable proposition

attribute [local irreducible] branchGood prefixAffine

private lemma prefixAffine_terminal_idealLabel (I : DomainParameters.PublicKeyInstance)
    (branch : GoodBranch I) :
    (prefixAffine I branch.val branch.property 34 (Nat.le_refl 34)).toGroupPoint =
      (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) branch.val).val :=
  prefixAffine_terminal_group I branch.val branch.property (Nat.le_refl 34)

private lemma prefixAffine_terminal_idealLabel_witnesses
    (I : DomainParameters.PublicKeyInstance) (branch : GoodBranch I)
    (good : branchGood I branch.val) (within : 34 ≤ 34) :
    (prefixAffine I branch.val good 34 within).toGroupPoint =
      (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I) branch.val).val := by
  have goodSame : good = branch.property := Subsingleton.elim _ _
  subst good
  have withinSame : within = Nat.le_refl 34 := Subsingleton.elim _ _
  subst within
  exact prefixAffine_terminal_idealLabel I branch

private lemma collisions_of_same_representations
    {Branch Point Raw Physical Label GroupLabel : Type}
    (encode : Point → Raw) (encodeFaithful : Function.Injective encode)
    (place : Raw → Physical) (placeFaithful : Function.Injective place)
    (pointGroup : Point → GroupLabel) (pointFaithful : Function.Injective pointGroup)
    (labelGroup : Label → GroupLabel) (labelFaithful : Function.Injective labelGroup)
    (points : Branch → Point) (labels : Branch → Label)
    (represented : ∀ branch, pointGroup (points branch) = labelGroup (labels branch))
    (first last : Branch) :
    place (encode (points first)) = place (encode (points last)) ↔
      labels first = labels last := by
  rw [placeFaithful.eq_iff, encodeFaithful.eq_iff, ← pointFaithful.eq_iff,
    represented first, represented last, labelFaithful.eq_iff]

/-- The actual complete point workspace has exactly the original group-output collisions. -/
lemma terminal_physicalLabel_eq_iff {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (first last : GoodBranch I) :
    parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (prefixAffine I first.val first.property 34 (Nat.le_refl 34))
          (false, false, false) 0) =
      parameters.physicalLabel
        (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
          (prefixAffine I last.val last.property 34 (Nat.le_refl 34))
          (false, false, false) 0) ↔
      idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
          (FullRange.chronologicalFixedSeed I) first.val =
        idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
          (FullRange.chronologicalFixedSeed I) last.val := by
  exact collisions_of_same_representations
    (Branch := GoodBranch I)
    (Point := AffinePoint (DomainParameters.curve I.curveCert))
    (Raw := PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Raw)
    (Physical := ctx.register.Index)
    (Label := (idealGroupRegister (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      (FullRange.chronologicalFixedSeed I)).Index)
    (GroupLabel := (DomainParameters.curve I.curveCert).GroupPoint)
    (fun point : AffinePoint (DomainParameters.curve I.curveCert) =>
      Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        point (false, false, false) 0)
    (Driver.driverAffineBlank_injective (actualCurveSpec I) (actualCurveSpec_modulus I)
      (false, false, false) 0)
    parameters.physicalLabel parameters.physicalLabel_injective
    AffinePoint.toGroupPoint AffinePoint.toGroupPoint_injective
    Subtype.val Subtype.val_injective
    (fun branch : GoodBranch I =>
      prefixAffine I branch.val branch.property 34 (Nat.le_refl 34))
    (fun branch : GoodBranch I => idealGroupLabel
      (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      (FullRange.chronologicalFixedSeed I) branch.val)
    (prefixAffine_terminal_idealLabel I) first last

private def terminalEncode (I : DomainParameters.PublicKeyInstance) :
    AffinePoint (DomainParameters.curve I.curveCert) →
      PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Raw :=
  fun point => Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
    point (false, false, false) 0

private lemma terminalEncode_injective (I : DomainParameters.PublicKeyInstance) :
    Function.Injective (terminalEncode I) :=
  Driver.driverAffineBlank_injective (actualCurveSpec I) (actualCurveSpec_modulus I)
    (false, false, false) 0

private lemma point_collisions_of_representations
    {Point Label Group : Type}
    (pointMap : Point → Group) (pointFaithful : Function.Injective pointMap)
    (labelMap : Label → Group) (labelFaithful : Function.Injective labelMap)
    (first last : Point) (firstLabel lastLabel : Label)
    (firstRep : pointMap first = labelMap firstLabel)
    (lastRep : pointMap last = labelMap lastLabel) :
    first = last ↔ firstLabel = lastLabel := by
  rw [← pointFaithful.eq_iff, firstRep, lastRep, labelFaithful.eq_iff]

private def terminalNormStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (within : 34 ≤ 34) (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference),
    ‖coherentPrefix (ctx := ctx) parameters I 34 within 520 amplitude
        (Reference := Reference) reference‖ =
      ‖∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (amplitude branch * reference ref) •
          (NormalizedVector.ket
            (R := (idealGroupRegister
              (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I)).prod Reference)
            (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I) branch.val, ref)).vec‖

private lemma terminalNormStatement_proof : terminalNormStatement := by
  intro ctx parameters I within amplitude Reference reference
  unfold coherentPrefix coherentLabel
  refine HilbertVector.norm_sum_sum_smul_ket_eq_of_eq_iff
    (Branch := GoodBranch I) (Physical := ctx.register) (Source := Sampling.SourceRegister)
    (Group := idealGroupRegister (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
      (FullRange.chronologicalFixedSeed I)) (Reference := Reference)
    _ _ (0, 0) _ ?_ ?_ amplitude reference
  · intro branch
    exact Sampling.remainingSource_terminal (sourceBranch I branch.val)
  · intro first last
    rw [parameters.physicalLabel_injective.eq_iff]
    change terminalEncode I _ = terminalEncode I _ ↔ _
    rw [(terminalEncode_injective I).eq_iff]
    refine point_collisions_of_representations
      (Point := AffinePoint (DomainParameters.curve I.curveCert))
      (Label := (idealGroupRegister (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
        (FullRange.chronologicalFixedSeed I)).Index)
      (Group := (DomainParameters.curve I.curveCert).GroupPoint)
      AffinePoint.toGroupPoint AffinePoint.toGroupPoint_injective
      Subtype.val Subtype.val_injective _ _ _ _ ?_ ?_
    · generalize_proofs certificate actualGood
      have certificateSame : certificate = I.curveCert := Subsingleton.elim _ _
      subst certificate
      exact prefixAffine_terminal_idealLabel_witnesses I first actualGood within
    · generalize_proofs certificate actualGood
      have certificateSame : certificate = I.curveCert := Subsingleton.elim _ _
      subst certificate
      exact prefixAffine_terminal_idealLabel_witnesses I last actualGood within

/-- Terminal physical and original group-label coherent sums retain exactly the same norm. -/
lemma coherentPrefix_terminal_norm {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (amplitude : GoodBranch I → ℂ) {Reference : Register}
    (reference : HilbertVector Reference) :
    ‖coherentPrefix (ctx := ctx) parameters I 34 (Nat.le_refl 34) 520 amplitude
        (Reference := Reference) reference‖ =
      ‖∑ branch : GoodBranch I, ∑ ref : Reference.Index,
        (amplitude branch * reference ref) •
          (NormalizedVector.ket
            (R := (idealGroupRegister
              (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I)).prod Reference)
            (idealGroupLabel (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
              (FullRange.chronologicalFixedSeed I) branch.val, ref)).vec‖ :=
  terminalNormStatement_proof (ctx := ctx) parameters I (Nat.le_refl 34) amplitude
    (Reference := Reference) reference

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
