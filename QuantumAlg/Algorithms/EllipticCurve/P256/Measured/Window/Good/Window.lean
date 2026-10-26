/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Good.Step
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Storage.Parameters
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Sampling.Source.Affine

/-!
# Admissible chronological affine geometry

The original branch predicate supplies the exact current and next affine
points and excludes the selected exceptional points. These geometric facts
feed the actual named point action proved in `Good.Action`.
-/

namespace QuantumAlg.EllipticCurve.P256.Measured.Window.Good

noncomputable section

open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Driver

open Execution PrimeFieldShortWeierstrass
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window
open PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Window.Sampling
open QuantumFourierTransform.Semiclassical
open QuantumFourierTransform.Semiclassical.Window
open QuantumFourierTransform.Semiclassical.Window.Source

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

attribute [local irreducible] PrimeFieldShortWeierstrass.Arithmetic.P256.modulus
  sourceBlank Inversion.Seed.blank

/-! The following bridges feed the same actual point certificate; none assumes its action. -/

private lemma fed_affine_enabled {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) (point : AffinePoint (actualCurveSpec I).curve) :
    let index := Sampling.chronologicalIndex position
    let fed := Sampling.sourceFedRaw parameters index (sourceBranch I branch)
      (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        point (false, false, false) 0)
    Driver.driverAffineEnabled (parameters.pointParameters index)
        (actualCurveSpec I) (actualCurveSpec_modulus I) point fed.1.2 fed.2 =
      FullRange.chronologicalSelected I branch position := by
  dsimp only
  let index := Sampling.chronologicalIndex position
  let blank := Driver.driverAffineBlank (actualCurveSpec I)
    (actualCurveSpec_modulus I) point (false, false, false) 0
  let fed := Sampling.sourceFedRaw parameters index (sourceBranch I branch) blank
  have blankEq := fed_affine_blank parameters index (sourceBranch I branch)
    (actualCurveSpec I) (actualCurveSpec_modulus I) point
  have enabled := driver_enabled_blank (parameters.pointParameters index)
    (actualCurveSpec I) (actualCurveSpec_modulus I) point fed.1.2 fed.2
  have restored := congrArg (Chain.Control.digitEnabled index.stream index.lowerWidth
    index.lowerWidth_bound) blankEq.symm
  have digit := sourceFedRaw_enabled parameters index (sourceBranch I branch) blank
  have selected := sampling_sourcePartition_chronologicalSelected parameters I branch position
  have actual : Driver.driverAffineEnabled (parameters.pointParameters index)
      (actualCurveSpec I) (actualCurveSpec_modulus I) point fed.1.2 fed.2 =
        Chain.Control.digitEnabled index.stream index.lowerWidth index.lowerWidth_bound
          (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
            point fed.1.2 fed.2) := by
    simpa only [Sampling.Parameters.pointParameters, index.addressWidth] using enabled
  exact actual.trans (restored.trans (digit.trans selected))


private lemma fed_affine_address {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (position : Fin 34) (point : AffinePoint (actualCurveSpec I).curve) :
    let index := Sampling.chronologicalIndex position
    let fed := Sampling.sourceFedRaw parameters index (sourceBranch I branch)
      (Driver.driverAffineBlank (actualCurveSpec I) (actualCurveSpec_modulus I)
        point (false, false, false) 0)
    (Driver.driverSelectedRow (parameters.pointParameters index)
      (actualCurveSpec I) (actualCurveSpec_modulus I) point fed.1.2 fed.2).val =
        FullRange.chronologicalAddress I branch position := by
  dsimp only
  have current := fed_affine_address_current parameters (Sampling.chronologicalIndex position)
    (sourceBranch I branch) (actualCurveSpec I) (actualCurveSpec_modulus I) point
  exact current.trans
    (sampling_sourcePartition_chronologicalAddress parameters I branch position)


private lemma sampler_point_references {outer ctx : RuntimeCtx .quantum}
    (original : Sampling.Storage.Inputs outer) (lift : ClassicalWorkspace.Transport outer ctx)
    (same : outer.quantumLayout.wires = ctx.quantumLayout.wires)
    (scratch : Sampling.Storage.Frame ctx 256 256)
    (fresh : Sampling.Storage.CallerFree scratch lift) (index : Sampling.WindowIndex) :
    Driver.driverScratchReferences
      ((original.samplerParameters lift same scratch fresh).pointParameters index)
      scratch (fun bit => Fin.castLE index.lowCapacity bit) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

section PrefixGeometryElaboration

attribute [local irreducible] prefixAffine branchGood

/-- Reuse the original affine prefix facts in the concrete curve's own group instance. -/
private lemma prefix_affine_geometry (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34)
    (firstBound : position.val ≤ 34) (resultBound : position.val + 1 ≤ 34)
    (prime : Fact DomainParameters.fieldModulus.Prime) :
    letI : Fact DomainParameters.fieldModulus.Prime := prime
    Driver.affineRowGeometry
      (Group := (DomainParameters.curve I.curveCert).MathlibPoint)
      (FullRange.chronologicalSelected I branch position)
      (prefixAffine I branch good position.val firstBound).toMathlib
      (prefixAffine I branch good (position.val + 1) resultBound).toMathlib
      (FullRange.chronologicalAddress I branch position • chronologicalBasePoint I position) := by
  have primeSame : prime =
      (⟨(DomainParameters.curve I.curveCert).prime⟩ : Fact DomainParameters.fieldModulus.Prime) :=
    Subsingleton.elim _ _
  subst prime
  have firstSame : firstBound = position.isLt.le := Subsingleton.elim _ _
  have resultSame : resultBound = Nat.succ_le_of_lt position.isLt := Subsingleton.elim _ _
  subst firstBound
  subst resultBound
  let : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  exact ⟨prefixAffine_exclusions I branch good position, prefixAffine_next I branch good position⟩

/-- Transport only opaque group values; scalar multiplication stays in the concrete caller. -/
private lemma affineRowGeometry_transport {Group : Type} [AddGroup Group]
    (enabled selected : Bool) (first result actualAddend expectedAddend : Group)
    (sameEnabled : enabled = selected) (sameAddend : actualAddend = expectedAddend)
    (geometry : Driver.affineRowGeometry selected first result expectedAddend) :
    Driver.affineRowGeometry enabled first result actualAddend := by
  cases sameEnabled
  cases sameAddend
  exact geometry

/-- The actual fed row has the admissible affine geometry for the same physical
source branch, selected address and chronological table base. The concrete
caller reads that same certified base from its original retained rows. -/
private def FedGeometryStatement : Prop :=
  ∀ {ctx : RuntimeCtx .quantum}
    (parameters : Sampling.Parameters ctx) (I : DomainParameters.PublicKeyInstance)
    (branch : EllipticCurve.FullRange.Branch (Cascade.exponentWidth I))
    (good : branchGood I branch) (position : Fin 34),
    letI : Fact DomainParameters.fieldModulus.Prime :=
      ⟨(DomainParameters.curve I.curveCert).prime⟩
    let firstBound : position.val ≤ 34 := position.isLt.le
    let resultBound : position.val + 1 ≤ 34 := Nat.succ_le_of_lt position.isLt
    let index := Sampling.chronologicalIndex position
    let first := prefixAffine I branch good position.val firstBound
    let result := prefixAffine I branch good (position.val + 1) resultBound
    let fed := Sampling.sourceFedRaw parameters index (sourceBranch I branch)
      (Driver.driverAffineBlank (actualCurveSpec I)
        (actualCurveSpec_modulus I) first (false, false, false) 0)
    Driver.affineRowGeometry
      (Group := (DomainParameters.curve I.curveCert).MathlibPoint)
      (Driver.driverAffineEnabled (parameters.pointParameters index)
        (actualCurveSpec I) (actualCurveSpec_modulus I) first fed.1.2 fed.2)
      first.toMathlib result.toMathlib
      ((Driver.driverSelectedRow (parameters.pointParameters index)
        (actualCurveSpec I) (actualCurveSpec_modulus I) first fed.1.2 fed.2).val •
          chronologicalBasePoint I position)

attribute [local irreducible] FedGeometryStatement Driver.affineRowGeometry

private lemma point_prefix_fed_geometry : FedGeometryStatement := by
  unfold FedGeometryStatement
  intro ctx parameters I branch good position firstBound resultBound index first result fed
  let prime : Fact DomainParameters.fieldModulus.Prime :=
    ⟨(DomainParameters.curve I.curveCert).prime⟩
  let : Fact DomainParameters.fieldModulus.Prime := prime
  let enabled := Driver.driverAffineEnabled (parameters.pointParameters index)
    (actualCurveSpec I) (actualCurveSpec_modulus I) first fed.1.2 fed.2
  let address := (Driver.driverSelectedRow (parameters.pointParameters index)
    (actualCurveSpec I) (actualCurveSpec_modulus I) first fed.1.2 fed.2).val
  have sameAddend := congrArg
    (fun value : Nat => value • chronologicalBasePoint I position)
    (fed_affine_address parameters I branch position first)
  exact affineRowGeometry_transport
    (Group := (DomainParameters.curve I.curveCert).MathlibPoint)
    enabled (FullRange.chronologicalSelected I branch position)
    first.toMathlib result.toMathlib
    (address • chronologicalBasePoint I position)
    (FullRange.chronologicalAddress I branch position • chronologicalBasePoint I position)
    (fed_affine_enabled parameters I branch position first) sameAddend
    (prefix_affine_geometry I branch good position firstBound resultBound prime)

end PrefixGeometryElaboration

end

end QuantumAlg.EllipticCurve.P256.Measured.Window.Good
