/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.StoreMachine.Recovery.Lattice.Target.Wide.Program

/-!
# Actual wide-target agreement with the original short-log samples

The two original sample words produce exact unwrapped preimages in the supplied
width. Actual stored-bit centering yields the original pure lattice target.
Only the unmodified third coordinate requires its original initial zero.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine

open Execution
open ClassicalRoutines.NumberTheory.SignedWord

noncomputable section

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {m ell width : Nat}

/-- Both actual preimages retain every read outside their two original destination cells. -/
theorem preimages_callerFrame (refs : Refs ctx m ell width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape) (avoids : AvoidsPreimageWrites other refs) :
    (preimagesStep refs store).1.read other = store.read other :=
  (scaleKInto_callerFrame refs.second _ other avoids.2).trans
    (scaleKInto_callerFrame refs.first store other avoids.1)

/-- The first original preimage survives the actual second scaling call. -/
theorem preimages_first (refs : Refs ctx m ell width) (separation : Separation refs)
    (store : Store ctx) (sourceFits : ell + m + 1 ≤ width) :
    ((preimagesStep refs store).1.read refs.target.first.a).toNat =
      2 ^ m * (store.read refs.first.k).toNat := by
  rw [refs.firstInput]
  change ((scaleKStep refs.second (scaleKStep refs.first store).1).1.read
    (writeInput refs.first.scaled)).toNat = _
  rw [scaleKInto_callerFrame refs.second _ _ separation.firstScaledAvoidsSecond]
  exact scaleKInto_read refs.first store sourceFits

/-- The actual second scaling call reads the original second sample component. -/
theorem preimages_second (refs : Refs ctx m ell width) (separation : Separation refs)
    (store : Store ctx) (sourceFits : ell + m + 1 ≤ width) :
    ((preimagesStep refs store).1.read refs.target.second.a).toNat =
      2 ^ m * (store.read refs.second.k).toNat := by
  rw [refs.secondInput]
  change ((scaleKStep refs.second (scaleKStep refs.first store).1).1.read
    (writeInput refs.second.scaled)).toNat = _
  rw [scaleKInto_read refs.second _ sourceFits,
    scaleKInto_callerFrame refs.first store _ separation.secondKAvoidsFirst]

/-- Every actual read outside the original two preimage and eight centering writes is preserved. -/
theorem loadTargetInto_callerFrame (refs : Refs ctx m ell width) (store : Store ctx)
    {shape : CShape} (other : CInputRef ctx shape)
    (preimages : AvoidsPreimageWrites other refs)
    (first : LatticeTargetPoint.AvoidsTargetWrites other refs.target.first)
    (second : LatticeTargetPoint.AvoidsTargetWrites other refs.target.second) :
    (targetStep refs store).1.read other = store.read other :=
  (LatticeTargetPoint.loadTargetPointInto_callerFrame refs.target _ other first second).trans
    (preimages_callerFrame refs store other preimages)

/-- The actual supplied scaled inputs and modulus define precisely the original sample target. -/
theorem prepared_sourcePoint (refs : Refs ctx m ell width) (separation : Separation refs)
    (store : Store ctx) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (sourceFits : ell + m + 1 ≤ width) (first : SampleKRepresents store refs.first.k samples.1)
    (second : SampleKRepresents store refs.second.k samples.2)
    (modulus : (store.read refs.modulus).toNat = 2 ^ (ell + m)) :
    LatticeTargetPoint.sourcePoint refs.target (preimagesStep refs store).1 =
      RSA.shortLogLatticeTarget m ell samples := by
  have firstA := (preimages_first refs separation store sourceFits).trans
    (congrArg (fun k => 2 ^ m * k) first)
  have secondA := (preimages_second refs separation store sourceFits).trans
    (congrArg (fun k => 2 ^ m * k) second)
  have modulusFrame := preimages_callerFrame refs store refs.modulus
    separation.modulusAvoidsPreimages
  unfold LatticeTargetPoint.sourcePoint RSA.shortLogLatticeTarget
  rw [firstA, secondA, refs.firstModulus, refs.secondModulus, modulusFrame, modulus,
    RSA.ShortLogTarget.centeredValue_eq_shortLogTargetCoordinate,
    RSA.ShortLogTarget.centeredValue_eq_shortLogTargetCoordinate]

/-- The complete actual wide-target output represents the original pure short-log target. -/
theorem loadTargetInto_represents (refs : Refs ctx m ell width) (separation : Separation refs)
    (store : Store ctx) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (sourceFits : ell + m + 1 ≤ width) (first : SampleKRepresents store refs.first.k samples.1)
    (second : SampleKRepresents store refs.second.k samples.2)
    (modulus : (store.read refs.modulus).toNat = 2 ^ (ell + m))
    (thirdZero : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.target.point.third)) 0) :
    LatticeArithmetic.PointRawRepresents (targetStep refs store).1 refs.target.point
      (RSA.shortLogLatticeTarget m ell samples) := by
  have third : RawSignedRepresents ((preimagesStep refs store).1.read
      (LatticeState.coordinateInput refs.target.point.third)) 0 := by
    rw [preimages_callerFrame refs store _ separation.thirdAvoidsPreimages]
    exact thirdZero
  have target := LatticeTargetPoint.loadTargetPointInto_represents refs.target separation.target
    (preimagesStep refs store).1 third
  rw [prepared_sourcePoint refs separation store samples sourceFits first second modulus] at target
  exact target

/-- Exact original pure target and complete actual ten-write caller frame. -/
structure TargetOutcome (refs : Refs ctx m ell width)
    (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (before after : Store ctx) : Prop where
  target : LatticeArithmetic.PointRawRepresents after refs.target.point
    (RSA.shortLogLatticeTarget m ell samples)
  callerFrame : ∀ {shape : CShape} (other : CInputRef ctx shape),
    AvoidsPreimageWrites other refs →
      LatticeTargetPoint.AvoidsTargetWrites other refs.target.first →
        LatticeTargetPoint.AvoidsTargetWrites other refs.target.second →
          after.read other = before.read other

/-- Actual wide-target loading meets the original sample contract with explicit scratch reset. -/
theorem loadTargetInto_correct (refs : Refs ctx m ell width) (separation : Separation refs)
    (store : Store ctx) (samples : RSA.ShortLogSample m ell × RSA.ShortLogSample m ell)
    (sourceFits : ell + m + 1 ≤ width) (first : SampleKRepresents store refs.first.k samples.1)
    (second : SampleKRepresents store refs.second.k samples.2)
    (modulus : (store.read refs.modulus).toNat = 2 ^ (ell + m))
    (thirdZero : RawSignedRepresents
      (store.read (LatticeState.coordinateInput refs.target.point.third)) 0) :
    TargetOutcome refs samples store (targetStep refs store).1 :=
  ⟨loadTargetInto_represents refs separation store samples sourceFits first second modulus
      thirdZero,
    loadTargetInto_callerFrame refs store⟩

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.LatticeWideTargetMachine
