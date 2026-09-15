/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Mul
import all QuantumAlg.Components.Classical.EllipticCurve.Field.Native.Reduction.Resources

/-!
# Actual original loaded field-multiplication resources

The real full-product event precedes the original modulus loader, division
and resize. Its product, modulus and quotient/remainder cells coexist at the
actual peak. The complete caller context is included in both ownership views.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native

open Execution ClassicalAlgorithms.Modular
open Modular.Reduce.Native

variable {kind : ProblemKind} {ctx : RuntimeCtx kind} {width : Nat}

/-- Original full multiplication precedes the real loaded-reduction event sequence. -/
def multiplicationTrace (kind : ProblemKind) (spec : ModulusSpec width) :
    List (Resource.Event kind) :=
  .classicalOperation (.mulFull width width) :: loadedReductionTrace kind (width + width) spec

/-- Actual full product, loaded modulus and complete quotient/remainder storage. -/
def multiplicationScratchSpace (kind : ProblemKind) (width : Nat) : SpacePool kind :=
  SpacePool.ofShape (.unsignedWord (width + width)) +
    SpacePool.ofShape (.unsignedWord (width + 1)) +
      SpacePool.ofShape (divisionShape (width + width) width)

/-- The original trace survives every real allocation and release exactly. -/
theorem fieldMulIntoWord_eventTrace (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (mulIntoWord spec left right output).Path) :
    (mulIntoWord spec left right output).eventTrace path = multiplicationTrace kind spec := by
  change .classicalOperation (.mulFull width width) ::
    (reduceIntoWord spec (reductionRead (multiplicationProduct ctx width))
      (writeUnderMultiplication output width)).eventTrace path.2 = _
  exact congrArg (List.cons (.classicalOperation (.mulFull width width)))
    (fieldReduceIntoWord_eventTrace _ _ _ path.2)

/-- Every native resource is projected from this same actual original trace. -/
theorem mulIntoWord_resourcePool (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (mulIntoWord spec left right output).Path) :
    (mulIntoWord spec left right output).resourcePool path =
      ResourcePool.ofList (multiplicationTrace kind spec) :=
  congrArg ResourcePool.ofList (fieldMulIntoWord_eventTrace spec left right output path)

/-- The original serial dependency depth includes every actual loader duration. -/
theorem mulIntoWord_durationDepth (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width)) (duration : Resource.Event kind → Nat)
    (path : (mulIntoWord spec left right output).Path) :
    (mulIntoWord spec left right output).depth duration path =
      ((multiplicationTrace kind spec).map duration).sum := by
  change duration (.classicalOperation (.mulFull width width)) +
    (reduceIntoWord spec (reductionRead (multiplicationProduct ctx width))
      (writeUnderMultiplication output width)).depth duration path.2 = _
  exact congrArg (Nat.add (duration (.classicalOperation (.mulFull width width))))
    (reduceIntoWord_durationDepth _ _ _ duration path.2)

/-- All original product and reduction workspaces coexist at the exact resident peak. -/
theorem mulIntoWord_resident (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (mulIntoWord spec left right output).Path) :
    (mulIntoWord spec left right output).peakResidentSpace path =
      multiplicationScratchSpace kind width + ctx.residentSpace := by
  have bodyPeak : (multiplicationPlaced spec left right output).peakResidentSpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape (width + width) width) +
          (multiplicationCtx ctx width).residentSpace := by
    refine (Circuit.peakResidentSpace_seq
      (.classical (Modular.NativePower.productOp (underMultiplication left width)
        (underMultiplication right width) (multiplicationProduct ctx width)))
      (reduceIntoWord spec (reductionRead (multiplicationProduct ctx width))
        (writeUnderMultiplication output width)) path).trans ?_
    rw [reduceIntoWord_resident, Circuit.peakResidentSpace_classical]
    exact SpacePool.max_eq_right le_add_self
  refine (Circuit.peakResidentSpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh
      (multiplicationPlaced spec left right output) path).trans
        ((congrArg (SpacePool.max ctx.residentSpace) bodyPeak).trans ?_)
  have enlarged : ctx.residentSpace ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape (width + width) width) +
          (multiplicationCtx ctx width).residentSpace := le_trans le_add_self le_add_self
  rw [SpacePool.max_eq_right enlarged]
  change _ + _ + (_ + ctx.residentSpace) = _
  unfold multiplicationScratchSpace
  ac_rfl

/-- Each of the three original scratch cells keeps its actual auxiliary role. -/
theorem mulIntoWord_auxiliary (spec : ModulusSpec width)
    (left right : CInputRef ctx (.unsignedWord width))
    (output : CWriteRef ctx (.unsignedWord width))
    (path : (mulIntoWord spec left right output).Path) :
    (mulIntoWord spec left right output).peakAuxiliarySpace path =
      multiplicationScratchSpace kind width + ctx.auxiliarySpace := by
  have bodyPeak : (multiplicationPlaced spec left right output).peakAuxiliarySpace path =
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape (width + width) width) +
          (multiplicationCtx ctx width).auxiliarySpace := by
    refine (Circuit.peakAuxiliarySpace_seq
      (.classical (Modular.NativePower.productOp (underMultiplication left width)
        (underMultiplication right width) (multiplicationProduct ctx width)))
      (reduceIntoWord spec (reductionRead (multiplicationProduct ctx width))
        (writeUnderMultiplication output width)) path).trans ?_
    rw [reduceIntoWord_auxiliary, Circuit.peakAuxiliarySpace_classical]
    exact SpacePool.max_eq_right le_add_self
  refine (Circuit.peakAuxiliarySpace_workspace ctx.canonicalFreshKey
    (.unsignedWord (width + width)) ctx.canonicalFreshKey_fresh
      (multiplicationPlaced spec left right output) path).trans
        ((congrArg (SpacePool.max ctx.auxiliarySpace) bodyPeak).trans ?_)
  have enlarged : ctx.auxiliarySpace ≤
      SpacePool.ofShape (.unsignedWord (width + 1)) +
        SpacePool.ofShape (divisionShape (width + width) width) +
          (multiplicationCtx ctx width).auxiliarySpace := le_trans le_add_self le_add_self
  rw [SpacePool.max_eq_right enlarged]
  change _ + _ + (_ + ctx.auxiliarySpace) = _
  unfold multiplicationScratchSpace
  ac_rfl

/-- The original product and both reduction workspaces occupy this exact number of bits. -/
theorem multiplicationScratch_classicalBits :
    multiplicationScratchSpace kind width .classicalBits = 6 * width + 2 := by
  simp [multiplicationScratchSpace, divisionShape, SpacePool.ofShape, CShape.bitWidth]
  omega

end QuantumAlg.ClassicalRoutines.EllipticCurve.Field.Native
