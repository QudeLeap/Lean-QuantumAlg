/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Local
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Division.Resources
import all QuantumAlg.Primitives.MeasuredUncompute.InPlace.Multiplication.Resources
import all QuantumAlg.Core.Execution.Local.Framing.Resources

/-!
# Actual measured arithmetic inside a physically present runtime frame

Both operations compile their original reusable body beside the actual frame.
They use the already present EEA workspace and measurement cells; preparation
and allocation belong to the enclosing program. Every compiled path pays the
same original native event allowance, and its space includes all frame systems
and cells [LYL+26, sec_point_add/sec_point_add.tex:45-122].

This module constructs real circuits and proves their projected resource
bounds. Arithmetic state correctness is a separate contract; locality alone
does not imply that a workspace has been restored.
-/

namespace QuantumAlg.MeasuredUncompute.InPlaceFraming

noncomputable section

open Execution ContextUnion

variable (modulus : Nat) (prime : Nat.Prime modulus) (frame : RuntimeCtx .quantum)
  (separate : RuntimeCtx.StorageDisjoint (NumeratorMeasurement.context modulus.size) frame)

/-- Execute the original measured division using its existing allocation in the real union. -/
def division :
    Circuit (.quantum AlgorithmGate.model .empty)
      ((NumeratorMeasurement.context modulus.size).disjointUnion frame separate)
      ((NumeratorMeasurement.context modulus.size).disjointUnion frame separate) :=
  frameLocal (InPlaceDivision.body modulus prime)
    (inPlaceDivision_body_isLocal modulus prime) frame separate

/-- Execute the original measured multiplication in that same actual union context. -/
def multiplication :
    Circuit (.quantum AlgorithmGate.model .empty)
      ((NumeratorMeasurement.context modulus.size).disjointUnion frame separate)
      ((NumeratorMeasurement.context modulus.size).disjointUnion frame separate) :=
  frameLocal (InPlaceMultiplication.body modulus prime)
    (inPlaceMultiplication_body_isLocal modulus prime) frame separate

/-- Every real framed division path satisfies the independent original body allowance. -/
theorem division_budget (path : (division modulus prime frame separate).Path) :
    (division modulus prime frame separate).resourcePool path ≤
      InPlaceDivisionResources.bodyBudget modulus.size := by
  let paths := frameLocalPathEquiv (InPlaceDivision.body modulus prime)
    (inPlaceDivision_body_isLocal modulus prime) frame separate
  obtain ⟨original, rfl⟩ := paths.surjective path
  exact (frameLocal_resourcePool (InPlaceDivision.body modulus prime)
    (inPlaceDivision_body_isLocal modulus prime) frame separate original).le.trans
      (InPlaceDivisionResources.body_budget modulus prime original)

/-- Every real framed multiplication path satisfies its independent original body allowance. -/
theorem multiplication_budget (path : (multiplication modulus prime frame separate).Path) :
    (multiplication modulus prime frame separate).resourcePool path ≤
      InPlaceMultiplicationResources.bodyBudget modulus.size := by
  let paths := frameLocalPathEquiv (InPlaceMultiplication.body modulus prime)
    (inPlaceMultiplication_body_isLocal modulus prime) frame separate
  obtain ⟨original, rfl⟩ := paths.surjective path
  exact (frameLocal_resourcePool (InPlaceMultiplication.body modulus prime)
    (inPlaceMultiplication_body_isLocal modulus prime) frame separate original).le.trans
      (InPlaceMultiplicationResources.body_budget modulus prime original)

/-- The original arithmetic context and every real frame cell/system remain resident. -/
theorem division_resident (path : (division modulus prime frame separate).Path) :
    (division modulus prime frame separate).peakResidentSpace path =
      (NumeratorMeasurement.context modulus.size).residentSpace + frame.residentSpace :=
  frameLocal_peakResidentSpace (InPlaceDivision.body modulus prime)
    (inPlaceDivision_body_isLocal modulus prime) frame separate path

/-- Multiplication reuses the same space and includes the same physically resident frame. -/
theorem multiplication_resident (path : (multiplication modulus prime frame separate).Path) :
    (multiplication modulus prime frame separate).peakResidentSpace path =
      (NumeratorMeasurement.context modulus.size).residentSpace + frame.residentSpace :=
  frameLocal_peakResidentSpace (InPlaceMultiplication.body modulus prime)
    (inPlaceMultiplication_body_isLocal modulus prime) frame separate path

end

end QuantumAlg.MeasuredUncompute.InPlaceFraming
