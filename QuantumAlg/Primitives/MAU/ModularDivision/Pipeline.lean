/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularDivision.Basic

/-!
# Modular-division selected pipeline

This module records the inverse/multiply/add/uncompute pipeline and staged
transition invariant for unit-denominator modular division [PZ03,
ecc.tex:622-640].
-/

@[expose] public section

namespace QuantumAlg
namespace ModularDivision

/-! ### Selected division pipeline -/

/-- Coarse stages of the selected unit-denominator division pipeline.  The
route follows the Proos--Zalka decomposition of `x,y <-> x,y/x` into inverse,
multiplication, inverse uncompute, and reverse multiplication cleanup [PZ03,
ecc.tex:622-640]. -/
inductive PipelineStage where
  | computeInverse
  | multiplyQuotient
  | addToTarget
  | uncomputeScratch
deriving DecidableEq

namespace PipelineStage

/-- Human-readable label for a selected division-pipeline stage. -/
def label : PipelineStage -> String
  | computeInverse => "compute-denominator-inverse"
  | multiplyQuotient => "multiply-numerator-by-inverse"
  | addToTarget => "add-quotient-into-target"
  | uncomputeScratch => "uncompute-inverse-and-quotient-scratch"

end PipelineStage

/-- Register roles for the selected division pipeline. -/
structure PipelineRegisterRoles where
  /-- Unit denominator input register. -/
  denominator : String
  /-- Numerator input register. -/
  numerator : String
  /-- Target accumulator register. -/
  target : String
  /-- Scratch register for the denominator inverse. -/
  inverseScratch : String
  /-- Scratch register for the quotient product. -/
  quotientScratch : String
  /-- Temporary cleanup flag register. -/
  cleanupFlag : String
deriving DecidableEq

/-- Register-role certificate for unit-denominator division. -/
def unitDenominatorRegisterRoles : PipelineRegisterRoles where
  denominator := "unit denominator x"
  numerator := "numerator y"
  target := "target accumulator z"
  inverseScratch := "scratch copy of x^{-1}"
  quotientScratch := "scratch copy of y*x^{-1}"
  cleanupFlag := "temporary cleanup flag"

/-- Coarse stages of the selected inverse/multiply/add/uncompute division route. -/
def inverseMultiplyAddUncomputeStages : List PipelineStage :=
  [PipelineStage.computeInverse, PipelineStage.multiplyQuotient,
    PipelineStage.addToTarget, PipelineStage.uncomputeScratch]

/-- Selected unit-denominator division pipeline. -/
structure PipelineSchedule where
  /-- Coarse stages of the inverse-multiply-add-uncompute route. -/
  stages : List PipelineStage
  /-- Register-role annotation for the pipeline. -/
  roles : PipelineRegisterRoles
deriving DecidableEq

/-- Source-backed selected division pipeline. -/
def selectedPipelineSchedule : PipelineSchedule where
  stages := inverseMultiplyAddUncomputeStages
  roles := unitDenominatorRegisterRoles

@[simp] theorem selectedPipelineSchedule_stages :
    selectedPipelineSchedule.stages = inverseMultiplyAddUncomputeStages :=
  rfl

/-! ### Pipeline transition model -/

/-- Coarse proof phase for the selected division pipeline. -/
inductive PipelinePhase where
  | initial
  | inverseComputed
  | quotientComputed
  | targetUpdated
  | scratchUncomputed
deriving DecidableEq

/-- Abstract state carried by the division-pipeline proof. -/
structure PipelineState (N : Nat) where
  /-- Unit denominator input. -/
  denominator : (ZMod N)ˣ
  /-- Numerator residue input. -/
  numerator : ZMod N
  /-- Target accumulator register. -/
  target : ZMod N
  /-- Scratch register for the denominator inverse. -/
  inverseScratch : ZMod N
  /-- Scratch register for the quotient residue. -/
  quotientScratch : ZMod N
  /-- Temporary cleanup flag for the staged model. -/
  flag : Bool
deriving DecidableEq

instance instFintypePipelineState (N : Nat) [NeZero N] :
    Fintype (PipelineState N) := by
  classical
  let e :
      PipelineState N ≃
        ((ZMod N)ˣ × ZMod N × ZMod N × ZMod N × ZMod N × Bool) := {
    toFun := fun s =>
      (s.denominator, s.numerator, s.target, s.inverseScratch,
        s.quotientScratch, s.flag)
    invFun := fun x =>
      { denominator := x.1
        numerator := x.2.1
        target := x.2.2.1
        inverseScratch := x.2.2.2.1
        quotientScratch := x.2.2.2.2.1
        flag := x.2.2.2.2.2 }
    left_inv := by
      intro s
      cases s
      rfl
    right_inv := by
      intro x
      rcases x with ⟨denominator, rest⟩
      rcases rest with ⟨numerator, rest'⟩
      rcases rest' with ⟨target, rest''⟩
      rcases rest'' with ⟨inverseScratch, rest'''⟩
      rcases rest''' with ⟨quotientScratch, flag⟩
      rfl
  }
  exact
    Fintype.ofEquiv
      ((ZMod N)ˣ × ZMod N × ZMod N × ZMod N × ZMod N × Bool) e.symm

namespace PipelineState

/-- Initial clean state before computing the denominator inverse. -/
def initial {N : Nat} (u : (ZMod N)ˣ) (v z : ZMod N) :
    PipelineState N where
  denominator := u
  numerator := v
  target := z
  inverseScratch := 0
  quotientScratch := 0
  flag := false

/-- Compute the denominator inverse into scratch. -/
def computeInverse {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := ModularInversion.inverseResidue s.denominator
  quotientScratch := s.quotientScratch
  flag := s.flag

/-- Multiply the numerator by the inverse scratch into quotient scratch. -/
def multiplyQuotient {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := s.inverseScratch
  quotientScratch := s.numerator * s.inverseScratch
  flag := s.flag

/-- Add the quotient scratch into the target register. -/
def addQuotientToTarget {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target + s.quotientScratch
  inverseScratch := s.inverseScratch
  quotientScratch := s.quotientScratch
  flag := s.flag

/-- Uncompute both scratch registers and restore the clean flag. -/
def uncomputeScratch {N : Nat} (s : PipelineState N) : PipelineState N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  inverseScratch := 0
  quotientScratch := 0
  flag := false

/-- Forget the internal scratch registers and return to the endpoint data shape. -/
def toData {N : Nat} (s : PipelineState N) : Data N where
  denominator := s.denominator
  numerator := s.numerator
  target := s.target
  flag := s.flag

/-- Run the selected coarse division pipeline on clean input. -/
def run {N : Nat} (u : (ZMod N)ˣ) (v z : ZMod N) : PipelineState N :=
  uncomputeScratch
    (addQuotientToTarget
      (multiplyQuotient
        (computeInverse (initial u v z))))

@[simp] theorem run_denominator {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).denominator = u :=
  rfl

@[simp] theorem run_numerator {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).numerator = v :=
  rfl

@[simp] theorem run_target {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).target = z + quotientResidue u v :=
  rfl

@[simp] theorem run_inverseScratch {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).inverseScratch = 0 :=
  rfl

@[simp] theorem run_quotientScratch {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).quotientScratch = 0 :=
  rfl

@[simp] theorem run_flag {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).flag = false :=
  rfl

/-- Final-value theorem for the selected coarse division pipeline. -/
theorem run_final {N : Nat} (u : (ZMod N)ˣ) (v z : ZMod N) :
    run u v z =
      { denominator := u
        numerator := v
        target := z + quotientResidue u v
        inverseScratch := 0
        quotientScratch := 0
        flag := false } :=
  rfl

/-- The selected pipeline agrees with the endpoint permutation after forgetting
the internal scratch registers. -/
theorem run_toData_eq_addQuotientIntoTarget {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    (run u v z).toData =
      ({ denominator := u, numerator := v, target := z, flag := false } :
        Data N).addQuotientIntoTarget :=
  rfl

/-- Coarse invariant for the selected division pipeline. -/
def Invariant {N : Nat} (u : (ZMod N)ˣ) (v z : ZMod N) :
    PipelinePhase -> PipelineState N -> Prop
  | PipelinePhase.initial, s =>
      s.denominator = u ∧ s.numerator = v ∧ s.target = z ∧
        s.inverseScratch = 0 ∧ s.quotientScratch = 0 ∧ s.flag = false
  | PipelinePhase.inverseComputed, s =>
      s.denominator = u ∧ s.numerator = v ∧ s.target = z ∧
        s.inverseScratch = ModularInversion.inverseResidue u ∧
        s.quotientScratch = 0 ∧ s.flag = false
  | PipelinePhase.quotientComputed, s =>
      s.denominator = u ∧ s.numerator = v ∧ s.target = z ∧
        s.inverseScratch = ModularInversion.inverseResidue u ∧
        s.quotientScratch = quotientResidue u v ∧ s.flag = false
  | PipelinePhase.targetUpdated, s =>
      s.denominator = u ∧ s.numerator = v ∧ s.target = z + quotientResidue u v ∧
        s.inverseScratch = ModularInversion.inverseResidue u ∧
        s.quotientScratch = quotientResidue u v ∧ s.flag = false
  | PipelinePhase.scratchUncomputed, s =>
      s.denominator = u ∧ s.numerator = v ∧ s.target = z + quotientResidue u v ∧
        s.inverseScratch = 0 ∧ s.quotientScratch = 0 ∧ s.flag = false

@[simp] theorem initial_invariant {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Invariant u v z PipelinePhase.initial (initial u v z) := by
  simp [Invariant, initial]

@[simp] theorem computeInverse_invariant {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Invariant u v z PipelinePhase.inverseComputed
      (computeInverse (initial u v z)) := by
  simp [Invariant, initial, computeInverse]

@[simp] theorem multiplyQuotient_invariant {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Invariant u v z PipelinePhase.quotientComputed
      (multiplyQuotient (computeInverse (initial u v z))) := by
  simp [Invariant, quotientResidue, initial, computeInverse, multiplyQuotient]

@[simp] theorem addQuotientToTarget_invariant {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Invariant u v z PipelinePhase.targetUpdated
      (addQuotientToTarget
        (multiplyQuotient (computeInverse (initial u v z)))) := by
  simp [Invariant, quotientResidue, initial, computeInverse, multiplyQuotient,
    addQuotientToTarget]

@[simp] theorem run_invariant {N : Nat}
    (u : (ZMod N)ˣ) (v z : ZMod N) :
    Invariant u v z PipelinePhase.scratchUncomputed (run u v z) := by
  simp [Invariant, quotientResidue, run, initial, computeInverse,
    multiplyQuotient, addQuotientToTarget, uncomputeScratch]

/-- The final invariant implies the quotient value and clean scratch registers. -/
theorem final_value_of_invariant {N : Nat}
    {u : (ZMod N)ˣ} {v z : ZMod N} {s : PipelineState N}
    (h : Invariant u v z PipelinePhase.scratchUncomputed s) :
    s.target = z + quotientResidue u v ∧
      s.inverseScratch = 0 ∧ s.quotientScratch = 0 ∧ s.flag = false := by
  exact ⟨h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

end PipelineState


end ModularDivision
end QuantumAlg
