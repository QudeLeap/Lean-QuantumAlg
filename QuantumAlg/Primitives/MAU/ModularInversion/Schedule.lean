/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.MAU.ModularInversion.Basic

/-!
# Modular-inversion selected schedule

This module records the fixed-round Montgomery-Kaliski schedule,
register-role annotation, and stage-transition invariant for unit-domain
modular inversion [RNSL17, ECDLP.tex:390-465,753-755].
-/

@[expose] public section

namespace QuantumAlg
namespace ModularInversion

/-! ### Selected inversion schedule -/

/-- Coarse stages of the selected unit-domain inversion route.  The selected
source route is the fixed-round Montgomery-Kaliski inverse from RNSL17:
run the reversible binary-GCD round for `2n` iterations, copy the inverse into
the target, and run the computation backwards for cleanup [RNSL17,
ECDLP.tex:390-465,753-755]. -/
inductive ScheduleStage where
  | computeInverse
  | addToTarget
  | uncomputeInverse
deriving DecidableEq

namespace ScheduleStage

/-- Human-readable label for the selected schedule stage. -/
def label : ScheduleStage -> String
  | computeInverse => "compute-montgomery-inverse"
  | addToTarget => "add-inverse-into-target"
  | uncomputeInverse => "uncompute-montgomery-inverse"

end ScheduleStage

/-- Register roles used by the selected fixed-round modular-inversion schedule.
The intermediate names mirror the `u,v,r,s,k,f,m_i` registers in the RNSL17
Montgomery-Kaliski circuit [RNSL17, ECDLP.tex:416-465]. -/
structure RegisterRoles where
  /-- Unit input register holding the invertible residue. -/
  unitInput : String
  /-- Target accumulator register. -/
  target : String
  /-- Euclidean-state work registers used by the inversion route. -/
  euclideanState : String
  /-- Branch-history registers used for reversible cleanup. -/
  branchHistory : String
  /-- Termination flag register in the fixed-round model. -/
  terminationFlag : String
  /-- Fixed-round counter register. -/
  counter : String
deriving DecidableEq

/-- Register-role certificate for the unit-domain inversion endpoint. -/
def unitDomainRegisterRoles : RegisterRoles where
  unitInput := "unit denominator x"
  target := "target accumulator z"
  euclideanState := "Montgomery-Kaliski u/v/r/s registers"
  branchHistory := "per-round branch-history bits m_i"
  terminationFlag := "termination flag f"
  counter := "fixed-round counter k"

/-- The selected source-backed inversion schedule.  The `rounds = 2 * width`
field records the fixed worst-case loop bound used to make the binary-GCD
route input-independent [RNSL17, ECDLP.tex:406-465]. -/
structure Schedule where
  /-- Operand width used to instantiate the fixed-round schedule. -/
  width : Nat
  /-- Number of fixed Montgomery-Kaliski rounds. -/
  rounds : Nat
  /-- Coarse stages of the selected inversion route. -/
  stages : List ScheduleStage
  /-- Register-role annotation for this schedule. -/
  roles : RegisterRoles
deriving DecidableEq

/-- Coarse stages of the selected modular-inversion schedule. -/
def rnsl17MontgomeryStages : List ScheduleStage :=
  [ScheduleStage.computeInverse, ScheduleStage.addToTarget,
    ScheduleStage.uncomputeInverse]

/-- Selected fixed-round Montgomery-Kaliski schedule for an `n`-bit modulus. -/
def rnsl17MontgomerySchedule (n : Nat) : Schedule where
  width := n
  rounds := 2 * n
  stages := rnsl17MontgomeryStages
  roles := unitDomainRegisterRoles

@[simp] theorem rnsl17MontgomerySchedule_rounds (n : Nat) :
    (rnsl17MontgomerySchedule n).rounds = 2 * n :=
  rfl

@[simp] theorem rnsl17MontgomerySchedule_stages (n : Nat) :
    (rnsl17MontgomerySchedule n).stages = rnsl17MontgomeryStages :=
  rfl

/-! ### Stage transition model -/

/-- Coarse proof phase for the selected inversion schedule. -/
inductive SchedulePhase where
  | initial
  | inverseComputed
  | targetUpdated
  | inverseUncomputed
deriving DecidableEq

/-- Abstract state carried by the inversion schedule proof.  The
`inverseScratch` field stands for the copy-out register used between computing
the inverse and uncomputing the Montgomery-Kaliski work registers. -/
structure StageState (N : Nat) where
  /-- Unit input whose inverse is being computed. -/
  input : (ZMod N)ˣ
  /-- Target accumulator register. -/
  target : ZMod N
  /-- Scratch register holding the computed inverse before cleanup. -/
  inverseScratch : ZMod N
  /-- Temporary cleanup flag for the staged model. -/
  flag : Bool
deriving DecidableEq

instance instFintypeStageState (N : Nat) [NeZero N] :
    Fintype (StageState N) := by
  classical
  let e : StageState N ≃ ((ZMod N)ˣ × ZMod N × ZMod N × Bool) := {
    toFun := fun s => (s.input, s.target, s.inverseScratch, s.flag)
    invFun := fun x =>
      { input := x.1
        target := x.2.1
        inverseScratch := x.2.2.1
        flag := x.2.2.2 }
    left_inv := by
      intro s
      cases s
      rfl
    right_inv := by
      intro x
      rcases x with ⟨input, rest⟩
      rcases rest with ⟨target, rest'⟩
      rcases rest' with ⟨inverseScratch, flag⟩
      rfl
  }
  exact Fintype.ofEquiv ((ZMod N)ˣ × ZMod N × ZMod N × Bool) e.symm

namespace StageState

/-- Initial clean state before computing the inverse. -/
def initial {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) : StageState N where
  input := u
  target := z
  inverseScratch := 0
  flag := false

/-- Compute the inverse into the scratch register. -/
def computeInverse {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := inverseResidue s.input
  flag := s.flag

/-- Add the scratch inverse into the target register. -/
def addScratchToTarget {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target + s.inverseScratch
  inverseScratch := s.inverseScratch
  flag := s.flag

/-- Uncompute the inverse scratch register and restore the clean flag. -/
def uncomputeInverse {N : Nat} (s : StageState N) : StageState N where
  input := s.input
  target := s.target
  inverseScratch := 0
  flag := false

/-- Forget the internal scratch register and return to the endpoint data shape. -/
def toData {N : Nat} (s : StageState N) : Data N where
  input := s.input
  target := s.target
  flag := s.flag

/-- Run the selected coarse inversion schedule on a clean input. -/
def run {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) : StageState N :=
  uncomputeInverse (addScratchToTarget (computeInverse (initial u z)))

@[simp] theorem run_input {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    (run u z).input = u :=
  rfl

@[simp] theorem run_target {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    (run u z).target = z + inverseResidue u :=
  rfl

@[simp] theorem run_inverseScratch {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    (run u z).inverseScratch = 0 :=
  rfl

@[simp] theorem run_flag {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    (run u z).flag = false :=
  rfl

/-- Final-value theorem for the selected coarse inversion schedule. -/
theorem run_final {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    run u z =
      { input := u
        target := z + inverseResidue u
        inverseScratch := 0
        flag := false } :=
  rfl

/-- The selected schedule agrees with the endpoint permutation after forgetting
the internal scratch register. -/
theorem run_toData_eq_addInverseIntoTarget {N : Nat}
    (u : (ZMod N)ˣ) (z : ZMod N) :
    (run u z).toData =
      ({ input := u, target := z, flag := false } : Data N).addInverseIntoTarget :=
  rfl

/-- Coarse invariant for the selected inversion schedule. -/
def Invariant {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    SchedulePhase -> StageState N -> Prop
  | SchedulePhase.initial, s =>
      s.input = u ∧ s.target = z ∧ s.inverseScratch = 0 ∧ s.flag = false
  | SchedulePhase.inverseComputed, s =>
      s.input = u ∧ s.target = z ∧
        s.inverseScratch = inverseResidue u ∧ s.flag = false
  | SchedulePhase.targetUpdated, s =>
      s.input = u ∧ s.target = z + inverseResidue u ∧
        s.inverseScratch = inverseResidue u ∧ s.flag = false
  | SchedulePhase.inverseUncomputed, s =>
      s.input = u ∧ s.target = z + inverseResidue u ∧
        s.inverseScratch = 0 ∧ s.flag = false

@[simp] theorem initial_invariant {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    Invariant u z SchedulePhase.initial (initial u z) := by
  simp [Invariant, initial]

@[simp] theorem computeInverse_invariant {N : Nat}
    (u : (ZMod N)ˣ) (z : ZMod N) :
    Invariant u z SchedulePhase.inverseComputed
      (computeInverse (initial u z)) := by
  simp [Invariant, initial, computeInverse]

@[simp] theorem addScratchToTarget_invariant {N : Nat}
    (u : (ZMod N)ˣ) (z : ZMod N) :
    Invariant u z SchedulePhase.targetUpdated
      (addScratchToTarget (computeInverse (initial u z))) := by
  simp [Invariant, initial, computeInverse, addScratchToTarget]

@[simp] theorem run_invariant {N : Nat} (u : (ZMod N)ˣ) (z : ZMod N) :
    Invariant u z SchedulePhase.inverseUncomputed (run u z) := by
  simp [Invariant, run, initial, computeInverse, addScratchToTarget, uncomputeInverse]

/-- The final invariant implies the unit-domain inverse value and clean scratch. -/
theorem final_value_of_invariant {N : Nat} {u : (ZMod N)ˣ} {z : ZMod N}
    {s : StageState N}
    (h : Invariant u z SchedulePhase.inverseUncomputed s) :
    s.target = z + inverseResidue u ∧ s.inverseScratch = 0 ∧ s.flag = false := by
  exact ⟨h.2.1, h.2.2.1, h.2.2.2⟩

end StageState


end ModularInversion
end QuantumAlg
