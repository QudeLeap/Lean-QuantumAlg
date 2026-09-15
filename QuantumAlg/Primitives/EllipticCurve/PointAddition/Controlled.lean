/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/


module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.PointAddition.Generic

/-!
# Controlled affine point-addition endpoint

This module packages the controlled generic affine ECADD endpoint, including
its branch-selection support model, clean external-work interface, resource
profile, and public-bounds witness.  The controlled point-addition resource
interface matches the RNSL17 short-Weierstrass implementation boundary
[RNSL17, ECDLP.tex:650-696].
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass

variable {p : ℕ}

namespace ControlledPointAddition

/-- Controlled ECADD reuses the same generic-addition input subtype; the
control bit does not change the affine genericity obligation. -/
abbrev Input (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) :=
  GenericPointAddition.Input E Q

/-- Controlled ECADD inputs expose the same generic predicate as ECADD. -/
theorem input_controlledDomain {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (P : Input E Q) :
    ControlledAddDomain P.1 Q :=
  P.2

/-- Data registers for controlled generic affine point addition. -/
structure Data (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) where
  /-- Generic-domain input point for the controlled addition. -/
  input : Input E Q
  /-- Control bit selecting whether the addition branch is applied. -/
  control : Bool
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Temporary cleanup flag carried by the controlled endpoint. -/
  flag : Bool
deriving DecidableEq

noncomputable instance instFintypeData (E : PrimeFieldShortWeierstrass p) [NeZero p]
    (Q : AffinePoint E) : Fintype (Data E Q) := by
  classical
  let e :
      Data E Q ≃ (Input E Q × Bool × ZMod p × ZMod p × Bool) := {
    toFun := fun x => (x.input, (x.control, (x.targetX, (x.targetY, x.flag))))
    invFun := fun x =>
      { input := x.1, control := x.2.1, targetX := x.2.2.1,
        targetY := x.2.2.2.1, flag := x.2.2.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨input, rest⟩
      rcases rest with ⟨control, rest'⟩
      rcases rest' with ⟨targetX, rest''⟩
      rcases rest'' with ⟨targetY, flag⟩
      rfl
  }
  exact Fintype.ofEquiv
    (Input E Q × Bool × ZMod p × ZMod p × Bool) e.symm

namespace Data

/-- Encode the finite affine input carried by a controlled point-addition
register label. -/
def encodedInput {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (x : Data E Q) :
    Fin (2 ^ n) × Fin (2 ^ n) :=
  GenericPointAddition.encodeInput encoding x.input

/-- Controlled-register inputs decode to valid finite affine encodings. -/
theorem encodedInput_isValid {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) (x : Data E Q) :
    encoding.IsValidFiniteEncoding (x.encodedInput encoding) :=
  GenericPointAddition.encodeInput_isValid encoding x.input

/-- Equality of encoded controlled-register inputs gives equality of the
underlying affine coordinates at the circuit boundary. -/
theorem encodedInput_ext {E : PrimeFieldShortWeierstrass p}
    {Q : AffinePoint E} {n : ℕ}
    (encoding : PointEncoding E n) {x y : Data E Q}
    (h : x.encodedInput encoding = y.encodedInput encoding) :
    x.input.1.x = y.input.1.x ∧ x.input.1.y = y.input.1.y :=
  GenericPointAddition.encodeInput_ext encoding h

/-! #### Controlled ECADD stage support -/

/-- Coarse stages of the controlled ECADD support pipeline.  RNSL17's
controlled-addition schedule separates the control branch, the generic affine
addition, and clean uncomputation [RNSL17, ECDLP.tex:650-696]. -/
inductive Stage where
  | inspectControl
  | runGenericOrSkip
  | cleanup
deriving DecidableEq

/-- Intermediate state for the controlled ECADD stage proof. -/
structure StageState (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E) where
  /-- Generic-domain input point for the controlled staged addition. -/
  input : Input E Q
  /-- Control bit supplied to the staged controlled addition. -/
  control : Bool
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Branch flag recording whether the controlled addition is active. -/
  branchActive : Bool
  /-- Temporary cleanup flag for the staged controlled endpoint. -/
  flag : Bool
deriving DecidableEq

namespace StageState

/-- Initial clean controlled ECADD state. -/
def initial {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    StageState E Q where
  input := P
  control := control
  targetX := targetX
  targetY := targetY
  branchActive := false
  flag := false

/-- Copy the control value into the branch selector. -/
def inspectControl {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (s : StageState E Q) : StageState E Q where
  input := s.input
  control := s.control
  targetX := s.targetX
  targetY := s.targetY
  branchActive := s.control
  flag := s.flag

/-- Run the generic ECADD update on the active branch and skip it otherwise. -/
def runGenericOrSkip {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (s : StageState E Q) : StageState E Q where
  input := s.input
  control := s.control
  targetX :=
    if s.branchActive then
      (GenericPointAddition.Data.StageState.run s.input s.targetX s.targetY).targetX
    else s.targetX
  targetY :=
    if s.branchActive then
      (GenericPointAddition.Data.StageState.run s.input s.targetX s.targetY).targetY
    else s.targetY
  branchActive := s.branchActive
  flag := s.flag

/-- Uncompute the branch selector and restore the clean flag. -/
def cleanup {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (s : StageState E Q) : StageState E Q where
  input := s.input
  control := s.control
  targetX := s.targetX
  targetY := s.targetY
  branchActive := false
  flag := false

/-- Execute one named controlled ECADD support stage. -/
def step {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (stage : Stage) (s : StageState E Q) :
    StageState E Q :=
  match stage with
  | .inspectControl => inspectControl s
  | .runGenericOrSkip => runGenericOrSkip s
  | .cleanup => cleanup s

/-- Run the controlled ECADD support pipeline. -/
def run {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    StageState E Q :=
  step .cleanup
    (step .runGenericOrSkip
      (step .inspectControl (initial P control targetX targetY)))

/-- Forget the internal branch selector and recover the endpoint data shape. -/
def toData {E : PrimeFieldShortWeierstrass p} {Q : AffinePoint E}
    (s : StageState E Q) : Data E Q where
  input := s.input
  control := s.control
  targetX := s.targetX
  targetY := s.targetY
  flag := s.flag

/-- The inactive controlled stage pipeline is the identity on target data and
preserves the control bit. -/
theorem run_false {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (P : Input E Q) (targetX targetY : ZMod p) :
    run P false targetX targetY =
      { input := P
        control := false
        targetX := targetX
        targetY := targetY
        branchActive := false
        flag := false } :=
  rfl

/-- The active controlled stage pipeline performs the generic affine update and
preserves the control bit. -/
theorem run_true {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {Q : AffinePoint E} (P : Input E Q) (targetX targetY : ZMod p) :
    run P true targetX targetY =
      { input := P
        control := true
        targetX := targetX + genericAddX E P.1 Q
        targetY := targetY + genericAddY E P.1 Q
        branchActive := false
        flag := false } :=
  by
    simp [run, step, initial, inspectControl, runGenericOrSkip, cleanup]

/-- The active controlled stage reuses the generic ECADD stage endpoint. -/
theorem run_true_toData_eq_genericStage {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} (P : Input E Q)
    (targetX targetY : ZMod p) :
    (run P true targetX targetY).toData =
      ({ input := P
         control := true
         targetX := (GenericPointAddition.Data.StageState.run P targetX targetY).toData.targetX
         targetY := (GenericPointAddition.Data.StageState.run P targetX targetY).toData.targetY
         flag := (GenericPointAddition.Data.StageState.run P targetX targetY).toData.flag } :
        Data E Q) :=
  by
    simp [run, step, initial, inspectControl, runGenericOrSkip, cleanup, toData,
      GenericPointAddition.Data.StageState.toData]

/-- The controlled stage pipeline reaches the public endpoint data shape. -/
theorem run_toData_eq_endpoint {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    (run P control targetX targetY).toData =
      ({ input := P
         control := control
         targetX := if control then targetX + genericAddX E P.1 Q else targetX
         targetY := if control then targetY + genericAddY E P.1 Q else targetY
         flag := false } : Data E Q) := by
  cases control <;>
    simp [run, step, initial, inspectControl, runGenericOrSkip, cleanup, toData]

end StageState

/-- Apply the controlled generic addition to target coordinate registers. -/
def addIntoTarget {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (x : Data E Q) : Data E Q where
  input := x.input
  control := x.control
  targetX :=
    if x.control then x.targetX + genericAddX E x.input.1 Q else x.targetX
  targetY :=
    if x.control then x.targetY + genericAddY E x.input.1 Q else x.targetY
  flag := x.flag

/-- The controlled ECADD stage pipeline agrees with the endpoint data update. -/
theorem StageState.run_toData_eq_addIntoTarget {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E}
    (P : Input E Q) (control : Bool) (targetX targetY : ZMod p) :
    (StageState.run P control targetX targetY).toData =
      ({ input := P
         control := control
         targetX := targetX
         targetY := targetY
         flag := false } : Data E Q).addIntoTarget := by
  cases control <;>
    simp [StageState.run, StageState.step, StageState.initial, StageState.inspectControl,
      StageState.runGenericOrSkip, StageState.cleanup, StageState.toData, addIntoTarget]

/-- Inverse controlled update on target coordinate registers. -/
def subFromTarget {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] {Q : AffinePoint E}
    (x : Data E Q) : Data E Q where
  input := x.input
  control := x.control
  targetX :=
    if x.control then x.targetX - genericAddX E x.input.1 Q else x.targetX
  targetY :=
    if x.control then x.targetY - genericAddY E x.input.1 Q else x.targetY
  flag := x.flag

/-- Controlled generic point addition as a reversible coordinate-target map. -/
def controlledEquiv (E : PrimeFieldShortWeierstrass p) [Fact p.Prime] (Q : AffinePoint E) :
    Equiv.Perm (Data E Q) where
  toFun := addIntoTarget
  invFun := subFromTarget
  left_inv := by
    intro x
    cases x with
    | mk input control targetX targetY flag =>
        cases control <;> simp [addIntoTarget, subFromTarget]
  right_inv := by
    intro x
    cases x with
    | mk input control targetX targetY flag =>
        cases control <;> simp [addIntoTarget, subFromTarget]

@[simp] theorem controlledEquiv_apply {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} (x : Data E Q) :
    controlledEquiv E Q x = x.addIntoTarget :=
  rfl

/-- Controlled point addition with an external work register. -/
def withWorkEquiv (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    [Fact p.Prime] (Work : Type) : Equiv.Perm (Data E Q × Work) :=
  Equiv.prodCongr (controlledEquiv E Q) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} {Work : Type} (x : Data E Q) (w : Work) :
    withWorkEquiv E Q Work (x, w) = (x.addIntoTarget, w) :=
  rfl

/-- The controlled map leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] {Q : AffinePoint E} {Work : Type} :
    WorkRegister.Preserves (Data := Data E Q) (Work := Work)
      (withWorkEquiv E Q Work) := by
  intro x
  cases x
  rfl

/-- Certified clean reversible map for controlled generic point addition. -/
def withWorkCleanMap (E : PrimeFieldShortWeierstrass p) (Q : AffinePoint E)
    [Fact p.Prime] (Work : Type) :
    WorkRegister.CleanReversibleMap (Data E Q) Work where
  perm := withWorkEquiv E Q Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-- Register whose labels are controlled point-addition data states. -/
@[implicit_reducible]
noncomputable def register (E : PrimeFieldShortWeierstrass p) [NeZero p] (Q : AffinePoint E) :
    Register where
  Index := Data E Q
  fintype := inferInstance
  decEq := inferInstance

/-- Metadata-free controlled generic point-addition operator for a fixed addend `Q`. -/
noncomputable def controlledOp (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) : UnitaryOperator (register E Q) :=
  UnitaryOperator.ofPerm (Data.controlledEquiv E Q).symm

/-- Basis action of the controlled generic point-addition operator. -/
theorem controlledOp_apply_ket (E : PrimeFieldShortWeierstrass p) [NeZero p]
    [Fact p.Prime] (Q : AffinePoint E) (x : Data E Q) :
    (controlledOp E Q).apply (NormalizedVector.ket (R := register E Q) x) =
      NormalizedVector.ket (R := register E Q) x.addIntoTarget := by
  rw [controlledOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

end ControlledPointAddition

end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
