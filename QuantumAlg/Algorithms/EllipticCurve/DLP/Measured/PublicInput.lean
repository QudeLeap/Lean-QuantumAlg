/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Measurement
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Points
import all QuantumAlg.Core.Execution.Context.Union.Store.Laws

/-!
# Original public point inputs beside the actual measured exponent program

Both public points remain borrowed classical inputs of their original
`Nat.clog` coordinate shape and original identity-inclusive encoding. Their
storage identities are chosen fresh beyond the complete original quantum
program and terminal cells, because the old base identity conflicts with the
original arithmetic auxiliary identity. No original quantum key or wire moves.

This owner defines the initial input frame and its exact values and space.
It does not emit an allocation or admit inputs midway through execution.
The same two inputs must be present in the enclosing program's initial context.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput

noncomputable section

open Execution FiniteCyclicDLP

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (exponentWidth : Nat)

private def pointShape : CShape := Canonical.Runtime.Context.PointShape E

/-- A public input identity disjoint from every original quantum and measurement cell. -/
def baseKey : StorageKey :=
  (exponentMeasurementContext p exponentWidth).canonicalFreshKey

private theorem baseKey_fresh :
    baseKey (p := p) exponentWidth ∉ (exponentMeasurementContext p exponentWidth).keys :=
  (exponentMeasurementContext p exponentWidth).canonicalFreshKey_fresh

private def reservedBase : RuntimeCtx .quantum :=
  (exponentMeasurementContext p exponentWidth).addBorrowedInput
    (baseKey (p := p) exponentWidth) (pointShape E) (baseKey_fresh (p := p) exponentWidth)

/-- The second public input identity is fresh beyond the first and every original cell. -/
def targetKey : StorageKey := (reservedBase E exponentWidth).canonicalFreshKey

private theorem targetKey_fresh :
    targetKey E exponentWidth ∉ (exponentMeasurementContext p exponentWidth).keys := by
  have fresh := (reservedBase E exponentWidth).canonicalFreshKey_fresh
  change targetKey E exponentWidth ∉
    baseKey (p := p) exponentWidth :: (exponentMeasurementContext p exponentWidth).keys at fresh
  exact fun present => fresh (List.mem_cons_of_mem _ present)

private theorem keys_distinct : targetKey E exponentWidth ≠ baseKey (p := p) exponentWidth := by
  have fresh := (reservedBase E exponentWidth).canonicalFreshKey_fresh
  intro same
  apply fresh
  change targetKey E exponentWidth ∈
    baseKey (p := p) exponentWidth :: (exponentMeasurementContext p exponentWidth).keys
  exact List.mem_cons.mpr (Or.inl same)

private theorem empty_fresh :
    baseKey (p := p) exponentWidth ∉ (RuntimeCtx.empty : RuntimeCtx .quantum).keys := by
  change baseKey (p := p) exponentWidth ∉ []
  simp

private def baseContext : RuntimeCtx .quantum :=
  RuntimeCtx.empty.addBorrowedInput (baseKey (p := p) exponentWidth) (pointShape E)
    (empty_fresh (p := p) exponentWidth)

private theorem baseContext_fresh :
    targetKey E exponentWidth ∉ (baseContext E exponentWidth).keys := by
  change targetKey E exponentWidth ∉ [baseKey (p := p) exponentWidth]
  exact fun present => keys_distinct E exponentWidth (List.mem_singleton.mp present)

/-- The original base-then-target borrowed input order, with nonconflicting storage identities. -/
def frame : RuntimeCtx .quantum :=
  (baseContext E exponentWidth).addBorrowedInput (targetKey E exponentWidth) (pointShape E)
    (baseContext_fresh E exponentWidth)

/-- The borrowed point frame contains exactly its two original public values. -/
theorem frame_keys : (frame E exponentWidth).keys =
    [targetKey E exponentWidth, baseKey (p := p) exponentWidth] := rfl

/-- Both public inputs are classical; the frame introduces no quantum system. -/
theorem frame_quantumWires : (frame E exponentWidth).quantumWires = [] := rfl

/-- The public classical frame adds no physical identity to the quantum program. -/
theorem frame_physicalIdx : (frame E exponentWidth).physicalIdx = [] := rfl

/-- The public point frame has no quantum coordinate in addition to the original register. -/
theorem frame_systemCount : (frame E exponentWidth).systemCount = 0 := rfl

/-- Both actual borrowed point shapes contribute to the resident input space. -/
theorem frame_resident : (frame E exponentWidth).residentSpace =
    2 • SpacePool.ofShape (Canonical.Runtime.Context.PointShape E) := by
  rw [frame, RuntimeCtx.residentSpace_addBorrowedInput, baseContext,
    RuntimeCtx.residentSpace_addBorrowedInput]
  change SpacePool.ofShape (pointShape E) + (SpacePool.ofShape (pointShape E) + 0) = _
  rw [add_zero, two_nsmul]
  rfl

/-- Borrowed public inputs incur resident input space and no owned auxiliary space. -/
theorem frame_auxiliary : (frame E exponentWidth).auxiliarySpace = 0 := rfl

/-- All original quantum identities and finite result cells remain disjoint from both inputs. -/
theorem terminal_disjoint :
    RuntimeCtx.StorageDisjoint (exponentMeasurementContext p exponentWidth)
      (frame E exponentWidth) := by
  constructor
  · apply (RuntimeCtx.keysDisjoint_iff_listDisjoint _ _).mpr
    rw [frame_keys]
    apply List.disjoint_left.mpr
    intro key original framed
    rcases List.mem_cons.mp framed with same | other
    · exact targetKey_fresh E exponentWidth (same ▸ original)
    · exact baseKey_fresh (p := p) exponentWidth ((List.mem_singleton.mp other) ▸ original)
  · apply (RuntimeCtx.physicallyDisjoint_iff_listDisjoint _ _).mpr
    change List.Disjoint (exponentMeasurementContext p exponentWidth).physicalIdx []
    exact List.disjoint_nil_right _

/-- Read the original borrowed base point from the complete public input frame. -/
def baseRef : CInputRef (frame E exponentWidth) (Canonical.Runtime.Context.PointShape E) :=
  .storage ((CStorageRef.borrowedInputHead RuntimeCtx.empty (baseKey (p := p) exponentWidth)
    (pointShape E) (empty_fresh (p := p) exponentWidth)).underBorrowedInput
      (targetKey E exponentWidth) (pointShape E) (baseContext_fresh E exponentWidth))

/-- Read the original borrowed target point from the same complete frame. -/
def targetRef : CInputRef (frame E exponentWidth) (Canonical.Runtime.Context.PointShape E) :=
  .storage (CStorageRef.borrowedInputHead (baseContext E exponentWidth)
    (targetKey E exponentWidth) (pointShape E) (baseContext_fresh E exponentWidth))

/-- The existing public mathematical instance supplies both input values before execution. -/
def store (problem : KnownOrderProblem E.GroupPoint) : Store (frame E exponentWidth) :=
  ⟨(Canonical.Runtime.Context.pointValue E problem.target.toMathlib,
    (Canonical.Runtime.Context.pointValue E problem.generator.toMathlib, ()))⟩

/-- The initial base input has precisely the original public point encoding. -/
theorem store_base (problem : KnownOrderProblem E.GroupPoint) :
    (store E exponentWidth problem).read (baseRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.generator.toMathlib := rfl

/-- The initial target input has precisely the original public point encoding. -/
theorem store_target (problem : KnownOrderProblem E.GroupPoint) :
    (store E exponentWidth problem).read (targetRef E exponentWidth) =
      Canonical.Runtime.Context.pointValue E problem.target.toMathlib := rfl

/-- The actual initial base value represents the original public group point. -/
theorem store_base_represents (problem : KnownOrderProblem E.GroupPoint) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      ((store E exponentWidth problem).read (baseRef E exponentWidth))
      problem.generator.toMathlib := by
  rw [store_base]
  exact publicPoint_represents E problem.generator

/-- The actual initial target value represents the original public group point. -/
theorem store_target_represents (problem : KnownOrderProblem E.GroupPoint) :
    ClassicalRoutines.EllipticCurve.PointRepresents (Canonical.Layout.curveSpec E)
      ((store E exponentWidth problem).read (targetRef E exponentWidth))
      problem.target.toMathlib := by
  rw [store_target]
  exact publicPoint_represents E problem.target

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.PublicInput
