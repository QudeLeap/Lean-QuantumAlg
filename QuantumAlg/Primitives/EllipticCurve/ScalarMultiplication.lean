/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.EllipticCurve.CleanComposition
public import QuantumAlg.Primitives.EllipticCurve.PointAddition

/-!
# Scalar-multiplication schedule certificates

This module records the support layer needed before an elliptic-curve
scalar-multiplication circuit endpoint can be stated. It tracks the fixed-base
controlled-addition schedule, the accumulator recurrence, and the generic-domain
side condition required by every lower-level controlled point-addition step.
The schedule shape follows the fixed-base controlled-addition stack used in
elliptic-curve discrete-logarithm resource estimates
[RNSL17, ECDLP.tex:589-597,650-699].
The generic-domain condition is the affine distinct-`x` branch used by the
underlying elliptic-curve addition formulas [PZ03, ecc.tex:525-551;
HJN+20, elliptic-curves.tex:8-9].

The declarations here do not define a full scalar-multiplication circuit.
-/

@[expose] public section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication

variable {p : Nat}

/-- Current accumulator slot for a controlled-addition schedule step. -/
def currentIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val, Nat.lt_trans i.isLt (Nat.lt_succ_self n)⟩

/-- Next accumulator slot for a controlled-addition schedule step. -/
def nextIndex {n : Nat} (i : Fin n) : Fin (n + 1) :=
  ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

/-- Fixed-base controlled-addition schedule. The addends are usually the
precomputed multiples selected by the scalar bits. -/
structure Schedule (E : PrimeFieldShortWeierstrass p) where
  /-- Number of controlled-addition steps in the schedule. -/
  length : Nat
  /-- Fixed affine addend selected at each schedule step. -/
  addend : Fin length -> AffinePoint E

namespace Schedule

/-- Scalar weight attached to a schedule index in the binary fixed-base route.
The endpoint control convention uses the same `i.val` bit index [PZ03,
ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
def addendWeight {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (i : Fin schedule.length) : Nat :=
  2 ^ i.val

/-- Fixed-base addend-generation contract for the generic-affine scalar
multiplication schedule.  It states that every finite addend in the schedule
represents the Mathlib group-law multiple `2^i` of one base point, leaving the
generic-domain side conditions and the final selected-bit fold to separate
certificates [PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
structure FixedBaseAddends {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    (schedule : Schedule E) where
  /-- Base point whose powers populate the fixed-addend schedule. -/
  base : AffinePoint E
  /-- Proof that each addend is the expected group multiple of the base. -/
  addend_eq_groupMultiple :
    forall i : Fin schedule.length,
      (schedule.addend i).toMathlib =
        (schedule.addendWeight i) • base.toMathlib

namespace FixedBaseAddends

variable {E : PrimeFieldShortWeierstrass p}
variable [Fact p.Prime]
variable {schedule : Schedule E}

/-- The fixed-base contract exposes the group-law multiple represented by the
selected schedule addend [RNSL17, ECDLP.tex:589-593]. -/
theorem addend_toMathlib (fixed : FixedBaseAddends schedule)
    (i : Fin schedule.length) :
    (schedule.addend i).toMathlib =
      (schedule.addendWeight i) • fixed.base.toMathlib :=
  fixed.addend_eq_groupMultiple i

end FixedBaseAddends

/-- Controls for one run of a fixed-base schedule. -/
abbrev Controls {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E) :=
  (i : Fin schedule.length) -> Bool

/-- Accumulator labels before the first step and after every step. -/
abbrev Accumulators {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E) :=
  Fin (schedule.length + 1) -> AffinePoint E

/-- Generic-domain side condition needed by every controlled-addition step. -/
def GenericDomain {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (accumulators : Accumulators schedule) : Prop :=
  forall i : Fin schedule.length,
    (accumulators (currentIndex i)).x ≠ (schedule.addend i).x

end Schedule

/-- Homogeneous data shape for one controlled-addition step of a fixed
scalar-multiplication schedule.  The `step` index selects the addend, so all
steps share one wrapper type even though each lower-level controlled ECADD
endpoint is indexed by its own fixed addend [RNSL17,
ECDLP.tex:589-597,650-699]. -/
structure StepData (E : PrimeFieldShortWeierstrass p) (schedule : Schedule E) where
  /-- Schedule step selecting the lower-level controlled-addition endpoint. -/
  step : Fin schedule.length
  /-- Lower-level controlled-addition input for this step. -/
  input : ControlledPointAddition.Input E (schedule.addend step)
  /-- Control bit applied at this step. -/
  control : Bool
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Temporary cleanup flag carried by the endpoint. -/
  flag : Bool
deriving DecidableEq

namespace StepData

variable {E : PrimeFieldShortWeierstrass p} {schedule : Schedule E}

/-- Forget the homogeneous wrapper and recover the per-addend controlled ECADD
data at the selected schedule step. -/
def toControlled (x : StepData E schedule) :
    ControlledPointAddition.Data E (schedule.addend x.step) where
  input := x.input
  control := x.control
  targetX := x.targetX
  targetY := x.targetY
  flag := x.flag

/-- Embed a per-addend controlled ECADD data value into the homogeneous
schedule-step wrapper. -/
def ofControlled (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    StepData E schedule where
  step := i
  input := x.input
  control := x.control
  targetX := x.targetX
  targetY := x.targetY
  flag := x.flag

@[simp] theorem toControlled_ofControlled (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    (ofControlled (schedule := schedule) i x).toControlled = x := by
  cases x
  rfl

@[simp] theorem ofControlled_toControlled (x : StepData E schedule) :
    ofControlled x.step x.toControlled = x := by
  cases x
  rfl

@[simp] theorem ofControlled_step (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    (ofControlled (schedule := schedule) i x).step = i :=
  rfl

@[simp] theorem ofControlled_control (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    (ofControlled (schedule := schedule) i x).control = x.control :=
  rfl

@[simp] theorem ofControlled_flag (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    (ofControlled (schedule := schedule) i x).flag = x.flag :=
  rfl

/-- Equivalence between the homogeneous wrapper and the sigma family of
per-addend controlled ECADD data values. -/
def sigmaEquiv (E : PrimeFieldShortWeierstrass p) (schedule : Schedule E) :
    StepData E schedule ≃
      (Σ i : Fin schedule.length,
        ControlledPointAddition.Data E (schedule.addend i)) where
  toFun := fun x => ⟨x.step, x.toControlled⟩
  invFun := fun x => ofControlled x.1 x.2
  left_inv := by
    intro x
    exact ofControlled_toControlled x
  right_inv := by
    intro x
    cases x with
    | mk i data =>
        simp [toControlled_ofControlled]

noncomputable instance instFintypeStepData (E : PrimeFieldShortWeierstrass p)
    [NeZero p] (schedule : Schedule E) :
    Fintype (StepData E schedule) := by
  classical
  exact Fintype.ofEquiv
    (Σ i : Fin schedule.length,
      ControlledPointAddition.Data E (schedule.addend i))
    (sigmaEquiv E schedule).symm

/-- The lifted per-step controlled ECADD permutation on the sigma family of
per-addend data values.  It acts only on the selected schedule index and leaves
other indices unchanged. -/
def controlledSigmaEquivAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) :
    Equiv.Perm
      (Σ j : Fin schedule.length,
        ControlledPointAddition.Data E (schedule.addend j)) :=
  Equiv.sigmaCongrRight fun j =>
    if j = i then
      ControlledPointAddition.Data.controlledEquiv E (schedule.addend j)
    else
      Equiv.refl _

/-- The fixed-step controlled ECADD permutation lifted to the homogeneous
schedule-step data type. -/
def controlledEquivAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) :
    Equiv.Perm (StepData E schedule) :=
  (sigmaEquiv E schedule).trans
    ((controlledSigmaEquivAt E schedule i).trans (sigmaEquiv E schedule).symm)

/-- The lifted step map agrees with the original per-addend endpoint at the
selected schedule index. -/
@[simp] theorem controlledEquivAt_ofControlled
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length)
    (x : ControlledPointAddition.Data E (schedule.addend i)) :
    controlledEquivAt E schedule i (ofControlled i x) =
      ofControlled i x.addIntoTarget := by
  cases x with
  | mk input control targetX targetY flag =>
      cases control <;>
        simp [controlledEquivAt, controlledSigmaEquivAt, sigmaEquiv,
          toControlled, ofControlled, ControlledPointAddition.Data.addIntoTarget]

/-- Lifted step map with an external work register. -/
def withWorkEquivAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) (Work : Type) :
    Equiv.Perm (StepData E schedule × Work) :=
  Equiv.prodCongr (controlledEquivAt E schedule i) (Equiv.refl Work)

@[simp] theorem withWorkEquivAt_apply_ofControlled
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) (Work : Type)
    (x : ControlledPointAddition.Data E (schedule.addend i)) (w : Work) :
    withWorkEquivAt E schedule i Work (ofControlled i x, w) =
      (ofControlled i x.addIntoTarget, w) := by
  simp [withWorkEquivAt]

/-- Lifted clean reversible map for the selected schedule step. -/
def withWorkCleanMapAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) (Work : Type) :
    WorkRegister.CleanReversibleMap (StepData E schedule) Work where
  perm := withWorkEquivAt E schedule i Work
  preservesWork := by
    intro x
    cases x
    rfl

end StepData

/-- Schedule-wide controlled ECADD endpoint data, with one component for each
fixed-base addend in the scalar-multiplication trace [RNSL17,
ECDLP.tex:589-597,650-699]. -/
abbrev TraceData (E : PrimeFieldShortWeierstrass p)
    (schedule : Schedule E) :=
  (i : Fin schedule.length) ->
    ControlledPointAddition.Data E (schedule.addend i)

namespace TraceData

/-- Per-step controlled ECADD map over a complete schedule trace.  Only the
selected component is updated; every other scheduled step is left untouched. -/
def controlledEquivAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) :
    Equiv.Perm (TraceData E schedule) :=
  Equiv.piCongrRight fun j =>
    if j = i then
      ControlledPointAddition.Data.controlledEquiv E (schedule.addend j)
    else
      Equiv.refl _

@[simp] theorem controlledEquivAt_apply_self
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length)
    (x : TraceData E schedule) :
    controlledEquivAt E schedule i x i = (x i).addIntoTarget := by
  simp [controlledEquivAt]

theorem controlledEquivAt_apply_ne
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) {i j : Fin schedule.length}
    (hji : j ≠ i) (x : TraceData E schedule) :
    controlledEquivAt E schedule i x j = x j := by
  simp [controlledEquivAt, hji]

/-- Schedule-wide normal form that applies every controlled ECADD endpoint in
the trace once. -/
def controlledEquiv (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) :
    Equiv.Perm (TraceData E schedule) :=
  Equiv.piCongrRight fun i =>
    ControlledPointAddition.Data.controlledEquiv E (schedule.addend i)

@[simp] theorem controlledEquiv_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (x : TraceData E schedule)
    (i : Fin schedule.length) :
    controlledEquiv E schedule x i = (x i).addIntoTarget := by
  rfl

/-- Per-step clean map over a complete schedule trace and an external work
register. -/
def withWorkCleanMapAt (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (i : Fin schedule.length) (Work : Type) :
    WorkRegister.CleanReversibleMap (TraceData E schedule) Work where
  perm := Equiv.prodCongr (controlledEquivAt E schedule i) (Equiv.refl Work)
  preservesWork := by
    intro x
    rfl

/-- Schedule-wide clean map that applies every controlled ECADD endpoint in the
trace and preserves the external work register. -/
def withWorkCleanMap (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type) :
    WorkRegister.CleanReversibleMap (TraceData E schedule) Work where
  perm := Equiv.prodCongr (controlledEquiv E schedule) (Equiv.refl Work)
  preservesWork := by
    intro x
    rfl

@[simp] theorem withWorkCleanMap_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type)
    (x : TraceData E schedule) (w : Work) :
    (withWorkCleanMap E schedule Work).perm (x, w) =
      (fun i => (x i).addIntoTarget, w) := by
  rfl

end TraceData

/-- Schedule-ordered controlled-addition clean maps over the complete trace
register. -/
def controlledTraceStepCleanMaps (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (schedule : Schedule E) (Work : Type) :
    List (WorkRegister.CleanReversibleMap (TraceData E schedule) Work) :=
  (List.ofFn fun i : Fin schedule.length => i).map fun i =>
    TraceData.withWorkCleanMapAt E schedule i Work

/-- Sequential clean-composition witness for the schedule trace maps. -/
def controlledTraceSequentialCleanComposition
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type) :
    WorkRegister.CleanReversibleMap (TraceData E schedule) Work :=
  CleanComposition.composeList (TraceData E schedule) Work
    (controlledTraceStepCleanMaps E schedule Work)

/-- The sequential trace-map composition preserves the external work register. -/
theorem controlledTraceSequentialCleanComposition_preserves_work
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type) (x : TraceData E schedule × Work) :
    ((controlledTraceSequentialCleanComposition E schedule Work).perm x).2 = x.2 :=
  CleanComposition.composeList_preserves_work
    (controlledTraceStepCleanMaps E schedule Work) x

private theorem controlledTraceCleanMapList_fold_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type)
    (l : List (Fin schedule.length))
    (start : WorkRegister.CleanReversibleMap (TraceData E schedule) Work)
    (x : TraceData E schedule × Work) :
    ((l.map fun i => TraceData.withWorkCleanMapAt E schedule i Work).foldl
        WorkRegister.CleanReversibleMap.sequential start).perm x =
      l.foldl
        (fun y i => (TraceData.withWorkCleanMapAt E schedule i Work).perm y)
        (start.perm x) := by
  induction l generalizing start x with
  | nil =>
      rfl
  | cons i l ih =>
      simpa [List.foldl_cons] using
        ih (WorkRegister.CleanReversibleMap.sequential start
          (TraceData.withWorkCleanMapAt E schedule i Work)) x

private theorem controlledTracePairFold_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type)
    (l : List (Fin schedule.length)) (x : TraceData E schedule) (w : Work) :
    l.foldl
        (fun y i => (TraceData.withWorkCleanMapAt E schedule i Work).perm y)
        (x, w) =
      (l.foldl (fun y i => TraceData.controlledEquivAt E schedule i y) x, w) := by
  induction l generalizing x w with
  | nil =>
      rfl
  | cons i l ih =>
      simpa [List.foldl_cons, TraceData.withWorkCleanMapAt] using
        ih (TraceData.controlledEquivAt E schedule i x) w

private theorem controlledTraceDataFold_apply_of_nodup
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (l : List (Fin schedule.length)) (hnodup : l.Nodup)
    (x : TraceData E schedule) (j : Fin schedule.length) :
    (l.foldl (fun y i => TraceData.controlledEquivAt E schedule i y) x) j =
      if j ∈ l then (x j).addIntoTarget else x j := by
  induction l generalizing x j with
  | nil =>
      simp
  | cons i l ih =>
      have hnot : i ∉ l := by
        exact (List.nodup_cons.mp hnodup).1
      have hnodup_tail : l.Nodup := by
        exact (List.nodup_cons.mp hnodup).2
      by_cases hji : j = i
      · subst j
        have h :=
          ih hnodup_tail (TraceData.controlledEquivAt E schedule i x) i
        simp [hnot] at h
        simpa [hnot] using h
      · have h :=
          ih hnodup_tail (TraceData.controlledEquivAt E schedule i x) j
        by_cases hjmem : j ∈ l
        · simp [hji, hjmem] at h ⊢
          simpa [TraceData.controlledEquivAt_apply_ne E schedule hji x] using h
        · simp [hji, hjmem] at h ⊢
          simpa [TraceData.controlledEquivAt_apply_ne E schedule hji x] using h

/-- The schedule-ordered `composeList` of controlled ECADD trace maps applies
each per-addend endpoint exactly once. -/
theorem controlledTraceSequentialCleanComposition_apply
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type)
    (x : TraceData E schedule) (w : Work) :
    (controlledTraceSequentialCleanComposition E schedule Work).perm (x, w) =
      (fun i => (x i).addIntoTarget, w) := by
  apply Prod.ext
  · funext i
    let indices : List (Fin schedule.length) :=
      List.ofFn fun i : Fin schedule.length => i
    have hclean :=
      controlledTraceCleanMapList_fold_apply E schedule Work indices
        (WorkRegister.CleanReversibleMap.identity (TraceData E schedule) Work) (x, w)
    have hpair :=
      controlledTracePairFold_apply E schedule Work indices x w
    have hnodup : indices.Nodup := by
      dsimp [indices]
      exact List.nodup_ofFn_ofInjective (fun _ _ h => h)
    have hcomponent :=
      controlledTraceDataFold_apply_of_nodup E schedule indices hnodup x i
    have hmem : i ∈ indices := by
      dsimp [indices]
      simp
    have hseq :
        (controlledTraceSequentialCleanComposition E schedule Work).perm (x, w) =
          (indices.foldl
            (fun y i => TraceData.controlledEquivAt E schedule i y) x, w) := by
      change
        (List.foldl WorkRegister.CleanReversibleMap.sequential
            (WorkRegister.CleanReversibleMap.identity (TraceData E schedule) Work)
            (indices.map fun i => TraceData.withWorkCleanMapAt E schedule i Work)).perm
          (x, w) =
            (indices.foldl
              (fun y i => TraceData.controlledEquivAt E schedule i y) x, w)
      simpa [WorkRegister.CleanReversibleMap.identity] using hclean.trans hpair
    rw [congrArg (fun y => y.1 i) hseq]
    simpa [hmem] using hcomponent
  · exact controlledTraceSequentialCleanComposition_preserves_work
      E schedule Work (x, w)

/-- Schedule-wide clean composition of the schedule-ordered controlled ECADD
trace-step maps. -/
def controlledTraceCleanComposition
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type) :
    WorkRegister.CleanReversibleMap (TraceData E schedule) Work :=
  controlledTraceSequentialCleanComposition E schedule Work

/-- The schedule-wide trace composition preserves the external work register. -/
theorem controlledTraceCleanComposition_preserves_work
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (Work : Type) (x : TraceData E schedule × Work) :
    ((controlledTraceCleanComposition E schedule Work).perm x).2 = x.2 :=
  (controlledTraceCleanComposition E schedule Work).preservesWork x

/-- Generic affine sum as a finite nonsingular point. -/
noncomputable def genericStepPoint (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hgeneric : P.x ≠ Q.x) :
    AffinePoint E where
  x := genericAddX E P Q
  y := genericAddY E P Q
  nonsingular := genericAdd_nonsingular E P Q hgeneric

@[simp] theorem genericStepPoint_x (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hgeneric : P.x ≠ Q.x) :
    (genericStepPoint E P Q hgeneric).x = genericAddX E P Q :=
  rfl

@[simp] theorem genericStepPoint_y (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hgeneric : P.x ≠ Q.x) :
    (genericStepPoint E P Q hgeneric).y = genericAddY E P Q :=
  rfl

/-- The generic scalar-multiplication step is the finite affine group-law sum
in Mathlib's elliptic-curve point type, under the same nonexceptional branch
used by the fixed-addend ECADD endpoint [PZ03, ecc.tex:525-551; RNSL17,
ECDLP.tex:589-593]. -/
theorem genericStepPoint_group_law_mathlib (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] (P Q : AffinePoint E) (hgeneric : P.x ≠ Q.x) :
    P.toMathlib + Q.toMathlib =
      (genericStepPoint E P Q hgeneric).toMathlib := by
  simpa [genericStepPoint, AffinePoint.toMathlib] using
    genericAdd_group_law_mathlib E P Q hgeneric

/-- A certified run of a fixed-base scalar-multiplication schedule. The
recurrence records only the generic controlled-addition path, not a complete
exceptional-case group law. -/
structure Run (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) where
  /-- Control-bit assignment used by the run. -/
  controls : Schedule.Controls schedule
  /-- Accumulator values before the first step and after each step. -/
  accumulators : Schedule.Accumulators schedule
  /-- Initial accumulator point. -/
  startsAt : AffinePoint E
  /-- Proof that the first accumulator slot is the initial point. -/
  startsAt_eq : accumulators ⟨0, Nat.succ_pos schedule.length⟩ = startsAt
  /-- Nonexceptional-domain proof for every controlled-addition step. -/
  genericDomain : schedule.GenericDomain accumulators
  /-- Inactive controls leave the accumulator unchanged. -/
  inactive_step :
    forall i : Fin schedule.length,
      controls i = false ->
        accumulators (nextIndex i) = accumulators (currentIndex i)
  /-- Active controls apply the generic fixed-addend group step. -/
  active_step :
    forall i : Fin schedule.length,
      controls i = true ->
        accumulators (nextIndex i) =
          genericStepPoint E
            (accumulators (currentIndex i)) (schedule.addend i)
            (genericDomain i)

namespace Run

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}

/-- The run-level certificate supplies the nonexceptional input required by
the controlled point-addition endpoint at this schedule step. -/
def stepInput (run : Run E schedule) (i : Fin schedule.length) :
    {P : AffinePoint E // P.x ≠ (schedule.addend i).x} :=
  ⟨run.accumulators (currentIndex i), run.genericDomain i⟩

@[simp] theorem stepInput_val (run : Run E schedule) (i : Fin schedule.length) :
    (run.stepInput i).1 = run.accumulators (currentIndex i) :=
  rfl

@[simp] theorem stepInput_property (run : Run E schedule) (i : Fin schedule.length) :
    (run.accumulators (currentIndex i)).x ≠ (schedule.addend i).x :=
  run.genericDomain i

/-- Lower-level controlled point-addition data for one schedule step. This is
the bridge from the schedule certificate to the existing point-addition API. -/
def controlledStepData (run : Run E schedule) (i : Fin schedule.length) :
    ControlledPointAddition.Data E (schedule.addend i) where
  input := run.stepInput i
  control := run.controls i
  targetX := 0
  targetY := 0
  flag := false

@[simp] theorem controlledStepData_input
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.controlledStepData i).input = run.stepInput i :=
  rfl

@[simp] theorem controlledStepData_control
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.controlledStepData i).control = run.controls i :=
  rfl

/-- The generic-domain certificate is exactly the side condition carried by the
lower-level controlled point-addition input. -/
theorem genericDomain_supplies_step
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.controlledStepData i).input.1.x ≠ (schedule.addend i).x :=
  run.genericDomain i

/-- Complete controlled-ECADD endpoint trace induced by a certified schedule
run. -/
def controlledTraceData (run : Run E schedule) : TraceData E schedule :=
  fun i => run.controlledStepData i

/-- Endpoint trace after every controlled ECADD component has been applied
once. -/
def updatedTraceData (run : Run E schedule) : TraceData E schedule :=
  fun i => (run.controlledStepData i).addIntoTarget

/-- Homogeneous schedule-step data for one certified controlled ECADD step. -/
def homogeneousStepData (run : Run E schedule) (i : Fin schedule.length) :
    StepData E schedule :=
  StepData.ofControlled i (run.controlledStepData i)

@[simp] theorem homogeneousStepData_step
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.homogeneousStepData i).step = i :=
  rfl

@[simp] theorem homogeneousStepData_toControlled
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.homogeneousStepData i).toControlled = run.controlledStepData i :=
  rfl

@[simp] theorem homogeneousStepData_control
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.homogeneousStepData i).control = run.controls i :=
  rfl

/-- Inactive schedule steps preserve the accumulator. -/
theorem inactive_accumulator
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = false) :
    run.accumulators (nextIndex i) =
      run.accumulators (currentIndex i) :=
  run.inactive_step i hcontrol

/-- Active schedule steps advance by the generic affine-addition formula. -/
theorem active_accumulator
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = true) :
    run.accumulators (nextIndex i) =
      genericStepPoint E
        (run.accumulators (currentIndex i)) (schedule.addend i)
        (run.genericDomain i) :=
  run.active_step i hcontrol

/-- Inactive schedule steps are identity steps in the Mathlib group-law view. -/
theorem inactive_accumulator_group_law_mathlib
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = false) :
    (run.accumulators (nextIndex i)).toMathlib =
      (run.accumulators (currentIndex i)).toMathlib := by
  rw [inactive_accumulator run i hcontrol]

/-- Active schedule steps add the selected fixed addend in the Mathlib
elliptic-curve group-law view, matching the binary controlled-addition route
[PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem active_accumulator_group_law_mathlib
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = true) :
    (run.accumulators (nextIndex i)).toMathlib =
      (run.accumulators (currentIndex i)).toMathlib +
        (schedule.addend i).toMathlib := by
  rw [active_accumulator run i hcontrol]
  exact (genericStepPoint_group_law_mathlib
    E (run.accumulators (currentIndex i)) (schedule.addend i)
    (run.genericDomain i)).symm

/-- One certified schedule step in the Mathlib group-law view: inactive bits
preserve the accumulator, while active bits add the selected fixed addend
[RNSL17, ECDLP.tex:589-593]. -/
theorem accumulator_step_group_law_mathlib
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.accumulators (nextIndex i)).toMathlib =
      if run.controls i then
        (run.accumulators (currentIndex i)).toMathlib +
          (schedule.addend i).toMathlib
      else
        (run.accumulators (currentIndex i)).toMathlib := by
  cases hcontrol : run.controls i
  · simpa using inactive_accumulator_group_law_mathlib run i hcontrol
  · simpa using active_accumulator_group_law_mathlib run i hcontrol

/-- The active-step `x` accumulator agrees with the lower-level generic
point-addition coordinate formula. -/
theorem active_accumulator_x
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = true) :
    (run.accumulators (nextIndex i)).x =
      genericAddX E (run.accumulators (currentIndex i)) (schedule.addend i) := by
  rw [active_accumulator run i hcontrol]
  rfl

/-- The active-step `y` accumulator agrees with the lower-level generic
point-addition coordinate formula. -/
theorem active_accumulator_y
    (run : Run E schedule) (i : Fin schedule.length)
    (hcontrol : run.controls i = true) :
    (run.accumulators (nextIndex i)).y =
      genericAddY E (run.accumulators (currentIndex i)) (schedule.addend i) := by
  rw [active_accumulator run i hcontrol]
  rfl

/-- Circuit-facing bridge for the zero-control branch of one certified
schedule step. -/
theorem controlledCircuit_apply_certified_zero
    [NeZero p] (run : Run E schedule) (i : Fin schedule.length)
    (params : ControlledPointAddition.ResourceParameters)
    (hcontrol : run.controls i = false) :
    Circuit.apply
        (ControlledPointAddition.controlledCircuit E (schedule.addend i) params)
        (PureState.ket
          (R := ControlledPointAddition.register E (schedule.addend i))
          (run.controlledStepData i) :
          StateVector (ControlledPointAddition.register E (schedule.addend i))) =
      (PureState.ket
        (R := ControlledPointAddition.register E (schedule.addend i))
        ({ input := run.stepInput i
           control := false
           targetX := 0
           targetY := 0
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)) :
        StateVector (ControlledPointAddition.register E (schedule.addend i))) := by
  dsimp [controlledStepData]
  rw [hcontrol]
  exact
    ControlledPointAddition.controlledCircuit_apply_zero_branch
      E (schedule.addend i) params (run.stepInput i)

/-- Homogeneous-data bridge for the zero-control branch of one certified
schedule step.  This is the same lower-level theorem as
`controlledCircuit_apply_certified_zero`, but with the schedule-wide wrapper as
the source of the per-addend ECADD data. -/
theorem controlledCircuit_apply_homogeneous_zero
    [NeZero p] (run : Run E schedule) (i : Fin schedule.length)
    (params : ControlledPointAddition.ResourceParameters)
    (hcontrol : run.controls i = false) :
    Circuit.apply
        (ControlledPointAddition.controlledCircuit E (schedule.addend i) params)
        (PureState.ket
          (R := ControlledPointAddition.register E (schedule.addend i))
          ((run.homogeneousStepData i).toControlled) :
          StateVector (ControlledPointAddition.register E (schedule.addend i))) =
      (PureState.ket
        (R := ControlledPointAddition.register E (schedule.addend i))
        ({ input := run.stepInput i
           control := false
           targetX := 0
           targetY := 0
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)) :
        StateVector (ControlledPointAddition.register E (schedule.addend i))) := by
  simpa using controlledCircuit_apply_certified_zero run i params hcontrol

/-- Circuit-facing bridge for the one-control branch of one certified schedule
step. -/
theorem controlledCircuit_apply_certified_one
    [NeZero p] (run : Run E schedule) (i : Fin schedule.length)
    (params : ControlledPointAddition.ResourceParameters)
    (hcontrol : run.controls i = true) :
    Circuit.apply
        (ControlledPointAddition.controlledCircuit E (schedule.addend i) params)
        (PureState.ket
          (R := ControlledPointAddition.register E (schedule.addend i))
          (run.controlledStepData i) :
          StateVector (ControlledPointAddition.register E (schedule.addend i))) =
      (PureState.ket
        (R := ControlledPointAddition.register E (schedule.addend i))
        ({ input := run.stepInput i
           control := true
           targetX := genericAddX E (run.stepInput i).1 (schedule.addend i)
           targetY := genericAddY E (run.stepInput i).1 (schedule.addend i)
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)) :
        StateVector (ControlledPointAddition.register E (schedule.addend i))) := by
  dsimp [controlledStepData]
  rw [hcontrol]
  exact
    ControlledPointAddition.controlledCircuit_apply_one_branch
      E (schedule.addend i) params (run.stepInput i)

/-- Homogeneous-data bridge for the one-control branch of one certified
schedule step.  The common wrapper transports back to the per-addend controlled
ECADD data before applying the existing endpoint theorem. -/
theorem controlledCircuit_apply_homogeneous_one
    [NeZero p] (run : Run E schedule) (i : Fin schedule.length)
    (params : ControlledPointAddition.ResourceParameters)
    (hcontrol : run.controls i = true) :
    Circuit.apply
        (ControlledPointAddition.controlledCircuit E (schedule.addend i) params)
        (PureState.ket
          (R := ControlledPointAddition.register E (schedule.addend i))
          ((run.homogeneousStepData i).toControlled) :
          StateVector (ControlledPointAddition.register E (schedule.addend i))) =
      (PureState.ket
        (R := ControlledPointAddition.register E (schedule.addend i))
        ({ input := run.stepInput i
           control := true
           targetX := genericAddX E (run.stepInput i).1 (schedule.addend i)
           targetY := genericAddY E (run.stepInput i).1 (schedule.addend i)
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)) :
        StateVector (ControlledPointAddition.register E (schedule.addend i))) := by
  simpa using controlledCircuit_apply_certified_one run i params hcontrol

/-- The lifted clean map for a certified schedule step agrees with the existing
per-addend controlled ECADD endpoint and preserves the external work label. -/
theorem controlledStepCleanMap_apply_certified
    (run : Run E schedule) (i : Fin schedule.length)
    (Work : Type) (w : Work) :
    (StepData.withWorkCleanMapAt E schedule i Work).perm
        (run.homogeneousStepData i, w) =
      (StepData.ofControlled i
        (ControlledPointAddition.Data.addIntoTarget (run.controlledStepData i)), w) := by
  simp [homogeneousStepData, StepData.withWorkCleanMapAt]

/-- Zero-control certified schedule steps are identity updates under the lifted
clean map. -/
theorem controlledStepCleanMap_apply_certified_zero
    (run : Run E schedule) (i : Fin schedule.length)
    (Work : Type) (w : Work) (hcontrol : run.controls i = false) :
    (StepData.withWorkCleanMapAt E schedule i Work).perm
        (run.homogeneousStepData i, w) =
      (StepData.ofControlled i
        ({ input := run.stepInput i
           control := false
           targetX := 0
           targetY := 0
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)), w) := by
  rw [controlledStepCleanMap_apply_certified]
  dsimp [controlledStepData]
  rw [hcontrol]
  simp [ControlledPointAddition.Data.addIntoTarget]

/-- One-control certified schedule steps apply the generic affine ECADD update
under the lifted clean map. -/
theorem controlledStepCleanMap_apply_certified_one
    (run : Run E schedule) (i : Fin schedule.length)
    (Work : Type) (w : Work) (hcontrol : run.controls i = true) :
    (StepData.withWorkCleanMapAt E schedule i Work).perm
        (run.homogeneousStepData i, w) =
      (StepData.ofControlled i
        ({ input := run.stepInput i
           control := true
           targetX := genericAddX E (run.stepInput i).1 (schedule.addend i)
           targetY := genericAddY E (run.stepInput i).1 (schedule.addend i)
           flag := false } : ControlledPointAddition.Data E (schedule.addend i)), w) := by
  rw [controlledStepCleanMap_apply_certified]
  dsimp [controlledStepData]
  rw [hcontrol]
  simp [ControlledPointAddition.Data.addIntoTarget]

/-- The schedule-wide clean composition maps the certified ECADD trace to the
trace of per-step ECADD outputs, while preserving the external work label. -/
theorem controlledTraceCleanComposition_apply_certified
    (run : Run E schedule) (Work : Type) (w : Work) :
    (controlledTraceCleanComposition E schedule Work).perm
        (run.controlledTraceData, w) =
      (run.updatedTraceData, w) := by
  have h :=
    controlledTraceSequentialCleanComposition_apply E schedule Work
      run.controlledTraceData w
  apply Prod.ext
  · funext i
    change
      ((controlledTraceSequentialCleanComposition E schedule Work).perm
        (run.controlledTraceData, w)).1 i =
        (run.updatedTraceData, w).1 i
    rw [congrArg (fun y => y.1 i) h]
    rfl
  · change
      ((controlledTraceSequentialCleanComposition E schedule Work).perm
        (run.controlledTraceData, w)).2 =
        (run.updatedTraceData, w).2
    exact congrArg Prod.snd h

/-- The updated trace exposes the certified accumulator recurrence at every
schedule step.  Active steps return the next accumulator coordinates through the
controlled ECADD endpoint, and inactive steps use the run certificate to keep
the accumulator fixed. -/
theorem updatedTraceData_accumulator_contract
    (run : Run E schedule) (i : Fin schedule.length) :
    (run.updatedTraceData i).input.1 =
        run.accumulators (currentIndex i) ∧
      (run.updatedTraceData i).control = run.controls i ∧
      (run.updatedTraceData i).flag = false ∧
      (run.controls i = false ->
        (run.updatedTraceData i).targetX = 0 ∧
          (run.updatedTraceData i).targetY = 0 ∧
          run.accumulators (nextIndex i) =
            run.accumulators (currentIndex i)) ∧
      (run.controls i = true ->
        (run.updatedTraceData i).targetX =
            (run.accumulators (nextIndex i)).x ∧
          (run.updatedTraceData i).targetY =
            (run.accumulators (nextIndex i)).y) := by
  constructor
  · rfl
  constructor
  · simp [updatedTraceData, controlledStepData,
      ControlledPointAddition.Data.addIntoTarget]
  constructor
  · simp [updatedTraceData, controlledStepData,
      ControlledPointAddition.Data.addIntoTarget]
  constructor
  · intro hcontrol
    constructor
    · simp [updatedTraceData, controlledStepData,
        ControlledPointAddition.Data.addIntoTarget, hcontrol]
    constructor
    · simp [updatedTraceData, controlledStepData,
        ControlledPointAddition.Data.addIntoTarget, hcontrol]
    · exact inactive_accumulator run i hcontrol
  · intro hcontrol
    constructor
    · simp [updatedTraceData, controlledStepData,
        ControlledPointAddition.Data.addIntoTarget, hcontrol,
        (active_accumulator_x run i hcontrol).symm]
    · simp [updatedTraceData, controlledStepData,
        ControlledPointAddition.Data.addIntoTarget, hcontrol,
        (active_accumulator_y run i hcontrol).symm]

/-- Run-level accumulator-composition theorem for the schedule-wide clean
controlled-ECADD trace.  The same composed map consumes the certified controls
and fixed addends, preserves work, and exposes the accumulator recurrence at
each step. -/
theorem controlledTraceCleanComposition_accumulator_contract
    (run : Run E schedule) (Work : Type) (w : Work)
    (i : Fin schedule.length) :
    let out :=
      ((controlledTraceCleanComposition E schedule Work).perm
        (run.controlledTraceData, w)).1 i
    out.input.1 = run.accumulators (currentIndex i) ∧
      out.control = run.controls i ∧
      out.flag = false ∧
      (run.controls i = false ->
        out.targetX = 0 ∧ out.targetY = 0 ∧
          run.accumulators (nextIndex i) =
            run.accumulators (currentIndex i)) ∧
      (run.controls i = true ->
        out.targetX = (run.accumulators (nextIndex i)).x ∧
          out.targetY = (run.accumulators (nextIndex i)).y) := by
  rw [controlledTraceCleanComposition_apply_certified]
  exact updatedTraceData_accumulator_contract run i

end Run

end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
