/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import all QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication
import Mathlib.Combinatorics.Colex

/-!
# Certified scalar-multiplication endpoint

This module layers a typed reversible endpoint and public resource-bound
certificate on top of the fixed-base generic affine schedule certificates in
`ScalarMultiplication`. It does not claim a complete exceptional-case group law,
a signed-windowed route, or a concrete P-256 resource row.  The endpoint follows
the fixed-base controlled-addition scalar-multiplication boundary used for
elliptic-curve discrete-logarithm resource estimates
[RNSL17, ECDLP.tex:589-597,650-699],
while the generic affine branch is the same source route as the lower-level
point-addition formulas [PZ03, ecc.tex:525-551].  Signed/windowed refinements
remain outside this generic endpoint [HJN+20, elliptic-curves.tex:20-36].
-/

section

namespace QuantumAlg
namespace EllipticCurve
namespace PrimeFieldShortWeierstrass
namespace ScalarMultiplication

variable {p : Nat}

/-- Final accumulator slot of a scalar-multiplication schedule. -/
def finalIndex {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E) :
    Fin (schedule.length + 1) :=
  ⟨schedule.length, Nat.lt_succ_self schedule.length⟩

/-- Bit control selected by a scalar for a schedule step. -/
def bitControl {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) (i : Fin schedule.length) : Bool :=
  scalar.val.testBit i.val

/-- The endpoint control bit and fixed-base addend weight use the same schedule
index: bit `i.val` selects the addend whose group-law weight is `2^i.val`
[PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem bitControl_uses_addendWeight_index
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) (i : Fin schedule.length) :
    bitControl schedule scalar i = scalar.val.testBit i.val ∧
      schedule.addendWeight i = 2 ^ i.val := by
  exact ⟨rfl, rfl⟩

/-- Natural scalar represented by the addend weights selected by the scalar
bits in a fixed-base controlled-addition schedule [PZ03, ecc.tex:448-462;
RNSL17, ECDLP.tex:589-593]. -/
def selectedAddendWeight {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) : Nat :=
  Finset.univ.sum (fun i : Fin schedule.length =>
    if bitControl schedule scalar i then schedule.addendWeight i else 0)

/-- Mathlib group-law fold of exactly the addends selected by the scalar bits
in the fixed-base controlled-addition route [PZ03, ecc.tex:448-462; RNSL17,
ECDLP.tex:589-593]. -/
noncomputable def selectedAddendGroupFold {E : PrimeFieldShortWeierstrass p}
    [Fact p.Prime] (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) : E.MathlibPoint :=
  Finset.univ.sum (fun i : Fin schedule.length =>
    if bitControl schedule scalar i then (schedule.addend i).toMathlib else 0)

/-- Inactive scalar bits contribute the identity element to the selected-addend
group fold [RNSL17, ECDLP.tex:589-593]. -/
theorem selectedAddendGroupFold_inactive_term
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) (i : Fin schedule.length)
    (hcontrol : bitControl schedule scalar i = false) :
    (if bitControl schedule scalar i then (schedule.addend i).toMathlib else 0) = 0 := by
  simp [hcontrol]

/-- Active scalar bits contribute the fixed-base group-law multiple attached
to their binary position [PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem selectedAddendGroupFold_active_term
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (fixed : schedule.FixedBaseAddends)
    (scalar : Fin (2 ^ schedule.length)) (i : Fin schedule.length)
    (hcontrol : bitControl schedule scalar i = true) :
    (if bitControl schedule scalar i then (schedule.addend i).toMathlib else 0) =
      schedule.addendWeight i • fixed.base.toMathlib := by
  simp [hcontrol, fixed.addend_toMathlib i]

/-- The selected group-law fold equals the selected natural weight acting on
the fixed base [PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem selectedAddendGroupFold_eq_selectedAddendWeight_nsmul
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (fixed : schedule.FixedBaseAddends)
    (scalar : Fin (2 ^ schedule.length)) :
    selectedAddendGroupFold schedule scalar =
      selectedAddendWeight schedule scalar • fixed.base.toMathlib := by
  unfold selectedAddendGroupFold selectedAddendWeight
  calc
    Finset.univ.sum (fun i : Fin schedule.length =>
        if bitControl schedule scalar i then (schedule.addend i).toMathlib else 0)
        =
      Finset.univ.sum (fun i : Fin schedule.length =>
        if bitControl schedule scalar i then
          schedule.addendWeight i • fixed.base.toMathlib
        else 0) := by
      refine Finset.sum_congr rfl ?_
      intro i _hi
      by_cases hcontrol : bitControl schedule scalar i
      · simp [hcontrol, fixed.addend_toMathlib i]
      · simp [hcontrol]
    _ =
      Finset.univ.sum (fun i : Fin schedule.length =>
        if bitControl schedule scalar i then schedule.addendWeight i else 0) •
          fixed.base.toMathlib := by
      rw [← Finset.sum_nsmul_assoc]
      simp [ite_smul]

private theorem bitIndex_lt_length_of_lt_two_pow {n m i : Nat} (hm : m < 2 ^ n)
    (hi : i ∈ m.bitIndices) : i < n := by
  by_contra hlt
  have hni : n ≤ i := Nat.le_of_not_gt hlt
  have hpow_le : 2 ^ n ≤ 2 ^ i :=
    Nat.pow_le_pow_right (by decide : 0 < 2) hni
  have hi_le : 2 ^ i ≤ m := Nat.two_pow_le_of_mem_bitIndices hi
  exact (Nat.not_le_of_gt hm) (le_trans hpow_le hi_le)

/-- The selected binary addend weights sum to exactly the scalar register
value, using the same bit order as `bitControl` [PZ03, ecc.tex:448-462;
RNSL17, ECDLP.tex:589-593]. -/
theorem selectedAddendWeight_eq_scalar
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) :
    selectedAddendWeight schedule scalar = scalar.val := by
  classical
  unfold selectedAddendWeight
  have hsum :
      (Finset.univ.filter (fun i : Fin schedule.length => bitControl schedule scalar i)).sum
          (fun i : Fin schedule.length => 2 ^ i.val) =
        scalar.val.bitIndices.toFinset.sum (fun i : Nat => 2 ^ i) := by
    refine Finset.sum_bij (fun i _ => i.val) ?_ ?_ ?_ ?_
    · intro i hi
      rw [List.mem_toFinset]
      rw [Nat.mem_bitIndices]
      exact (Finset.mem_filter.mp hi).2
    · intro i₁ _ i₂ _ hval
      exact Fin.ext hval
    · intro j hj
      rw [List.mem_toFinset] at hj
      have hjlt : j < schedule.length :=
        bitIndex_lt_length_of_lt_two_pow scalar.isLt hj
      refine ⟨⟨j, hjlt⟩, ?_, rfl⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      simpa only [bitControl] using Nat.mem_bitIndices.mp hj
    · intro i hi
      rfl
  simpa [Schedule.addendWeight, Finset.sum_filter] using
    hsum.trans (Finset.sum_toFinset_bitIndices_two_pow scalar.val)

/-- For a fixed-base schedule, the group-law fold selected by the scalar bits
is the scalar multiple of the fixed base [PZ03, ecc.tex:448-462; RNSL17,
ECDLP.tex:589-593]. -/
theorem selectedAddendGroupFold_eq_scalar_nsmul
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (fixed : schedule.FixedBaseAddends)
    (scalar : Fin (2 ^ schedule.length)) :
    selectedAddendGroupFold schedule scalar =
      scalar.val • fixed.base.toMathlib := by
  rw [selectedAddendGroupFold_eq_selectedAddendWeight_nsmul schedule fixed scalar,
    selectedAddendWeight_eq_scalar schedule scalar]

private noncomputable def selectedAddendRangeFold
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) (k : Nat) : E.MathlibPoint :=
  (Finset.range k).sum fun j =>
    if h : j < schedule.length then
      if bitControl schedule scalar ⟨j, h⟩ then
        (schedule.addend ⟨j, h⟩).toMathlib
      else
        0
    else
      0

private theorem selectedAddendRangeFold_succ
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) {k : Nat} (hk : k < schedule.length) :
    selectedAddendRangeFold schedule scalar (k + 1) =
      selectedAddendRangeFold schedule scalar k +
        if bitControl schedule scalar ⟨k, hk⟩ then
          (schedule.addend ⟨k, hk⟩).toMathlib
        else
          0 := by
  unfold selectedAddendRangeFold
  rw [Finset.sum_range_succ]
  simp [hk]

private theorem selectedAddendRangeFold_final
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
    (scalar : Fin (2 ^ schedule.length)) :
    selectedAddendRangeFold schedule scalar schedule.length =
      selectedAddendGroupFold schedule scalar := by
  unfold selectedAddendRangeFold selectedAddendGroupFold
  rw [Finset.sum_fin_eq_sum_range]

namespace Run

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}

/-- Output point carried by the final accumulator of a certified run. -/
def outputPoint (run : Run E schedule) : AffinePoint E :=
  run.accumulators (finalIndex schedule)

@[simp] theorem outputPoint_x (run : Run E schedule) :
    run.outputPoint.x = (run.accumulators (finalIndex schedule)).x :=
  rfl

@[simp] theorem outputPoint_y (run : Run E schedule) :
    run.outputPoint.y = (run.accumulators (finalIndex schedule)).y :=
  rfl

private theorem accumulator_after_steps_group_law
    (run : Run E schedule) (scalar : Fin (2 ^ schedule.length))
    (hcontrols : ∀ i : Fin schedule.length,
      run.controls i = bitControl schedule scalar i) :
    ∀ k : Nat, ∀ hk : k ≤ schedule.length,
      (run.accumulators ⟨k, Nat.lt_succ_of_le hk⟩).toMathlib =
        run.startsAt.toMathlib + selectedAddendRangeFold schedule scalar k := by
  intro k
  induction k with
  | zero =>
      intro _hk
      have hstart := congrArg AffinePoint.toMathlib run.startsAt_eq
      simpa [selectedAddendRangeFold] using hstart
  | succ k ih =>
      intro hk_succ
      have hklt : k < schedule.length := Nat.lt_of_succ_le hk_succ
      have hk : k ≤ schedule.length := Nat.le_of_lt hklt
      let i : Fin schedule.length := ⟨k, hklt⟩
      have hstep := accumulator_step_group_law_mathlib run i
      rw [hcontrols i] at hstep
      have hstep' :
          (run.accumulators ⟨k + 1, Nat.lt_succ_of_le hk_succ⟩).toMathlib =
            if bitControl schedule scalar i then
              (run.accumulators ⟨k, Nat.lt_succ_of_le hk⟩).toMathlib +
                (schedule.addend i).toMathlib
            else
              (run.accumulators ⟨k, Nat.lt_succ_of_le hk⟩).toMathlib := by
        simpa [i, currentIndex, nextIndex] using hstep
      rw [hstep']
      have ihk := ih hk
      rw [ihk]
      rw [selectedAddendRangeFold_succ schedule scalar hklt]
      by_cases hbit : bitControl schedule scalar i
      · simp [i, hbit, add_assoc]
      · simp [i, hbit]

/-- A run whose controls are the scalar bits has final accumulator equal to the
start point plus the group-law fold of the selected fixed-base addends
[PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem outputPoint_eq_start_add_selectedAddendGroupFold
    (run : Run E schedule) (scalar : Fin (2 ^ schedule.length))
    (hcontrols : ∀ i : Fin schedule.length,
      run.controls i = bitControl schedule scalar i) :
    run.outputPoint.toMathlib =
      run.startsAt.toMathlib + selectedAddendGroupFold schedule scalar := by
  have hfinal :=
    accumulator_after_steps_group_law (schedule := schedule) run scalar hcontrols
      schedule.length le_rfl
  simpa [outputPoint, finalIndex, selectedAddendRangeFold_final] using hfinal

/-- For a fixed-base schedule, a scalar-bit controlled run has final
accumulator equal to the start point plus the scalar multiple of the fixed base
[PZ03, ecc.tex:448-462; RNSL17, ECDLP.tex:589-593]. -/
theorem outputPoint_eq_start_add_scalar_nsmul
    (run : Run E schedule) (fixed : schedule.FixedBaseAddends)
    (scalar : Fin (2 ^ schedule.length))
    (hcontrols : ∀ i : Fin schedule.length,
      run.controls i = bitControl schedule scalar i) :
    run.outputPoint.toMathlib =
      run.startsAt.toMathlib + scalar.val • fixed.base.toMathlib := by
  rw [outputPoint_eq_start_add_selectedAddendGroupFold run scalar hcontrols,
    selectedAddendGroupFold_eq_scalar_nsmul schedule fixed scalar]

end Run

/-- Source-facing certificate that a scalar/start-point input is realized by
the fixed-base generic affine schedule. -/
structure CertifiedScalarAction (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) where
  /-- Certified output point for a scalar/start-point input. -/
  output : Fin (2 ^ schedule.length) -> AffinePoint E -> AffinePoint E
  /-- Nonexceptional-domain predicate for scalar/start-point inputs. -/
  genericDomain : Fin (2 ^ schedule.length) -> AffinePoint E -> Prop
  /-- Existence of a schedule run realizing each generic scalar action. -/
  hasRun :
    ∀ scalar start,
      genericDomain scalar start ->
        ∃ run : Run E schedule,
          run.startsAt = start ∧
            (∀ i : Fin schedule.length,
              run.controls i = bitControl schedule scalar i) ∧
            run.outputPoint = output scalar start

namespace CertifiedScalarAction

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E}

/-- Extract a certified schedule run for a generic scalar/start-point input. -/
theorem exists_run (cert : CertifiedScalarAction E schedule)
    (scalar : Fin (2 ^ schedule.length)) (start : AffinePoint E)
    (hgeneric : cert.genericDomain scalar start) :
    ∃ run : Run E schedule,
      run.startsAt = start ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule scalar i) ∧
        run.outputPoint = cert.output scalar start :=
  cert.hasRun scalar start hgeneric

end CertifiedScalarAction

namespace CertifiedEndpoint

/-- Data registers for the certified scalar-multiplication endpoint. -/
structure Data (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) where
  /-- Scalar/start-point input bundled with the certificate's generic-domain proof. -/
  input :
    {sp : Fin (2 ^ schedule.length) × AffinePoint E //
      cert.genericDomain sp.1 sp.2}
  /-- Target `x` coordinate accumulator. -/
  targetX : ZMod p
  /-- Target `y` coordinate accumulator. -/
  targetY : ZMod p
  /-- Temporary cleanup flag carried by the endpoint. -/
  flag : Bool
deriving DecidableEq

noncomputable instance instFintypeData (E : PrimeFieldShortWeierstrass p)
    [Fact p.Prime] [NeZero p]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [DecidablePred
      (fun sp : Fin (2 ^ schedule.length) × AffinePoint E =>
        cert.genericDomain sp.1 sp.2)] :
    Fintype (Data E schedule cert) := by
  classical
  let e :
      Data E schedule cert ≃
        ({sp : Fin (2 ^ schedule.length) × AffinePoint E //
          cert.genericDomain sp.1 sp.2} × ZMod p × ZMod p × Bool) := {
    toFun := fun x => (x.input, (x.targetX, (x.targetY, x.flag)))
    invFun := fun x =>
      { input := x.1, targetX := x.2.1, targetY := x.2.2.1, flag := x.2.2.2 }
    left_inv := by
      intro x
      cases x
      rfl
    right_inv := by
      intro x
      rcases x with ⟨input, targetX, targetY, flag⟩
      rfl }
  exact Fintype.ofEquiv _ e.symm

namespace Data

variable {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
variable {schedule : Schedule E} {cert : CertifiedScalarAction E schedule}

/-- The temporary flag is clean at the public endpoint boundary. -/
def FlagClean (x : Data E schedule cert) : Prop :=
  x.flag = false

/-- Scalar register component of the certified endpoint input. -/
def scalar (x : Data E schedule cert) : Fin (2 ^ schedule.length) :=
  x.input.1.1

/-- Start-point register component of the certified endpoint input. -/
def startPoint (x : Data E schedule cert) : AffinePoint E :=
  x.input.1.2

/-- Certified scalar-action output point for this endpoint input. -/
def outputPoint (x : Data E schedule cert) : AffinePoint E :=
  cert.output x.scalar x.startPoint

/-- Add the certified scalar-action output to target coordinate registers. -/
def addIntoTarget (x : Data E schedule cert) : Data E schedule cert where
  input := x.input
  targetX := x.targetX + x.outputPoint.x
  targetY := x.targetY + x.outputPoint.y
  flag := x.flag

/-- Subtract the certified scalar-action output from target coordinates. -/
def subFromTarget (x : Data E schedule cert) : Data E schedule cert where
  input := x.input
  targetX := x.targetX - x.outputPoint.x
  targetY := x.targetY - x.outputPoint.y
  flag := x.flag

/-- Certified scalar multiplication as a reversible coordinate-target map. -/
def mulEquiv (E : PrimeFieldShortWeierstrass p)
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule) :
    Equiv.Perm (Data E schedule cert) where
  toFun := addIntoTarget
  invFun := subFromTarget
  left_inv := by
    intro x
    cases x
    simp [addIntoTarget, subFromTarget, outputPoint, scalar, startPoint]
  right_inv := by
    intro x
    cases x
    simp [addIntoTarget, subFromTarget, outputPoint, scalar, startPoint]

@[simp] theorem mulEquiv_apply {schedule : Schedule E}
    {cert : CertifiedScalarAction E schedule} (x : Data E schedule cert) :
    mulEquiv E schedule cert x = x.addIntoTarget :=
  rfl

/-- Certified scalar multiplication with an external work register. -/
def withWorkEquiv (E : PrimeFieldShortWeierstrass p)
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) : Equiv.Perm (Data E schedule cert × Work) :=
  Equiv.prodCongr (mulEquiv E schedule cert) (Equiv.refl Work)

@[simp] theorem withWorkEquiv_apply {schedule : Schedule E}
    {cert : CertifiedScalarAction E schedule} {Work : Type}
    (x : Data E schedule cert) (w : Work) :
    withWorkEquiv E schedule cert Work (x, w) = (x.addIntoTarget, w) :=
  rfl

/-- The certified scalar-multiplication map leaves the external work register clean. -/
theorem withWorkEquiv_preserves_work {schedule : Schedule E}
    {cert : CertifiedScalarAction E schedule} {Work : Type} :
    WorkRegister.Preserves (withWorkEquiv E schedule cert Work) := by
  intro x
  rfl

/-- Certified clean reversible map for scalar multiplication with external work. -/
def withWorkCleanMap (E : PrimeFieldShortWeierstrass p)
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) : WorkRegister.CleanReversibleMap (Data E schedule cert) Work where
  perm := withWorkEquiv E schedule cert Work
  preservesWork := withWorkEquiv_preserves_work

end Data

/-- Register whose labels are certified scalar-multiplication endpoint states. -/
@[implicit_reducible]
noncomputable def register (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] :
    Register where
  Index := Data E schedule cert
  fintype := inferInstance
  decEq := inferInstance

/-- Metadata-free certified scalar-multiplication operator for a fixed schedule certificate. -/
noncomputable def mulOp (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] : UnitaryOperator (register E schedule cert) :=
  UnitaryOperator.ofPerm (Data.mulEquiv E schedule cert).symm

/-- Basis action of the certified scalar-multiplication operator. -/
theorem mulOp_apply_ket (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] (x : Data E schedule cert) :
    (mulOp E schedule cert).apply
        (NormalizedVector.ket (R := register E schedule cert) x) =
      NormalizedVector.ket (R := register E schedule cert) x.addIntoTarget := by
  rw [mulOp, UnitaryOperator.ofPerm_apply_ket]
  rfl

end CertifiedEndpoint

end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg

end
