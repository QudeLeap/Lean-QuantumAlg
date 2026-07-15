/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Primitives.EllipticCurve.ScalarMultiplication
public import QuantumAlg.Primitives.EllipticCurve.Resource
public import Mathlib.Combinatorics.Colex

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

@[expose] public section

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
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
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
    {E : PrimeFieldShortWeierstrass p} [Fact p.Prime] (schedule : Schedule E)
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
      simp [bitControl, Nat.mem_bitIndices.mp hj]
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
noncomputable def register (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] :
    Register where
  Index := Data E schedule cert
  fintype := inferInstance
  decEq := inferInstance

/-- Certified scalar-multiplication gate for a fixed schedule certificate. -/
noncomputable def mulGate (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] : Gate (register E schedule cert) :=
  Gate.ofPerm (Data.mulEquiv E schedule cert).symm

/-- Basis action of the certified scalar-multiplication gate. -/
theorem mulGate_apply_ket (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] (x : Data E schedule cert) :
    (mulGate E schedule cert).apply
        (PureState.ket (R := register E schedule cert) x) =
      PureState.ket (R := register E schedule cert) x.addIntoTarget := by
  rw [mulGate, Gate.ofPerm_apply_ket]
  rfl

/-- Resource parameters attached to the certified scalar-multiplication endpoint. -/
structure ResourceParameters where
  /-- Resource profile for each controlled-addition schedule step. -/
  controlledAdditionProfile : ModularArithmeticResourceProfile
  /-- Resource profile for clean composition around the step sequence. -/
  cleanCompositionProfile : ModularArithmeticResourceProfile
  /-- Resource profile for the final coordinate target update. -/
  targetUpdateProfile : ModularArithmeticResourceProfile
deriving DecidableEq

namespace ResourceParameters

/-- Compose scalar-multiplication resources from repeated controlled additions,
the clean-work composition layer, and the final target update [RNSL17,
ECDLP.tex:650-699; HJN+20, elliptic-curves.tex:20-36]. -/
def toProfile (params : ResourceParameters) {E : PrimeFieldShortWeierstrass p}
    (schedule : Schedule E) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential
    (ModularArithmeticResourceProfile.repeatSequential schedule.length
      params.controlledAdditionProfile)
    (ModularArithmeticResourceProfile.sequential
      params.cleanCompositionProfile params.targetUpdateProfile)

/-- Scalar-multiplication resource parameters induced by one controlled-ECADD
resource hook and the scalar endpoint overhead profiles [RNSL17,
ECDLP.tex:650-699; HJN+20, elliptic-curves.tex:20-36]. -/
def ofControlledAdditionHook
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile) :
    ResourceParameters where
  controlledAdditionProfile := controlledAdditionHook.profile
  cleanCompositionProfile := cleanCompositionProfile
  targetUpdateProfile := targetUpdateProfile

@[simp] theorem ofControlledAdditionHook_controlledAdditionProfile
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile) :
    (ofControlledAdditionHook controlledAdditionHook
      cleanCompositionProfile targetUpdateProfile).controlledAdditionProfile =
      controlledAdditionHook.profile :=
  rfl

@[simp] theorem ofControlledAdditionHook_cleanCompositionProfile
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile) :
    (ofControlledAdditionHook controlledAdditionHook
      cleanCompositionProfile targetUpdateProfile).cleanCompositionProfile =
      cleanCompositionProfile :=
  rfl

@[simp] theorem ofControlledAdditionHook_targetUpdateProfile
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile) :
    (ofControlledAdditionHook controlledAdditionHook
      cleanCompositionProfile targetUpdateProfile).targetUpdateProfile =
      targetUpdateProfile :=
  rfl

/-- Concrete public component bounds for a scalar-multiplication endpoint. -/
structure PublicBaselineBounds where
  /-- Schedule length used when repeating the controlled-addition bound. -/
  scheduleLength : Nat
  /-- Public bound for one controlled-addition step. -/
  controlledAdditionBound : ModularArithmeticResourceProfile
  /-- Public bound for clean composition around the step sequence. -/
  cleanCompositionBound : ModularArithmeticResourceProfile
  /-- Public bound for the final coordinate target update. -/
  targetUpdateBound : ModularArithmeticResourceProfile
deriving DecidableEq

namespace PublicBaselineBounds

/-- The composed public bound profile for scalar multiplication. -/
def toProfile (bounds : PublicBaselineBounds) : ModularArithmeticResourceProfile :=
  ModularArithmeticResourceProfile.sequential
    (ModularArithmeticResourceProfile.repeatSequential bounds.scheduleLength
      bounds.controlledAdditionBound)
    (ModularArithmeticResourceProfile.sequential
      bounds.cleanCompositionBound bounds.targetUpdateBound)

end PublicBaselineBounds

/-- The exact scalar-multiplication profile supports the public baseline. -/
structure SupportsPublicBaseline {E : PrimeFieldShortWeierstrass p}
    (schedule : Schedule E)
    (profile : ModularArithmeticResourceProfile) (bounds : PublicBaselineBounds) :
    Prop where
  upperBound :
    ModularArithmeticResourceProfile.SupportsUpperBound profile bounds.toProfile

/-- Fieldwise source-bound certificate for the scalar-multiplication endpoint. -/
structure SourceBoundCertificate {E : PrimeFieldShortWeierstrass p}
    (schedule : Schedule E)
    (params : ResourceParameters) (bounds : PublicBaselineBounds) : Prop where
  scheduleLength_eq : bounds.scheduleLength = schedule.length
  controlledAddition_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.controlledAdditionProfile bounds.controlledAdditionBound
  cleanComposition_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.cleanCompositionProfile bounds.cleanCompositionBound
  targetUpdate_le :
    ModularArithmeticResourceProfile.SupportsUpperBound
      params.targetUpdateProfile bounds.targetUpdateBound

/-- The component certificate implies the composed scalar-multiplication bound. -/
theorem SourceBoundCertificate.supportsUpperBound {E : PrimeFieldShortWeierstrass p}
    {schedule : Schedule E} {params : ResourceParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate schedule params bounds) :
    ModularArithmeticResourceProfile.SupportsUpperBound
      (params.toProfile schedule) bounds.toProfile := by
  rw [toProfile, PublicBaselineBounds.toProfile, cert.scheduleLength_eq]
  exact
    ModularArithmeticResourceProfile.SupportsUpperBound.sequential
      (ModularArithmeticResourceProfile.SupportsUpperBound.repeatSequential
        cert.controlledAddition_le)
      (ModularArithmeticResourceProfile.SupportsUpperBound.sequential
        cert.cleanComposition_le cert.targetUpdate_le)

/-- Public-baseline form of the scalar-multiplication source-bound certificate. -/
theorem SourceBoundCertificate.supportsPublicBaseline
    {E : PrimeFieldShortWeierstrass p}
    {schedule : Schedule E} {params : ResourceParameters}
    {bounds : PublicBaselineBounds}
    (cert : SourceBoundCertificate schedule params bounds) :
    SupportsPublicBaseline schedule (params.toProfile schedule) bounds where
  upperBound := cert.supportsUpperBound

/-- Abstract ECC resource hook induced by a certified scalar-multiplication endpoint. -/
def resourceHook (params : ResourceParameters) {E : PrimeFieldShortWeierstrass p}
    (schedule : Schedule E) (width cleanQubits dirtyQubits : Nat) :
    QuantumAlg.EllipticCurve.ResourceHook :=
  QuantumAlg.EllipticCurve.ResourceHook.ofProfile width
    (params.toProfile schedule) cleanQubits dirtyQubits

/-- Hook-level ECMUL recurrence induced by a controlled-ECADD hook. Sequential
controlled additions scale counted work by the schedule length and reuse live
controlled-addition footprint; scalar endpoint overheads are composed as
abstract profiles, without asserting source-specific formulas [RNSL17,
ECDLP.tex:650-699; HJN+20, elliptic-curves.tex:20-36]. -/
def resourceHookFromControlledAdditionHook
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile)
    (extraCleanQubits extraDirtyQubits : Nat) :
    QuantumAlg.EllipticCurve.ResourceHook :=
  QuantumAlg.EllipticCurve.ResourceHook.ofProfile controlledAdditionHook.width
    ((ofControlledAdditionHook controlledAdditionHook
      cleanCompositionProfile targetUpdateProfile).toProfile schedule)
    (max controlledAdditionHook.cleanQubits extraCleanQubits)
    (max controlledAdditionHook.dirtyQubits extraDirtyQubits)

@[simp] theorem resourceHookFromControlledAdditionHook_width
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile)
    (extraCleanQubits extraDirtyQubits : Nat) :
    (resourceHookFromControlledAdditionHook controlledAdditionHook schedule
      cleanCompositionProfile targetUpdateProfile extraCleanQubits extraDirtyQubits).width =
      controlledAdditionHook.width :=
  rfl

@[simp] theorem resourceHookFromControlledAdditionHook_profile
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile)
    (extraCleanQubits extraDirtyQubits : Nat) :
    (resourceHookFromControlledAdditionHook controlledAdditionHook schedule
      cleanCompositionProfile targetUpdateProfile extraCleanQubits extraDirtyQubits).profile =
      (ofControlledAdditionHook controlledAdditionHook
        cleanCompositionProfile targetUpdateProfile).toProfile schedule :=
  rfl

@[simp] theorem resourceHookFromControlledAdditionHook_cleanQubits
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile)
    (extraCleanQubits extraDirtyQubits : Nat) :
    (resourceHookFromControlledAdditionHook controlledAdditionHook schedule
      cleanCompositionProfile targetUpdateProfile extraCleanQubits extraDirtyQubits).cleanQubits =
      max controlledAdditionHook.cleanQubits extraCleanQubits :=
  rfl

@[simp] theorem resourceHookFromControlledAdditionHook_dirtyQubits
    (controlledAdditionHook : QuantumAlg.EllipticCurve.ResourceHook)
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    (cleanCompositionProfile targetUpdateProfile : ModularArithmeticResourceProfile)
    (extraCleanQubits extraDirtyQubits : Nat) :
    (resourceHookFromControlledAdditionHook controlledAdditionHook schedule
      cleanCompositionProfile targetUpdateProfile extraCleanQubits extraDirtyQubits).dirtyQubits =
      max controlledAdditionHook.dirtyQubits extraDirtyQubits :=
  rfl

/-- Fieldwise hook bounds transfer through the controlled-ECADD-to-ECMUL
resource recurrence [RNSL17, ECDLP.tex:650-699; HJN+20,
elliptic-curves.tex:20-36]. -/
theorem resourceHookFromControlledAdditionHook_supportsUpperBound
    {controlledAdditionHook controlledAdditionBound :
      QuantumAlg.EllipticCurve.ResourceHook}
    {E : PrimeFieldShortWeierstrass p} (schedule : Schedule E)
    {cleanCompositionProfile cleanCompositionBound
      targetUpdateProfile targetUpdateBound : ModularArithmeticResourceProfile}
    {extraCleanQubits extraCleanBound extraDirtyQubits extraDirtyBound : Nat}
    (hcontrolled :
      QuantumAlg.EllipticCurve.ResourceHook.SupportsUpperBound
        controlledAdditionHook controlledAdditionBound)
    (hclean :
      ModularArithmeticResourceProfile.SupportsUpperBound
        cleanCompositionProfile cleanCompositionBound)
    (htarget :
      ModularArithmeticResourceProfile.SupportsUpperBound
        targetUpdateProfile targetUpdateBound)
    (hcleanQubits : extraCleanQubits ≤ extraCleanBound)
    (hdirtyQubits : extraDirtyQubits ≤ extraDirtyBound) :
    QuantumAlg.EllipticCurve.ResourceHook.SupportsUpperBound
      (resourceHookFromControlledAdditionHook controlledAdditionHook schedule
        cleanCompositionProfile targetUpdateProfile extraCleanQubits extraDirtyQubits)
      (resourceHookFromControlledAdditionHook controlledAdditionBound schedule
        cleanCompositionBound targetUpdateBound extraCleanBound extraDirtyBound) where
  width_eq := hcontrolled.width_eq
  profile_le :=
    (SourceBoundCertificate.supportsUpperBound
      ({ scheduleLength_eq := rfl
         controlledAddition_le := hcontrolled.profile_le
         cleanComposition_le := hclean
         targetUpdate_le := htarget } :
        SourceBoundCertificate schedule
          (ofControlledAdditionHook controlledAdditionHook
            cleanCompositionProfile targetUpdateProfile)
          ({ scheduleLength := schedule.length
             controlledAdditionBound := controlledAdditionBound.profile
             cleanCompositionBound := cleanCompositionBound
             targetUpdateBound := targetUpdateBound } : PublicBaselineBounds)))
  cleanQubits_le := max_le_max hcontrolled.cleanQubits_le hcleanQubits
  dirtyQubits_le := max_le_max hcontrolled.dirtyQubits_le hdirtyQubits

end ResourceParameters

/-- Typed endpoint witness for certified scalar multiplication, modeled as one
permutation gate with an attached resource profile. -/
noncomputable def mulCircuit (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] (params : ResourceParameters) :
    Circuit (register E schedule cert) :=
  Circuit.ofGate "elliptic-curve-certified-scalar-multiplication"
    (mulGate E schedule cert) (params.toProfile schedule).toResourceProfile
    (params.toProfile schedule).circuitDepth
    (params.toProfile schedule).oracleQueries

/-- Basis-state correctness for the certified scalar-multiplication circuit. -/
theorem mulCircuit_apply_ket (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E)
    (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] (params : ResourceParameters)
    (x : Data E schedule cert) :
    Circuit.apply (mulCircuit E schedule cert params)
        (PureState.ket (R := register E schedule cert) x :
          StateVector (register E schedule cert)) =
      (PureState.ket (R := register E schedule cert) x.addIntoTarget :
        StateVector (register E schedule cert)) := by
  simpa [mulCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (register E schedule cert) =>
      (psi : StateVector (register E schedule cert)))
      (mulGate_apply_ket E schedule cert x)

/-- Clean-target correctness for the certified scalar-multiplication endpoint. -/
theorem mulCircuit_apply_clean_ket
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)] (params : ResourceParameters)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    Circuit.apply (mulCircuit E schedule cert params)
        (PureState.ket (R := register E schedule cert)
          ({ input := input, targetX := 0, targetY := 0, flag := false } :
            Data E schedule cert) :
          StateVector (register E schedule cert)) =
      (PureState.ket (R := register E schedule cert)
        ({ input := input
           targetX := (cert.output input.1.1 input.1.2).x
           targetY := (cert.output input.1.1 input.1.2).y
           flag := false } : Data E schedule cert) :
          StateVector (register E schedule cert)) := by
  simpa [Data.addIntoTarget, Data.outputPoint, Data.scalar, Data.startPoint] using
    mulCircuit_apply_ket E schedule cert params
      ({ input := input, targetX := 0, targetY := 0, flag := false } :
        Data E schedule cert)

/-- Certified scalar multiplication as an external-work clean reversible circuit. -/
noncomputable def mulWithWorkCircuit
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    [Fintype (Data E schedule cert)] (params : ResourceParameters) :
    Circuit (WorkRegister.CleanReversibleMap.register (Data E schedule cert) Work) :=
  (Data.withWorkCleanMap E schedule cert Work).circuit (params.toProfile schedule)

/-- Basis-state correctness for scalar multiplication with an external work register. -/
theorem mulWithWorkCircuit_apply_ket
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    [Fintype (Data E schedule cert)] (params : ResourceParameters)
    (x : Data E schedule cert) (w : Work) :
    Circuit.apply (mulWithWorkCircuit E schedule cert Work params)
        (PureState.ket
          (R := WorkRegister.CleanReversibleMap.register
            (Data E schedule cert) Work) (x, w) :
          StateVector (WorkRegister.CleanReversibleMap.register
            (Data E schedule cert) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (Data E schedule cert) Work) (x.addIntoTarget, w) :
        StateVector (WorkRegister.CleanReversibleMap.register
          (Data E schedule cert) Work)) := by
  simpa [mulWithWorkCircuit, Data.withWorkCleanMap, Data.withWorkEquiv] using
    WorkRegister.CleanReversibleMap.circuit_apply_ket
      (clean := Data.withWorkCleanMap E schedule cert Work)
      (profile := params.toProfile schedule) (x := (x, w))

/-- The external-work scalar-multiplication circuit preserves clean work. -/
theorem mulWithWorkCircuit_preserves_work
    (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) (_params : ResourceParameters)
    (x : Data E schedule cert) (w : Work) :
    ((Data.withWorkCleanMap E schedule cert Work).perm (x, w)).2 = w := by
  exact (Data.withWorkCleanMap E schedule cert Work).preservesWork (x, w)

/-- Clean-target correctness with an external work register. -/
theorem mulWithWorkCircuit_apply_clean_ket
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    [Fintype (Data E schedule cert)] (params : ResourceParameters)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) (w : Work) :
    Circuit.apply (mulWithWorkCircuit E schedule cert Work params)
        (PureState.ket
          (R := WorkRegister.CleanReversibleMap.register
            (Data E schedule cert) Work)
          (({ input := input, targetX := 0, targetY := 0, flag := false } :
            Data E schedule cert), w) :
          StateVector (WorkRegister.CleanReversibleMap.register
            (Data E schedule cert) Work)) =
      (PureState.ket
        (R := WorkRegister.CleanReversibleMap.register
          (Data E schedule cert) Work)
        (({ input := input
            targetX := (cert.output input.1.1 input.1.2).x
            targetY := (cert.output input.1.1 input.1.2).y
            flag := false } : Data E schedule cert), w) :
          StateVector (WorkRegister.CleanReversibleMap.register
            (Data E schedule cert) Work)) := by
  simpa [Data.addIntoTarget, Data.outputPoint, Data.scalar, Data.startPoint] using
    mulWithWorkCircuit_apply_ket E schedule cert Work params
      ({ input := input, targetX := 0, targetY := 0, flag := false } :
        Data E schedule cert) w

/-- Resource-correct witness for the external-work scalar-multiplication circuit. -/
noncomputable def mulWithWorkCircuitResourceCorrectWitness
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    (Work : Type) [Fintype Work] [DecidableEq Work]
    [Fintype (Data E schedule cert)] (params : ResourceParameters) :
    ResourceCorrectWitness
      (R := WorkRegister.CleanReversibleMap.register (Data E schedule cert) Work)
      (∀ x : Data E schedule cert, ∀ w : Work,
        Circuit.apply (mulWithWorkCircuit E schedule cert Work params)
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register
              (Data E schedule cert) Work) (x, w) :
            StateVector (WorkRegister.CleanReversibleMap.register
              (Data E schedule cert) Work)) =
          (PureState.ket
            (R := WorkRegister.CleanReversibleMap.register
              (Data E schedule cert) Work) (x.addIntoTarget, w) :
            StateVector (WorkRegister.CleanReversibleMap.register
              (Data E schedule cert) Work)))
      ((mulWithWorkCircuit E schedule cert Work params).resources =
          (params.toProfile schedule).toResourceProfile ∧
        (mulWithWorkCircuit E schedule cert Work params).depth =
          (params.toProfile schedule).circuitDepth ∧
        (mulWithWorkCircuit E schedule cert Work params).queryDepth =
          (params.toProfile schedule).oracleQueries) := by
  exact
    { circuit := mulWithWorkCircuit E schedule cert Work params
      correctness := fun x w => mulWithWorkCircuit_apply_ket E schedule cert Work params x w
      resources := ⟨rfl, rfl, rfl⟩ }

/-- Certified endpoint theorem: clean-target correctness, existence of a
matching schedule run, and resource projection all refer to the same supplied
scalar-action certificate. -/
theorem main_with_schedule_certificate
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)]
    (params : ResourceParameters)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    Circuit.apply (mulCircuit E schedule cert params)
        (PureState.ket (R := register E schedule cert)
          ({ input := input, targetX := 0, targetY := 0, flag := false } :
            Data E schedule cert) :
          StateVector (register E schedule cert)) =
      (PureState.ket (R := register E schedule cert)
        ({ input := input
           targetX := (cert.output input.1.1 input.1.2).x
           targetY := (cert.output input.1.1 input.1.2).y
           flag := false } : Data E schedule cert) :
          StateVector (register E schedule cert)) ∧
    (∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2) ∧
    (mulCircuit E schedule cert params).resources =
        (params.toProfile schedule).toResourceProfile ∧
    (mulCircuit E schedule cert params).depth =
        (params.toProfile schedule).circuitDepth ∧
    (mulCircuit E schedule cert params).queryDepth =
        (params.toProfile schedule).oracleQueries := by
  constructor
  · exact mulCircuit_apply_clean_ket E schedule cert params input
  constructor
  · exact cert.exists_run input.1.1 input.1.2 input.2
  · exact ⟨rfl, rfl, rfl⟩

/-- Public-bounds endpoint for certified generic affine scalar multiplication. -/
theorem main_with_public_bounds
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds :
      ResourceParameters.SourceBoundCertificate schedule params bounds)
    (input :
      {sp : Fin (2 ^ schedule.length) × AffinePoint E //
        cert.genericDomain sp.1 sp.2}) :
    Circuit.apply (mulCircuit E schedule cert params)
        (PureState.ket (R := register E schedule cert)
          ({ input := input, targetX := 0, targetY := 0, flag := false } :
            Data E schedule cert) :
          StateVector (register E schedule cert)) =
      (PureState.ket (R := register E schedule cert)
        ({ input := input
           targetX := (cert.output input.1.1 input.1.2).x
           targetY := (cert.output input.1.1 input.1.2).y
           flag := false } : Data E schedule cert) :
          StateVector (register E schedule cert)) ∧
    (∃ run : Run E schedule,
      run.startsAt = input.1.2 ∧
        (∀ i : Fin schedule.length,
          run.controls i = bitControl schedule input.1.1 i) ∧
        run.outputPoint = cert.output input.1.1 input.1.2) ∧
    ResourceParameters.SupportsPublicBaseline
      schedule (params.toProfile schedule) bounds ∧
    ModularArithmeticResourceProfile.SupportsUpperBound
      (params.toProfile schedule) bounds.toProfile ∧
    (mulCircuit E schedule cert params).resources =
        (params.toProfile schedule).toResourceProfile ∧
    (mulCircuit E schedule cert params).depth =
        (params.toProfile schedule).circuitDepth ∧
    (mulCircuit E schedule cert params).queryDepth =
        (params.toProfile schedule).oracleQueries := by
  have hmain := main_with_schedule_certificate E schedule cert params input
  constructor
  · exact hmain.1
  constructor
  · exact hmain.2.1
  constructor
  · exact componentBounds.supportsPublicBaseline
  constructor
  · exact componentBounds.supportsUpperBound
  · exact hmain.2.2

/-- Resource-correct public witness for certified scalar multiplication. -/
noncomputable def mainWithPublicBoundsResourceCorrectWitness
    (E : PrimeFieldShortWeierstrass p) [NeZero p] [Fact p.Prime]
    (schedule : Schedule E) (cert : CertifiedScalarAction E schedule)
    [Fintype (Data E schedule cert)]
    (params : ResourceParameters)
    (bounds : ResourceParameters.PublicBaselineBounds)
    (componentBounds :
      ResourceParameters.SourceBoundCertificate schedule params bounds) :
    ResourceCorrectWitness
      (R := register E schedule cert)
      (∀ input :
        {sp : Fin (2 ^ schedule.length) × AffinePoint E //
          cert.genericDomain sp.1 sp.2},
        Circuit.apply (mulCircuit E schedule cert params)
          (PureState.ket (R := register E schedule cert)
            ({ input := input, targetX := 0, targetY := 0, flag := false } :
              Data E schedule cert) :
            StateVector (register E schedule cert)) =
          (PureState.ket (R := register E schedule cert)
            ({ input := input
               targetX := (cert.output input.1.1 input.1.2).x
               targetY := (cert.output input.1.1 input.1.2).y
               flag := false } : Data E schedule cert) :
            StateVector (register E schedule cert)))
      (ResourceParameters.SupportsPublicBaseline
          schedule (params.toProfile schedule) bounds ∧
        ModularArithmeticResourceProfile.SupportsUpperBound
          (params.toProfile schedule) bounds.toProfile ∧
        (mulCircuit E schedule cert params).resources =
          (params.toProfile schedule).toResourceProfile ∧
        (mulCircuit E schedule cert params).depth =
          (params.toProfile schedule).circuitDepth ∧
        (mulCircuit E schedule cert params).queryDepth =
          (params.toProfile schedule).oracleQueries) := by
  exact
    { circuit := mulCircuit E schedule cert params
      correctness := fun input =>
        (main_with_public_bounds E schedule cert params bounds componentBounds input).1
      resources :=
        ⟨componentBounds.supportsPublicBaseline,
          componentBounds.supportsUpperBound, rfl, rfl, rfl⟩ }

end CertifiedEndpoint

end ScalarMultiplication
end PrimeFieldShortWeierstrass
end EllipticCurve
end QuantumAlg
