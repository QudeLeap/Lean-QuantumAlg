/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Init
public import QuantumAlg.Algorithms.OrderFinding.Resource
public import QuantumAlg.Algorithms.OrderFinding.Probability
public import QuantumAlg.Algorithms.QPE
public import QuantumAlg.Core.Circuit
public import QuantumAlg.Primitives.MAU.ModularMultiplicationGate
public import QuantumAlg.Util.OrderFinding
public import QuantumAlg.Util.RationalApproximation
public import Mathlib.Data.Nat.Totient

/-!
# Order finding (exact, dyadic period `r ∣ 2^t`)

Order finding is the quantum core of Shor's factoring algorithm. This module
formalizes the exact regime where the period divides the register size,
`r ∣ 2^t`. In that regime the eigenphase `s/r` is dyadic, quantum phase
estimation returns the basis index `j = s * (2^t / r)` exactly, and a classical
gcd recovers the order.

The period-finding route follows Shor's order-finding reduction and Fourier
post-processing [Sho95, source.tex:1124-1134] [dW19, qcnotes.tex:2155-2301].
The modular-multiplication eigenstate convention is the circuit-level Lean
form of the same order-finding phase analysis [Sho95, source.tex:1550-1633].
-/

@[expose] public section

namespace QuantumAlg

open PureState Gate

noncomputable section

/-! ### Classical order recovery -/

namespace OrderFinding

/-! ### Modular-multiplication eigenstate phase convention -/

/-- Sign convention for Fourier-style phases in modular-multiplication
eigenstates. -/
inductive FourierPhaseSign where
  | positive
  | negative
deriving DecidableEq

/-- The convention used for modular-multiplication eigenstates in order finding:
the eigenvalue has positive phase `exp(2*pi*i*k/r)`, while the eigenstate
coefficient of the `j`-th orbit element has negative phase
`exp(-2*pi*i*k*j/r)` and normalization `1/sqrt r`. -/
structure ModularEigenstateConvention where
  /-- Sign convention used in the modular-multiplication eigenvalue phase. -/
  eigenvalueSign : FourierPhaseSign
  /-- Sign convention used in the modular eigenstate coefficients. -/
  coefficientSign : FourierPhaseSign
  /-- Index origin used for the modular eigenstate orbit. -/
  indexStart : ℕ
  /-- Whether eigenstates use the square-root order normalization. -/
  normalizedBySqrtOrder : Bool
deriving DecidableEq

/-- Selected convention for the modular-multiplication eigenstate statements. -/
def modularEigenstateConvention : ModularEigenstateConvention where
  eigenvalueSign := .positive
  coefficientSign := .negative
  indexStart := 0
  normalizedBySqrtOrder := true

/-- Eigenvalue phase for the `k`-th modular-multiplication eigenstate. This is
the phase convention consumed by the existing QPE interface with `phase = k/r`. -/
def modularEigenphase (r k : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * ((k : ℝ) / r) * Complex.I)

/-- Coefficient of the `j`-th orbit basis state in the `k`-th
modular-multiplication eigenstate. -/
def modularEigenCoefficient (r k j : ℕ) : ℂ :=
  (Real.sqrt (r : ℝ))⁻¹ *
    Complex.exp (-(2 * Real.pi * ((k : ℝ) * j / r)) * Complex.I)

/-- Coordinate register for one length-`r` modular-multiplication cycle. -/
abbrev cycleRegister (r : ℕ) : Register where
  Index := Fin r
  fintype := inferInstance
  decEq := inferInstance

/-- Raw eigenstate vector over the coordinate labels of a length-`r` cycle. The
later modular-multiplication action lemmas map these coordinates onto the
corresponding residue orbit. -/
def cycleEigenstateVec (r k : ℕ) : StateVector (cycleRegister r) :=
  WithLp.toLp 2 fun j : Fin r => modularEigenCoefficient r k j.val

@[simp]
theorem modularEigenphase_eq_qpePhase (r k : ℕ) :
    modularEigenphase r k =
      Complex.exp (2 * Real.pi * ((k : ℝ) / r) * Complex.I) :=
  rfl

@[simp]
theorem modularEigenCoefficient_eq (r k j : ℕ) :
    modularEigenCoefficient r k j =
      (Real.sqrt (r : ℝ))⁻¹ *
        Complex.exp (-(2 * Real.pi * ((k : ℝ) * j / r)) * Complex.I) :=
  rfl

@[simp]
theorem cycleEigenstateVec_apply (r k : ℕ) (j : Fin r) :
    cycleEigenstateVec r k j = modularEigenCoefficient r k j.val :=
  rfl

theorem norm_modularEigenCoefficient (r k j : ℕ) :
    ‖modularEigenCoefficient r k j‖ = (Real.sqrt (r : ℝ))⁻¹ := by
  have hphase :
      ‖Complex.exp (-(2 * Real.pi * ((k : ℝ) * j / r)) * Complex.I)‖ = 1 := by
    simpa using
      Complex.norm_exp_ofReal_mul_I (-(2 * Real.pi * ((k : ℝ) * j / r)))
  rw [modularEigenCoefficient, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (inv_nonneg.mpr (Real.sqrt_nonneg _)),
    hphase, mul_one]

theorem norm_sq_modularEigenCoefficient (r k j : ℕ) :
    ‖modularEigenCoefficient r k j‖ ^ 2 = ((r : ℝ)⁻¹) := by
  rw [norm_modularEigenCoefficient, inv_pow,
    Real.sq_sqrt (by positivity : (0 : ℝ) ≤ (r : ℝ))]

@[simp]
theorem probOutcome_cycleEigenstateVec (r k : ℕ) (j : Fin r) :
    StateVector.probOutcome (cycleEigenstateVec r k) j = ((r : ℝ)⁻¹) := by
  rw [StateVector.probOutcome, cycleEigenstateVec_apply, norm_sq_modularEigenCoefficient]

theorem sum_probOutcome_cycleEigenstateVec (r k : ℕ) (hr : 0 < r) :
    ∑ j : Fin r, StateVector.probOutcome (cycleEigenstateVec r k) j = 1 := by
  calc
    ∑ j : Fin r, StateVector.probOutcome (cycleEigenstateVec r k) j =
        ∑ _j : Fin r, ((r : ℝ)⁻¹) := by
      refine Finset.sum_congr rfl fun j _ => ?_
      exact probOutcome_cycleEigenstateVec r k j
    _ = 1 := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      exact mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hr.ne')

theorem norm_cycleEigenstateVec (r k : ℕ) (hr : 0 < r) :
    ‖cycleEigenstateVec r k‖ = 1 := by
  have hsq : ‖cycleEigenstateVec r k‖ ^ 2 = (1 : ℝ) ^ 2 := by
    calc
      ‖cycleEigenstateVec r k‖ ^ 2 =
          ∑ x, StateVector.probOutcome (cycleEigenstateVec r k) x :=
        (StateVector.sum_probOutcome (cycleEigenstateVec r k)).symm
      _ = 1 := sum_probOutcome_cycleEigenstateVec r k hr
      _ = (1 : ℝ) ^ 2 := by norm_num
  exact (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp hsq

/-- Normalized eigenstate over one length-`r` cycle. -/
def cycleEigenstate (r k : ℕ) (hr : 0 < r) : PureState (cycleRegister r) :=
  PureState.ofVec (cycleEigenstateVec r k) (norm_cycleEigenstateVec r k hr)

/-- Previous coordinate in a finite cycle. This is the raw-vector action of the
forward basis shift `|j> ↦ |j+1 mod r>` on coefficients. -/
def cyclePred (r : ℕ) (j : Fin r) : Fin r :=
  if h : j.val = 0 then
    ⟨r - 1, by
      have hr : 0 < r := by simpa [h] using j.isLt
      exact Nat.pred_lt hr.ne'⟩
  else
    ⟨j.val - 1, lt_of_le_of_lt (Nat.sub_le _ _) j.isLt⟩

theorem cyclePred_val (r : ℕ) (j : Fin r) :
    (cyclePred r j).val = if j.val = 0 then r - 1 else j.val - 1 := by
  unfold cyclePred
  split <;> rfl

@[simp]
theorem cyclePred_val_zero {r : ℕ} (j : Fin r) (h : j.val = 0) :
    (cyclePred r j).val = r - 1 := by
  rw [cyclePred_val, if_pos h]

@[simp]
theorem cyclePred_val_nonzero {r : ℕ} (j : Fin r) (h : j.val ≠ 0) :
    (cyclePred r j).val = j.val - 1 := by
  rw [cyclePred_val, if_neg h]

/-- Next coordinate in a finite cycle. This is the basis-label action
corresponding to modular multiplication by the selected unit on its orbit. -/
def cycleSucc (r : ℕ) (j : Fin r) : Fin r :=
  if h : j.val + 1 < r then
    ⟨j.val + 1, h⟩
  else
    ⟨0, lt_of_le_of_lt (Nat.zero_le _) j.isLt⟩

theorem cycleSucc_val (r : ℕ) (j : Fin r) :
    (cycleSucc r j).val = if j.val + 1 < r then j.val + 1 else 0 := by
  unfold cycleSucc
  split <;> rfl

@[simp]
theorem cycleSucc_val_of_lt {r : ℕ} (j : Fin r) (h : j.val + 1 < r) :
    (cycleSucc r j).val = j.val + 1 := by
  rw [cycleSucc_val, if_pos h]

@[simp]
theorem cycleSucc_val_of_wrap {r : ℕ} (j : Fin r) (h : ¬ j.val + 1 < r) :
    (cycleSucc r j).val = 0 := by
  rw [cycleSucc_val, if_neg h]

/-- Moving to the predecessor and then forward returns the original cycle
coordinate. -/
theorem cycleSucc_cyclePred {r : ℕ} (j : Fin r) :
    cycleSucc r (cyclePred r j) = j := by
  apply Fin.ext
  by_cases hzero : j.val = 0
  · rw [cycleSucc_val, cyclePred_val_zero j hzero, hzero]
    split <;> omega
  · rw [cycleSucc_val, cyclePred_val_nonzero j hzero]
    have hlt : j.val - 1 + 1 < r := by
      have hjpos : 0 < j.val := Nat.pos_of_ne_zero hzero
      omega
    rw [if_pos hlt]
    omega

/-- Orbit label `u^j` for the cyclic subgroup generated by a modular
multiplication unit. -/
def modularOrbitLabel {N n r : ℕ} (D : ModularMultiplicationDomain N n)
    (u : D.UnitCarrier) (j : Fin r) : D.UnitCarrier :=
  u ^ j.val

/-- The generated orbit labels are injective across one full order cycle. -/
theorem modularOrbitLabel_injective_of_order {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) :
    Function.Injective (modularOrbitLabel D u : Fin r → D.UnitCarrier) := by
  intro i j h
  have hmod : i.val ≡ j.val [MOD orderOf u] := by
    exact pow_eq_pow_iff_modEq.mp h
  rw [horder] at hmod
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
  exact Fin.ext hmod

/-- The generated orbit has exactly `r` distinct unit-register labels when the
selected unit has order `r`. -/
private theorem card_modularOrbitLabel_image_of_order {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) :
    ((Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u)).card = r := by
  rw [Finset.card_image_of_injective]
  · simp
  · exact modularOrbitLabel_injective_of_order D u horder

/-- Linear embedding of a cycle-coordinate vector into the unit-register orbit
spanned by the generated labels `u^j`. -/
def modularOrbitLiftVec {N n r : ℕ} (D : ModularMultiplicationDomain N n)
    (u : D.UnitCarrier) (psi : StateVector (cycleRegister r)) :
    StateVector D.unitRegister :=
  WithLp.toLp 2 fun x : D.unitRegister.Index =>
    ∑ j : Fin r,
      psi j * if x = modularOrbitLabel D u j then (1 : ℂ) else 0

/-- On generated orbit labels, the linear orbit lift recovers the original
cycle-coordinate amplitude. -/
theorem modularOrbitLiftVec_apply_orbit {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) (psi : StateVector (cycleRegister r))
    (j : Fin r) :
    modularOrbitLiftVec D u psi (modularOrbitLabel D u j) = psi j := by
  classical
  unfold modularOrbitLiftVec
  change
    (∑ k : Fin r,
      psi k *
        (if modularOrbitLabel D u j = modularOrbitLabel D u k then (1 : ℂ) else 0)) =
      psi j
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ hk
    have hlabel :
        modularOrbitLabel D u j ≠ modularOrbitLabel D u k := by
      intro h
      exact hk ((modularOrbitLabel_injective_of_order D u horder) h.symm)
    simp [hlabel]

/-- The linear orbit lift is zero away from the generated orbit labels. -/
theorem modularOrbitLiftVec_apply_not_mem_orbit {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (psi : StateVector (cycleRegister r)) {x : D.UnitCarrier}
    (hnot :
      x ∉ (Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u)) :
    modularOrbitLiftVec D u psi x = 0 := by
  classical
  unfold modularOrbitLiftVec
  change
    (∑ j : Fin r,
      psi j * if x = modularOrbitLabel D u j then (1 : ℂ) else 0) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : x ≠ modularOrbitLabel D u j := by
    intro h
    exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
  simp [hne]

/-! ### Residue-register bridge for the public modular-multiplication statement -/

/-- The public residue-space register for the `N`-dimensional modular
multiplication unitary. This is the statement-facing carrier from Shor's
notation; implementation circuits may use the selected unit carrier internally
and then transport to this register [Sho95, source.tex:1124-1134]. -/
noncomputable def residueRegister (N : ℕ) [NeZero N] : Register :=
  { Index := ZMod N
    fintype := inferInstance
    decEq := inferInstance }

/-- Multiplication by a unit on the full residue ring. -/
def residueMultiplicationPerm {N : ℕ} (u : (ZMod N)ˣ) : Equiv.Perm (ZMod N) where
  toFun := fun x => (u : ZMod N) * x
  invFun := fun x => ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x
  left_inv x := by
    simp
  right_inv x := by
    simp

@[simp]
theorem residueMultiplicationPerm_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    residueMultiplicationPerm u x = (u : ZMod N) * x :=
  rfl

@[simp]
theorem residueMultiplicationPerm_symm_apply {N : ℕ} (u : (ZMod N)ˣ) (x : ZMod N) :
    (residueMultiplicationPerm u).symm x =
      ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x :=
  rfl

/-- The residue-register modular-multiplication gate. The inverse permutation
is passed to `Gate.ofPerm` so that the source-facing ket action is
`|x> ↦ |u*x>`. -/
noncomputable def residueMultiplicationGate {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) : Gate (residueRegister N) :=
  Gate.ofPerm (residueMultiplicationPerm u).symm

/-- Basis action of the public residue-register modular-multiplication gate. -/
theorem residueMultiplicationGate_apply_ket {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (x : ZMod N) :
    (residueMultiplicationGate u).apply
        (PureState.ket (R := residueRegister N) x) =
      PureState.ket (R := residueRegister N) ((u : ZMod N) * x) := by
  rw [residueMultiplicationGate, Gate.ofPerm_apply_ket]
  rfl

theorem residueMultiplicationGate_applyVec {N : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (psi : StateVector (residueRegister N)) (x : ZMod N) :
    (residueMultiplicationGate u).applyVec psi x =
      psi (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x) := by
  rw [residueMultiplicationGate, Gate.ofPerm_applyVec]
  rfl

/-- Orbit label `u^j` in the public residue register. -/
def residueOrbitLabel {N r : ℕ} (u : (ZMod N)ˣ) (j : Fin r) : ZMod N :=
  (u ^ j.val : (ZMod N)ˣ)

/-- Residue-register orbit labels are injective over one order cycle. -/
theorem residueOrbitLabel_injective_of_order {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) :
    Function.Injective (residueOrbitLabel (N := N) u : Fin r → ZMod N) := by
  intro i j h
  have hunit : u ^ i.val = u ^ j.val := by
    ext
    exact h
  have hmod : i.val ≡ j.val [MOD orderOf u] := by
    exact pow_eq_pow_iff_modEq.mp hunit
  rw [horder] at hmod
  unfold Nat.ModEq at hmod
  rw [Nat.mod_eq_of_lt i.isLt, Nat.mod_eq_of_lt j.isLt] at hmod
  exact Fin.ext hmod

/-- Linear embedding of a cycle-coordinate vector into the public residue
register along the generated orbit labels. -/
noncomputable def residueOrbitLiftVec {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (psi : StateVector (cycleRegister r)) :
    StateVector (residueRegister N) :=
  WithLp.toLp 2 fun x : (residueRegister N).Index =>
    ∑ j : Fin r,
      psi j * if x = residueOrbitLabel u j then (1 : ℂ) else 0

/-- On generated residue-orbit labels, the residue lift recovers the original
cycle-coordinate amplitude. -/
theorem residueOrbitLiftVec_apply_orbit {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (horder : orderOf u = r)
    (psi : StateVector (cycleRegister r)) (j : Fin r) :
    residueOrbitLiftVec u psi (residueOrbitLabel u j) = psi j := by
  classical
  unfold residueOrbitLiftVec
  change
    (∑ k : Fin r,
      psi k *
        (if residueOrbitLabel u j = residueOrbitLabel u k then (1 : ℂ) else 0)) =
      psi j
  rw [Finset.sum_eq_single_of_mem j (Finset.mem_univ j)]
  · simp
  · intro k _ hk
    have hlabel : residueOrbitLabel u j ≠ residueOrbitLabel u k := by
      intro h
      exact hk ((residueOrbitLabel_injective_of_order u horder) h.symm)
    simp [hlabel]

/-- The residue lift is zero away from the generated residue orbit. -/
theorem residueOrbitLiftVec_apply_not_mem_orbit {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (psi : StateVector (cycleRegister r)) {x : ZMod N}
    (hnot :
      x ∉ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)) :
    residueOrbitLiftVec u psi x = 0 := by
  classical
  unfold residueOrbitLiftVec
  change
    (∑ j : Fin r,
      psi j * if x = residueOrbitLabel u j then (1 : ℂ) else 0) = 0
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : x ≠ residueOrbitLabel u j := by
    intro h
    exact hnot (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h.symm⟩)
  simp [hne]

/-- Multiplication by the generating unit advances the public residue-orbit
label by one cycle coordinate. -/
theorem residueMultiplication_residueOrbitLabel_cycleSucc {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) (j : Fin r) :
    (u : ZMod N) * residueOrbitLabel u j =
      residueOrbitLabel u (cycleSucc r j) := by
  unfold residueOrbitLabel
  change ((u * u ^ j.val : (ZMod N)ˣ) : ZMod N) =
    ((u ^ (cycleSucc r j).val : (ZMod N)ˣ) : ZMod N)
  apply congrArg (fun v : (ZMod N)ˣ => (v : ZMod N))
  by_cases hlt : j.val + 1 < r
  · rw [cycleSucc_val_of_lt j hlt]
    rw [pow_succ']
  · rw [cycleSucc_val_of_wrap j hlt]
    have hsucc : j.val + 1 = r := by
      omega
    rw [← pow_succ', hsucc, ← horder, pow_orderOf_eq_one]
    simp

/-- Multiplication by the inverse unit preserves the complement of the public
residue orbit. -/
theorem residueMultiplication_inv_notMem_residueOrbitLabel_image_of_notMem
    {N r : ℕ} (u : (ZMod N)ˣ) (horder : orderOf u = r) {x : ZMod N}
    (hnot : x ∉ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)) :
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x ∉
      (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨j, _hj, hj⟩
  have hx :
      x = residueOrbitLabel u (cycleSucc r j) := by
    calc
      x = (u : ZMod N) * (((u⁻¹ : (ZMod N)ˣ) : ZMod N) * x) := by
        rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel]
        simp
      _ = (u : ZMod N) * residueOrbitLabel u j := by rw [← hj]
      _ = residueOrbitLabel u (cycleSucc r j) :=
        residueMultiplication_residueOrbitLabel_cycleSucc u horder j
  exact hnot (Finset.mem_image.mpr ⟨cycleSucc r j, Finset.mem_univ _, hx.symm⟩)

/-- Multiplication by the generating unit advances the orbit label by one
cycle coordinate. -/
theorem multiplyUnit_modularOrbitLabel_cycleSucc {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) (j : Fin r) :
    D.multiplyUnit u (modularOrbitLabel D u j) =
      modularOrbitLabel D u (cycleSucc r j) := by
  unfold modularOrbitLabel
  rw [ModularMultiplicationDomain.multiplyUnit_apply]
  by_cases hlt : j.val + 1 < r
  · rw [cycleSucc_val_of_lt j hlt]
    rw [pow_succ']
  · rw [cycleSucc_val_of_wrap j hlt]
    have hsucc : j.val + 1 = r := by
      omega
    rw [← pow_succ', hsucc, ← horder, pow_orderOf_eq_one]
    simp

/-- Multiplication by the inverse generating unit moves one step backward on
the generated orbit. -/
theorem multiplyUnit_inv_modularOrbitLabel_cyclePred {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) (j : Fin r) :
    D.multiplyUnit u⁻¹ (modularOrbitLabel D u j) =
      modularOrbitLabel D u (cyclePred r j) := by
  have hfwd :
      D.multiplyUnit u (modularOrbitLabel D u (cyclePred r j)) =
        modularOrbitLabel D u j := by
    rw [multiplyUnit_modularOrbitLabel_cycleSucc D u horder,
      cycleSucc_cyclePred]
  rw [← hfwd]
  simp [ModularMultiplicationDomain.multiplyUnit]

/-- Multiplication by the inverse unit preserves the complement of the
generated orbit. -/
theorem multiplyUnit_inv_notMem_modularOrbitLabel_image_of_notMem
    {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) {x : D.UnitCarrier}
    (hnot :
      x ∉ (Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u)) :
    D.multiplyUnit u⁻¹ x ∉
      (Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u) := by
  intro hmem
  rcases Finset.mem_image.mp hmem with ⟨j, _hj, hlabel⟩
  have hx :
      x = modularOrbitLabel D u (cycleSucc r j) := by
    rw [← multiplyUnit_modularOrbitLabel_cycleSucc D u horder j]
    rw [hlabel]
    simp [ModularMultiplicationDomain.multiplyUnit]
  exact hnot (Finset.mem_image.mpr
    ⟨cycleSucc r j, Finset.mem_univ _, hx.symm⟩)

/-- Basis action of the modular-multiplication gate on the generated orbit:
`U_u |u^j> = |u^{j+1}>`, wrapping at the order. -/
theorem multiplicationGate_apply_modularOrbitKet {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) (j : Fin r) :
    (D.multiplicationGate u).apply
        (PureState.ket (R := D.unitRegister) (modularOrbitLabel D u j)) =
      PureState.ket (R := D.unitRegister)
        (modularOrbitLabel D u (cycleSucc r j)) := by
  rw [ModularMultiplicationDomain.multiplicationGate_apply_ket]
  rw [multiplyUnit_modularOrbitLabel_cycleSucc D u horder j]

/-- Circuit-level basis action of modular multiplication on the generated
orbit. -/
theorem multiplicationCircuit_apply_modularOrbitKet {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (resources : ResourceProfile) (depth queryDepth : ℕ)
    (horder : orderOf u = r) (j : Fin r) :
    Circuit.apply (D.multiplicationCircuit u resources depth queryDepth)
        (PureState.ket (R := D.unitRegister) (modularOrbitLabel D u j) :
          StateVector D.unitRegister) =
      (PureState.ket (R := D.unitRegister)
        (modularOrbitLabel D u (cycleSucc r j)) :
          StateVector D.unitRegister) := by
  rw [ModularMultiplicationDomain.multiplicationCircuit_apply_ket]
  rw [multiplyUnit_modularOrbitLabel_cycleSucc D u horder j]

/-- Raw-vector action of the modular-multiplication gate on an orbit-lifted
vector, evaluated on generated orbit labels. -/
theorem multiplicationGate_applyVec_modularOrbitLiftVec_orbit {N n r : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (horder : orderOf u = r) (psi : StateVector (cycleRegister r))
    (j : Fin r) :
    (D.multiplicationGate u).applyVec (modularOrbitLiftVec D u psi)
        (modularOrbitLabel D u j) =
      psi (cyclePred r j) := by
  rw [ModularMultiplicationDomain.multiplicationGate_applyVec,
    multiplyUnit_inv_modularOrbitLabel_cyclePred D u horder,
    modularOrbitLiftVec_apply_orbit D u horder]

/-- Raw action of the forward cyclic basis shift on coordinate vectors. -/
def cycleForwardShiftVec (r : ℕ) (psi : StateVector (cycleRegister r)) :
    StateVector (cycleRegister r) :=
  WithLp.toLp 2 fun j : Fin r => psi (cyclePred r j)

@[simp]
theorem cycleForwardShiftVec_apply (r : ℕ) (psi : StateVector (cycleRegister r))
    (j : Fin r) :
    cycleForwardShiftVec r psi j = psi (cyclePred r j) :=
  rfl

theorem modularEigenCoefficient_cyclePred (r k : ℕ) (hr : 0 < r) (j : Fin r) :
    modularEigenCoefficient r k (cyclePred r j).val =
      modularEigenphase r k * modularEigenCoefficient r k j.val := by
  rw [modularEigenCoefficient, modularEigenCoefficient, modularEigenphase]
  by_cases hzero : j.val = 0
  · rw [cyclePred_val_zero j hzero, hzero]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hangle :
        -(2 * (Real.pi : ℂ) * ((k : ℂ) * ((r : ℂ) - 1) / (r : ℂ)) * Complex.I) =
          2 * (Real.pi : ℂ) * ((k : ℂ) / (r : ℂ)) * Complex.I +
            -(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
      field_simp [hrC]
      ring
    have hperiod :
        Complex.exp (-(k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I)) = 1 := by
      simpa using Complex.exp_int_mul_two_pi_mul_I (-(k : ℤ))
    rw [Nat.cast_sub (Nat.succ_le_of_lt hr)]
    norm_num
    rw [hangle, Complex.exp_add, hperiod, mul_one]
    ring
  · rw [cyclePred_val_nonzero j hzero]
    have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
    have hjpos : 0 < j.val := Nat.pos_of_ne_zero hzero
    have hangle :
        -(2 * (Real.pi : ℂ) * ((k : ℂ) * ((j.val : ℂ) - 1) / (r : ℂ)) * Complex.I) =
          2 * (Real.pi : ℂ) * ((k : ℂ) / (r : ℂ)) * Complex.I +
            -(2 * (Real.pi : ℂ) * ((k : ℂ) * (j.val : ℂ) / (r : ℂ)) * Complex.I) := by
      field_simp [hrC]
      ring
    rw [Nat.cast_sub (Nat.succ_le_of_lt hjpos)]
    norm_num
    rw [hangle, Complex.exp_add]
    ring

/-- The lifted coordinate eigenvector has the expected eigenvalue action on
generated orbit labels. The statement is intentionally orbit-local; a full
unit-register eigenvector theorem also needs the off-orbit support argument. -/
theorem multiplicationGate_applyVec_modularOrbitLiftEigenstateVec_orbit
    {N n r k : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (hr : 0 < r) (horder : orderOf u = r) (j : Fin r) :
    (D.multiplicationGate u).applyVec
        (modularOrbitLiftVec D u (cycleEigenstateVec r k))
        (modularOrbitLabel D u j) =
      (modularEigenphase r k •
        modularOrbitLiftVec D u (cycleEigenstateVec r k))
        (modularOrbitLabel D u j) := by
  rw [multiplicationGate_applyVec_modularOrbitLiftVec_orbit D u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k *
      modularOrbitLiftVec D u (cycleEigenstateVec r k) (modularOrbitLabel D u j)
  rw [modularOrbitLiftVec_apply_orbit D u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k * modularEigenCoefficient r k j.val
  exact modularEigenCoefficient_cyclePred r k hr j

/-- Full lifted unit-register eigenvector relation for the generated orbit.
The proof combines the orbit-local eigenvalue calculation with the off-orbit
support theorem for the linear lift. -/
theorem multiplicationGate_applyVec_modularOrbitLiftEigenstateVec
    {N n r k : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (hr : 0 < r) (horder : orderOf u = r) :
    (D.multiplicationGate u).applyVec
        (modularOrbitLiftVec D u (cycleEigenstateVec r k)) =
      modularEigenphase r k •
        modularOrbitLiftVec D u (cycleEigenstateVec r k) := by
  apply WithLp.ofLp_injective
  funext x
  by_cases hmem :
      x ∈ (Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u)
  · rcases Finset.mem_image.mp hmem with ⟨j, _hj, rfl⟩
    exact multiplicationGate_applyVec_modularOrbitLiftEigenstateVec_orbit
      D u hr horder j
  · rw [ModularMultiplicationDomain.multiplicationGate_applyVec]
    have hpre :
        D.multiplyUnit u⁻¹ x ∉
          (Finset.univ : Finset (Fin r)).image (modularOrbitLabel D u) :=
      multiplyUnit_inv_notMem_modularOrbitLabel_image_of_notMem D u horder hmem
    rw [modularOrbitLiftVec_apply_not_mem_orbit D u _ hpre]
    change 0 =
      modularEigenphase r k *
        modularOrbitLiftVec D u (cycleEigenstateVec r k) x
    rw [modularOrbitLiftVec_apply_not_mem_orbit D u _ hmem]
    simp

/-- Circuit-level lifted eigenvector relation for modular multiplication on
the generated unit orbit. -/
theorem multiplicationCircuit_apply_modularOrbitLiftEigenstateVec
    {N n r k : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (resources : ResourceProfile) (depth queryDepth : ℕ)
    (hr : 0 < r) (horder : orderOf u = r) :
    Circuit.apply (D.multiplicationCircuit u resources depth queryDepth)
        (modularOrbitLiftVec D u (cycleEigenstateVec r k)) =
      modularEigenphase r k •
        modularOrbitLiftVec D u (cycleEigenstateVec r k) := by
  change (D.multiplicationGate u).applyVec
      (modularOrbitLiftVec D u (cycleEigenstateVec r k)) =
    modularEigenphase r k •
      modularOrbitLiftVec D u (cycleEigenstateVec r k)
  exact multiplicationGate_applyVec_modularOrbitLiftEigenstateVec D u hr horder

theorem cycleForwardShiftVec_eigenstateVec (r k : ℕ) (hr : 0 < r) :
    cycleForwardShiftVec r (cycleEigenstateVec r k) =
      modularEigenphase r k • cycleEigenstateVec r k := by
  apply WithLp.ofLp_injective
  funext j
  change cycleForwardShiftVec r (cycleEigenstateVec r k) j =
    (modularEigenphase r k • cycleEigenstateVec r k) j
  rw [cycleForwardShiftVec_apply, PiLp.smul_apply, cycleEigenstateVec_apply,
    cycleEigenstateVec_apply, smul_eq_mul]
  exact modularEigenCoefficient_cyclePred r k hr j

/-- Positive phase root used to prove finite Fourier orthogonality for a cycle
coordinate. The eigenstate coefficients use powers of this root's inverse. -/
def cyclePhaseRoot (r : ℕ) (j : Fin r) : ℂ :=
  Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ))

theorem cyclePhaseRoot_pow_card (r : ℕ) (hr : 0 < r) (j : Fin r) :
    cyclePhaseRoot r j ^ r = 1 := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  rw [cyclePhaseRoot, ← Complex.exp_nat_mul]
  have hangle :
      (r : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ)) =
        (j.val : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) := by
    field_simp [hrC]
  rw [hangle]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    Complex.exp_nat_mul_two_pi_mul_I j.val

theorem cyclePhaseRoot_ne_one_of_nonzero (r : ℕ) (hr : 0 < r)
    (j : Fin r) (hj : j.val ≠ 0) :
    cyclePhaseRoot r j ≠ 1 := by
  intro hroot
  have hdiv : r ∣ j.val := by
    have hiff := Complex.exp_two_pi_mul_I_mul_div_eq_one_iff
      (k := j.val) (N := r) hr.ne'
    exact hiff.mp (by
      simpa [cyclePhaseRoot, mul_assoc, mul_comm, mul_left_comm] using hroot)
  rcases hdiv with ⟨m, hm⟩
  have hm0 : m = 0 := by
    by_contra hmne
    have hmpos : 0 < m := Nat.pos_of_ne_zero hmne
    have : r ≤ j.val := by
      rw [hm]
      exact Nat.le_mul_of_pos_right r hmpos
    exact not_le_of_gt j.isLt this
  exact hj (by simp [hm, hm0])

theorem cyclePhaseRoot_inv_ne_one_of_nonzero (r : ℕ) (hr : 0 < r)
    (j : Fin r) (hj : j.val ≠ 0) :
    (cyclePhaseRoot r j)⁻¹ ≠ 1 := by
  intro hinv
  exact cyclePhaseRoot_ne_one_of_nonzero r hr j hj (inv_eq_one.mp hinv)

theorem cyclePhaseRoot_inv_pow_card (r : ℕ) (hr : 0 < r) (j : Fin r) :
    (cyclePhaseRoot r j)⁻¹ ^ r = 1 := by
  rw [inv_pow, cyclePhaseRoot_pow_card r hr j, inv_one]

theorem cyclePhaseRoot_inv_pow_eq_coefficient_phase
    (r : ℕ) (_hr : 0 < r) (j k : Fin r) :
    (cyclePhaseRoot r j)⁻¹ ^ k.val =
      Complex.exp (-(2 * Real.pi * ((k.val : ℝ) * j.val / r)) * Complex.I) := by
  rw [cyclePhaseRoot, ← Complex.exp_neg, ← Complex.exp_nat_mul]
  have hangle :
      (k.val : ℂ) * (-(2 * (Real.pi : ℂ) * Complex.I * (j.val : ℂ) / (r : ℂ))) =
        -(2 * (Real.pi : ℂ) * ((k.val : ℂ) * (j.val : ℂ) / (r : ℂ)) * Complex.I) := by
    ring
  rw [hangle]
  congr 1
  push_cast
  ring_nf

theorem sum_cyclePhaseRoot_inv_pow (r : ℕ) (hr : 0 < r) (j : Fin r) :
    ∑ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val =
      if j.val = 0 then (r : ℂ) else 0 := by
  by_cases hj : j.val = 0
  · rw [if_pos hj]
    have hterm : ∀ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val = (1 : ℂ) := by
      intro k
      rw [cyclePhaseRoot, hj]
      norm_num
    simp only [hterm, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, mul_one]
  · rw [if_neg hj]
    rw [Fin.sum_univ_eq_sum_range fun k => (cyclePhaseRoot r j)⁻¹ ^ k]
    have hne : (cyclePhaseRoot r j)⁻¹ ≠ 1 :=
      cyclePhaseRoot_inv_ne_one_of_nonzero r hr j hj
    have hpow : (cyclePhaseRoot r j)⁻¹ ^ r = 1 :=
      cyclePhaseRoot_inv_pow_card r hr j
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

theorem sum_modularEigenCoefficient_over_modes (r : ℕ) (hr : 0 < r) (j : Fin r) :
    ∑ k : Fin r, modularEigenCoefficient r k.val j.val =
      if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0 := by
  calc
    ∑ k : Fin r, modularEigenCoefficient r k.val j.val =
        (Real.sqrt (r : ℝ))⁻¹ *
          ∑ k : Fin r, (cyclePhaseRoot r j)⁻¹ ^ k.val := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [cyclePhaseRoot_inv_pow_eq_coefficient_phase r hr j k, modularEigenCoefficient]
    _ = if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0 := by
      rw [sum_cyclePhaseRoot_inv_pow r hr j]
      by_cases hj : j.val = 0
      · simp only [hj, if_true]
        rw [← Complex.ofReal_natCast, ← Complex.ofReal_mul]
        congr 1
        rw [inv_mul_eq_div, div_eq_iff (Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr))]
        exact (Real.mul_self_sqrt (by positivity : (0 : ℝ) ≤ (r : ℝ))).symm
      · rw [if_neg hj, if_neg hj, mul_zero]

theorem cycleBasisZero_eq_eigenstate_average (r : ℕ) (hr : 0 < r) :
    (PureState.ket (R := cycleRegister r) ⟨0, hr⟩ : StateVector (cycleRegister r)) =
      (Real.sqrt (r : ℝ))⁻¹ • ∑ k : Fin r, cycleEigenstateVec r k := by
  apply WithLp.ofLp_injective
  funext (j : Fin r)
  rw [show (((Real.sqrt (r : ℝ))⁻¹ • ∑ k : Fin r, cycleEigenstateVec r k) :
      StateVector (cycleRegister r)).ofLp j =
        (Real.sqrt (r : ℝ))⁻¹ * (∑ k : Fin r, cycleEigenstateVec r k).ofLp j from rfl]
  rw [show (∑ k : Fin r, cycleEigenstateVec r k).ofLp j =
      ∑ k : Fin r, (cycleEigenstateVec r k).ofLp j by simp]
  change (PureState.ket (R := cycleRegister r) (⟨0, hr⟩ : Fin r) :
      StateVector (cycleRegister r)) (j : Fin r) =
    (Real.sqrt (r : ℝ))⁻¹ *
      ∑ k : Fin r, modularEigenCoefficient r k.val j.val
  rw [sum_modularEigenCoefficient_over_modes r hr j]
  by_cases hj : j.val = 0
  · have hj_eq : j = ⟨0, hr⟩ := Fin.ext hj
    rw [if_pos hj, hj_eq, PureState.ket_apply, if_pos rfl]
    rw [← Complex.ofReal_mul]
    have hsqrt_ne : Real.sqrt (r : ℝ) ≠ 0 :=
      Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
    rw [inv_mul_cancel₀ hsqrt_ne]
    norm_num
  · have hj_ne : j ≠ ⟨0, hr⟩ := fun h => hj (Fin.ext_iff.mp h)
    rw [if_neg hj, PureState.ket_apply, if_neg hj_ne, mul_zero]

/-- Multiplication by the inverse generating unit moves one step backward on
the public residue orbit. -/
theorem residueMultiplication_inv_residueOrbitLabel_cyclePred {N r : ℕ}
    (u : (ZMod N)ˣ) (horder : orderOf u = r) (j : Fin r) :
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * residueOrbitLabel u j =
      residueOrbitLabel u (cyclePred r j) := by
  have hfwd :
      (u : ZMod N) * residueOrbitLabel u (cyclePred r j) =
        residueOrbitLabel u j := by
    rw [residueMultiplication_residueOrbitLabel_cycleSucc u horder,
      cycleSucc_cyclePred]
  calc
    ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * residueOrbitLabel u j =
        ((u⁻¹ : (ZMod N)ˣ) : ZMod N) *
          ((u : ZMod N) * residueOrbitLabel u (cyclePred r j)) := by
            rw [hfwd]
    _ = residueOrbitLabel u (cyclePred r j) := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel]
      simp

/-- Orbit-local residue-register eigenvalue calculation. -/
theorem residueMultiplicationGate_applyVec_residueOrbitLiftEigenstateVec_orbit
    {N r k : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (hr : 0 < r) (horder : orderOf u = r) (j : Fin r) :
    (residueMultiplicationGate u).applyVec
        (residueOrbitLiftVec u (cycleEigenstateVec r k))
        (residueOrbitLabel u j) =
      (modularEigenphase r k •
        residueOrbitLiftVec u (cycleEigenstateVec r k))
        (residueOrbitLabel u j) := by
  rw [residueMultiplicationGate_applyVec]
  rw [residueMultiplication_inv_residueOrbitLabel_cyclePred u horder]
  rw [residueOrbitLiftVec_apply_orbit u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k *
      residueOrbitLiftVec u (cycleEigenstateVec r k) (residueOrbitLabel u j)
  rw [residueOrbitLiftVec_apply_orbit u horder]
  change modularEigenCoefficient r k (cyclePred r j).val =
    modularEigenphase r k * modularEigenCoefficient r k j.val
  exact modularEigenCoefficient_cyclePred r k hr j

/-- Full residue-register lifted eigenvector relation for the generated
orbit. This is the residue-space bridge needed by the public
modular-multiplication eigenstructure statement; it keeps the off-orbit support
explicit rather than weakening the target to the unit carrier. -/
theorem residueMultiplicationGate_applyVec_residueOrbitLiftEigenstateVec
    {N r k : ℕ} [NeZero N] (u : (ZMod N)ˣ)
    (hr : 0 < r) (horder : orderOf u = r) :
    (residueMultiplicationGate u).applyVec
        (residueOrbitLiftVec u (cycleEigenstateVec r k)) =
      modularEigenphase r k •
        residueOrbitLiftVec u (cycleEigenstateVec r k) := by
  apply WithLp.ofLp_injective
  funext (x : ZMod N)
  by_cases hmem :
      (x : ZMod N) ∈ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)
  · rcases Finset.mem_image.mp hmem with ⟨j, _hj, hx⟩
    subst hx
    exact residueMultiplicationGate_applyVec_residueOrbitLiftEigenstateVec_orbit
      u hr horder j
  · rw [residueMultiplicationGate_applyVec]
    have hpre :
        ((u⁻¹ : (ZMod N)ˣ) : ZMod N) * (x : ZMod N) ∉
          (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u) :=
      residueMultiplication_inv_notMem_residueOrbitLabel_image_of_notMem
        u horder hmem
    rw [residueOrbitLiftVec_apply_not_mem_orbit u _ hpre]
    change 0 =
      modularEigenphase r k *
        residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N)
    rw [residueOrbitLiftVec_apply_not_mem_orbit u _ hmem]
    simp

/-- In the public residue register, the source basis state `|1>` is the
uniform average of the lifted Fourier eigenvectors. This is the residue-space
transport of `cycleBasisZero_eq_eigenstate_average`. -/
theorem residueBasisOne_eq_lifted_eigenstate_average {N r : ℕ} [NeZero N]
    (u : (ZMod N)ˣ) (hr : 0 < r) (horder : orderOf u = r) :
    (PureState.ket (R := residueRegister N) (1 : ZMod N) :
      StateVector (residueRegister N)) =
      (Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k) := by
  apply WithLp.ofLp_injective
  funext x
  by_cases hmem :
      (x : ZMod N) ∈ (Finset.univ : Finset (Fin r)).image (residueOrbitLabel u)
  · rcases Finset.mem_image.mp hmem with ⟨j, _hj, hx⟩
    subst hx
    rw [show (((Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k)) :
          StateVector (residueRegister N)).ofLp (residueOrbitLabel u j) =
        (Real.sqrt (r : ℝ))⁻¹ *
          (∑ k : Fin r,
            residueOrbitLiftVec u (cycleEigenstateVec r k)
              (residueOrbitLabel u j)) by
          simp]
    rw [show (∑ k : Fin r,
        residueOrbitLiftVec u (cycleEigenstateVec r k)
          (residueOrbitLabel u j)) =
        ∑ k : Fin r, cycleEigenstateVec r k j by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [residueOrbitLiftVec_apply_orbit u horder]]
    change (PureState.ket (R := residueRegister N) (1 : ZMod N))
        (residueOrbitLabel u j) =
      (Real.sqrt (r : ℝ))⁻¹ *
        ∑ k : Fin r, modularEigenCoefficient r k.val j.val
    rw [PureState.ket_apply, sum_modularEigenCoefficient_over_modes r hr j]
    change (if (residueOrbitLabel u j : ZMod N) = (1 : ZMod N) then (1 : ℂ) else 0) =
      (Real.sqrt (r : ℝ))⁻¹ * if j.val = 0 then (Real.sqrt (r : ℝ) : ℂ) else 0
    by_cases hj : j.val = 0
    · have hj_eq : j = ⟨0, hr⟩ := Fin.ext hj
      have hlabel : residueOrbitLabel u j = (1 : ZMod N) := by
        rw [hj_eq]
        simp [residueOrbitLabel]
      rw [if_pos hlabel, if_pos hj]
      rw [← Complex.ofReal_mul]
      have hsqrt_ne : Real.sqrt (r : ℝ) ≠ 0 :=
        Real.sqrt_ne_zero'.mpr (by exact_mod_cast hr)
      rw [inv_mul_cancel₀ hsqrt_ne]
      norm_num
    · have hlabel : residueOrbitLabel u j ≠ (1 : ZMod N) := by
        intro h
        have hzero :
            residueOrbitLabel u (⟨0, hr⟩ : Fin r) = (1 : ZMod N) := by
          simp [residueOrbitLabel]
        have hsame :
            residueOrbitLabel u j =
              residueOrbitLabel u (⟨0, hr⟩ : Fin r) := by
          rw [h, hzero]
        have hj0 := (residueOrbitLabel_injective_of_order u horder) hsame
        exact hj (Fin.ext_iff.mp hj0)
      rw [if_neg hlabel, if_neg hj, mul_zero]
  · rw [PureState.ket_apply]
    have hx_ne : x ≠ (1 : ZMod N) := by
      intro hx
      apply hmem
      refine Finset.mem_image.mpr ⟨⟨0, hr⟩, Finset.mem_univ _, ?_⟩
      change residueOrbitLabel u (⟨0, hr⟩ : Fin r) = (x : ZMod N)
      rw [hx]
      simp [residueOrbitLabel]
    rw [if_neg hx_ne]
    rw [show (((Real.sqrt (r : ℝ))⁻¹ •
        ∑ k : Fin r, residueOrbitLiftVec u (cycleEigenstateVec r k)) :
          StateVector (residueRegister N)).ofLp x =
        (Real.sqrt (r : ℝ))⁻¹ *
          (∑ k : Fin r,
            residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N)) by
          simp]
    change 0 = (Real.sqrt (r : ℝ))⁻¹ *
      (∑ k : Fin r,
        residueOrbitLiftVec u (cycleEigenstateVec r k) (x : ZMod N))
    rw [Finset.sum_eq_zero]
    · simp
    · intro k _hk
      exact residueOrbitLiftVec_apply_not_mem_orbit u _ hmem

/-- Residue-register modular-multiplication eigenstructure package matching
the accepted public theorem shape. The statement exposes the source-facing
residue gate, the lifted residue eigenvectors, and the transport of the first
orbit basis state from the cycle register to `|1>`. -/
structure ResidueRegisterEigenstructure {N : ℕ} [NeZero N]
    (a : ℕ) (ha : Nat.Coprime a N) (r : ℕ) : Prop where
  order_pos : 0 < r
  order_eq : orderOf (ZMod.unitOfCoprime a ha) = r
  basisAction :
    ∀ j : Fin r,
      (residueMultiplicationGate (ZMod.unitOfCoprime a ha)).apply
          (PureState.ket (R := residueRegister N)
            (residueOrbitLabel (ZMod.unitOfCoprime a ha) j)) =
        PureState.ket (R := residueRegister N)
          (residueOrbitLabel (ZMod.unitOfCoprime a ha) (cycleSucc r j))
  liftedEigenvectorRelation :
    ∀ k : ℕ,
      (residueMultiplicationGate (ZMod.unitOfCoprime a ha)).applyVec
          (residueOrbitLiftVec (ZMod.unitOfCoprime a ha)
            (cycleEigenstateVec r k)) =
        modularEigenphase r k •
          residueOrbitLiftVec (ZMod.unitOfCoprime a ha)
            (cycleEigenstateVec r k)
  basisOneLabel_eq :
    residueOrbitLabel (ZMod.unitOfCoprime a ha) ⟨0, order_pos⟩ = (1 : ZMod N)
  residueBasisOneDecomposition :
    (PureState.ket (R := residueRegister N) (1 : ZMod N) :
      StateVector (residueRegister N)) =
      (Real.sqrt (r : ℝ))⁻¹ •
        ∑ mode : Fin r,
          residueOrbitLiftVec (ZMod.unitOfCoprime a ha)
            (cycleEigenstateVec r mode)
  cycleBasisZeroDecomposition :
    (PureState.ket (R := cycleRegister r) ⟨0, order_pos⟩ :
      StateVector (cycleRegister r)) =
      (Real.sqrt (r : ℝ))⁻¹ • ∑ mode : Fin r, cycleEigenstateVec r mode

/-- Bridge from a natural coprime base to the residue-register public
eigenstructure shape. -/
theorem ResidueRegisterEigenstructure.main {N a r : ℕ} [NeZero N]
    (ha : Nat.Coprime a N) (hr : 0 < r)
    (horder : orderOf (ZMod.unitOfCoprime a ha) = r) :
    ResidueRegisterEigenstructure a ha r where
  order_pos := hr
  order_eq := horder
  basisAction := by
    intro j
    rw [residueMultiplicationGate_apply_ket]
    rw [residueMultiplication_residueOrbitLabel_cycleSucc
      (ZMod.unitOfCoprime a ha) horder]
  liftedEigenvectorRelation := by
    intro k
    exact residueMultiplicationGate_applyVec_residueOrbitLiftEigenstateVec
      (ZMod.unitOfCoprime a ha) hr horder
  basisOneLabel_eq := by
    simp [residueOrbitLabel]
  residueBasisOneDecomposition :=
    residueBasisOne_eq_lifted_eigenstate_average
      (ZMod.unitOfCoprime a ha) hr horder
  cycleBasisZeroDecomposition :=
    cycleBasisZero_eq_eigenstate_average r hr

/-- Modular-multiplication eigenstructure package for one generated orbit. The
first component connects the actual modular-multiplication gate to the orbit
labels `u^j`; the second gives the Fourier eigenvector relation on the orbit
coordinate register; the third is the source-facing decomposition of the first
orbit basis state as the uniform average over Fourier modes. -/
private theorem modularMultiplication_eigenstructure_support {N n r k : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (hr : 0 < r) (horder : orderOf u = r) :
    (∀ j : Fin r,
      (D.multiplicationGate u).apply
          (PureState.ket (R := D.unitRegister) (modularOrbitLabel D u j)) =
        PureState.ket (R := D.unitRegister)
          (modularOrbitLabel D u (cycleSucc r j))) ∧
      cycleForwardShiftVec r (cycleEigenstateVec r k) =
        modularEigenphase r k • cycleEigenstateVec r k ∧
      (PureState.ket (R := cycleRegister r) ⟨0, hr⟩ : StateVector (cycleRegister r)) =
        (Real.sqrt (r : ℝ))⁻¹ • ∑ mode : Fin r, cycleEigenstateVec r mode := by
  constructor
  · intro j
    exact multiplicationGate_apply_modularOrbitKet D u horder j
  constructor
  · exact cycleForwardShiftVec_eigenstateVec r k hr
  · exact cycleBasisZero_eq_eigenstate_average r hr

/-- Circuit-shaped modular-multiplication eigenstructure support for one
generated orbit. This is the same source-facing eigenstructure as the gate
theorem, with resource counters attached to the typed `Circuit` wrapper. -/
private theorem modularMultiplication_circuit_eigenstructure_support {N n r k : ℕ}
    (D : ModularMultiplicationDomain N n) (u : D.UnitCarrier)
    (resources : ResourceProfile) (depth queryDepth : ℕ)
    (hr : 0 < r) (horder : orderOf u = r) :
    (∀ j : Fin r,
      Circuit.apply (D.multiplicationCircuit u resources depth queryDepth)
          (PureState.ket (R := D.unitRegister)
            (modularOrbitLabel D u j) : StateVector D.unitRegister) =
        (PureState.ket (R := D.unitRegister)
          (modularOrbitLabel D u (cycleSucc r j)) :
            StateVector D.unitRegister)) ∧
      Circuit.apply (D.multiplicationCircuit u resources depth queryDepth)
          (modularOrbitLiftVec D u (cycleEigenstateVec r k)) =
        modularEigenphase r k •
          modularOrbitLiftVec D u (cycleEigenstateVec r k) ∧
      (D.multiplicationCircuit u resources depth queryDepth).resources = resources ∧
      (D.multiplicationCircuit u resources depth queryDepth).depth = depth ∧
      (D.multiplicationCircuit u resources depth queryDepth).queryDepth = queryDepth := by
  constructor
  · intro j
    exact multiplicationCircuit_apply_modularOrbitKet
      D u resources depth queryDepth horder j
  constructor
  · exact multiplicationCircuit_apply_modularOrbitLiftEigenstateVec
      D u resources depth queryDepth hr horder
  constructor
  · rfl
  constructor
  · rfl
  · rfl

/-- Source-facing modular-multiplication eigenstructure support. The base is
given as a natural number coprime to the modulus, then promoted to the selected
unit-group carrier. The statement exposes the gate action on orbit basis labels,
the Fourier eigenvector relation on the generated cycle, and the decomposition
of the first orbit basis state into Fourier modes. -/
structure ModularMultiplicationEigenstructure {N n : ℕ}
    (D : ModularMultiplicationDomain N n) (a : ℕ)
    (ha : Nat.Coprime a N) (r : ℕ) : Prop where
  order_pos : 0 < r
  order_eq : orderOf (D.unitOfCoprime a ha) = r
  eigenvalueSign_eq : modularEigenstateConvention.eigenvalueSign = .positive
  coefficientSign_eq : modularEigenstateConvention.coefficientSign = .negative
  normalizedBySqrtOrder_eq :
    modularEigenstateConvention.normalizedBySqrtOrder = true
  basisAction :
    ∀ j : Fin r,
      (D.multiplicationGate (D.unitOfCoprime a ha)).apply
          (PureState.ket (R := D.unitRegister)
            (modularOrbitLabel D (D.unitOfCoprime a ha) j)) =
        PureState.ket (R := D.unitRegister)
          (modularOrbitLabel D (D.unitOfCoprime a ha) (cycleSucc r j))
  eigenvectorRelation :
    ∀ k : ℕ,
      cycleForwardShiftVec r (cycleEigenstateVec r k) =
        modularEigenphase r k • cycleEigenstateVec r k
  basisZeroDecomposition :
    (PureState.ket (R := cycleRegister r) ⟨0, order_pos⟩ : StateVector (cycleRegister r)) =
      (Real.sqrt (r : ℝ))⁻¹ • ∑ mode : Fin r, cycleEigenstateVec r mode

/-- Source-facing wrapper for modular-multiplication eigenstructure from a
natural coprime base. -/
private theorem modularMultiplication_eigenstructure {N n a r : ℕ}
    (D : ModularMultiplicationDomain N n) (ha : Nat.Coprime a N)
    (hr : 0 < r) (horder : orderOf (D.unitOfCoprime a ha) = r) :
    ModularMultiplicationEigenstructure D a ha r where
  order_pos := hr
  order_eq := horder
  eigenvalueSign_eq := rfl
  coefficientSign_eq := rfl
  normalizedBySqrtOrder_eq := rfl
  basisAction := by
    intro j
    exact multiplicationGate_apply_modularOrbitKet D (D.unitOfCoprime a ha) horder j
  eigenvectorRelation := by
    intro k
    exact cycleForwardShiftVec_eigenstateVec r k hr
  basisZeroDecomposition := cycleBasisZero_eq_eigenstate_average r hr

end OrderFinding

namespace OrderFinding

/-- Full unit-register lifted eigenvector relation exposed through the
source-facing modular-multiplication eigenstructure wrapper. -/
def ModularMultiplicationEigenstructure.liftedEigenvectorRelation
    {N n : ℕ} {D : ModularMultiplicationDomain N n} {a r : ℕ}
    {ha : Nat.Coprime a N}
    (support : ModularMultiplicationEigenstructure D a ha r) : Prop :=
  let _h : 0 < r := support.order_pos
  ∀ k : ℕ,
    (D.multiplicationGate (D.unitOfCoprime a ha)).applyVec
        (modularOrbitLiftVec D (D.unitOfCoprime a ha)
          (cycleEigenstateVec r k)) =
      modularEigenphase r k •
        modularOrbitLiftVec D (D.unitOfCoprime a ha)
          (cycleEigenstateVec r k)

namespace ModularMultiplicationEigenstructure

/-- The source-facing support package entails the full lifted unit-register
eigenvector relation, not only the coordinate-cycle relation. -/
private theorem liftedEigenvectorRelation_of_support
    {N n : ℕ} {D : ModularMultiplicationDomain N n} {a r : ℕ}
    {ha : Nat.Coprime a N}
    (support : ModularMultiplicationEigenstructure D a ha r) :
    support.liftedEigenvectorRelation := by
  intro k
  exact multiplicationGate_applyVec_modularOrbitLiftEigenstateVec
    D (D.unitOfCoprime a ha) support.order_pos support.order_eq

end ModularMultiplicationEigenstructure

end OrderFinding

/-! ### Exact order finding via phase estimation -/

namespace OrderFinding

/-- Exact order finding through the decoupled QPE interface. The inverse-QFT
readout is stated at the raw-vector layer because the phase superposition is a
linear combination before it is packaged as a `PureState`. -/
theorem main_exact_dyadic {t s r : ℕ} (hr : 0 < r) (hrt : r ∣ 2 ^ t)
    (hsr : Nat.Coprime s r) (j : Fin (2 ^ t))
    (hj : j.val = s * (2 ^ t / r)) :
    (invQFT t).applyVec (phaseState t ((s : ℝ) / r))
      = (PureState.ket (R := Qubits t) j : StateVector (Qubits t))
      ∧ 2 ^ t / Nat.gcd j.val (2 ^ t) = r := by
  refine ⟨?_, ?_⟩
  · apply QuantumPhaseEstimation.main_exact_dyadic
    rw [hj]
    have hr0 : (r : ℝ) ≠ 0 := by exact_mod_cast hr.ne'
    have h2t0 : (2 : ℝ) ^ t ≠ 0 := by positivity
    have hrr : (r : ℝ) * ((2 ^ t / r : ℕ) : ℝ) = (2 : ℝ) ^ t := by
      exact_mod_cast Nat.mul_div_cancel' hrt
    rw [div_eq_div_iff hr0 h2t0]
    push_cast
    rw [← hrr]
    ring
  · rw [hj]
    exact main_recovery hr hrt hsr

/-- The general-order eigenphase has the same positive-sign convention as the
modular-multiplication eigenstate phase. -/
private theorem generalOrderEigenphase_matches_modularEigenphase (s r : ℕ) :
    Complex.exp (2 * Real.pi * generalOrderEigenphase s r * Complex.I) =
      modularEigenphase r s := by
  simp [generalOrderEigenphase, modularEigenphase]


end OrderFinding

namespace OrderFinding

/-- Trusted decoupled resource profile for exact order finding: one modular-
exponentiation oracle call feeding an inverse-QFT/readout layer. -/
def orderFindingExactResourceProfile (t : ℕ) : ResourceProfile where
  oracleQueries := 1
  hadamardGates := t
  elementaryGates := t ^ 2
  classicalOps := 1

/-- Resource profile for the inverse-QFT/readout and classical post-processing
boundary after the modular-exponentiation oracle call. -/
def orderFindingFourierReadoutResourceProfile (t : ℕ) : ResourceProfile where
  oracleQueries := 0
  hadamardGates := t
  elementaryGates := t ^ 2
  classicalOps := 1

/-- Named QFT-layer gate families for the black-box order-finding theorem. -/
def orderFindingFourierGateProfile (t : ℕ) : CircuitGateProfile where
  hadamardGates := t
  controlledPhaseGates := t * (t - 1) / 2
  swapGates := t / 2

theorem orderFindingExactResourceProfile_exact (t : ℕ) :
    ResourceProfile.HasExactCounts
      (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  simp [ResourceProfile.HasExactCounts, orderFindingExactResourceProfile]

/-- Exact coarse counts for the Fourier/readout boundary once the oracle query
has already been charged. -/
private theorem orderFindingFourierReadoutResourceProfile_exact (t : ℕ) :
    ResourceProfile.HasExactCounts
      (orderFindingFourierReadoutResourceProfile t) 0 t (t ^ 2) 1 := by
  simp [ResourceProfile.HasExactCounts, orderFindingFourierReadoutResourceProfile]

/-- Exact named-gate count for the inverse-QFT/readout layer used by
order finding. -/
theorem orderFindingFourierGateProfile_exact (t : ℕ) :
    CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
      t (t * (t - 1) / 2) (t / 2) :=
  ⟨rfl, rfl, rfl⟩

/-- General-order order-finding bridge with explicit success and resource
certificates. This is the integration point for the measurement distribution,
continued-fraction recovery, and black-box oracle resource profile; the
source-specific analytic lower bound is supplied as the certificate's
`successLowerBound_le_goodMass` field. -/
private theorem generalOrder_run_with_resource_certificates {t s r : ℕ}
    (hr : 0 < r) (cert : GeneralOrderRunCertificate t s r) :
    (∃ n,
      (s : ℚ) / (r : ℚ) =
        (((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
      ((((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r)) ∧
      cert.successLowerBound ≤ goodPhaseRegisterOutcomeMass t s r ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · exact cert.denominatorRecovery hr
  constructor
  · exact cert.successLowerBound_le_goodMass
  constructor
  · exact orderFindingExactResourceProfile_exact t
  · exact orderFindingFourierGateProfile_exact t

/-- Shor source joint-event order-finding bridge with the public coarse
resource profile. This is the public-facing source-joint integration layer:
the source certificate supplies one recoverable phase event for every coprime
numerator and the aggregate order-recovery success lower bound. -/
theorem shorSourceJoint_run_with_resource_certificates {t r : ℕ}
    (hr : 0 < r) (cert : ShorSourceJointEventMapCertificate t r) :
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
        (((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r, cert.prob outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · intro d hd
    have hcop : Nat.Coprime d.val r := by
      have hd' : r.Coprime d.val := by
        simpa [shorRecoverableFractionIndices] using hd
      simpa [Nat.coprime_comm] using hd'
    exact goodPhaseRegisterOutcome_denominatorRecovery hr hcop (cert.good d hd)
  constructor
  · exact cert.successLowerBound_le_totalMass hr
  constructor
  · exact orderFindingExactResourceProfile_exact t
  · exact orderFindingFourierGateProfile_exact t

/-- Shor source joint-event order-finding bridge over the actual recoverable
event set. This is stronger than the older total-mass corollary: every event in
the certified recoverable set has a continued-fraction denominator equal to the
true order, and Shor's source lower bound is charged to that recoverable-event
mass rather than to all measurement outcomes. -/
theorem shorSourceJoint_run_with_recoverable_event_resource_certificates {t r : ℕ}
    (hr : 0 < r) (cert : ShorSourceJointEventMapCertificate t r) :
    (∀ outcome,
      outcome ∈ shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)) ∧
            (((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents (t := t) (r := r) cert.eventOf).sum
          cert.prob ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · intro outcome houtcome
    rcases Finset.mem_image.mp houtcome with ⟨idx, hidx, houtcome_eq⟩
    rcases idx with ⟨k, d⟩
    have hd : d ∈ shorRecoverableFractionIndices r := by
      simpa [shorRecoverableStateIndices] using hidx
    cases houtcome_eq
    refine ⟨d, hd, ?_⟩
    have hcop : Nat.Coprime d.val r := by
      have hd' : r.Coprime d.val := by
        simpa [shorRecoverableFractionIndices] using hd
      simpa [Nat.coprime_comm] using hd'
    exact goodPhaseRegisterOutcome_denominatorRecovery hr hcop (cert.good d hd)
  constructor
  · exact cert.successLowerBound_le_recoverableMass hr
  constructor
  · exact orderFindingExactResourceProfile_exact t
  · exact orderFindingFourierGateProfile_exact t

open ShorSourceJointEventMapCertificate in
/-- Direct Shor source joint-event order-finding theorem from the rounded
nearest-fraction construction and the finite geometric/sine lower bound. -/
theorem shorSourceJoint_run_with_scaled_error_resource_certificates {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hr hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hr hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  let cert := ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError
    hr hq hlarge
  simpa [cert,
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError,
    ofSourceJointProbabilityRoundedNearestFractionEvents,
    ofSourceJointProbabilityInferInjectivity,
    ofSourceJointProbability] using
      shorSourceJoint_run_with_resource_certificates hr cert

open ShorSourceJointEventMapCertificate in
/-- Direct Shor source joint-event order-finding theorem from the rounded
nearest-fraction construction, with success charged to the recoverable event
set. This is the concrete-source version of
`shorSourceJoint_run_with_recoverable_event_resource_certificates`
[Sho95, source.tex:1183-1185]. -/
theorem shorSourceJoint_run_with_scaled_error_recoverable_event_resource_success
    {t r : ℕ} (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    (∀ outcome,
      outcome ∈
          shorSourceJointRecoverableEvents
            (t := t) (r := r) (shorNearestFractionEvent hr hq) →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)) ∧
            (((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents
            (t := t) (r := r) (shorNearestFractionEvent hr hq)).sum
          (shorSourceJointProbability t r) ∧
      ResourceProfile.HasExactCounts
        (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  let cert :=
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError hr hq hlarge
  simpa [cert,
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError,
    ofSourceJointProbabilityRoundedNearestFractionEvents,
    ofSourceJointProbabilityInferInjectivity,
    ofSourceJointProbability] using
      shorSourceJoint_run_with_recoverable_event_resource_certificates hr cert

/-- Direct Shor source joint-event order-finding theorem from public register
bounds. The usual lower bound `N^2 <= 2^t` supplies the scaled-error premise
because the source order is strictly smaller than the modulus. The finite
source-distribution lower bound additionally needs `12N <= 2^t`; the older
upper bound `2^t < 2N^2` does not imply it for small moduli. -/
private theorem shorSourceJoint_run_with_public_register_resource_certificates
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hlargeRegister : 12 * N ≤ 2 ^ t) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  have hlarge : 12 * r ≤ 2 ^ t :=
    largeRegister_of_order_le_modulus
      (le_of_lt (input_order_lt_modulus hinput)) hlargeRegister
  simpa [hq] using
    shorSourceJoint_run_with_scaled_error_resource_certificates
      hinput.order_pos hq hlarge

/-- Direct Shor source joint-event order-finding theorem from the restored
public register lower bound, in the large-modulus branch. When `12 <= N`, the
public lower bound `N^2 <= 2^t` already implies the finite large-register
hypothesis used by the current source-joint probability proof
[Sho95, source.tex:1183-1185]. -/
theorem shorSourceJoint_run_with_public_register_large_modulus_resource_certificates
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hN : 12 ≤ N)
    (hregister : N ^ 2 ≤ 2 ^ t) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t)
        1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  have hlarge : 12 * r ≤ 2 ^ t :=
    largeRegister_of_publicRegisterBound_of_modulus_ge_twelve
      hN (input_order_lt_modulus hinput) hregister
  simpa [hq] using
    shorSourceJoint_run_with_scaled_error_resource_certificates
      hinput.order_pos hq hlarge

open ShorSourceJointEventMapCertificate in
/-- Direct Shor source joint-event order-finding theorem from the restored
public register window, in the finite small-modulus branch. The residual cases
left after the large-register route are discharged by explicit quotient-length
bounds for the rounded nearest-fraction source events
[Sho95, source.tex:1183-1185]. -/
theorem shorSourceJoint_run_with_public_register_small_modulus_resource_certificates
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hN : N < 12)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t)
        1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  rcases smallModulus_publicRegisterWindow_large_or_possibleResidual
      hinput hN hregister hupper with hlarge | hres
  · simpa [hq] using
      shorSourceJoint_run_with_scaled_error_resource_certificates
        hinput.order_pos hq hlarge
  · have hbounds :
        ∀ idx, idx ∈ shorRecoverableStateIndices r →
          (11 / 12 : ℝ) ≤
              (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
                (2 : ℝ) ^ t ∧
            (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) * (r : ℝ)) /
                (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) := by
      intro idx _hidx
      rcases idx with ⟨k, _d⟩
      rcases hres with h2 | hres
      · rcases h2 with ⟨hN2, ht, hr⟩
        subst N
        subst t
        subst r
        fin_cases k
        norm_num
      rcases hres with h3 | hres
      · rcases h3 with ⟨hN3, ht, hr⟩
        subst N
        subst t
        subst r
        fin_cases k <;> norm_num
      rcases hres with h4 | hres
      · rcases h4 with ⟨hN4, ht, hr⟩
        subst N
        subst t
        subst r
        fin_cases k <;> norm_num
      rcases hres with h5 | h7
      · rcases h5 with ⟨hN5, ht, hr⟩
        subst N
        subst t
        subst r
        fin_cases k <;> norm_num
      · rcases h7 with ⟨hN7, ht, hr⟩
        subst N
        subst t
        subst r
        fin_cases k <;> norm_num
    let cert : ShorSourceJointEventMapCertificate t r :=
      ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds
        hinput.order_pos hq hbounds
    simpa [hq, cert,
      ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds,
      ofSourceJointProbabilityRoundedNearestFractionEvents,
      ofSourceJointProbabilityInferInjectivity,
      ofSourceJointProbability] using
        shorSourceJoint_run_with_resource_certificates hinput.order_pos cert

/-- Direct Shor source joint-event order-finding theorem from the restored
public register window `N^2 <= 2^t < 2N^2`. The large-modulus branch uses the
usual `12N <= 2^t` consequence; the small-modulus branch is a finite residual
check against the same Shor source probability route
[Sho95, source.tex:1183-1185]. -/
theorem shorSourceJoint_run_with_restored_public_register_resource_certificates
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      ResourceProfile.HasExactCounts (orderFindingExactResourceProfile t)
        1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  by_cases hN : 12 ≤ N
  · simpa using
      shorSourceJoint_run_with_public_register_large_modulus_resource_certificates
        hinput hN hregister
  · have hNlt : N < 12 := Nat.lt_of_not_ge hN
    simpa using
      shorSourceJoint_run_with_public_register_small_modulus_resource_certificates
        hinput hNlt hregister hupper

open ShorSourceJointEventMapCertificate in
/-- Direct Shor source joint-event order-finding theorem from the restored
public register window, with success charged to the recoverable events that
classical continued-fraction post-processing maps to the true order
[Sho95, source.tex:1183-1185, source.tex:1614-1633]. -/
theorem shorSourceJoint_run_with_restored_public_register_recoverable_event_resource_success
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    (∀ outcome,
      outcome ∈
          shorSourceJointRecoverableEvents
            (t := t) (r := r) (shorNearestFractionEvent hinput.order_pos hq) →
        ∃ d, d ∈ shorRecoverableFractionIndices r ∧
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)) ∧
            (((((outcome.1.val : ℝ) / (2 : ℝ) ^ t).convergent n)).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorSourceJointRecoverableEvents
            (t := t) (r := r) (shorNearestFractionEvent hinput.order_pos hq)).sum
          (shorSourceJointProbability t r) ∧
      ResourceProfile.HasExactCounts
        (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  by_cases hN : 12 ≤ N
  · have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister
    have hlarge : 12 * r ≤ 2 ^ t :=
      largeRegister_of_publicRegisterBound_of_modulus_ge_twelve
        hN (input_order_lt_modulus hinput) hregister
    simpa [hq] using
      shorSourceJoint_run_with_scaled_error_recoverable_event_resource_success
        hinput.order_pos hq hlarge
  · have hNlt : N < 12 := Nat.lt_of_not_ge hN
    have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister
    rcases smallModulus_publicRegisterWindow_large_or_possibleResidual
        hinput hNlt hregister hupper with hlarge | hres
    · simpa [hq] using
        shorSourceJoint_run_with_scaled_error_recoverable_event_resource_success
          hinput.order_pos hq hlarge
    · have hbounds :
          ∀ idx, idx ∈ shorRecoverableStateIndices r →
            (11 / 12 : ℝ) ≤
                (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) *
                    (r : ℝ)) /
                  (2 : ℝ) ^ t ∧
              (((((2 ^ t - 1 - idx.1.val) / r) + 1 : ℕ) : ℝ) *
                    (r : ℝ)) /
                  (2 : ℝ) ^ t ≤ (13 / 12 : ℝ) := by
        intro idx _hidx
        rcases idx with ⟨k, _d⟩
        rcases hres with h2 | hres
        · rcases h2 with ⟨hN2, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k
          norm_num
        rcases hres with h3 | hres
        · rcases h3 with ⟨hN3, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        rcases hres with h4 | hres
        · rcases h4 with ⟨hN4, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        rcases hres with h5 | h7
        · rcases h5 with ⟨hN5, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
        · rcases h7 with ⟨hN7, ht, hr⟩
          subst N
          subst t
          subst r
          fin_cases k <;> norm_num
      let cert : ShorSourceJointEventMapCertificate t r :=
        ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds
          hinput.order_pos hq hbounds
      simpa [hq, cert,
        ofSourceJointProbabilityRoundedNearestFractionEventsOfQuotientBounds,
        ofSourceJointProbabilityRoundedNearestFractionEvents,
        ofSourceJointProbabilityInferInjectivity,
        ofSourceJointProbability] using
          shorSourceJoint_run_with_recoverable_event_resource_certificates
            hinput.order_pos cert

/-- Direct order-finding public-output theorem from the restored public register
window. The success lower bound is stated for the validated classical output
event, not merely for the recoverable source-event set
[Sho95, source.tex:1183-1185, source.tex:1614-1633]. -/
theorem ShorSourceJoint.main
    {N x t r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hupper : 2 ^ t < 2 * N ^ 2) :
    orderFindingOutputSuccessLowerBound r ≤
        orderFindingOutputSuccessMass
          (ZMod.unitOfCoprime x hinput.coprime)
          (orderFindingPublicOutcomeProbability t r) ∧
      ResourceProfile.HasExactCounts
        (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 ∧
      CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
        t (t * (t - 1) / 2) (t / 2) := by
  have hsupport :=
    shorSourceJoint_run_with_restored_public_register_recoverable_event_resource_success
      hinput hregister hupper
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  rcases hsupport with ⟨hcf_full, hmass, hresources, hgates⟩
  refine ⟨?_, hresources, hgates⟩
  refine
    shorOrderRecoverySuccessLowerBound_le_outputSuccessMass_of_recoverableEvents
      (eventOf := shorNearestFractionEvent hinput.order_pos hq)
      (prob := orderFindingPublicOutcomeProbability t r) ?_ hinput.order_pos
      (orderOf_zmodUnitOfCoprime_eq_input_order hinput) hmass ?_
  · intro outcome houtcome
    rcases hcf_full outcome houtcome with ⟨_d, _hd, hden⟩
    rcases hden with ⟨n, _hfrac, hden_eq⟩
    exact ⟨n, hden_eq⟩
  · intro outcome
    exact orderFindingPublicOutcomeProbability_nonneg t r outcome

/-- General-order order-finding bridge with the private exact-resource profile.
This strengthens the older coarse resource endpoint by exposing logical
footprint, QFT gate families, circuit depth, and structured classical
post-processing as concrete natural-number fields. -/
private theorem generalOrder_run_with_private_exact_resource_certificates {t s r : ℕ}
    (hr : 0 < r) (cert : GeneralOrderRunCertificate t s r)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t) :
    (∃ n,
      (s : ℚ) / (r : ℚ) =
        (((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
      ((((cert.sample.val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r)) ∧
      cert.successLowerBound ≤ goodPhaseRegisterOutcomeMass t s r ∧
      Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (t + params.oracleRegisterQubits)
        t
        (t * (t - 1) / 2)
        (t / 2)
        (params.oracleDepth + params.fourierReadoutDepth)
        params.classicalPostProcessing.total ∧
      CircuitGateProfile.HasExactCounts params.fourierGateProfile
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · exact cert.denominatorRecovery hr
  constructor
  · exact cert.successLowerBound_le_goodMass
  constructor
  · simpa [hphase] using
      Resource.ResourceParameters.toExactResourceProfile_hasExactCounts params
  · simpa [hphase] using Resource.ResourceParameters.fourierGateProfile_exact params

/-- Shor source joint-event bridge with private exact-resource counts. This
version keeps the analytic source distribution at the joint phase/orbit level,
so a source proof of the joint pointwise lower bound can feed denominator
recovery and aggregate success accounting without first proving a marginal
comparison against the fixed-eigenphase good-outcome mass. -/
theorem shorSourceJoint_run_with_private_exact_resource_certificates {t r : ℕ}
    (hr : 0 < r) (cert : ShorSourceJointEventMapCertificate t r)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t) :
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
        (((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r, cert.prob outcome ∧
      Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (t + params.oracleRegisterQubits)
        t
        (t * (t - 1) / 2)
        (t / 2)
        (params.oracleDepth + params.fourierReadoutDepth)
        params.classicalPostProcessing.total ∧
      CircuitGateProfile.HasExactCounts params.fourierGateProfile
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · intro d hd
    have hcop : Nat.Coprime d.val r := by
      have hd' : r.Coprime d.val := by
        simpa [shorRecoverableFractionIndices] using hd
      simpa [Nat.coprime_comm] using hd'
    exact goodPhaseRegisterOutcome_denominatorRecovery hr hcop (cert.good d hd)
  constructor
  · exact cert.successLowerBound_le_totalMass hr
  constructor
  · simpa [hphase] using
      Resource.ResourceParameters.toExactResourceProfile_hasExactCounts params
  · simpa [hphase] using Resource.ResourceParameters.fourierGateProfile_exact params

open ShorSourceJointEventMapCertificate in
/-- Direct Shor source joint-event bridge with private exact-resource counts.
This specializes `shorSourceJoint_run_with_private_exact_resource_certificates`
to the rounded nearest-fraction source certificate produced by the finite
geometric/sine lower bound. -/
private theorem shorSourceJoint_run_with_scaled_error_private_exact_resource_certificates {t r : ℕ}
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t) :
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((shorNearestFractionEvent hr hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n) ∧
        (((((shorNearestFractionEvent hr hq d).val : ℝ) /
            (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        ∑ outcome : ShorSourceJointOutcome t r,
          shorSourceJointProbability t r outcome ∧
      Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (t + params.oracleRegisterQubits)
        t
        (t * (t - 1) / 2)
        (t / 2)
        (params.oracleDepth + params.fourierReadoutDepth)
        params.classicalPostProcessing.total ∧
      CircuitGateProfile.HasExactCounts params.fourierGateProfile
        t (t * (t - 1) / 2) (t / 2) := by
  let cert := ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError
    hr hq hlarge
  simpa [cert,
    ofSourceJointProbabilityRoundedNearestFractionEventsOfScaledError,
    ofSourceJointProbabilityRoundedNearestFractionEvents,
    ofSourceJointProbabilityInferInjectivity,
    ofSourceJointProbability] using
      shorSourceJoint_run_with_private_exact_resource_certificates hr cert params hphase

/-- Shor source phase-mass bridge with private exact-resource counts. The
analytic source certificate supplies one recoverable phase event for every
coprime numerator; this wrapper exposes denominator recovery for each such
numerator and the aggregate order-recovery success lower bound. -/
private theorem shorSourcePhaseMass_run_with_private_exact_resource_certificates {t r : ℕ}
    (hr : 0 < r) (cert : ShorSourcePhaseMassCertificate t r)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t) :
    (∀ d, d ∈ shorRecoverableFractionIndices r →
      ∃ n,
        (d.val : ℚ) / (r : ℚ) =
          ((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n) ∧
        (((((cert.eventOf d).val : ℝ) / (2 : ℝ) ^ t).convergent n).den = r)) ∧
      shorOrderRecoverySuccessLowerBound r ≤
        (shorRecoverableFractionIndices r).sum
          (fun d => goodPhaseRegisterOutcomeMass t d.val r) ∧
      Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (t + params.oracleRegisterQubits)
        t
        (t * (t - 1) / 2)
        (t / 2)
        (params.oracleDepth + params.fourierReadoutDepth)
        params.classicalPostProcessing.total ∧
      CircuitGateProfile.HasExactCounts params.fourierGateProfile
        t (t * (t - 1) / 2) (t / 2) := by
  constructor
  · intro d hd
    exact (cert.toGeneralOrderRunCertificate d hd).denominatorRecovery hr
  constructor
  · exact cert.orderRecoverySuccessLowerBound_le_goodMassSum hr
  constructor
  · simpa [hphase] using
      Resource.ResourceParameters.toExactResourceProfile_hasExactCounts params
  · simpa [hphase] using Resource.ResourceParameters.fourierGateProfile_exact params

/-- Typed circuit witness for the exact order-finding endpoint. -/
def orderFindingCircuit (t : ℕ) : Circuit (Qubits t) :=
  Circuit.abstract (Qubits t) "order-finding" (orderFindingExactResourceProfile t)
    (t ^ 2) 1

/-- Register assumptions for the modular-exponentiation oracle used in exact
order finding. The target register has `m` qubits, large enough to hold
residues modulo `N`. -/
structure ModExpOracleAccess (N x t m : ℕ) where
  modulus_pos : 0 < N
  register_fits : N ≤ 2 ^ m

/-- Target-register update for the modular-exponentiation oracle:
`y ↦ y xor (x^a mod N)`. -/
def modExpOracleTarget {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) : Fin (2 ^ m) :=
  ⟨Nat.xor y.val (x ^ a.val % N),
    Nat.xor_lt_two_pow y.isLt
      (lt_of_lt_of_le (Nat.mod_lt _ A.modulus_pos) A.register_fits)⟩

@[simp]
theorem modExpOracleTarget_val {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracleTarget A a y).val = Nat.xor y.val (x ^ a.val % N) :=
  rfl

/-- The basis permutation underlying the modular-exponentiation oracle. -/
def modExpOraclePerm {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    Equiv.Perm (Fin (2 ^ t) × Fin (2 ^ m)) where
  toFun p := (p.1, modExpOracleTarget A p.1 p.2)
  invFun p := (p.1, modExpOracleTarget A p.1 p.2)
  left_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_assoc]
  right_inv p := by
    ext <;> simp [modExpOracleTarget, Nat.xor_assoc]

@[simp]
theorem modExpOraclePerm_apply {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (p : Fin (2 ^ t) × Fin (2 ^ m)) :
    modExpOraclePerm A p = (p.1, modExpOracleTarget A p.1 p.2) :=
  rfl

@[simp]
theorem modExpOraclePerm_symm {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    (modExpOraclePerm A).symm = modExpOraclePerm A :=
  rfl

/-- The modular-exponentiation oracle gate in the public access model:
`U_x |a,y> = |a, y xor (x^a mod N)>`. -/
def modExpOracle {N x t m : ℕ} (A : ModExpOracleAccess N x t m) : Gate (Qubits (t + m)) :=
  Gate.ofPerm (prodEquiv.permCongr (modExpOraclePerm A))

theorem modExpOracle_mem_unitaryGroup {N x t m : ℕ} (A : ModExpOracleAccess N x t m) :
    ((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
      ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ :=
  Gate.ofPerm_mem_unitaryGroup _

/-- Basis action of the modular-exponentiation oracle. -/
theorem modExpOracle_apply_ket {N x t m : ℕ} (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    (modExpOracle A).apply (ket (prodEquiv (a, y))) =
      ket (prodEquiv (a, modExpOracleTarget A a y)) := by
  rw [modExpOracle, Gate.ofPerm_apply_ket]
  congr 1
  change prodEquiv ((modExpOraclePerm A).symm (prodEquiv.symm (prodEquiv (a, y))))
      = prodEquiv (a, modExpOracleTarget A a y)
  rw [Equiv.symm_apply_apply, modExpOraclePerm_symm, modExpOraclePerm_apply]

/-- Coarse one-query resource profile for the modular-exponentiation oracle
boundary used by the public order-finding access model. -/
def modExpOracleResourceProfile : ResourceProfile where
  oracleQueries := 1
  hadamardGates := 0
  elementaryGates := 0
  classicalOps := 0

theorem modExpOracleResourceProfile_exact :
    ResourceProfile.HasExactCounts modExpOracleResourceProfile 1 0 0 0 := by
  simp [ResourceProfile.HasExactCounts, modExpOracleResourceProfile]

/-- Typed circuit witness for the modular-exponentiation oracle in the public
order-finding access model. -/
noncomputable def modExpOracleCircuit {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) : Circuit (Qubits (t + m)) :=
  Circuit.ofGate "order-finding-modexp-oracle" (modExpOracle A)
    modExpOracleResourceProfile 1 1

/-- Modular-exponentiation oracle circuit with source-supplied depth. The
query count remains one; the depth parameter is selected by the exact
resource-counting pass. -/
noncomputable def modExpOracleCircuitWithDepth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (oracleDepth : ℕ) : Circuit (Qubits (t + m)) :=
  Circuit.ofGate "order-finding-modexp-oracle" (modExpOracle A)
    modExpOracleResourceProfile oracleDepth 1

/-- Typed resource boundary for the inverse-QFT/readout stage that follows the
modular-exponentiation oracle in the public order-finding access model. -/
def orderFindingFourierReadoutCircuit (t m : ℕ) : Circuit (Qubits (t + m)) :=
  Circuit.abstract (Qubits (t + m)) "order-finding-fourier-readout"
    (orderFindingFourierReadoutResourceProfile t) (t ^ 2) 0

/-- Resource projection for the exact inverse-QFT/readout and classical
post-processing pass selected by source-count parameters. -/
def orderFindingExactFourierReadoutResourceProfile
    (params : Resource.ResourceParameters) : ResourceProfile where
  oracleQueries := 0
  hadamardGates := params.phaseRegisterQubits
  elementaryGates :=
    params.fourierGateProfile.controlledPhaseGates +
      params.fourierGateProfile.swapGates
  classicalOps := params.classicalPostProcessing.total

/-- Typed resource boundary for the exact inverse-QFT/readout pass selected by
source-count parameters. -/
def orderFindingExactFourierReadoutCircuit {t m : ℕ}
    (params : Resource.ResourceParameters) : Circuit (Qubits (t + m)) :=
  Circuit.abstract (Qubits (t + m)) "order-finding-exact-fourier-readout"
    (orderFindingExactFourierReadoutResourceProfile params)
    params.fourierReadoutDepth 0

/-- Access-level order-finding circuit: a real modular-exponentiation oracle
gate followed by the abstract Fourier/readout resource boundary. -/
noncomputable def orderFindingAccessCircuit {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) : Circuit (Qubits (t + m)) :=
  Circuit.seq (modExpOracleCircuit A) (orderFindingFourierReadoutCircuit t m)

/-- Exact-resource access-level order-finding circuit: the real oracle gate is
paired with the exact resource boundary selected for inverse-QFT/readout and
classical post-processing. -/
noncomputable def orderFindingExactAccessCircuit {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (params : Resource.ResourceParameters) :
    Circuit (Qubits (t + m)) :=
  Circuit.seq (modExpOracleCircuitWithDepth A params.oracleDepth)
    (orderFindingExactFourierReadoutCircuit (t := t) (m := m) params)

@[simp] theorem modExpOracleCircuit_resources {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    (modExpOracleCircuit A).resources = modExpOracleResourceProfile :=
  rfl

@[simp] theorem modExpOracleCircuit_depth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    (modExpOracleCircuit A).depth = 1 :=
  rfl

@[simp] theorem modExpOracleCircuit_queryDepth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    (modExpOracleCircuit A).queryDepth = 1 :=
  rfl

@[simp] theorem modExpOracleCircuitWithDepth_resources {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (oracleDepth : ℕ) :
    (modExpOracleCircuitWithDepth A oracleDepth).resources = modExpOracleResourceProfile :=
  rfl

@[simp] theorem modExpOracleCircuitWithDepth_depth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (oracleDepth : ℕ) :
    (modExpOracleCircuitWithDepth A oracleDepth).depth = oracleDepth :=
  rfl

@[simp] theorem modExpOracleCircuitWithDepth_queryDepth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (oracleDepth : ℕ) :
    (modExpOracleCircuitWithDepth A oracleDepth).queryDepth = 1 :=
  rfl

@[simp] theorem orderFindingFourierReadoutCircuit_resources (t m : ℕ) :
    (orderFindingFourierReadoutCircuit t m).resources =
      orderFindingFourierReadoutResourceProfile t :=
  rfl

@[simp] theorem orderFindingExactFourierReadoutCircuit_resources {t m : ℕ}
    (params : Resource.ResourceParameters) :
    (orderFindingExactFourierReadoutCircuit (t := t) (m := m) params).resources =
      orderFindingExactFourierReadoutResourceProfile params :=
  rfl

@[simp] theorem orderFindingExactAccessCircuit_resources {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (params : Resource.ResourceParameters) :
    (orderFindingExactAccessCircuit A params).resources =
      params.toExactResourceProfile.toResourceProfile := by
  ext <;>
    simp [orderFindingExactAccessCircuit, modExpOracleCircuitWithDepth,
      orderFindingExactFourierReadoutCircuit, orderFindingExactFourierReadoutResourceProfile,
      modExpOracleResourceProfile,
      Resource.ResourceParameters.toExactResourceProfile,
      Resource.ResourceParameters.fourierGateProfile,
      Resource.ResourceParameters.oracleQueryCount,
      Resource.ExactResourceProfile.toResourceProfile, Resource.ExactResourceProfile.classicalOps,
      ResourceProfile.sequential, Circuit.seq, Circuit.ofGate, Circuit.atom, Circuit.abstract]

@[simp] theorem orderFindingExactAccessCircuit_depth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (params : Resource.ResourceParameters) :
    (orderFindingExactAccessCircuit A params).depth =
      params.oracleDepth + params.fourierReadoutDepth :=
  rfl

@[simp] theorem orderFindingExactAccessCircuit_queryDepth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (params : Resource.ResourceParameters) :
    (orderFindingExactAccessCircuit A params).queryDepth = 1 :=
  rfl

/-- The exact access circuit carries the coarse projection of the selected
private order-finding exact-resource profile. -/
theorem orderFindingExactAccessCircuit_resourceProjection {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) (params : Resource.ResourceParameters) :
    (orderFindingExactAccessCircuit A params).resources =
      params.toExactResourceProfile.toResourceProfile ∧
      (orderFindingExactAccessCircuit A params).depth =
        params.toExactResourceProfile.circuitDepth ∧
      (orderFindingExactAccessCircuit A params).queryDepth =
        params.toExactResourceProfile.oracleQueries := by
  constructor
  · exact orderFindingExactAccessCircuit_resources A params
  constructor
  · simp [orderFindingExactAccessCircuit, modExpOracleCircuitWithDepth,
      orderFindingExactFourierReadoutCircuit, Resource.ResourceParameters.toExactResourceProfile,
      Resource.ResourceParameters.circuitDepth, Circuit.seq, Circuit.ofGate, Circuit.atom,
      Circuit.abstract]
  · simp [orderFindingExactAccessCircuit, modExpOracleCircuitWithDepth,
      orderFindingExactFourierReadoutCircuit, Resource.ResourceParameters.toExactResourceProfile,
      Resource.ResourceParameters.oracleQueryCount, Circuit.seq, Circuit.ofGate, Circuit.atom,
      Circuit.abstract]

@[simp] theorem orderFindingAccessCircuit_resources {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingAccessCircuit A).resources =
      ResourceProfile.sequential modExpOracleResourceProfile
        (orderFindingFourierReadoutResourceProfile t) :=
  rfl

@[simp] theorem orderFindingAccessCircuit_queryDepth {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    (orderFindingAccessCircuit A).queryDepth = 1 :=
  rfl

/-- Coarse exact counts for the access-level order-finding circuit. -/
theorem orderFindingAccessCircuit_resources_exact {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    ResourceProfile.HasExactCounts
      (orderFindingAccessCircuit A).resources 1 t (t ^ 2) 1 := by
  simp [ResourceProfile.HasExactCounts, orderFindingAccessCircuit,
    orderFindingFourierReadoutCircuit, modExpOracleCircuit,
    modExpOracleResourceProfile, orderFindingFourierReadoutResourceProfile,
    ResourceProfile.sequential]

/-- Circuit-aware source-joint endpoint for general-order Shor order finding.
The source distribution and continued-fraction recovery are supplied by the
rounded nearest-fraction certificate, while the black-box oracle/readout
resources are tied to the typed access circuit. -/
noncomputable def shorSourceJointRunWithScaledErrorResourceCorrectWitness
    {N x t m r : ℕ}
    (A : ModExpOracleAccess N x t m)
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t) :
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hr hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n) ∧
            (((((shorNearestFractionEvent hr hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome)
      (ResourceProfile.HasExactCounts (orderFindingAccessCircuit A).resources 1 t (t ^ 2) 1 ∧
        CircuitGateProfile.HasExactCounts (orderFindingFourierGateProfile t)
          t (t * (t - 1) / 2) (t / 2)) := by
  have hrun := shorSourceJoint_run_with_scaled_error_resource_certificates hr hq hlarge
  exact
    { circuit := orderFindingAccessCircuit A
      correctness := ⟨⟨modExpOracle_mem_unitaryGroup A, fun a y => modExpOracle_apply_ket A a y⟩,
        hrun.1, hrun.2.1⟩
      resources := ⟨orderFindingAccessCircuit_resources_exact A, hrun.2.2.2⟩ }

/-- Circuit-aware source-joint endpoint for the private exact-resource
order-finding target. The phase events and aggregate lower bound use the same
rounded nearest-fraction source certificate as the public source-joint bridge
[Sho95, source.tex:1614-1633] [dW19, qcnotes.tex:2279-2301], while the
resource claim is tied to the typed exact access circuit. -/
noncomputable def shorSourceJointRunWithScaledErrorPrivateExactResourceCorrectWitness
    {N x t m r : ℕ}
    (A : ModExpOracleAccess N x t m)
    (hr : 0 < r) (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t)
    (horacle : params.oracleRegisterQubits = m) :
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hr hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n) ∧
            (((((shorNearestFractionEvent hr hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome)
      (Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
          1
          (t + m)
          t
          (t * (t - 1) / 2)
          (t / 2)
          (params.oracleDepth + params.fourierReadoutDepth)
          params.classicalPostProcessing.total ∧
        (orderFindingExactAccessCircuit A params).resources =
          params.toExactResourceProfile.toResourceProfile ∧
        (orderFindingExactAccessCircuit A params).depth =
          params.oracleDepth + params.fourierReadoutDepth ∧
        (orderFindingExactAccessCircuit A params).queryDepth = 1 ∧
        CircuitGateProfile.HasExactCounts params.fourierGateProfile
          t (t * (t - 1) / 2) (t / 2)) := by
  have hrun := shorSourceJoint_run_with_scaled_error_resource_certificates hr hq hlarge
  have hexact :
      Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
        1
        (t + m)
        t
        (t * (t - 1) / 2)
        (t / 2)
        (params.oracleDepth + params.fourierReadoutDepth)
        params.classicalPostProcessing.total := by
    simpa [hphase, horacle] using
      Resource.ResourceParameters.toExactResourceProfile_hasExactCounts params
  have hgate :
      CircuitGateProfile.HasExactCounts params.fourierGateProfile
        t (t * (t - 1) / 2) (t / 2) := by
    simpa [hphase] using Resource.ResourceParameters.fourierGateProfile_exact params
  have hprojection := orderFindingExactAccessCircuit_resourceProjection A params
  exact
    { circuit := orderFindingExactAccessCircuit A params
      correctness := ⟨⟨modExpOracle_mem_unitaryGroup A, fun a y => modExpOracle_apply_ket A a y⟩,
        hrun.1, hrun.2.1⟩
      resources := ⟨hexact, hprojection.1, hprojection.2.1, hprojection.2.2, hgate⟩ }

/-- Circuit-aware source-joint endpoint from public register bounds. This is
the strengthened order-finding witness intended for public-register theorem
projection: the correctness statement and private exact-resource statement are
tied to the same typed `orderFindingExactAccessCircuit`. -/
noncomputable def shorSourceJointRunWithPublicRegisterPrivateExactResourceCorrectWitness
    {N x t m r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hlargeRegister : 12 * N ≤ 2 ^ t)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t)
    (horacle : params.oracleRegisterQubits = m) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n) ∧
            (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome)
      (Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
          1
          (t + m)
          t
          (t * (t - 1) / 2)
          (t / 2)
          (params.oracleDepth + params.fourierReadoutDepth)
          params.classicalPostProcessing.total ∧
        (orderFindingExactAccessCircuit A params).resources =
          params.toExactResourceProfile.toResourceProfile ∧
        (orderFindingExactAccessCircuit A params).depth =
          params.oracleDepth + params.fourierReadoutDepth ∧
        (orderFindingExactAccessCircuit A params).queryDepth = 1 ∧
        CircuitGateProfile.HasExactCounts params.fourierGateProfile
          t (t * (t - 1) / 2) (t / 2)) := by
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  have hlarge : 12 * r ≤ 2 ^ t :=
    largeRegister_of_order_le_modulus
      (le_of_lt (input_order_lt_modulus hinput)) hlargeRegister
  simpa [hq] using
    shorSourceJointRunWithScaledErrorPrivateExactResourceCorrectWitness
      A hinput.order_pos hq hlarge params hphase horacle

/-- Circuit-aware source-joint endpoint from the restored public register lower
bound in the large-modulus branch. This wrapper keeps correctness and exact
resource accounting tied to the same typed circuit while deriving the current
finite large-register hypothesis from `12 <= N` and `N^2 <= 2^t`
[Sho95, source.tex:1183-1185]. -/
noncomputable def
    shorSourceJointRunWithPublicRegisterLargeModulusPrivateExactResourceCorrectWitness
    {N x t m r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (hN : 12 ≤ N)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t)
    (horacle : params.oracleRegisterQubits = m) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) :
            HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n) ∧
            (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome)
      (Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
          1
          (t + m)
          t
          (t * (t - 1) / 2)
          (t / 2)
          (params.oracleDepth + params.fourierReadoutDepth)
          params.classicalPostProcessing.total ∧
        (orderFindingExactAccessCircuit A params).resources =
          params.toExactResourceProfile.toResourceProfile ∧
        (orderFindingExactAccessCircuit A params).depth =
          params.oracleDepth + params.fourierReadoutDepth ∧
        (orderFindingExactAccessCircuit A params).queryDepth = 1 ∧
        CircuitGateProfile.HasExactCounts params.fourierGateProfile
          t (t * (t - 1) / 2) (t / 2)) := by
  have hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
    publicRegisterBound_implies_scaledError_of_order_lt_modulus
      (input_order_lt_modulus hinput) hregister
  have hlarge : 12 * r ≤ 2 ^ t :=
    largeRegister_of_publicRegisterBound_of_modulus_ge_twelve
      hN (input_order_lt_modulus hinput) hregister
  simpa [hq] using
    shorSourceJointRunWithScaledErrorPrivateExactResourceCorrectWitness
      A hinput.order_pos hq hlarge params hphase horacle

open Resource.ResourceParameters in
/-- Circuit-aware source-joint endpoint from public register bounds with the
canonical continued-fraction post-processing upper bound attached. This is the
public exact-resource projection of the stronger private witness: correctness,
the modular-exponentiation oracle boundary, and the explicit
`C_OF(t)` classical arithmetic count are all attached to the same typed
`orderFindingExactAccessCircuit`. The continued-fraction recovery route follows
Shor's nearest-fraction step [Sho95, source.tex:1617-1633] and the same
post-processing formulation in de Wolf's notes [dW19, qcnotes.tex:2292-2303]. -/
noncomputable def
    shorSourceJointRunWithPublicRegisterContinuedFractionUpperBoundResourceCorrectWitness
    {N x t m r : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m)
    (hregister : N ^ 2 ≤ 2 ^ t)
    (hlargeRegister : 12 * N ≤ 2 ^ t)
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t)
    (horacle : params.oracleRegisterQubits = m) :
    let hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t :=
      publicRegisterBound_implies_scaledError_of_order_lt_modulus
        (input_order_lt_modulus hinput) hregister;
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ n,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n) ∧
            (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent n).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome)
      (Resource.ExactResourceProfile.HasExactCounts
          params.withContinuedFractionUpperBound.toExactResourceProfile
          1
          (t + m)
          t
          (t * (t - 1) / 2)
          (t / 2)
          (params.oracleDepth + params.fourierReadoutDepth)
          (Resource.PostProcessingCountParameters.continuedFractionUpperBoundTotal t) ∧
        (orderFindingExactAccessCircuit A params.withContinuedFractionUpperBound).resources =
          params.withContinuedFractionUpperBound.toExactResourceProfile.toResourceProfile ∧
        (orderFindingExactAccessCircuit A params.withContinuedFractionUpperBound).depth =
          params.oracleDepth + params.fourierReadoutDepth ∧
        (orderFindingExactAccessCircuit A params.withContinuedFractionUpperBound).queryDepth = 1 ∧
        CircuitGateProfile.HasExactCounts
          params.withContinuedFractionUpperBound.fourierGateProfile
          t (t * (t - 1) / 2) (t / 2)) := by
  let params' := params.withContinuedFractionUpperBound
  have hphase' : params'.phaseRegisterQubits = t := by
    simpa [params', Resource.ResourceParameters.withContinuedFractionUpperBound,
      Resource.ResourceParameters.withPostProcessingCounts] using hphase
  have horacle' : params'.oracleRegisterQubits = m := by
    simpa [params', Resource.ResourceParameters.withContinuedFractionUpperBound,
      Resource.ResourceParameters.withPostProcessingCounts] using horacle
  have hclassical :
      params'.classicalPostProcessing.total =
        Resource.PostProcessingCountParameters.continuedFractionUpperBoundTotal t := by
    dsimp [params']
    rw [Resource.ResourceParameters.withContinuedFractionUpperBound_classicalOps]
    rw [hphase]
  let run :=
    shorSourceJointRunWithPublicRegisterPrivateExactResourceCorrectWitness
      hinput A hregister hlargeRegister params' hphase' horacle'
  exact
    { circuit := run.circuit
      correctness := run.correctness
      resources := by
        refine ⟨?_, run.resources.2.1, ?_, run.resources.2.2.2.1,
          run.resources.2.2.2.2⟩
        · simpa [hphase, horacle] using
            withContinuedFractionUpperBound_toExactResourceProfile_hasExactCounts params
        · simp [Resource.ResourceParameters.withContinuedFractionUpperBound,
            Resource.ResourceParameters.withPostProcessingCounts] }

/-- Basis action of the typed modular-exponentiation oracle circuit. -/
theorem modExpOracleCircuit_apply_ket {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m)
    (a : Fin (2 ^ t)) (y : Fin (2 ^ m)) :
    Circuit.apply (modExpOracleCircuit A)
      (PureState.ket (R := Qubits (t + m)) (prodEquiv (a, y)) :
        StateVector (Qubits (t + m))) =
      (PureState.ket (R := Qubits (t + m))
        (prodEquiv (a, modExpOracleTarget A a y)) :
        StateVector (Qubits (t + m))) := by
  simpa [modExpOracleCircuit, Circuit.apply_ofGate, Gate.apply_coe] using
    congrArg (fun psi : PureState (Qubits (t + m)) =>
      (psi : StateVector (Qubits (t + m)))) (modExpOracle_apply_ket A a y)

/-- Resource-correct witness for the public modular-exponentiation oracle
boundary. -/
noncomputable def modExpOracleCircuitResourceCorrectWitness {N x t m : ℕ}
    (A : ModExpOracleAccess N x t m) :
    ResourceCorrectWitness (R := Qubits (t + m))
      (∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
        Circuit.apply (modExpOracleCircuit A)
          (PureState.ket (R := Qubits (t + m)) (prodEquiv (a, y)) :
            StateVector (Qubits (t + m))) =
          (PureState.ket (R := Qubits (t + m))
            (prodEquiv (a, modExpOracleTarget A a y)) :
            StateVector (Qubits (t + m))))
      (ResourceProfile.HasExactCounts (modExpOracleCircuit A).resources 1 0 0 0 ∧
        (modExpOracleCircuit A).depth = 1 ∧
        (modExpOracleCircuit A).queryDepth = 1) := by
  exact
    { circuit := modExpOracleCircuit A
      correctness := fun a y => modExpOracleCircuit_apply_ket A a y
      resources := ⟨by simpa [modExpOracleCircuit] using modExpOracleResourceProfile_exact,
        rfl, rfl⟩ }

/-- Exact order finding paired with the decoupled resource profile. -/
theorem main_exact_dyadic_with_resources {t s r : ℕ}
    (hr : 0 < r) (hrt : r ∣ 2 ^ t) (hsr : Nat.Coprime s r)
    (j : Fin (2 ^ t)) (hj : j.val = s * (2 ^ t / r)) :
    ((invQFT t).applyVec (phaseState t ((s : ℝ) / r))
        = (PureState.ket (R := Qubits t) j : StateVector (Qubits t))
      ∧ 2 ^ t / Nat.gcd j.val (2 ^ t) = r) ∧
      ResourceProfile.HasExactCounts
        (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  constructor
  · exact main_exact_dyadic hr hrt hsr j hj
  · exact orderFindingExactResourceProfile_exact t

end OrderFinding

namespace OrderFinding

/-- Exact order-finding output index paired with the public one-query resource
claim. If `q = 2^t` is a multiple of the order `r`, then every
`s ∈ {0, ..., r-1}` gives a valid phase-register output index
`j = s(q/r)`. The modular-exponentiation oracle body is treated as one oracle
call in this resource profile. -/
theorem main_output_with_resources {N x t r s : ℕ}
    (hinput : OrderFinding.Input N x r) (hrt : r ∣ 2 ^ t) (hs : s < r) :
    ∃ j : Fin (2 ^ t),
      j.val = s * (2 ^ t / r) ∧
        ResourceProfile.HasExactCounts
          (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  obtain ⟨q, hq⟩ := hrt
  have hqpos : 0 < q := by
    rcases Nat.eq_zero_or_pos q with hzero | hpos
    · exfalso
      have hpow : 0 < 2 ^ t := pow_pos (by norm_num) t
      rw [hq, hzero, Nat.mul_zero] at hpow
      exact (Nat.lt_irrefl 0) hpow
    · exact hpos
  have hdiv : 2 ^ t / r = q := by
    rw [hq]
    exact Nat.mul_div_cancel_left q hinput.order_pos
  have hlt : s * q < 2 ^ t := by
    rw [hq]
    exact Nat.mul_lt_mul_of_pos_right hs hqpos
  refine ⟨⟨s * q, hlt⟩, ?_⟩
  constructor
  · rw [hdiv]
  · exact orderFindingExactResourceProfile_exact t

end OrderFinding

namespace OrderFinding

/-- Integrated exact order-finding access theorem: the modular-exponentiation
oracle is a unitary gate with the public basis action, and the exact divisible
case has a phase-register output index with the trusted one-query resource
profile. -/
theorem main {N x t m r s : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hrt : r ∣ 2 ^ t) (hs : s < r) :
    (((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
        ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
      ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
        (modExpOracle A).apply (ket (prodEquiv (a, y))) =
          ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
      ∃ j : Fin (2 ^ t),
        j.val = s * (2 ^ t / r) ∧
          ResourceProfile.HasExactCounts
            (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1 := by
  constructor
  · constructor
    · exact modExpOracle_mem_unitaryGroup A
    · intro a y
      exact modExpOracle_apply_ket A a y
  · exact main_output_with_resources hinput hrt hs

/-- Resource-correct public witness for exact order finding. -/
def mainResourceCorrectWitness {N x t m r s : ℕ}
    (hinput : OrderFinding.Input N x r)
    (A : ModExpOracleAccess N x t m) (hrt : r ∣ 2 ^ t) (hs : s < r) :
    ResourceCorrectWitness (R := Qubits (t + m))
      ((((modExpOracle A : Gate (Qubits (t + m))) : HilbertOperator (Qubits (t + m)))
          ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
        ∀ a : Fin (2 ^ t), ∀ y : Fin (2 ^ m),
          (modExpOracle A).apply (ket (prodEquiv (a, y))) =
            ket (prodEquiv (a, modExpOracleTarget A a y))) ∧
        ∃ j : Fin (2 ^ t),
          j.val = s * (2 ^ t / r) ∧
            ResourceProfile.HasExactCounts
              (orderFindingExactResourceProfile t) 1 t (t ^ 2) 1)
      (ResourceProfile.HasExactCounts (orderFindingAccessCircuit A).resources 1 t (t ^ 2) 1) := by
  exact
    { circuit := orderFindingAccessCircuit A
      correctness := main hinput A hrt hs
      resources := orderFindingAccessCircuit_resources_exact A }

end OrderFinding

namespace OrderFinding

/-- Private exact-resource version of the circuit-aware Shor bridge from the
source-joint order-finding endpoint to nontrivial gcd factors. This is the
intended proof object for later public Shor/RSA theorem nodes: the public
statement should be obtained by projecting or upper-bounding this stronger
exact-resource witness, so correctness and resource accounting stay tied to
the same typed `orderFindingExactAccessCircuit`. -/
noncomputable def shorSourceJointGcdBridgePrivateExactResourceCorrectWitness
    {N n a t m r : ℕ}
    (D : ModularMultiplicationDomain N n)
    (hinput : OrderFinding.Input N a r)
    (A : ModExpOracleAccess N a t m)
    (hq : (r : ℝ) ^ 2 < (2 : ℝ) ^ t)
    (hlarge : 12 * r ≤ 2 ^ t)
    (heven : Even r)
    (hleft : ¬ (a ^ (r / 2) - 1) ≡ 0 [MOD N])
    (hright : ¬ (a ^ (r / 2) + 1) ≡ 0 [MOD N])
    (params : Resource.ResourceParameters)
    (hphase : params.phaseRegisterQubits = t)
    (horacle : params.oracleRegisterQubits = m) :
    ResourceCorrectWitness (R := Qubits (t + m))
      (((((modExpOracle A : Gate (Qubits (t + m))) :
            HilbertOperator (Qubits (t + m)))
            ∈ Matrix.unitaryGroup (Fin (2 ^ (t + m))) ℂ ∧
          ∀ exponent : Fin (2 ^ t), ∀ target : Fin (2 ^ m),
            (modExpOracle A).apply (ket (prodEquiv (exponent, target))) =
              ket (prodEquiv (exponent, modExpOracleTarget A exponent target))) ∧
        (∀ d, d ∈ shorRecoverableFractionIndices r →
          ∃ k,
            (d.val : ℚ) / (r : ℚ) =
              ((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent k) ∧
            (((((shorNearestFractionEvent hinput.order_pos hq d).val : ℝ) /
                (2 : ℝ) ^ t).convergent k).den = r)) ∧
        shorOrderRecoverySuccessLowerBound r ≤
          ∑ outcome : ShorSourceJointOutcome t r,
            shorSourceJointProbability t r outcome) ∧
        ((1 < Nat.gcd (a ^ (r / 2) - 1) N ∧
            Nat.gcd (a ^ (r / 2) - 1) N < N) ∧
          (1 < Nat.gcd (a ^ (r / 2) + 1) N ∧
            Nat.gcd (a ^ (r / 2) + 1) N < N)))
      (Resource.ExactResourceProfile.HasExactCounts params.toExactResourceProfile
          1
          (t + m)
          t
          (t * (t - 1) / 2)
          (t / 2)
          (params.oracleDepth + params.fourierReadoutDepth)
          params.classicalPostProcessing.total ∧
        (orderFindingExactAccessCircuit A params).resources =
          params.toExactResourceProfile.toResourceProfile ∧
        (orderFindingExactAccessCircuit A params).depth =
          params.oracleDepth + params.fourierReadoutDepth ∧
        (orderFindingExactAccessCircuit A params).queryDepth = 1 ∧
        CircuitGateProfile.HasExactCounts params.fourierGateProfile
          t (t * (t - 1) / 2) (t / 2)) := by
  let run :=
    shorSourceJointRunWithScaledErrorPrivateExactResourceCorrectWitness
      A hinput.order_pos hq hlarge params hphase horacle
  exact
    { circuit := run.circuit
      correctness :=
        ⟨run.correctness,
          shor_gcd_bridge_of_input_order D hinput heven hleft hright⟩
      resources := run.resources }

end OrderFinding

end

end QuantumAlg
