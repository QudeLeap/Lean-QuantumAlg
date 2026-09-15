/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
public import QuantumAlg.Core.Base.Gate.OperatorNorm
import all QuantumAlg.Core.Base.Gate.OperatorNorm
import all QuantumAlg.Core.Base.Gate.Basic
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# Exact and approximate circuit realizations

A compiled circuit is useful only together with the statement of what it
computes. `UnitaryCircuit.ExactRealization target` packages a circuit whose
matrix is exactly `target`; `UnitaryCircuit.ApproxRealization target ε` packages a
circuit whose matrix is within operator-norm distance `ε` of `target`.

Both are plain structures over the sealed `UnitaryCircuit`, so every accounting
projection (`eventCost`, `eventDepth`, gate counts) of the realization is the
projection of its circuit. Error composes additively under sequencing,
is preserved by `dagger`, and scales linearly under `iterate`; these are the
only composition rules compiled-circuit error analyses need.

`seq left right` executes `left` first, so sequencing a realization of `U₁`
followed by a realization of `U₂` realizes `U₂ * U₁`.
-/

section

namespace QuantumAlg

namespace UnitaryCircuit

noncomputable section

variable {R : Register}

/-- A circuit whose matrix is exactly the target unitary. -/
public structure ExactRealization (target : UnitaryOperator R) where
  /-- The realizing circuit. -/
  circuit : UnitaryCircuit R
  /-- The circuit computes the target exactly. -/
  matrix_eq : circuit.matrix = target

/-- A circuit whose matrix is within operator-norm distance `ε` of the target. -/
public structure ApproxRealization (target : UnitaryOperator R) (ε : ℝ) where
  /-- The realizing circuit. -/
  circuit : UnitaryCircuit R
  /-- The operator-norm error bound. -/
  error_le :
    HilbertOperator.opNorm ((circuit.matrix : HilbertOperator R) - (target : HilbertOperator R)) ≤ ε

namespace ExactRealization

variable {target : UnitaryOperator R}

theorem coe_matrix_eq (r : ExactRealization target) :
    (r.circuit.matrix : HilbertOperator R) = (target : HilbertOperator R) := by
  rw [r.matrix_eq]

/-- An exact realization is an approximate realization with zero error. -/
public def toApprox (r : ExactRealization target) : ApproxRealization target 0 where
  circuit := r.circuit
  error_le := by
    rw [r.coe_matrix_eq, sub_self, HilbertOperator.opNorm_zero]

@[simp]
theorem toApprox_circuit (r : ExactRealization target) : r.toApprox.circuit = r.circuit := rfl

/-- Sequencing exact realizations: `left` runs first. -/
public def seq {U₁ U₂ : UnitaryOperator R} (left : ExactRealization U₁)
    (right : ExactRealization U₂) : ExactRealization (U₂ * U₁) where
  circuit := UnitaryCircuit.seq left.circuit right.circuit
  matrix_eq := by
    apply Subtype.ext
    rw [seq_matrix, left.coe_matrix_eq, right.coe_matrix_eq]
    rfl

@[simp]
theorem seq_circuit {U₁ U₂ : UnitaryOperator R} (left : ExactRealization U₁)
    (right : ExactRealization U₂) :
    (left.seq right).circuit = UnitaryCircuit.seq left.circuit right.circuit := rfl

/-- The adjoint circuit realizes the adjoint unitary exactly. -/
public def dagger {U : UnitaryOperator R} (r : ExactRealization U) : ExactRealization (star U) where
  circuit := r.circuit.dagger
  matrix_eq := by
    apply Subtype.ext
    rw [dagger_matrix, r.coe_matrix_eq]
    rfl

@[simp]
theorem dagger_circuit {U : UnitaryOperator R} (r : ExactRealization U) :
    r.dagger.circuit = r.circuit.dagger := rfl

/-- Iterating an exact realization realizes the power exactly. -/
public def iterate {U : UnitaryOperator R} (count : Nat) (r : ExactRealization U) :
    ExactRealization (U ^ count) where
  circuit := UnitaryCircuit.iterate count r.circuit
  matrix_eq := by
    apply Subtype.ext
    rw [iterate_matrix, r.coe_matrix_eq]
    rfl

@[simp]
theorem iterate_circuit {U : UnitaryOperator R} (count : Nat) (r : ExactRealization U) :
    (r.iterate count).circuit = UnitaryCircuit.iterate count r.circuit := rfl

end ExactRealization

namespace ApproxRealization

variable {target : UnitaryOperator R} {ε : ℝ}

theorem error_le' (r : ApproxRealization target ε) :
    HilbertOperator.opNorm ((target : HilbertOperator R) - (r.circuit.matrix : HilbertOperator R)) ≤
      ε := by
  rw [HilbertOperator.opNorm_sub_comm]
  exact r.error_le

theorem nonneg (r : ApproxRealization target ε) : 0 ≤ ε :=
  (HilbertOperator.opNorm_nonneg _).trans r.error_le

/-- Any bound at least as large is also a valid bound. -/
public def weaken (r : ApproxRealization target ε) {ε' : ℝ} (h : ε ≤ ε') :
    ApproxRealization target ε' where
  circuit := r.circuit
  error_le := r.error_le.trans h

@[simp]
theorem weaken_circuit (r : ApproxRealization target ε) {ε' : ℝ} (h : ε ≤ ε') :
    (r.weaken h).circuit = r.circuit := rfl

/-- A zero-error approximate realization is exact. -/
public def toExact (r : ApproxRealization target 0) : ExactRealization target where
  circuit := r.circuit
  matrix_eq := by
    apply Subtype.ext
    have h := r.error_le
    have h0 : HilbertOperator.opNorm
        ((r.circuit.matrix : HilbertOperator R) - (target : HilbertOperator R)) = 0 :=
      le_antisymm h (HilbertOperator.opNorm_nonneg _)
    exact sub_eq_zero.mp (HilbertOperator.opNorm_eq_zero_iff.mp h0)

/-- Sequencing approximate realizations: `left` runs first and the errors add. -/
public def seq {U₁ U₂ : UnitaryOperator R} {ε₁ ε₂ : ℝ} (left : ApproxRealization U₁ ε₁)
    (right : ApproxRealization U₂ ε₂) : ApproxRealization (U₂ * U₁) (ε₁ + ε₂) where
  circuit := UnitaryCircuit.seq left.circuit right.circuit
  error_le := by
    have hcoe : ((U₂ * U₁ : UnitaryOperator R) : HilbertOperator R) =
        (U₂ : HilbertOperator R) * (U₁ : HilbertOperator R) := rfl
    rw [seq_matrix, hcoe]
    have h := HilbertOperator.opNorm_mul_sub_mul_le
      (A₁ := (right.circuit.matrix : HilbertOperator R))
      (A₂ := (left.circuit.matrix : HilbertOperator R))
      (B₁ := (U₂ : HilbertOperator R)) (B₂ := (U₁ : HilbertOperator R))
      left.circuit.matrix.2 U₂.2
    calc HilbertOperator.opNorm
          ((right.circuit.matrix : HilbertOperator R) * (left.circuit.matrix : HilbertOperator R) -
            (U₂ : HilbertOperator R) * (U₁ : HilbertOperator R))
        ≤ HilbertOperator.opNorm
              ((right.circuit.matrix : HilbertOperator R) - (U₂ : HilbertOperator R)) +
            HilbertOperator.opNorm
              ((left.circuit.matrix : HilbertOperator R) - (U₁ : HilbertOperator R)) := h
      _ ≤ ε₂ + ε₁ := add_le_add right.error_le left.error_le
      _ = ε₁ + ε₂ := add_comm _ _

@[simp]
theorem seq_circuit {U₁ U₂ : UnitaryOperator R} {ε₁ ε₂ : ℝ} (left : ApproxRealization U₁ ε₁)
    (right : ApproxRealization U₂ ε₂) :
    (left.seq right).circuit = UnitaryCircuit.seq left.circuit right.circuit := rfl

/-- The adjoint circuit approximates the adjoint unitary with the same error. -/
public def dagger {U : UnitaryOperator R} (r : ApproxRealization U ε) :
    ApproxRealization (star U) ε where
  circuit := r.circuit.dagger
  error_le := by
    have hcoe : ((star U : UnitaryOperator R) : HilbertOperator R) =
        star (U : HilbertOperator R) := rfl
    rw [dagger_matrix, hcoe, ← Matrix.star_eq_conjTranspose, ← star_sub,
      HilbertOperator.opNorm_star]
    exact r.error_le

@[simp]
theorem dagger_circuit {U : UnitaryOperator R} (r : ApproxRealization U ε) :
    r.dagger.circuit = r.circuit.dagger := rfl

/-- Iterating an approximate realization multiplies the error by the count. -/
public def iterate {U : UnitaryOperator R} (count : Nat) (r : ApproxRealization U ε) :
    ApproxRealization (U ^ count) (count * ε) where
  circuit := UnitaryCircuit.iterate count r.circuit
  error_le := by
    have hcoe : ((U ^ count : UnitaryOperator R) : HilbertOperator R) =
        (U : HilbertOperator R) ^ count := rfl
    rw [iterate_matrix, hcoe]
    calc HilbertOperator.opNorm
          ((r.circuit.matrix : HilbertOperator R) ^ count - (U : HilbertOperator R) ^ count)
        ≤ count * HilbertOperator.opNorm
            ((r.circuit.matrix : HilbertOperator R) - (U : HilbertOperator R)) :=
          HilbertOperator.opNorm_pow_sub_pow_le r.circuit.matrix.2 U.2 count
      _ ≤ count * ε := by
          apply mul_le_mul_of_nonneg_left r.error_le
          exact Nat.cast_nonneg count

@[simp]
theorem iterate_circuit {U : UnitaryOperator R} (count : Nat) (r : ApproxRealization U ε) :
    (r.iterate count).circuit = UnitaryCircuit.iterate count r.circuit := rfl

/-- Operational meaning: on every raw vector the realized circuit is within
`ε * ‖ψ‖` of the target action. -/
theorem norm_applyVec_sub_le (r : ApproxRealization target ε) (ψ : HilbertVector R) :
    ‖r.circuit.applyVec ψ - target.applyVec ψ‖ ≤ ε * ‖ψ‖ := by
  have hsub : r.circuit.applyVec ψ - target.applyVec ψ =
      HilbertOperator.applyVec
        ((r.circuit.matrix : HilbertOperator R) - (target : HilbertOperator R)) ψ := by
    rw [HilbertOperator.sub_applyVec]
    rfl
  rw [hsub]
  calc ‖HilbertOperator.applyVec
          ((r.circuit.matrix : HilbertOperator R) - (target : HilbertOperator R)) ψ‖
      ≤ HilbertOperator.opNorm
          ((r.circuit.matrix : HilbertOperator R) - (target : HilbertOperator R)) * ‖ψ‖ :=
        HilbertOperator.norm_applyVec_le _ ψ
    _ ≤ ε * ‖ψ‖ := mul_le_mul_of_nonneg_right r.error_le (norm_nonneg ψ)

end ApproxRealization

end

end UnitaryCircuit

end QuantumAlg

end
