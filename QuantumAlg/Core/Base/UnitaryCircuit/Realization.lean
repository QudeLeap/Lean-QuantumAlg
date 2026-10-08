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
# Realizations in a declared target language
A realization contains an actual target-model circuit on the specified physical
layout and its exact-phase equality or operator-norm error bound. Every resource
observation is derived from that circuit. Sequencing and repetition reuse real
constructions. Adjoint realization additionally consumes an actual target-model
implementation of the adjoint, with no automatic inverse-gate capability.
-/
section
namespace QuantumAlg
namespace UnitaryCircuit
noncomputable section
variable {gates : GateModel} {oracles : OracleModel}
variable {count : Nat} {layout : QuantumLayout count}
/-- An actual circuit realizing the target exactly, including its full phase. -/
public structure ExactRealization (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) (target : UnitaryOperator layout.register) where
  /-- The actual implementation in the declared language and physical layout. -/
  circuit : UnitaryCircuit gates oracles layout
  /-- Exact operator equality, without quotienting by global phase. -/
  matrix_eq : circuit.matrix = target
/-- An actual target-language circuit with an operator-norm error guarantee. -/
public structure ApproxRealization (gates : GateModel) (oracles : OracleModel)
    {count : Nat} (layout : QuantumLayout count) (target : UnitaryOperator layout.register)
    (ε : ℝ) where
  /-- The actual implementation supplies all its native resources. -/
  circuit : UnitaryCircuit gates oracles layout
  /-- Error is measured against the independently stated target operator. -/
  error_le : HilbertOperator.opNorm
    ((circuit.matrix : HilbertOperator layout.register) -
      (target : HilbertOperator layout.register)) ≤ ε
namespace ExactRealization
variable {target : UnitaryOperator layout.register}
theorem coe_matrix_eq (r : ExactRealization gates oracles layout target) :
    (r.circuit.matrix : HilbertOperator layout.register) =
      (target : HilbertOperator layout.register) := by
  rw [r.matrix_eq]
/-- An exact realization is an approximate realization with zero error. -/
public def toApprox (r : ExactRealization gates oracles layout target) :
    ApproxRealization gates oracles layout target 0 where
  circuit := r.circuit
  error_le := by
    rw [r.coe_matrix_eq, sub_self, HilbertOperator.opNorm_zero]
@[simp]
theorem toApprox_circuit (r : ExactRealization gates oracles layout target) :
    r.toApprox.circuit = r.circuit := rfl
/-- Sequencing exact realizations: `left` runs first. -/
public def seq {U₁ U₂ : UnitaryOperator layout.register}
    (left : ExactRealization gates oracles layout U₁)
    (right : ExactRealization gates oracles layout U₂) :
    ExactRealization gates oracles layout (U₂ * U₁) where
  circuit := UnitaryCircuit.seq left.circuit right.circuit
  matrix_eq := by
    rw [seq_matrix, left.matrix_eq, right.matrix_eq]
@[simp]
theorem seq_circuit {U₁ U₂ : UnitaryOperator layout.register}
    (left : ExactRealization gates oracles layout U₁)
    (right : ExactRealization gates oracles layout U₂) :
    (left.seq right).circuit = UnitaryCircuit.seq left.circuit right.circuit := rfl
/-- Iterating an exact realization realizes the power exactly. -/
public def iterate {U : UnitaryOperator layout.register} (count : Nat)
    (r : ExactRealization gates oracles layout U) :
    ExactRealization gates oracles layout (U ^ count) where
  circuit := UnitaryCircuit.iterate count r.circuit
  matrix_eq := by
    rw [iterate_matrix, r.matrix_eq]
@[simp]
theorem iterate_circuit {U : UnitaryOperator layout.register} (count : Nat)
    (r : ExactRealization gates oracles layout U) :
    (r.iterate count).circuit = UnitaryCircuit.iterate count r.circuit := rfl
/-- Use an actual realization of the implementation's adjoint in the same target language. -/
public def dagger {U : UnitaryOperator layout.register}
    (realized : ExactRealization gates oracles layout U)
    (implementation : ExactRealization gates oracles layout (star realized.circuit.matrix)) :
    ExactRealization gates oracles layout (star U) where
  circuit := implementation.circuit
  matrix_eq := by rw [implementation.matrix_eq, realized.matrix_eq]
@[simp] theorem dagger_circuit {U : UnitaryOperator layout.register}
    (realized : ExactRealization gates oracles layout U)
    (implementation : ExactRealization gates oracles layout (star realized.circuit.matrix)) :
    (realized.dagger implementation).circuit = implementation.circuit := rfl
end ExactRealization
namespace ApproxRealization
variable {target : UnitaryOperator layout.register} {ε : ℝ}
theorem error_le' (r : ApproxRealization gates oracles layout target ε) :
    HilbertOperator.opNorm ((target : HilbertOperator layout.register) -
      (r.circuit.matrix : HilbertOperator layout.register)) ≤
      ε := by
  rw [HilbertOperator.opNorm_sub_comm]
  exact r.error_le
theorem nonneg (r : ApproxRealization gates oracles layout target ε) : 0 ≤ ε :=
  (HilbertOperator.opNorm_nonneg _).trans r.error_le
/-- Any bound at least as large is also a valid bound. -/
public def weaken (r : ApproxRealization gates oracles layout target ε) {ε' : ℝ} (h : ε ≤ ε') :
    ApproxRealization gates oracles layout target ε' where
  circuit := r.circuit
  error_le := r.error_le.trans h
@[simp]
theorem weaken_circuit (r : ApproxRealization gates oracles layout target ε) {ε' : ℝ} (h : ε ≤ ε') :
    (r.weaken h).circuit = r.circuit := rfl
/-- A zero-error approximate realization is exact. -/
public def toExact (r : ApproxRealization gates oracles layout target 0) :
    ExactRealization gates oracles layout target where
  circuit := r.circuit
  matrix_eq := by
    apply Subtype.ext
    have h := r.error_le
    have h0 : HilbertOperator.opNorm
        ((r.circuit.matrix : HilbertOperator layout.register) -
          (target : HilbertOperator layout.register)) = 0 :=
      le_antisymm h (HilbertOperator.opNorm_nonneg _)
    exact sub_eq_zero.mp (HilbertOperator.opNorm_eq_zero_iff.mp h0)
/-- Sequencing approximate realizations: `left` runs first and the errors add. -/
public def seq {U₁ U₂ : UnitaryOperator layout.register} {ε₁ ε₂ : ℝ}
    (left : ApproxRealization gates oracles layout U₁ ε₁)
    (right : ApproxRealization gates oracles layout U₂ ε₂) :
    ApproxRealization gates oracles layout (U₂ * U₁) (ε₁ + ε₂) where
  circuit := UnitaryCircuit.seq left.circuit right.circuit
  error_le := by
    have hcoe : ((U₂ * U₁ : UnitaryOperator layout.register) : HilbertOperator layout.register) =
        (U₂ : HilbertOperator layout.register) * (U₁ : HilbertOperator layout.register) := rfl
    rw [seq_matrix, hcoe]
    have h := HilbertOperator.opNorm_mul_sub_mul_le
      (A₁ := (right.circuit.matrix : HilbertOperator layout.register))
      (A₂ := (left.circuit.matrix : HilbertOperator layout.register))
      (B₁ := (U₂ : HilbertOperator layout.register)) (B₂ := (U₁ : HilbertOperator layout.register))
      left.circuit.matrix.2 U₂.2
    calc HilbertOperator.opNorm
          ((right.circuit.matrix : HilbertOperator layout.register) *
            (left.circuit.matrix : HilbertOperator layout.register) -
            (U₂ : HilbertOperator layout.register) * (U₁ : HilbertOperator layout.register))
        ≤ HilbertOperator.opNorm
              ((right.circuit.matrix : HilbertOperator layout.register) -
                (U₂ : HilbertOperator layout.register)) +
            HilbertOperator.opNorm
              ((left.circuit.matrix : HilbertOperator layout.register) -
                (U₁ : HilbertOperator layout.register)) := h
      _ ≤ ε₂ + ε₁ := add_le_add right.error_le left.error_le
      _ = ε₁ + ε₂ := add_comm _ _
@[simp]
theorem seq_circuit {U₁ U₂ : UnitaryOperator layout.register} {ε₁ ε₂ : ℝ}
    (left : ApproxRealization gates oracles layout U₁ ε₁)
    (right : ApproxRealization gates oracles layout U₂ ε₂) :
    (left.seq right).circuit = UnitaryCircuit.seq left.circuit right.circuit := rfl
/-- Iterating an approximate realization multiplies the error by the count. -/
public def iterate {U : UnitaryOperator layout.register} (count : Nat)
    (r : ApproxRealization gates oracles layout U ε) :
    ApproxRealization gates oracles layout (U ^ count) (count * ε) where
  circuit := UnitaryCircuit.iterate count r.circuit
  error_le := by
    have hcoe : ((U ^ count : UnitaryOperator layout.register) : HilbertOperator layout.register) =
        (U : HilbertOperator layout.register) ^ count := rfl
    rw [iterate_matrix, hcoe]
    calc HilbertOperator.opNorm
          ((r.circuit.matrix : HilbertOperator layout.register) ^ count -
            (U : HilbertOperator layout.register) ^ count)
        ≤ count * HilbertOperator.opNorm
            ((r.circuit.matrix : HilbertOperator layout.register) -
              (U : HilbertOperator layout.register)) :=
          HilbertOperator.opNorm_pow_sub_pow_le r.circuit.matrix.2 U.2 count
      _ ≤ count * ε := by
          apply mul_le_mul_of_nonneg_left r.error_le
          exact Nat.cast_nonneg count
@[simp]
theorem iterate_circuit {U : UnitaryOperator layout.register} (count : Nat)
    (r : ApproxRealization gates oracles layout U ε) :
    (r.iterate count).circuit = UnitaryCircuit.iterate count r.circuit := rfl
/-- Operational meaning: on every raw vector the realized circuit is within
`ε * ‖ψ‖` of the target action. -/
theorem norm_applyVec_sub_le (r : ApproxRealization gates oracles layout target ε)
    (ψ : HilbertVector layout.register) :
    ‖r.circuit.applyVec ψ - target.applyVec ψ‖ ≤ ε * ‖ψ‖ := by
  have hsub : r.circuit.applyVec ψ - target.applyVec ψ =
      HilbertOperator.applyVec
        ((r.circuit.matrix : HilbertOperator layout.register) -
          (target : HilbertOperator layout.register)) ψ := by
    rw [HilbertOperator.sub_applyVec]
    rfl
  rw [hsub]
  calc ‖HilbertOperator.applyVec
          ((r.circuit.matrix : HilbertOperator layout.register) -
            (target : HilbertOperator layout.register)) ψ‖
      ≤ HilbertOperator.opNorm
          ((r.circuit.matrix : HilbertOperator layout.register) -
            (target : HilbertOperator layout.register)) * ‖ψ‖ :=
        HilbertOperator.norm_applyVec_le _ ψ
    _ ≤ ε * ‖ψ‖ := mul_le_mul_of_nonneg_right r.error_le (norm_nonneg ψ)
/-- Adjoint error is preserved after supplying the actual target-language adjoint implementation. -/
public def dagger {U : UnitaryOperator layout.register}
    (realized : ApproxRealization gates oracles layout U ε)
    (implementation : ExactRealization gates oracles layout (star realized.circuit.matrix)) :
    ApproxRealization gates oracles layout (star U) ε where
  circuit := implementation.circuit
  error_le := by
    rw [implementation.matrix_eq]
    change HilbertOperator.opNorm
      (star (realized.circuit.matrix : HilbertOperator layout.register) -
        star (U : HilbertOperator layout.register)) ≤ ε
    rw [← star_sub, HilbertOperator.opNorm_star]
    exact realized.error_le
@[simp] theorem dagger_circuit {U : UnitaryOperator layout.register}
    (realized : ApproxRealization gates oracles layout U ε)
    (implementation : ExactRealization gates oracles layout (star realized.circuit.matrix)) :
    (realized.dagger implementation).circuit = implementation.circuit := rfl
end ApproxRealization
end
end UnitaryCircuit
end QuantumAlg
end
