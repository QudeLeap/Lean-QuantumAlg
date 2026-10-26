/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Core.Base.Gate.Unitary
public import QuantumAlg.Components.Gates.SingleQubit.Diagonal
import all QuantumAlg.Components.Gates.SingleQubit.Diagonal
public import QuantumAlg.Core.Base.UnitaryCircuit.Leaf
import all QuantumAlg.Core.Base.UnitaryCircuit.Leaf
public import QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.ResourcePool
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Util.Complex

/-!
# Native scalar phase

The exact scalar phase is retained before coherent control
[WBA11, h2.arxiv2.tex:835]. This gate uses the convention `exp (-i θ) • I`
and contributes one native one-qubit event on a real selected wire.
The mathematical scalar operator remains available at every register width.
-/

section

namespace QuantumAlg

noncomputable section

/-- The certified scalar operator `exp (-i θ) • I` on any register. -/
public def globalPhaseOp {R : Register} (θ : ℝ) : UnitaryOperator R :=
  UnitaryOperator.ofMatrix (Complex.exp (-(Complex.I * (θ : ℂ))) •
    (1 : HilbertOperator R)) (by
      rw [Matrix.mem_unitaryGroup_iff, star_smul, smul_mul_smul_comm]
      have h : Complex.exp (-(Complex.I * (θ : ℂ))) *
          starRingEnd ℂ (Complex.exp (-(Complex.I * (θ : ℂ)))) = 1 := by
        rw [mul_comm Complex.I, conj_exp_neg_I]
        exact exp_neg_I_mul_exp_I θ
      simp [h])

/-- Raw scalar formula for the certified global phase. -/
@[simp] public lemma globalPhaseOp_coe {R : Register} (θ : ℝ) :
    ((globalPhaseOp (R := R) θ) : HilbertOperator R) =
      Complex.exp (-(Complex.I * (θ : ℂ))) • 1 := by rfl

/-- Execute the one-qubit scalar operator on a selected physical qubit.
Its extension is a scalar on the complete register, including every spectator. -/
public def globalPhaseAt {n : Nat} (layout : QubitLayout n) (oracles : OracleModel)
    (θ : ℝ) (target : Fin n) : UnitaryCircuit AlgorithmGate.model oracles layout.toQuantum :=
  Gate.singleQubitAt layout.toQuantum oracles (globalPhaseOp θ) target rfl

/-- The selected one-qubit instruction retains the exact ambient scalar phase. -/
public lemma globalPhaseAt_matrix {n : Nat} (layout : QubitLayout n) (oracles : OracleModel)
    (θ : ℝ) (target : Fin n) (environment : oracles.Interpretation) :
    (globalPhaseAt layout oracles θ target).matrix environment = globalPhaseOp θ := by
  apply Subtype.ext
  ext row column
  refine (Gate.singleQubitAt_diagonal_entry layout oracles (environment := environment)
    (globalPhaseOp θ)
    (fun _ => Complex.exp (-(Complex.I * (θ : ℂ)))) (by
      intro i j
      simp only [globalPhaseOp_coe, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
      split <;> simp_all) target row column).trans ?_
  simp only [globalPhaseOp_coe, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]
  change (if row = column then Complex.exp (-(Complex.I * (θ : ℂ))) else 0) =
    Complex.exp (-(Complex.I * (θ : ℂ))) * (if row = column then 1 else 0)
  split <;> simp_all

/-- Scalar phase is one default-model one-qubit event, including at zero angle. -/
public lemma globalPhaseAt_eventCost {n : Nat} (layout : QubitLayout n)
    (oracles : OracleModel) (θ : ℝ) (target : Fin n) :
    (globalPhaseAt layout oracles θ target).eventCost =
      ResourcePool.singleton (model := .quantum AlgorithmGate.model oracles)
        (.gate .singleQubit) := by
  rw [globalPhaseAt, Gate.singleQubitAt_eventCost]

end
end QuantumAlg

end
