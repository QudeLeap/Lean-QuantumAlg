/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Primitives.FTQC.CliffordLayers
import all QuantumAlg.Analysis.FTQC.CliffordT.Word
import all QuantumAlg.Components.Kets
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.QubitPrimitive
import all QuantumAlg.Components.QubitPrimitive.Operator
import all QuantumAlg.Core.Base.WireAddress
import all QuantumAlg.Components.BinaryLabelEncoding
import all QuantumAlg.Core.Base
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Gate.Unitary
import all QuantumAlg.Util.FinPow
import all QuantumAlg.Util.Matrix.Diagonal
import all QuantumAlg.Util.Sum
import all QuantumAlg.Core.Base.UnitaryCircuit.Construction
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import Mathlib.Tactic

/-!
# Seven-T Toffoli with four T stages

The phase polynomial is a+b+c-(a xor b)-(b xor c)+(a xor b xor c)-(a xor c).
It equals 4abc modulo eight. Hadamard conjugation of its target gives Toffoli.
The seven-T, six-CNOT construction follows Nielsen and Chuang, Figure 4.9
(citation-only) and the resource construction discussed by Amy et al.,
MeetintheMiddlev4.tex:586-590.
Each T-dagger is explicitly expanded to T S S S.
-/

public section

namespace QuantumAlg.FTQC

open CliffordT UnitaryCircuit Gate

open NormalizedVector

noncomputable section

/-- Native Toffoli specification: controls zero and one, target two. -/
def toffoliOp : UnitaryOperator (Qubits 3) :=
  QubitPrimitive.operator (.toffoli 0 1 2 (by decide) (by decide) (by decide))

/-- The diagonal parity network inside the Toffoli construction. -/
def parity7T (oracles : OracleModel) : CliffordCircuit oracles 3 := blocks
  [layer3 oracles [.t] [.t] [.t],
    cx oracles 1 2 (by decide), cx oracles 0 1 (by decide),
    layer3 oracles [] tDaggerWord tDaggerWord,
    cx oracles 0 1 (by decide), cx oracles 0 2 (by decide),
    layer3 oracles [] [] [.t], cx oracles 1 2 (by decide),
    layer3 oracles [] [] tDaggerWord, cx oracles 0 2 (by decide)]

/-- Seven T leaves, six CNOT leaves, and two target Hadamards. -/
def toffoli7TCircuit (oracles : OracleModel) : CliffordCircuit oracles 3 := blocks
  [layer3 oracles [] [] [.h], parity7T oracles, layer3 oracles [] [] [.h]]

namespace Toffoli7TProof

lemma tOp_entries : (TOp : HilbertOperator (Qubits 1)) =
    !![1, 0; 0, (Real.sqrt 2 : ℂ) / 2 + (Real.sqrt 2 : ℂ) / 2 * Complex.I] := by
  change !![1, 0; 0, Complex.exp (((Real.pi / 4 : ℝ) : ℂ) * Complex.I)] = _
  rw [Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four]
  norm_num

lemma tOp_diagonal : (TOp : HilbertOperator (Qubits 1)) =
    Matrix.diagonal ![1, (Real.sqrt 2 : ℂ) / 2 + (Real.sqrt 2 : ℂ) / 2 * Complex.I] := by
  rw [tOp_entries]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

lemma sOp_diagonal : (SOp : HilbertOperator (Qubits 1)) =
    Matrix.diagonal ![1, Complex.I] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [SOp]

lemma sqrtTwo_sq : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
  norm_cast
  norm_num

lemma sqrtTwo_four : (Real.sqrt 2 : ℂ) ^ 4 = 4 := by
  calc
    (Real.sqrt 2 : ℂ) ^ 4 = ((Real.sqrt 2 : ℂ) ^ 2) ^ 2 := by ring
    _ = 4 := by rw [sqrtTwo_sq]; norm_num

lemma sqrtTwo_inv_sq : ((Real.sqrt 2 : ℂ)⁻¹) ^ 2 = (2 : ℂ)⁻¹ := by
  rw [inv_pow, sqrtTwo_sq]

lemma sqrtTwo_cube_mul_inv :
    (Real.sqrt 2 : ℂ) ^ 3 * (Real.sqrt 2 : ℂ)⁻¹ = 2 := by
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    norm_cast
    positivity
  calc
    (Real.sqrt 2 : ℂ) ^ 3 * (Real.sqrt 2 : ℂ)⁻¹ =
        (Real.sqrt 2 : ℂ) ^ 2 * ((Real.sqrt 2 : ℂ) * (Real.sqrt 2 : ℂ)⁻¹) := by ring
    _ = (Real.sqrt 2 : ℂ) ^ 2 := by rw [mul_inv_cancel₀ hs, mul_one]
    _ = 2 := sqrtTwo_sq

end Toffoli7TProof

end

end QuantumAlg.FTQC
