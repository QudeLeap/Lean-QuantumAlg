/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates
import all QuantumAlg.Components.Gates.Operator
import all QuantumAlg.Components.Gates.Rotation.Operator
import all QuantumAlg.Core.Base.Gate.Unitary

/-!
# The phase-exact principal square root of Pauli X

This convention has eigenvalues one and i, and agrees with H S H. It squares
to X without a scalar phase. It is the standard square-root gate convention
of Nielsen and Chuang, Chapter 4.
-/

@[expose] public section

namespace QuantumAlg.Gate

noncomputable section

/-- Square root of X with eigenvalues one and i. -/
def sqrtXOp : UnitaryOperator (Qubits 1) :=
  UnitaryOperator.ofMatrix
    (!![(1 + Complex.I) / 2, (1 - Complex.I) / 2;
      (1 - Complex.I) / 2, (1 + Complex.I) / 2] : HilbertOperator (Qubits 1)) (by
      rw [Matrix.mem_unitaryGroup_iff]
      ext i j
      fin_cases i <;> fin_cases j <;>
        norm_num [Matrix.mul_apply, Matrix.star_apply, Complex.ext_iff,
          Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im])

lemma sqrtXOp_sq : sqrtXOp * sqrtXOp = XOp := by
  apply Subtype.ext
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [sqrtXOp, XOp, UnitaryOperator.ofPerm, Matrix.mul_apply,
      Complex.ext_iff, Complex.mul_re, Complex.mul_im, Complex.div_re, Complex.div_im]

end

end QuantumAlg.Gate
