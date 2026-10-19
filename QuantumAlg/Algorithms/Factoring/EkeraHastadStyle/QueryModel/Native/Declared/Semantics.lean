/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.Factoring.EkeraHastadStyle.QueryModel.Native.Declared.Program
import all QuantumAlg.Primitives.ShortDLP.BornProbability

/-!
# Source amplitudes of the declared short-DLP member

The original-width runtime member uses the fixed model-owned group query.
Its matrix coordinates are the same binary coordinates as the proved short-DLP
Born distribution, including the group-value workspace.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared

noncomputable section

/-- Placing the declared stage on the original bank preserves every complex
matrix entry in the source's binary basis. -/
lemma declaredMember_binaryMatrix_entry {ctx : RuntimeCtx .quantum} (N : Nat)
    (sameWires : ctx.quantumWires = (Native.layout N).wires)
    (interpretation : (ShortDLP.declaredModel N (Native.parameters N)).Interpretation)
    (parameter : (ParameterShape N).Value) (row column : ctx.register.Index) :
    (Native.declaredMember N sameWires parameter).matrix interpretation row column =
      (ShortDLP.DeclaredStage.circuit N (Native.parameters N)
        (parameterUnit parameter) (parameterTarget parameter)).binaryMatrix interpretation
          (Native.basisEquiv N sameWires row)
          (Native.basisEquiv N sameWires column) := by
  rw [← Native.declaredBasisEquiv_eq_basisEquiv N sameWires]
  rw [Native.declaredMember_matrix,
    UnitaryCircuit.binaryMatrix_eq_reindex]
  simp only [UnitaryOperator.coe_reindex,
    Matrix.reindex_apply, Matrix.submatrix_apply]
  exact congrArg₂
    (fun left right =>
      (ShortDLP.DeclaredStage.circuit N (Native.parameters N)
        (parameterUnit parameter) (parameterTarget parameter)).matrix interpretation left right)
    (by simp only [Native.declaredBasisEquiv, Equiv.trans_apply,
        Equiv.symm_apply_apply])
    (by simp only [Native.declaredBasisEquiv, Equiv.trans_apply,
        Equiv.symm_apply_apply])

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel.Native.Declared
