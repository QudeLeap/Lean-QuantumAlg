/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.Oracle.Declared

/-!
# Exact oracle graph on a zero workspace

One model-owned query loads the selected group value into the original
workspace when that workspace starts in its zero basis state.
-/

namespace QuantumAlg.ShortDLP

noncomputable section

lemma oracleTarget_zero {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    oracleTarget encoding g x a b 0 =
      encodeUnit encoding (oracleValue g x a.val b.val) := by
  apply Fin.ext
  simp [oracleTarget]

/-- A loaded workspace is zero exactly when its input label was the encoded
group value. This is the inverse row convention of the permutation matrix. -/
lemma oracleTarget_eq_zero_iff {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell))
    (workspace : Fin (2 ^ params.workspaceBits)) :
    oracleTarget encoding g x a b workspace = 0 ↔
      workspace = encodeUnit encoding (oracleValue g x a.val b.val) := by
  constructor
  · intro h
    have htwice := congrArg (oracleTarget encoding g x a b) h
    simpa [oracleTarget, Nat.xor_assoc] using htwice
  · intro h
    subst workspace
    apply Fin.ext
    simp [oracleTarget]

/-- The actual declared query takes each zero-workspace input ket to the
corresponding source group-operation graph ket. -/
lemma declaredCircuit_binaryMatrix_apply_zero (gates : GateModel)
    {N : Nat} {params : RegisterParameters}
    (encoding : UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (a : Fin (2 ^ firstBits params)) (b : Fin (2 ^ params.ell)) :
    ((declaredCircuit gates N params g x).binaryMatrix
      (declaredInterpretation encoding)).apply
        (NormalizedVector.ket (tripleEquiv params ((a, b), 0))) =
      NormalizedVector.ket
        (tripleEquiv params
          ((a, b), encodeUnit encoding (oracleValue g x a.val b.val))) := by
  rw [declaredCircuit_binaryMatrix_apply_ket]
  simp only [oraclePerm, Equiv.coe_fn_mk, oracleTarget_zero]

end

end QuantumAlg.ShortDLP
