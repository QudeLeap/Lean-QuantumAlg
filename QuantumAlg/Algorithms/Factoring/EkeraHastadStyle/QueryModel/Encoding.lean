/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.BornProbability

/-!
# Faithful oracle encodings preserve the exponent observation

The original complex amplitudes vanish outside the encoded unit image.
Summing that image identifies the same exponent-pair probability for any
faithful workspace encoding, including different target-register widths.
No execution, preparation replacement, or oracle resource equivalence is
asserted by this pure mathematical observation.
-/

namespace QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel

noncomputable section

/-- Marginalizing a faithful workspace encoding is the same as summing over
all group units; padding basis states contribute zero. -/
theorem pairBornProbability_eq_unit_sum
    {N : Nat} [NeZero N] {params : ShortDLP.RegisterParameters}
    (encoding : ShortDLP.UnitEncoding N params.workspaceBits)
    (g x : (ZMod N)ˣ)
    (pair : Fin (2 ^ ShortDLP.firstBits params) ×
      Fin (2 ^ params.ell)) :
    ShortDLP.BornProbability.pairBornProbability encoding g x pair =
      ∑ unit : (ZMod N)ˣ,
        ENNReal.ofReal
          (‖ShortDLP.BornProbability.circuitAmplitude encoding g x
            pair.1 pair.2 (ShortDLP.encodeUnit encoding unit)‖ ^ 2) := by
  classical
  unfold ShortDLP.BornProbability.pairBornProbability
  let embedding : (ZMod N)ˣ ↪ Fin (2 ^ params.workspaceBits) :=
    { toFun := ShortDLP.encodeUnit encoding
      inj' := ShortDLP.encodeUnit_injective encoding }
  calc
    (∑ workspace : Fin (2 ^ params.workspaceBits),
        ENNReal.ofReal
          (‖ShortDLP.BornProbability.circuitAmplitude encoding g x
            pair.1 pair.2 workspace‖ ^ 2)) =
      ∑ workspace ∈ (Finset.univ : Finset ((ZMod N)ˣ)).map embedding,
        ENNReal.ofReal
          (‖ShortDLP.BornProbability.circuitAmplitude encoding g x
            pair.1 pair.2 workspace‖ ^ 2) := by
      symm
      apply Finset.sum_subset (by simp)
      intro workspace _workspaceMember outside
      rw [ShortDLP.BornProbability.circuitAmplitude_eq_zero_of_not_oracleRange
        encoding g x pair.1 pair.2 workspace]
      · simp
      · intro a b workspaceEq
        apply outside
        apply Finset.mem_map.mpr
        exact ⟨ShortDLP.oracleValue g x a.val b.val, Finset.mem_univ _,
          workspaceEq.symm⟩
    _ = ∑ unit : (ZMod N)ˣ,
        ENNReal.ofReal
          (‖ShortDLP.BornProbability.circuitAmplitude encoding g x
            pair.1 pair.2 (ShortDLP.encodeUnit encoding unit)‖ ^ 2) := by
      rw [Finset.sum_map]
      rfl

/-- Two faithful workspace encodings with the same exponent dimensions induce
the same exponent-pair marginal, even when their workspace widths differ. -/
theorem pairBornProbability_encoding_independent
    {N : Nat} [NeZero N] (m ell : Nat) {leftBits rightBits : Nat}
    (leftEncoding : ShortDLP.UnitEncoding N leftBits)
    (rightEncoding : ShortDLP.UnitEncoding N rightBits)
    (g x : (ZMod N)ˣ)
    (pair : Fin (2 ^ (ell + m)) × Fin (2 ^ ell)) :
    ShortDLP.BornProbability.pairBornProbability
        (params := { m := m, ell := ell, workspaceBits := leftBits })
        leftEncoding g x pair =
      ShortDLP.BornProbability.pairBornProbability
        (params := { m := m, ell := ell, workspaceBits := rightBits })
        rightEncoding g x pair := by
  rw [pairBornProbability_eq_unit_sum,
    pairBornProbability_eq_unit_sum]
  apply Finset.sum_congr rfl
  intro unit _unitMember
  apply congrArg ENNReal.ofReal
  apply congrArg (fun value : Real => value ^ 2)
  apply congrArg norm
  unfold ShortDLP.BornProbability.circuitAmplitude
  simp only [ShortDLP.firstBits]
  apply Finset.sum_congr rfl
  intro a _aMember
  apply Finset.sum_congr rfl
  intro b _bMember
  by_cases equal : unit = ShortDLP.oracleValue g x a.val b.val
  · rw [if_pos (congrArg
        (ShortDLP.encodeUnit
          (params := { m := m, ell := ell, workspaceBits := leftBits })
          leftEncoding) equal),
      if_pos (congrArg
        (ShortDLP.encodeUnit
          (params := { m := m, ell := ell, workspaceBits := rightBits })
          rightEncoding) equal)]
  · rw [if_neg (fun encoded => equal
        (ShortDLP.encodeUnit_injective
          (params := { m := m, ell := ell, workspaceBits := leftBits })
          leftEncoding encoded)),
      if_neg (fun encoded => equal
        (ShortDLP.encodeUnit_injective
          (params := { m := m, ell := ell, workspaceBits := rightBits })
          rightEncoding encoded))]

end

end QuantumAlg.Factoring.EkeraHastadStyle.Canonical.OracleModel
