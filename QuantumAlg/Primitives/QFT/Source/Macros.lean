/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source
import all QuantumAlg.Primitives.QFT.Source.Primitive
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement.Macros

/-! # Native Fourier source instructions do not rely on descriptive macro annotations -/

namespace QuantumAlg.QuantumFourierTransform.Source
noncomputable section

private lemma phasePrefix_macroCount (oracles : OracleModel) (name : String)
    (n count : Nat) (bounded : count ≤ n) :
    (phasePrefix oracles n count bounded).macroCount name = 0 := by
  induction count with
  | zero => rfl
  | succ count ih =>
      rw [phasePrefix, UnitaryCircuit.macroCount_seq, ih]
      rfl

private lemma noSwap_macroCount (oracles : OracleModel) (name : String) (n : Nat) :
    (noSwap oracles n).macroCount name = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      rw [noSwap, UnitaryCircuit.macroCount_seq, UnitaryCircuit.macroCount_seq,
        phaseLayer, phasePrefix_macroCount, tailLayer, UnitaryCircuit.placeAt_macroCount, ih]
      rfl

private lemma reversePrefix_macroCount (oracles : OracleModel) (name : String)
    (n count : Nat) (bounded : count ≤ n / 2) :
    (reversePrefix oracles n count bounded).macroCount name = 0 := by
  exact reversePrefix_macroCount_zero oracles name n count bounded

/-- The natural-gate source has actual native instructions and no descriptive source macros. -/
public lemma qftSource_circuit_macroCount (oracles : OracleModel) (name : String) (n : Nat) :
    (circuit oracles n).macroCount name = 0 := by
  rw [circuit, UnitaryCircuit.macroCount_seq, noSwap_macroCount,
    bitReverse, reversePrefix_macroCount]

end
end QuantumAlg.QuantumFourierTransform.Source
