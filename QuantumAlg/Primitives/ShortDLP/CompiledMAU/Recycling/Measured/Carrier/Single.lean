/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Control

/-!
# Actual H and stored-phase matrices on the complete measured arithmetic carrier

The native physical control acts beside identity on every canonical unit
seed. Exact physical-label ket action supplies the full rectangular matrix
identities; the arbitrary external-reference extension is then functorial
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier

noncomputable section

open MAU.Multiplication.Gidney.Measured
open NormalizedVector

private lemma tensor_column_sum {R S : Register}
    (embedding : ((Qubits 1).prod S).Index ↪ R.Index)
    (operator : UnitaryOperator (Qubits 1)) (row : R.Index)
    (column : ((Qubits 1).prod S).Index) :
    (∑ index : ((Qubits 1).prod S).Index, if embedding index = row then
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator S)) index column else 0) =
        operator 0 column.1 * (NormalizedVector.ket (embedding (0, column.2))).vec row +
          operator 1 column.1 * (NormalizedVector.ket (embedding (1, column.2))).vec row := by
  classical
  change (∑ index : Fin 2 × S.Index, if embedding index = row then
    (operator : HilbertOperator (Qubits 1)) index.1 column.1 *
      (if index.2 = column.2 then 1 else 0) else 0) = _
  rw [Fintype.sum_prod_type]
  have seedSum (bit : Fin 2) :
      (∑ seed : S.Index, if embedding (bit, seed) = row then
        (operator : HilbertOperator (Qubits 1)) bit column.1 *
          (if seed = column.2 then 1 else 0) else 0) =
      if embedding (bit, column.2) = row then operator bit column.1 else 0 := by
    rw [Finset.sum_eq_single column.2]
    · simp
    · intro seed _ different
      simp [different]
    · intro absent
      exact False.elim (absent (Finset.mem_univ _))
  simp_rw [seedSum]
  rw [Fin.sum_univ_two]
  simp [NormalizedVector.ket_apply, eq_comm]

variable {width : Nat} (modulus : BitVec width) [NeZero modulus.toNat]

private lemma hadamard_row_zero (bit : Fin 2) : Gate.HOp 0 bit = invSqrt2 := by
  fin_cases bit <;> simp [Gate.HOp]

private lemma hadamard_row_one (bit : Fin 2) :
    Gate.HOp 1 bit = if bit = 0 then invSqrt2 else -invSqrt2 := by
  fin_cases bit <;> simp [Gate.HOp]

/-- Native H preserves the complete clean arithmetic carrier with its exact input-one phase. -/
lemma physical_hadamard_intertwines (environment : OracleModel.empty.Interpretation) :
    ((Placement.physicalSingle width Gate.HOp).matrix environment :
        HilbertOperator (Physical.qubits width).toQuantum.register) *
      BasisEmbedding.matrix (embedding modulus) =
    BasisEmbedding.matrix (embedding modulus) *
      (UnitaryOperator.prodTensor Gate.HOp
        (1 : UnitaryOperator (Recycling.Carrier.units modulus.toNat)) :
          HilbertOperator (Recycling.Carrier.full modulus.toNat)) := by
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  rw [tensor_column_sum]
  rcases column with ⟨bit, seed⟩
  have action := Physical.cleanLabel_hadamard width (finTwoEquiv bit) (unitWord modulus seed)
    .empty environment
  have actual := congrArg
    (fun vector : HilbertVector (Physical.qubits width).toQuantum.register => vector row) action
  change HilbertOperator.applyVec ((Placement.physicalSingle width Gate.HOp).matrix environment)
    (NormalizedVector.ket (embedding modulus (bit, seed))).vec row = _ at actual
  rw [HilbertOperator.applyVec_ket] at actual
  rw [hadamard_row_zero, hadamard_row_one]
  fin_cases bit
  · change _ = invSqrt2 *
      ((1 : ℂ) * (NormalizedVector.ket (embedding modulus (0, seed))).vec row +
        (NormalizedVector.ket (embedding modulus (1, seed))).vec row) at actual
    change _ = invSqrt2 * (NormalizedVector.ket (embedding modulus (0, seed))).vec row +
      invSqrt2 * (NormalizedVector.ket (embedding modulus (1, seed))).vec row
    simpa only [one_mul, mul_add] using actual
  · change _ = invSqrt2 *
      ((-1 : ℂ) * (NormalizedVector.ket (embedding modulus (1, seed))).vec row +
        (NormalizedVector.ket (embedding modulus (0, seed))).vec row) at actual
    change _ = invSqrt2 * (NormalizedVector.ket (embedding modulus (0, seed))).vec row +
      (-invSqrt2) * (NormalizedVector.ket (embedding modulus (1, seed))).vec row
    linear_combination actual

/-- Any actual feedback phase preserves both original control/unit columns with the exact phase. -/
lemma physical_phase_intertwines (angle : Real)
    (environment : OracleModel.empty.Interpretation) :
    ((Placement.physicalSingle width (phaseGateOp angle)).matrix environment :
        HilbertOperator (Physical.qubits width).toQuantum.register) *
      BasisEmbedding.matrix (embedding modulus) =
    BasisEmbedding.matrix (embedding modulus) *
      (UnitaryOperator.prodTensor (phaseGateOp angle)
        (1 : UnitaryOperator (Recycling.Carrier.units modulus.toNat)) :
          HilbertOperator (Recycling.Carrier.full modulus.toNat)) := by
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  rw [tensor_column_sum]
  rcases column with ⟨bit, seed⟩
  have action := Physical.cleanLabel_phase width (finTwoEquiv bit) (unitWord modulus seed)
    angle .empty environment
  have actual := congrArg
    (fun vector : HilbertVector (Physical.qubits width).toQuantum.register => vector row) action
  change HilbertOperator.applyVec
    ((Placement.physicalSingle width (phaseGateOp angle)).matrix environment)
      (NormalizedVector.ket (embedding modulus (bit, seed))).vec row = _ at actual
  rw [HilbertOperator.applyVec_ket] at actual
  fin_cases bit
  · change _ = (1 : ℂ) * (NormalizedVector.ket (embedding modulus (0, seed))).vec row at actual
    change _ = (1 : ℂ) * (NormalizedVector.ket (embedding modulus (0, seed))).vec row +
      (0 : ℂ) * (NormalizedVector.ket (embedding modulus (1, seed))).vec row
    simpa only [one_mul, zero_mul, add_zero] using actual
  · change _ = Complex.exp ((angle : Complex) * Complex.I) *
      (NormalizedVector.ket (embedding modulus (1, seed))).vec row at actual
    change _ = (0 : ℂ) * (NormalizedVector.ket (embedding modulus (0, seed))).vec row +
      Complex.exp ((angle : Complex) * Complex.I) *
        (NormalizedVector.ket (embedding modulus (1, seed))).vec row
    simpa only [zero_mul, zero_add] using actual

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured.Carrier
