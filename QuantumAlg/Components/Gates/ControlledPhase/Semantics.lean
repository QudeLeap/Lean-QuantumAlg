/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Components.Gates.ControlledPhase.Placement
import all QuantumAlg.Components.Gates.ControlledPhase.Placement
import all QuantumAlg.Components.Gates.ControlledPhase.Construction
import all QuantumAlg.Components.Gates.ControlledPhase.Operator
import all QuantumAlg.Components.GateModel.Algorithm.Permutation
import all QuantumAlg.Core.Base.Gate.Placement.Canonical
import all QuantumAlg.Core.Base.UnitaryCircuit
public import QuantumAlg.Core.Base.UnitaryCircuit.Realization
import all QuantumAlg.Core.Base.Layout.Signature
import all QuantumAlg.Util.Complex

/-!
# Exact controlled phase from three phases and two CNOTs

Conjugating the middle phase by the two actual CNOT occurrences supplies the
parity-dependent phase. Together with the two original half phases, this is
exactly the addressed controlled-phase operator, including its global phase.
No auxiliary wire or additional oracle access occurs in the realization.
-/

namespace QuantumAlg.Gate.ControlledPhase

noncomputable section

private def phaseWeight (angle : Real) (bit : Fin 2) : Complex :=
  if bit = 0 then 1 else Complex.exp ((angle : Complex) * Complex.I)

private theorem cnot_twice (basis : layout.Basis) :
    AlgorithmGate.cnotPermutation (AlgorithmGate.cnotPermutation basis) = basis := by
  simp [AlgorithmGate.cnotPermutation]

private theorem conjugate_diagonal (register : Register)
    (permutation : Equiv.Perm register.Index) (involution : Function.Involutive permutation)
    (weight : register.Index → Complex) :
    ((UnitaryOperator.ofPerm (R := register) permutation).val * Matrix.diagonal weight) *
        (UnitaryOperator.ofPerm (R := register) permutation).val =
      Matrix.diagonal (fun basis => weight (permutation basis)) := by
  ext row column
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, UnitaryOperator.ofPerm_entry]
  rw [Finset.sum_eq_single (permutation row)]
  · rw [involution]
    by_cases same : row = column <;> simp [same]
  · intro other _ different
    simp [Ne.symm different]
  · simp

private theorem target_diagonal (angle : Real) :
    (operator angle : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis => qftControlledPhaseFactor (n := 2) 0 1 angle
        (QuantumSignature.qubitsIndexEquiv 2 basis)) := by
  ext row column
  change (Matrix.diagonal (qftControlledPhaseFactor (n := 2) 0 1 angle))
    (QuantumSignature.qubitsIndexEquiv 2 row) (QuantumSignature.qubitsIndexEquiv 2 column) = _
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq]

private theorem phase_product (angle : Real) (basis : layout.Basis) :
    phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) *
      (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin 2))) =
        qftControlledPhaseFactor (n := 2) 0 1 angle
          (QuantumSignature.qubitsIndexEquiv 2 basis) := by
  have pair (first second : Fin 2) :
      phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation ![first, second]) (1 : Fin 2)) *
        (phaseWeight (angle / 2) second * phaseWeight (angle / 2) first) =
          qftControlledPhaseFactor (n := 2) 0 1 angle
            (QuantumSignature.qubitsIndexEquiv 2 ![first, second]) := by
    rw [AlgorithmGate.cnotPermutation_pair]
    fin_cases first <;> fin_cases second
    · change (1 : Complex) * (1 * 1) = 1
      simp
    · change Complex.exp ((-(angle / 2) : Real) * Complex.I) *
        (Complex.exp ((angle / 2 : Real) * Complex.I) * 1) = 1
      simp only [mul_one]
      simpa only [Complex.ofReal_neg, neg_mul] using exp_neg_I_mul_exp_I (angle / 2)
    · change Complex.exp ((-(angle / 2) : Real) * Complex.I) *
        (1 * Complex.exp ((angle / 2 : Real) * Complex.I)) = 1
      simp only [one_mul]
      simpa only [Complex.ofReal_neg, neg_mul] using exp_neg_I_mul_exp_I (angle / 2)
    · change (1 : Complex) * (Complex.exp ((angle / 2 : Real) * Complex.I) *
        Complex.exp ((angle / 2 : Real) * Complex.I)) =
          Complex.exp ((angle : Real) * Complex.I)
      rw [one_mul, ← Complex.exp_add]
      congr 1
      push_cast
      ring
  have coordinates : basis = ![basis 0, basis 1] := by
    funext index
    fin_cases index <;> rfl
  rw [coordinates]
  exact pair (basis (0 : Fin 2)) (basis (1 : Fin 2))

private theorem word_diagonal (oracles : OracleModel) (angle : Real) :
    ((circuit oracles angle).matrix : HilbertOperator layout.register) =
      Matrix.diagonal (fun basis =>
        phaseWeight (-(angle / 2)) ((AlgorithmGate.cnotPermutation basis) (1 : Fin 2)) *
          (phaseWeight (angle / 2) (basis (1 : Fin 2)) * phaseWeight (angle / 2) (basis (0 : Fin
            2)))) := by
  simp only [circuit, UnitaryCircuit.macroCall_matrix, UnitaryCircuit.seq_matrix,
    Submonoid.coe_mul, UnitaryCircuit.native_matrix,
    GateModel.Application.gateApplication_canonical_operator, AlgorithmGate.cnot_operator_ofPerm]
  simp only [controlledPhase_single_phase_diagonal]
  rw [← mul_assoc, ← mul_assoc,
    conjugate_diagonal layout.register AlgorithmGate.cnotPermutation cnot_twice]
  rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
  rfl

/-- The complete five-gate native word realizes the original target with exact phase. -/
public theorem controlledPhase_circuit_matrix (oracles : OracleModel) (angle : Real) :
    (circuit oracles angle).matrix = operator angle := by
  apply Subtype.ext
  rw [word_diagonal, target_diagonal]
  exact congrArg Matrix.diagonal (funext (phase_product angle))

/-- The exact realization carries the actual default-model expansion and its own resource trace. -/
public def realization (oracles : OracleModel) (angle : Real) :
    UnitaryCircuit.ExactRealization AlgorithmGate.model oracles layout (operator angle) where
  circuit := circuit oracles angle
  matrix_eq := controlledPhase_circuit_matrix oracles angle

end

end QuantumAlg.Gate.ControlledPhase
