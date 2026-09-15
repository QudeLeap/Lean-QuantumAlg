/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Construction
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Queries
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Power.Laws
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Power.Coordinates
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Util.FinPow

/-!
# The complete elementary amplitude-estimation operator

At every width the actual program applies the original phase Hadamards and
inverse QFT around a source power determined only by the original phase
value. The separate work value does not select that power. When no extra
work system is present, a value-preserving width equality identifies the
full operator with the independent source's mathematical QPE target.
-/

namespace QuantumAlg.AmplitudeEstimation.Elementary

noncomputable section

/-- The entire physical program has this full-space matrix, at every phase width. -/
theorem program_matrix {n : Nat} (t : Nat) (U : UnitaryOperator (Qubits n))
    (good : NormalizedVector (Qubits n)) :
    (program t U good).matrix =
      let powers : UnitaryOperator (Qubits (totalQubits t n)) :=
        qpeExponentOp (phaseWidth t n)
          (U * (ZeroReflection.zeroReflectionOperator n *
            (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))
          (fun phase => (originalPhase t n phase).val)
      let initial : UnitaryOperator (Qubits (totalQubits t n)) :=
        UnitaryOperator.tensor (1 : UnitaryOperator (Qubits (phaseWidth t n))) U
      (phaseReadout t n).matrix * powers * (phaseHadamards t n).matrix * initial := by
  dsimp only
  apply Subtype.ext
  rw [program, UnitaryCircuit.seq_matrix, UnitaryCircuit.seq_matrix,
    UnitaryCircuit.seq_matrix, ladder_matrix, preparation_matrix]
  rfl

/-- No absent work position changes the value of any existing basis coordinate. -/
def unextendedBasisEquiv (t n : Nat) (empty : helperWidth t n = 0) :
    Fin (2 ^ totalQubits t n) ≃ Fin (2 ^ (t + n)) :=
  finCongr (congrArg (fun width : Nat => 2 ^ width)
    (by simp only [totalQubits, phaseWidth, empty, Nat.add_zero]))

private theorem originalPhase_val_of_noHelper {t n : Nat} (empty : helperWidth t n = 0)
    (phase : Fin (2 ^ phaseWidth t n)) :
    (originalPhase t n phase).val = phase.val := by
  rw [originalPhase, prodEquiv_symm_fst_val]
  have denominator : 2 ^ helperWidth t n = 1 := by rw [empty, pow_zero]
  exact (congrArg (fun divisor : Nat => phase.val / divisor) denominator).trans
    (Nat.div_one phase.val)

private theorem reindex_qubits_self {width : Nat} (same : 2 ^ width = 2 ^ width)
    (operator : UnitaryOperator (Qubits width)) :
    UnitaryOperator.reindex (finCongr same) operator = operator := by
  apply Subtype.ext
  rfl

private theorem reindex_width_family (t a b : Nat) (same : a = b)
    (family : (width : Nat) → UnitaryOperator (Qubits (t + width))) :
    UnitaryOperator.reindex (R := Qubits (t + a)) (S := Qubits (t + b))
      (finCongr (congrArg (fun width : Nat => 2 ^ (t + width)) same)) (family a) =
        family b := by
  subst b
  exact reindex_qubits_self _ _

private theorem assembled_noHelper (t n work : Nat) (empty : work = 0)
    (source preparation : UnitaryOperator (Qubits n)) :
    UnitaryOperator.reindex (R := Qubits ((t + work) + n)) (S := Qubits (t + n))
      (finCongr (congrArg (fun width : Nat => 2 ^ width)
        (by rw [empty, Nat.add_zero])))
      (UnitaryOperator.reindex (R := Qubits (t + (work + n)))
          (S := Qubits ((t + work) + n))
          (finCongr (congrArg (fun width : Nat => 2 ^ width) (Nat.add_assoc t work n).symm))
          (qpeReadoutFullCircuit t (work + n)).matrix *
        qpeControlledPowerOp (t + work) source *
        UnitaryOperator.reindex (R := Qubits (t + (work + n)))
          (S := Qubits ((t + work) + n))
          (finCongr (congrArg (fun width : Nat => 2 ^ width) (Nat.add_assoc t work n).symm))
          (qpePreparationCircuit t (work + n)).matrix *
        UnitaryOperator.tensor (1 : UnitaryOperator (Qubits (t + work))) preparation) =
      (qpeCircuit t source).matrix *
        UnitaryOperator.tensor (1 : UnitaryOperator (Qubits t)) preparation := by
  subst work
  rw [reindex_qubits_self (width := t + n)]
  rw [reindex_width_family t (0 + n) n (Nat.zero_add n)
    (fun width => (qpeReadoutFullCircuit t width).matrix)]
  rw [reindex_width_family t (0 + n) n (Nat.zero_add n)
    (fun width => (qpePreparationCircuit t width).matrix)]
  rw [qpeCircuit_matrix]
  simp only [Nat.add_zero]

/-- On the admitted width branch the actual full operator equals the original QPE target.
The hypothesis is an internal layout fact derived from the original validity domain. -/
theorem program_matrix_of_noHelper {n : Nat} (t : Nat) (empty : helperWidth t n = 0)
    (U : UnitaryOperator (Qubits n)) (good : NormalizedVector (Qubits n)) :
    UnitaryOperator.reindex (unextendedBasisEquiv t n empty) (program t U good).matrix =
      (qpeCircuit t (U * (ZeroReflection.zeroReflectionOperator n *
        (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good)))).matrix *
          UnitaryOperator.tensor (1 : UnitaryOperator (Qubits t)) U := by
  rw [program_matrix]
  have exponent : (fun phase : Fin (2 ^ phaseWidth t n) => (originalPhase t n phase).val) =
      Fin.val := funext (originalPhase_val_of_noHelper empty)
  rw [exponent]
  simp only [unextendedBasisEquiv, phaseReadout, phaseHadamards,
    UnitaryCircuit.reindex_matrix, phaseRegroupEquiv, totalQubits, phaseWidth]
  exact assembled_noHelper t n (helperWidth t n) empty
    (U * (ZeroReflection.zeroReflectionOperator n *
      (U.dagger * OrthogonalProjector.rankOnePhaseReflectionOp good))) U

end

end QuantumAlg.AmplitudeEstimation.Elementary
