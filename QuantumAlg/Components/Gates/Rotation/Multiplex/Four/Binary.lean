/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Gates.Rotation.Multiplex.Four.Placement
import all QuantumAlg.Components.Gates.Rotation.Multiplex.Binary

/-!
# Four binary phase branches with a preserved source suffix

The exact matrix is projected into its original selector, selector, phase,
source coordinates. The binary view introduces no executable operation.
-/

namespace QuantumAlg.Gate.Rotation.Multiplex.Four
noncomputable section

private def binaryWeight (width : Nat) (a00 a01 a10 a11 : ℝ)
    (label : Fin (2 ^ (1 + (1 + (1 + width))))) : ℂ :=
  let basis := (QuantumSignature.qubitsIndexEquiv (1 + (1 + (1 + width)))).symm label
  let outer : Fin 2 := basis (prefixPositions width 0)
  let inner : Fin 2 := basis (prefixPositions width 1)
  let phase : Fin 2 := basis (prefixPositions width 2)
  weight (if outer = 0 then (if inner = 0 then a00 else a01)
    else (if inner = 0 then a10 else a11)) phase

private lemma binaryWeight_coordinates (width : Nat) (a00 a01 a10 a11 : ℝ)
    (outer inner phase : Fin 2) (source : Fin (2 ^ width)) :
    binaryWeight width a00 a01 a10 a11
      (prodEquiv (outer, prodEquiv (inner, prodEquiv (phase, source)))) =
      weight (if outer = 0 then (if inner = 0 then a00 else a01)
        else (if inner = 0 then a10 else a11)) phase := by
  have first := firstDecoded (1 + width) outer inner (prodEquiv (phase, source))
  have second := secondDecoded (1 + width) outer inner (prodEquiv (phase, source))
  have third := (BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := 1 + (1 + width)) outer
    (prodEquiv (inner, prodEquiv (phase, source)))
    (Fin.natAdd 1 (0 : Fin (1 + width)))).trans
      (secondDecoded width inner phase source)
  exact congrArg₂ (fun angle bit => weight angle bit)
    (congrArg₂ (fun a b : Fin 2 => if a = 0 then (if b = 0 then a00 else a01)
      else (if b = 0 then a10 else a11)) first second) third

/-- Four independently specified rotations are the exact branches of the actual native word. -/
lemma fourRotation_prefix_binaryMatrix (oracles : OracleModel) (width : Nat)
    (a00 a01 a10 a11 : ℝ) (environment : oracles.Interpretation) :
    let branch := fun zero one : ℝ =>
      HilbertOperator.tensor HilbertOperator.proj0
        (HilbertOperator.tensor (rotZStdOp zero : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits width))) +
      HilbertOperator.tensor HilbertOperator.proj1
        (HilbertOperator.tensor (rotZStdOp one : HilbertOperator (Qubits 1))
          (1 : HilbertOperator (Qubits width)))
    (((onPrefix oracles width a00 a01 a10 a11).binaryMatrix environment) :
      HilbertOperator (Qubits (1 + (1 + (1 + width))))) =
      HilbertOperator.tensor HilbertOperator.proj0 (branch a00 a01) +
        HilbertOperator.tensor HilbertOperator.proj1 (branch a10 a11) := by
  dsimp only
  have diagonal :
      (((onPrefix oracles width a00 a01 a10 a11).binaryMatrix environment) :
        HilbertOperator (Qubits (1 + (1 + (1 + width))))) =
        Matrix.diagonal (binaryWeight width a00 a01 a10 a11) := by
    rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex, fourRotation_prefix_matrix]
    exact Matrix.submatrix_diagonal
      (fun basis :
        (QuantumSignature.qubits (1 + (1 + (1 + width)))).canonicalPlacement.layout.Basis =>
        let outer : Fin 2 := basis (prefixPositions width 0)
        let inner : Fin 2 := basis (prefixPositions width 1)
        let phase : Fin 2 := basis (prefixPositions width 2)
        weight (if outer = 0 then (if inner = 0 then a00 else a01)
          else (if inner = 0 then a10 else a11)) phase)
      (QuantumSignature.qubitsIndexEquiv (1 + (1 + (1 + width)))).symm
      (QuantumSignature.qubitsIndexEquiv (1 + (1 + (1 + width)))).symm.injective
  rw [diagonal]
  ext row column
  obtain ⟨⟨a, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + (1 + width))).surjective row
  obtain ⟨⟨b, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + width)).surjective rest
  obtain ⟨⟨p, x⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective rest
  obtain ⟨⟨c, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + (1 + width))).surjective column
  obtain ⟨⟨d, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + width)).surjective rest
  obtain ⟨⟨q, y⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective rest
  simp only [Matrix.diagonal_apply, Equiv.apply_eq_iff_eq, binaryWeight_coordinates,
    HilbertOperator.tensor_apply, Equiv.symm_apply_apply, Matrix.add_apply]
  fin_cases a <;> fin_cases b <;> fin_cases p <;> fin_cases c <;> fin_cases d <;> fin_cases q <;>
    by_cases same : x = y <;>
    simp [HilbertOperator.proj0, HilbertOperator.proj1, rotZStdOp, rotZOp, weight,
      same, Matrix.one_apply]

end
end QuantumAlg.Gate.Rotation.Multiplex.Four
