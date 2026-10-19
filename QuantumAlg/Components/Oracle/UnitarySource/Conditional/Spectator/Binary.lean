/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Oracle.UnitarySource.Conditional.Spectator.Coordinates
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Tensor.Basic

/-!
# Binary branches of source control around a resident phase wire

The spectator is preserved in the full matrix, without assumptions about its
initial state or its correlations with the source and selector.
-/

namespace QuantumAlg.UnitarySource.Conditional
noncomputable section

private lemma spectator_phase {width : Nat} (selector phase : Fin 2)
    (source : Fin (2 ^ width)) :
    spectatorBasis selector phase source (⟨1, by omega⟩ : Fin (1 + (1 + width))) = phase := by
  have outer := BinaryBasis.bigEndianEquiv_prod_right
    (leftWidth := 1) (rightWidth := 1 + width) selector (prodEquiv (phase, source)) 0
  have inner := BinaryBasis.bigEndianEquiv_prod_left
    (leftWidth := 1) (rightWidth := width) phase source 0
  have first : (BinaryBasis.bigEndianEquiv 1).symm phase 0 = phase := by
    fin_cases phase <;> rfl
  exact outer.trans (inner.trans first)

private lemma complement_eq_iff {width : Nat} (s t p q : Fin 2)
    (x y : Fin (2 ^ width)) :
    (layout (1 + width)).restrictComplementBasis (Finset.univ.map (spectatorPositions width))
        (spectatorBasis s p x) =
      (layout (1 + width)).restrictComplementBasis (Finset.univ.map (spectatorPositions width))
        (spectatorBasis t q y) ↔ p = q := by
  constructor
  · intro same
    have values := congrFun same
      ⟨(⟨1, by omega⟩ : Fin (1 + (1 + width))),
        Finset.mem_compl.mpr (spectator_not_selected width)⟩
    change spectatorBasis s p x (⟨1, by omega⟩ : Fin (1 + (1 + width))) =
      spectatorBasis t q y (⟨1, by omega⟩ : Fin (1 + (1 + width))) at values
    apply Fin.ext
    have numeric := congrArg Fin.val values
    exact (congrArg Fin.val (spectator_phase s p x)).symm.trans
      (numeric.trans (congrArg Fin.val (spectator_phase t q y)))
  · intro same
    subst q
    funext index
    have value := spectator_only_complement width index.val (Finset.mem_compl.mp index.property)
    have wire : index.val = (⟨1, by omega⟩ : Fin (1 + (1 + width))) := Fin.ext value
    change spectatorBasis s p x index.val = spectatorBasis t p y index.val
    rw [wire, spectator_phase, spectator_phase]

/-- The exact source-controlled tensor decomposition retains the phase identity factor. -/
lemma withSpectator_binaryMatrix {width : Nat} (U : UnitaryOperator (Qubits width))
    (useInverse : Bool) :
    (((withSpectator width useInverse).binaryMatrix (interpretation U true true false)) :
      HilbertOperator (Qubits (1 + (1 + width)))) =
      HilbertOperator.tensor HilbertOperator.proj0 (1 : HilbertOperator (Qubits (1 + width))) +
      HilbertOperator.tensor HilbertOperator.proj1
        (HilbertOperator.tensor (1 : HilbertOperator (Qubits 1))
          ((if useInverse then U⁻¹ else U : UnitaryOperator (Qubits width)) :
            HilbertOperator (Qubits width))) := by
  ext row column
  obtain ⟨⟨s, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + width)).surjective row
  obtain ⟨⟨p, x⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective rest
  obtain ⟨⟨t, rest⟩, rfl⟩ := (prodEquiv (m := 1) (n := 1 + width)).surjective column
  obtain ⟨⟨q, y⟩, rfl⟩ := (prodEquiv (m := 1) (n := width)).surjective rest
  rw [UnitaryCircuit.binaryMatrix, UnitaryOperator.coe_reindex, withSpectator_matrix]
  change UnitaryCircuit.operatorAt _ _ _ _ _ (spectatorBasis s p x) (spectatorBasis t q y) = _
  rw [UnitaryCircuit.operatorAt_entry, spectator_selected_basis, spectator_selected_basis]
  have indicator :
      (if (layout (1 + width)).restrictComplementBasis
          (Finset.univ.map (spectatorPositions width)) (spectatorBasis s p x) =
        (layout (1 + width)).restrictComplementBasis
          (Finset.univ.map (spectatorPositions width)) (spectatorBasis t q y)
        then (1 : ℂ) else 0) = (if p = q then 1 else 0) := by
    by_cases same : p = q
    · rw [if_pos ((complement_eq_iff s t p q x y).mpr same), if_pos same]
    · have different := mt (complement_eq_iff s t p q x y).mp same
      rw [if_neg different, if_neg same]
  rw [indicator]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_symm, Equiv.apply_symm_apply, UnitaryOperator.coe_controlledQubits,
    HilbertOperator.tensor_apply, Equiv.symm_apply_apply, Matrix.add_apply]
  fin_cases s <;> fin_cases t <;> by_cases phaseSame : p = q <;> by_cases sourceSame : x = y <;>
    simp [HilbertOperator.proj0, HilbertOperator.proj1, Matrix.one_apply,
      phaseSame, sourceSame]

end
end QuantumAlg.UnitarySource.Conditional
