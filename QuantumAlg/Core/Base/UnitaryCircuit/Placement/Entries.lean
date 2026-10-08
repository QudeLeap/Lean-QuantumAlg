/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Placement
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection

/-!
# Actual basis entries of a placed native word

The entry formula reads the requested ambient positions in their original
argument order and retains equality of every complementary coordinate. The
auxiliary extension of physical addresses has no observable role in this
formula. Spectator values need not be initialized or separable.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable {gates : GateModel} {oracles : OracleModel}
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

/-- Read the selected coordinates, casting only by their certified dimension equalities. -/
public def selectedInput (basis : target.Basis) : source.Basis :=
  fun index => Fin.cast (congrArg (fun size : ℕ+ => (size : Nat)) (dimensions index).symm)
    (basis (position index))

/-- Every placed matrix entry has exactly the original action and the untouched complement. -/
public theorem operatorAt_entry (operator : UnitaryOperator source.register)
    (row column : target.Basis) :
    operatorAt source target position dimensions operator row column =
      operator (selectedInput source target position dimensions row)
        (selectedInput source target position dimensions column) *
          (if target.restrictComplementBasis (Finset.univ.map position) row =
            target.restrictComplementBasis (Finset.univ.map position) column then 1 else 0) := by
  have selected (basis : target.Basis) :
      ((relocatedPlacement source target position dimensions).splitBasis basis).1 =
        selectedInput source target position dimensions basis := by
    funext index
    apply Fin.ext
    rfl
  refine ((relocatedPlacement source target position dimensions).liftOperator_entry
    operator row column).trans ?_
  rw [selected row, selected column]
  rfl

/-- An ambient basis is determined by the values read at the placed source
positions together with the complete unselected complement. -/
public theorem basis_eq_iff_selectedInput_eq_and_complement_eq
    (left right : target.Basis) :
    left = right ↔
      selectedInput source target position dimensions left =
          selectedInput source target position dimensions right ∧
        target.restrictComplementBasis (Finset.univ.map position) left =
          target.restrictComplementBasis (Finset.univ.map position) right := by
  constructor
  · intro same
    subst right
    exact ⟨rfl, rfl⟩
  · rintro ⟨selected, complement⟩
    apply (target.selectionBasisEquiv (Finset.univ.map position)).injective
    apply Prod.ext
    · funext index
      obtain ⟨sourceIndex, _present, same⟩ := Finset.mem_map.mp index.property
      have value := congrArg
        (fun basis => (basis sourceIndex).val) selected
      change (left (position sourceIndex)).val =
        (right (position sourceIndex)).val at value
      apply Fin.ext
      change (left index.val).val = (right index.val).val
      rw [← same]
      exact value
    · exact complement

/-- Place a proved computational-basis action at selected ambient positions.
The unselected physical systems retain their exact original values. -/
public theorem placeAt_applyNormalized_ket_of_eq
    (body : UnitaryCircuit gates oracles source)
    (sourceInput sourceOutput : source.Basis)
    (actual : body.applyNormalized (NormalizedVector.ket sourceInput) =
      NormalizedVector.ket sourceOutput)
    (targetInput targetOutput : target.Basis)
    (inputSelected : selectedInput source target position dimensions targetInput = sourceInput)
    (outputSelected : selectedInput source target position dimensions targetOutput = sourceOutput)
    (complementUnchanged :
      target.restrictComplementBasis (Finset.univ.map position) targetOutput =
        target.restrictComplementBasis (Finset.univ.map position) targetInput) :
    (placeAt source target position dimensions body).applyNormalized
        (NormalizedVector.ket targetInput) = NormalizedVector.ket targetOutput := by
  apply NormalizedVector.ext
  intro row
  have sourceEntry := congrArg
    (fun state : NormalizedVector source.register =>
      state (selectedInput source target position dimensions row)) actual
  change body.matrix.applyVec
      (NormalizedVector.ket (R := source.register) sourceInput).vec
        (selectedInput source target position dimensions row) =
    NormalizedVector.ket (R := source.register) sourceOutput
      (selectedInput source target position dimensions row) at sourceEntry
  simp only [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket] at sourceEntry
  change (placeAt source target position dimensions body).matrix.applyVec
      (NormalizedVector.ket (R := target.register) targetInput).vec row =
    NormalizedVector.ket (R := target.register) targetOutput row
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_ket]
  rw [placeAt_matrix, operatorAt_entry, inputSelected, sourceEntry]
  simp only [NormalizedVector.ket_apply]
  have rowCharacterization :=
    basis_eq_iff_selectedInput_eq_and_complement_eq source target position dimensions
      row targetOutput
  rw [outputSelected, complementUnchanged] at rowCharacterization
  by_cases same : row = targetOutput
  · have parts := rowCharacterization.mp same
    rw [if_pos same, if_pos parts.1, if_pos parts.2, one_mul]
  · have notParts :
        selectedInput source target position dimensions row ≠ sourceOutput ∨
          target.restrictComplementBasis (Finset.univ.map position) row ≠
            target.restrictComplementBasis (Finset.univ.map position) targetInput := by
      by_contra neither
      push Not at neither
      exact same (rowCharacterization.mpr neither)
    rcases notParts with selectedDifferent | complementDifferent
    · rw [if_neg same, if_neg selectedDifferent, zero_mul]
    · rw [if_neg same, if_neg complementDifferent, mul_zero]

end

end QuantumAlg.UnitaryCircuit
