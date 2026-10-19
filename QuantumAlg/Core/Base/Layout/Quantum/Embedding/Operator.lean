/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Layout.Quantum.Embedding
public import QuantumAlg.Core.Base.Control.Operator
public import QuantumAlg.Core.Base.Tensor.Certified
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding
import all QuantumAlg.Core.Base.Layout.Quantum.Selection
import all QuantumAlg.Core.Base.Control.Operator
import all QuantumAlg.Core.Base.Tensor.Certified

/-!
# Operators on embedded physical subsystems

The embedding supplies coordinate restriction and reassembly. Extending an
operator tensors identity on every unselected wire; it cannot supply a new
basis permutation or change a spectator system.
-/

namespace QuantumAlg.QuantumLayout.Embedding

variable {small large : Nat} {source : QuantumLayout small} {target : QuantumLayout large}

/-- Extend the source action by identity on the full physical complement. -/
@[expose]
public noncomputable def liftOperator (embedding : Embedding source target)
    (operator : UnitaryOperator source.register) : UnitaryOperator target.register :=
  UnitaryOperator.reindex embedding.splitBasis.symm
    (UnitaryOperator.prodTensor operator
      (1 : UnitaryOperator (target.complementRegister embedding.selection)))

/-- Every ambient entry retains the complete complementary-basis equality condition. -/
public lemma liftOperator_entry (embedding : Embedding source target)
    (operator : UnitaryOperator source.register) (row column : target.Basis) :
    embedding.liftOperator operator row column =
      operator (embedding.splitBasis row).1 (embedding.splitBasis column).1 *
        (if (embedding.splitBasis row).2 = (embedding.splitBasis column).2 then 1 else 0) := by
  change UnitaryOperator.prodTensor operator
    (1 : UnitaryOperator (target.complementRegister embedding.selection))
    (embedding.splitBasis row) (embedding.splitBasis column) = _
  rw [UnitaryOperator.unitaryOperator_prodTensor_apply]
  rfl

/-- Assemble a target vector from a vector on the embedded subsystem and a
vector on its exact physical complement. -/
public noncomputable def mergeVector (embedding : Embedding source target)
    (selected : HilbertVector source.register)
    (complement : HilbertVector (target.complementRegister embedding.selection)) :
    HilbertVector target.register :=
  WithLp.toLp 2 fun basis =>
    selected (embedding.splitBasis basis).1 *
      complement (embedding.splitBasis basis).2

/-- Pointwise form of assembling a vector through an embedding. -/
@[simp] public lemma mergeVector_apply (embedding : Embedding source target)
    (selected : HilbertVector source.register)
    (complement : HilbertVector (target.complementRegister embedding.selection))
    (basis : target.Basis) :
    embedding.mergeVector selected complement basis =
      selected (embedding.splitBasis basis).1 *
        complement (embedding.splitBasis basis).2 := by
  rfl

/-- A lifted operator acts only on the embedded vector and leaves an
arbitrary complementary vector unchanged. -/
public lemma liftOperator_applyVec_mergeVector
    (embedding : Embedding source target)
    (operator : UnitaryOperator source.register)
    (selected : HilbertVector source.register)
    (complement : HilbertVector (target.complementRegister embedding.selection)) :
    (embedding.liftOperator operator).applyVec
        (embedding.mergeVector selected complement) =
      embedding.mergeVector (operator.applyVec selected) complement := by
  apply WithLp.ofLp_injective
  funext row
  rw [UnitaryOperator.applyVec, HilbertOperator.applyVec_apply]
  let summand : target.Basis → ℂ := fun column =>
      embedding.liftOperator operator row column *
        embedding.mergeVector selected complement column
  change (∑ column : target.Basis, summand column) =
    embedding.mergeVector (operator.applyVec selected) complement row
  rw [← Equiv.sum_comp embedding.splitBasis.symm summand, Fintype.sum_prod_type]
  simp only [summand, liftOperator_entry, mergeVector_apply, Equiv.apply_symm_apply,
    mul_ite, ite_mul, mul_one, mul_zero, zero_mul, Finset.sum_ite_eq,
    Finset.mem_univ, if_true, UnitaryOperator.applyVec_apply]
  rw [Finset.sum_mul]
  simp only [mul_assoc]
  rfl

/-- A placement covering every target position has no complementary quantum subsystem. -/
public lemma liftOperator_entry_of_surjective (embedding : Embedding source target)
    (onto : Function.Surjective embedding.position)
    (operator : UnitaryOperator source.register) (row column : target.Basis) :
    embedding.liftOperator operator row column =
      operator (embedding.splitBasis row).1 (embedding.splitBasis column).1 := by
  rw [liftOperator_entry]
  have same : (embedding.splitBasis row).2 = (embedding.splitBasis column).2 := by
    funext index
    have absent := Finset.mem_compl.mp index.property
    obtain ⟨original, equality⟩ := onto index.val
    exact False.elim (absent (equality ▸ Finset.mem_map_of_mem _ (Finset.mem_univ original)))
  rw [if_pos same, mul_one]

/-- Extending identity on an embedded subsystem is identity on every ambient wire. -/
public lemma embedding_liftOperator_one (embedding : Embedding source target) :
    embedding.liftOperator (1 : UnitaryOperator source.register) = 1 := by
  apply Subtype.ext
  funext row column
  rw [liftOperator_entry]
  change (if (embedding.splitBasis row).1 = (embedding.splitBasis column).1 then 1 else 0) *
      (if (embedding.splitBasis row).2 = (embedding.splitBasis column).2 then 1 else 0) =
    (if row = column then 1 else 0)
  by_cases same : row = column
  · subst column
    simp
  · by_cases selected : (embedding.splitBasis row).1 = (embedding.splitBasis column).1
    · have complement : (embedding.splitBasis row).2 ≠ (embedding.splitBasis column).2 := by
        intro equal
        exact same (embedding.splitBasis.injective (Prod.ext selected equal))
      simp only [same, selected, complement, if_false, if_true, mul_zero]
    · simp only [same, selected, if_false, zero_mul]

end QuantumAlg.QuantumLayout.Embedding
