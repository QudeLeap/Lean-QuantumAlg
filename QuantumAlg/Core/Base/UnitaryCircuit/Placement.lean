/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Realization.Placement
import all QuantumAlg.Core.Base.UnitaryCircuit.Physical
import all QuantumAlg.Core.Base.Layout.Quantum.Relabeling
import all QuantumAlg.Core.Base.Layout.Quantum.Embedding.Operator
import Mathlib.Logic.Equiv.Fintype

/-!
# Placing a complete native word at dimension-correct positions

The selected positions determine the physical addresses of every actual gate
and query in the construction. A finite injective address assignment extends
to a permutation of addresses; only the original wires occur in the relocated
word. Embedding then leaves every unselected ambient system unchanged.
-/

namespace QuantumAlg.UnitaryCircuit

noncomputable section

variable {gates : GateModel} {oracles : OracleModel}
variable {small large : Nat} (source : QuantumLayout small) (target : QuantumLayout large)
variable (position : Fin small ↪ Fin large)
variable (dimensions : ∀ index,
  (source.wire index).dimension = (target.wire (position index)).dimension)

private def addressPermutation : Equiv.Perm Nat :=
  Classical.choose (Equiv.Perm.exists_extending_pair
    (fun index => (source.wire index).identity)
    (fun index => (target.wire (position index)).identity)
    source.identityInjective (target.identityInjective.comp position.injective))

private theorem addressPermutation_apply (index : Fin small) :
    addressPermutation source target position (source.wire index).identity =
      (target.wire (position index)).identity :=
  Classical.choose_spec (Equiv.Perm.exists_extending_pair
    (fun index => (source.wire index).identity)
    (fun index => (target.wire (position index)).identity)
    source.identityInjective (target.identityInjective.comp position.injective)) index

private def relocatedPlacement :
    QuantumLayout.Embedding
      (source.relabel (addressPermutation source target position).toEmbedding) target where
  position := position
  wire_eq index := by
    symm
    have identities := addressPermutation_apply source target position index
    have sizes := dimensions index
    change QuantumWire.relabel _ (source.wire index) = target.wire (position index)
    cases first : source.wire index with
    | mk firstIdentity firstDimension =>
      cases second : target.wire (position index) with
      | mk secondIdentity secondDimension =>
        simp only [first, second] at identities sizes
        change QuantumWire.mk (addressPermutation source target position firstIdentity)
          firstDimension = QuantumWire.mk secondIdentity secondDimension
        rw [identities, sizes]

/-- Extend the independent source operator by identity at the selected physical positions. -/
public def operatorAt (operator : UnitaryOperator source.register) :
    UnitaryOperator target.register :=
  (relocatedPlacement source target position dimensions).liftOperator
    (UnitaryOperator.reindex
      (QuantumLayout.relabelBasis source
        (addressPermutation source target position).toEmbedding) operator)

/-- Read an ambient computational basis at the selected physical positions,
in the source word's argument order. -/
@[expose] public def basisAt (basis : target.Basis) : source.Basis :=
  fun index => Fin.cast (congrArg Subtype.val (dimensions index).symm)
    (basis (position index))

@[simp] public theorem basisAt_val (basis : target.Basis) (index : Fin small) :
    (basisAt source target position dimensions basis index).val =
      (basis (position index)).val := rfl

/-- When the selected positions cover the ambient layout, an embedded
operator entry is the source entry read in the supplied position order. -/
public theorem operatorAt_entry_of_surjective
    (onto : Function.Surjective position)
    (operator : UnitaryOperator source.register) (row column : target.Basis) :
    operatorAt source target position dimensions operator row column =
      operator (basisAt source target position dimensions row)
        (basisAt source target position dimensions column) := by
  rw [operatorAt, QuantumLayout.Embedding.liftOperator_entry_of_surjective
    (relocatedPlacement source target position dimensions) onto]
  simp only [UnitaryOperator.coe_reindex, Matrix.reindex_apply,
    Matrix.submatrix_apply]
  have rowBasis :
      (QuantumLayout.relabelBasis source
        (addressPermutation source target position).toEmbedding).symm
          ((relocatedPlacement source target position dimensions).splitBasis row).1 =
        basisAt source target position dimensions row := by
    funext index
    apply Fin.ext
    change
      (((relocatedPlacement source target position dimensions).splitBasis row).1
          index).val = (row (position index)).val
    rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value]
    rfl
  have columnBasis :
      (QuantumLayout.relabelBasis source
        (addressPermutation source target position).toEmbedding).symm
          ((relocatedPlacement source target position dimensions).splitBasis column).1 =
        basisAt source target position dimensions column := by
    funext index
    apply Fin.ext
    change
      (((relocatedPlacement source target position dimensions).splitBasis column).1
          index).val = (column (position index)).val
    rw [QuantumLayout.Embedding.embedding_splitBasis_selected_value]
    rfl
  rw [rowBasis, columnBasis]

/-- Assemble a target vector from the selected source coordinates and the
exact complementary physical coordinates of this placement. -/
public def vectorAt
    (selected : HilbertVector source.register)
    (complement : HilbertVector
      (target.complementRegister (Finset.univ.map position))) :
    HilbertVector target.register :=
  (relocatedPlacement source target position dimensions).mergeVector selected complement

/-- A placed operator acts only on the selected vector and fixes an arbitrary
vector on every unselected physical system. -/
public theorem operatorAt_applyVec_vectorAt
    (operator : UnitaryOperator source.register)
    (selected : HilbertVector source.register)
    (complement : HilbertVector
      (target.complementRegister (Finset.univ.map position))) :
    (operatorAt source target position dimensions operator).applyVec
        (vectorAt source target position dimensions selected complement) =
      vectorAt source target position dimensions
        (operator.applyVec selected) complement :=
  QuantumLayout.Embedding.liftOperator_applyVec_mergeVector
    (relocatedPlacement source target position dimensions) operator selected complement

/-- Relocate and embed the actual native construction at the selected dimension-correct wires. -/
public def placeAt (body : UnitaryCircuit gates oracles source) :
    UnitaryCircuit gates oracles target :=
  (body.relabel (addressPermutation source target position).toEmbedding).embed
    (relocatedPlacement source target position dimensions)

/-- Placement preserves the full operator, including phase and all spectator coherences. -/
public theorem placeAt_matrix (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).matrix =
      operatorAt source target position dimensions body.matrix := by
  rw [placeAt, embed_matrix, relabel_matrix]
  rfl

/-- A placed native word acts only on its selected vector and fixes an
arbitrary vector on the exact physical complement. -/
public theorem placeAt_applyVec_vectorAt
    (body : UnitaryCircuit gates oracles source)
    (selected : HilbertVector source.register)
    (complement : HilbertVector
      (target.complementRegister (Finset.univ.map position))) :
    (placeAt source target position dimensions body).matrix.applyVec
        (vectorAt source target position dimensions selected complement) =
      vectorAt source target position dimensions
        (body.matrix.applyVec selected) complement := by
  rw [placeAt_matrix]
  exact operatorAt_applyVec_vectorAt source target position dimensions
    body.matrix selected complement

/-- Physical placement retains the exact native occurrence order. -/
public theorem placeAt_eventTrace (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).eventTrace = body.eventTrace := by
  rw [placeAt, embed_eventTrace, relabel_eventTrace]

/-- Physical placement retains the exact native-event ledger of the original word. -/
public theorem placeAt_eventCost (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).eventCost = body.eventCost := by
  rw [← ofList_eventTrace_eq_eventCost, placeAt_eventTrace,
    ofList_eventTrace_eq_eventCost]

/-- Physical placement retains the complete dependency expression of the original word. -/
public theorem placeAt_eventDepth (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).eventDepth = body.eventDepth := by
  rw [placeAt, embed_eventDepth, relabel_eventDepth]

/-- Physical placement retains every evaluated dependency depth of the original word. -/
public theorem placeAt_evaluatedEventDepth
    (duration : Resource.Event (.quantum gates oracles) → Nat)
    (body : UnitaryCircuit gates oracles source) :
    (placeAt source target position dimensions body).evaluatedEventDepth duration =
      body.evaluatedEventDepth duration := by
  unfold evaluatedEventDepth
  rw [placeAt_eventDepth]

/-- Realize the independently placed target using the complete relocated native word. -/
public def placeRealization {operator : UnitaryOperator source.register}
    (realized : ExactRealization gates oracles source operator) :
    ExactRealization gates oracles target (operatorAt source target position dimensions operator)
      where
  circuit := placeAt source target position dimensions realized.circuit
  matrix_eq := by rw [placeAt_matrix, realized.matrix_eq]

end

end QuantumAlg.UnitaryCircuit
