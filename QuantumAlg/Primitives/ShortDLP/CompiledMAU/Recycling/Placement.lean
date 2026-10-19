/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Carrier
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Construction
import all QuantumAlg.Components.Encoded.StateEmbedding
import all QuantumAlg.Core.Execution.Context.Layout.Unitary
import all QuantumAlg.Components.Gates.Construction
import all QuantumAlg.Core.Base.Control.Operator
import Mathlib.Data.List.OfFn

/-!
# Actual physical placement of the recycled native bank

These are local equal-wire instances for
the actual owned context, not a new compiler or a new Core placement framework.
The existing direct placed one-qubit constructor is retained. Its complete
matrix equals the existing canonical one-qubit word embedded on exactly the
same ordered physical wires; native trace and dependency expression agree too.
The source-clean embedding is then transported by that actual wire equality.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Placement

noncomputable section

variable {environment : OracleModel.empty.Interpretation}

open Execution

local instance {α : Type} : DecidableEq α := Classical.decEq α

private lemma single_equal_wires_matrix {leftCount rightCount : Nat}
    (left : QuantumLayout leftCount) (right : QuantumLayout rightCount)
    (same : left.wires = right.wires) (operator : UnitaryOperator (Qubits 1))
    (target : Fin leftCount) (leftQubit : (left.wire target).dimension = 2)
    (rightQubit :
      (right.wire (positionsOfEqualWires left right same target)).dimension = 2) :
    ((Gate.singleQubitAt right .empty operator
        (positionsOfEqualWires left right same target) rightQubit).matrix environment) =
      UnitaryOperator.reindex (basisOfEqualWires left right same)
        ((Gate.singleQubitAt left .empty operator target leftQubit).matrix environment) := by
  have countSame : leftCount = rightCount := by
    simpa only [QuantumLayout.wires_length] using congrArg List.length same
  subst rightCount
  have layoutSame : left = right :=
    QuantumLayout.eq_of_wire_eq (List.ofFn_injective same)
  subst right
  have corresponding : positionsOfEqualWires left left same = Equiv.refl (Fin leftCount) := by
    ext index
    rfl
  have positionSame (index : Fin leftCount) :
      positionsOfEqualWires left left same index = index :=
    congrArg (fun equivalence : Fin leftCount ≃ Fin leftCount => equivalence index)
      corresponding
  have basisSame : basisOfEqualWires left left same = Equiv.refl left.Basis := by
    ext basis index
    have value := basisOfEqualWires_value left left same basis index
    rw [positionSame index] at value
    exact value
  rw [basisSame]
  apply Subtype.ext
  ext row column
  rfl

private lemma reindex_intertwines {R S T : Register}
    (equivalence : R.Index ≃ T.Index) (embedding : S.Index ↪ R.Index)
    (source : UnitaryOperator S) (native : UnitaryOperator R)
    (derived : (native : HilbertOperator R) * BasisEmbedding.matrix embedding =
      BasisEmbedding.matrix embedding * (source : HilbertOperator S)) :
    (UnitaryOperator.reindex equivalence native : HilbertOperator T) *
        BasisEmbedding.matrix (embedding.trans equivalence.toEmbedding) =
      BasisEmbedding.matrix (embedding.trans equivalence.toEmbedding) *
        (source : HilbertOperator S) := by
  apply BasisEmbedding.intertwines_of_columns
  intro row column
  have nativeColumns : native (equivalence.symm row) (embedding column) =
      ∑ index : S.Index,
        if embedding index = equivalence.symm row then source index column else 0 := by
    have equal := congrArg (fun matrix => matrix (equivalence.symm row) column) derived
    simpa [Matrix.mul_apply, BasisEmbedding.matrix] using equal
  change native (equivalence.symm row) (equivalence.symm (equivalence (embedding column))) =
    ∑ index : S.Index, if equivalence (embedding index) = row then source index column else 0
  simpa only [Equiv.symm_apply_apply, equivalence.eq_symm_apply] using nativeColumns

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- The native bank always contains its control wire, including zero arithmetic width. -/
private lemma arithmeticWidth_neZero (width : Nat) :
    NeZero (Arithmetic.encoding width).width :=
  ⟨by rw [Arithmetic.width_eq]; omega⟩

attribute [local instance] arithmeticWidth_neZero

def basis : (Carrier.physical width).Index ≃ (Context base noQuantum m ell width).register.Index :=
  basisOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width)

def embeddedSingle (operator : UnitaryOperator (Qubits 1)) :
    UnitaryCircuit AlgorithmGate.model .empty (Context base noQuantum m ell width).quantumLayout :=
  unitaryOfEqualWires (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) (Carrier.oneQubit (width := width) operator)

/-- The unchanged direct constructor and canonical embedding have identical full matrices. -/
lemma single_matrix (operator : UnitaryOperator (Qubits 1)) :
    ((single base noQuantum m ell width operator).matrix environment) =
      ((embeddedSingle base noQuantum m ell width operator).matrix environment) := by
  rw [embeddedSingle, unitaryOfEqualWires_matrix]
  exact single_equal_wires_matrix (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) operator 0 rfl
      (control_qubit base noQuantum m ell width)

/-- This is correspondence of the bottom-level physical wire, including its identity. -/
lemma single_physical_wire :
    (Context base noQuantum m ell width).quantumLayout.wire (control base noQuantum m ell width) =
      (Arithmetic.layout width).toQuantum.wire 0 :=
  wireAtCorrespondingPosition (Arithmetic.layout width).toQuantum
    (Context base noQuantum m ell width).quantumLayout
    (context_wires base noQuantum m ell width) 0

/-- Native accounting agrees for every operation/service declaration, not only empty defaults. -/
lemma single_trace (operator : UnitaryOperator (Qubits 1))
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (single base noQuantum m ell width operator).eventTrace operations services =
      (embeddedSingle base noQuantum m ell width operator).eventTrace operations services := by
  rw [embeddedSingle, unitaryOfEqualWires_trace]
  rfl

lemma single_cost (operator : UnitaryOperator (Qubits 1))
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (single base noQuantum m ell width operator).eventCost operations services =
      (embeddedSingle base noQuantum m ell width operator).eventCost operations services := by
  rw [embeddedSingle, unitaryOfEqualWires_cost]
  rfl

lemma single_depth (operator : UnitaryOperator (Qubits 1))
    (operations : ClassicalOpModel) (services : ClassicalOracleModel) :
    (single base noQuantum m ell width operator).eventDepth operations services =
      (embeddedSingle base noQuantum m ell width operator).eventDepth operations services := by
  rw [embeddedSingle, unitaryOfEqualWires_depth]
  rfl

variable (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val] (positive : 0 < modulus.val)

def embedding : (Carrier.full modulus.val).Index ↪
    (Context base noQuantum m ell width).register.Index :=
  (Carrier.embedding modulus positive).trans (basis base noQuantum m ell width).toEmbedding

def zeroEmbedding : (Carrier.units modulus.val).Index ↪
    (Context base noQuantum m ell width).register.Index :=
  (Carrier.zeroEmbedding modulus positive).trans (basis base noQuantum m ell width).toEmbedding

/-- The member's actual direct H/phase acts on every clean carrier column as claimed. -/
lemma single_intertwines (operator : UnitaryOperator (Qubits 1)) :
    (((single base noQuantum m ell width operator).matrix environment) :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (embedding base noQuantum m ell width modulus positive) =
    BasisEmbedding.matrix (embedding base noQuantum m ell width modulus positive) *
      (UnitaryOperator.prodTensor operator (1 : UnitaryOperator (Carrier.units modulus.val)) :
        HilbertOperator (Carrier.full modulus.val)) := by
  rw [single_matrix, embeddedSingle, unitaryOfEqualWires_matrix]
  exact reindex_intertwines _ _ _ _ (Carrier.oneQubit_intertwines modulus positive operator)

/-- The internally valid/fitted branch uses the real compiler, not its identity fallback. -/
lemma arithmetic_intertwines (coefficient : (ZMod modulus.val)ˣ) :
    (((arithmetic base noQuantum m ell width modulus.val coefficient).matrix environment) :
        HilbertOperator (Context base noQuantum m ell width).register) *
      BasisEmbedding.matrix (embedding base noQuantum m ell width modulus positive) =
    BasisEmbedding.matrix (embedding base noQuantum m ell width modulus positive) *
      (UnitaryOperator.ofPerm (Carrier.controlledAction modulus coefficient).symm :
        HilbertOperator (Carrier.full modulus.val)) := by
  have fitted : modulus.val ≤ 2 ^ width := Nat.le_of_lt_succ modulus.isLt
  have selected : sourceArithmetic width modulus.val coefficient = Arithmetic.program modulus
      coefficient := by
    simp only [sourceArithmetic, dif_pos positive, dif_pos fitted]
  rw [arithmetic, selected, unitaryOfEqualWires_matrix]
  exact reindex_intertwines _ _ _ _ (Carrier.arithmetic_intertwines modulus positive coefficient)

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Placement
