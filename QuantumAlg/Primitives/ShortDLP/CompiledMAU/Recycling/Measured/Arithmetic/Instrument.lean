/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Placement
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Carrier.Action
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Coherent
import all QuantumAlg.Core.Base.Gate.Unitary.Reindex

/-!
# Actual measured arithmetic records on the complete unit/reference carrier

Each actual record has one common scalar on the independently specified
controlled unit translation. Full original Stores and overwritten vent cells
remain explicit. Arbitrary external-reference coordinates are untouched
[G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat]

/-- The full control/unit carrier and arbitrary reference occupy their actual physical labels. -/
def arithmeticJointEmbedding (Reference : Register) :
    ((Recycling.Carrier.full modulus.toNat).prod Reference).Index ↪
      ((Context base noQuantum m ell width).register.prod Reference).Index :=
  BasisEmbedding.withReference (Placement.embedding base noQuantum m ell width modulus) Reference

private lemma unit_expansion {Reference : Register}
    (label : (Recycling.Carrier.full modulus.toNat).Index) (reference : Reference.Index)
    (scalar : ℂ) :
    encodedExpansion (Physical.qubits width) (context_wires base noQuantum m ell width)
        (fun _ : Unit => Carrier.physicalLabel modulus label) (fun _ => reference)
        (fun _ => scalar) =
      scalar • (NormalizedVector.ket
        (arithmeticJointEmbedding base noQuantum m ell width modulus Reference
          (label, reference))).vec := by
  dsimp only [encodedExpansion]
  rw [Fintype.sum_unique]
  have linear (coordinates : (Register.prod (Physical.qubits width).toQuantum.register
      Reference).Index ≃ (Register.prod (Context base noQuantum m ell width).register
        Reference).Index) (vector : HilbertVector
          (Register.prod (Physical.qubits width).toQuantum.register Reference)) :
      HilbertVector.reindex coordinates (scalar • vector) =
        scalar • HilbertVector.reindex coordinates vector := rfl
  rw [linear, HilbertVector.reindex_ket]
  rfl

/-- Every actual original arithmetic record implements the same controlled unit/reference column. -/
lemma measuredArithmetic_record_ket (wide : 2 ≤ width) (positive : 0 < modulus.toNat)
    (coefficient : (ZMod modulus.toNat)ˣ) (environment : model.Environment)
    (store : Store (Context base noQuantum m ell width))
    (measured : WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val))
    (Reference : Register)
    (column : ((Recycling.Carrier.full modulus.toNat).prod Reference).Index) :
    (wordActualKraus (operations := BitWord.model) (services := .empty)
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) environment.quantum Reference
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
      store measured).applyVec
        (NormalizedVector.ket
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference column)).vec =
      arithmeticAlpha width modulus coefficient •
        (NormalizedVector.ket
          (arithmeticJointEmbedding base noQuantum m ell width modulus Reference
            (Carrier.controlledAction modulus coefficient column.1, column.2))).vec := by
  rcases column with ⟨localColumn, referenceColumn⟩
  have action := Layout.multiplicationWord_recordCoherent (operations := BitWord.model)
    (services := .empty) (Physical.layout width) wide modulus
      (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (recordBank base noQuantum m ell width) environment.quantum
  have applied := action store measured Reference Unit
    (fun _ => Carrier.physicalLabel modulus localColumn) (fun _ => referenceColumn) (fun _ => 1)
    (fun _ => Carrier.physicalLabel_helpers modulus localColumn)
  have labels :
      (fun _ : Unit => wordLabel ((Physical.layout width).multiplicationWord wide modulus
          (coefficient : ZMod modulus.toNat).val
          ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
        (Carrier.physicalLabel modulus localColumn)) =
      (fun _ : Unit => Carrier.physicalLabel modulus
        (Carrier.controlledAction modulus coefficient localColumn)) := by
    funext _
    exact Carrier.measuredWord_physicalLabel modulus wide positive coefficient localColumn
  rw [labels] at applied
  simpa only [one_mul, unit_expansion, one_smul, recordBank, arithmeticAlpha] using applied

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
