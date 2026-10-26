/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Arithmetic
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Physical.Action
import all QuantumAlg.Primitives.MAU.Multiplication.Gidney.Measured.Coherent
import all QuantumAlg.Primitives.MAU.Addition.Gidney.Measured.Syntax.Coherent

/-!
# Actual selected arithmetic record action on the canonical recycling carrier

Every actual original Store, physical measurement record and external
reference has the same scalar. Complete physical output labels implement
the independently specified selected modular product and restore all three
original helpers, including the reduction flag. No phase depends on the
borrowed source bits or reference [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured
open MAU.Addition.Gidney.Measured.Instruction

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev Context := context base noQuantum m ell width

/-- One input-independent actual record scalar for both emitted original MAC words. -/
def arithmeticAlpha (modulus : BitVec width) (coefficient : (ZMod modulus.toNat)ˣ) : ℂ :=
  Layout.accumulatePrefixAlpha
      (Layout.forwardConstant modulus (coefficient : ZMod modulus.toNat).val) width le_rfl *
    Layout.accumulatePrefixAlpha
      (Layout.inverseConstant modulus
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val) width le_rfl

/-- Every actual arithmetic record acts with common alpha on every canonical coherent family. -/
lemma arithmetic_record_coherent (wide : 2 ≤ width) (modulus : BitVec width)
    (positive : 0 < modulus.toNat) (coefficient : (ZMod modulus.toNat)ˣ)
    (environment : model.Environment) (store : Store (Context base noQuantum m ell width))
    (measured : WordOutcomes (Physical.qubits width) (context_wires base noQuantum m ell width)
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val))
    {Reference : Register} {Index : Type} [Fintype Index]
    (control : Index → Bool) (source : Index → BitVec width)
    (reference : Index → Reference.Index) (amplitude : Index → ℂ)
    (canonical : ∀ index, (source index).toNat < modulus.toNat) :
    (wordActualKraus (operations := BitWord.model) (services := .empty)
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (ventCell base noQuantum m ell width) environment.quantum Reference
      ((Physical.layout width).multiplicationWord wide modulus
        (coefficient : ZMod modulus.toNat).val
        ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
      store measured).applyVec
        (encodedExpansion (Physical.qubits width) (context_wires base noQuantum m ell width)
          (fun index => Physical.cleanLabel width (control index) (source index))
          reference amplitude) =
      encodedExpansion (Physical.qubits width) (context_wires base noQuantum m ell width)
        (fun index => Physical.cleanLabel width (control index)
          (Physical.selectedProduct modulus coefficient (control index) (source index))) reference
        (fun index => amplitude index * arithmeticAlpha width modulus coefficient) := by
  have action := Layout.multiplicationWord_recordCoherent (operations := BitWord.model)
    (services := .empty) (Physical.layout width) wide modulus
      (coefficient : ZMod modulus.toNat).val
      ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val
      (Physical.qubits width) (context_wires base noQuantum m ell width)
      (recordBank base noQuantum m ell width) environment.quantum
  have applied := action store measured Reference Index
    (fun index => Physical.cleanLabel width (control index) (source index)) reference amplitude
    (fun index helper =>
      (Physical.cleanLabel_helpers width (control index) (source index)).1 helper)
  have labels :
      (fun index => wordLabel ((Physical.layout width).multiplicationWord wide modulus
          (coefficient : ZMod modulus.toNat).val
          ((coefficient⁻¹ : (ZMod modulus.toNat)ˣ) : ZMod modulus.toNat).val)
        (Physical.cleanLabel width (control index) (source index))) =
      (fun index => Physical.cleanLabel width (control index)
        (Physical.selectedProduct modulus coefficient (control index) (source index))) := by
    funext index
    exact Physical.multiplicationWord_cleanLabel wide modulus positive coefficient
      (control index) (source index) (canonical index)
  rw [labels] at applied
  exact applied

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
