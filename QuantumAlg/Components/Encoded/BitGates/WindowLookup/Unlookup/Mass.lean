/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Encoded.BitGates.WindowLookup.Unlookup.Coherent

/-!
# Normalized actual unlookup branch weights on the concrete lookup graph

Graph clearing preserves distinct complete physical/reference basis labels.
Its coherent norm therefore equals the original norm. The actual common
branch coefficient gives exactly one over the full result-word cardinality
per outcome; the complete actual outcome-path family sums to one.
-/

namespace QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame

open Execution NormalizedVector
open scoped BigOperators

noncomputable section

variable {Data : Type} {encoding : BinaryLabelEncoding Data}
  {ctx : RuntimeCtx .quantum} {services : ClassicalOracleModel}
  {resultWidth lowWidth highRemaining : Nat}
  (frame : UnlookupFrame encoding resultWidth lowWidth highRemaining)

/-- The concrete lookup graph's actual cleared labels preserve every coherent reference norm. -/
lemma clearedGraph_reference_norm (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (graph : ∀ index, frame.Graph table (state index)) (reference : Index → Reference.Index)
    (injective : Function.Injective fun index =>
      (measuredEncodedBasis physical sameWires (state index), reference index))
    (amplitude : Index → ℂ) :
    ‖∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires
          (resultSetConstant frame.result 0 (state index)), reference index)).vec‖ =
      ‖∑ index, amplitude index •
        (NormalizedVector.ket (R := Register.prod ctx.register Reference)
          (measuredEncodedBasis physical sameWires (state index), reference index)).vec‖ := by
  have original := HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq
    (R := Register.prod ctx.register Reference) Finset.univ
    (fun index => (measuredEncodedBasis physical sameWires (state index), reference index))
    injective amplitude
  have cleared := HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq
    (R := Register.prod ctx.register Reference) Finset.univ
    (fun index => (measuredEncodedBasis physical sameWires
      (resultSetConstant frame.result 0 (state index)), reference index))
    (frame.clearedGraph_reference_injective physical sameWires table state graph reference
      injective)
    amplitude
  exact cleared.trans original.symm

/-- Each actual retained branch has its normalized full-width result probability. -/
lemma branchOperator_graph_mass (physical : QubitLayout encoding.width)
    (sameWires : physical.toQuantum.wires = ctx.quantumLayout.wires)
    (output : Fin resultWidth → CWriteRef ctx (.finite 2))
    (outputDistinct : Function.Injective fun index => (output index).key)
    (mask : CWriteRef ctx (.bits resultWidth))
    (parity : Fin (2 ^ lowWidth) → CWriteRef ctx .bit)
    (table : Bool → Fin (2 ^ highRemaining) → Fin (2 ^ lowWidth) → Fin (2 ^ resultWidth))
    (separate : ∀ index, (parity index).key ∉
      (CInputRef.storage mask.toCStorageRef).storageKeys)
    (environment : OracleModel.Interpretation .empty) (store : Store ctx)
    (seed : Data) (outcome : Fin (2 ^ resultWidth))
    {Reference : Register} {Index : Type} [Fintype Index] (state : Index → Data)
    (graph : ∀ index, frame.Graph table (state index))
    (clean : ∀ index, frame.high.CleanFrom 0 (state index))
    (reference : Index → Reference.Index)
    (injective : Function.Injective fun index =>
      (measuredEncodedBasis physical sameWires (state index), reference index))
    (amplitude : Index → ℂ)
    (normalized : ‖∑ index, amplitude index •
      (NormalizedVector.ket (R := Register.prod ctx.register Reference)
        (measuredEncodedBasis physical sameWires (state index), reference index)).vec‖ = 1) :
    ‖(frame.branchOperator (services := services) physical sameWires output mask parity table store
      (namedResultPath (oracles := .empty) (services := services)
        physical sameWires frame.result output seed outcome) environment Reference).applyVec
          (∑ index, amplitude index •
            (NormalizedVector.ket (R := Register.prod ctx.register Reference)
              (measuredEncodedBasis physical sameWires (state index), reference index)).vec)‖ ^ 2 =
      ((2 : ℝ)⁻¹) ^ resultWidth := by
  rw [frame.branchOperator_graph_coherent physical sameWires output outputDistinct mask parity table
    separate environment store seed outcome state graph clean reference amplitude,
    norm_smul, norm_pow,
    frame.clearedGraph_reference_norm physical sameWires table state graph reference injective,
    normalized, mul_one]
  calc
    (‖invSqrt2‖ ^ resultWidth) ^ 2 = (‖invSqrt2‖ ^ 2) ^ resultWidth := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm resultWidth 2]
    _ = _ := by rw [norm_sq_invSqrt2]

/-- The actual full-width outcome probabilities sum to one. -/
lemma resultOutcome_mass_total (width : Nat) :
    (∑ _ : Fin (2 ^ width), ((2 : ℝ)⁻¹) ^ width) = 1 := by
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
    Nat.cast_pow, Nat.cast_ofNat]
  rw [← mul_pow]
  norm_num

end

end QuantumAlg.EncodedBit.WindowLookup.UnlookupFrame
