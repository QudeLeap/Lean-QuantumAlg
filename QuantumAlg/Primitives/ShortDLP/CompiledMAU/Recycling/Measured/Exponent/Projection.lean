/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Record
import all QuantumAlg.Primitives.QFT.Semiclassical.Mathematics
import Mathlib.Logic.Equiv.Prod

/-!
# Exact reindexing of actual exponent records into arithmetic and retained bits

This is a bijection of the original chronological outcome family. It keeps
every overwritten arithmetic result distinct and converts only the finite
label of the same physical readout qubit. It executes no packing operation
and discards no actual record [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ProjectionCtx := context base noQuantum m ell width

/-- Only the finite coordinate of the actual physically addressed control is converted. -/
def exponentReadoutEquiv :
    Fin ((ProjectionCtx base noQuantum m ell width).quantumLayout.wire
      (control base noQuantum m ell width)).dimension ≃ Fin 2 :=
  finCongr (congrArg PNat.val (control_qubit base noQuantum m ell width))

variable (modulus : BitVec width) (wide : 2 ≤ width) {bits : Nat}
  (unit : (ZMod modulus.toNat)ˣ)

/-- Every original arithmetic record, without identifying reused physical storage writes. -/
def ExponentArithmeticOutcomes :
    (remaining position : Nat) → position + remaining ≤ bits → Type
  | 0, _, _ => Unit
  | remaining + 1, position, bounded =>
      stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          (⟨position, by omega⟩ : Fin bits) ×
        ExponentArithmeticOutcomes remaining (position + 1) (by omega)

instance exponentArithmeticOutcomesFintype (remaining position : Nat)
    (bounded : position + remaining ≤ bits) :
    Fintype (ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
      position bounded) := by
  induction remaining generalizing position with
  | zero => change Fintype Unit; infer_instance
  | succ remaining induction =>
      change Fintype (stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          (⟨position, by omega⟩ : Fin bits) ×
        ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
          (position + 1) (by omega))
      letI := induction (position + 1) (by omega)
      infer_instance

/-- A bijection preserves every actual arithmetic record beside the retained exponent bit tuple. -/
def exponentOutcomeEquiv : (remaining position : Nat) →
    (bounded : position + remaining ≤ bits) →
    ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position bounded ≃
      (ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining position
        bounded × Bits remaining)
  | 0, _, _ =>
      { toFun := fun _ => ((), ())
        invFun := fun _ => ()
        left_inv := fun value => by cases value; rfl
        right_inv := fun value => by rcases value with ⟨⟨⟩, ⟨⟩⟩; rfl }
  | remaining + 1, position, bounded =>
      (Equiv.prodCongr
        (Equiv.prodCongr (Equiv.refl _)
          (exponentReadoutEquiv base noQuantum m ell width))
        (exponentOutcomeEquiv remaining (position + 1) (by omega))).trans
        (Equiv.prodProdProdComm _ _ _ _)

/-- Reindexing the original finite sum retains every arithmetic outcome and every exponent bit. -/
lemma exponent_outcome_sum_reindex {M : Type} [AddCommMonoid M] (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (function : ExponentOutcomes base noQuantum m ell width modulus wide unit remaining position
      bounded → M) :
    (∑ outcomes, function outcomes) =
      ∑ arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit
          remaining position bounded,
        ∑ readout : Bits remaining,
          function ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining
            position bounded).symm (arithmetic, readout)) := by
  let correspondence := exponentOutcomeEquiv base noQuantum m ell width modulus wide unit
    remaining position bounded
  calc
    _ = ∑ joined, function (correspondence.symm joined) :=
      Fintype.sum_equiv correspondence _ _ (fun outcomes =>
        congrArg function (correspondence.symm_apply_apply outcomes).symm)
    _ = _ := by rw [Fintype.sum_prod_type]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
