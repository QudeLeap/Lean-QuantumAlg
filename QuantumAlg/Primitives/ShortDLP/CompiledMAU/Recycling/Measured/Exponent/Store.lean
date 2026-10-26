/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Stage.Store

/-!
# Actual complete exponent records retain exactly the same chronological outputs

The compared Store below describes only the original real exponent writes.
The actual interpreter keeps all vent writes and complete histories; these
do not change any retained result used by the next paid feedback. Original
future output values remain arbitrary [G25, main.tex:199-295].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution
open QuantumFourierTransform.Semiclassical (Bits)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpStoreCtx := context base noQuantum m ell width

variable {bits : Nat} (selection : Fin bits → Fin (resultBits m ell))

/-- Only the actual chronological retained exponent writes, with all old values preserved. -/
def exponentOutputStore : (remaining position : Nat) →
    position + remaining ≤ bits → Store (ExpStoreCtx base noQuantum m ell width) →
    Bits remaining → Store (ExpStoreCtx base noQuantum m ell width)
  | 0, _, _, store, _ => store
  | remaining + 1, position, bounded, store, readout =>
      exponentOutputStore remaining (position + 1) (by omega)
        (store.write (resultCell base noQuantum m ell width (selection ⟨position, by omega⟩))
          (.finite readout.1)) readout.2

variable (modulus : BitVec width) (wide : 2 ≤ width) (unit : (ZMod modulus.toNat)ˣ)
  (inverse : Bool)

private lemma exponent_record_store_step (remaining position : Nat)
    (bounded : position + (remaining + 1) ≤ bits)
    (store : Store (ExpStoreCtx base noQuantum m ell width))
    (head : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
      (⟨position, by omega⟩ : Fin bits))
    (tail : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := bits) unit
      remaining (position + 1) (by omega)) (bit : Fin 2) (readout : Bits remaining) :
    (exponentActualRecord base noQuantum m ell width modulus wide unit inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) (remaining + 1)
      position bounded store
      ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit (remaining + 1) position
        bounded).symm ((head, tail), (bit, readout)))).1 =
    (exponentActualRecord base noQuantum m ell width modulus wide unit inverse
      (fun index => resultCell base noQuantum m ell width (selection index)) remaining
      (position + 1) (by omega)
      (stageRecord base noQuantum m ell width modulus wide inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) unit
        (⟨position, by omega⟩ : Fin bits) store head
        ((exponentReadoutEquiv base noQuantum m ell width).symm bit)).1
      ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining (position + 1)
        (by omega)).symm (tail, readout))).1 := rfl

/-- Every complete original exponent record preserves the independently described result writes. -/
lemma exponentRecord_resultStoreAgree (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (first second : Store (ExpStoreCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second)
    (arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
      position bounded) (readout : Bits remaining) :
    ResultStoreAgree base noQuantum m ell width
      (exponentActualRecord base noQuantum m ell width modulus wide unit inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) remaining position
        bounded first ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining
          position bounded).symm (arithmetic, readout))).1
      (exponentOutputStore base noQuantum m ell width selection remaining position bounded second
        readout) := by
  induction remaining generalizing position first second with
  | zero => exact same
  | succ remaining induction =>
      change stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
          (⟨position, by omega⟩ : Fin bits) ×
        ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := bits) unit
          remaining (position + 1) (by omega) at arithmetic
      rcases arithmetic with ⟨head, tail⟩
      rcases readout with ⟨bit, readout⟩
      let current : Fin bits := ⟨position, by omega⟩
      have next := stageRecord_resultStoreAgree base noQuantum m ell width modulus wide inverse
        selection unit current first second same head
        ((exponentReadoutEquiv base noQuantum m ell width).symm bit)
      rw [Equiv.apply_symm_apply] at next
      rw [exponent_record_store_step]
      exact induction (position + 1) (by omega) _ _ next tail readout

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
