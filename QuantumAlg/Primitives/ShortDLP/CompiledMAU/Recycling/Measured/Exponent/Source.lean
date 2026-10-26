/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Matrix
import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Measured.Exponent.Store

/-!
# Complete logical exponent products independent of arithmetic histories

Every source factor reads the retained outputs of the actual paid-feedback
program. The original arithmetic histories are reindexed bijectively and
proved irrelevant to this source matrix; they are not discarded by a free
classical instruction. The same unnormalized accumulator/reference matrix
passes through every factor [G25, main.tex:199-295,354-360].
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured

noncomputable section

open Execution MAU.Multiplication.Gidney.Measured EncodedBit.MeasuredUncompute
open QuantumFourierTransform.Semiclassical (Bits)

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = [])
  (m ell width : Nat)

private abbrev ExpSourceCtx := context base noQuantum m ell width

variable (modulus : BitVec width) [NeZero modulus.toNat] (wide : 2 ≤ width) {bits : Nat}
  (unit : (ZMod modulus.toNat)ˣ) (inverse : Bool)
  (selection : Fin bits → Fin (resultBits m ell))

private lemma stage_source_resultStore (position : Fin bits) (Reference : Register)
    (first second : Store (ExpSourceCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second) (outcome : Fin 2) :
    stageSourceKraus base noQuantum m ell width modulus inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) unit position
        Reference first outcome =
      stageSourceKraus base noQuantum m ell width modulus inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) unit position
        Reference second outcome := by
  unfold stageSourceKraus
  rw [feedbackScalar_resultStoreAgree base noQuantum m ell width inverse selection position first
    second same position.val le_rfl]

/-- Chronological half-sums read the independently described actual retained output writes. -/
def exponentReadoutSource (Reference : Register) : (remaining position : Nat) →
    position + remaining ≤ bits → Store (ExpSourceCtx base noQuantum m ell width) →
    Bits remaining → HilbertOperator ((Recycling.Carrier.units modulus.toNat).prod Reference)
  | 0, _, _, _, _ => 1
  | remaining + 1, position, bounded, store, readout =>
      let current : Fin bits := ⟨position, by omega⟩
      exponentReadoutSource Reference remaining (position + 1) (by omega)
          (store.write (resultCell base noQuantum m ell width (selection current))
            (.finite readout.1)) readout.2 *
        stageSourceKraus base noQuantum m ell width modulus inverse
          (fun index => resultCell base noQuantum m ell width (selection index)) unit current
          Reference store readout.1

private lemma exponent_source_step (Reference : Register) (remaining position : Nat)
    (bounded : position + (remaining + 1) ≤ bits)
    (store : Store (ExpSourceCtx base noQuantum m ell width))
    (head : stageArithmeticOutcomes base noQuantum m ell width modulus wide unit
      (⟨position, by omega⟩ : Fin bits))
    (tail : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide (bits := bits) unit
      remaining (position + 1) (by omega)) (bit : Fin 2) (readout : Bits remaining) :
    exponentSourceKraus base noQuantum m ell width modulus wide unit inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) Reference
        (remaining + 1) position bounded store
        ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit (remaining + 1) position
          bounded).symm ((head, tail), (bit, readout))) =
      exponentSourceKraus base noQuantum m ell width modulus wide unit inverse
          (fun index => resultCell base noQuantum m ell width (selection index)) Reference remaining
          (position + 1) (by omega)
          (stageRecord base noQuantum m ell width modulus wide inverse
            (fun index => resultCell base noQuantum m ell width (selection index)) unit
            (⟨position, by omega⟩ : Fin bits) store head
            ((exponentReadoutEquiv base noQuantum m ell width).symm bit)).1
          ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining
            (position + 1) (by omega)).symm (tail, readout)) *
        stageSourceKraus base noQuantum m ell width modulus inverse
          (fun index => resultCell base noQuantum m ell width (selection index)) unit
          (⟨position, by omega⟩ : Fin bits) Reference store bit := rfl

/-- All arithmetic histories yield the same complete logical source for the retained bits. -/
lemma exponentSourceKraus_readout (Reference : Register) (remaining position : Nat)
    (bounded : position + remaining ≤ bits)
    (first second : Store (ExpSourceCtx base noQuantum m ell width))
    (same : ResultStoreAgree base noQuantum m ell width first second)
    (arithmetic : ExponentArithmeticOutcomes base noQuantum m ell width modulus wide unit remaining
      position bounded) (readout : Bits remaining) :
    exponentSourceKraus base noQuantum m ell width modulus wide unit inverse
        (fun index => resultCell base noQuantum m ell width (selection index)) Reference remaining
        position bounded first
        ((exponentOutcomeEquiv base noQuantum m ell width modulus wide unit remaining position
          bounded).symm (arithmetic, readout)) =
      exponentReadoutSource base noQuantum m ell width modulus unit inverse selection Reference
        remaining position bounded second readout := by
  induction remaining generalizing position first second with
  | zero => rfl
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
      have tailEquation := induction (position + 1) (by omega)
        (stageRecord base noQuantum m ell width modulus wide inverse
          (fun index => resultCell base noQuantum m ell width (selection index)) unit current first
          head ((exponentReadoutEquiv base noQuantum m ell width).symm bit)).1
        (second.write (resultCell base noQuantum m ell width (selection current)) (.finite bit))
        next tail readout
      rw [exponent_source_step]
      change _ = (_ * _)
      rw [tailEquation,
        stage_source_resultStore base noQuantum m ell width modulus unit inverse selection current
          Reference first second same bit]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.Measured
