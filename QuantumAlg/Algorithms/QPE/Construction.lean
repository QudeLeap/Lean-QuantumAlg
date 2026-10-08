/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Core.Base.Accounting.Kind
import all QuantumAlg.Algorithms.QPE.Analysis
import all QuantumAlg.Algorithms.QPE.Basic
import all QuantumAlg.Algorithms.QPE.Circuit.Action
import all QuantumAlg.Core.Base.UnitaryCircuit.Binary
import all QuantumAlg.Components.Kets
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.UnitaryCircuit
import all QuantumAlg.Core.Base.Layout.Qubit
import all QuantumAlg.Core.Measure
import all QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Primitives.WalshHadamard
import all QuantumAlg.Util.Real.ReciprocalSquareTail
import Mathlib.Data.Nat.Bitwise
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# The actual QPE unitary and its mathematical Born readout

The initial Hadamard layer, explicit controlled-power ladder and inverse QFT
form one executable unitary. Its exact action on an eigenstate gives the
source geometric amplitudes and native query/readout counts
[Lin22, phaseestimation.tex:510-521,647-715].

The layout and Born readout below describe this mathematical state. Runtime
preparation, stored Z outcomes, complete Output and borrowed restoration
belong to the separate native endpoint; no execution engine is defined here.
-/

section

namespace QuantumAlg

open NormalizedVector Gate
open scoped BigOperators

noncomputable section

/-- Metadata-free normalized QPE input with a zeroed phase register and the
supplied eigenstate. -/
def qpeInput {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    NormalizedVector (Qubits (t + n)) :=
  (NormalizedVector.ket (R := Qubits t) (0 : Fin (2 ^ t))).tensor P.eigenstate

/-- The actual native word preserves the supplied eigenstate and produces the original readout. -/
theorem qpeCircuit_applyNormalized_input {n : Nat} (P : QPEEigenstateInput n)
    (t : Nat) :
    (QuantumPhaseEstimation.Native.circuit t P.unitary).binaryMatrix.apply (qpeInput P t) =
      ((invQFT t).apply (phaseState t P.phase)).tensor P.eigenstate :=
  QuantumPhaseEstimation.Native.qpeNative_circuit_apply_eigenstate P t

/-! ### Canonical layout and terminal phase-register measurement -/

/-- Canonical physical placement of the phase and eigenstate registers. -/
def qpeLayout (t n : Nat) : QubitLayout (t + n) where
  physical_idx := fun i => i.val
  physical_idx_injective := fun _ _ h => Fin.ext h

@[simp] theorem qpeLayout_systemIdx (t n : Nat) :
    (qpeLayout t n).systemIdx = List.range (t + n) := by
  simp [qpeLayout, QubitLayout.systemIdx, List.ofFn_eq_pmap]

/-- Normalized, canonically placed QPE input. -/
def qpeInputState {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) where
  state := PureState.ofNormalized (qpeInput P t)
    (qpeLayout t n).systemIdx
  system_idx_eq := rfl

/-- Select the complete phase register in logical order. -/
def qpeMeasurement (t n : Nat) : TerminalZMeasure (qpeLayout t n) t :=
  zMeasureAt (qpeLayout t n)
    (fun i => ⟨i.val, Nat.lt_add_right n i.isLt⟩)
    (fun _ _ h => Fin.ext (Fin.mk.inj h))

/-- Big-endian terminal outcome corresponding to dyadic index `j`. -/
def qpeOutcome (t : Nat) (j : Fin (2 ^ t)) :
    TerminalZMeasure.Outcome t :=
  fun outputIndex => j.val.testBit (t - 1 - outputIndex.val)

/-- The canonical full-register big-endian decoder recovers the QPE phase-grid
index from its terminal bit vector. -/
@[simp] theorem qpeOutcome_fullRegisterIndex (t : Nat)
    (j : Fin (2 ^ t)) :
    TerminalZMeasure.fullRegisterIndex (qpeOutcome t j) = j := by
  apply Fin.val_injective
  change Nat.ofBits ((qpeOutcome t j) ∘ Fin.rev) = j.val
  have hbits :
      (qpeOutcome t j) ∘ Fin.rev =
        fun bit : Fin t => j.val.testBit bit.val := by
    funext bit
    simp only [Function.comp_apply, qpeOutcome]
    apply congrArg j.val.testBit
    calc
      t - 1 - (Fin.rev bit).val = t - ((Fin.rev bit).val + 1) := by
        rw [Nat.sub_sub, Nat.add_comm]
      _ = (Fin.rev (Fin.rev bit)).val := rfl
      _ = bit.val := congrArg Fin.val (Fin.rev_rev bit)
  rw [hbits, Nat.ofBits_testBit, Nat.mod_eq_of_lt j.isLt]

theorem qpeOutcome_injective (t : Nat) :
    Function.Injective (qpeOutcome t) := by
  intro left right h
  apply Fin.ext
  apply Nat.eq_of_testBit_eq
  intro bit
  by_cases hbit : bit < t
  · let outputIndex : Fin t := ⟨t - 1 - bit, by omega⟩
    have hreverse : t - 1 - outputIndex.val = bit := by
      dsimp [outputIndex]
      omega
    have hout := congrFun h outputIndex
    simpa [qpeOutcome, hreverse] using hout
  · have htbit : t ≤ bit := Nat.le_of_not_gt hbit
    have hpow : 2 ^ t ≤ 2 ^ bit :=
      Nat.pow_le_pow_right (by decide : 1 ≤ 2) htbit
    rw [Nat.testBit_eq_false_of_lt (left.isLt.trans_le hpow),
      Nat.testBit_eq_false_of_lt (right.isLt.trans_le hpow)]

@[simp] theorem qpeMeasurement_readout_prod {t n : Nat}
    (j : Fin (2 ^ t)) (y : Fin (2 ^ n)) :
    (qpeMeasurement t n).readout (prodEquiv (j, y)) = qpeOutcome t j := by
  funext outputIndex
  change (prodEquiv (j, y)).val.testBit
      (t + n - 1 - outputIndex.val) =
    j.val.testBit (t - 1 - outputIndex.val)
  have hindex :
      t + n - 1 - outputIndex.val = n + (t - 1 - outputIndex.val) := by
    omega
  rw [hindex]
  exact prodEquiv_testBit_left j y
    ⟨t - 1 - outputIndex.val, by omega⟩

theorem qpeMeasurement_readout_eq_outcome_iff {t n : Nat}
    (basis : Fin (2 ^ (t + n))) (j : Fin (2 ^ t)) :
    (qpeMeasurement t n).readout basis = qpeOutcome t j ↔
      (prodEquiv.symm basis).1 = j := by
  have hself :
      (qpeMeasurement t n).readout basis =
        qpeOutcome t (prodEquiv.symm basis).1 := by
    simpa using qpeMeasurement_readout_prod
      (n := n) (prodEquiv.symm basis).1 (prodEquiv.symm basis).2
  constructor
  · intro h
    exact qpeOutcome_injective t (hself.symm.trans h)
  · intro h
    exact hself.trans (congrArg (qpeOutcome t) h)

/-! ### Measurement probability from the evolved state -/

/-- The normalized state after the exact circuit stored in the algorithm run. -/
def qpeEvolvedState {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    QubitLayout.State (qpeLayout t n) :=
  { state := PureState.ofNormalized
      ((QuantumPhaseEstimation.Native.circuit t P.unitary).binaryMatrix.apply (qpeInput P t))
      (qpeLayout t n).systemIdx
    system_idx_eq := rfl }

theorem qpeEvolvedState_apply_prod {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat)
    (j : Fin (2 ^ t)) (y : Fin (2 ^ n)) :
    (qpeEvolvedState P t).normalized (prodEquiv (j, y)) =
      phaseRegisterGeometricAmplitude t P.phase j * P.eigenstate y := by
  change (QuantumPhaseEstimation.Native.circuit t P.unitary).binaryMatrix.apply
      (qpeInput P t) (prodEquiv (j, y)) = _
  rw [qpeCircuit_applyNormalized_input, NormalizedVector.tensor_apply_prod]
  change (invQFT t).apply (phaseState t P.phase) j * P.eigenstate y = _
  rw [invQFT_phaseState_apply_geometricSum]

/-- Embed the unmeasured eigenstate-register basis into one fixed phase-index
measurement fiber. -/
def qpeFiberEmbedding {t n : Nat} (j : Fin (2 ^ t)) :
    Fin (2 ^ n) ↪ Fin (2 ^ (t + n)) where
  toFun := fun y => prodEquiv (j, y)
  inj' := by
    intro left right h
    cases prodEquiv.injective h
    rfl

@[simp] theorem qpeFiberEmbedding_apply {t n : Nat} (j : Fin (2 ^ t))
    (y : Fin (2 ^ n)) :
    qpeFiberEmbedding j y = prodEquiv (j, y) := rfl

theorem qpeMeasurement_fiber {t n : Nat} (j : Fin (2 ^ t)) :
    Finset.univ.filter
        (fun basis : Fin (2 ^ (t + n)) =>
          (qpeMeasurement t n).readout basis = qpeOutcome t j) =
      Finset.univ.map (qpeFiberEmbedding j) := by
  ext basis
  rw [Finset.mem_filter, qpeMeasurement_readout_eq_outcome_iff]
  simp only [Finset.mem_univ, true_and]
  constructor
  · intro hleft
    apply Finset.mem_map.mpr
    refine ⟨(prodEquiv.symm basis).2, Finset.mem_univ _, ?_⟩
    rw [qpeFiberEmbedding_apply, ← hleft]
    exact
      (Equiv.apply_symm_apply (prodEquiv (m := t) (n := n)) basis)
  · intro hmem
    obtain ⟨y, _, hy⟩ := Finset.mem_map.mp hmem
    change prodEquiv (j, y) = basis at hy
    rw [← hy, Equiv.symm_apply_apply]

theorem qpeMeasurement_outcomePMF_apply {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) (j : Fin (2 ^ t)) :
    (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
        (qpeOutcome t j) =
      ENNReal.ofReal
        (‖phaseRegisterGeometricAmplitude t P.phase j‖ ^ 2) := by
  rw [TerminalZMeasure.outcomePMF_apply, qpeMeasurement_fiber,
    Finset.sum_map]
  simp_rw [qpeFiberEmbedding_apply, qpeEvolvedState_apply_prod, norm_mul, mul_pow,
    ENNReal.ofReal_mul (sq_nonneg _)]
  rw [← Finset.mul_sum]
  have heigen :
      ∑ y : Fin (2 ^ n), ENNReal.ofReal (‖P.eigenstate y‖ ^ 2) = 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun _ _ => sq_nonneg _)]
    rw [← EuclideanSpace.norm_sq_eq, P.eigenstate.norm_eq_one]
    norm_num
  rw [heigen, mul_one]

theorem qpeNearestOutcome_probability_ge {n : Nat}
    (P : QPEEigenstateInput n) (t : Nat) :
    ENNReal.ofReal (4 / Real.pi ^ 2) ≤
      (qpeMeasurement t n).outcomePMF (qpeEvolvedState P t)
        (qpeOutcome t (qpeNearestIndex t P.phase)) := by
  rw [qpeMeasurement_outcomePMF_apply,
    phaseRegisterGeometricAmplitude_nearest_eq_errorAmplitude]
  apply ENNReal.ofReal_le_ofReal
  have hnorm := qpeErrorAmplitude_norm_lower_bound t (qpeRoundedError t P.phase)
    (qpeRoundedError_abs_le t P.phase)
  have hsquare := mul_self_le_mul_self (by positivity : 0 ≤ 2 / Real.pi) hnorm
  calc
    4 / Real.pi ^ 2 = (2 / Real.pi) * (2 / Real.pi) := by
      field_simp [Real.pi_ne_zero]
      ring
    _ ≤ ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ *
        ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ := hsquare
    _ = ‖qpeErrorAmplitude t (qpeRoundedError t P.phase)‖ ^ 2 := by ring

end

end QuantumAlg

end
