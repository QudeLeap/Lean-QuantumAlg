/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.ShortDLP.CompiledMAU.Recycling.Stored.Trajectory
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Frequency
import all QuantumAlg.Primitives.QFT.Semiclassical.Partner.Recycling
import Mathlib.Data.List.OfFn
import Mathlib.Tactic.FinCases

/-!
# Instantiating the shared coherent-partner Fourier factorization

This owner derives the real chronological
feedback angles of Trajectory from the shared QFT updatedAngles recurrence.
Its half sums and old-bank Fourier contraction are the existing shared QFT
definitions and theorems; no generic Fourier proof is copied here. Exact mixed
partner/reference posteriors are compared after removing the old measured bank.

The shared old bank contains the ordered controlled translations at the stated
MSB addresses and the actual complete native inverse/forward Fourier matrix.
Identifying that ordered clean-carrier program with the preexisting full-word
ShortDLP arithmetic schedule remains a separate execution proof. This owner
does not claim an old full-word AlgorithmRun, packing operation or parent retry
program has already been replaced, nor compare unequal full register states.
-/

namespace QuantumAlg.ShortDLP.CompiledMAU.Recycling.PartnerComparison

noncomputable section

open QuantumFourierTransform
open QuantumFourierTransform.Semiclassical
open scoped Kronecker

/-- Dropping a measured head moves exactly its selected native phase into each later angle. -/
private lemma feedbackAngle_head_tail (inverse : Bool) {n : Nat}
    (head : Fin 2) (tail : Bits n) (position : Fin n)
    (count : Nat) (bounded : count ≤ position.val) :
    Trajectory.feedbackAngle inverse (tupleCoordinates (n + 1) (head, tail)) position.succ
        (count + 1) (Nat.succ_le_succ bounded) =
      Trajectory.feedbackAngle inverse (tupleCoordinates n tail) position count bounded +
        if head = 1 then
          if inverse then -(Source.phaseAngle position.val) else Source.phaseAngle position.val
        else 0 := by
  induction count with
  | zero =>
      fin_cases head <;>
        simp [Trajectory.feedbackAngle, tupleCoordinates_head, Fin.val_succ]
  | succ count induction =>
      change
        (Trajectory.feedbackAngle inverse (tupleCoordinates (n + 1) (head, tail)) position.succ
          (count + 1) (by simp only [Fin.val_succ]; omega) +
          if (tupleCoordinates (n + 1) (head, tail) ⟨count + 1, by omega⟩).val = 1 then
            if inverse then -(Source.phaseAngle (position.succ.val - (count + 1) - 1))
            else Source.phaseAngle (position.succ.val - (count + 1) - 1)
          else 0) =
        (Trajectory.feedbackAngle inverse (tupleCoordinates n tail) position count (by omega) +
          if (tupleCoordinates n tail ⟨count, by omega⟩).val = 1 then
            if inverse then -(Source.phaseAngle (position.val - count - 1))
            else Source.phaseAngle (position.val - count - 1)
          else 0) +
          if head = 1 then
            if inverse then -(Source.phaseAngle position.val) else Source.phaseAngle position.val
          else 0
      rw [induction (Nat.le_of_succ_le bounded)]
      have index : (⟨count + 1, by omega⟩ : Fin (n + 1)) =
          (⟨count, by omega⟩ : Fin n).succ := Fin.ext rfl
      have separation : position.succ.val - (count + 1) - 1 = position.val - count - 1 := by
        simp only [Fin.val_succ]
        omega
      rw [index, tupleCoordinates_tail, separation]
      ring

variable {width : Nat} (modulus : Fin (2 ^ width + 1)) [NeZero modulus.val]

/-- The actual clean arithmetic's original MSB-addressed unit-translation family. -/
def powerOperators (bits : Nat) (unit : (ZMod modulus.val)ˣ) :
    Fin bits → UnitaryOperator (Carrier.units modulus.val) :=
  fun position => Carrier.translation modulus (unit ^ (2 ^ position.rev.val))

private lemma powerOperators_tail (n : Nat) (unit : (ZMod modulus.val)ˣ) :
    (fun position : Fin n =>
      (powerOperators modulus (n + 1) unit position.succ :
        HilbertOperator (Carrier.units modulus.val))) =
      fun position : Fin n =>
        (powerOperators modulus n unit position : HilbertOperator (Carrier.units modulus.val)) :=
    by
  funext position
  have address : position.succ.rev.val = position.rev.val := by
    simp only [Fin.val_rev, Fin.val_succ]
    omega
  simp only [powerOperators, address]

/-- An initial angle is an ordinary gate parameter, subsequently updated by the real record. -/
def phasedChoices (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (angles : Fin bits → ℝ) (record : Fin bits → Fin 2) : List (Trajectory.Choice modulus) :=
  List.ofFn fun position : Fin bits =>
    ⟨unit ^ (2 ^ position.rev.val),
      angles position + Trajectory.feedbackAngle inverse record position position.val le_rfl,
      record position⟩

omit [NeZero modulus.val] in
private lemma phasedChoices_zero (inverse : Bool) {bits : Nat}
    (unit : (ZMod modulus.val)ˣ) (record : Fin bits → Fin 2) :
    phasedChoices modulus inverse unit (fun _ => 0) record =
      Trajectory.exponentChoices modulus inverse unit record := by
  simp only [phasedChoices, Trajectory.exponentChoices, zero_add]

omit [NeZero modulus.val] in
/-- The same feedback is shifted by physical distance, retaining all original power addresses. -/
private lemma phasedChoices_succ (inverse : Bool) (n : Nat) (unit : (ZMod modulus.val)ˣ)
    (angles : Fin (n + 1) → ℝ) (head : Fin 2) (tail : Bits n) :
    phasedChoices modulus inverse unit angles (tupleCoordinates (n + 1) (head, tail)) =
      ⟨unit ^ (2 ^ n), angles 0, head⟩ ::
        phasedChoices modulus inverse unit (Partner.updatedAngles inverse n angles head)
          (tupleCoordinates n tail) := by
  rw [phasedChoices, List.ofFn_succ]
  congr 1
  · simp only [Fin.val_rev, Fin.val_zero, Nat.zero_add, Nat.add_sub_cancel,
      Trajectory.feedbackAngle, add_zero, tupleCoordinates_head]
  · unfold phasedChoices
    apply congrArg List.ofFn
    funext position
    have address : position.succ.rev.val = position.rev.val := by
      simp only [Fin.val_rev, Fin.val_succ]
      omega
    rw [address, tupleCoordinates_tail]
    have feedback :
        Trajectory.feedbackAngle inverse (tupleCoordinates (n + 1) (head, tail)) position.succ
            position.succ.val le_rfl =
          Trajectory.feedbackAngle inverse (tupleCoordinates n tail) position position.val le_rfl +
            if head = 1 then
              if inverse then -(Source.phaseAngle position.val) else Source.phaseAngle position.val
            else 0 :=
      feedbackAngle_head_tail inverse head tail position position.val le_rfl
    congr 1
    calc
      _ = angles position.succ +
          (Trajectory.feedbackAngle inverse (tupleCoordinates n tail) position
            position.val le_rfl +
              if head = 1 then
                if inverse then -(Source.phaseAngle position.val)
                else Source.phaseAngle position.val
              else 0) :=
        congrArg (fun angle : ℝ => angles position.succ + angle) feedback
      _ = _ := by
        unfold Partner.updatedAngles
        ring

/-- The real trajectory is the shared QFT half-sum product, with a common untouched reference. -/
lemma phased_sourceProduct_angleKraus (inverse : Bool) (Reference : Register) :
    ∀ (bits : Nat) (unit : (ZMod modulus.val)ˣ) (angles : Fin bits → ℝ) (outcome : Bits bits),
    Trajectory.sourceProduct modulus Reference
        (phasedChoices modulus inverse unit angles (tupleCoordinates bits outcome)) =
      Partner.angleKraus inverse bits
        (fun position => (powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) angles outcome ⊗ₖ
            (1 : HilbertOperator Reference) := by
  intro bits
  induction bits with
  | zero =>
      intro unit angles outcome
      simp only [phasedChoices, List.ofFn_zero, Trajectory.sourceProduct, Partner.angleKraus]
      exact Matrix.one_kronecker_one.symm
  | succ bits induction =>
      intro unit angles outcome
      rcases outcome with ⟨head, tail⟩
      rw [phasedChoices_succ, Trajectory.sourceProduct, induction]
      have step :
          Partner.angleKraus inverse (bits + 1)
              (fun position => (powerOperators modulus (bits + 1) unit position :
                HilbertOperator (Carrier.units modulus.val))) angles (head, tail) =
            Partner.angleKraus inverse bits
                (fun position => (powerOperators modulus (bits + 1) unit position.succ :
                  HilbertOperator (Carrier.units modulus.val)))
                (Partner.updatedAngles inverse bits angles head) tail *
              Partner.halfSum
                (powerOperators modulus (bits + 1) unit 0 :
                  HilbertOperator (Carrier.units modulus.val))
                (Complex.exp ((angles 0 : ℂ) * Complex.I)) head := rfl
      refine Eq.trans ?_ (congrArg
        (fun operator : HilbertOperator (Carrier.units modulus.val) =>
          operator ⊗ₖ (1 : HilbertOperator Reference)) step).symm
      rw [powerOperators_tail]
      have first : powerOperators modulus (bits + 1) unit 0 =
          Carrier.translation modulus (unit ^ (2 ^ bits)) := by
        simp only [powerOperators, Fin.val_rev, Fin.val_zero, Nat.zero_add, Nat.add_sub_cancel]
      rw [first]
      change (_ ⊗ₖ (1 : HilbertOperator Reference)) *
        (Partner.halfSum _ _ _ ⊗ₖ (1 : HilbertOperator Reference)) = _
      rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- Original zero-initialized feedback is a specialization, not a premise of the comparison. -/
lemma sourceProduct_angleKraus (inverse : Bool) {bits : Nat}
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (outcome : Bits bits) :
    Trajectory.sourceProduct modulus Reference
        (Trajectory.exponentChoices modulus inverse unit (tupleCoordinates bits outcome)) =
      Partner.angleKraus inverse bits
        (fun position => (powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) (fun _ => 0) outcome ⊗ₖ
            (1 : HilbertOperator Reference) := by
  rw [← phasedChoices_zero]
  exact phased_sourceProduct_angleKraus modulus inverse Reference bits unit (fun _ => 0) outcome

/-- The measured bank is removed before comparing the complete coherent partner operator. -/
lemma sourceProduct_oldKraus (inverse : Bool) {bits : Nat}
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (outcome : Bits bits) :
    Trajectory.sourceProduct modulus Reference
        (Trajectory.exponentChoices modulus inverse unit (tupleCoordinates bits outcome)) =
      Partner.oldKraus inverse bits
        (fun position => (powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) outcome ⊗ₖ
            (1 : HilbertOperator Reference) := by
  rw [sourceProduct_angleKraus, ← Partner.qftPartner_oldKraus_eq_angleKraus]

/-- A full native Fourier output frequency is compared at its actual reversed physical record. -/
lemma sourceProduct_fullOldKraus (inverse : Bool) {bits : Nat}
    (unit : (ZMod modulus.val)ˣ) (Reference : Register) (frequency : Fin (2 ^ bits)) :
    Trajectory.sourceProduct modulus Reference
        (Trajectory.exponentChoices modulus inverse unit
          (tupleCoordinates bits (frequencyBits bits frequency))) =
      Partner.fullOldKraus inverse bits
        (fun position => (powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) frequency ⊗ₖ
            (1 : HilbertOperator Reference) := by
  rw [sourceProduct_oldKraus, Partner.qftPartner_fullOldKraus_physical]

/-- Exact mixed partner/reference density, including every off-diagonal entry and branch mass. -/
lemma sigma_fullSigma (inverse : Bool) {bits : Nat} (unit : (ZMod modulus.val)ˣ)
    (Reference : Register) (frequency : Fin (2 ^ bits))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    Trajectory.σ modulus Reference
        (Trajectory.exponentChoices modulus inverse unit
          (tupleCoordinates bits (frequencyBits bits frequency))) density =
      Partner.fullSigma inverse bits
        (fun position => (powerOperators modulus bits unit position :
          HilbertOperator (Carrier.units modulus.val))) frequency Reference density := by
  rw [Trajectory.sigma_eq_product, sourceProduct_fullOldKraus]
  rfl

variable (base : RuntimeCtx .quantum) (noQuantum : base.quantumWires = []) (m ell : Nat)

private abbrev Context := context base noQuantum m ell width

/-- Two exact full-bank source posteriors match the actual reused accumulator's sigma_y. -/
lemma memberSigma_fullSigma (generator target : (ZMod modulus.val)ˣ) (Reference : Register)
    (original : Execution.Store (Context (width := width) base noQuantum m ell))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell))
    (density : HilbertOperator ((Carrier.units modulus.val).prod Reference)) :
    MemberInstrument.memberSigma base noQuantum m ell width modulus generator target Reference
        original (frequencyBits (ell + m) first, frequencyBits ell second) density =
      Partner.fullSigma true ell
        (fun position => (powerOperators modulus ell target⁻¹ position :
          HilbertOperator (Carrier.units modulus.val))) second Reference
        (Partner.fullSigma true (ell + m)
          (fun position => (powerOperators modulus (ell + m) generator position :
            HilbertOperator (Carrier.units modulus.val))) first Reference density) := by
  rw [StoredTrajectory.memberSigma_trajectory, Trajectory.memberChoices, Trajectory.sigma_append,
    sigma_fullSigma, sigma_fullSigma]

/-- Existing paid-packing input selects the canonical frequency coordinates of both streams. -/
lemma memberStore_frequencyInput
    (original : Execution.Store (Context (width := width) base noQuantum m ell))
    (first : Fin (2 ^ (ell + m))) (second : Fin (2 ^ ell)) :
    (MemberInstrument.memberStore base noQuantum m ell width original
      (frequencyBits (ell + m) first, frequencyBits ell second)).read
        (frequencyInput base noQuantum m ell width) =
      .fixedVector (fun index => .finite (Fin.addCases
        ((BinaryBasis.bigEndianEquiv (ell + m)).symm first)
        ((BinaryBasis.bigEndianEquiv ell).symm second) index)) := by
  rw [StoredTrajectory.memberStore_frequencyInput]
  simp_rw [Partner.qftPartner_frequency_reversed_coordinate]

end

end QuantumAlg.ShortDLP.CompiledMAU.Recycling.PartnerComparison
