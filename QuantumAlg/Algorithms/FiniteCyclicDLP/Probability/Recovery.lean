/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
public import QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model
public import QuantumAlg.Util.FinPow
public import Mathlib.Algebra.Group.Units.Defs
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Readout.Outcome
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Probability.Fiber
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model

/-!
# Original selected-frequency recovery mathematics

The original selected raw inputs and fixed-width recovery proofs retain their
full names and bodies. The secret occurs only as a mathematical witness; the
raw recovery model computes its own rescaling, checked inverse and verification.
-/

namespace QuantumAlg.FiniteCyclicDLP.Canonical.Probability

open scoped BigOperators

noncomputable section

universe u

variable {G : Type u} [Group G]

/-- The raw terminal bit string selected by one invertible Fourier residue.
The second raw frequency encodes only the hidden-line relation; this
definition does not claim that a classical routine has recovered the secret. -/
@[expose] public def selectedRawOutcome (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) : BornBridge.Outcome P :=
  BornBridge.measurementOutcome P
    (prodEquiv
      (selectedIndex P (unit : ZMod P.order),
        selectedIndex P (-input.secret * (unit : ZMod P.order))))

/-- Predicate selecting exactly the useful raw terminal family. -/
@[expose] public def SelectedRawOutcome (P : KnownOrderProblem G) (input : SecretInput P)
    (outcome : BornBridge.Outcome P) : Prop :=
  ∃ unit : (ZMod P.order)ˣ, outcome = selectedRawOutcome P input unit

/-- The selected raw outcome uniquely determines its unit parameter. -/
public lemma selectedRawOutcome_injective (P : KnownOrderProblem G)
    (input : SecretInput P) : Function.Injective (selectedRawOutcome P input) := by
  intro left right h
  have hpacked := BornBridge.measurementOutcome_injective P h
  have hpair := prodEquiv.injective hpacked
  have hleft :
      selectedIndex P (left : ZMod P.order) =
        selectedIndex P (right : ZMod P.order) :=
    congrArg Prod.fst hpair
  exact Units.ext (selectedIndex_injective P hleft)

/-! ## Pure fixed-width recovery bridge -/

namespace RecoveryBridge

open ClassicalAlgorithms.Modular

/-- Store one selected big-endian terminal outcome in the exact raw shape
consumed by the fixed-width recovery routine. -/
@[expose] public def selectedRawInput (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ) :
    CShape.Value
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.InputShape
        (orderWidth P)) :=
  .bits (selectedRawOutcome P input unit)

/-- The raw decoder sees the packed selected Fourier pair, with the left
register in the high half and the right register in the low half. -/
lemma decodedTerminal_selectedRawInput (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.decodedTerminal
        (selectedRawInput P input unit) =
      (prodEquiv
        (selectedIndex P (unit : ZMod P.order),
          selectedIndex P (-input.secret * (unit : ZMod P.order)))).val := by
  change ClassicalAlgorithms.TerminalDecode.decodeNat
      { order := .bigEndian, bits := selectedRawOutcome P input unit } = _
  rw [ClassicalAlgorithms.TerminalDecode.decodeNat_bigEndian]
  exact congrArg Fin.val
    (BornBridge.fullRegisterIndex_measurementOutcome P _)

lemma leftRaw_selectedRawInput (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.leftRaw
        (selectedRawInput P input unit) =
      (selectedIndex P (unit : ZMod P.order)).val := by
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.leftRaw,
    decodedTerminal_selectedRawInput]
  simpa using (prodEquiv_symm_fst_val
    (prodEquiv
      (selectedIndex P (unit : ZMod P.order),
        selectedIndex P (-input.secret * (unit : ZMod P.order))))).symm

lemma rightRaw_selectedRawInput (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ) :
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.rightRaw
        (selectedRawInput P input unit) =
      (selectedIndex P (-input.secret * (unit : ZMod P.order))).val := by
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.rightRaw,
    decodedTerminal_selectedRawInput]
  simpa using (prodEquiv_symm_snd_val
    (prodEquiv
      (selectedIndex P (unit : ZMod P.order),
        selectedIndex P (-input.secret * (unit : ZMod P.order))))).symm

/-- Integer rescaling of the selected left raw frequency returns the canonical
representative of the selected unit. -/
lemma normalize_selectedRawInput_left_val (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)).left.val =
      (unit : ZMod P.order).val := by
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.scaleFrequency,
    leftRaw_selectedRawInput]
  change
    ((selectedIndex P (unit : ZMod P.order)).val * spec.modulus /
      2 ^ orderWidth P) % spec.modulus = _
  rw [hspec]
  change
    ((selectedRawFrequency P (residueIndex P (unit : ZMod P.order))).val *
      P.order / fourierModulus P) % P.order = _
  rw [selectedRawFrequency_scale]
  exact Nat.mod_eq_of_lt (residueIndex P (unit : ZMod P.order)).isLt

/-- Integer rescaling of the selected right raw frequency returns the
canonical representative of the negated hidden-line frequency. -/
lemma normalize_selectedRawInput_right_val (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)).right.val =
      (-input.secret * (unit : ZMod P.order)).val := by
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize,
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.scaleFrequency,
    rightRaw_selectedRawInput]
  change
    ((selectedIndex P (-input.secret * (unit : ZMod P.order))).val *
      spec.modulus / 2 ^ orderWidth P) % spec.modulus = _
  rw [hspec]
  change
    ((selectedRawFrequency P
      (residueIndex P (-input.secret * (unit : ZMod P.order)))).val *
      P.order / fourierModulus P) % P.order = _
  rw [selectedRawFrequency_scale]
  exact Nat.mod_eq_of_lt
    (residueIndex P (-input.secret * (unit : ZMod P.order))).isLt

/-- The normalized selected unit remains a checked-inverse input that is
coprime to the represented group order. -/
lemma normalize_selectedRawInput_left_coprime (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    Nat.Coprime
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
        (selectedRawInput P input unit)).left.val
      spec.modulus := by
  rw [normalize_selectedRawInput_left_val P input unit spec hspec, hspec]
  exact ZMod.val_coe_unit_coprime unit

/-- Checked inversion therefore selects its canonical inverse payload rather
than the failure branch. -/
lemma checkedInverse_selectedRawInput (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    ClassicalAlgorithms.NumberTheory.TryInv.eval spec
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
          (selectedRawInput P input unit)).left =
      some (ClassicalAlgorithms.NumberTheory.inverseCandidate spec
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
          (selectedRawInput P input unit)).left) := by
  exact
    ClassicalAlgorithms.NumberTheory.TryInv.tryInv_eval_some_value
      spec _ (normalize_selectedRawInput_left_coprime P input unit spec hspec)

/-- Modular negation of the normalized right frequency is exactly the
canonical representative of `secret * unit`. -/
lemma negateRight_selectedRawInput_val (P : KnownOrderProblem G)
    (input : SecretInput P) (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight spec
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
        (selectedRawInput P input unit))).val =
      (input.secret * (unit : ZMod P.order)).val := by
  let normalized :=
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)
  have hright : normalized.right.val =
      (-input.secret * (unit : ZMod P.order)).val :=
    normalize_selectedRawInput_right_val P input unit spec hspec
  have hnegCast :
      ((spec.modulus - normalized.right.val : Nat) : ZMod P.order) =
        input.secret * (unit : ZMod P.order) := by
    let _ : NeZero P.order := ⟨P.order_ne_zero⟩
    have hrightLe : normalized.right.val ≤ spec.modulus :=
      normalized.right.isLt.le
    have hmodCast : (spec.modulus : ZMod P.order) = 0 := by
      rw [hspec]
      exact ZMod.natCast_self P.order
    have hrightCast :
        (normalized.right.val : ZMod P.order) =
          -input.secret * (unit : ZMod P.order) := by
      rw [hright, ZMod.natCast_zmod_val]
    rw [Nat.cast_sub hrightLe, hmodCast, hrightCast]
    ring
  unfold ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight
  change (spec.modulus - normalized.right.val) % spec.modulus = _
  have hval := congrArg ZMod.val hnegCast
  simpa [ZMod.val_natCast, hspec] using hval

/-- The fixed-width helper fed by the successful checked inverse returns the
advertised secret as its canonical candidate. -/
lemma helperOutput_selectedRawInput_candidate_val
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    let normalized :=
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
        (selectedRawInput P input unit)
    let inverse :=
      ClassicalAlgorithms.NumberTheory.inverseCandidate spec
        normalized.left
    (ClassicalRoutines.FiniteCyclicDLP.outputOf spec
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
        normalized inverse)).candidate.val = input.secret.val := by
  let normalized :=
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)
  let inverse :=
    ClassicalAlgorithms.NumberTheory.inverseCandidate spec
      normalized.left
  let _ : NeZero P.order := ⟨P.order_ne_zero⟩
  have hcoprime : Nat.Coprime normalized.left.val spec.modulus :=
    normalize_selectedRawInput_left_coprime P input unit spec hspec
  have hleft : normalized.left.val = (unit : ZMod P.order).val :=
    normalize_selectedRawInput_left_val P input unit spec hspec
  have hnegated :
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight spec
        normalized).val = (input.secret * (unit : ZMod P.order)).val :=
    negateRight_selectedRawInput_val P input unit spec hspec
  have hinverseLaw :
      normalized.left.val * inverse.val % spec.modulus = 1 :=
    ClassicalAlgorithms.NumberTheory.inverseCandidate_mul_mod
      spec normalized.left hcoprime
  have honeLt : 1 < P.order := by
    have : 2 ≤ P.order := hspec ▸ spec.two_le
    omega
  have hinverseCast :
      (unit : ZMod P.order) * (inverse.val : ZMod P.order) = 1 := by
    have hcast :
        ((normalized.left.val * inverse.val : Nat) : ZMod P.order) = 1 := by
      have hcast' := (ZMod.natCast_eq_natCast_iff'
        (normalized.left.val * inverse.val) 1 P.order).2 (by
          simpa [hspec, Nat.mod_eq_of_lt honeLt] using hinverseLaw)
      norm_num at hcast' ⊢
      exact hcast'
    rw [Nat.cast_mul, hleft, ZMod.natCast_zmod_val] at hcast
    exact hcast
  let candidate :=
    (ClassicalRoutines.FiniteCyclicDLP.outputOf spec
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
        normalized inverse)).candidate
  have hcandidateCast : (candidate.val : ZMod P.order) = input.secret := by
    have hmodulus :
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight
            spec normalized).val * inverse.val % spec.modulus =
          (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight
            spec normalized).val * inverse.val % P.order :=
      congrArg
        (fun modulus =>
          (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight
              spec normalized).val * inverse.val % modulus)
        hspec
    change
      ((((ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight
        spec normalized).val * inverse.val) % spec.modulus : Nat) :
          ZMod P.order) = input.secret
    rw [hmodulus, ZMod.natCast_mod, Nat.cast_mul, hnegated,
      ZMod.natCast_zmod_val]
    calc
      input.secret * (unit : ZMod P.order) * (inverse.val : ZMod P.order) =
          input.secret *
            ((unit : ZMod P.order) * (inverse.val : ZMod P.order)) := by ring
      _ = input.secret := by rw [hinverseCast, mul_one]
  calc
    candidate.val = ((candidate.val : ZMod P.order)).val := by
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
      exact candidate.isLt.trans_eq hspec
    _ = input.secret.val := congrArg ZMod.val hcandidateCast

/-- The independent reconstruction check accepts the recovered selected
candidate. -/
lemma helperOutput_selectedRawInput_verified
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    let normalized :=
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
        (selectedRawInput P input unit)
    let inverse :=
      ClassicalAlgorithms.NumberTheory.inverseCandidate spec
        normalized.left
    (ClassicalRoutines.FiniteCyclicDLP.outputOf spec
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
        normalized inverse)).verified = true := by
  let normalized :=
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)
  let inverse :=
    ClassicalAlgorithms.NumberTheory.inverseCandidate spec
      normalized.left
  let helper :=
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
      normalized inverse
  have hcandidate :=
    helperOutput_selectedRawInput_candidate_val P input unit spec hspec
  have hleft : normalized.left.val = (unit : ZMod P.order).val :=
    normalize_selectedRawInput_left_val P input unit spec hspec
  have hnegated :
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight spec
        normalized).val = (input.secret * (unit : ZMod P.order)).val :=
    negateRight_selectedRawInput_val P input unit spec hspec
  change decide
      (((ClassicalRoutines.FiniteCyclicDLP.recoverValue spec helper).val *
        helper.leftFrequency.val) % spec.modulus =
        helper.negatedRightFrequency.val) = true
  rw [decide_eq_true_eq]
  change
    ((ClassicalRoutines.FiniteCyclicDLP.outputOf spec helper).candidate.val *
        normalized.left.val) % spec.modulus =
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.negateRight spec
        normalized).val
  rw [hcandidate, hleft, hnegated, hspec]
  exact (ZMod.val_mul input.secret (unit : ZMod P.order)).symm

/-- On a selected raw terminal outcome, the pure raw-recovery model takes its
successful checked-inverse branch. -/
lemma outputOf_selectedRawInput
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    let normalized :=
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
        (selectedRawInput P input unit)
    let inverse :=
      ClassicalAlgorithms.NumberTheory.inverseCandidate spec
        normalized.left
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
        (selectedRawInput P input unit) =
      some (ClassicalRoutines.FiniteCyclicDLP.outputOf spec
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
          normalized inverse)) := by
  simp only
  rw [ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf_checked_inverse]
  rw [checkedInverse_selectedRawInput P input unit spec hspec]

/-- Complete pure semantic bridge used by endpoint integration: the selected
raw outcome yields `some` candidate, that candidate is the advertised secret,
and the reconstruction flag is true. -/
public lemma outputOf_selectedRawInput_recovers
    (P : KnownOrderProblem G) (input : SecretInput P)
    (unit : (ZMod P.order)ˣ)
    (spec : ModulusSpec (orderWidth P)) (hspec : spec.modulus = P.order) :
    ∃ output : ClassicalRoutines.FiniteCyclicDLP.Output spec,
      ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputOf spec
          (selectedRawInput P input unit) = some output ∧
        output.candidate.val = input.secret.val ∧ output.verified = true := by
  let normalized :=
    ClassicalRoutines.FiniteCyclicDLP.RawRecovery.normalize spec
      (selectedRawInput P input unit)
  let inverse :=
    ClassicalAlgorithms.NumberTheory.inverseCandidate spec
      normalized.left
  let output :=
    ClassicalRoutines.FiniteCyclicDLP.outputOf spec
      (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.helperInput spec
        normalized inverse)
  refine ⟨output, outputOf_selectedRawInput P input unit spec hspec, ?_, ?_⟩
  · exact helperOutput_selectedRawInput_candidate_val P input unit spec hspec
  · exact helperOutput_selectedRawInput_verified P input unit spec hspec

end RecoveryBridge

end

end QuantumAlg.FiniteCyclicDLP.Canonical.Probability
