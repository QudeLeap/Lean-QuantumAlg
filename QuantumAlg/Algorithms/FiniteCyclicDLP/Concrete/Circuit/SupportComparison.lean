/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.FiniteCyclicDLP.Concrete.BornBridge.State
import all QuantumAlg.Core.Base.Gate.SupportHybrid
import all QuantumAlg.Core.Measure.Stability

/-!
# Support-restricted comparison for finite-cyclic DLP circuits

This module compares a candidate oracle circuit with a clean
`ConcreteCircuitAccess` when they agree only on an explicit predicate over the
two prepared exponent registers.  All carrier widths remain parameters.  The
comparison uses the exact finite-range preparation support and charges the
complementary branches through a Born-mass bound.
-/

section

namespace QuantumAlg
namespace FiniteCyclicDLP
namespace ConcreteCircuitAccess
namespace SupportComparison

noncomputable section

universe u

variable {G : Type u} [Group G]
variable {P : KnownOrderProblem G}

/-- One pair of Fourier exponent labels for the supplied problem. -/
abbrev Branch (P : KnownOrderProblem G) :=
  Fin (2 ^ orderWidth P) × Fin (2 ^ orderWidth P)

/-- Product amplitude of one pair of exact finite-range exponent states. -/
def preparationAmplitude (P : KnownOrderProblem G) (branch : Branch P) : ℂ :=
  Concrete.BornBridge.exponentState P branch.1 *
    Concrete.BornBridge.exponentState P branch.2

/-- Both exponent labels lie in the range populated by preparation. -/
def InSourceRange (P : KnownOrderProblem G) (branch : Branch P) : Prop :=
  branch.1.val < P.order ∧ branch.2.val < P.order

/-- Exact support of the two finite-range exponent preparations. -/
def supportBranches (P : KnownOrderProblem G) : Finset (Branch P) := by
  classical
  exact Finset.univ.filter (InSourceRange P)

@[simp] theorem mem_supportBranches (P : KnownOrderProblem G)
    (branch : Branch P) :
    branch ∈ supportBranches P ↔ InSourceRange P branch := by
  classical
  simp [supportBranches]

/-- Every branch outside the exact prepared support has zero amplitude. -/
theorem preparationAmplitude_eq_zero_of_not_inSourceRange
    (P : KnownOrderProblem G) (branch : Branch P)
    (outside : ¬ InSourceRange P branch) :
    preparationAmplitude P branch = 0 := by
  by_cases leftRange : branch.1.val < P.order
  · have rightOutside : ¬ branch.2.val < P.order := by
      intro rightRange
      exact outside ⟨leftRange, rightRange⟩
    simp [preparationAmplitude, Concrete.BornBridge.exponentState_apply,
      leftRange, rightOutside]
  · simp [preparationAmplitude, Concrete.BornBridge.exponentState_apply,
      leftRange]

/-- Every supported branch has reciprocal-square Born mass. -/
theorem preparationAmplitude_norm_sq_of_inSourceRange
    (P : KnownOrderProblem G) (branch : Branch P)
    (inRange : InSourceRange P branch) :
    ‖preparationAmplitude P branch‖ ^ 2 =
      ((P.order : ℝ)⁻¹) * ((P.order : ℝ)⁻¹) := by
  have amplitude : preparationAmplitude P branch =
      invSqrtOrder P.order * invSqrtOrder P.order := by
    simp [preparationAmplitude, Concrete.BornBridge.exponentState_apply,
      inRange.1, inRange.2]
  rw [amplitude]
  calc
    ‖invSqrtOrder P.order * invSqrtOrder P.order‖ ^ 2 =
        ‖invSqrtOrder P.order‖ ^ 2 *
          ‖invSqrtOrder P.order‖ ^ 2 := by
      rw [Complex.norm_mul]
      ring
    _ = ((P.order : ℝ)⁻¹) * ((P.order : ℝ)⁻¹) := by
      rw [norm_sq_invSqrtOrder P.order_pos]

/-- Basis label of one prepared branch with the access clean identity tail. -/
def preparedSourceLabel (A : ConcreteCircuitAccess P) (branch : Branch P) :
    Fin (2 ^ A.totalQubits) :=
  A.encoding.encode ((branch.1, branch.2), A.cleanTail 1)

/-- Prepared source labels are injective in their exponent branch. -/
theorem preparedSourceLabel_injective (A : ConcreteCircuitAccess P) :
    Function.Injective (preparedSourceLabel A) := by
  intro left right equality
  have decoded := A.encoding.encode_injective equality
  exact Prod.ext
    (congrArg (fun value => value.1.1) decoded)
    (congrArg (fun value => value.1.2) decoded)

private def preparedIndexEquiv (A : ConcreteCircuitAccess P) :
    (Branch P × Fin (2 ^ A.tailEncoding.width)) ≃
      Fin (2 ^ A.totalQubits) :=
  (Equiv.prodCongr
      (prodEquiv (m := orderWidth P) (n := orderWidth P))
      (Equiv.refl _)).trans
    (prodEquiv
      (m := orderWidth P + orderWidth P)
      (n := A.tailEncoding.width))

@[simp] private theorem preparedIndexEquiv_apply
    (A : ConcreteCircuitAccess P) (branch : Branch P)
    (tail : Fin (2 ^ A.tailEncoding.width)) :
    preparedIndexEquiv A (branch, tail) =
      Concrete.BornBridge.fullIndex A branch.1 branch.2 tail :=
  rfl

/-- Pointwise amplitude of the exact prepared state in natural coordinates. -/
theorem preparedVec_apply (A : ConcreteCircuitAccess P)
    (branch : Branch P) (tail : Fin (2 ^ A.tailEncoding.width)) :
    Concrete.BornBridge.preparedVec A
        (Concrete.BornBridge.fullIndex A branch.1 branch.2 tail) =
      preparationAmplitude P branch *
        if tail = A.tailEncoding.encode (A.cleanTail 1) then 1 else 0 := by
  simp [Concrete.BornBridge.preparedVec, Concrete.BornBridge.fullIndex,
    preparationAmplitude, NormalizedVector.ket_apply]

/-- Exact computational-basis expansion delivered to the oracle. -/
theorem preparedVec_expansion (A : ConcreteCircuitAccess P) :
    (∑ branch : Branch P,
      preparationAmplitude P branch •
        (NormalizedVector.ket (R := Qubits A.totalQubits)
          (preparedSourceLabel A branch) :
          HilbertVector (Qubits A.totalQubits))) =
      Concrete.BornBridge.preparedVec A := by
  classical
  have expansion := HilbertVector.sum_amplitude_smul_ket
    (Concrete.BornBridge.preparedVec A)
  rw [← Equiv.sum_comp (preparedIndexEquiv A),
    Fintype.sum_prod_type] at expansion
  have expanded :
      (∑ branch : Branch P,
        ∑ tail : Fin (2 ^ A.tailEncoding.width),
          Concrete.BornBridge.preparedVec A
              (Concrete.BornBridge.fullIndex A branch.1 branch.2 tail) •
            (NormalizedVector.ket (R := Qubits A.totalQubits)
              (Concrete.BornBridge.fullIndex A branch.1 branch.2 tail) :
              HilbertVector (Qubits A.totalQubits))) =
        Concrete.BornBridge.preparedVec A := by
    simpa only [preparedIndexEquiv_apply] using expansion
  rw [← expanded]
  apply Finset.sum_congr rfl
  intro branch _
  rw [Finset.sum_eq_single (A.tailEncoding.encode (A.cleanTail 1))]
  · rw [preparedVec_apply]
    simp only [if_pos, mul_one, preparedSourceLabel,
      Concrete.BornBridge.encoding_encode]
  · intro tail _ tailNe
    rw [preparedVec_apply]
    simp only [tailNe, if_false, mul_zero, zero_smul]
  · simp

/-- The exact expansion restricted to the branches actually populated by
finite-range preparation. -/
theorem preparedVec_support_expansion (A : ConcreteCircuitAccess P) :
    (∑ branch ∈ supportBranches P,
      preparationAmplitude P branch •
        (NormalizedVector.ket (R := Qubits A.totalQubits)
          (preparedSourceLabel A branch) :
          HilbertVector (Qubits A.totalQubits))) =
      Concrete.BornBridge.preparedVec A := by
  classical
  rw [supportBranches, Finset.sum_filter_of_ne]
  · exact preparedVec_expansion A
  · intro branch _ nonzeroTerm
    by_contra outside
    apply nonzeroTerm
    rw [preparationAmplitude_eq_zero_of_not_inSourceRange P branch outside,
      zero_smul]

/-- Prepared support on which the candidate oracle agrees with the access. -/
def goodBranches (P : KnownOrderProblem G) (Good : Branch P → Prop) :
    Finset (Branch P) := by
  classical
  exact (supportBranches P).filter Good

/-- Complementary exceptional branches inside the exact prepared support. -/
def badBranches (P : KnownOrderProblem G) (Good : Branch P → Prop) :
    Finset (Branch P) := by
  classical
  exact (supportBranches P).filter fun branch => ¬ Good branch

theorem goodBranches_union_badBranches
    (P : KnownOrderProblem G) (Good : Branch P → Prop) :
    goodBranches P Good ∪ badBranches P Good = supportBranches P := by
  classical
  ext branch
  by_cases supported : branch ∈ supportBranches P <;>
    by_cases good : Good branch <;>
      simp [goodBranches, badBranches, supported, good]

theorem goodBranches_disjoint_badBranches
    (P : KnownOrderProblem G) (Good : Branch P → Prop) :
    Disjoint (goodBranches P Good) (badBranches P Good) := by
  classical
  rw [Finset.disjoint_left]
  intro branch goodMember badMember
  exact (Finset.mem_filter.mp badMember).2
    (Finset.mem_filter.mp goodMember).2

/-- Exceptional Born mass induced by one branch agreement predicate. -/
def exceptionalMass (P : KnownOrderProblem G) (Good : Branch P → Prop) : ℝ :=
  ∑ branch ∈ badBranches P Good, ‖preparationAmplitude P branch‖ ^ 2

/-- Exceptional mass is the exceptional branch count times the common
per-branch Born mass. -/
theorem exceptionalMass_eq_card_mul_inv_sq
    (P : KnownOrderProblem G) (Good : Branch P → Prop) :
    exceptionalMass P Good =
      (badBranches P Good).card *
        (((P.order : ℝ)⁻¹) * ((P.order : ℝ)⁻¹)) := by
  classical
  unfold exceptionalMass
  calc
    (∑ branch ∈ badBranches P Good,
        ‖preparationAmplitude P branch‖ ^ 2) =
        ∑ _branch ∈ badBranches P Good,
          ((P.order : ℝ)⁻¹) * ((P.order : ℝ)⁻¹) := by
      apply Finset.sum_congr rfl
      intro branch member
      apply preparationAmplitude_norm_sq_of_inSourceRange P branch
      exact (mem_supportBranches P branch).mp
        (Finset.mem_filter.mp member).1
    _ = (badBranches P Good).card *
        (((P.order : ℝ)⁻¹) * ((P.order : ℝ)⁻¹)) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- A branch-count certificate gives a direct exceptional Born-mass bound. -/
theorem exceptionalMass_le_of_card_bound
    (P : KnownOrderProblem G) (Good : Branch P → Prop)
    (budget : Nat) (orderAtLeastTwo : 2 ≤ P.order)
    (cardBound :
      (P.order - 1) * (badBranches P Good).card ≤
        (P.order * P.order) * budget) :
    exceptionalMass P Good ≤
      (budget : ℝ) / ((P.order - 1 : Nat) : ℝ) := by
  have orderPositive : 0 < (P.order : ℝ) := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) orderAtLeastTwo)
  have predecessorPositive : 0 < ((P.order - 1 : Nat) : ℝ) := by
    exact_mod_cast Nat.sub_pos_of_lt
      (lt_of_lt_of_le Nat.one_lt_two orderAtLeastTwo)
  have cardBoundReal :
      ((((P.order - 1) * (badBranches P Good).card : Nat) : ℝ) ≤
        (((P.order * P.order) * budget : Nat) : ℝ)) := by
    exact_mod_cast cardBound
  rw [exceptionalMass_eq_card_mul_inv_sq]
  have massForm :
      ((badBranches P Good).card : ℝ) *
          ((P.order : ℝ)⁻¹ * (P.order : ℝ)⁻¹) =
        ((badBranches P Good).card : ℝ) /
          ((P.order : ℝ) * (P.order : ℝ)) := by
    field_simp
  rw [massForm]
  refine (div_le_div_iff₀
    (a := ((badBranches P Good).card : ℝ))
    (b := (P.order : ℝ) * (P.order : ℝ))
    (c := (budget : ℝ))
    (d := ((P.order - 1 : Nat) : ℝ))
    (mul_pos orderPositive orderPositive) predecessorPositive).2 ?_
  simpa only [Nat.cast_mul, mul_comm, mul_left_comm, mul_assoc] using
    cardBoundReal

/-- Orthogonality evaluates the exceptional prepared component exactly. -/
theorem norm_badPart (A : ConcreteCircuitAccess P) (Good : Branch P → Prop) :
    ‖∑ branch ∈ badBranches P Good,
        preparationAmplitude P branch •
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch) :
            HilbertVector (Qubits A.totalQubits))‖ =
      Real.sqrt (exceptionalMass P Good) := by
  simpa only [exceptionalMass] using
    (HilbertVector.norm_sum_smul_ket_eq_sqrt_sum_norm_sq
      (R := Qubits A.totalQubits) (Branch := Branch P)
      (badBranches P Good) (preparedSourceLabel A)
      (preparedSourceLabel_injective A) (preparationAmplitude P))

/-- Candidate and ideal oracle outputs differ by at most twice the square root
of the exceptional prepared mass. -/
theorem oracleDistance_le (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits))
    (Good : Branch P → Prop)
    (agrees : ∀ branch, Good branch →
      actualOracle.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch)) =
        A.oracleCircuit.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch))) :
    ‖actualOracle.matrix.applyVec (Concrete.BornBridge.preparedVec A) -
        A.oracleCircuit.matrix.applyVec (Concrete.BornBridge.preparedVec A)‖ ≤
      2 * Real.sqrt (exceptionalMass P Good) := by
  classical
  have agreesRaw : ∀ branch ∈ goodBranches P Good,
      actualOracle.matrix.applyVec
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch) :
            HilbertVector (Qubits A.totalQubits)) =
        A.oracleCircuit.matrix.applyVec
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch) :
            HilbertVector (Qubits A.totalQubits)) := by
    intro branch member
    have action := congrArg
      (fun state : NormalizedVector (Qubits A.totalQubits) =>
        (state : HilbertVector (Qubits A.totalQubits)))
      (agrees branch (Finset.mem_filter.mp member).2)
    simpa only [UnitaryCircuit.applyNormalized_coe, UnitaryCircuit.applyVec,
      UnitaryOperator.apply_coe] using action
  have hybrid :=
    UnitaryOperator.applyVec_sub_norm_le_two_mul_badBranchPart_norm
      actualOracle.matrix A.oracleCircuit.matrix
      (supportBranches P) (goodBranches P Good) (badBranches P Good)
      (goodBranches_union_badBranches P Good)
      (goodBranches_disjoint_badBranches P Good)
      (preparedSourceLabel A) (preparationAmplitude P) agreesRaw
      (Concrete.BornBridge.preparedVec A) (preparedVec_support_expansion A)
  rw [norm_badPart A Good] at hybrid
  exact hybrid

/-- Prepare, execute the candidate oracle, and apply the access readout on one
common carrier. -/
def actualFullCircuit (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits)) :
    UnitaryCircuit (Qubits A.totalQubits) :=
  UnitaryCircuit.seq A.preparationCircuit
    (UnitaryCircuit.seq actualOracle A.readoutCircuit)

/-- A full-footprint candidate oracle yields a full-footprint comparison
circuit. -/
theorem actualFullCircuit_physical_idx (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits))
    (actualPhysical : actualOracle.physical_idx = List.range A.totalQubits) :
    (actualFullCircuit A actualOracle).physical_idx = A.layout.systemIdx := by
  rw [ConcreteCircuitAccess.layout_systemIdx]
  simp only [actualFullCircuit, UnitaryCircuit.seq,
    ConcreteCircuitAccess.preparationCircuit_physical_idx, actualPhysical,
    ConcreteCircuitAccess.readoutCircuit_physical_idx,
    UnitaryCircuit.unionPhysicalIdx_self]

/-- Candidate post-readout state on the access layout. -/
def actualTerminalState (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits)) :
    QubitLayout.State A.layout where
  state := PureState.ofNormalized
    ((actualFullCircuit A actualOracle).applyNormalized A.preparation.normalized)
    A.layout.systemIdx
  system_idx_eq := rfl

/-- Access post-readout state on its canonical layout. -/
def idealTerminalState (A : ConcreteCircuitAccess P) :
    QubitLayout.State A.layout where
  state := PureState.ofNormalized
    (A.fullCircuit.applyNormalized A.preparation.normalized)
    A.layout.systemIdx
  system_idx_eq := rfl

@[simp] theorem actualTerminalState_normalized (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits)) :
    (actualTerminalState A actualOracle).normalized =
      (actualFullCircuit A actualOracle).applyNormalized
        A.preparation.normalized :=
  rfl

@[simp] theorem idealTerminalState_normalized (A : ConcreteCircuitAccess P) :
    (idealTerminalState A).normalized =
      A.fullCircuit.applyNormalized A.preparation.normalized :=
  rfl

/-- The sealed preparation descriptor produces the exact vector used by the
support comparison. -/
theorem preparationCircuit_apply_normalized (A : ConcreteCircuitAccess P) :
    A.preparationCircuit.applyVec
        (A.preparation.normalized : HilbertVector (Qubits A.totalQubits)) =
      Concrete.BornBridge.preparedVec A := by
  simpa only [ConcreteCircuitAccess.preparation,
    KnownPreparation.normalized_basis, ConcreteCircuitAccess.cleanState,
    Concrete.BornBridge.encoding_encode] using
      (Concrete.BornBridge.preparation_apply_input A)

/-- The common inverse-QFT readout preserves the support-hybrid distance. -/
theorem terminalStateDistance_le (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits))
    (Good : Branch P → Prop)
    (agrees : ∀ branch, Good branch →
      actualOracle.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch)) =
        A.oracleCircuit.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch))) :
    ‖((actualTerminalState A actualOracle).normalized :
          HilbertVector (Qubits A.totalQubits)) -
        ((idealTerminalState A).normalized :
          HilbertVector (Qubits A.totalQubits))‖ ≤
      2 * Real.sqrt (exceptionalMass P Good) := by
  have oracleBound := oracleDistance_le A actualOracle Good agrees
  calc
    ‖((actualTerminalState A actualOracle).normalized :
          HilbertVector (Qubits A.totalQubits)) -
        ((idealTerminalState A).normalized :
          HilbertVector (Qubits A.totalQubits))‖ =
        ‖A.readoutCircuit.matrix.applyVec
          (actualOracle.matrix.applyVec (Concrete.BornBridge.preparedVec A) -
            A.oracleCircuit.matrix.applyVec
              (Concrete.BornBridge.preparedVec A))‖ := by
      rw [UnitaryOperator.applyVec_sub]
      simp only [actualTerminalState_normalized, idealTerminalState_normalized,
        actualFullCircuit, ConcreteCircuitAccess.fullCircuit,
        UnitaryCircuit.applyNormalized_coe]
      rw [UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq,
        UnitaryCircuit.applyVec_seq, UnitaryCircuit.applyVec_seq]
      rw [preparationCircuit_apply_normalized]
      rfl
    _ = ‖actualOracle.matrix.applyVec (Concrete.BornBridge.preparedVec A) -
          A.oracleCircuit.matrix.applyVec
            (Concrete.BornBridge.preparedVec A)‖ :=
      A.readoutCircuit.matrix.norm_applyVec _
    _ ≤ 2 * Real.sqrt (exceptionalMass P Good) := oracleBound

/-- Every ideal terminal event is bounded by the candidate event plus four
times the square root of the exceptional prepared mass. -/
theorem idealEvent_le_actual_add (A : ConcreteCircuitAccess P)
    (actualOracle : UnitaryCircuit (Qubits A.totalQubits))
    (_actualPhysical : actualOracle.physical_idx = List.range A.totalQubits)
    (Good : Branch P → Prop)
    (agrees : ∀ branch, Good branch →
      actualOracle.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch)) =
        A.oracleCircuit.applyNormalized
          (NormalizedVector.ket (R := Qubits A.totalQubits)
            (preparedSourceLabel A branch)))
    (event : Set (TerminalZMeasure.Outcome (orderWidth P + orderWidth P))) :
    (A.measurement.outcomePMF (idealTerminalState A)).toOuterMeasure event ≤
      (A.measurement.outcomePMF (actualTerminalState A actualOracle)).toOuterMeasure
          event +
        ENNReal.ofReal (4 * Real.sqrt (exceptionalMass P Good)) := by
  have forwardDistance := terminalStateDistance_le A actualOracle Good agrees
  have reverseDistance :
      ‖((idealTerminalState A).normalized :
          HilbertVector (Qubits A.totalQubits)) -
        ((actualTerminalState A actualOracle).normalized :
          HilbertVector (Qubits A.totalQubits))‖ ≤
        2 * Real.sqrt (exceptionalMass P Good) := by
    simpa only [norm_sub_rev] using forwardDistance
  have stability :=
    TerminalZMeasure.outcomePMF_toOuterMeasure_le_add_of_norm_sub_le
      A.measurement (idealTerminalState A)
      (actualTerminalState A actualOracle) event reverseDistance
  have slackEquality :
      2 * (2 * Real.sqrt (exceptionalMass P Good)) =
        4 * Real.sqrt (exceptionalMass P Good) := by
    ring
  simpa only [slackEquality] using stability

end

end SupportComparison
end ConcreteCircuitAccess
end FiniteCyclicDLP
end QuantumAlg

end
