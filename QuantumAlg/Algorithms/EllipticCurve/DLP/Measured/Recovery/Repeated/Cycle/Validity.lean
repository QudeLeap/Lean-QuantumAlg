/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Selection

/-!
# Sound accepted-scalar retention through complete checked ECC sections

These laws hold for actual first and reused nonterminal sections, including
their physical reset boundaries, with arbitrary quantum references and histories.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution ContextUnion FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

/-- The borrowed public points and scalar equation for an accepted word,
read from the actual persistent classical store. -/
def CheckedSelectionValid
    (problem : KnownOrderProblem E.GroupPoint)
    (store : Store (persistentCtx (PublicInput.terminal E (orderWidth problem))
      (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  PointRepresents (Canonical.Layout.curveSpec E)
    (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
      (PublicInput.terminalBaseRef E (orderWidth problem)))) problem.generator.toMathlib ∧
  PointRepresents (Canonical.Layout.curveSpec E)
    (store.read (persistentInput (Canonical.Layout.fieldWidth E) (orderWidth problem)
      (PublicInput.terminalTargetRef E (orderWidth problem)))) problem.target.toMathlib ∧
  ((store.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true →
    (store.read (.storage (persistentSelected _ _ _).toCStorageRef)).toNat •
      problem.generator.toMathlib = problem.target.toMathlib)

/-- A real persistent section preserves the public-point interpretations and
equation of every accepted selected word on all supported histories. -/
def RetainsValidity
    (problem : KnownOrderProblem E.GroupPoint)
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))) : Prop :=
  ∀ {Reference : Register} {H : Type} [Fintype H]
    (state : State _ Reference (ClassicalOracleModel.empty.HiddenState × H)),
    (∀ entry, 0 < (state.block entry).mass → CheckedSelectionValid E problem entry.1) →
      ∀ result, 0 < ((code.execute Reference state).block result).mass →
        CheckedSelectionValid E problem result.1

private theorem retainsValidity_seq
    (first second : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem))
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)))
    (left : RetainsValidity E problem first)
    (right : RetainsValidity E problem second) :
    RetainsValidity E problem (first.seq second) := by
  intro Reference H _ state holds result positive
  rw [Circuit.execute_seq] at positive
  obtain ⟨original, equality, present⟩ := (mapped_positive _ _ _ _).mp positive
  have kept := right (first.execute Reference state) (left state holds) original present
  rw [← equality]
  exact kept

private theorem underPersistent_retainsValidity
    (code : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)))
    (supported : code.IsLocal) :
    RetainsValidity E problem
      (underPersistent code supported (Canonical.Layout.fieldWidth E)
        (orderWidth problem)) := by
  intro Reference H _ state holds result positive
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  have publicPoints := PublicInput.persistentProgram_preserves_represents E
    (orderWidth problem) problem
    (underPersistent code supported (Canonical.Layout.fieldWidth E)
      (orderWidth problem)) noQuantum state
    (fun entry present => ⟨(holds entry present).1, (holds entry present).2.1⟩)
    result positive
  have sound := underPersistent_latches_property code supported
    (Canonical.Layout.fieldWidth E) (orderWidth problem)
    (fun pair => pair.1 = true → pair.2.toNat •
      problem.generator.toMathlib = problem.target.toMathlib)
    state (fun entry present => (holds entry present).2.2) result positive
  exact ⟨publicPoints.1, publicPoints.2, sound⟩

private theorem reset_retainsValidity :
    RetainsValidity E problem
      (persistentSamplingReset E fieldTail sameWidth fits problem seed) := by
  let raw := samplingReset E fieldTail (orderWidth problem) sameWidth fits seed
  let selected : Circuit (.quantum AlgorithmGate.model .empty BitWord.model)
      (PublicInput.terminal E (orderWidth problem))
      (PublicInput.terminal E (orderWidth problem)) := BitWord.selectForCircuit raw
  have supported : selected.IsLocal := BitWord.selectForCircuit_isLocal raw
    (samplingReset_isLocal E fieldTail (orderWidth problem) sameWidth fits seed)
  have sameCode :
      persistentSamplingReset E fieldTail sameWidth fits problem seed =
        underPersistent selected supported (Canonical.Layout.fieldWidth E)
          (orderWidth problem) := by
    rfl
  rw [sameCode]
  intro Reference H _ state holds result positive
  exact underPersistent_retainsValidity E problem selected supported
    state holds result positive

/-- The terminal readout/check body preserves admitted public-point validity
and the accepted scalar without requiring a following reset. -/
theorem checkedSectionBody_retainsValidity :
    RetainsValidity E problem
      ((persistentSamplingReadout E fieldTail odd problem points).seq
        (persistentCheckedRecovery E problem nontrivial)) := by
  intro Reference H _ state holds result positive
  let measured := inputLeft (PublicInput.terminal_disjoint E (orderWidth problem))
    (QubitReadouts.input (exponentMeasurementCells p (orderWidth problem)))
  let raw := samplingReadout E fieldTail odd problem points
  let selected := BitWord.selectForCircuit raw
  let supported := BitWord.selectForCircuit_isLocal raw
    (samplingReadout_isLocal E fieldTail odd problem points)
  have noQuantum :
      (persistentCtx (PublicInput.terminal E (orderWidth problem))
        (Canonical.Layout.fieldWidth E) (orderWidth problem)).borrowedQuantumWires = [] :=
    (persistentCtx_borrowedQuantumWires _ _ _).trans
      (PublicInput.terminal_noBorrowedQuantum E (orderWidth problem))
  have localPoints : ∀ entry,
      0 < (((underPersistent selected supported (Canonical.Layout.fieldWidth E)
        (orderWidth problem)).execute Reference state).block entry).mass →
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalBaseRef E (orderWidth problem))))
          problem.generator.toMathlib ∧
      PointRepresents (Canonical.Layout.curveSpec E)
        (entry.1.read (persistentInput (Canonical.Layout.fieldWidth E)
          (orderWidth problem) (PublicInput.terminalTargetRef E (orderWidth problem))))
          problem.target.toMathlib := by
    intro entry present
    exact PublicInput.persistentProgram_preserves_represents E (orderWidth problem)
      problem (underPersistent selected supported (Canonical.Layout.fieldWidth E)
        (orderWidth problem)) noQuantum state
      (fun previous source => ⟨(holds previous source).1, (holds previous source).2.1⟩)
      entry present
  exact sampledAttempt_preserves_validity selected supported
    (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
    (rawRecoveryInput problem measured) (PublicInput.terminalBaseRef E (orderWidth problem))
    (PublicInput.terminalTargetRef E (orderWidth problem))
    problem.generator.toMathlib problem.target.toMathlib state holds localPoints result positive

/-- The first complete nonterminal checked section preserves admitted point
representations and accepted-scalar soundness through both physical resets. -/
theorem firstCheckedSection_retainsValidity :
    RetainsValidity E problem
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) := by
  exact retainsValidity_seq E problem _ _
    (retainsValidity_seq E problem _ _
      (reset_retainsValidity E fieldTail sameWidth fits problem seed)
      (checkedSectionBody_retainsValidity E fieldTail odd problem points nontrivial))
    (reset_retainsValidity E fieldTail sameWidth fits problem seed)

/-- Every reused complete nonterminal checked section preserves the same
public-point and accepted-scalar invariant through its real following reset. -/
theorem reusedCheckedSection_retainsValidity :
    RetainsValidity E problem
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) := by
  exact retainsValidity_seq E problem _ _
    (checkedSectionBody_retainsValidity E fieldTail odd problem points nontrivial)
    (reset_retainsValidity E fieldTail sameWidth fits problem seed)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
