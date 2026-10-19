/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Sampling
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Observation.PaidPacking
import all QuantumAlg.Algorithms.FiniteCyclicDLP.Resources.Modulus
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Workspace
import all QuantumAlg.Components.Classical.Model.BitWord.Promotion

/-!
# Actual streaming sampling, checked recovery and finite workspace reuse

The literal zero allocation occurs once. Each declared round then resets the
same physical bank, executes the complete converted stream, reads the reversed
positions inside each chronological result block and runs the original checked
recovery. The seven persistent destinations are retained once. The final option
is allocated and packed once, including when the requested round count is zero.

The live-space bounds charge the complete public context, all seven persistent
cells and the maximum of the actual lexical recovery scratch and final option.
The resulting qubit bound concerns this same full run and every syntactic Path.
No success bound or Algorithm.Solves result is asserted here.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
  (recoveryTailScratchSpace persistentCellSpace recoveryTailScratchSpace_eq_bits
    persistentCellSpace_eq_bits)
open QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction (signedWidth)

private lemma recovery_classical_count_le (fieldWidth sampleWidth : Nat)
    {actual caller : SpacePool .quantum}
    (bounded : actual ≤ recoveryTailScratchSpace .quantum fieldWidth sampleWidth +
      persistentCellSpace .quantum fieldWidth sampleWidth + caller) :
    SpacePool.count .classicalBits actual ≤
      max (25 * sampleWidth + 9 * signedWidth sampleWidth + 16)
          (27 * fieldWidth + 9 * signedWidth fieldWidth + 15) +
        (2 * fieldWidth + 2 * sampleWidth + 5) +
          SpacePool.count .classicalBits caller := by
  have counted := SpacePool.le_iff_count.mp bounded .classicalBits
  simpa only [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    SpacePool.count_add, SpacePool.count_classicalBits_ofShape, CShape.bitWidth] using counted

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.FiniteCyclicDLP (KnownOrderProblem orderWidth)
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native
  (batchResultCtx sampledRecoveryRun sampledRecoveryTail_resident_le
    sampledRecoveryTail_auxiliary_le)
open QuantumAlg.ClassicalRoutines.NumberTheory.Checked.SignedReduction (signedWidth)

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

/-- Read the same physical bits through the checker's equal-width vector index. -/
private def recoveryInput {kind : ProblemKind} {ctx : RuntimeCtx kind} (width : Nat)
    (measured : CInputRef ctx (.fixedVector (2 * width) (.finite 2))) :
    CInputRef ctx (.fixedVector (width + width) (.finite 2)) :=
  .fixedVector fun index => .vectorGet measured (Fin.cast (by omega) index)

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

/-- The same actual reset and converted sampler execute in the fixed public caller. -/
def round : Circuit Model (Recovery.PublicInput.context E (orderWidth problem))
    (Recovery.PublicInput.context E (orderWidth problem)) false :=
  BitWord.selectForCircuit
    (Circuit.embed (allowAllocation := false)
      (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))
      (Recovery.PublicInput.Sampling.body E fieldTail (orderWidth problem) seed r points
        coefficient))

/-- The original complete checker reads the actual chronological cells in canonical bit order. -/
def tailRun (nontrivial : 2 ≤ problem.order) (count : Nat) :
    AlgorithmRun Model (Recovery.PublicInput.context E (orderWidth problem))
      (batchResultCtx (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))
      (.option (.unsignedWord (orderWidth problem))) :=
  sampledRecoveryRun (round E fieldTail problem points seed r coefficient) count
    (ECDLP.Canonical.Layout.curveSpec E)
    (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
    (recoveryInput (orderWidth problem)
      (PaidPacking.callerInput
        (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))))
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem))

/-- One actual allocation precedes all sampling/checking rounds and the one final option pack. -/
def run (nontrivial : 2 ≤ problem.order) (count : Nat) :
    AlgorithmRun Model (Recovery.PublicInput.frame E (orderWidth problem))
      (batchResultCtx (Recovery.PublicInput.context E (orderWidth problem))
        (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem))
      (.option (.unsignedWord (orderWidth problem))) where
  code := (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth
    problem))).seq
    (tailRun E fieldTail problem points seed r coefficient nontrivial count).code
  output := (tailRun E fieldTail problem points seed r coefficient nontrivial count).output

variable (nontrivial : 2 ≤ problem.order) (count : Nat)

/-- The literal execution preserves allocation, retry, checking and packing Paths in full records.
-/
lemma run_execute {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (Model.HiddenState × History)) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.execute environment
      Reference state =
        ((tailRun E fieldTail problem points seed r coefficient nontrivial count).code.execute
          environment Reference ((BitWord.selectForCircuit
            (Recovery.PublicInput.Allocation.circuit E
              (orderWidth problem))).execute environment Reference state)).mapHistory (fun record =>
              (record.1, (record.2.1.1, (record.2.1.2, record.2.2)))) :=
  Circuit.execute_seq environment
    (BitWord.selectForCircuit (Recovery.PublicInput.Allocation.circuit E (orderWidth problem)))
    (tailRun E fieldTail problem points seed r coefficient nontrivial count).code state

/-- Both actual borrowed public points and all their Reference correlations are restored. -/
lemma run_borrowedRestored {Reference : Register} {History : Type} [Fintype History]
    (state : State (Recovery.PublicInput.frame E (orderWidth problem)) Reference
      (Model.HiddenState × History)) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.BorrowedRestored
      Reference state
        ((run E fieldTail problem points seed r coefficient nontrivial count).code.execute
          environment Reference state) := by
  have noBorrowed : (Recovery.PublicInput.frame E (orderWidth problem)).borrowedQuantumWires =
    [] := rfl
  exact Circuit.borrowedRestored_of_noBorrowedQuantum (environment := environment) (model := Model)
    (allowAllocation := true)
    (run E fieldTail problem points seed r coefficient nontrivial count).code
    noBorrowed Reference state

/-- Every complete path charges the full resident public bank, recovery cells and lexical scratch.
-/
lemma run_resident_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.peakResidentSpace
      path ≤
        recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
            (orderWidth problem) +
          persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
            (orderWidth problem) + (Recovery.PublicInput.context E (orderWidth
              problem)).residentSpace := by
  change ((BitWord.selectForCircuit
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).seq
      (tailRun E fieldTail problem points seed r coefficient nontrivial count).code).Path at path
  change ((BitWord.selectForCircuit
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).seq
      (tailRun E fieldTail problem points seed r coefficient nontrivial
        count).code).peakResidentSpace path ≤ _
  rw [Circuit.peakResidentSpace_seq]
  apply SpacePool.max_le
  · have selected := BitWord.selectForCircuit_peakResidentSpace
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))
      ((BitWord.selectForCircuitPathEquiv
        (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).symm path.1)
    simp only [Equiv.apply_symm_apply] at selected
    rw [selected, Recovery.PublicInput.Allocation.circuit_peakResidentSpace]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_resident_le
      (round E fieldTail problem points seed r coefficient) count
      (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
      (recoveryInput (orderWidth problem)
        (PaidPacking.callerInput
          (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))))
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) path.2

/-- The same actual path reuses every owned auxiliary role independently of retry count. -/
lemma run_auxiliary_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    (run E fieldTail problem points seed r coefficient nontrivial count).code.peakAuxiliarySpace
      path ≤
        recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
            (orderWidth problem) +
          persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
            (orderWidth problem) + (Recovery.PublicInput.context E (orderWidth
              problem)).auxiliarySpace := by
  change ((BitWord.selectForCircuit
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).seq
      (tailRun E fieldTail problem points seed r coefficient nontrivial count).code).Path at path
  change ((BitWord.selectForCircuit
    (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).seq
      (tailRun E fieldTail problem points seed r coefficient nontrivial
        count).code).peakAuxiliarySpace path ≤ _
  rw [Circuit.peakAuxiliarySpace_seq]
  apply SpacePool.max_le
  · have selected := BitWord.selectForCircuit_peakAuxiliarySpace
      (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))
      ((BitWord.selectForCircuitPathEquiv
        (Recovery.PublicInput.Allocation.circuit E (orderWidth problem))).symm path.1)
    simp only [Equiv.apply_symm_apply] at selected
    rw [selected, Recovery.PublicInput.Allocation.circuit_peakAuxiliarySpace]
    exact fun _ => Nat.le_add_left _ _
  · exact sampledRecoveryTail_auxiliary_le
      (round E fieldTail problem points seed r coefficient) count
      (ECDLP.Canonical.Layout.curveSpec E)
      (FiniteCyclicDLP.Canonical.resourceModulusSpec problem nontrivial)
      (recoveryInput (orderWidth problem)
        (PaidPacking.callerInput
          (Recovery.PublicInput.AllocatedFixed.placement E (orderWidth problem))))
      (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
      (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) path.2

/-- The full classical bounds retain seven destinations and the actual scratch/final-option max.
-/
lemma run_classical_space_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    let fieldWidth := ECDLP.Canonical.Layout.fieldWidth E
    let sampleWidth := orderWidth problem
    let recoveryBits := max (25 * sampleWidth + 9 * signedWidth sampleWidth + 16)
      (27 * fieldWidth + 9 * signedWidth fieldWidth + 15) +
        (2 * fieldWidth + 2 * sampleWidth + 5)
    SpacePool.count .classicalBits
        ((run E fieldTail problem points seed r coefficient nontrivial
          count).code.peakResidentSpace path) ≤
        recoveryBits + SpacePool.count .classicalBits
          (Recovery.PublicInput.context E sampleWidth).residentSpace ∧
      SpacePool.count .classicalBits
        ((run E fieldTail problem points seed r coefficient nontrivial
          count).code.peakAuxiliarySpace path) ≤
        recoveryBits + SpacePool.count .classicalBits
          (Recovery.PublicInput.context E sampleWidth).auxiliarySpace := by
  dsimp only
  constructor
  · exact recovery_classical_count_le (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (run_resident_le E fieldTail problem points seed r coefficient nontrivial count path)
  · exact recovery_classical_count_le (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem)
      (run_auxiliary_le E fieldTail problem points seed r coefficient nontrivial count path)

/-- No classical recovery cell or lexical scratch introduces a quantum system of any dimension.
-/
lemma run_quantumSystems_le
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path)
    (dimension : ℕ+) :
    SpacePool.count (.quantumSystems dimension)
      ((run E fieldTail problem points seed r coefficient nontrivial
        count).code.peakResidentSpace path) ≤
      if 2 = dimension then 3 * p.size + 4 * p.size.size + 14 else 0 := by
  have bounded := SpacePool.le_iff_count.mp
    (run_resident_le E fieldTail problem points seed r coefficient nontrivial count path)
    (.quantumSystems dimension)
  simpa only [recoveryTailScratchSpace_eq_bits, persistentCellSpace_eq_bits,
    SpacePool.count_add, SpacePool.count_quantumSystems_ofShape, zero_add,
    Recovery.PublicInput.AllocatedFixed.public_quantum_count] using bounded

/-- Every path of allocation, all retries, complete checking and final packing uses at most 818
qubits at field width 256. This is a resource result for the actual run, not a success certificate.
-/
lemma run_width256_qubits_le (width : p.size = 256)
    (path : (run E fieldTail problem points seed r coefficient nontrivial count).code.Path) :
    SpacePool.count (.quantumSystems 2)
      ((run E fieldTail problem points seed r coefficient nontrivial
        count).code.peakResidentSpace path) ≤ 818 := by
  refine (run_quantumSystems_le E fieldTail problem points seed r coefficient
    nontrivial count path 2).trans_eq ?_
  rw [if_pos rfl, width]
  decide

end

end ExecutionContract
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
