/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Solves
public import QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Algorithm
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Context
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Algorithm
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.State
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Recovery.Contract
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Resources.Contract
import all QuantumAlg.Algorithms.EllipticCurve.P256.Measured.Window.Factory.Probability.Success
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Prefix
import all QuantumAlg.Core.Algorithm.AlgorithmRun.Borrowed.NoQuantum

/-!
# The registered P-256 endpoint for one complete paid window execution

The original public input domain, independent problem and all seven Solves
fields concern the same literal secret-independent algorithm. Supporting
probability, state and resource owners do not import this endpoint.
-/

namespace QuantumAlg.EllipticCurve.P256LogicalResources

noncomputable section

open QuantumAlg.Execution
open QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open QuantumAlg.EllipticCurve.P256
open QuantumAlg.EllipticCurve.P256.Measured
open QuantumAlg.EllipticCurve.P256.Measured.Window
open QuantumAlg.ClassicalRoutines.EllipticCurve

local instance {Label : Type} : DecidableEq Label := Classical.decEq Label

/-- Certified P-256 ECDLP with original inputs and bounded checked answers.

**Input.**
- The original two-point domain, with the certified base and target values and
  every normalized extension by an arbitrary external Reference. No initialized
  workspace or additional preparation certificate is required.
**Output.**
- An optional 260-bit word. An accepted word represents a scalar below the
  original subgroup order whose multiple of the base equals the target.
**Resource budget.**
- Independent complete-run limits include allocation, table preparation,
  three resets and checked attempts, cleanup and result packing.
- The allowance adds 854 qubits and 85,101,142 classical bits to the caller's
  storage, bounds Toffoli, CNOT and single-qubit gates by 99,272,733,288,
  81,134,896,044 and 25,700,867,624, and bounds quantum time by 171,185,448,791.
- A finite event allowance also retains every modeled preparation, measurement
  and native classical operation; circuit-construction costs remain separate.
**Success.**
- The accepted output has probability at least 99 percent on every valid input.
  Every output leaves the retained owned bank in physical zero.
- The separate mandatory borrowed-state obligation restores the full borrowed
  classical data and their quantum-reference correlations.
**Source.**
- [PZ03, ecc.tex:448-556] supplies the group-shift and measured Fourier
  construction. The independent window limits and three-round guarantee are
  project derivations proved for the same actual execution.
-/
public def problem (I : DomainParameters.PublicKeyInstance) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model)
      (Pre I) (Post I) OutputShape where
  Witness := Unit
  valid := fun _ _ => ECDLP.Measured.Recovery.PublicInput.Support.inputDomain
    (DomainParameters.curve I.curveCert) (Cascade.exponentWidth I)
    (ECDLP.Canonical.problem (Cascade.ecdlpInstance I))
  initialization := fun _ _ _ => True
  accepts := fun _ _ _ output => Recovery.AcceptedOutput I output
  successLB := fun _ _ => LogicalResources.successLowerBound ((1 : ℝ) / 100)
  states := fun _ _ => [zeroRequirement I]
  resources := Factory.resourceBudget .empty (Pre I) I
  quantumTimeLimit := Factory.quantumTimeBudget

private lemma snd_singleton_probability {A B : Type}
    (distribution : PMF (A × B)) (value : B) :
    distribution.toOuterMeasure (Prod.snd ⁻¹' {value}) =
      (distribution.map Prod.snd) value :=
  (PMF.toOuterMeasure_map_apply Prod.snd distribution {value}).symm.trans
    (PMF.toOuterMeasure_apply_singleton (distribution.map Prod.snd) value)

private lemma candidate_success_floor : 1 - ENNReal.ofReal ((1 : ℝ) / 100) ≤
    ENNReal.ofReal ((124 : ℝ) / 125) := by
  rw [← ENNReal.ofReal_one,
    ← ENNReal.ofReal_sub 1 (show (0 : ℝ) ≤ 1 / 100 by norm_num)]
  exact ENNReal.ofReal_le_ofReal (by norm_num)

private def CandidateSuccessStatement : Prop :=
  ∀ (I : DomainParameters.PublicKeyInstance)
    (environment : (ExecutionModel.quantum AlgorithmGate.model .empty BitWord.model).Environment)
    {Reference : Register} (supplied : OracleInput .empty (Window.Pre I) Reference)
    (_valid : (problem I).valid environment () supplied.caller.localState),
    ((problem I).successLB environment ()).value ≤
      ((Window.algorithm I).relationalDistribution environment supplied).toOuterMeasure
        {pair | (problem I).accepts environment () pair.1 pair.2}

private lemma candidate_success : CandidateSuccessStatement := by
  intro I environment Reference supplied valid
  let secret := FiniteCyclicDLP.Canonical.Probability.SecretInput.ofKnownOrderProblem
    (ECDLP.Canonical.problem (P256.Cascade.ecdlpInstance I))
  let wanted : CShape.Value Window.OutputShape :=
    .optionSome (CShape.wordOfNat 260 secret.secret.val)
  have output := Factory.paidRun_secret_probability_ge I environment secret supplied valid
  have sameRun : (Window.algorithm I).run =
      Factory.paidRun (services := .empty)
        (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
        (Factory.publicBaseRef I) (Factory.publicTargetRef I) := rfl
  have sameOutput := congrArg (fun run : AlgorithmRun
    (.quantum AlgorithmGate.model .empty BitWord.model)
      (Window.Pre I) (Window.Post I) Window.OutputShape =>
        run.outputDistribution environment supplied wanted) sameRun
  have sameFunction :
      @AlgorithmRun.outputDistribution true
        (.quantum AlgorithmGate.model .empty BitWord.model)
        (Window.Pre I) (Window.Post I) Window.OutputShape =
      @AlgorithmRun.outputDistribution true
        (.quantum AlgorithmGate.model .empty BitWord.model)
        (Factory.publicFrame I)
        (CandidateCheck.Native.batchResultCtx
          (Factory.tableContext (Factory.publicFrame I) (Factory.publicFrame_noQuantum I)) 256 260)
        (.option (.unsignedWord 260)) := rfl
  have parameterOutput := congrArg (fun law => law
    (Factory.paidRun (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I)) environment supplied wanted)
        sameFunction
  have publicOutput := output.trans_eq (sameOutput.trans parameterOutput).symm
  have accepted :
      {pair : Store (Window.Pre I) × CShape.Value Window.OutputShape |
        (problem I).accepts environment () pair.1 pair.2} = Prod.snd ⁻¹' {wanted} := by
    ext pair
    exact Window.Recovery.acceptedOutput_iff_secret I secret pair.2
  have projection := snd_singleton_probability
    ((Window.algorithm I).run.relationalDistribution environment supplied) wanted
  have marginal := congrArg (fun law : PMF (CShape.Value Window.OutputShape) => law wanted)
    (AlgorithmRun.relationalDistribution_map_output (Window.algorithm I).run environment supplied)
  change 1 - ENNReal.ofReal ((1 : ℝ) / 100) ≤ _
  rw [accepted]
  exact candidate_success_floor.trans (publicOutput.trans_eq (projection.trans marginal).symm)

attribute [local irreducible] Circuit.resourcePool

private lemma candidate_solves (I : P256.DomainParameters.PublicKeyInstance) :
    (Window.algorithm I).Solves (problem I) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro environment witness Reference supplied valid _initialized
    cases witness
    exact candidate_success I environment supplied valid
  · intro environment _witness Reference supplied _valid _initialized requirement member
    change requirement ∈ [Window.zeroRequirement I] at member
    rcases List.mem_singleton.mp member with rfl
    exact Factory.paidRun_zero_requirement (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I) environment supplied
  · intro environment _witness Reference supplied _valid _initialized
    have noBorrowed : (Window.Pre I).borrowedQuantumWires = [] := by
      have sub := (Window.Pre I).borrowedQuantumWires_sublist
      rw [Window.pre_noQuantum I] at sub
      exact List.sublist_nil.mp sub
    exact AlgorithmRun.restoresBorrowed_of_noBorrowedQuantum
      (environment := environment) (Window.algorithm I).run noBorrowed supplied
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact Factory.paidRun_events_le (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I) path
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact Factory.paidRun_resident_budget (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I) path
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact Factory.paidRun_auxiliary_budget (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I) path
  · intro _environment _witness _Reference _supplied _valid _initialized path _supported
    exact Factory.paidRun_time_budget (services := .empty)
      (Factory.publicFrame I) (Factory.publicFrame_noQuantum I) I
      (Factory.publicBaseRef I) (Factory.publicTargetRef I) path

/-- One secret-independent paid window algorithm satisfies every original-input
correctness, state, borrowed-restoration and resource obligation. -/
public theorem main (I : P256.DomainParameters.PublicKeyInstance) :
    ∃ candidate : Algorithm (.quantum AlgorithmGate.model .empty BitWord.model)
        (Window.Pre I) (Window.Post I) Window.OutputShape,
      candidate.Solves (problem I) :=
  ⟨Window.algorithm I, candidate_solves I⟩

end

end QuantumAlg.EllipticCurve.P256LogicalResources
