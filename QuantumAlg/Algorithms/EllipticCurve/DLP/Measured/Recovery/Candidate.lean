/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Points
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Probability.Recovery.Execution
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Batch.Correctness
import all QuantumAlg.Components.Classical.FiniteCyclicDLP.RawRecovery.Model.Bounds

/-!
# Original selected exponent events pass the actual candidate condition

The original selected event already determines the raw inverse-success flag,
recovered secret word and reconstruction flag. Its natural scalar acts on the
original public base and target points. The original order and Fourier width
internally prove that encoding the secret does not truncate it. The secret is
a proof witness and is never an input to the actual recovery circuit.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP Canonical.Probability
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} {E : PrimeFieldShortWeierstrass p} [Fact p.Prime]
    {kind : ProblemKind} {ctx : RuntimeCtx kind}

/-- Within the original subgroup order, the public point equation identifies the unique secret. -/
theorem bounded_groupScalar_eq_target_iff (problem : KnownOrderProblem E.GroupPoint)
    (input : SecretInput problem) (scalar : Nat) (bounded : scalar < problem.order) :
    scalar • problem.generator.toMathlib = problem.target.toMathlib ↔
      scalar = input.secret.val := by
  rw [groupScalar_eq_target_iff]
  constructor
  · intro accepted
    have sameResidue := pow_inj_mod.mp (accepted.trans input.target_eq_generator_pow.symm)
    have secretBound : input.secret.val < problem.order :=
      (residueIndex problem input.secret).isLt
    rw [← problem.order_eq_orderOf, Nat.mod_eq_of_lt bounded,
      Nat.mod_eq_of_lt secretBound] at sameResidue
    exact sameResidue
  · intro same
    rw [same]
    exact input.target_eq_generator_pow

/-- The actual raw candidate condition recognizes precisely the secret and original two flags. -/
theorem sampleAccepted_iff_secret (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (sample : CShape.Value (.fixedVector (orderWidth problem + orderWidth problem) (.finite 2))) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib sample ↔
      let raw := ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells
        (recoveryModulusSpec problem nontrivial)
        (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.Native.preparationInput sample)
      raw.second.first.toNat = input.secret.val ∧
        raw.first.toBool = true ∧ raw.second.second.toBool = true := by
  dsimp only [SampleAccepted]
  exact and_congr (bounded_groupScalar_eq_target_iff problem input _
    (ClassicalRoutines.FiniteCyclicDLP.RawRecovery.outputCells_candidate_lt
      (recoveryModulusSpec problem nontrivial) _)) Iff.rfl

/-- Every original selected measured event meets the actual raw flags and public point equation. -/
theorem selectedExponentEvent_sampleAccepted (problem : KnownOrderProblem E.GroupPoint)
    (nontrivial : 2 ≤ problem.order) (input : SecretInput problem)
    (measured : CInputRef ctx (.fixedVector (2 * orderWidth problem) (.finite 2)))
    (before : Store ctx)
    (selected : selectedExponentEvent problem input (QubitReadouts.mask (before.read measured)) =
      true) :
    SampleAccepted (Canonical.Layout.curveSpec E) (recoveryModulusSpec problem nontrivial)
      problem.generator.toMathlib problem.target.toMathlib
      (before.read (rawRecoveryInput problem measured)) := by
  have secretFits : input.secret.val < 2 ^ orderWidth problem :=
    lt_of_lt_of_le (residueIndex problem input.secret).isLt (order_le_fourierModulus problem)
  unfold SampleAccepted
  rw [preparationInput_rawRecoveryInput,
    outputCells_selectedExponentEvent problem input _ selected
      (recoveryModulusSpec problem nontrivial) rfl]
  change (input.secret.val % 2 ^ orderWidth problem) • problem.generator.toMathlib =
      problem.target.toMathlib ∧ true = true ∧ true = true
  rw [Nat.mod_eq_of_lt secretFits]
  exact ⟨secret_groupScalar_eq_target problem input, rfl, rfl⟩

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
