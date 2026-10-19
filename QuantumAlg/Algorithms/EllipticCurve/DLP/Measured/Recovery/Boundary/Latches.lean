/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Boundary.Execution
import all QuantumAlg.Components.Classical.EllipticCurve.CandidateCheck.Native.Sampling.First

/-!
# First accepted values at both native completed-section boundaries

The statement quantifies over all incoming states, finite histories, external References
and positive output records, with no sampled-success hypothesis. Both real resets
preserve the persistent latches. The reused boundary omits exactly the leading reset,
and the complete original checker remains present.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
namespace ExecutionContract.Boundary

noncomputable section

variable {environment : (ExecutionModel.quantum AlgorithmGate.model .empty
  BitWord.model).Environment}

open QuantumAlg QuantumAlg.Execution
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open FiniteCyclicDLP
open QuantumAlg.ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty BitWord.model

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (r : Nat) (coefficient : (ZMod p)ˣ)

/-- A previously accepted scalar survives in every complete positive execution block. -/
def RetainsFirst (code : Circuit Model (sectionCtx E problem) (sectionCtx E problem)) : Prop :=
  ∀ (wanted : (CShape.unsignedWord (orderWidth problem)).Value)
    {Reference : Register} {History : Type} [Fintype History]
    (state : State (sectionCtx E problem) Reference (Model.HiddenState × History)),
    (∀ entry, 0 < (state.block entry).mass →
      (entry.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true ∧
        entry.1.read (.storage (persistentSelected _ _ _).toCStorageRef) = wanted) →
    ∀ result, 0 < ((code.execute environment Reference state).block result).mass →
      (result.1.read (.storage (persistentAccepted _ _ _).toCStorageRef)).toBool = true ∧
        result.1.read (.storage (persistentSelected _ _ _).toCStorageRef) = wanted

omit [Fact p.Prime] in
private lemma retainsFirst_seq
    (left right : Circuit Model (sectionCtx E problem) (sectionCtx E problem))
    (leftKeeps : RetainsFirst (environment := environment) E problem left) (rightKeeps :
      RetainsFirst (environment := environment) E problem right) :
    RetainsFirst (environment := environment) E problem (left.seq right) := by
  intro wanted
  exact preservesStore_seq (model := Model) (ctx := sectionCtx E problem) left right
    (firstSelected (model := Model) (ctx := Recovery.PublicInput.context E (orderWidth problem))
      (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) wanted)
    (leftKeeps wanted) (rightKeeps wanted)

private lemma reset_retainsFirst : RetainsFirst (environment := environment) E problem (reset E
  fieldTail problem seed) := by
  intro wanted Reference History _ state holds result positive
  exact sampled_supported_first (resetChild E fieldTail problem seed)
    (ECDLP.Canonical.Layout.fieldWidth E) (orderWidth problem) wanted state holds result positive

private lemma body_retainsFirst (nontrivial : 2 ≤ problem.order) :
    RetainsFirst (environment := environment) E problem (body E problem points r coefficient
      nontrivial) := by
  intro wanted Reference History _ state holds result positive
  exact sampledAttempt_preserves_first (readoutChild E problem points r coefficient)
    (ECDLP.Canonical.Layout.curveSpec E)
    (Canonical.resourceModulusSpec problem nontrivial) (sample E problem)
    (Recovery.PublicInput.contextBaseRef E (orderWidth problem))
    (Recovery.PublicInput.contextTargetRef E (orderWidth problem)) state wanted holds result
      positive

/-- The first completed section retains the original first-success latch and word through resets.
-/
lemma first_retainsFirst (nontrivial : 2 ≤ problem.order) :
    RetainsFirst (environment := environment) E problem (first E fieldTail problem points seed r
      coefficient nontrivial) :=
  retainsFirst_seq E problem _ _
    (retainsFirst_seq E problem _ _ (reset_retainsFirst E fieldTail problem seed)
      (body_retainsFirst E problem points r coefficient nontrivial))
    (reset_retainsFirst E fieldTail problem seed)

/-- The reused section retains the same first value through complete checking and the next reset.
-/
lemma reused_retainsFirst (nontrivial : 2 ≤ problem.order) :
    RetainsFirst (environment := environment) E problem (reused E fieldTail problem points seed r
      coefficient nontrivial) :=
  retainsFirst_seq E problem _ _ (body_retainsFirst E problem points r coefficient nontrivial)
    (reset_retainsFirst E fieldTail problem seed)

end

end ExecutionContract.Boundary
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery
