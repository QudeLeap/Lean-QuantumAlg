/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Cycle.Admission

/-!
# Admitting actual checked ECC sections to the next independent cycle protocol

The generic conversion keeps both protocol arguments abstract. The ECC
instances supply the full actual next-input domain and the physical reset seed.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured

noncomputable section

open Execution FiniteCyclicDLP
open ClassicalRoutines.EllipticCurve ClassicalRoutines.EllipticCurve.CandidateCheck.Native

private theorem entryCompatible_cycles
    {model : ExecutionModel} {pre mid post : RuntimeCtx model.kind}
    {leftShape shape : CShape}
    (left : Problem model pre mid leftShape)
    (right : Problem model mid post shape)
    (code : Circuit model pre mid)
    (step : ∀ (Reference : Register)
      (input : Execution.OracleInput model.classicalOracles pre Reference),
      left.Admits input → right.Admits (code.nextInput input)) :
    Circuit.EntryCompatible (.cycle left) (.cycle right) code := by
  exact step

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]
  (fieldTail : Nat) (sameWidth : fieldTail.succ = p.size)
  (fits : p < 2 ^ fieldTail.succ) (odd : Odd p)
  (problem : KnownOrderProblem E.GroupPoint)
  (points : Fin (2 * orderWidth problem) → AffinePoint E) (seed : AffinePoint E)
  (nontrivial : 2 ≤ problem.order)

private theorem firstCheckedSection_admits_reused
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    ∀ (Reference : Register) (input : OracleInput .empty _ Reference),
      (checkedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).Admits input →
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).Admits
        ((firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial).nextInput input) := by
  intro Reference input admitted
  have valid : checkedSectionInputDomain E problem input.caller.localState := admitted.1
  exact ⟨firstCheckedSection_nextInput_domain E fieldTail sameWidth fits odd problem
    points seed nontrivial input valid,
    firstCheckedSection_nextInput_seeded E fieldTail sameWidth fits odd problem
      points seed nontrivial input⟩

private theorem reusedCheckedSection_admits_reused
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    ∀ (Reference : Register) (input : OracleInput .empty _ Reference),
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).Admits input →
      (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed nontrivial
        addends).Admits
        ((reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
          nontrivial).nextInput input) := by
  intro Reference input admitted
  have valid : checkedSectionInputDomain E problem input.caller.localState := admitted.1
  exact ⟨reusedCheckedSection_nextInput_domain E fieldTail sameWidth fits odd problem
    points seed nontrivial input valid,
    reusedCheckedSection_nextInput_seeded E fieldTail sameWidth fits odd problem
      points seed nontrivial input⟩

/-- The first completed checked section admits the actual execution state to
the independently specified reused protocol, including the real reset seed. -/
theorem firstCheckedSection_entryCompatible
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.EntryCompatible
      (.cycle (checkedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends))
      (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends))
      (firstCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) :=
  entryCompatible_cycles _ _ _
    (firstCheckedSection_admits_reused E fieldTail sameWidth fits odd problem points
      seed nontrivial addends)

/-- A reused completed checked section admits its real successor to the same
independent reused protocol, for arbitrary finite repetition. -/
theorem reusedCheckedSection_entryCompatible
    (addends : (fun index => (points index).toGroupPoint) =
      ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth problem)
        problem.generator problem.target) :
    Circuit.EntryCompatible
      (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends))
      (.cycle (reusedCheckedSectionProblem E fieldTail sameWidth fits problem points seed
        nontrivial addends))
      (reusedCheckedSectionCode E fieldTail sameWidth fits odd problem points seed
        nontrivial) :=
  entryCompatible_cycles _ _ _
    (reusedCheckedSection_admits_reused E fieldTail sameWidth fits odd problem points
      seed nontrivial addends)

end

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured
