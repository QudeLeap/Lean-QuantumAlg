/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
public import QuantumAlg.Algorithms.FiniteCyclicDLP.Preparation
public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Components.GateModel.Algorithm
public import QuantumAlg.Components.Classical.Model.BitWord
public import Mathlib.Data.Nat.Bits
public import Mathlib.Data.Real.Basic
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Problem
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.PublicInput.Domain
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.Repeated.Resources
import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Support
import all QuantumAlg.Core.Algorithm.Problem

/-!
# Independent resources for original measured elliptic-curve discrete logarithms

The problem prescribes the original public points and mathematical scalar
relation. Its event and space allowances are parameter formulas, independent
of the candidate algorithm. The original exceptional-error term remains in
the finite repetition condition. Borrowed restoration is a separate mandatory
obligation; an empty list of final-state promises does not assert cleanup.
-/

namespace QuantumAlg.EllipticCurve.LogicalResources

noncomputable section

open Execution PrimeFieldShortWeierstrass FiniteCyclicDLP
open PrimeFieldShortWeierstrass.ECDLP.Measured
open ClassicalRoutines.EllipticCurve.CandidateCheck.Native

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) [Fact p.Prime]

/-- The exact original input context, exposed at the complete problem boundary. -/
public def inputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  PublicInput.before E (orderWidth (ECDLP.Canonical.problem I))

/-- The exact original final context includes all live wires and the retained optional result. -/
public def outputContext (I : ECDLPInstance E) : RuntimeCtx .quantum :=
  checkedContext E (ECDLP.Canonical.problem I)

/-- Every physical affine addend represents its original big-endian public group power. -/
public def AddendEncoding (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E) : Prop :=
  (fun index => (points index).toGroupPoint) =
    ExceptionalOffsetAveraging.pairedBigEndianAddend (orderWidth (ECDLP.Canonical.problem I))
      (ECDLP.Canonical.problem I).generator (ECDLP.Canonical.problem I).target

/-- The complete original exceptional error must fit the explicitly chosen finite retry budget. -/
public def RepetitionCondition (I : ECDLPInstance E)
    (points : Fin (2 * orderWidth (ECDLP.Canonical.problem I)) → AffinePoint E)
    (seed : AffinePoint E) (count : Nat) (failure : ℝ) : Prop :=
  (1 - (((I.subgroupOrder : ℝ) * Nat.totient I.subgroupOrder /
    (4 * (fourierModulus (ECDLP.Canonical.problem I) : ℝ) ^ 2)) -
      4 * Real.sqrt (preparedExceptionalMass (ECDLP.Canonical.problem I) points seed))) ^
        count ≤ failure

/-- Only a bounded scalar satisfying the original public group equation is accepted. -/
def AcceptedOutput (I : ECDLPInstance E)
    (output : CShape.Value (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I))))) :
    Prop :=
  ∃ scalar : ZMod I.subgroupOrder, I.CandidateScalar scalar ∧
    output = .optionSome (CShape.wordOfNat (orderWidth (ECDLP.Canonical.problem I)) scalar.val)

/-- The independent success requirement uses the explicitly allowed failure probability. -/
def successLowerBound (failure : ℝ) : ProbabilityLowerBound where
  value := 1 - ENNReal.ofReal failure
  le_one := tsub_le_self

/-- All preparations, real resets, samples, classical checks and final packing are charged. -/
def resourceBudget (I : ECDLPInstance E) (count : Nat) :
    ResourceBudget (.quantum AlgorithmGate.model .empty BitWord.model) where
  events := repeatedRunBudget E (ECDLP.Canonical.problem I)
    I.subgroupOrder_prime.two_le count
  resident :=
    recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) +
      persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) +
      (PublicInput.terminal E (orderWidth (ECDLP.Canonical.problem I))).residentSpace
  auxiliary :=
    recoveryTailScratchSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) +
      persistentCellSpace .quantum (ECDLP.Canonical.Layout.fieldWidth E)
        (orderWidth (ECDLP.Canonical.problem I)) +
      (PublicInput.terminal E (orderWidth (ECDLP.Canonical.problem I))).auxiliarySpace

/-- The unit-duration allowance counts the complete original native event envelope. -/
def depthLimit (I : ECDLPInstance E) (count : Nat) : Nat :=
  ResourcePool.weightedCount (fun _ => 1)
    (repeatedRunBudget E (ECDLP.Canonical.problem I) I.subgroupOrder_prime.two_le count)

/-- Original measured ECDLP with explicit finite repetition and independent native budgets.

**Input.**
- A prime-field curve, an affine generator of known prime subgroup order and
  an affine public target in that subgroup. The local input fixes those two
  borrowed classical values and admits every normalized quantum state and
  every external reference extension.
**Output.**
- An optional bounded scalar satisfying the original public group equation.
**Resource budget.**
- Native events: all original zero preparations and fixed-bit loads, followed by
  `count` times the complete sampling/reset and checked-recovery allowances,
  then one actual option pack.
- Resident and auxiliary space: the complete original terminal context plus
  seven persistent cells and the maximum successive recovery scratch scope.
  Repetition reuses this space; it does not multiply live storage by `count`.
- Depth: the unit-weighted count of the independent complete native-event
  envelope. This is a serial bound on the actual dependency path.
**Success.**
- At least `1 - failure`; the implementation theorem retains the original
  affine-addend and exceptional-error finite-repetition conditions.
- No final purity or zero-state promise is imposed. All borrowed classical
  and reference correlations must nevertheless be restored.
**Source.**
- [PZ03, ecc.tex:448-556].
- The finite Fourier sampling and classical recovery use the original
  registered finite-cyclic DLP analysis.
-/
public def problem (I : ECDLPInstance E) (count : Nat) (failure : ℝ) :
    Problem (.quantum AlgorithmGate.model .empty BitWord.model)
      (inputContext E I) (outputContext E I)
      (.option (.unsignedWord (orderWidth (ECDLP.Canonical.problem I)))) where
  valid := PublicInput.inputDomain E (orderWidth (ECDLP.Canonical.problem I))
    (ECDLP.Canonical.problem I)
  initialization := fun _ => True
  accepts := fun _store output => AcceptedOutput E I output
  successLB := successLowerBound failure
  states := []
  resources := resourceBudget E I count
  depth :=
    { duration := fun _ => 1
      limit := depthLimit E I count
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.EllipticCurve.LogicalResources
