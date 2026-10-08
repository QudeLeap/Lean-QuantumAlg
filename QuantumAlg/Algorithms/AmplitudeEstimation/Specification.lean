/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.AmplitudeEstimation.Basic
public import QuantumAlg.Algorithms.AmplitudeEstimation.Context
public import QuantumAlg.Algorithms.AmplitudeEstimation.Storage
public import QuantumAlg.Core.Measure.Distribution
import all QuantumAlg.Algorithms.AmplitudeEstimation.Construction
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Components.Oracle.AmplitudeAmplification
import all QuantumAlg.Algorithms.AmplitudeEstimation.Elementary.Resources
import all QuantumAlg.Components.Oracle.ZeroReflection.Phase.Resources

/-!
# Independent native amplitude-estimation specification

The source model, interior-probability promise, selected width, and additive
error event retain the original source domain. Budgets below are explicit
parameter formulas, independent of the circuit and all its projections.
-/

namespace QuantumAlg.AmplitudeEstimation

noncomputable section

/-- The original legal confidence lower bound. -/
def successLB (η : Real) (nonnegative : 0 ≤ η) : ProbabilityLowerBound where
  value := ENNReal.ofReal (1 - η)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    linarith

/-- Independent query and elementary-reflection multiplicities for one actual source step. -/
def stepBudget {n : Nat} (E : GeneralAmplitudeEstimationInput n) : ResourcePool (model E) :=
  ResourcePool.singleton (model := model E) (.oracle .controlledGoodReflection) +
    ResourcePool.singleton (model := model E) (.oracle .inversePreparation) +
    ZeroReflection.controlledElementaryEventPool
      (Elementary.oracles E.source.preparation E.source.good) n BitWord.model .empty +
    ResourcePool.singleton (model := model E) (.oracle .preparation)

/-- Expanded inverse-Fourier multiplicities preserve the literal selected native coordinates. -/
def readoutBudget {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    ResourcePool (model E) :=
  (t + 3 * t.choose 2) • ResourcePool.singleton (model := model E) (.gate .singleQubit) +
    (2 * t.choose 2 + 3 * (t / 2)) •
      ResourcePool.singleton (model := model E) (.gate .cnot)

/-- Independent native unitary budget in the caller's classical execution context. -/
def unitaryBudget {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    ResourcePool (model E) :=
  ResourcePool.singleton (model := model E) (.oracle .preparation) +
    (t • ResourcePool.singleton (model := model E) (.gate .singleQubit) +
      ((2 ^ t - 1) • stepBudget E + readoutBudget E t))

/-- Independent native unitary, per-system preparation, actual Z writes and bit packing. -/
def eventBudget {n : Nat} (E : GeneralAmplitudeEstimationInput n) (t : Nat) :
    ResourcePool (model E) :=
  (t + (Elementary.helperWidth t n + n)) •
      ResourcePool.singleton (model := model E) (.preparation (2 : ℕ+)) +
    unitaryBudget E t +
    (t • ResourcePool.singleton (model := model E) (.measurement (2 : ℕ+)) +
      ResourcePool.singleton (model := model E)
        (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

/-- All phase and source systems survive, together with both t-bit classical representations. -/
def spaceBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension =>
      if (2 : ℕ+) = dimension then t + (Elementary.helperWidth t n + n) else 0

/-- The explicit structural unit-event depth includes preparation and every sequential Z write. -/
def depthBudget (t n : Nat) : Nat := 1 + Elementary.unitaryDepth t n + t + 1

/-- The actual packed phase bits are accepted by the original additive-error predicate. -/
def accepts {n : Nat} (E : GeneralAmplitudeEstimationInput n) (eps : Real) {t : Nat}
    (_initial : Execution.Store pre) (result : CShape.Value (.bits t)) : Prop :=
  match result with
  | .bits outcome => SuccessfulOutcome E eps outcome

/-- General prepared-state amplitude estimation with complete native storage.

**Input.**
- The original intrinsic source preparation $U$, orthogonal good and bad
  states, first-quadrant angle, exact prepared-state decomposition, and
  positive interior-probability lower bound.
- Classical parameters $0<\epsilon\le1$ and $0<\eta\le1$, selecting
  $t=\lceil\log_2(\eta^{-1}/(\epsilon/\pi))\rceil$ phase wires internally.
- Empty runtime storage and any normalized external reference.
**Output.**
- Actual $t$-bit phase data whose sine-squared decoding estimates the source
  good probability.
- Complete Output retaining all $t+n$ prepared systems, $t$ finite binary
  measurement cells, and the packed $t$-bit result.
**Resource budget.**
- Writing $L=2^t-1$, there are $L+1$ ordinary $U$ queries, $L$ ordinary
  $U^\dagger$ queries, and $L$ controlled good-reflection queries.
- Each controlled all-zero reflection is an actual elementary circuit with
  $C(n)$ gates: $C(0)=0$, $C(1)=3$, $C(2)=8$, $C(3)=13$, $C(4)=21$, and
  $C(n)=10n-21$ for $n\ge5$. The complete unitary uses
  $2t+LC(n)+5\binom{t}{2}+3\lfloor t/2\rfloor$ elementary gates.
- The original valid domain implies $t\ge2$. Large reflections borrow a
  different existing phase wire and restore its arbitrary value exactly,
  including the controlled global phase. Thus no extra qubit is allocated
  on the admitted domain. The total definition at $t=1,n\ge3$ honestly
  prepares and retains one extra work system.
- One zero preparation per actual qubit, $t$ binary Z measurements, and one packing
  operation are charged. Resident and auxiliary capacities are $t+n$
  dimension-two systems and $2t$ classical bits.
- Unit-event depth is
  $1+(1+([t>0]+(L(3+C(n))+t+5\binom{t}{2}+3\lfloor t/2\rfloor)))+t+1$.
**Success.**
- The actual additive-error event has probability at least $1-\eta$.
- The complete external reference is restored independently of this event.
**Source.**
- Preparation, signed eigenphases, selected precision, and the additive-error
  guarantee in [Lin22, appqpe.tex:187-254].
- Native execution additionally records its actual preparation, measurements,
  retained cells, and packing.
-/
public def problem {n : Nat} (E : GeneralAmplitudeEstimationInput n)
    (eps η : Real) (nonnegative : 0 ≤ η) :
    Problem (model E) pre (post (selectedPhaseQubits eps η) n)
      (.bits (selectedPhaseQubits eps η)) where
  valid := fun _ => 0 < eps ∧ eps ≤ 1 ∧ 0 < η ∧ η ≤ 1
  initialization := fun _ => True
  accepts := accepts E eps
  successLB := successLB η nonnegative
  states := []
  resources :=
    { events := eventBudget E (selectedPhaseQubits eps η)
      resident := spaceBudget (selectedPhaseQubits eps η) n
      auxiliary := spaceBudget (selectedPhaseQubits eps η) n }
  depth :=
    { duration := fun _ => 1
      limit := depthBudget (selectedPhaseQubits eps η) n
      classicalQuery_unit := fun _ => rfl
      quantumQuery_unit := fun _ => rfl }

end

end QuantumAlg.AmplitudeEstimation
