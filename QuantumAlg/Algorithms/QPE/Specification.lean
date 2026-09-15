/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Algorithm.Problem
public import QuantumAlg.Algorithms.QPE.Basic
public import QuantumAlg.Algorithms.QPE.Context
public import QuantumAlg.Algorithms.QPE.Storage
import all QuantumAlg.Algorithms.QPE.Construction
import all QuantumAlg.Algorithms.QPE.WindowProbability
import all QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Core.Base.Accounting.Space
import all QuantumAlg.Primitives.QFT.Construction
import Mathlib.Analysis.Real.Pi.Bounds

/-!
# Independent native borrowed-eigenstate QPE specification

The original positive-width domain and source eigenstate are unchanged.
Validity constrains the actual local density matrix, so every allowed
extension by an external reference remains in scope. Complete-output storage
and all event budgets below are explicit formulas independent of the run.
-/

namespace QuantumAlg.QuantumPhaseEstimation

noncomputable section

/-- The original pure eigenstate in the supplied physical source coordinates. -/
def inputPromise {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (state : DensityOperator (pre t n).register) : Prop :=
  ∀ row column, state.matrix row column =
    P.eigenstate (inputBasisEquiv t n row) * star (P.eigenstate (inputBasisEquiv t n column))

def successLB : ProbabilityLowerBound where
  value := ENNReal.ofReal (4 / Real.pi ^ 2)
  le_one := by
    apply ENNReal.ofReal_le_one.mpr
    apply (div_le_one (sq_pos_of_pos Real.pi_pos)).mpr
    nlinarith [Real.pi_gt_three]

/-- One actual zero preparation of exactly the owned phase prefix. -/
def basisPreparationEvent (t : Nat) : Resource.Event .quantum :=
  .preparation
    { family := "builtin", name := "computational-basis"
      parameters := t :: (List.replicate t 2 ++ List.replicate t 0) }

/-- Independent controlled-query, inverse-Fourier, preparation, measurement and packing ledger. -/
def eventBudget (t n : Nat) : ResourcePool .quantum :=
  ResourcePool.singleton (basisPreparationEvent t) +
    (ResourcePool.singleton (.gate (.builtin "hadamard")) t +
      (2 ^ t - 1) • ResourcePool.singleton (qpeControlledSourceUnitaryEvent n) +
      (t • ResourcePool.singleton (.gate (.builtin "hadamard")) +
        t.choose 2 • ResourcePool.singleton (.gate qftControlledPhaseLabel) +
        (t / 2) • ResourcePool.singleton (.gate (.builtin "swap")))) +
    (t • ResourcePool.singleton
      (.measurement { family := "builtin", name := "z", parameters := [2] }) +
      ResourcePool.singleton (.classicalOperation (.nominalEncoding (.packFiniteBits t))))

/-- Every source and phase system remains resident, along with both classical representations. -/
def residentBudget (t n : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t + n else 0

/-- The supplied borrowed source is excluded from owned auxiliary storage. -/
def auxiliaryBudget (t : Nat) : SpacePool .quantum
  | .classicalBits => 2 * t
  | .quantumSystems dimension => if (2 : ℕ+) = dimension then t else 0

/-- The explicit total event count bounds the actual critical path at unit event duration. -/
def depthBudget (t : Nat) : Nat :=
  1 + (t + (2 ^ t - 1) + (t + t.choose 2 + t / 2)) + t + 1

def accepts {n : Nat} (P : QPEEigenstateInput n) (t : Nat)
    (_initial : Execution.Store (pre t n)) (result : CShape.Value (.bits t)) : Prop :=
  match result with
  | .bits outcome => SuccessfulOutcome P t outcome

/-- Quantum phase estimation on the supplied borrowed eigenstate.

**Input.**
- An $n$-qubit unitary $U$, its borrowed normalized eigenstate $\ket{\psi}$
  satisfying $U\ket{\psi}=e^{2\pi i\theta}\ket{\psi}$, and controlled-$U$ access.
- A positive precision width $t$ and every normalized extension of the
  promised local pure input by an external reference.
- The phase prefix is prepared internally in $\ket{0^t}$.
**Output.**
- Actual stored $t$-bit phase data with circular precision $2^{-t}$.
- Complete Output retaining the $n$ borrowed source systems, $t$ owned phase
  systems, $t$ binary measurement cells, and the packed $t$-bit result.
**Resource budget.**
- Exactly $2^t-1$ controlled-$U$ calls and $t$ preparation Hadamards.
- The inverse Fourier readout uses $t$ Hadamards, $t(t-1)/2$ controlled
  phases, and $\lfloor t/2\rfloor$ SWAPs.
- One phase-prefix basis preparation, $t$ individual Z measurements, and
  one actual finite-bit packing operation.
- Resident capacity is $t+n$ dimension-two systems and $2t$ classical bits;
  auxiliary capacity is $t$ dimension-two systems and $2t$ classical bits.
- Unit-event depth is at most the sum of these explicit event multiplicities.
**Success.**
- The original circular phase-window event has probability at least $4/\pi^2$.
- The complete borrowed eigenstate and external reference are restored jointly,
  independently of the success event; the owned phase systems remain live.
**Source.**
- QPE, the controlled-power ladder, and its success analysis in
  [Lin22, phaseestimation.tex:510-521,647-715].
- Exact preparation and inverse-QFT native gate counts come from the same
  structural source circuit; execution records its actual Z writes and packing.
-/
public def problem {n : Nat} (P : QPEEigenstateInput n) (t : Nat) :
    Problem .quantum (pre t n) (post t n) (.bits t) where
  valid := fun state => 0 < t ∧ inputPromise P t state.quantumMarginal
  accepts := accepts P t
  successLB := successLB
  states := []
  resources :=
    { events := eventBudget t n
      resident := residentBudget t n
      auxiliary := auxiliaryBudget t }
  depth := .quantum (fun _ => 1) (depthBudget t)

end

end QuantumAlg.QuantumPhaseEstimation
