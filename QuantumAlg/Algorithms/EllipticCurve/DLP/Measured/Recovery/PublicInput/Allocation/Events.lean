/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Algorithms.EllipticCurve.DLP.Measured.Recovery.PublicInput.Allocation
import all QuantumAlg.Core.Execution.Preparation.Resources
import all QuantumAlg.Core.Execution.Measurement.Cells.Framing

/-!
# Every physical preparation in the actual public allocation

The five original prepareZero instructions contribute one preparation event
per physical qubit. Both complete retained-cell families contribute zero
native events. Every actual allocation Path is covered, with arbitrary
borrowed point inputs and no initial clean-state or support condition.

The allowance depends only on the declared field width.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
namespace Allocation.Events

noncomputable section

open QuantumAlg QuantumAlg.Execution QuantumAlg.MeasuredUncompute
open QuantumAlg.EllipticCurve QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass
open ScalarMultiplication.MeasuredPlacement MAU.Inversion.SharedEEA

private abbrev Model : ExecutionModel := .quantum AlgorithmGate.model .empty

/-- The original three indexed qubits, two coordinates, and arithmetic complement. -/
def bankWidth (width : Nat) : Nat := 3 * width + 4 * width.size + 14

/-- One actual zero-preparation event for a dimension-two physical system. -/
def preparation : ResourcePool Model :=
  ResourcePool.singleton (model := .quantum AlgorithmGate.model .empty) (.preparation (2 : ℕ+))

/-- Independent width-only allowance for the complete initial physical allocation. -/
def allocationBudget (width : Nat) : ResourcePool Model := bankWidth width • preparation

private lemma prepare_pool (ctx : RuntimeCtx .quantum) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ ctx.keys)
    (disjoint : List.Disjoint layout.identities ctx.physicalIdx)
    (qubits : ∀ wire, (layout.wire wire).dimension = 2)
    (path : (Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty) ctx key layout fresh disjoint).Path) :
    (Circuit.prepareZero (gates := AlgorithmGate.model) (oracles := .empty)
      (operations := .empty) (classicalOracles := .empty)
      ctx key layout fresh disjoint).resourcePool path = count • preparation := by
  change ZeroPreparation.eventCost AlgorithmGate.model .empty layout = _
  exact ZeroPreparation.zeroPreparation_uniform_cost AlgorithmGate.model .empty layout 2 qubits

private lemma append_pool {pre middle : RuntimeCtx .quantum}
    (first : Circuit Model pre middle) (key : StorageKey) {count : Nat}
    (layout : QuantumLayout count) (fresh : key ∉ middle.keys)
    (disjoint : List.Disjoint layout.identities middle.physicalIdx) (prefixCount : Nat)
    (qubits : ∀ wire, (layout.wire wire).dimension = 2)
    (prefixPool : ∀ path, first.resourcePool path = prefixCount • preparation)
    (path : (first.seq (.prepareZero middle key layout fresh disjoint)).Path) :
    (first.seq (.prepareZero middle key layout fresh disjoint)).resourcePool path =
      (prefixCount + count) • preparation := by
  change ResourcePool.ofList (first.eventTrace path.1 ++
    (Circuit.prepareZero middle key layout fresh disjoint).eventTrace path.2) = _
  rw [ResourcePool.ofList_append]
  change first.resourcePool path.1 +
    (Circuit.prepareZero middle key layout fresh disjoint).resourcePool path.2 = _
  rw [prefixPool, prepare_pool middle key layout fresh disjoint qubits]
  exact (add_nsmul preparation prefixCount count).symm

private lemma cast_pool {pre post pre' post' : RuntimeCtx .quantum}
    (input : pre = pre') (output : post = post') (code : Circuit Model pre post)
    (pool : ResourcePool Model) (same : ∀ path, code.resourcePool path = pool)
    (path : (castCircuit input output code).Path) :
    (castCircuit input output code).resourcePool path = pool := by
  cases input
  cases output
  exact same path

private lemma retained_pool (ctx frame : RuntimeCtx .quantum) (dimension : ℕ+) (count : Nat)
    (separate : RuntimeCtx.StorageDisjoint (MeasurementCells.context ctx dimension count) frame)
    (path : (MeasurementCells.allocateFramed (model := Model)
      ctx frame dimension count separate).Path) :
    (MeasurementCells.allocateFramed (model := Model)
      ctx frame dimension count separate).resourcePool path = 0 := by
  rw [Circuit.resourcePool, MeasurementCells.allocateFramed_eventTrace, ResourcePool.ofList_nil]

variable {p : Nat} (E : PrimeFieldShortWeierstrass p) (m : Nat)

private lemma zeroBankRaw_pool (path : (zeroBankRaw E m).Path) :
    (zeroBankRaw E m).resourcePool path = allocationBudget p.size := by
  have raw : ∀ rawPath : (zeroBankRaw E m).Path,
      (zeroBankRaw E m).resourcePool rawPath =
        (1 + 1 + 1 + (p.size + p.size) + InputPreparation.auxiliaryWidth p.size) •
          preparation := by
    intro rawPath
    unfold zeroBankRaw
    apply append_pool
    · intro wire
      rfl
    · intro prefixPath
      apply append_pool
      · intro wire
        rfl
      · intro prefixPath
        apply append_pool
        · intro wire
          rfl
        · intro prefixPath
          apply append_pool
          · intro wire
            rfl
          · intro preparePath
            exact prepare_pool _ _ _ _ _ (fun _ => rfl) preparePath
  have width : 1 + 1 + 1 + (p.size + p.size) + InputPreparation.auxiliaryWidth p.size =
      bankWidth p.size := by
    unfold InputPreparation.auxiliaryWidth InputPreparation.prefixWidth
      InputPreparation.suffixWidth bankWidth
    omega
  exact (raw path).trans (congrArg (fun count => count • preparation) width)

private lemma zeroBank_pool (path : (zeroBank E m).Path) :
    (zeroBank E m).resourcePool path = allocationBudget p.size :=
  cast_pool rfl (withAuxiliary_eq E m) (zeroBankRaw E m) (allocationBudget p.size)
    (zeroBankRaw_pool E m) path

private lemma numeratorCells_pool (path : (numeratorCells E m).Path) :
    (numeratorCells E m).resourcePool path = 0 := by
  apply cast_pool (numeratorCells_input E m) (numeratorCells_output E m)
    (numeratorCellsRaw E m) 0
  intro rawPath
  exact retained_pool (InversePreparation.after p.size)
    ((indexed (p := p)).disjointUnion (Recovery.PublicInput.frame E m) (indexed_disjoint E m))
    2 p.size (numerator_rest_disjoint E m) rawPath

private lemma terminalCells_pool (path : (terminalCells E m).Path) :
    (terminalCells E m).resourcePool path = 0 :=
  retained_pool (Recovery.Layout.bank p.size) (Recovery.PublicInput.frame E m) 2 (2 * m)
    (Recovery.PublicInput.terminal_disjoint E m) path

/-- All five preparations are charged exactly, followed by both zero-event retain families. -/
lemma circuit_pool (path : (circuit E m).Path) :
    (circuit E m).resourcePool path = allocationBudget p.size := by
  rcases path with ⟨⟨bankPath, numeratorPath⟩, terminalPath⟩
  change ResourcePool.ofList
    (((zeroBank E m).eventTrace bankPath ++ (numeratorCells E m).eventTrace numeratorPath) ++
      (terminalCells E m).eventTrace terminalPath) = _
  simp only [ResourcePool.ofList_append]
  change (zeroBank E m).resourcePool bankPath + (numeratorCells E m).resourcePool numeratorPath +
    (terminalCells E m).resourcePool terminalPath = _
  rw [zeroBank_pool, numeratorCells_pool, terminalCells_pool, add_zero, add_zero]

end

end Allocation.Events
end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.ECDLP.Measured.Recovery.PublicInput
