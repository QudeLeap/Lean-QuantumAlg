/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Core.Base.Accounting.ResourcePool
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.ControlPushdown

/-!
# Exact coordinates of the actual complete controlled product

All sums follow the two actual finite bit scans. The comparison starts with
the previous outer control of the already optimized one-control accumulator.
No quantum/classical exchange rate or earlier fully controlled baseline is used.
-/

namespace QuantumAlg.MAU.Multiplication.VariableGidney.PushdownComparison

noncomputable section

open Nat.FixedWidth EncodedBit GateSpec
open Accumulate.Gidney.ControlPushdown

private lemma controlled_append (outerWidth width : Nat) (address : Fin outerWidth)
    (first second : List (GateSpec (Accumulate.Gidney.encoding width))) :
    let controlled := originalControlled outerWidth width address
    xCount (controlled (first ++ second)) = xCount (controlled first) +
        xCount (controlled second) ∧
      cCount (controlled (first ++ second)) = cCount (controlled first) +
        cCount (controlled second) ∧
      tCount (controlled (first ++ second)) = tCount (controlled first) +
        tCount (controlled second) ∧
      (controlled (first ++ second)).length = (controlled first).length +
        (controlled second).length := by
  dsimp only
  by_cases small : width ≤ 1
  · simp only [originalControlled, dif_pos small, List.map_append, xCount_append,
      cCount_append, tCount_append, List.length_append, and_self]
  · simp only [originalControlled, dif_neg small]
    have joined := outerControl_counts outerWidth width (by omega) address (first ++ second)
    have one := outerControl_counts outerWidth width (by omega) address first
    have two := outerControl_counts outerWidth width (by omega) address second
    refine ⟨by omega, ?_, ?_, ?_⟩
    · rw [joined.2.1, one.2.1, two.2.1, xCount_append]
    · rw [joined.2.2, one.2.2, two.2.2, cCount_append, tCount_append]
      ring
    · simp only [length_eq_multiplicity_sums]
      change xCount _ + cCount _ + tCount _ =
        (xCount _ + cCount _ + tCount _) + (xCount _ + cCount _ + tCount _)
      rw [joined.1, joined.2.1, joined.2.2, one.1, one.2.1, one.2.2,
        two.1, two.2.1, two.2.2, xCount_append, cCount_append, tCount_append]
      ring

/-- Sum a real source-stage coordinate over its increasing-bit execution prefix. -/
def sourcePrefixTotal (coordinate : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat) (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : Nat → Nat
  | 0 => 0
  | count + 1 => sourcePrefixTotal coordinate width modulus coefficient count +
      coordinate width modulus (accumulateConstant modulus coefficient count)

private lemma sourcePrefix_coordinates (outerWidth width : Nat) (address : Fin outerWidth)
    (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat) (within : count ≤ width) :
    let previous := originalControlled outerWidth width address
      (Accumulate.Gidney.prefixGates width modulus coefficient count within)
    let actual := twoPrefix outerWidth width address modulus coefficient count within
    xCount previous = 0 ∧ cCount previous = 0 ∧
      cCount actual = sourcePrefixTotal sourceCnotIncrease width modulus coefficient count ∧
      tCount previous = tCount actual +
        sourcePrefixTotal sourceToffoliSaving width modulus coefficient count ∧
      previous.length = actual.length +
        sourcePrefixTotal sourceTimeSaving width modulus coefficient count := by
  induction count with
  | zero =>
      dsimp only [Accumulate.Gidney.prefixGates, twoPrefix, sourcePrefixTotal]
      by_cases small : width ≤ 1
      · simp only [originalControlled, dif_pos small, List.map_nil, xCount, cCount, tCount,
          List.sum_nil, List.length_nil, Nat.zero_add, and_self]
      · simp only [originalControlled, dif_neg small]
        have empty := outerControl_counts outerWidth width (by omega) address []
        have length : (outerControl outerWidth width (by omega) address []).length = 0 := by
          rw [length_eq_multiplicity_sums]
          change xCount _ + cCount _ + tCount _ = 0
          rw [empty.1, empty.2.1, empty.2.2]
          rfl
        exact ⟨empty.1, by simpa only [xCount, List.map_nil, List.sum_nil] using empty.2.1,
          rfl, by simpa only [cCount, tCount, List.map_nil, List.sum_nil,
            Nat.mul_zero, Nat.zero_add] using empty.2.2,
          length⟩
  | succ index ih =>
      dsimp only
      have previous := ih (by omega)
      have current := source_coordinates outerWidth width address ⟨index, by omega⟩ modulus
        (accumulateConstant modulus coefficient index)
      have joined := controlled_append outerWidth width address
        (Accumulate.Gidney.prefixGates width modulus coefficient index (by omega))
        (Accumulate.Gidney.stageGates width ⟨index, by omega⟩ modulus
          (accumulateConstant modulus coefficient index))
      dsimp only at previous current joined
      simp only [Accumulate.Gidney.prefixGates, twoPrefix, sourcePrefixTotal,
        cCount_append, tCount_append]
      exact ⟨by rw [joined.1, previous.1, current.1],
        by rw [joined.2.1, previous.2.1, current.2.1],
        by rw [previous.2.2.1, current.2.2.1],
        by rw [joined.2.2.1, previous.2.2.2.1, current.2.2.2.1]; omega,
        by rw [joined.2.2.2, previous.2.2.2.2, current.2.2.2.2,
          List.length_append]; omega⟩

/-- Small-width paths have no change; larger widths sum the actual source stages. -/
def accumulateTotal (coordinate : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat) (width : Nat) (modulus : Fin (2 ^ width + 1))
    (coefficient : Nat) : Nat :=
  if width ≤ 2 then 0 else sourcePrefixTotal coordinate width modulus coefficient width

private lemma accumulate_coordinates (outerWidth : Nat) : (width : Nat) →
    (address : Fin outerWidth) → (modulus : Fin (2 ^ width + 1)) → (coefficient : Nat) →
    let previous := originalControlled outerWidth width address
      (Accumulate.Gidney.gates width modulus coefficient)
    let actual := twoGates outerWidth width address modulus coefficient
    xCount previous = 0 ∧ cCount previous = 0 ∧
      cCount actual = accumulateTotal sourceCnotIncrease width modulus coefficient ∧
      tCount previous = tCount actual +
        accumulateTotal sourceToffoliSaving width modulus coefficient ∧
      previous.length = actual.length +
        accumulateTotal sourceTimeSaving width modulus coefficient
  | 0, address, modulus, coefficient
  | 1, address, modulus, coefficient
  | 2, address, modulus, coefficient => by
      have counts := originalControlled_native_counts outerWidth _ address
        (Accumulate.Gidney.gates _ modulus coefficient)
      have zero := Accumulate.Gidney.gidneyAccumulateGates_xMultiplicity_sum
        _ modulus coefficient
      change xCount _ = 0 at zero
      simp only [twoGates, accumulateTotal, Nat.reduceLeDiff, if_true]
      exact ⟨counts.1, counts.2.trans zero, counts.2.trans zero, by omega, by omega⟩
  | extra + 3, address, modulus, coefficient => by
      simpa only [Accumulate.Gidney.gates, twoGates, accumulateTotal,
        if_neg (show ¬extra + 3 ≤ 2 by omega)] using
        sourcePrefix_coordinates outerWidth (extra + 3) address modulus coefficient
          (extra + 3) (Nat.le_refl _)

/-- Sum a MAC coordinate over the actual increasing first-input-bit prefix. -/
def productPrefixTotal (coordinate : (width : Nat) → (modulus : Fin (2 ^ width + 1)) →
    Fin (modulus.val + 1) → Nat) (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat → Nat
  | 0 => 0
  | count + 1 => productPrefixTotal coordinate width modulus count +
      accumulateTotal coordinate width modulus (2 ^ count)

private lemma productPrefix_coordinates (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    let previous := previousPrefixGates width modulus count within
    let actual := prefixGates width modulus count within
    xCount previous = 0 ∧ cCount previous = 0 ∧ xCount actual = 0 ∧
      cCount actual = productPrefixTotal sourceCnotIncrease width modulus count ∧
      tCount previous = tCount actual +
        productPrefixTotal sourceToffoliSaving width modulus count ∧
      previous.length = actual.length +
        productPrefixTotal sourceTimeSaving width modulus count := by
  induction count with
  | zero => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
  | succ index ih =>
      have previous := ih (by omega)
      have current := accumulate_coordinates width width ⟨index, by omega⟩ modulus (2 ^ index)
      have zero := twoGates_xCount width width ⟨index, by omega⟩ modulus (2 ^ index)
      dsimp only at previous current
      change xCount (previousStageGates width modulus ⟨index, by omega⟩) = 0 ∧
        cCount (previousStageGates width modulus ⟨index, by omega⟩) = 0 ∧
        cCount (stageGates width modulus ⟨index, by omega⟩) =
          accumulateTotal sourceCnotIncrease width modulus (2 ^ index) ∧
        tCount (previousStageGates width modulus ⟨index, by omega⟩) =
          tCount (stageGates width modulus ⟨index, by omega⟩) +
            accumulateTotal sourceToffoliSaving width modulus (2 ^ index) ∧
        (previousStageGates width modulus ⟨index, by omega⟩).length =
          (stageGates width modulus ⟨index, by omega⟩).length +
            accumulateTotal sourceTimeSaving width modulus (2 ^ index) at current
      change xCount (stageGates width modulus ⟨index, by omega⟩) = 0 at zero
      dsimp only [previousPrefixGates, prefixGates, productPrefixTotal]
      simp only [xCount_append, cCount_append, tCount_append, List.length_append]
      exact ⟨by rw [previous.1, current.1],
        by rw [previous.2.1, current.2.1],
        by rw [previous.2.2.1, zero],
        by rw [previous.2.2.2.1, current.2.2.1],
        by rw [previous.2.2.2.2.1, current.2.2.2.1]; omega,
        by rw [previous.2.2.2.2.2, current.2.2.2.2]; omega⟩

/-- Toffolis in the actual complete replacement, from its literal native instructions. -/
public def actualToffoliCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  tCount (gates width modulus)

/-- Toffolis in the previous outer expansion of the current one-control accumulator. -/
public def previousToffoliCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  tCount (previousGates width modulus)

/-- CNOTs in the actual complete replacement, independent of the Toffoli coordinate. -/
public def actualCnotCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  cCount (gates width modulus)

/-- CNOTs in the previous current-baseline program. -/
public def previousCnotCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  cCount (previousGates width modulus)

/-- Single-qubit instructions of the actual complete replacement. -/
public def actualSingleQubitCount (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  xCount (gates width modulus)

/-- The actual serial critical path under the existing native quantum-duration metric. -/
public def actualQuantumTime (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  (program width modulus).evaluatedEventDepth Resource.Event.quantumDuration

/-- The previous real serial word under that same native duration metric. -/
public def previousQuantumTime (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  (programList (QubitLayout.canonical _) .empty
    (previousGates width modulus)).evaluatedEventDepth Resource.Event.quantumDuration

/-- The exact Toffoli reduction is a symbolic sum over the two actual finite scans. -/
public def toffoliSaving (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  productPrefixTotal sourceToffoliSaving width modulus width

/-- The exact time reduction uses the same two scans and retains all CNOT durations. -/
public def quantumTimeSaving (width : Nat) (modulus : Fin (2 ^ width + 1)) : Nat :=
  productPrefixTotal sourceTimeSaving width modulus width

private lemma prefix_quantumTime (width : Nat) (modulus : Fin (2 ^ width + 1))
    (count : Nat) (within : count ≤ width) :
    (prefixProgram width modulus count within).evaluatedEventDepth
      Resource.Event.quantumDuration = (prefixGates width modulus count within).length := by
  induction count with
  | zero => rfl
  | succ index ih =>
      change ((prefixProgram width modulus index (by omega)).seq
        (stageProgram width modulus ⟨index, by omega⟩)).evaluatedEventDepth _ = _
      rw [UnitaryCircuit.evaluatedEventDepth_seq, ih (by omega)]
      change _ + (programList (QubitLayout.canonical _) .empty
        (stageGates width modulus ⟨index, by omega⟩)).evaluatedEventDepth _ = _
      rw [native_time, prefixGates, List.length_append]

/-- Actual native instructions give separate exact coordinate and time comparisons. -/
public lemma exact_comparison (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    previousToffoliCount width modulus = actualToffoliCount width modulus +
        toffoliSaving width modulus ∧
      previousCnotCount width modulus = 0 ∧ actualSingleQubitCount width modulus = 0 ∧
      previousQuantumTime width modulus = actualQuantumTime width modulus +
        quantumTimeSaving width modulus := by
  have result := productPrefix_coordinates width modulus width (Nat.le_refl width)
  refine ⟨result.2.2.2.2.1, result.2.1, result.2.2.1, ?_⟩
  change (programList (QubitLayout.canonical _) .empty
    (previousGates width modulus)).evaluatedEventDepth _ = _
  rw [native_time]
  change (previousGates width modulus).length =
    (program width modulus).evaluatedEventDepth _ + quantumTimeSaving width modulus
  rw [program, prefix_quantumTime]
  exact result.2.2.2.2.2

/-- Toffoli and time reductions retain the additional CNOT coordinate separately. -/
public lemma saving_decomposition (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    toffoliSaving width modulus = actualCnotCount width modulus +
      quantumTimeSaving width modulus := by
  have result := productPrefix_coordinates width modulus width (Nat.le_refl width)
  rcases result with ⟨oldX, oldC, newX, _newC, toffoli, time⟩
  have before := length_eq_multiplicity_sums
    (previousPrefixGates width modulus width (Nat.le_refl width))
  have after := length_eq_multiplicity_sums
    (prefixGates width modulus width (Nat.le_refl width))
  change (previousPrefixGates width modulus width _).length =
    xCount _ + cCount _ + tCount _ at before
  change (prefixGates width modulus width _).length =
    xCount _ + cCount _ + tCount _ at after
  rw [oldX, oldC] at before
  rw [newX] at after
  change productPrefixTotal sourceToffoliSaving width modulus width =
    cCount (prefixGates width modulus width _) +
      productPrefixTotal sourceTimeSaving width modulus width
  omega

/-- The unchanged independent per-coordinate allowance of the public product endpoint. -/
public def nativeCoordinateCap (width : Nat) : Nat := eventBound width

/-- The independent original public per-coordinate envelope still bounds the actual CNOTs. -/
public lemma actual_cnot_bound (width : Nat) (modulus : Fin (2 ^ width + 1)) :
    actualCnotCount width modulus ≤ nativeCoordinateCap width := by
  have length := variableGidney_gates_length_bound width modulus
  have coordinates := length_eq_multiplicity_sums (gates width modulus)
  change (gates width modulus).length = xCount _ + cCount _ + tCount _ at coordinates
  change cCount (gates width modulus) ≤ eventBound width
  omega

end

end QuantumAlg.MAU.Multiplication.VariableGidney.PushdownComparison
