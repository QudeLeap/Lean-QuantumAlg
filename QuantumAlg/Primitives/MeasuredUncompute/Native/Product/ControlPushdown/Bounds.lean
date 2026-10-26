/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import QuantumAlg.Primitives.MeasuredUncompute.Native.Product.ControlPushdown.Controlled
import all QuantumAlg.Primitives.MeasuredUncompute.Native.Product.ControlPushdown.Controlled
import all QuantumAlg.Primitives.MAU.Multiplication.VariableGidney.ControlPushdown.Resources

/-!
# Public strictness and small-width boundaries without exposing a gate AST

Each real bi-flip includes one controlled complement CNOT per target bit.
Their actual unselected occurrences give a symbolic CNOT lower bound and
strict Toffoli/time savings at the final supplied-control consumer. Widths
zero, one and two retain exactly the previous costs and literal programs.
-/

namespace QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown

noncomputable section

open MAU.Multiplication EncodedBit GateSpec BinaryLabelEncoding
open VariableGidney VariableGidney.PushdownComparison
open Accumulate.Gidney.ControlPushdown

private lemma complement_xCount (width : Nat) :
    xCount (MAU.Addition.Gidney.complementGates width) = width := by
  simp only [xCount, MAU.Addition.Gidney.complementGates, List.map_ofFn,
    Function.comp_def, xMultiplicity]
  simp

private lemma biFlip_cCount_lower (extra : Nat)
    (pivot : Fin (2 ^ (extra + 3) + 1)) :
    extra + 3 ≤ cCount (MAU.Addition.Gidney.biFlipGates (extra + 3) pivot) := by
  have placed := sum_xMultiplicity_eq_of_events_eq .empty
    (map_event_prodLeft (oracles := .empty) (left := finIdentity (extra + 3)) bool
      (MAU.Addition.Gidney.complementGates (extra + 3)))
  rw [biFlip_cCount_eq_body_xCount, MAU.Addition.Gidney.biFlipBodyGates, xCount_append]
  change extra + 3 ≤ xCount _ +
    xCount ((MAU.Addition.Gidney.complementGates (extra + 3)).map (GateSpec.prodLeft bool))
  change xCount ((MAU.Addition.Gidney.complementGates (extra + 3)).map
    (GateSpec.prodLeft bool)) = xCount _ at placed
  rw [placed, complement_xCount]
  omega

private lemma source_cnot_lower (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) (constant : Fin (modulus.val + 1)) :
    6 * width ≤ sourceCnotIncrease width modulus constant := by
  match width with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | extra + 3 =>
      have first := biFlip_cCount_lower extra (Nat.FixedWidth.offsetFirstPivot modulus constant)
      have middle := biFlip_cCount_lower extra modulus
      have last := biFlip_cCount_lower extra (Nat.FixedWidth.offsetLastPivot modulus constant)
      change 6 * (extra + 3) ≤ offsetCnotIncrease extra modulus constant
      unfold offsetCnotIncrease
      omega

private lemma accumulatePrefix_cnot_lower (outerWidth width : Nat) (large : 3 ≤ width)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient count : Nat)
    (within : count ≤ width) :
    count * (6 * width) ≤
      cCount (twoPrefix outerWidth width address modulus coefficient count within) := by
  induction count with
  | zero => simpa only [Nat.zero_mul] using
      (Nat.zero_le (cCount (twoPrefix outerWidth width address modulus coefficient 0 within)))
  | succ index ih =>
      have actual := (VariableGidney.PushdownComparison.source_coordinates outerWidth width
        address ⟨index, by omega⟩ modulus (Nat.FixedWidth.accumulateConstant modulus
          coefficient index)).2.2.1
      have lower := source_cnot_lower width large modulus
        (Nat.FixedWidth.accumulateConstant modulus coefficient index)
      rw [twoPrefix, cCount_append, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) (lower.trans_eq actual.symm)

private lemma accumulate_cnot_lower (outerWidth width : Nat) (large : 3 ≤ width)
    (address : Fin outerWidth) (modulus : Fin (2 ^ width + 1)) (coefficient : Nat) :
    width * (6 * width) ≤ cCount (twoGates outerWidth width address modulus coefficient) := by
  match width with
  | 0 => omega
  | 1 => omega
  | 2 => omega
  | extra + 3 =>
      exact accumulatePrefix_cnot_lower outerWidth (extra + 3) large address modulus coefficient
        (extra + 3) (Nat.le_refl _)

private lemma productPrefix_cnot_lower (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) (count : Nat) (within : count ≤ width) :
    count * (width * (6 * width)) ≤ cCount (prefixGates width modulus count within) := by
  induction count with
  | zero => simpa only [Nat.zero_mul] using
      (Nat.zero_le (cCount (prefixGates width modulus 0 within)))
  | succ index ih =>
      have lower : width * (6 * width) ≤ cCount (stageGates width modulus ⟨index, by omega⟩) :=
        accumulate_cnot_lower width width large ⟨index, by omega⟩ modulus (2 ^ index)
      rw [prefixGates, cCount_append, Nat.succ_mul]
      exact Nat.add_le_add (ih (by omega)) lower

/-- The real unselected complements contribute at least this many source CNOTs. -/
public lemma actual_cnot_lower (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) : 6 * width ^ 3 ≤ actualCnotCount width modulus := by
  calc
    6 * width ^ 3 = width * (width * (6 * width)) := by ring
    _ ≤ actualCnotCount width modulus :=
      productPrefix_cnot_lower width large modulus width (Nat.le_refl width)

/-- Every large-width actual source program has a positive, separately paid CNOT coordinate. -/
public lemma actual_cnot_pos (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) : 0 < actualCnotCount width modulus := by
  have positive : 0 < width := by omega
  exact (Nat.mul_pos (by decide : 0 < 6) (Nat.pow_pos positive)).trans_le
    (actual_cnot_lower width large modulus)

/-- Small paths have zero Toffoli and time reduction for every fitted modulus. -/
public lemma small_savings (width : Nat) (small : width ≤ 2)
    (modulus : Fin (2 ^ width + 1)) :
    toffoliSaving width modulus = 0 ∧ quantumTimeSaving width modulus = 0 := by
  match width with
  | 0 => exact ⟨rfl, rfl⟩
  | 1 => exact ⟨rfl, rfl⟩
  | 2 => exact ⟨rfl, rfl⟩
  | extra + 3 => omega

/-- The source program's actual Toffoli reduction is strictly positive at every large width. -/
public lemma source_toffoli_strict (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) :
    placedToffoliCount width modulus < previousToffoliCount width modulus := by
  have positive := actual_cnot_pos width large modulus
  have split := saving_decomposition width modulus
  have actual := (placed_comparison width modulus).1
  omega

/-- The final real supplied-control consumer has strict Toffoli and time reductions. -/
public lemma controlled_strict (width : Nat) (large : 3 ≤ width)
    (modulus : Fin (2 ^ width + 1)) :
    Controlled.controlledToffoliCount width modulus <
        Controlled.previousControlledToffoliCount width modulus ∧
      Controlled.controlledQuantumTime width modulus <
        Controlled.previousControlledQuantumTime width modulus := by
  have positive := actual_cnot_pos width large modulus
  have saving : 0 < Controlled.controlledSaving width modulus := by
    unfold Controlled.controlledSaving
    omega
  have actual := Controlled.controlled_comparison width modulus
  omega

end

end QuantumAlg.MeasuredUncompute.NativeProductFrame.Pushdown
