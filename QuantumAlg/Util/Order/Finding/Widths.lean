/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

public import Mathlib.Analysis.SpecialFunctions.Log.Base
import Mathlib.Tactic

/-!
# Minimal binary widths for order finding

The phase cardinality is the least power of two at least the square of the
modulus. This realizes the register window in [Sho95, source.tex:1183-1185]
without asking a caller to supply a separate register-size certificate.
-/

namespace QuantumAlg.OrderFinding

/-- The minimum number of target qubits that represents all residues. -/
public def targetWidth (modulus : Nat) : Nat := Nat.clog 2 modulus

/-- The minimum phase width in the general order-finding register window. -/
public def phaseWidth (modulus : Nat) : Nat := Nat.clog 2 (modulus ^ 2)

/-- The natural binary width is the real logarithm ceiling used in the statement. -/
public lemma orderFinding_targetWidth_eq_logCeiling (N : Nat) :
    targetWidth N = ⌈Real.logb 2 N⌉₊ :=
  (Real.natCeil_logb_natCast 2 N).symm

/-- The phase width agrees with the logarithm ceiling of the squared modulus. -/
public lemma orderFinding_phaseWidth_eq_logCeiling (N : Nat) :
    phaseWidth N = ⌈Real.logb 2 ((N : Real) ^ 2)⌉₊ := by
  calc
    phaseWidth N = ⌈Real.logb 2 (((N ^ 2 : Nat) : Real))⌉₊ :=
      (Real.natCeil_logb_natCast 2 (N ^ 2)).symm
    _ = _ := congrArg (fun value : Real => ⌈Real.logb 2 value⌉₊) (Nat.cast_pow N 2)

/-- Every residue fits in the minimum target register. -/
public lemma orderFinding_targetWidth_fits (N : Nat) : N ≤ 2 ^ targetWidth N :=
  Nat.le_pow_clog (by decide) N

/-- The canonical phase cardinality is at least the square of the modulus. -/
public lemma orderFinding_phaseWidth_fits (N : Nat) : N ^ 2 ≤ 2 ^ phaseWidth N :=
  Nat.le_pow_clog (by decide) (N ^ 2)

/-- Nontrivial moduli have positive target and phase widths. -/
public lemma orderFinding_widths_positive {N : Nat} (modulus : 2 ≤ N) :
    0 < targetWidth N ∧ 0 < phaseWidth N := by
  constructor
  · exact Nat.clog_pos (by decide) (by omega)
  · exact Nat.clog_pos (by decide) (by nlinarith)

/-- The least phase register satisfies the strict upper end of Shor's window. -/
public lemma orderFinding_phaseWidth_upper {N : Nat} (modulus : 2 ≤ N) :
    2 ^ phaseWidth N < 2 * N ^ 2 := by
  have positive := (orderFinding_widths_positive modulus).2
  have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (by nlinarith : 1 < N ^ 2)
  have successor : phaseWidth N = (phaseWidth N).pred + 1 :=
    (Nat.succ_pred_eq_of_pos positive).symm
  calc
    2 ^ phaseWidth N = 2 ^ ((phaseWidth N).pred + 1) := congrArg (2 ^ ·) successor
    _ = 2 * 2 ^ (phaseWidth N).pred := by rw [pow_succ, Nat.mul_comm]
    _ < 2 * N ^ 2 := Nat.mul_lt_mul_of_pos_left previous (by decide)

/-- The canonical phase width never exceeds twice the target width. -/
public lemma orderFinding_phaseWidth_le_twice_targetWidth (N : Nat) :
    phaseWidth N ≤ 2 * targetWidth N := by
  apply Nat.clog_le_of_le_pow
  calc
    N ^ 2 ≤ (2 ^ targetWidth N) ^ 2 :=
      Nat.pow_le_pow_left (orderFinding_targetWidth_fits N) 2
    _ = 2 ^ (2 * targetWidth N) := by rw [← pow_mul, Nat.mul_comm]

/-- The canonical phase width is one of the two adjacent widths around twice
the target width. -/
public lemma orderFinding_twice_targetWidth_sub_one_le_phaseWidth
    {N : Nat} (modulus : 2 ≤ N) :
    2 * targetWidth N - 1 ≤ phaseWidth N := by
  have positive := (orderFinding_widths_positive modulus).1
  have previous := Nat.pow_pred_clog_lt_self (by decide : 1 < 2)
    (by omega : 1 < N)
  have square : 2 ^ (2 * (targetWidth N).pred) < N ^ 2 := by
    rw [Nat.mul_comm, pow_mul]
    exact Nat.pow_lt_pow_left previous (by decide)
  have width := (Nat.lt_clog_iff_pow_lt (by decide : 1 < 2)).mpr square
  change 2 * (targetWidth N).pred < phaseWidth N at width
  have predecessor : (targetWidth N).pred + 1 = targetWidth N :=
    Nat.succ_pred_eq_of_pos positive
  omega

end QuantumAlg.OrderFinding
