/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Chain.Program.Query.Label
import all QuantumAlg.Primitives.EllipticCurve.Arithmetic.P256.Point.Window.Query.Columns.Action

/-!
# Original query premises from the complete initialized label

The paid initializer has the original clean pool and zero A word for
all binary X/Y values and all C/N/W bits. Only when interpreting the
target as an ordinary field residue do canonical X/Y coordinates enter.
No condition is added to the inactive binary-word contract.
-/

namespace QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain

namespace Program

noncomputable section

open EncodedBit.WindowLookup Arithmetic.Call Arithmetic.Call.Endpoint
open MAU.Inversion.SharedEEA.Scanned

attribute [local implicit_reducible] capacity width
attribute [local irreducible] modulus

/-- The actual same original pool is clean before every original initialized query. -/
lemma queryInitial_clean (x y : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) :
    Frame.CleanPool (clearedInitial x y flags address).1 :=
  initial_clean_pool x y flags

/-- Every real query loads its actual zero A word, with no condition on numerical X/Y. -/
lemma queryInitial_source_zero (occurrence : Fin 6) (x y : Fin (2 ^ modulus.size))
    (flags : Frame.Controls) (address : Window.Address) (bit : Fin 256) :
    ((Window.resultWord (Window.QueryColumns.assignment occurrence).source).bit bit).get
        (clearedInitial x y flags address) = false := by
  rw [Window.QueryColumns.assignment_source]
  change (WordPort.bit .work1 bit).get
    (Inversion.initial x y (0, (0, false)) flags) = false
  rw [WordPort.bit_get]
  change (Frame.work1 (Inversion.initial x y (0, (0, false)) flags)).val.testBit bit.val = false
  rw [initial_work1_zero]
  exact Nat.zero_testBit bit.val

/-- The complete original numerator is its original ordinary field word. -/
lemma queryInitial_numerator (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    Frame.numerator (clearedInitial (Residue.input x) (Residue.input y) flags address).1 =
      Residue.word y := by
  have actual := (congrArg Frame.numerator
    (initial_physical_label (Residue.input x) (Residue.input y) flags)).trans
      ((Inversion.Transport.state_numerator Inversion.modulus_size _).trans
        (congrArg (Fin.cast (congrArg (fun size => 2 ^ size) Inversion.modulus_size))
          (ControlledResident.initial_numerator modulus (Residue.input x) (Residue.input y)
            (0, (0, false)) flags)))
  exact actual.trans (Residue.cast_input y)

/-- The actual occurrence's target is its original canonical X or Y coordinate. -/
lemma queryInitial_target_canonical (occurrence : Fin 6) (x y : ZMod modulus)
    (flags : Frame.Controls) (address : Window.Address) :
    Canonical ((Window.QueryColumns.assignment occurrence).target.value
      (clearedInitial (Residue.input x) (Residue.input y) flags address).1) := by
  by_cases horizontal : occurrence.val = 0 ∨ occurrence.val = 2 ∨ occurrence.val = 4
  · simp only [Window.QueryColumns.assignment, if_pos horizontal, Offset.Placed.horizontal]
    change Canonical (Frame.work2
      (Inversion.initial (Residue.input x) (Residue.input y) (0, (0, false)) flags))
    have actual := Inversion.initial_value (Residue.input x) (Residue.input y)
      (0, (0, false)) flags
    rw [Residue.cast_input] at actual
    rw [actual]
    exact Residue.word_canonical x
  · simp only [Window.QueryColumns.assignment, if_neg horizontal, Offset.Placed.vertical]
    change Canonical (Frame.numerator _)
    rw [queryInitial_numerator]
    exact Residue.word_canonical y

end

end Program

end QuantumAlg.EllipticCurve.PrimeFieldShortWeierstrass.Arithmetic.P256.Point.Chain
