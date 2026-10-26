/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
import Mathlib.Data.Fin.Basic

/-!
# Disjoint original small-base rows for the two public points

One real X array and one real Y array retain both original point families.
Each family has every full-window base and its final tail base. The row
indices are direct natural offsets with certified bounds, without modular
index truncation or an executed classical regrouping.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables

/-- Original rows zero through baseCount in the two shared coordinate arrays. -/
def firstBaseRows {baseCount : Nat} (index : Fin (baseCount + 1)) :
    Fin (2 * (baseCount + 1)) :=
  ⟨index.val, by have := index.isLt; omega⟩

/-- The second point family follows the complete first family in the same two arrays. -/
def secondBaseRows {baseCount : Nat} (index : Fin (baseCount + 1)) :
    Fin (2 * (baseCount + 1)) :=
  ⟨baseCount + 1 + index.val, by have := index.isLt; omega⟩

/-- Every real first-family base has its own physical row identity. -/
lemma firstBaseRows_injective {baseCount : Nat} :
    Function.Injective (@firstBaseRows baseCount) := by
  intro first second same
  have values := congrArg (fun row : Fin (2 * (baseCount + 1)) => row.val) same
  exact Fin.ext values

/-- Every real second-family base has its own physical row identity. -/
lemma secondBaseRows_injective {baseCount : Nat} :
    Function.Injective (@secondBaseRows baseCount) := by
  intro first second same
  have values := congrArg Fin.val same
  apply Fin.ext
  dsimp only [secondBaseRows] at values
  omega

/-- Every word in the first family is outside every selected row of the second family. -/
lemma firstBaseRows_ne_secondBaseRows {baseCount : Nat}
    (first second : Fin (baseCount + 1)) : firstBaseRows first ≠ secondBaseRows second := by
  intro same
  have values := congrArg Fin.val same
  have bounded := first.isLt
  dsimp only [firstBaseRows, secondBaseRows] at values
  omega

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables
