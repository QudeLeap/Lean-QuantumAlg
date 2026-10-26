/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Builder.Rows
import all QuantumAlg.Components.Classical.EllipticCurve.WindowTables.Batch.Circuit

/-!
# Symbolic actual five-table construction

Each binary layer prepares its power-of-two seed, batches the nonseed
denominators in C/D and writes the new coordinate rows. A final -2y batch
reuses C/D, then every nonzero row is converted into the five target columns.
The identity row is explicitly zeroed last. Loops remain parameterized by
their actual finite counts rather than expanding concrete window tables.
-/

namespace QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame

open Execution ClassicalAlgorithms.Modular

noncomputable section

/-- Actual row of the power-of-two point at this binary level. -/
def layerSeed (window : Nat) (level : Fin window) : Fin (2 ^ window) :=
  ⟨2 ^ level.val, Nat.pow_lt_pow_right (by decide) level.isLt⟩

/-- The immediately preceding power-of-two seed, used only by a noninitial level. -/
def previousSeed (window : Nat) (level : Fin window) : Fin (2 ^ window) :=
  ⟨2 ^ (level.val - 1), Nat.pow_lt_pow_right (by decide)
    (lt_of_le_of_lt (Nat.sub_le _ _) level.isLt)⟩

/-- The nonseed rows present before this level's additions. -/
def layerCount {window : Nat} (level : Fin window) : Nat := 2 ^ level.val - 1

/-- Earlier coordinate row; it is positive and strictly below the current seed. -/
def oldRow {window : Nat} (level : Fin window) (index : Fin (layerCount level)) :
    Fin (2 ^ window) :=
  ⟨index.val + 1, by
    have old := index.isLt
    have seed := (layerSeed window level).isLt
    dsimp only [layerCount, layerSeed] at old seed
    omega⟩

/-- New coordinate row is the actual sum of the seed index and the earlier row index. -/
def newRow {window : Nat} (level : Fin window) (index : Fin (layerCount level)) :
    Fin (2 ^ window) :=
  ⟨2 ^ level.val + (index.val + 1), by
    have old := index.isLt
    have doubled := Nat.pow_le_pow_right Nat.zero_lt_two (Nat.succ_le_of_lt level.isLt)
    rw [pow_succ] at doubled
    dsimp only [layerCount] at old
    have positive := Nat.two_pow_pos level.val
    omega⟩

variable {model : ExecutionModel} [BitWord.Selected model]
  {ctx : RuntimeCtx model.kind} {width window : Nat}
  (frame : TableFrame ctx width (2 ^ window))

/-- The previous seed is doubled into existing array storage; the first seed copies actual input. -/
def prepareSeed (spec : ModulusSpec width) (level : Fin window) : Circuit model ctx ctx :=
  if level.val = 0 then frame.seedRow (layerSeed window level) else
    frame.doubleRow spec (previousSeed window level) (layerSeed window level)

/-- One actual binary layer reuses C and D for its single batch inverse. -/
def layerCircuit (spec : ModulusSpec width) (level : Fin window) : Circuit model ctx ctx :=
  let count := layerCount level
  have fits : count < 2 ^ window := by
    have seed := (layerSeed window level).isLt
    have positive := Nat.two_pow_pos level.val
    dsimp only [layerSeed] at seed
    dsimp only [count, layerCount]
    omega
  .seq (frame.prepareSeed spec level)
    (.seq (Circuit.forRange count fun index =>
        frame.denominatorRow (layerSeed window level) (oldRow level index))
      (.seq (frame.batch.circuit spec count fits)
        (Circuit.forRange count fun index =>
          frame.extendRow (layerSeed window level) (oldRow level index) (newRow level index))))

/-- A nonzero row in the complete final table, with no modular index truncation. -/
def nonzeroRow (window : Nat) (index : Fin (2 ^ window - 1)) : Fin (2 ^ window) :=
  ⟨index.val + 1, by have := index.isLt; omega⟩

/-- The actual five-array program, including all inversions, row writes and identity handling. -/
def circuit (spec : ModulusSpec width) : Circuit model ctx ctx :=
  let count := 2 ^ window - 1
  have fits : count < 2 ^ window := by have := Nat.two_pow_pos window; omega
  .seq (Circuit.forRange window (frame.layerCircuit spec))
    (.seq (Circuit.forRange count fun index =>
        frame.tangentDenominatorRow (nonzeroRow window index))
      (.seq (frame.batch.circuit spec count fits)
        (.seq (Circuit.forRange count fun index => frame.finishRow (nonzeroRow window index))
          (frame.clearIdentityRow ⟨0, Nat.two_pow_pos window⟩))))

end

end QuantumAlg.ClassicalRoutines.EllipticCurve.WindowTables.TableFrame
