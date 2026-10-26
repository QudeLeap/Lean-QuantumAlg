/-
Copyright (c) 2026 QudeLeap. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: QudeLeap Team
-/

module

import QuantumAlg.Init
public import QuantumAlg.Analysis.FTQC.CliffordT.Checker.Basic
public import QuantumAlg.Analysis.FTQC.CliffordT.CertificateData

/-!
# Kernel verification of synthesized rotation candidates

Generated accumulator checkpoints split long word reductions into eight-letter steps.
Each step and the final rational error bound are proved by kernel computation.
The final theorem rewrites the original checker, retaining its semantic soundness.
-/

section

namespace QuantumAlg.CliffordT
private def word23Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word23State1 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word23Step0 :
    word23Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word23State1 := by decide +kernel

private def word23Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word23State2 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word23Step1 :
    word23Chunk1.foldl (fun acc a => a.applyPacked acc)
      word23State1 = word23State2 := by decide +kernel

private def word23Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word23State3 : PackedMat2 :=
    ⟨⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(-1 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word23Step2 :
    word23Chunk2.foldl (fun acc a => a.applyPacked acc)
      word23State2 = word23State3 := by decide +kernel

private def word23Chunk3 : List Letter := [.s, .s, .h, .s, .s, .h, .t, .h]
private def word23State4 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨(0 : Dyadic),
        (0 : Dyadic)⟩⟩⟩
private lemma word23Step3 :
    word23Chunk3.foldl (fun acc a => a.applyPacked acc)
      word23State3 = word23State4 := by decide +kernel

private def word23Chunk4 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word23State5 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        (0 : Dyadic)⟩⟩⟩
private lemma word23Step4 :
    word23Chunk4.foldl (fun acc a => a.applyPacked acc)
      word23State4 = word23State5 := by decide +kernel

private def word23Chunk5 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word23State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word23Step5 :
    word23Chunk5.foldl (fun acc a => a.applyPacked acc)
      word23State5 = word23State6 := by decide +kernel

private def word23Chunk6 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word23State7 : PackedMat2 :=
    ⟨⟨⟨((-1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨(0 : Dyadic),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 1)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((-1 : Dyadic) * half ^ 4)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word23Step6 :
    word23Chunk6.foldl (fun acc a => a.applyPacked acc)
      word23State6 = word23State7 := by decide +kernel

private def word23Chunk7 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word23State8 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 5)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((5 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-5 : Dyadic) * half ^ 5)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-5 : Dyadic) * half ^ 4),
        ((13 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 3),
        ((9 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word23Step7 :
    word23Chunk7.foldl (fun acc a => a.applyPacked acc)
      word23State7 = word23State8 := by decide +kernel

private def word23Chunk8 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word23State9 : PackedMat2 :=
    ⟨⟨⟨((13 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((23 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((-11 : Dyadic) * half ^ 5),
        ((7 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((-9 : Dyadic) * half ^ 4)⟩,
       ⟨((-1 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 5)⟩⟩⟩
private lemma word23Step8 :
    word23Chunk8.foldl (fun acc a => a.applyPacked acc)
      word23State8 = word23State9 := by decide +kernel

private def word23Chunk9 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word23State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((7 : Dyadic) * half ^ 5),
        ((1 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-13 : Dyadic) * half ^ 6)⟩,
       ⟨((-11 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-11 : Dyadic) * half ^ 4),
        ((-11 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-13 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 4)⟩⟩⟩
private lemma word23Step9 :
    word23Chunk9.foldl (fun acc a => a.applyPacked acc)
      word23State9 = word23State10 := by decide +kernel

private def word23Chunk10 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word23State11 : PackedMat2 :=
    ⟨⟨⟨((-41 : Dyadic) * half ^ 6),
        ((-5 : Dyadic) * half ^ 7)⟩,
       ⟨((11 : Dyadic) * half ^ 5),
        ((-11 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((41 : Dyadic) * half ^ 7)⟩,
       ⟨((1 : Dyadic) * half ^ 6),
        ((-45 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 5),
        ((-3 : Dyadic) * half ^ 7)⟩,
       ⟨((-43 : Dyadic) * half ^ 6),
        ((-1 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 3),
        ((-19 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 6),
        ((-63 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word23Step10 :
    word23Chunk10.foldl (fun acc a => a.applyPacked acc)
      word23State10 = word23State11 := by decide +kernel

private def word23Chunk11 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word23State12 : PackedMat2 :=
    ⟨⟨⟨((-25 : Dyadic) * half ^ 7),
        ((-37 : Dyadic) * half ^ 7)⟩,
       ⟨((-95 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((-5 : Dyadic) * half ^ 4),
        ((-5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((15 : Dyadic) * half ^ 7)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        ((5 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((25 : Dyadic) * half ^ 7),
        ((37 : Dyadic) * half ^ 7)⟩,
       ⟨((-95 : Dyadic) * half ^ 7),
        ((19 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word23Step11 :
    word23Chunk11.foldl (fun acc a => a.applyPacked acc)
      word23State11 = word23State12 := by decide +kernel

private def word23Chunk12 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word23State13 : PackedMat2 :=
    ⟨⟨⟨((-11 : Dyadic) * half ^ 8),
        ((-59 : Dyadic) * half ^ 8)⟩,
       ⟨((-27 : Dyadic) * half ^ 8),
        ((-71 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 8),
        ((5 : Dyadic) * half ^ 8)⟩,
       ⟨((107 : Dyadic) * half ^ 8),
        ((-11 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-49 : Dyadic) * half ^ 8),
        ((31 : Dyadic) * half ^ 8)⟩,
       ⟨((-39 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((83 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 5)⟩,
       ⟨((201 : Dyadic) * half ^ 8),
        ((19 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word23Step12 :
    word23Chunk12.foldl (fun acc a => a.applyPacked acc)
      word23State12 = word23State13 := by decide +kernel

private def word23Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word23State14 : PackedMat2 :=
    ⟨⟨⟨((57 : Dyadic) * half ^ 7),
        ((165 : Dyadic) * half ^ 9)⟩,
       ⟨((-35 : Dyadic) * half ^ 7),
        ((69 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-19 : Dyadic) * half ^ 7),
        ((75 : Dyadic) * half ^ 8)⟩,
       ⟨((-45 : Dyadic) * half ^ 8),
        ((23 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((45 : Dyadic) * half ^ 8),
        ((-23 : Dyadic) * half ^ 6)⟩,
       ⟨((19 : Dyadic) * half ^ 7),
        ((-75 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-35 : Dyadic) * half ^ 7),
        ((69 : Dyadic) * half ^ 9)⟩,
       ⟨((57 : Dyadic) * half ^ 7),
        ((165 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word23Step13 :
    word23Chunk13.foldl (fun acc a => a.applyPacked acc)
      word23State13 = word23State14 := by decide +kernel

private def word23Chunk14 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word23State15 : PackedMat2 :=
    ⟨⟨⟨((-5 : Dyadic) * half ^ 5),
        ((9 : Dyadic) * half ^ 7)⟩,
       ⟨((-255 : Dyadic) * half ^ 9),
        ((51 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((-125 : Dyadic) * half ^ 9),
        ((75 : Dyadic) * half ^ 10)⟩,
       ⟨((363 : Dyadic) * half ^ 9),
        ((185 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((55 : Dyadic) * half ^ 9),
        ((61 : Dyadic) * half ^ 7)⟩,
       ⟨((65 : Dyadic) * half ^ 8),
        ((119 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-33 : Dyadic) * half ^ 8),
        ((175 : Dyadic) * half ^ 10)⟩,
       ⟨((-69 : Dyadic) * half ^ 8),
        ((335 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word23Step14 :
    word23Chunk14.foldl (fun acc a => a.applyPacked acc)
      word23State14 = word23State15 := by decide +kernel

private def word23Chunk15 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word23State16 : PackedMat2 :=
    ⟨⟨⟨((101 : Dyadic) * half ^ 9),
        ((-289 : Dyadic) * half ^ 11)⟩,
       ⟨((-239 : Dyadic) * half ^ 10),
        ((-623 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-13 : Dyadic) * half ^ 6),
        ((-507 : Dyadic) * half ^ 11)⟩,
       ⟨((-195 : Dyadic) * half ^ 10),
        ((1005 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((195 : Dyadic) * half ^ 10),
        ((-1005 : Dyadic) * half ^ 11)⟩,
       ⟨((13 : Dyadic) * half ^ 6),
        ((507 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-239 : Dyadic) * half ^ 10),
        ((-623 : Dyadic) * half ^ 11)⟩,
       ⟨((101 : Dyadic) * half ^ 9),
        ((-289 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word23Step15 :
    word23Chunk15.foldl (fun acc a => a.applyPacked acc)
      word23State15 = word23State16 := by decide +kernel

private def word23Chunk16 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word23State17 : PackedMat2 :=
    ⟨⟨⟨((-49 : Dyadic) * half ^ 11),
        ((-337 : Dyadic) * half ^ 12)⟩,
       ⟨((-183 : Dyadic) * half ^ 10),
        ((-43 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-249 : Dyadic) * half ^ 8),
        ((25 : Dyadic) * half ^ 12)⟩,
       ⟨((-161 : Dyadic) * half ^ 11),
        ((-109 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-161 : Dyadic) * half ^ 11),
        ((-109 : Dyadic) * half ^ 12)⟩,
       ⟨((-249 : Dyadic) * half ^ 8),
        ((25 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((183 : Dyadic) * half ^ 10),
        ((43 : Dyadic) * half ^ 12)⟩,
       ⟨((49 : Dyadic) * half ^ 11),
        ((337 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word23Step16 :
    word23Chunk16.foldl (fun acc a => a.applyPacked acc)
      word23State16 = word23State17 := by decide +kernel

private def word23Chunk17 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word23State18 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 7),
        ((-943 : Dyadic) * half ^ 12)⟩,
       ⟨((-25 : Dyadic) * half ^ 11),
        ((271 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((333 : Dyadic) * half ^ 12),
        ((-131 : Dyadic) * half ^ 8)⟩,
       ⟨((-2291 : Dyadic) * half ^ 12),
        ((-89 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-333 : Dyadic) * half ^ 12),
        ((131 : Dyadic) * half ^ 8)⟩,
       ⟨((-2291 : Dyadic) * half ^ 12),
        ((-89 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 7),
        ((-943 : Dyadic) * half ^ 12)⟩,
       ⟨((25 : Dyadic) * half ^ 11),
        ((-271 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word23Step17 :
    word23Chunk17.foldl (fun acc a => a.applyPacked acc)
      word23State17 = word23State18 := by decide +kernel

private def word23Chunk18 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word23State19 : PackedMat2 :=
    ⟨⟨⟨((-1329 : Dyadic) * half ^ 13),
        ((355 : Dyadic) * half ^ 13)⟩,
       ⟨((147 : Dyadic) * half ^ 13),
        ((-1003 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((327 : Dyadic) * half ^ 10),
        ((-647 : Dyadic) * half ^ 11)⟩,
       ⟨((-1583 : Dyadic) * half ^ 11),
        ((-1167 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-3755 : Dyadic) * half ^ 13),
        ((-929 : Dyadic) * half ^ 12)⟩,
       ⟨((-1421 : Dyadic) * half ^ 13),
        ((2237 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((81 : Dyadic) * half ^ 10),
        ((591 : Dyadic) * half ^ 13)⟩,
       ⟨((-679 : Dyadic) * half ^ 12),
        ((369 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word23Step18 :
    word23Chunk18.foldl (fun acc a => a.applyPacked acc)
      word23State18 = word23State19 := by decide +kernel

private def word23Chunk19 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word23State20 : PackedMat2 :=
    ⟨⟨⟨((-5769 : Dyadic) * half ^ 14),
        ((-1493 : Dyadic) * half ^ 14)⟩,
       ⟨((-719 : Dyadic) * half ^ 14),
        ((-1043 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((1009 : Dyadic) * half ^ 14),
        ((2393 : Dyadic) * half ^ 13)⟩,
       ⟨((1611 : Dyadic) * half ^ 14),
        ((-9275 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-1009 : Dyadic) * half ^ 14),
        ((-2393 : Dyadic) * half ^ 13)⟩,
       ⟨((1611 : Dyadic) * half ^ 14),
        ((-9275 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-5769 : Dyadic) * half ^ 14),
        ((-1493 : Dyadic) * half ^ 14)⟩,
       ⟨((719 : Dyadic) * half ^ 14),
        ((1043 : Dyadic) * half ^ 13)⟩⟩⟩
private lemma word23Step19 :
    word23Chunk19.foldl (fun acc a => a.applyPacked acc)
      word23State19 = word23State20 := by decide +kernel

private def word23Chunk20 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word23State21 : PackedMat2 :=
    ⟨⟨⟨((759 : Dyadic) * half ^ 12),
        ((-933 : Dyadic) * half ^ 13)⟩,
       ⟨((-3509 : Dyadic) * half ^ 14),
        ((-5963 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((709 : Dyadic) * half ^ 12),
        ((2695 : Dyadic) * half ^ 15)⟩,
       ⟨((-1093 : Dyadic) * half ^ 13),
        ((17457 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-7381 : Dyadic) * half ^ 14),
        ((2511 : Dyadic) * half ^ 14)⟩,
       ⟨((-2519 : Dyadic) * half ^ 12),
        ((-325 : Dyadic) * half ^ 14)⟩⟩,
     ⟨⟨((-4097 : Dyadic) * half ^ 14),
        ((-6545 : Dyadic) * half ^ 15)⟩,
       ⟨((-7829 : Dyadic) * half ^ 14),
        ((-473 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word23Step20 :
    word23Chunk20.foldl (fun acc a => a.applyPacked acc)
      word23State20 = word23State21 := by decide +kernel

private def word23Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word23State22 : PackedMat2 :=
    ⟨⟨⟨((1099 : Dyadic) * half ^ 12),
        ((8371 : Dyadic) * half ^ 16)⟩,
       ⟨((-11951 : Dyadic) * half ^ 15),
        ((-17181 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((22927 : Dyadic) * half ^ 15),
        ((-13639 : Dyadic) * half ^ 16)⟩,
       ⟨((1967 : Dyadic) * half ^ 14),
        ((8585 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-2527 : Dyadic) * half ^ 15),
        ((26861 : Dyadic) * half ^ 16)⟩,
       ⟨((-1389 : Dyadic) * half ^ 12),
        ((18993 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((4405 : Dyadic) * half ^ 15),
        ((3159 : Dyadic) * half ^ 16)⟩,
       ⟨((-1597 : Dyadic) * half ^ 12),
        ((-20743 : Dyadic) * half ^ 16)⟩⟩⟩
private lemma word23Step21 :
    word23Chunk21.foldl (fun acc a => a.applyPacked acc)
      word23State21 = word23State22 := by decide +kernel

private def word23Chunk22 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word23State23 : PackedMat2 :=
    ⟨⟨⟨((13199 : Dyadic) * half ^ 15),
        ((48689 : Dyadic) * half ^ 17)⟩,
       ⟨((-5387 : Dyadic) * half ^ 16),
        ((-22189 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-1145 : Dyadic) * half ^ 14),
        ((8145 : Dyadic) * half ^ 17)⟩,
       ⟨((-37805 : Dyadic) * half ^ 16),
        ((36173 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((-22159 : Dyadic) * half ^ 16),
        ((42385 : Dyadic) * half ^ 17)⟩,
       ⟨((7007 : Dyadic) * half ^ 15),
        ((-33225 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((6625 : Dyadic) * half ^ 15),
        ((21011 : Dyadic) * half ^ 17)⟩,
       ⟨((35439 : Dyadic) * half ^ 16),
        ((31785 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word23Step22 :
    word23Chunk22.foldl (fun acc a => a.applyPacked acc)
      word23State22 = word23State23 := by decide +kernel

private def word23Chunk23 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word23State24 : PackedMat2 :=
    ⟨⟨⟨((-2033 : Dyadic) * half ^ 17),
        ((84813 : Dyadic) * half ^ 18)⟩,
       ⟨((19793 : Dyadic) * half ^ 16),
        ((-59845 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-6627 : Dyadic) * half ^ 14),
        ((40149 : Dyadic) * half ^ 18)⟩,
       ⟨((57749 : Dyadic) * half ^ 17),
        ((80867 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((57749 : Dyadic) * half ^ 17),
        ((80867 : Dyadic) * half ^ 18)⟩,
       ⟨((-6627 : Dyadic) * half ^ 14),
        ((40149 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-19793 : Dyadic) * half ^ 16),
        ((59845 : Dyadic) * half ^ 18)⟩,
       ⟨((2033 : Dyadic) * half ^ 17),
        ((-84813 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word23Step23 :
    word23Chunk23.foldl (fun acc a => a.applyPacked acc)
      word23State23 = word23State24 := by decide +kernel

private def word23Chunk24 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word23State25 : PackedMat2 :=
    ⟨⟨⟨((-21721 : Dyadic) * half ^ 16),
        ((3167 : Dyadic) * half ^ 14)⟩,
       ⟨((285 : Dyadic) * half ^ 12),
        ((13219 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-10671 : Dyadic) * half ^ 18),
        ((-47915 : Dyadic) * half ^ 18)⟩,
       ⟨((23059 : Dyadic) * half ^ 18),
        ((158297 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((-55191 : Dyadic) * half ^ 17),
        ((-3097 : Dyadic) * half ^ 17)⟩,
       ⟨((51553 : Dyadic) * half ^ 16),
        ((16865 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((63891 : Dyadic) * half ^ 18),
        ((-17161 : Dyadic) * half ^ 17)⟩,
       ⟨((37453 : Dyadic) * half ^ 18),
        ((-26281 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word23Step24 :
    word23Chunk24.foldl (fun acc a => a.applyPacked acc)
      word23State24 = word23State25 := by decide +kernel

private def word23Chunk25 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word23State26 : PackedMat2 :=
    ⟨⟨⟨((60045 : Dyadic) * half ^ 19),
        ((-8075 : Dyadic) * half ^ 14)⟩,
       ⟨((-49775 : Dyadic) * half ^ 19),
        ((116827 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-100649 : Dyadic) * half ^ 19),
        ((-155749 : Dyadic) * half ^ 19)⟩,
       ⟨((219039 : Dyadic) * half ^ 19),
        ((3227 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-100649 : Dyadic) * half ^ 19),
        ((-155749 : Dyadic) * half ^ 19)⟩,
       ⟨((-219039 : Dyadic) * half ^ 19),
        ((-3227 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-60045 : Dyadic) * half ^ 19),
        ((8075 : Dyadic) * half ^ 14)⟩,
       ⟨((-49775 : Dyadic) * half ^ 19),
        ((116827 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word23Step25 :
    word23Chunk25.foldl (fun acc a => a.applyPacked acc)
      word23State25 = word23State26 := by decide +kernel

private def word23Chunk26 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word23State27 : PackedMat2 :=
    ⟨⟨⟨((-583473 : Dyadic) * half ^ 20),
        ((-13285 : Dyadic) * half ^ 17)⟩,
       ⟨((-640543 : Dyadic) * half ^ 20),
        ((22469 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((105079 : Dyadic) * half ^ 20),
        ((-146783 : Dyadic) * half ^ 19)⟩,
       ⟨((-63921 : Dyadic) * half ^ 20),
        ((262379 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-105079 : Dyadic) * half ^ 20),
        ((146783 : Dyadic) * half ^ 19)⟩,
       ⟨((-63921 : Dyadic) * half ^ 20),
        ((262379 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-583473 : Dyadic) * half ^ 20),
        ((-13285 : Dyadic) * half ^ 17)⟩,
       ⟨((640543 : Dyadic) * half ^ 20),
        ((-22469 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word23Step26 :
    word23Chunk26.foldl (fun acc a => a.applyPacked acc)
      word23State26 = word23State27 := by decide +kernel

private def word23Chunk27 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word23State28 : PackedMat2 :=
    ⟨⟨⟨((-490239 : Dyadic) * half ^ 21),
        ((269955 : Dyadic) * half ^ 21)⟩,
       ⟨((-40747 : Dyadic) * half ^ 21),
        ((-296679 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-1516033 : Dyadic) * half ^ 21),
        ((-232775 : Dyadic) * half ^ 21)⟩,
       ⟨((-403187 : Dyadic) * half ^ 21),
        ((151747 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-1516033 : Dyadic) * half ^ 21),
        ((-232775 : Dyadic) * half ^ 21)⟩,
       ⟨((403187 : Dyadic) * half ^ 21),
        ((-151747 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((490239 : Dyadic) * half ^ 21),
        ((-269955 : Dyadic) * half ^ 21)⟩,
       ⟨((-40747 : Dyadic) * half ^ 21),
        ((-296679 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word23Step27 :
    word23Chunk27.foldl (fun acc a => a.applyPacked acc)
      word23State27 = word23State28 := by decide +kernel

private def word23Chunk28 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word23State29 : PackedMat2 :=
    ⟨⟨⟨((67435 : Dyadic) * half ^ 20),
        ((1698859 : Dyadic) * half ^ 22)⟩,
       ⟨((-159627 : Dyadic) * half ^ 21),
        ((-2010489 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-493093 : Dyadic) * half ^ 21),
        ((1095447 : Dyadic) * half ^ 22)⟩,
       ⟨((-107327 : Dyadic) * half ^ 20),
        ((46103 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((570775 : Dyadic) * half ^ 21),
        ((-707747 : Dyadic) * half ^ 22)⟩,
       ⟨((4099 : Dyadic) * half ^ 14),
        ((-278439 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((155815 : Dyadic) * half ^ 21),
        ((24757 : Dyadic) * half ^ 22)⟩,
       ⟨((-927337 : Dyadic) * half ^ 20),
        ((-294497 : Dyadic) * half ^ 22)⟩⟩⟩
private lemma word23Step28 :
    word23Chunk28.foldl (fun acc a => a.applyPacked acc)
      word23State28 = word23State29 := by decide +kernel

private def word23Chunk29 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word23State30 : PackedMat2 :=
    ⟨⟨⟨((215739 : Dyadic) * half ^ 19),
        ((-1443261 : Dyadic) * half ^ 23)⟩,
       ⟨((1420703 : Dyadic) * half ^ 22),
        ((-1920561 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((931383 : Dyadic) * half ^ 22),
        ((2824487 : Dyadic) * half ^ 23)⟩,
       ⟨((-1002391 : Dyadic) * half ^ 21),
        ((-1291317 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1002391 : Dyadic) * half ^ 21),
        ((1291317 : Dyadic) * half ^ 23)⟩,
       ⟨((-931383 : Dyadic) * half ^ 22),
        ((-2824487 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((1420703 : Dyadic) * half ^ 22),
        ((-1920561 : Dyadic) * half ^ 23)⟩,
       ⟨((215739 : Dyadic) * half ^ 19),
        ((-1443261 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word23Step29 :
    word23Chunk29.foldl (fun acc a => a.applyPacked acc)
      word23State29 = word23State30 := by decide +kernel

private def word23Chunk30 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word23State31 : PackedMat2 :=
    ⟨⟨⟨((-3630549 : Dyadic) * half ^ 23),
        ((805723 : Dyadic) * half ^ 21)⟩,
       ⟨((-2252551 : Dyadic) * half ^ 23),
        ((-384505 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((1573679 : Dyadic) * half ^ 22),
        ((3150349 : Dyadic) * half ^ 23)⟩,
       ⟨((-30321 : Dyadic) * half ^ 21),
        ((-219967 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((2710415 : Dyadic) * half ^ 23),
        ((1513037 : Dyadic) * half ^ 23)⟩,
       ⟨((3590283 : Dyadic) * half ^ 23),
        ((1634321 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1226941 : Dyadic) * half ^ 22),
        ((1470775 : Dyadic) * half ^ 22)⟩,
       ⟨((-1995951 : Dyadic) * half ^ 22),
        ((688999 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word23Step30 :
    word23Chunk30.foldl (fun acc a => a.applyPacked acc)
      word23State30 = word23State31 := by decide +kernel

private def word23Chunk31 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word23State32 : PackedMat2 :=
    ⟨⟨⟨((8819619 : Dyadic) * half ^ 24),
        ((-2421605 : Dyadic) * half ^ 24)⟩,
       ⟨((-8315927 : Dyadic) * half ^ 24),
        ((-272501 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((4169431 : Dyadic) * half ^ 24),
        ((1409141 : Dyadic) * half ^ 23)⟩,
       ⟨((-1363059 : Dyadic) * half ^ 24),
        ((6251957 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((3433675 : Dyadic) * half ^ 24),
        ((-2766245 : Dyadic) * half ^ 24)⟩,
       ⟨((9070239 : Dyadic) * half ^ 24),
        ((701593 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-241597 : Dyadic) * half ^ 24),
        ((8567773 : Dyadic) * half ^ 24)⟩,
       ⟨((4601613 : Dyadic) * half ^ 24),
        ((-125923 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word23Step31 :
    word23Chunk31.foldl (fun acc a => a.applyPacked acc)
      word23State31 = word23State32 := by decide +kernel

private def word23Chunk32 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word23State33 : PackedMat2 :=
    ⟨⟨⟨((5675969 : Dyadic) * half ^ 25),
        ((5730119 : Dyadic) * half ^ 24)⟩,
       ⟨((-11369523 : Dyadic) * half ^ 25),
        ((11402289 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((2465335 : Dyadic) * half ^ 25),
        ((12020059 : Dyadic) * half ^ 25)⟩,
       ⟨((11292035 : Dyadic) * half ^ 25),
        ((386967 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((8924323 : Dyadic) * half ^ 25),
        ((-2206675 : Dyadic) * half ^ 24)⟩,
       ⟨((-15115795 : Dyadic) * half ^ 25),
        ((-6878685 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-57949 : Dyadic) * half ^ 25),
        ((-4261373 : Dyadic) * half ^ 24)⟩,
       ⟨((22862527 : Dyadic) * half ^ 25),
        ((-2846777 : Dyadic) * half ^ 25)⟩⟩⟩
private lemma word23Step32 :
    word23Chunk32.foldl (fun acc a => a.applyPacked acc)
      word23State32 = word23State33 := by decide +kernel

private def word23Chunk33 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word23State34 : PackedMat2 :=
    ⟨⟨⟨((-19292817 : Dyadic) * half ^ 26),
        ((6988057 : Dyadic) * half ^ 24)⟩,
       ⟨((-27253287 : Dyadic) * half ^ 26),
        ((-9077291 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((986523 : Dyadic) * half ^ 26),
        ((-7631047 : Dyadic) * half ^ 25)⟩,
       ⟨((13677347 : Dyadic) * half ^ 26),
        ((22442043 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-986523 : Dyadic) * half ^ 26),
        ((7631047 : Dyadic) * half ^ 25)⟩,
       ⟨((13677347 : Dyadic) * half ^ 26),
        ((22442043 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-19292817 : Dyadic) * half ^ 26),
        ((6988057 : Dyadic) * half ^ 24)⟩,
       ⟨((27253287 : Dyadic) * half ^ 26),
        ((9077291 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word23Step33 :
    word23Chunk33.foldl (fun acc a => a.applyPacked acc)
      word23State33 = word23State34 := by decide +kernel

private def word23Chunk34 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word23State35 : PackedMat2 :=
    ⟨⟨⟨((13910965 : Dyadic) * half ^ 26),
        ((-1505627 : Dyadic) * half ^ 27)⟩,
       ⟨((-48626485 : Dyadic) * half ^ 26),
        ((-7547341 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((6890971 : Dyadic) * half ^ 26),
        ((-29162215 : Dyadic) * half ^ 26)⟩,
       ⟨((784835 : Dyadic) * half ^ 22),
        ((2224035 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-15693125 : Dyadic) * half ^ 25),
        ((-5666389 : Dyadic) * half ^ 27)⟩,
       ⟨((6734545 : Dyadic) * half ^ 24),
        ((-19448331 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-3020857 : Dyadic) * half ^ 26),
        ((-31268725 : Dyadic) * half ^ 26)⟩,
       ⟨((-1131621 : Dyadic) * half ^ 24),
        ((-271215 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word23Step34 :
    word23Chunk34.foldl (fun acc a => a.applyPacked acc)
      word23State34 = word23State35 := by decide +kernel

private def word23Chunk35 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word23State36 : PackedMat2 :=
    ⟨⟨⟨((54011829 : Dyadic) * half ^ 27),
        ((-22955159 : Dyadic) * half ^ 28)⟩,
       ⟨((-774217 : Dyadic) * half ^ 24),
        ((-103206667 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-84792755 : Dyadic) * half ^ 27),
        ((10839499 : Dyadic) * half ^ 28)⟩,
       ⟨((-9321861 : Dyadic) * half ^ 25),
        ((-40757051 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((-1869847 : Dyadic) * half ^ 24),
        ((-122080199 : Dyadic) * half ^ 28)⟩,
       ⟨((25798275 : Dyadic) * half ^ 27),
        ((-47505311 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((63080913 : Dyadic) * half ^ 27),
        ((-47818093 : Dyadic) * half ^ 28)⟩,
       ⟨((-20062877 : Dyadic) * half ^ 26),
        ((-60205565 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word23Step35 :
    word23Chunk35.foldl (fun acc a => a.applyPacked acc)
      word23State35 = word23State36 := by decide +kernel

private def word23Chunk36 : List Letter := [.h, .t, .h, .t, .h, .s, .t, .h]
private def word23State37 : PackedMat2 :=
    ⟨⟨⟨((31963867 : Dyadic) * half ^ 27),
        ((-242053095 : Dyadic) * half ^ 29)⟩,
       ⟨((-71402437 : Dyadic) * half ^ 28),
        ((-133370767 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((104125455 : Dyadic) * half ^ 28),
        ((20830065 : Dyadic) * half ^ 29)⟩,
       ⟨((-1461551 : Dyadic) * half ^ 24),
        ((-161727511 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1461551 : Dyadic) * half ^ 24),
        ((161727511 : Dyadic) * half ^ 29)⟩,
       ⟨((-104125455 : Dyadic) * half ^ 28),
        ((-20830065 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-71402437 : Dyadic) * half ^ 28),
        ((-133370767 : Dyadic) * half ^ 29)⟩,
       ⟨((31963867 : Dyadic) * half ^ 27),
        ((-242053095 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word23Step36 :
    word23Chunk36.foldl (fun acc a => a.applyPacked acc)
      word23State36 = word23State37 := by decide +kernel

private def word23Chunk37 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word23State38 : PackedMat2 :=
    ⟨⟨⟨((285316397 : Dyadic) * half ^ 29),
        ((-16625961 : Dyadic) * half ^ 27)⟩,
       ⟨((-11079997 : Dyadic) * half ^ 29),
        ((145598593 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((298358375 : Dyadic) * half ^ 29),
        ((23702153 : Dyadic) * half ^ 27)⟩,
       ⟨((50832699 : Dyadic) * half ^ 29),
        ((-151459089 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((246267701 : Dyadic) * half ^ 29),
        ((61881419 : Dyadic) * half ^ 28)⟩,
       ⟨((56650477 : Dyadic) * half ^ 29),
        ((-174595537 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((212102437 : Dyadic) * half ^ 29),
        ((-148198197 : Dyadic) * half ^ 29)⟩,
       ⟨((79094749 : Dyadic) * half ^ 29),
        ((17139775 : Dyadic) * half ^ 26)⟩⟩⟩
private lemma word23Step37 :
    word23Chunk37.foldl (fun acc a => a.applyPacked acc)
      word23State37 = word23State38 := by decide +kernel

private def word23Chunk38 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word23State39 : PackedMat2 :=
    ⟨⟨⟨((613970627 : Dyadic) * half ^ 30),
        ((-55189163 : Dyadic) * half ^ 28)⟩,
       ⟨((88488585 : Dyadic) * half ^ 30),
        ((301758829 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((582060695 : Dyadic) * half ^ 30),
        ((36859685 : Dyadic) * half ^ 28)⟩,
       ⟨((105534807 : Dyadic) * half ^ 30),
        ((218104277 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-582060695 : Dyadic) * half ^ 30),
        ((-36859685 : Dyadic) * half ^ 28)⟩,
       ⟨((105534807 : Dyadic) * half ^ 30),
        ((218104277 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((613970627 : Dyadic) * half ^ 30),
        ((-55189163 : Dyadic) * half ^ 28)⟩,
       ⟨((-88488585 : Dyadic) * half ^ 30),
        ((-301758829 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word23Step38 :
    word23Chunk38.foldl (fun acc a => a.applyPacked acc)
      word23State38 = word23State39 := by decide +kernel

private def word23Chunk39 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word23State40 : PackedMat2 :=
    ⟨⟨⟨((-14354261 : Dyadic) * half ^ 26),
        ((36974427 : Dyadic) * half ^ 30)⟩,
       ⟨((791515651 : Dyadic) * half ^ 30),
        ((52882421 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-41646601 : Dyadic) * half ^ 28),
        ((626697439 : Dyadic) * half ^ 31)⟩,
       ⟨((7322399 : Dyadic) * half ^ 24),
        ((-98256059 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((362476749 : Dyadic) * half ^ 30),
        ((-158804985 : Dyadic) * half ^ 29)⟩,
       ⟨((-132110345 : Dyadic) * half ^ 29),
        ((-75511783 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((68790415 : Dyadic) * half ^ 30),
        ((1021183827 : Dyadic) * half ^ 31)⟩,
       ⟨((142739269 : Dyadic) * half ^ 30),
        ((561847475 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word23Step39 :
    word23Chunk39.foldl (fun acc a => a.applyPacked acc)
      word23State39 = word23State40 := by decide +kernel

private def word23Chunk40 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word23State41 : PackedMat2 :=
    ⟨⟨⟨((-550980393 : Dyadic) * half ^ 31),
        ((-1297563475 : Dyadic) * half ^ 32)⟩,
       ⟨((112623761 : Dyadic) * half ^ 29),
        ((1558724097 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-71604273 : Dyadic) * half ^ 31),
        ((-160967895 : Dyadic) * half ^ 32)⟩,
       ⟨((-528179057 : Dyadic) * half ^ 30),
        ((1352434827 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((297866733 : Dyadic) * half ^ 30),
        ((-1127962387 : Dyadic) * half ^ 32)⟩,
       ⟨((-756701361 : Dyadic) * half ^ 31),
        ((984753841 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-130580311 : Dyadic) * half ^ 31),
        ((100485349 : Dyadic) * half ^ 32)⟩,
       ⟨((714071893 : Dyadic) * half ^ 30),
        ((1001475437 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word23Step40 :
    word23Chunk40.foldl (fun acc a => a.applyPacked acc)
      word23State40 = word23State41 := by decide +kernel

private def word23Chunk41 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word23State42 : PackedMat2 :=
    ⟨⟨⟨((-699631355 : Dyadic) * half ^ 31),
        ((-711801977 : Dyadic) * half ^ 32)⟩,
       ⟨((46365747 : Dyadic) * half ^ 30),
        ((-1077301937 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((922241419 : Dyadic) * half ^ 32),
        ((68178149 : Dyadic) * half ^ 29)⟩,
       ⟨((2030982351 : Dyadic) * half ^ 32),
        ((-270660253 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2052343 : Dyadic) * half ^ 31),
        ((-1476611885 : Dyadic) * half ^ 32)⟩,
       ⟨((-543372849 : Dyadic) * half ^ 31),
        ((277185233 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-2866405851 : Dyadic) * half ^ 32),
        ((-606899861 : Dyadic) * half ^ 32)⟩,
       ⟨((1442801897 : Dyadic) * half ^ 32),
        ((-792362849 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word23Step41 :
    word23Chunk41.foldl (fun acc a => a.applyPacked acc)
      word23State41 = word23State42 := by decide +kernel

private def word23Chunk42 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word23State43 : PackedMat2 :=
    ⟨⟨⟨((2055214531 : Dyadic) * half ^ 33),
        ((-3335840787 : Dyadic) * half ^ 33)⟩,
       ⟨((-2776899705 : Dyadic) * half ^ 33),
        ((-3032425723 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((171587177 : Dyadic) * half ^ 32),
        ((-1454140365 : Dyadic) * half ^ 32)⟩,
       ⟨((-200132241 : Dyadic) * half ^ 32),
        ((1416129339 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-1492151391 : Dyadic) * half ^ 33),
        ((-3568133 : Dyadic) * half ^ 30)⟩,
       ⟨((-4324410069 : Dyadic) * half ^ 33),
        ((185859709 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((3184133255 : Dyadic) * half ^ 32),
        ((360842587 : Dyadic) * half ^ 33)⟩,
       ⟨((37926883 : Dyadic) * half ^ 30),
        ((-1208028559 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word23Step42 :
    word23Chunk42.foldl (fun acc a => a.applyPacked acc)
      word23State42 = word23State43 := by decide +kernel

private def word23Chunk43 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word23State44 : PackedMat2 :=
    ⟨⟨⟨((-3494517387 : Dyadic) * half ^ 34),
        ((3671510915 : Dyadic) * half ^ 34)⟩,
       ⟨((-4352811269 : Dyadic) * half ^ 34),
        ((-1602229881 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-8193196683 : Dyadic) * half ^ 34),
        ((-1026345177 : Dyadic) * half ^ 32)⟩,
       ⟨((5230647563 : Dyadic) * half ^ 34),
        ((-6644385999 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((8193196683 : Dyadic) * half ^ 34),
        ((1026345177 : Dyadic) * half ^ 32)⟩,
       ⟨((5230647563 : Dyadic) * half ^ 34),
        ((-6644385999 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-3494517387 : Dyadic) * half ^ 34),
        ((3671510915 : Dyadic) * half ^ 34)⟩,
       ⟨((4352811269 : Dyadic) * half ^ 34),
        ((1602229881 : Dyadic) * half ^ 33)⟩⟩⟩
private lemma word23Step43 :
    word23Chunk43.foldl (fun acc a => a.applyPacked acc)
      word23State43 = word23State44 := by decide +kernel

private def word23Chunk44 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word23State45 : PackedMat2 :=
    ⟨⟨⟨((118258299 : Dyadic) * half ^ 32),
        ((-1771332185 : Dyadic) * half ^ 35)⟩,
       ⟨((-1841107905 : Dyadic) * half ^ 33),
        ((-7393222477 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-3477115033 : Dyadic) * half ^ 33),
        ((593713411 : Dyadic) * half ^ 33)⟩,
       ⟨((-14178969679 : Dyadic) * half ^ 34),
        ((348059957 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((839366865 : Dyadic) * half ^ 34),
        ((7224739613 : Dyadic) * half ^ 35)⟩,
       ⟨((-1535486779 : Dyadic) * half ^ 34),
        ((21133199745 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-1405472573 : Dyadic) * half ^ 33),
        ((-2077624503 : Dyadic) * half ^ 34)⟩,
       ⟨((-4582277331 : Dyadic) * half ^ 34),
        ((-1604591307 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word23Step44 :
    word23Chunk44.foldl (fun acc a => a.applyPacked acc)
      word23State44 = word23State45 := by decide +kernel

private def word23Chunk45 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word23State46 : PackedMat2 :=
    ⟨⟨⟨((8865113691 : Dyadic) * half ^ 35),
        ((5964435225 : Dyadic) * half ^ 36)⟩,
       ⟨((-1318697435 : Dyadic) * half ^ 31),
        ((-8439643891 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((17026856519 : Dyadic) * half ^ 35),
        ((-16375912231 : Dyadic) * half ^ 36)⟩,
       ⟨((-1287947171 : Dyadic) * half ^ 34),
        ((-18589863237 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-8741443867 : Dyadic) * half ^ 34),
        ((14450962177 : Dyadic) * half ^ 36)⟩,
       ⟨((1106975503 : Dyadic) * half ^ 35),
        ((19602750861 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((1237604333 : Dyadic) * half ^ 35),
        ((12234045269 : Dyadic) * half ^ 36)⟩,
       ⟨((-3601019779 : Dyadic) * half ^ 34),
        ((-29964272651 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word23Step45 :
    word23Chunk45.foldl (fun acc a => a.applyPacked acc)
      word23State45 = word23State46 := by decide +kernel

private def word23Chunk46 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word23State47 : PackedMat2 :=
    ⟨⟨⟨((78732347 : Dyadic) * half ^ 29),
        ((50185514759 : Dyadic) * half ^ 37)⟩,
       ⟨((-7713551275 : Dyadic) * half ^ 36),
        ((-15719127925 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((48123082281 : Dyadic) * half ^ 36),
        ((-14356116519 : Dyadic) * half ^ 37)⟩,
       ⟨((-205146085 : Dyadic) * half ^ 33),
        ((-38907449079 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((205146085 : Dyadic) * half ^ 33),
        ((38907449079 : Dyadic) * half ^ 37)⟩,
       ⟨((-48123082281 : Dyadic) * half ^ 36),
        ((14356116519 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-7713551275 : Dyadic) * half ^ 36),
        ((-15719127925 : Dyadic) * half ^ 37)⟩,
       ⟨((78732347 : Dyadic) * half ^ 29),
        ((50185514759 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word23Step46 :
    word23Chunk46.foldl (fun acc a => a.applyPacked acc)
      word23State46 = word23State47 := by decide +kernel

private def word23Chunk47 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .s]
private def word23State48 : PackedMat2 :=
    ⟨⟨⟨((8345829107 : Dyadic) * half ^ 35),
        ((14680691373 : Dyadic) * half ^ 37)⟩,
       ⟨((273983595 : Dyadic) * half ^ 31),
        ((36234041 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((30846019437 : Dyadic) * half ^ 37),
        ((43376187043 : Dyadic) * half ^ 37)⟩,
       ⟨((24128506905 : Dyadic) * half ^ 37),
        ((-76606665659 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-4153809827 : Dyadic) * half ^ 34),
        ((27487263171 : Dyadic) * half ^ 37)⟩,
       ⟨((59991426351 : Dyadic) * half ^ 36),
        ((1679378133 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-15840180685 : Dyadic) * half ^ 37),
        ((-12729566627 : Dyadic) * half ^ 36)⟩,
       ⟨((-13521202061 : Dyadic) * half ^ 37),
        ((-3962091587 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word23Step47 :
    word23Chunk47.foldl (fun acc a => a.applyPacked acc)
      word23State47 = word23State48 := by decide +kernel

private def word23Chunk48 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word23State49 : PackedMat2 :=
    ⟨⟨⟨((-88294305669 : Dyadic) * half ^ 38),
        ((35621579049 : Dyadic) * half ^ 38)⟩,
       ⟨((4166585831 : Dyadic) * half ^ 38),
        ((17701630341 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-12991764023 : Dyadic) * half ^ 38),
        ((155394299047 : Dyadic) * half ^ 38)⟩,
       ⟨((-80848507045 : Dyadic) * half ^ 38),
        ((-7756046017 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-217442667183 : Dyadic) * half ^ 38),
        ((-33928371511 : Dyadic) * half ^ 38)⟩,
       ⟨((93345930911 : Dyadic) * half ^ 38),
        ((-23460067767 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((218318367 : Dyadic) * half ^ 38),
        ((-23115222875 : Dyadic) * half ^ 37)⟩,
       ⟨((-71024839731 : Dyadic) * half ^ 38),
        ((42063859919 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word23Step48 :
    word23Chunk48.foldl (fun acc a => a.applyPacked acc)
      word23State48 = word23State49 := by decide +kernel

private def word23Chunk49 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word23State50 : PackedMat2 :=
    ⟨⟨⟨((-185056244703 : Dyadic) * half ^ 39),
        ((-53449773661 : Dyadic) * half ^ 39)⟩,
       ⟨((119190232497 : Dyadic) * half ^ 39),
        ((-44224343945 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((5517855023 : Dyadic) * half ^ 39),
        ((337969013111 : Dyadic) * half ^ 39)⟩,
       ⟨((-54226368331 : Dyadic) * half ^ 39),
        ((11192513663 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((5517855023 : Dyadic) * half ^ 39),
        ((337969013111 : Dyadic) * half ^ 39)⟩,
       ⟨((54226368331 : Dyadic) * half ^ 39),
        ((-11192513663 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((185056244703 : Dyadic) * half ^ 39),
        ((53449773661 : Dyadic) * half ^ 39)⟩,
       ⟨((119190232497 : Dyadic) * half ^ 39),
        ((-44224343945 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word23Step49 :
    word23Chunk49.foldl (fun acc a => a.applyPacked acc)
      word23State49 = word23State50 := by decide +kernel

private def word23Chunk50 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word23State51 : PackedMat2 :=
    ⟨⟨⟨((-135418441401 : Dyadic) * half ^ 38),
        ((-63239834245 : Dyadic) * half ^ 39)⟩,
       ⟨((-799790023 : Dyadic) * half ^ 39),
        ((20693101091 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((382581654391 : Dyadic) * half ^ 39),
        ((-168990410903 : Dyadic) * half ^ 40)⟩,
       ⟨((96093185613 : Dyadic) * half ^ 39),
        ((316675650883 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((242833030893 : Dyadic) * half ^ 39),
        ((-143244234389 : Dyadic) * half ^ 39)⟩,
       ⟨((36921309995 : Dyadic) * half ^ 38),
        ((119668710001 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((-10491616917 : Dyadic) * half ^ 36),
        ((-270037092779 : Dyadic) * half ^ 40)⟩,
       ⟨((21273366577 : Dyadic) * half ^ 38),
        ((271636672825 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word23Step50 :
    word23Chunk50.foldl (fun acc a => a.applyPacked acc)
      word23State50 = word23State51 := by decide +kernel

private def word23Chunk51 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word23State52 : PackedMat2 :=
    ⟨⟨⟨((-13860816505 : Dyadic) * half ^ 36),
        ((-899735618669 : Dyadic) * half ^ 41)⟩,
       ⟨((-612032335011 : Dyadic) * half ^ 40),
        ((40911162367 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-265883386539 : Dyadic) * half ^ 40),
        ((489873860081 : Dyadic) * half ^ 41)⟩,
       ⟨((53552552809 : Dyadic) * half ^ 37),
        ((-103283708167 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-53552552809 : Dyadic) * half ^ 37),
        ((103283708167 : Dyadic) * half ^ 41)⟩,
       ⟨((265883386539 : Dyadic) * half ^ 40),
        ((-489873860081 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-612032335011 : Dyadic) * half ^ 40),
        ((40911162367 : Dyadic) * half ^ 41)⟩,
       ⟨((-13860816505 : Dyadic) * half ^ 36),
        ((-899735618669 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word23Step51 :
    word23Chunk51.foldl (fun acc a => a.applyPacked acc)
      word23State51 = word23State52 := by decide +kernel

private def word23Chunk52 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word23State53 : PackedMat2 :=
    ⟨⟨⟨((-94408207701 : Dyadic) * half ^ 41),
        ((-160960127297 : Dyadic) * half ^ 41)⟩,
       ⟨((115716882411 : Dyadic) * half ^ 41),
        ((-1409052048851 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((15339552055 : Dyadic) * half ^ 36),
        ((101330583545 : Dyadic) * half ^ 40)⟩,
       ⟨((25289073953 : Dyadic) * half ^ 39),
        ((478227717047 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((680888884137 : Dyadic) * half ^ 41),
        ((148005490393 : Dyadic) * half ^ 40)⟩,
       ⟨((-275566549957 : Dyadic) * half ^ 41),
        ((97427342487 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((392503044037 : Dyadic) * half ^ 39),
        ((-10654337355 : Dyadic) * half ^ 41)⟩,
       ⟨((-624045960777 : Dyadic) * half ^ 40),
        ((3283204533 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word23Step52 :
    word23Chunk52.foldl (fun acc a => a.applyPacked acc)
      word23State52 = word23State53 := by decide +kernel

private def word23Chunk53 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word23State54 : PackedMat2 :=
    ⟨⟨⟨((1907672130981 : Dyadic) * half ^ 42),
        ((880480305939 : Dyadic) * half ^ 41)⟩,
       ⟨((-2055703816217 : Dyadic) * half ^ 42),
        ((1453600943883 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((702423664619 : Dyadic) * half ^ 42),
        ((-248344268259 : Dyadic) * half ^ 41)⟩,
       ⟨((-177493667469 : Dyadic) * half ^ 42),
        ((125506975885 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-702423664619 : Dyadic) * half ^ 42),
        ((248344268259 : Dyadic) * half ^ 41)⟩,
       ⟨((-177493667469 : Dyadic) * half ^ 42),
        ((125506975885 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((1907672130981 : Dyadic) * half ^ 42),
        ((880480305939 : Dyadic) * half ^ 41)⟩,
       ⟨((2055703816217 : Dyadic) * half ^ 42),
        ((-1453600943883 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word23Step53 :
    word23Chunk53.foldl (fun acc a => a.applyPacked acc)
      word23State53 = word23State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word23_check : check word23 23 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word23 = word23State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word23Chunk0 ++ word23Chunk1 ++ word23Chunk2 ++ word23Chunk3 ++
      word23Chunk4 ++ word23Chunk5 ++ word23Chunk6 ++ word23Chunk7 ++
      word23Chunk8 ++ word23Chunk9 ++ word23Chunk10 ++ word23Chunk11 ++
      word23Chunk12 ++ word23Chunk13 ++ word23Chunk14 ++ word23Chunk15 ++
      word23Chunk16 ++ word23Chunk17 ++ word23Chunk18 ++ word23Chunk19 ++
      word23Chunk20 ++ word23Chunk21 ++ word23Chunk22 ++ word23Chunk23 ++
      word23Chunk24 ++ word23Chunk25 ++ word23Chunk26 ++ word23Chunk27 ++
      word23Chunk28 ++ word23Chunk29 ++ word23Chunk30 ++ word23Chunk31 ++
      word23Chunk32 ++ word23Chunk33 ++ word23Chunk34 ++ word23Chunk35 ++
      word23Chunk36 ++ word23Chunk37 ++ word23Chunk38 ++ word23Chunk39 ++
      word23Chunk40 ++ word23Chunk41 ++ word23Chunk42 ++ word23Chunk43 ++
      word23Chunk44 ++ word23Chunk45 ++ word23Chunk46 ++ word23Chunk47 ++
      word23Chunk48 ++ word23Chunk49 ++ word23Chunk50 ++ word23Chunk51 ++
      word23Chunk52 ++ word23Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word23Step0, word23Step1, word23Step2, word23Step3, word23Step4,
      word23Step5, word23Step6, word23Step7, word23Step8, word23Step9,
      word23Step10, word23Step11, word23Step12, word23Step13, word23Step14,
      word23Step15, word23Step16, word23Step17, word23Step18, word23Step19,
      word23Step20, word23Step21, word23Step22, word23Step23, word23Step24,
      word23Step25, word23Step26, word23Step27, word23Step28, word23Step29,
      word23Step30, word23Step31, word23Step32, word23Step33, word23Step34,
      word23Step35, word23Step36, word23Step37, word23Step38, word23Step39,
      word23Step40, word23Step41, word23Step42, word23Step43, word23Step44,
      word23Step45, word23Step46, word23Step47, word23Step48, word23Step49,
      word23Step50, word23Step51, word23Step52, word23Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
