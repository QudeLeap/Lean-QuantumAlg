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
private def word20Chunk0 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word20State1 : PackedMat2 :=
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
private lemma word20Step0 :
    word20Chunk0.foldl (fun acc a => a.applyPacked acc)
      PackedMat2.identity = word20State1 := by decide +kernel

private def word20Chunk1 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word20State2 : PackedMat2 :=
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
private lemma word20Step1 :
    word20Chunk1.foldl (fun acc a => a.applyPacked acc)
      word20State1 = word20State2 := by decide +kernel

private def word20Chunk2 : List Letter := [.h, .s, .h, .s, .h, .s, .h, .s]
private def word20State3 : PackedMat2 :=
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
private lemma word20Step2 :
    word20Chunk2.foldl (fun acc a => a.applyPacked acc)
      word20State2 = word20State3 := by decide +kernel

private def word20Chunk3 : List Letter := [.s, .h, .s, .t, .h, .t, .h, .s]
private def word20State4 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        (0 : Dyadic)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((1 : Dyadic) * half ^ 1)⟩,
       ⟨((-1 : Dyadic) * half ^ 1),
        (0 : Dyadic)⟩⟩⟩
private lemma word20Step3 :
    word20Chunk3.foldl (fun acc a => a.applyPacked acc)
      word20State3 = word20State4 := by decide +kernel

private def word20Chunk4 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State5 : PackedMat2 :=
    ⟨⟨⟨(0 : Dyadic),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 2),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨((1 : Dyadic) * half ^ 2),
        ((1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 2),
        ((-1 : Dyadic) * half ^ 3)⟩,
       ⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word20Step4 :
    word20Chunk4.foldl (fun acc a => a.applyPacked acc)
      word20State4 = word20State5 := by decide +kernel

private def word20Chunk5 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .s]
private def word20State6 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩,
       ⟨((-1 : Dyadic) * half ^ 3),
        ((3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩,
       ⟨((-3 : Dyadic) * half ^ 3),
        ((-3 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 3),
        ((1 : Dyadic) * half ^ 2)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩⟩⟩
private lemma word20Step5 :
    word20Chunk5.foldl (fun acc a => a.applyPacked acc)
      word20State5 = word20State6 := by decide +kernel

private def word20Chunk6 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word20State7 : PackedMat2 :=
    ⟨⟨⟨((3 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((7 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((-3 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 4)⟩,
       ⟨((11 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 3)⟩⟩⟩
private lemma word20Step6 :
    word20Chunk6.foldl (fun acc a => a.applyPacked acc)
      word20State6 = word20State7 := by decide +kernel

private def word20Chunk7 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word20State8 : PackedMat2 :=
    ⟨⟨⟨((-11 : Dyadic) * half ^ 4),
        ((3 : Dyadic) * half ^ 5)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨(0 : Dyadic),
        ((-1 : Dyadic) * half ^ 5)⟩,
       ⟨(0 : Dyadic),
        ((11 : Dyadic) * half ^ 5)⟩⟩,
     ⟨⟨((3 : Dyadic) * half ^ 3),
        (0 : Dyadic)⟩,
       ⟨((5 : Dyadic) * half ^ 4),
        (0 : Dyadic)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 2),
        ((-7 : Dyadic) * half ^ 4)⟩,
       ⟨((-7 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 2)⟩⟩⟩
private lemma word20Step7 :
    word20Chunk7.foldl (fun acc a => a.applyPacked acc)
      word20State7 = word20State8 := by decide +kernel

private def word20Chunk8 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word20State9 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((-7 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-9 : Dyadic) * half ^ 5),
        ((-21 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 1),
        ((-15 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 1),
        ((15 : Dyadic) * half ^ 6)⟩,
       ⟨((9 : Dyadic) * half ^ 5),
        ((21 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((-7 : Dyadic) * half ^ 5),
        ((-17 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((-17 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word20Step8 :
    word20Chunk8.foldl (fun acc a => a.applyPacked acc)
      word20State8 = word20State9 := by decide +kernel

private def word20Chunk9 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word20State10 : PackedMat2 :=
    ⟨⟨⟨((1 : Dyadic) * half ^ 3),
        ((-33 : Dyadic) * half ^ 7)⟩,
       ⟨((27 : Dyadic) * half ^ 6),
        ((9 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 6),
        ((-69 : Dyadic) * half ^ 7)⟩,
       ⟨((-9 : Dyadic) * half ^ 5),
        ((-5 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 1),
        ((-19 : Dyadic) * half ^ 7)⟩,
       ⟨((-37 : Dyadic) * half ^ 6),
        ((-17 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-21 : Dyadic) * half ^ 6),
        ((-19 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-35 : Dyadic) * half ^ 7)⟩⟩⟩
private lemma word20Step9 :
    word20Chunk9.foldl (fun acc a => a.applyPacked acc)
      word20State9 = word20State10 := by decide +kernel

private def word20Chunk10 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word20State11 : PackedMat2 :=
    ⟨⟨⟨((-21 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 6)⟩,
       ⟨((1 : Dyadic) * half ^ 3),
        ((45 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-3 : Dyadic) * half ^ 4),
        ((1 : Dyadic) * half ^ 4)⟩,
       ⟨((1 : Dyadic) * half ^ 5),
        ((-69 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 5),
        ((69 : Dyadic) * half ^ 7)⟩,
       ⟨((3 : Dyadic) * half ^ 4),
        ((-1 : Dyadic) * half ^ 4)⟩⟩,
     ⟨⟨((1 : Dyadic) * half ^ 3),
        ((45 : Dyadic) * half ^ 7)⟩,
       ⟨((-21 : Dyadic) * half ^ 6),
        ((3 : Dyadic) * half ^ 6)⟩⟩⟩
private lemma word20Step10 :
    word20Chunk10.foldl (fun acc a => a.applyPacked acc)
      word20State10 = word20State11 := by decide +kernel

private def word20Chunk11 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word20State12 : PackedMat2 :=
    ⟨⟨⟨((57 : Dyadic) * half ^ 8),
        ((-77 : Dyadic) * half ^ 8)⟩,
       ⟨((-29 : Dyadic) * half ^ 8),
        ((9 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((63 : Dyadic) * half ^ 8),
        ((1 : Dyadic) * half ^ 3)⟩,
       ⟨((-201 : Dyadic) * half ^ 8),
        ((-17 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((15 : Dyadic) * half ^ 8),
        ((-69 : Dyadic) * half ^ 8)⟩,
       ⟨((49 : Dyadic) * half ^ 8),
        ((33 : Dyadic) * half ^ 6)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 8),
        ((-7 : Dyadic) * half ^ 7)⟩,
       ⟨((113 : Dyadic) * half ^ 8),
        ((-43 : Dyadic) * half ^ 8)⟩⟩⟩
private lemma word20Step11 :
    word20Chunk11.foldl (fun acc a => a.applyPacked acc)
      word20State11 = word20State12 := by decide +kernel

private def word20Chunk12 : List Letter := [.s, .t, .h, .s, .t, .h, .s, .t]
private def word20State13 : PackedMat2 :=
    ⟨⟨⟨((-7 : Dyadic) * half ^ 8),
        ((-255 : Dyadic) * half ^ 9)⟩,
       ⟨((-41 : Dyadic) * half ^ 6),
        ((-7 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-1 : Dyadic) * half ^ 6),
        ((67 : Dyadic) * half ^ 9)⟩,
       ⟨((-41 : Dyadic) * half ^ 8),
        ((65 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 8),
        ((65 : Dyadic) * half ^ 9)⟩,
       ⟨((-1 : Dyadic) * half ^ 6),
        ((67 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((41 : Dyadic) * half ^ 6),
        ((7 : Dyadic) * half ^ 9)⟩,
       ⟨((7 : Dyadic) * half ^ 8),
        ((255 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word20Step12 :
    word20Chunk12.foldl (fun acc a => a.applyPacked acc)
      word20State12 = word20State13 := by decide +kernel

private def word20Chunk13 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word20State14 : PackedMat2 :=
    ⟨⟨⟨((113 : Dyadic) * half ^ 9),
        ((187 : Dyadic) * half ^ 9)⟩,
       ⟨((27 : Dyadic) * half ^ 9),
        ((-191 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((177 : Dyadic) * half ^ 9),
        ((19 : Dyadic) * half ^ 8)⟩,
       ⟨((227 : Dyadic) * half ^ 9),
        ((-25 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-227 : Dyadic) * half ^ 9),
        ((25 : Dyadic) * half ^ 7)⟩,
       ⟨((-177 : Dyadic) * half ^ 9),
        ((-19 : Dyadic) * half ^ 8)⟩⟩,
     ⟨⟨((27 : Dyadic) * half ^ 9),
        ((-191 : Dyadic) * half ^ 9)⟩,
       ⟨((113 : Dyadic) * half ^ 9),
        ((187 : Dyadic) * half ^ 9)⟩⟩⟩
private lemma word20Step13 :
    word20Chunk13.foldl (fun acc a => a.applyPacked acc)
      word20State13 = word20State14 := by decide +kernel

private def word20Chunk14 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State15 : PackedMat2 :=
    ⟨⟨⟨((11 : Dyadic) * half ^ 10),
        ((147 : Dyadic) * half ^ 10)⟩,
       ⟨((-95 : Dyadic) * half ^ 10),
        ((205 : Dyadic) * half ^ 9)⟩⟩,
     ⟨⟨((-239 : Dyadic) * half ^ 10),
        ((-77 : Dyadic) * half ^ 9)⟩,
       ⟨((1 : Dyadic) * half ^ 10),
        ((527 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((373 : Dyadic) * half ^ 10),
        ((-119 : Dyadic) * half ^ 10)⟩,
       ⟨((-681 : Dyadic) * half ^ 10),
        ((-15 : Dyadic) * half ^ 7)⟩⟩,
     ⟨⟨((-557 : Dyadic) * half ^ 10),
        ((21 : Dyadic) * half ^ 9)⟩,
       ⟨((263 : Dyadic) * half ^ 10),
        ((-53 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word20Step14 :
    word20Chunk14.foldl (fun acc a => a.applyPacked acc)
      word20State14 = word20State15 := by decide +kernel

private def word20Chunk15 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word20State16 : PackedMat2 :=
    ⟨⟨⟨((157 : Dyadic) * half ^ 9),
        ((-245 : Dyadic) * half ^ 11)⟩,
       ⟨((13 : Dyadic) * half ^ 5),
        ((579 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-149 : Dyadic) * half ^ 10),
        ((-619 : Dyadic) * half ^ 11)⟩,
       ⟨((455 : Dyadic) * half ^ 10),
        ((-563 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((149 : Dyadic) * half ^ 10),
        ((619 : Dyadic) * half ^ 11)⟩,
       ⟨((455 : Dyadic) * half ^ 10),
        ((-563 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((157 : Dyadic) * half ^ 9),
        ((-245 : Dyadic) * half ^ 11)⟩,
       ⟨((-13 : Dyadic) * half ^ 5),
        ((-579 : Dyadic) * half ^ 11)⟩⟩⟩
private lemma word20Step15 :
    word20Chunk15.foldl (fun acc a => a.applyPacked acc)
      word20State15 = word20State16 := by decide +kernel

private def word20Chunk16 : List Letter := [.s, .t, .h, .t, .h, .t, .h, .t]
private def word20State17 : PackedMat2 :=
    ⟨⟨⟨((-21 : Dyadic) * half ^ 9),
        ((-713 : Dyadic) * half ^ 12)⟩,
       ⟨((687 : Dyadic) * half ^ 11),
        ((999 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-1509 : Dyadic) * half ^ 11),
        ((495 : Dyadic) * half ^ 12)⟩,
       ⟨((375 : Dyadic) * half ^ 10),
        ((1 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-375 : Dyadic) * half ^ 10),
        ((-1 : Dyadic) * half ^ 12)⟩,
       ⟨((1509 : Dyadic) * half ^ 11),
        ((-495 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((687 : Dyadic) * half ^ 11),
        ((999 : Dyadic) * half ^ 12)⟩,
       ⟨((-21 : Dyadic) * half ^ 9),
        ((-713 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word20Step16 :
    word20Chunk16.foldl (fun acc a => a.applyPacked acc)
      word20State16 = word20State17 := by decide +kernel

private def word20Chunk17 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word20State18 : PackedMat2 :=
    ⟨⟨⟨((-325 : Dyadic) * half ^ 11),
        ((-583 : Dyadic) * half ^ 12)⟩,
       ⟨((-297 : Dyadic) * half ^ 11),
        ((289 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-471 : Dyadic) * half ^ 11),
        ((-2009 : Dyadic) * half ^ 12)⟩,
       ⟨((-89 : Dyadic) * half ^ 8),
        ((677 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-655 : Dyadic) * half ^ 12),
        ((-1183 : Dyadic) * half ^ 12)⟩,
       ⟨((-3363 : Dyadic) * half ^ 12),
        ((241 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((5 : Dyadic) * half ^ 12),
        ((311 : Dyadic) * half ^ 11)⟩,
       ⟨((1161 : Dyadic) * half ^ 12),
        ((7 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word20Step17 :
    word20Chunk17.foldl (fun acc a => a.applyPacked acc)
      word20State17 = word20State18 := by decide +kernel

private def word20Chunk18 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word20State19 : PackedMat2 :=
    ⟨⟨⟨((-1227 : Dyadic) * half ^ 13),
        ((-2411 : Dyadic) * half ^ 13)⟩,
       ⟨((-2857 : Dyadic) * half ^ 13),
        ((-117 : Dyadic) * half ^ 10)⟩⟩,
     ⟨⟨((-2589 : Dyadic) * half ^ 13),
        ((-837 : Dyadic) * half ^ 12)⟩,
       ⟨((2927 : Dyadic) * half ^ 13),
        ((-3405 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((2589 : Dyadic) * half ^ 13),
        ((837 : Dyadic) * half ^ 12)⟩,
       ⟨((2927 : Dyadic) * half ^ 13),
        ((-3405 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-1227 : Dyadic) * half ^ 13),
        ((-2411 : Dyadic) * half ^ 13)⟩,
       ⟨((2857 : Dyadic) * half ^ 13),
        ((117 : Dyadic) * half ^ 10)⟩⟩⟩
private lemma word20Step18 :
    word20Chunk18.foldl (fun acc a => a.applyPacked acc)
      word20State18 = word20State19 := by decide +kernel

private def word20Chunk19 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word20State20 : PackedMat2 :=
    ⟨⟨⟨((439 : Dyadic) * half ^ 13),
        ((865 : Dyadic) * half ^ 11)⟩,
       ⟨((-1699 : Dyadic) * half ^ 12),
        ((-837 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 13),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((-453 : Dyadic) * half ^ 10),
        ((1971 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-41 : Dyadic) * half ^ 13),
        ((49 : Dyadic) * half ^ 8)⟩,
       ⟨((453 : Dyadic) * half ^ 10),
        ((-1971 : Dyadic) * half ^ 13)⟩⟩,
     ⟨⟨((-439 : Dyadic) * half ^ 13),
        ((-865 : Dyadic) * half ^ 11)⟩,
       ⟨((-1699 : Dyadic) * half ^ 12),
        ((-837 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word20Step19 :
    word20Chunk19.foldl (fun acc a => a.applyPacked acc)
      word20State19 = word20State20 := by decide +kernel

private def word20Chunk20 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State21 : PackedMat2 :=
    ⟨⟨⟨((2013 : Dyadic) * half ^ 12),
        ((3401 : Dyadic) * half ^ 15)⟩,
       ⟨((9247 : Dyadic) * half ^ 14),
        ((3367 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((2823 : Dyadic) * half ^ 14),
        ((-10415 : Dyadic) * half ^ 15)⟩,
       ⟨((931 : Dyadic) * half ^ 12),
        ((-7819 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((649 : Dyadic) * half ^ 13),
        ((901 : Dyadic) * half ^ 15)⟩,
       ⟨((-9117 : Dyadic) * half ^ 14),
        ((6547 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((17 : Dyadic) * half ^ 14),
        ((-1195 : Dyadic) * half ^ 15)⟩,
       ⟨((-423 : Dyadic) * half ^ 11),
        ((-17299 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word20Step20 :
    word20Chunk20.foldl (fun acc a => a.applyPacked acc)
      word20State20 = word20State21 := by decide +kernel

private def word20Chunk21 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word20State22 : PackedMat2 :=
    ⟨⟨⟨((5653 : Dyadic) * half ^ 14),
        ((5393 : Dyadic) * half ^ 15)⟩,
       ⟨((4645 : Dyadic) * half ^ 13),
        ((277 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-3317 : Dyadic) * half ^ 14),
        ((10625 : Dyadic) * half ^ 15)⟩,
       ⟨((3931 : Dyadic) * half ^ 14),
        ((-579 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((-1361 : Dyadic) * half ^ 15),
        ((-307 : Dyadic) * half ^ 14)⟩,
       ⟨((-19889 : Dyadic) * half ^ 15),
        ((453 : Dyadic) * half ^ 11)⟩⟩,
     ⟨⟨((9825 : Dyadic) * half ^ 15),
        ((14943 : Dyadic) * half ^ 15)⟩,
       ⟨((961 : Dyadic) * half ^ 15),
        ((-3637 : Dyadic) * half ^ 15)⟩⟩⟩
private lemma word20Step21 :
    word20Chunk21.foldl (fun acc a => a.applyPacked acc)
      word20State21 = word20State22 := by decide +kernel

private def word20Chunk22 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word20State23 : PackedMat2 :=
    ⟨⟨⟨((-22291 : Dyadic) * half ^ 16),
        ((-24087 : Dyadic) * half ^ 16)⟩,
       ⟨((10413 : Dyadic) * half ^ 16),
        ((415 : Dyadic) * half ^ 12)⟩⟩,
     ⟨⟨((29967 : Dyadic) * half ^ 16),
        ((-201 : Dyadic) * half ^ 12)⟩,
       ⟨((-31715 : Dyadic) * half ^ 16),
        ((16071 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((29967 : Dyadic) * half ^ 16),
        ((-201 : Dyadic) * half ^ 12)⟩,
       ⟨((31715 : Dyadic) * half ^ 16),
        ((-16071 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((22291 : Dyadic) * half ^ 16),
        ((24087 : Dyadic) * half ^ 16)⟩,
       ⟨((10413 : Dyadic) * half ^ 16),
        ((415 : Dyadic) * half ^ 12)⟩⟩⟩
private lemma word20Step22 :
    word20Chunk22.foldl (fun acc a => a.applyPacked acc)
      word20State22 = word20State23 := by decide +kernel

private def word20Chunk23 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word20State24 : PackedMat2 :=
    ⟨⟨⟨((-15681 : Dyadic) * half ^ 17),
        ((-12471 : Dyadic) * half ^ 16)⟩,
       ⟨((-40379 : Dyadic) * half ^ 17),
        ((7709 : Dyadic) * half ^ 17)⟩⟩,
     ⟨⟨((4207 : Dyadic) * half ^ 17),
        ((79635 : Dyadic) * half ^ 17)⟩,
       ⟨((-20501 : Dyadic) * half ^ 17),
        ((5059 : Dyadic) * half ^ 15)⟩⟩,
     ⟨⟨((-99871 : Dyadic) * half ^ 17),
        ((8147 : Dyadic) * half ^ 17)⟩,
       ⟨((-59399 : Dyadic) * half ^ 17),
        ((-6177 : Dyadic) * half ^ 16)⟩⟩,
     ⟨⟨((-17233 : Dyadic) * half ^ 17),
        ((-14015 : Dyadic) * half ^ 16)⟩,
       ⟨((-32651 : Dyadic) * half ^ 17),
        ((12349 : Dyadic) * half ^ 17)⟩⟩⟩
private lemma word20Step23 :
    word20Chunk23.foldl (fun acc a => a.applyPacked acc)
      word20State23 = word20State24 := by decide +kernel

private def word20Chunk24 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State25 : PackedMat2 :=
    ⟨⟨⟨((-38231 : Dyadic) * half ^ 17),
        ((37729 : Dyadic) * half ^ 18)⟩,
       ⟨((-25967 : Dyadic) * half ^ 17),
        ((-73035 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((14615 : Dyadic) * half ^ 16),
        ((-115547 : Dyadic) * half ^ 18)⟩,
       ⟨((11491 : Dyadic) * half ^ 15),
        ((63601 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((14615 : Dyadic) * half ^ 16),
        ((-115547 : Dyadic) * half ^ 18)⟩,
       ⟨((-11491 : Dyadic) * half ^ 15),
        ((-63601 : Dyadic) * half ^ 18)⟩⟩,
     ⟨⟨((38231 : Dyadic) * half ^ 17),
        ((-37729 : Dyadic) * half ^ 18)⟩,
       ⟨((-25967 : Dyadic) * half ^ 17),
        ((-73035 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word20Step24 :
    word20Chunk24.foldl (fun acc a => a.applyPacked acc)
      word20State24 = word20State25 := by decide +kernel

private def word20Chunk25 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word20State26 : PackedMat2 :=
    ⟨⟨⟨((16047 : Dyadic) * half ^ 18),
        ((110167 : Dyadic) * half ^ 19)⟩,
       ⟨((-45175 : Dyadic) * half ^ 17),
        ((-138589 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-4185 : Dyadic) * half ^ 16),
        ((-30919 : Dyadic) * half ^ 19)⟩,
       ⟨((202999 : Dyadic) * half ^ 18),
        ((-72941 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((202999 : Dyadic) * half ^ 18),
        ((-72941 : Dyadic) * half ^ 19)⟩,
       ⟨((-4185 : Dyadic) * half ^ 16),
        ((-30919 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((45175 : Dyadic) * half ^ 17),
        ((138589 : Dyadic) * half ^ 19)⟩,
       ⟨((-16047 : Dyadic) * half ^ 18),
        ((-110167 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word20Step25 :
    word20Chunk25.foldl (fun acc a => a.applyPacked acc)
      word20State25 = word20State26 := by decide +kernel

private def word20Chunk26 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word20State27 : PackedMat2 :=
    ⟨⟨⟨((67791 : Dyadic) * half ^ 19),
        ((446947 : Dyadic) * half ^ 20)⟩,
       ⟨((-87687 : Dyadic) * half ^ 18),
        ((82199 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((45053 : Dyadic) * half ^ 16),
        ((-43971 : Dyadic) * half ^ 20)⟩,
       ⟨((339 : Dyadic) * half ^ 19),
        ((-103873 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((29951 : Dyadic) * half ^ 19),
        ((360085 : Dyadic) * half ^ 20)⟩,
       ⟨((36961 : Dyadic) * half ^ 18),
        ((-360763 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-91187 : Dyadic) * half ^ 18),
        ((-243165 : Dyadic) * half ^ 20)⟩,
       ⟨((264573 : Dyadic) * half ^ 19),
        ((-107583 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word20Step26 :
    word20Chunk26.foldl (fun acc a => a.applyPacked acc)
      word20State26 = word20State27 := by decide +kernel

private def word20Chunk27 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State28 : PackedMat2 :=
    ⟨⟨⟨((79977 : Dyadic) * half ^ 18),
        ((9263 : Dyadic) * half ^ 18)⟩,
       ⟨((145415 : Dyadic) * half ^ 18),
        ((-51799 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-256593 : Dyadic) * half ^ 19),
        ((66191 : Dyadic) * half ^ 19)⟩,
       ⟨((34421 : Dyadic) * half ^ 16),
        ((156541 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((34421 : Dyadic) * half ^ 16),
        ((156541 : Dyadic) * half ^ 20)⟩,
       ⟨((-256593 : Dyadic) * half ^ 19),
        ((66191 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((-145415 : Dyadic) * half ^ 18),
        ((51799 : Dyadic) * half ^ 20)⟩,
       ⟨((-79977 : Dyadic) * half ^ 18),
        ((-9263 : Dyadic) * half ^ 18)⟩⟩⟩
private lemma word20Step27 :
    word20Chunk27.foldl (fun acc a => a.applyPacked acc)
      word20State27 = word20State28 := by decide +kernel

private def word20Chunk28 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word20State29 : PackedMat2 :=
    ⟨⟨⟨((-531715 : Dyadic) * half ^ 21),
        ((-80127 : Dyadic) * half ^ 20)⟩,
       ⟨((-72613 : Dyadic) * half ^ 21),
        ((599937 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((-374823 : Dyadic) * half ^ 21),
        ((-538851 : Dyadic) * half ^ 21)⟩,
       ⟨((-214851 : Dyadic) * half ^ 21),
        ((566951 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((374823 : Dyadic) * half ^ 21),
        ((538851 : Dyadic) * half ^ 21)⟩,
       ⟨((-214851 : Dyadic) * half ^ 21),
        ((566951 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((-531715 : Dyadic) * half ^ 21),
        ((-80127 : Dyadic) * half ^ 20)⟩,
       ⟨((72613 : Dyadic) * half ^ 21),
        ((-599937 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word20Step28 :
    word20Chunk28.foldl (fun acc a => a.applyPacked acc)
      word20State28 = word20State29 := by decide +kernel

private def word20Chunk29 : List Letter := [.h, .t, .h, .s, .t, .h, .s, .t]
private def word20State30 : PackedMat2 :=
    ⟨⟨⟨((-311359 : Dyadic) * half ^ 21),
        ((-1670503 : Dyadic) * half ^ 22)⟩,
       ⟨((441505 : Dyadic) * half ^ 21),
        ((-1366769 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-2587 : Dyadic) * half ^ 15),
        ((-1348471 : Dyadic) * half ^ 22)⟩,
       ⟨((113773 : Dyadic) * half ^ 18),
        ((-153765 : Dyadic) * half ^ 22)⟩⟩,
     ⟨⟨((-597353 : Dyadic) * half ^ 21),
        ((-134469 : Dyadic) * half ^ 19)⟩,
       ⟨((375559 : Dyadic) * half ^ 20),
        ((-93077 : Dyadic) * half ^ 19)⟩⟩,
     ⟨⟨((151867 : Dyadic) * half ^ 21),
        ((23527 : Dyadic) * half ^ 17)⟩,
       ⟨((-379659 : Dyadic) * half ^ 19),
        ((65073 : Dyadic) * half ^ 21)⟩⟩⟩
private lemma word20Step29 :
    word20Chunk29.foldl (fun acc a => a.applyPacked acc)
      word20State29 = word20State30 := by decide +kernel

private def word20Chunk30 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word20State31 : PackedMat2 :=
    ⟨⟨⟨((-2709361 : Dyadic) * half ^ 22),
        ((-331701 : Dyadic) * half ^ 23)⟩,
       ⟨((-463505 : Dyadic) * half ^ 21),
        ((-1532109 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-526697 : Dyadic) * half ^ 20),
        ((575493 : Dyadic) * half ^ 23)⟩,
       ⟨((-1837969 : Dyadic) * half ^ 22),
        ((602043 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-1837969 : Dyadic) * half ^ 22),
        ((602043 : Dyadic) * half ^ 23)⟩,
       ⟨((-526697 : Dyadic) * half ^ 20),
        ((575493 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((463505 : Dyadic) * half ^ 21),
        ((1532109 : Dyadic) * half ^ 23)⟩,
       ⟨((2709361 : Dyadic) * half ^ 22),
        ((331701 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word20Step30 :
    word20Chunk30.foldl (fun acc a => a.applyPacked acc)
      word20State30 = word20State31 := by decide +kernel

private def word20Chunk31 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word20State32 : PackedMat2 :=
    ⟨⟨⟨((-5094607 : Dyadic) * half ^ 23),
        ((3891069 : Dyadic) * half ^ 24)⟩,
       ⟨((-1372217 : Dyadic) * half ^ 22),
        ((-7024619 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-222471 : Dyadic) * half ^ 21),
        ((622731 : Dyadic) * half ^ 24)⟩,
       ⟨((-1865371 : Dyadic) * half ^ 23),
        ((-589171 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((605951 : Dyadic) * half ^ 23),
        ((975487 : Dyadic) * half ^ 24)⟩,
       ⟨((-4195 : Dyadic) * half ^ 21),
        ((2755255 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-1364461 : Dyadic) * half ^ 21),
        ((2350173 : Dyadic) * half ^ 24)⟩,
       ⟨((-1566775 : Dyadic) * half ^ 23),
        ((-7839041 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word20Step31 :
    word20Chunk31.foldl (fun acc a => a.applyPacked acc)
      word20State31 = word20State32 := by decide +kernel

private def word20Chunk32 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word20State33 : PackedMat2 :=
    ⟨⟨⟨((4250437 : Dyadic) * half ^ 23),
        ((-40241 : Dyadic) * half ^ 19)⟩,
       ⟨((-5614671 : Dyadic) * half ^ 23),
        ((-1110265 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-64083 : Dyadic) * half ^ 22),
        ((-513451 : Dyadic) * half ^ 21)⟩,
       ⟨((-3286831 : Dyadic) * half ^ 23),
        ((391529 : Dyadic) * half ^ 24)⟩⟩,
     ⟨⟨((-3286831 : Dyadic) * half ^ 23),
        ((391529 : Dyadic) * half ^ 24)⟩,
       ⟨((-64083 : Dyadic) * half ^ 22),
        ((-513451 : Dyadic) * half ^ 21)⟩⟩,
     ⟨⟨((5614671 : Dyadic) * half ^ 23),
        ((1110265 : Dyadic) * half ^ 24)⟩,
       ⟨((-4250437 : Dyadic) * half ^ 23),
        ((40241 : Dyadic) * half ^ 19)⟩⟩⟩
private lemma word20Step32 :
    word20Chunk32.foldl (fun acc a => a.applyPacked acc)
      word20State32 = word20State33 := by decide +kernel

private def word20Chunk33 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word20State34 : PackedMat2 :=
    ⟨⟨⟨((17588571 : Dyadic) * half ^ 25),
        ((2565927 : Dyadic) * half ^ 25)⟩,
       ⟨((-9124683 : Dyadic) * half ^ 25),
        ((-2967889 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((11102125 : Dyadic) * half ^ 25),
        ((-4600923 : Dyadic) * half ^ 24)⟩,
       ⟨((8898485 : Dyadic) * half ^ 25),
        ((-5764479 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((-11102125 : Dyadic) * half ^ 25),
        ((4600923 : Dyadic) * half ^ 24)⟩,
       ⟨((8898485 : Dyadic) * half ^ 25),
        ((-5764479 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((17588571 : Dyadic) * half ^ 25),
        ((2565927 : Dyadic) * half ^ 25)⟩,
       ⟨((9124683 : Dyadic) * half ^ 25),
        ((2967889 : Dyadic) * half ^ 23)⟩⟩⟩
private lemma word20Step33 :
    word20Chunk33.foldl (fun acc a => a.applyPacked acc)
      word20State33 = word20State34 := by decide +kernel

private def word20Chunk34 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .t]
private def word20State35 : PackedMat2 :=
    ⟨⟨⟨((38641009 : Dyadic) * half ^ 26),
        ((9433775 : Dyadic) * half ^ 26)⟩,
       ⟨((-15860503 : Dyadic) * half ^ 26),
        ((43337 : Dyadic) * half ^ 20)⟩⟩,
     ⟨⟨((28249971 : Dyadic) * half ^ 26),
        ((2591221 : Dyadic) * half ^ 25)⟩,
       ⟨((-17630379 : Dyadic) * half ^ 26),
        ((26485207 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((28249971 : Dyadic) * half ^ 26),
        ((2591221 : Dyadic) * half ^ 25)⟩,
       ⟨((17630379 : Dyadic) * half ^ 26),
        ((-26485207 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-38641009 : Dyadic) * half ^ 26),
        ((-9433775 : Dyadic) * half ^ 26)⟩,
       ⟨((-15860503 : Dyadic) * half ^ 26),
        ((43337 : Dyadic) * half ^ 20)⟩⟩⟩
private lemma word20Step34 :
    word20Chunk34.foldl (fun acc a => a.applyPacked acc)
      word20State34 = word20State35 := by decide +kernel

private def word20Chunk35 : List Letter := [.h, .t, .h, .s, .t, .h, .t, .h]
private def word20State36 : PackedMat2 :=
    ⟨⟨⟨((112543579 : Dyadic) * half ^ 27),
        ((613779 : Dyadic) * half ^ 26)⟩,
       ⟨((4836171 : Dyadic) * half ^ 27),
        ((26488905 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((-5319385 : Dyadic) * half ^ 27),
        ((7946397 : Dyadic) * half ^ 27)⟩,
       ⟨((-5181663 : Dyadic) * half ^ 27),
        ((2701699 : Dyadic) * half ^ 23)⟩⟩,
     ⟨⟨((-51173581 : Dyadic) * half ^ 27),
        ((1312631 : Dyadic) * half ^ 25)⟩,
       ⟨((35280787 : Dyadic) * half ^ 27),
        ((68861 : Dyadic) * half ^ 27)⟩⟩,
     ⟨⟨((27716463 : Dyadic) * half ^ 27),
        ((58689875 : Dyadic) * half ^ 27)⟩,
       ⟨((-25261347 : Dyadic) * half ^ 27),
        ((6731713 : Dyadic) * half ^ 24)⟩⟩⟩
private lemma word20Step35 :
    word20Chunk35.foldl (fun acc a => a.applyPacked acc)
      word20State35 = word20State36 := by decide +kernel

private def word20Chunk36 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word20State37 : PackedMat2 :=
    ⟨⟨⟨((-31037037 : Dyadic) * half ^ 28),
        ((42297891 : Dyadic) * half ^ 28)⟩,
       ⟨((-32787219 : Dyadic) * half ^ 28),
        ((18486553 : Dyadic) * half ^ 25)⟩⟩,
     ⟨⟨((1420285 : Dyadic) * half ^ 28),
        ((22192539 : Dyadic) * half ^ 27)⟩,
       ⟨((114270101 : Dyadic) * half ^ 28),
        ((53371293 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((97756371 : Dyadic) * half ^ 28),
        ((57845193 : Dyadic) * half ^ 28)⟩,
       ⟨((-8986215 : Dyadic) * half ^ 28),
        ((-14106227 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((-190190315 : Dyadic) * half ^ 28),
        ((498627 : Dyadic) * half ^ 22)⟩,
       ⟨((105594533 : Dyadic) * half ^ 28),
        ((-875091 : Dyadic) * half ^ 28)⟩⟩⟩
private lemma word20Step36 :
    word20Chunk36.foldl (fun acc a => a.applyPacked acc)
      word20State36 = word20State37 := by decide +kernel

private def word20Chunk37 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word20State38 : PackedMat2 :=
    ⟨⟨⟨((115826551 : Dyadic) * half ^ 28),
        ((-15694771 : Dyadic) * half ^ 26)⟩,
       ⟨((8317753 : Dyadic) * half ^ 24),
        ((26947875 : Dyadic) * half ^ 28)⟩⟩,
     ⟨⟨((3643637 : Dyadic) * half ^ 28),
        ((-24980429 : Dyadic) * half ^ 26)⟩,
       ⟨((34799977 : Dyadic) * half ^ 27),
        ((14544661 : Dyadic) * half ^ 26)⟩⟩,
     ⟨⟨((19762545 : Dyadic) * half ^ 25),
        ((65956317 : Dyadic) * half ^ 29)⟩,
       ⟨((-1304471 : Dyadic) * half ^ 23),
        ((73243591 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((-89726959 : Dyadic) * half ^ 28),
        ((-17257497 : Dyadic) * half ^ 29)⟩,
       ⟨((35831209 : Dyadic) * half ^ 28),
        ((-248910599 : Dyadic) * half ^ 29)⟩⟩⟩
private lemma word20Step37 :
    word20Chunk37.foldl (fun acc a => a.applyPacked acc)
      word20State37 = word20State38 := by decide +kernel

private def word20Chunk38 : List Letter := [.h, .s, .t, .h, .t, .h, .s, .t]
private def word20State39 : PackedMat2 :=
    ⟨⟨⟨((-3141933 : Dyadic) * half ^ 24),
        ((243713669 : Dyadic) * half ^ 30)⟩,
       ⟨((127979229 : Dyadic) * half ^ 29),
        ((213853519 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-359170345 : Dyadic) * half ^ 29),
        ((-126327511 : Dyadic) * half ^ 30)⟩,
       ⟨((77916067 : Dyadic) * half ^ 28),
        ((-309554123 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-77916067 : Dyadic) * half ^ 28),
        ((309554123 : Dyadic) * half ^ 30)⟩,
       ⟨((359170345 : Dyadic) * half ^ 29),
        ((126327511 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((127979229 : Dyadic) * half ^ 29),
        ((213853519 : Dyadic) * half ^ 30)⟩,
       ⟨((-3141933 : Dyadic) * half ^ 24),
        ((243713669 : Dyadic) * half ^ 30)⟩⟩⟩
private lemma word20Step38 :
    word20Chunk38.foldl (fun acc a => a.applyPacked acc)
      word20State38 = word20State39 := by decide +kernel

private def word20Chunk39 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word20State40 : PackedMat2 :=
    ⟨⟨⟨((178168169 : Dyadic) * half ^ 30),
        ((-65608037 : Dyadic) * half ^ 31)⟩,
       ⟨((392782983 : Dyadic) * half ^ 29),
        ((179522481 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((66341677 : Dyadic) * half ^ 28),
        ((-532012607 : Dyadic) * half ^ 31)⟩,
       ⟨((-16007041 : Dyadic) * half ^ 30),
        ((-739733643 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-51930259 : Dyadic) * half ^ 29),
        ((-281373749 : Dyadic) * half ^ 31)⟩,
       ⟨((-635873125 : Dyadic) * half ^ 30),
        ((249359667 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-122565259 : Dyadic) * half ^ 30),
        ((-607397797 : Dyadic) * half ^ 31)⟩,
       ⟨((-28478611 : Dyadic) * half ^ 29),
        ((-963734135 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word20Step39 :
    word20Chunk39.foldl (fun acc a => a.applyPacked acc)
      word20State39 = word20State40 := by decide +kernel

private def word20Chunk40 : List Letter := [.t, .h, .s, .t, .h, .s, .t, .h]
private def word20State41 : PackedMat2 :=
    ⟨⟨⟨((-148769989 : Dyadic) * half ^ 28),
        ((-501342995 : Dyadic) * half ^ 31)⟩,
       ⟨((-296578425 : Dyadic) * half ^ 29),
        ((241990821 : Dyadic) * half ^ 30)⟩⟩,
     ⟨⟨((-33508051 : Dyadic) * half ^ 28),
        ((472861101 : Dyadic) * half ^ 31)⟩,
       ⟨((-205728299 : Dyadic) * half ^ 30),
        ((-63331679 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((205728299 : Dyadic) * half ^ 30),
        ((63331679 : Dyadic) * half ^ 29)⟩,
       ⟨((33508051 : Dyadic) * half ^ 28),
        ((-472861101 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-296578425 : Dyadic) * half ^ 29),
        ((241990821 : Dyadic) * half ^ 30)⟩,
       ⟨((-148769989 : Dyadic) * half ^ 28),
        ((-501342995 : Dyadic) * half ^ 31)⟩⟩⟩
private lemma word20Step40 :
    word20Chunk40.foldl (fun acc a => a.applyPacked acc)
      word20State40 = word20State41 := by decide +kernel

private def word20Chunk41 : List Letter := [.s, .t, .h, .s, .t, .h, .t, .h]
private def word20State42 : PackedMat2 :=
    ⟨⟨⟨((403162095 : Dyadic) * half ^ 32),
        ((-2013902057 : Dyadic) * half ^ 32)⟩,
       ⟨((503991189 : Dyadic) * half ^ 32),
        ((-201995075 : Dyadic) * half ^ 29)⟩⟩,
     ⟨⟨((1374540153 : Dyadic) * half ^ 32),
        ((586749557 : Dyadic) * half ^ 31)⟩,
       ⟨((210606797 : Dyadic) * half ^ 32),
        ((63327609 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((1236826723 : Dyadic) * half ^ 32),
        ((792573475 : Dyadic) * half ^ 32)⟩,
       ⟨((1110171505 : Dyadic) * half ^ 32),
        ((290983339 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((3629862657 : Dyadic) * half ^ 32),
        ((-226788321 : Dyadic) * half ^ 31)⟩,
       ⟨((397941457 : Dyadic) * half ^ 32),
        ((50414547 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word20Step41 :
    word20Chunk41.foldl (fun acc a => a.applyPacked acc)
      word20State41 = word20State42 := by decide +kernel

private def word20Chunk42 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .s]
private def word20State43 : PackedMat2 :=
    ⟨⟨⟨((-1185600525 : Dyadic) * half ^ 31),
        ((977897543 : Dyadic) * half ^ 32)⟩,
       ⟨((-2101649629 : Dyadic) * half ^ 32),
        ((-1341704991 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((660095655 : Dyadic) * half ^ 31),
        ((-38093507 : Dyadic) * half ^ 30)⟩,
       ⟨((952178733 : Dyadic) * half ^ 32),
        ((-314898073 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-660095655 : Dyadic) * half ^ 31),
        ((38093507 : Dyadic) * half ^ 30)⟩,
       ⟨((952178733 : Dyadic) * half ^ 32),
        ((-314898073 : Dyadic) * half ^ 32)⟩⟩,
     ⟨⟨((-1185600525 : Dyadic) * half ^ 31),
        ((977897543 : Dyadic) * half ^ 32)⟩,
       ⟨((2101649629 : Dyadic) * half ^ 32),
        ((1341704991 : Dyadic) * half ^ 32)⟩⟩⟩
private lemma word20Step42 :
    word20Chunk42.foldl (fun acc a => a.applyPacked acc)
      word20State42 = word20State43 := by decide +kernel

private def word20Chunk43 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word20State44 : PackedMat2 :=
    ⟨⟨⟨((282794801 : Dyadic) * half ^ 29),
        ((-4331362161 : Dyadic) * half ^ 34)⟩,
       ⟨((-5217135077 : Dyadic) * half ^ 33),
        ((-2615516749 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1620734237 : Dyadic) * half ^ 33),
        ((-1202671913 : Dyadic) * half ^ 34)⟩,
       ⟨((1504998849 : Dyadic) * half ^ 32),
        ((1330057989 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-1504998849 : Dyadic) * half ^ 32),
        ((-1330057989 : Dyadic) * half ^ 34)⟩,
       ⟨((1620734237 : Dyadic) * half ^ 33),
        ((1202671913 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-5217135077 : Dyadic) * half ^ 33),
        ((-2615516749 : Dyadic) * half ^ 34)⟩,
       ⟨((282794801 : Dyadic) * half ^ 29),
        ((-4331362161 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word20Step43 :
    word20Chunk43.foldl (fun acc a => a.applyPacked acc)
      word20State43 = word20State44 := by decide +kernel

private def word20Chunk44 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .s]
private def word20State45 : PackedMat2 :=
    ⟨⟨⟨((-229197483 : Dyadic) * half ^ 34),
        ((7649733671 : Dyadic) * half ^ 34)⟩,
       ⟨((7534777389 : Dyadic) * half ^ 34),
        ((1111234131 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((-6129067867 : Dyadic) * half ^ 34),
        ((-340658517 : Dyadic) * half ^ 31)⟩,
       ⟨((-5424961603 : Dyadic) * half ^ 34),
        ((2149596363 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-5424961603 : Dyadic) * half ^ 34),
        ((2149596363 : Dyadic) * half ^ 33)⟩,
       ⟨((-6129067867 : Dyadic) * half ^ 34),
        ((-340658517 : Dyadic) * half ^ 31)⟩⟩,
     ⟨⟨((-7534777389 : Dyadic) * half ^ 34),
        ((-1111234131 : Dyadic) * half ^ 34)⟩,
       ⟨((229197483 : Dyadic) * half ^ 34),
        ((-7649733671 : Dyadic) * half ^ 34)⟩⟩⟩
private lemma word20Step44 :
    word20Chunk44.foldl (fun acc a => a.applyPacked acc)
      word20State44 = word20State45 := by decide +kernel

private def word20Chunk45 : List Letter := [.t, .h, .t, .h, .s, .t, .h, .t]
private def word20State46 : PackedMat2 :=
    ⟨⟨⟨((740229091 : Dyadic) * half ^ 35),
        ((-846242373 : Dyadic) * half ^ 34)⟩,
       ⟨((419346189 : Dyadic) * half ^ 35),
        ((20961525795 : Dyadic) * half ^ 35)⟩⟩,
     ⟨⟨((-6564074209 : Dyadic) * half ^ 35),
        ((-6546273157 : Dyadic) * half ^ 35)⟩,
       ⟨((11230285387 : Dyadic) * half ^ 35),
        ((-2248719893 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((6564074209 : Dyadic) * half ^ 35),
        ((6546273157 : Dyadic) * half ^ 35)⟩,
       ⟨((11230285387 : Dyadic) * half ^ 35),
        ((-2248719893 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((740229091 : Dyadic) * half ^ 35),
        ((-846242373 : Dyadic) * half ^ 34)⟩,
       ⟨((-419346189 : Dyadic) * half ^ 35),
        ((-20961525795 : Dyadic) * half ^ 35)⟩⟩⟩
private lemma word20Step45 :
    word20Chunk45.foldl (fun acc a => a.applyPacked acc)
      word20State45 = word20State46 := by decide +kernel

private def word20Chunk46 : List Letter := [.h, .s, .t, .h, .t, .h, .t, .h]
private def word20State47 : PackedMat2 :=
    ⟨⟨⟨((6105427743 : Dyadic) * half ^ 36),
        ((11398195631 : Dyadic) * half ^ 36)⟩,
       ⟨((-1968427023 : Dyadic) * half ^ 36),
        ((5171896459 : Dyadic) * half ^ 34)⟩⟩,
     ⟨⟨((24567543129 : Dyadic) * half ^ 36),
        ((-10757051125 : Dyadic) * half ^ 35)⟩,
       ⟨((-41844417335 : Dyadic) * half ^ 36),
        ((-11941372587 : Dyadic) * half ^ 36)⟩⟩,
     ⟨⟨((-33455474837 : Dyadic) * half ^ 36),
        ((-8638437103 : Dyadic) * half ^ 36)⟩,
       ⟨((-9572729663 : Dyadic) * half ^ 36),
        ((4150747529 : Dyadic) * half ^ 33)⟩⟩,
     ⟨⟨((-32085781467 : Dyadic) * half ^ 36),
        ((-258562545 : Dyadic) * half ^ 33)⟩,
       ⟨((9289390205 : Dyadic) * half ^ 36),
        ((-4036927383 : Dyadic) * half ^ 36)⟩⟩⟩
private lemma word20Step46 :
    word20Chunk46.foldl (fun acc a => a.applyPacked acc)
      word20State46 = word20State47 := by decide +kernel

private def word20Chunk47 : List Letter := [.s, .t, .h, .t, .h, .s, .t, .h]
private def word20State48 : PackedMat2 :=
    ⟨⟨⟨((24666180707 : Dyadic) * half ^ 36),
        ((-36096260343 : Dyadic) * half ^ 37)⟩,
       ⟨((44662508375 : Dyadic) * half ^ 36),
        ((21371141195 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((-1822303727 : Dyadic) * half ^ 35),
        ((25110720085 : Dyadic) * half ^ 37)⟩,
       ⟨((-320907267 : Dyadic) * half ^ 35),
        ((-42670933749 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((1822303727 : Dyadic) * half ^ 35),
        ((-25110720085 : Dyadic) * half ^ 37)⟩,
       ⟨((-320907267 : Dyadic) * half ^ 35),
        ((-42670933749 : Dyadic) * half ^ 37)⟩⟩,
     ⟨⟨((24666180707 : Dyadic) * half ^ 36),
        ((-36096260343 : Dyadic) * half ^ 37)⟩,
       ⟨((-44662508375 : Dyadic) * half ^ 36),
        ((-21371141195 : Dyadic) * half ^ 37)⟩⟩⟩
private lemma word20Step47 :
    word20Chunk47.foldl (fun acc a => a.applyPacked acc)
      word20State47 = word20State48 := by decide +kernel

private def word20Chunk48 : List Letter := [.t, .h, .t, .h, .t, .h, .s, .t]
private def word20State49 : PackedMat2 :=
    ⟨⟨⟨((-6679268177 : Dyadic) * half ^ 35),
        ((54532221293 : Dyadic) * half ^ 38)⟩,
       ⟨((101706997305 : Dyadic) * half ^ 37),
        ((-19839511565 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((32879608623 : Dyadic) * half ^ 37),
        ((84866373041 : Dyadic) * half ^ 38)⟩,
       ⟨((-6755534099 : Dyadic) * half ^ 36),
        ((-50653681087 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((6755534099 : Dyadic) * half ^ 36),
        ((50653681087 : Dyadic) * half ^ 38)⟩,
       ⟨((-32879608623 : Dyadic) * half ^ 37),
        ((-84866373041 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((101706997305 : Dyadic) * half ^ 37),
        ((-19839511565 : Dyadic) * half ^ 38)⟩,
       ⟨((-6679268177 : Dyadic) * half ^ 35),
        ((54532221293 : Dyadic) * half ^ 38)⟩⟩⟩
private lemma word20Step48 :
    word20Chunk48.foldl (fun acc a => a.applyPacked acc)
      word20State48 = word20State49 := by decide +kernel

private def word20Chunk49 : List Letter := [.h, .t, .h, .t, .h, .t, .h, .s]
private def word20State50 : PackedMat2 :=
    ⟨⟨⟨((100243154841 : Dyadic) * half ^ 38),
        ((-216379990233 : Dyadic) * half ^ 39)⟩,
       ⟨((21597987793 : Dyadic) * half ^ 37),
        ((-89552650227 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((8146646521 : Dyadic) * half ^ 34),
        ((196061443165 : Dyadic) * half ^ 39)⟩,
       ⟨((-601730273 : Dyadic) * half ^ 38),
        ((-5043084295 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-50276131865 : Dyadic) * half ^ 37),
        ((-130948074609 : Dyadic) * half ^ 39)⟩,
       ⟨((95509179435 : Dyadic) * half ^ 38),
        ((129744614063 : Dyadic) * half ^ 39)⟩⟩,
     ⟨⟨((-63413670003 : Dyadic) * half ^ 38),
        ((57047179255 : Dyadic) * half ^ 39)⟩,
       ⟨((76483160115 : Dyadic) * half ^ 37),
        ((-143439130427 : Dyadic) * half ^ 39)⟩⟩⟩
private lemma word20Step49 :
    word20Chunk49.foldl (fun acc a => a.applyPacked acc)
      word20State49 = word20State50 := by decide +kernel

private def word20Chunk50 : List Letter := [.t, .h, .t, .h, .t, .h, .t, .h]
private def word20State51 : PackedMat2 :=
    ⟨⟨⟨((-110422538563 : Dyadic) * half ^ 39),
        ((-370013724627 : Dyadic) * half ^ 40)⟩,
       ⟨((-113664570045 : Dyadic) * half ^ 38),
        ((402003404433 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((22069926855 : Dyadic) * half ^ 37),
        ((263888469155 : Dyadic) * half ^ 40)⟩,
       ⟨((101122623613 : Dyadic) * half ^ 39),
        ((269309039313 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((-2710285079 : Dyadic) * half ^ 39),
        ((-12842916193 : Dyadic) * half ^ 40)⟩,
       ⟨((-133299377117 : Dyadic) * half ^ 38),
        ((-189402331033 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((193004282265 : Dyadic) * half ^ 38),
        ((-116906601527 : Dyadic) * half ^ 40)⟩,
       ⟨((15994839903 : Dyadic) * half ^ 39),
        ((-337751678653 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word20Step50 :
    word20Chunk50.foldl (fun acc a => a.applyPacked acc)
      word20State50 = word20State51 := by decide +kernel

private def word20Chunk51 : List Letter := [.t, .h, .s, .t, .h, .t, .h, .t]
private def word20State52 : PackedMat2 :=
    ⟨⟨⟨((-54404877117 : Dyadic) * half ^ 40),
        ((-89740003101 : Dyadic) * half ^ 39)⟩,
       ⟨((190458242257 : Dyadic) * half ^ 40),
        ((-136747630515 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((273188384105 : Dyadic) * half ^ 40),
        ((138632050077 : Dyadic) * half ^ 40)⟩,
       ⟨((130259606643 : Dyadic) * half ^ 40),
        ((434068560407 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((143175152621 : Dyadic) * half ^ 38),
        ((100861997687 : Dyadic) * half ^ 39)⟩,
       ⟨((-147718255165 : Dyadic) * half ^ 39),
        ((71464388731 : Dyadic) * half ^ 40)⟩⟩,
     ⟨⟨((363235264131 : Dyadic) * half ^ 39),
        ((-34013341285 : Dyadic) * half ^ 39)⟩,
       ⟨((-183755257929 : Dyadic) * half ^ 39),
        ((122431559687 : Dyadic) * half ^ 40)⟩⟩⟩
private lemma word20Step51 :
    word20Chunk51.foldl (fun acc a => a.applyPacked acc)
      word20State51 = word20State52 := by decide +kernel

private def word20Chunk52 : List Letter := [.h, .s, .t, .h, .s, .t, .h, .t]
private def word20State53 : PackedMat2 :=
    ⟨⟨⟨((504645534823 : Dyadic) * half ^ 41),
        ((185667754663 : Dyadic) * half ^ 39)⟩,
       ⟨((-1101593254279 : Dyadic) * half ^ 41),
        ((1468638021 : Dyadic) * half ^ 41)⟩⟩,
     ⟨⟨((-644479623961 : Dyadic) * half ^ 41),
        ((-321756215551 : Dyadic) * half ^ 41)⟩,
       ⟨((906087630203 : Dyadic) * half ^ 41),
        ((-80087879627 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((644479623961 : Dyadic) * half ^ 41),
        ((321756215551 : Dyadic) * half ^ 41)⟩,
       ⟨((906087630203 : Dyadic) * half ^ 41),
        ((-80087879627 : Dyadic) * half ^ 38)⟩⟩,
     ⟨⟨((504645534823 : Dyadic) * half ^ 41),
        ((185667754663 : Dyadic) * half ^ 39)⟩,
       ⟨((1101593254279 : Dyadic) * half ^ 41),
        ((-1468638021 : Dyadic) * half ^ 41)⟩⟩⟩
private lemma word20Step52 :
    word20Chunk52.foldl (fun acc a => a.applyPacked acc)
      word20State52 = word20State53 := by decide +kernel

private def word20Chunk53 : List Letter := [.h, .s, .t, .h, .t, .h]
private def word20State54 : PackedMat2 :=
    ⟨⟨⟨((403926864443 : Dyadic) * half ^ 39),
        ((824933112353 : Dyadic) * half ^ 42)⟩,
       ⟨((353417610267 : Dyadic) * half ^ 40),
        ((-999625272643 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((-522477263241 : Dyadic) * half ^ 41),
        ((738894431707 : Dyadic) * half ^ 42)⟩,
       ⟨((-412146221857 : Dyadic) * half ^ 41),
        ((582862776631 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((522477263241 : Dyadic) * half ^ 41),
        ((-738894431707 : Dyadic) * half ^ 42)⟩,
       ⟨((-412146221857 : Dyadic) * half ^ 41),
        ((582862776631 : Dyadic) * half ^ 42)⟩⟩,
     ⟨⟨((403926864443 : Dyadic) * half ^ 39),
        ((824933112353 : Dyadic) * half ^ 42)⟩,
       ⟨((-353417610267 : Dyadic) * half ^ 40),
        ((999625272643 : Dyadic) * half ^ 42)⟩⟩⟩
private lemma word20Step53 :
    word20Chunk53.foldl (fun acc a => a.applyPacked acc)
      word20State53 = word20State54 := by decide +kernel

set_option maxRecDepth 10000 in
public lemma word20_check : check word20 20 (1 / 2 ^ 50) = true := by
  have he : evalRingPacked word20 = word20State54.toMatrix := by
    unfold evalRingPacked
    change ((
      word20Chunk0 ++ word20Chunk1 ++ word20Chunk2 ++ word20Chunk3 ++
      word20Chunk4 ++ word20Chunk5 ++ word20Chunk6 ++ word20Chunk7 ++
      word20Chunk8 ++ word20Chunk9 ++ word20Chunk10 ++ word20Chunk11 ++
      word20Chunk12 ++ word20Chunk13 ++ word20Chunk14 ++ word20Chunk15 ++
      word20Chunk16 ++ word20Chunk17 ++ word20Chunk18 ++ word20Chunk19 ++
      word20Chunk20 ++ word20Chunk21 ++ word20Chunk22 ++ word20Chunk23 ++
      word20Chunk24 ++ word20Chunk25 ++ word20Chunk26 ++ word20Chunk27 ++
      word20Chunk28 ++ word20Chunk29 ++ word20Chunk30 ++ word20Chunk31 ++
      word20Chunk32 ++ word20Chunk33 ++ word20Chunk34 ++ word20Chunk35 ++
      word20Chunk36 ++ word20Chunk37 ++ word20Chunk38 ++ word20Chunk39 ++
      word20Chunk40 ++ word20Chunk41 ++ word20Chunk42 ++ word20Chunk43 ++
      word20Chunk44 ++ word20Chunk45 ++ word20Chunk46 ++ word20Chunk47 ++
      word20Chunk48 ++ word20Chunk49 ++ word20Chunk50 ++ word20Chunk51 ++
      word20Chunk52 ++ word20Chunk53
      ).foldl (fun acc a => a.applyPacked acc) PackedMat2.identity).toMatrix = _
    simp only [List.foldl_append,
      word20Step0, word20Step1, word20Step2, word20Step3, word20Step4,
      word20Step5, word20Step6, word20Step7, word20Step8, word20Step9,
      word20Step10, word20Step11, word20Step12, word20Step13, word20Step14,
      word20Step15, word20Step16, word20Step17, word20Step18, word20Step19,
      word20Step20, word20Step21, word20Step22, word20Step23, word20Step24,
      word20Step25, word20Step26, word20Step27, word20Step28, word20Step29,
      word20Step30, word20Step31, word20Step32, word20Step33, word20Step34,
      word20Step35, word20Step36, word20Step37, word20Step38, word20Step39,
      word20Step40, word20Step41, word20Step42, word20Step43, word20Step44,
      word20Step45, word20Step46, word20Step47, word20Step48, word20Step49,
      word20Step50, word20Step51, word20Step52, word20Step53]
  unfold check
  rw [he]
  decide +kernel

end QuantumAlg.CliffordT

end
