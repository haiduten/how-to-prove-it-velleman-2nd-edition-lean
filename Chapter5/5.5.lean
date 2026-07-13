import HTPILib.Chap5
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Function
namespace HTPI.Exercises


theorem Example_5_5_2_1 {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∩ X) ⊆ image f W ∩ image f X := by
  intro x hx
  constructor
  ·
    have ⟨y, hy, hy'⟩ := hx
    exists y
    constructor
    · exact hy.1
    · exact hy'
  ·
    have ⟨y, hy, hy'⟩ := hx
    exists y
    constructor
    · exact hy.2
    · exact hy'

theorem Theorem_5_5_2_2 {A B : Type} (f : A → B) (W X : Set A)
    (h1 : one_to_one f) : image f (W ∩ X) = image f W ∩ image f X := by
  ext x
  constructor
  · intro hx
    constructor
    ·
      have ⟨y, hy, hy'⟩ := hx
      exists y
      constructor
      · exact hy.1
      · exact hy'
    ·
      have ⟨y, hy, hy'⟩ := hx
      exists y
      constructor
      · exact hy.2
      · exact hy'
  ·
    intro ⟨hx, hx'⟩
    have ⟨y, hy, hy'⟩ := hx
    have ⟨z, hz, hz'⟩ := hx'
    have hfinal : y = z := by
      apply h1
      rw[hy', hz']
    exists y
    constructor
    ·
      constructor
      ·
        exact hy
      ·
        rw[hfinal]
        exact hz
    ·
      rw[hfinal]
      exact hz'


theorem Exercise_5_5_1_a {A B : Type} (f : A → B) (W X : Set A) :
    image f (W ∪ X) = image f W ∪ image f X := by
  ext x
  constructor
  ·
    intro hx
    have ⟨y, hy, h'⟩ := hx
    cases hy
    case inl hy =>
      left
      exists y
    case inr hy =>
      right
      exists y
  ·
    intro hx
    simp at hx
    cases hx
    case inl hx =>
      have ⟨y, hy, hy'⟩ := hx
      exists y
      constructor
      ·
        left
        exact hy
      · exact hy'
    case inr hx =>
      have ⟨y, hy, hy'⟩ := hx
      exists y
      constructor
      ·
        right
        exact hy
      ·
        exact hy'

/-
Exercise_5_5_1_b
Counter example:
A = {a, b}
B = {1}
f = {(a, 1), (b, 1)}
W = {a}
X = {b}
f (W \ X) = {1}
f (W) \ f(x) = ∅
-/

/-
Exercise_5_5_1_c
Counter example:
A = {a, b}
B = {1}
f = {(a, 1), (b, 1)}
W = {a}
X = {b}
f (W \ X) = {1}
f (W) ⊆ f(X) is true
but W ⊄ X
-/

theorem Exercise_5_5_2_a {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f (Y ∩ Z) = inverse_image f Y ∩ inverse_image f Z := by
  ext x
  dsimp[inverse_image]
  simp

theorem Exercise_5_5_2_b {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f (Y ∪ Z) = inverse_image f Y ∪ inverse_image f Z := by
  ext x
  dsimp[inverse_image]
  simp

theorem Exercise_5_5_2_c {A B : Type} (f : A → B) (Y Z : Set B) :
    inverse_image f (Y \ Z) = inverse_image f Y \ inverse_image f Z := by
  ext x
  dsimp[inverse_image]
  simp

/-
Exercise_5_5_2_d
Counter example:
A = {a, b}
B = {1, 2, 3, 4}
f = {(a, 1), (b, 1)}
Y = {3}
Z = {4}
f⁻¹ (Y) = ∅
f⁻¹ (Z) = ∅
f⁻¹ (Y) ⊆ f⁻¹ (Z) but {3} ⊄ {4}
-/

/-
Exercise_5_5_3
Counter example:
A = {a, b}
B = {1, 2, 3, 4}
f = {(a, 1), (b, 1)}
X = {a}
f(X) = 1
f⁻¹(1) = {a, b}
{a} ≠ {a, b}
-/

/-
Exercise_5_5_4
Counter example:
A = {a, b}
B = {1, 2, 3}
f = {(a, 1), (b, 1)}
Y = {3}
f(f⁻¹(Y)) = ∅
∅ ≠ {3}
-/


theorem Exercise_5_5_5 {A : Type} (f : A → A) (C: Set A) :
    (closed f C ↔ image f C ⊆ C) ∧ (image f C ⊆ C ↔ C ⊆ inverse_image f C) := by
  constructor
  ·
    dsimp[closed, image]
    constructor
    ·
      intro h a ha
      simp at ha
      have ⟨c, hc, hc'⟩ := ha
      rw[← hc']
      apply h
      exact hc
    ·
      intro a c hc
      apply a
      simp
      exists c
  ·
    constructor
    ·
      dsimp[image, inverse_image]
      intro h c hc
      simp
      apply h
      simp
      exists c
    ·
      dsimp[inverse_image, image]
      intro h a ha
      simp at ha
      have ⟨c, hc, hc'⟩ := ha
      rw[← hc']
      apply h
      exact hc


theorem Exercise_5_5_6 {A B C: Type} (f : A → B) (g: B → C) (X: Set A) (Y: Set C):
  X ⊆ inverse_image f (inverse_image g Y) ↔ image g (image f X) ⊆ Y := by
  dsimp[inverse_image, image]
  constructor
  ·
    intro hX
    simp
    intro c hc
    simp at hc
    have ⟨x, hx, hx'⟩ := hc
    rw[← hx']
    apply hX
    exact hx
  ·
    intro h
    simp at h
    intro a ha
    simp
    apply h
    simp
    exists a

noncomputable section

open Classical


theorem Exercise_5_5_7 {A B: Type} [Inhabited A] (f: A → B) (hf: Function.Bijective f) (Y: Set B):
    let inverse : B → A := fun y : B => if h1 : ∃ x : A, f x = y then Classical.choose h1 else default
    inverse_image f Y = image (inverse) Y := by
  intro inverse
  ext a
  dsimp[inverse_image, image, inverse]
  constructor
  ·
    intro ha
    exists (f a)
    constructor
    · exact ha
    ·
      have q : ∃ (x : A), f x = f a := by
        exists a
      rw[dif_pos q]
      apply hf.1
      exact Classical.choose_spec q
  ·
    intro h
    have ⟨x, hx, hx'⟩ := h
    have q : ∃ (x_1 : A), f x_1 = x := by
      have ⟨t, ht⟩ := hf.2 x
      exists t
    rw[dif_pos q] at hx'
    have := Classical.choose_spec q
    rw[hx'] at this
    rw[this]
    exact hx
