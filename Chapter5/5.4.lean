import HTPILib.Chap5
import Mathlib.Data.Set.Operations
import Mathlib.Data.Set.Function
namespace HTPI.Exercises


/-
Example 5_4_2
1. C₁ yes. C₂ No
2. f Yes, g No
3. C₁ yes. C₂ No
-/

/-
Example 5_4_4
1. {a, b, c, d}
2. 0 + ℕ
-/

theorem Theorem_5_4_5 {A : Type} (f : A → A) (B : Set A) :
    ∃ (C : Set A), closure f B C := by
  set closedSets: Set (Set A) := {D : Set A | B ⊆ D ∧ closed f D}
  set glb: Set A := (⋂₀ closedSets)
  exists glb
  define
  constructor
  ·
    simp
    constructor
    ·
      intro b hb
      dsimp[glb, closedSets]
      intro T
      simp
      intro hBT hfT
      apply hBT
      exact hb
    ·
      define
      intro x hx
      dsimp[glb, closedSets] at *
      define at hx
      define
      intro T ⟨hT, hT'⟩
      apply hT'
      apply hx
      simp
      constructor
      · assumption
      · assumption
  ·
    intro T ⟨hT, hT'⟩
    dsimp[sub, glb, closedSets]
    define
    intro a ha
    apply ha
    constructor
    · exact hT
    · exact hT'

/-
  Example 5_4_7
  1. Yes, no

  2. Yes, no
-/

theorem Example_5_4_9 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := by
  set closedSets := {D : Set A | B ⊆ D ∧ closed2 f D}
  set glb: Set A := ⋂₀ closedSets
  exists glb
  define
  constructor
  · constructor
    ·
      intro b hb
      dsimp[glb, closedSets]
      simp
      intro T hBT _
      apply hBT
      exact hb
    ·
      dsimp[closed2]
      intro x hx y hy
      dsimp[glb, closedSets] at *
      simp at *
      intro T hBT hclosedFT
      apply hclosedFT
      exact hx T hBT hclosedFT
      exact hy T hBT hclosedFT
  ·
    intro T ⟨hT, hT'⟩
    dsimp[closed2] at *
    dsimp[sub, glb, closedSets]
    define
    intro a ha
    simp at ha
    apply ha
    exact hT
    exact hT'

/-
Exercise 5_4_1
a No
b Yes
c yes
d No


Exercise 5_4_2
a yes
b yes
c no
d yes

Exercise
-/

theorem Exercise_5_4_3:
    let f : ℤ → ℤ := fun x => (x^2) - x
    closure f {-1, (1: ℤ)} {-1 , (1: ℤ), 0, 2} := by
  intro f
  define
  constructor
  ·
    constructor
    · intro x hx
      simp at hx
      cases hx
      case inl h =>
        rw[h]
        simp
      case inr h =>
        rw[h]
        simp
    ·
      define
      intro x hx
      simp at hx
      cases hx
      case inl h =>
        rw[h]
        dsimp[f]
        simp
      case inr hx =>
        cases hx
        case inl h =>
          rw[h]
          dsimp[f]
          simp
        case inr h =>
          cases h
          case inl h =>
            rw[h]
            dsimp[f]
            simp
          case inr h =>
            rw[h]
            dsimp[f]
            simp
  ·
    intro X ⟨hX, hX'⟩
    dsimp[sub]
    dsimp[closed] at *
    intro x hx
    cases hx
    case inl hx =>
      rw[hx]
      apply hX
      simp
    case inr hx =>
      cases hx
      case inl hx =>
        rw[hx]
        apply hX
        simp
      case inr hx =>
        cases hx
        case inl hx =>
          rw[hx]
          apply hX' 1 (hX _)
          simp
        case inr hx =>
          rw[hx]
          apply hX' (-1) (hX _)
          simp

theorem Exercise_5_4_4_a (A: Type):
    let f : Set (A × A) → Set (A × A) := fun x => inv x
    let d : Set (Set (A × A)) := {S: Set (A × A) | ∀ x ∈ S, x.1 = x.2}
    closed f d:= by
  intro f d
  define
  intro X hX
  dsimp[d] at *
  dsimp[f, inv]
  intro ⟨a, b⟩ hab
  simp at *
  have := hX b a hab
  symm
  assumption

theorem Exercise_5_4_4_b (A: Type):
    let f : Set (A × A) → Set (A × A) := fun x => inv x
    let d : Set (Set (A × A)) := {S: Set (A × A) | ∀ x ∈ S, ⟨x.2, x.1⟩ ∈ S}
    closed f d:= by
  intro f d
  define
  intro X hX
  dsimp[d] at *
  dsimp[f, inv]
  intro x hx
  exact hX ⟨x.2, x.1⟩ hx

theorem Exercise_5_4_4_c (A: Type):
    let f : Set (A × A) → Set (A × A) := fun x => inv x
    let d : Set (Set (A × A)) := {S: Set (A × A) | ∀ x ∈ S, ∀ y ∈ S, x.2 = y.1 → (x.1, y.2) ∈ S}
    closed f d:= by
  intro f d
  define
  intro X hX
  dsimp[d] at *
  dsimp[f, inv]
  intro x hx y hy hxy
  symm at hxy
  exact hX (y.2, y.1) hy (x.2, x.1) hx hxy

theorem Exercise_5_4_5 (A: Type) (f: A → A):
    closed f ∅ := by
  define
  intro x hx
  by_contra h;
  exact hx

theorem Exercise_5_4_6_a (A: Type) (f: A → A) (C: Set A)
    (hf: Set.range f ⊆ C):
  closed f C := by
  define
  intro x hx
  apply hf
  simp

theorem Exercise_5_4_6_b (A: Type) (f: A → A) (C: Set A):
    ∀ B: Set A, closure f B C → C ⊆ B ∪ Set.range f := by
  intro B hC c hc
  dsimp[closure] at hC
  define at hC
  have ⟨⟨hC', hC''⟩  ,hC'''⟩ := hC
  apply hC'''
  dsimp[closed]
  constructor
  ·
    intro b hb
    left
    exact hb
  ·
    intro x hx
    right
    simp
  exact hc

def complement {A : Type} (B : Set A) : Set A := {a : A | a ∉ B}

theorem Exercise_5_4_7 {A : Type} (f g : A → A) (C : Set A)
    (h1 : f ∘ g = id) (h2 : closed f C) : closed g (complement C) := by
  intro x hx
  dsimp[complement] at *
  intro h'
  contradict hx
  have h:= h2 (g x) h'
  have: f (g x) = (f ∘ g) x := by rfl
  rw[this] at h
  rw[h1] at h
  simp at h
  exact h

theorem Exercise_5_4_8 (A: Type) (f: A → A) (C: Set A):
    closed f C ↔ closure f C C := by
  constructor
  ·
    intro hC'
    constructor
    ·
      constructor
      · rfl
      · exact hC'
    ·
      intro X ⟨hX, _⟩
      exact hX
  ·
    intro ⟨⟨_, hC'⟩, _⟩
    exact hC'

theorem Exercise_5_4_9a {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∪ C2) := by
  intro x hx
  cases hx
  case inl hx =>
    left
    exact h1 x hx
  case inr hx =>
    right
    exact h2 x hx

theorem Exercise_5_4_9b {A : Type} (f : A → A) (C1 C2 : Set A)
    (h1 : closed f C1) (h2 : closed f C2) : closed f (C1 ∩ C2) := by
    intro x hx
    constructor
    · exact h1 x hx.1
    · exact h2 x hx.2

/-
Exercise_5_4_9c. Counter example:
A = {a, b}
f = [(a, b), (b, b)]
C₁ = {a, b}
C₂ = {b}
C₁ \ C₂ = {a}. This is not closed under f
-/

theorem Exercise_5_4_10a {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    B1 ⊆ B2 → C1 ⊆ C2 := by
  intro hB1B2
  have ⟨⟨hC1, hC1'⟩ , hC1''⟩ := h1
  apply hC1''
  have ⟨⟨hC2, hC2'⟩ , hC2''⟩ := h2
  constructor
  · exact subset_trans hB1B2 hC2
  · exact hC2'

theorem Exercise_5_4_10b {A : Type} (f : A → A) (B1 B2 C1 C2 : Set A)
    (h1 : closure f B1 C1) (h2 : closure f B2 C2) :
    closure f (B1 ∪ B2) (C1 ∪ C2) := by
  have ⟨⟨hC1, hC1'⟩ , hC1''⟩ := h1
  have ⟨⟨hC2, hC2'⟩ , hC2''⟩ := h2
  constructor
  ·
    constructor
    ·
      intro x hx
      cases hx
      case inl hx =>
        left
        apply hC1
        exact hx
      case inr hx =>
        right
        apply hC2
        exact hx
    ·
      intro x hx
      cases hx
      case inl hx =>
        left
        apply hC1'
        exact hx
      case inr hx =>
        right
        apply hC2'
        exact hx
  ·
    intro D hD
    have ⟨hD, hD'⟩ := hD
    simp[sub]
    constructor
    ·
      apply hC1''
      constructor
      ·
        intro b1 hb1
        apply hD
        left
        exact hb1
      · exact hD'
    ·
      apply hC2''
      constructor
      ·
        intro b2 hb2
        apply hD
        right
        exact hb2
      · exact hD'

/-
Exercise 5_4_10_c
Counterexample:
A = {a, b, c}
f = {(a, c), (b, b), (c, c)}
B₁ = {a, b}
B₂ = {b, c}
C₁ = {a, b, c}
C₂ = {b, c}

The closure of B₁ ∩ B₂ is {b}
C₁ ∩ C₂ = {b, c}
-/

/-
Exercise 5_4_10_d
Counterexample:
A = {a, b, c, d}
f = {(a, d), (b, d), (c, d)}
B₁ = {a, b}
B₂ = {b, c}
C₁ = {a, b, d}
C₂ = {b, c, d}

The closure of B₁ \ B₂ is {a, d}
C₁ \ C₂ = {a}
-/

theorem Exercise_5_4_11 {A : Type} (f : A → A → A) (B : Set A) :
    ∃ (C : Set A), closure2 f B C := by
  set closedSets := {D : Set A | B ⊆ D ∧ closed2 f D}
  set glb: Set A := ⋂₀ closedSets
  exists glb
  define
  constructor
  · constructor
    ·
      intro b hb
      dsimp[glb, closedSets]
      simp
      intro T hBT _
      apply hBT
      exact hb
    ·
      dsimp[closed2]
      intro x hx y hy
      dsimp[glb, closedSets] at *
      simp at *
      intro T hBT hclosedFT
      apply hclosedFT
      exact hx T hBT hclosedFT
      exact hy T hBT hclosedFT
  ·
    intro T ⟨hT, hT'⟩
    dsimp[closed2] at *
    dsimp[sub, glb, closedSets]
    define
    intro a ha
    simp at ha
    apply ha
    exact hT
    exact hT'

/-
Exercise_5_4_12_a
ℤ

Exercise_5_4__12_b
{x ⊆ ℕ | x is finite}
-/

theorem Exercise_5_4_13a {A : Type} (F : Set (A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family F B C := by
  set closedSets: Set (Set A) := {D : Set A | B ⊆ D ∧ closed_family F D}
  set glb: Set A := (⋂₀ closedSets)
  exists glb
  constructor
  ·
    constructor
    · dsimp[glb, closedSets]
      define
      intro b hb
      define
      intro D ⟨hD, _⟩
      exact hD hb
    ·
      dsimp[closed_family]
      intro f hF
      dsimp[closed, glb, closedSets]
      intro x hx
      define at hx
      define
      intro D hD
      have  hx := hx D hD
      exact hD.2 f hF x hx
  ·
    intro D hD
    dsimp[sub]
    have ⟨hD, hD'⟩ := hD
    dsimp[glb, closedSets]
    intro x hx
    define at hx
    apply hx
    constructor
    · exact hD
    · exact hD'

theorem Exercise_5_4_13b {A : Type} (F : Set (A → A)) (B : Set A) (C: Set A) (hC: closure_family F B C ) :
    let UC := ⋃₀ {X : Set A | ∃ f ∈ F, closure f B X}
    let  closedSets: Set (Set A) := {D : Set A | B ⊆ D ∧ closed_family F D}
    let glb: Set A := (⋂₀ closedSets)
    UC ⊆ glb := by
    intro UC closedSets glb a ha
    have ⟨C, hC, hC'⟩ := ha
    simp at hC
    have ⟨f, hf, hf'⟩ := hC
    have ⟨_, hf''⟩ := hf'
    apply hf''
    constructor
    ·
      dsimp[glb, closedSets]
      intro b hb
      define
      intro D ⟨hD, _⟩
      exact hD hb
    .
      dsimp[glb, closedSets]
      intro x hx  D ⟨hD', hD⟩
      apply hD
      exact hf
      apply hx
      apply And.intro hD' hD
    exact hC'

/-
Exercise_5_4_13c
Counter example
A= {a, b, c, d}
B = {a, b}
f₁ = {(a, a), (b, c), (c, c). (d, d)}
f₂ = {(a, a), (b, b), (c, d), (d, d)}
C₁ = {a, b, c}
C₁ = {a, b}
⋃₀ C₁ ∧ C₂ = {a, b, c}
But this is not closed. It needs value d
-/

/-
Exercise_5_4_13d
Counter example
A= {a, b, c, d}
B = {a, b}
f₁ = {(a, a), (b, c), (c, c). (d, d)}
f₂ = {(a, a), (b, b), (c, d), (d, d)}
C₁ = {a, b, c}
C₁ = {a, b}
⋃₀ C₁ ∧ C₂ = {a, b, c}
But this is not closed. It needs value d
-/


/-
Exercise_5_4_14
ℤ

Exercise_5_4_15
ℚ⁺
-/

theorem Exercise_5_4_16_a:
  let I := {X : Set ℕ | X.Infinite}
  ∀ X : Set ℕ, ∃ Y ∈ I, ∃ Z ∈ I, Y ∩ Z = X := by
  intro I X
  let Y := X ∪ {n : ℕ | Even n}
  exists Y
  constructor
  ·
    dsimp[I]
    let f: ℕ → ℕ := fun x => 2 * x
    have hi: Function.Injective f := by
      intro x y hxy
      dsimp[f] at hxy
      apply_fun fun x => x / 2 at hxy
      simp at hxy
      exact hxy
    have hf:  ∀ (x : ℕ), f x ∈ Y := by
      intro x
      dsimp[f, Y]
      right
      simp
    exact Set.infinite_of_injective_forall_mem hi hf
  ·
    let Z := X ∪ {n : ℕ | Odd n}
    exists Z
    constructor
    ·
      dsimp[I]
      let f: ℕ → ℕ := fun x => 2 * x + 1
      have hi: Function.Injective f := by
        intro x y hxy
        dsimp[f] at hxy
        apply_fun fun x => (x - 1) / 2 at hxy
        simp at hxy
        exact hxy
      have hf:  ∀ (x : ℕ), f x ∈ Z := by
        intro x
        dsimp[f, Z]
        right
        simp
      exact Set.infinite_of_injective_forall_mem hi hf
    ·
      dsimp[Y, Z]
      ext x
      constructor
      ·
        intro ⟨hx, hx'⟩
        simp at *
        cases hx
        case inl hx =>
          cases hx'
          case inl hx' =>
            exact hx
          case inr hx' =>
            exact hx
        case inr hx =>
          cases hx'
          case inl hx' =>
            exact hx'
          case inr hx' =>
            have ⟨k, hk⟩ := hx
            have ⟨k', hk'⟩ := hx'
            have :=  Nat.even_xor_odd x
            by_contra h'
            contradict this
            simp
            constructor
            intro _
            exact hx'
            intro _
            exact hx
      · intro hx
        simp
        constructor
        ·
          left
          exact hx
        ·
          left
          exact hx

/-
Exercise 5_4_16_b
𝒫 ℕ
-/

theorem Exercise_5_4_17_a:
    let F := {f : ℝ → ℝ | Function.Injective f}
    let f : (ℝ → ℝ) →  (ℝ → ℝ) → (ℝ → ℝ ) := fun x => fun y => x ∘ y
    closed2 f F:= by
  intro F f g hg h hh
  dsimp[F] at *
  intro x y  hxy
  dsimp[f] at hxy
  apply hh
  apply hg
  exact hxy

theorem Exercise_5_4_17_b:
    let F := {f : ℝ → ℝ | Function.Surjective f}
    let f : (ℝ → ℝ) →  (ℝ → ℝ) → (ℝ → ℝ ) := fun x => fun y => x ∘ y
    closed2 f F := by
  intro F f g hg h hh
  dsimp[F] at *
  intro y
  dsimp[f]
  have ⟨x, hx⟩  := hg y
  have ⟨z, hz⟩ := hh x
  exists z
  rw[hz]
  exact hx

theorem Exercise_5_4_17_c:
    let F := {f : ℝ → ℝ | ∀ x: ℝ, ∀ y: ℝ, x < y → f x < f y}
    let f : (ℝ → ℝ) →  (ℝ → ℝ) → (ℝ → ℝ ) := fun x => fun y => x ∘ y
    closed2 f F := by
  intro F f g hg h hh
  dsimp[F] at *
  intro x y hxy
  dsimp[f]
  apply hg
  apply hh
  exact hxy

/-
Exercise_5_4_17_d
Counterexample
let f₁ (x) = 1 / x
let f₂ (x) = 1 / x
-/

/-
Exercise_5_4_18_a
Counterexample
let f (x) = x
let g (x) = -x

all values of (f + g) map to 0
-/

/-
Exercise_5_4_18_b
Counterexample
let f (x) = x
let g (x) = -x

all values of (f + g) map to 0
-/

theorem Exercise_5_4_18_c:
    let F := {f : ℝ → ℝ | ∀ x: ℝ, ∀ y: ℝ, x < y → f x < f y}
    let f : (ℝ → ℝ) →  (ℝ → ℝ) → (ℝ → ℝ ) := fun x => fun y => (fun z => (x z) + y z)
    closed2 f F := by
  intro F f g hg h hh
  dsimp[F] at *
  intro x y hxy
  dsimp[f]
  apply add_lt_add
  apply hg
  exact hxy
  apply hh
  exact hxy

theorem Exercise_5_4_18_d:
    let F := {f : ℝ → ℝ | ∀ x: ℝ, ∀ y: ℝ, x < y → f x > f y}
    let f : (ℝ → ℝ) →  (ℝ → ℝ) → (ℝ → ℝ ) := fun x => fun y => (fun z => (x z) + y z)
    closed2 f F := by
  intro F f g hg h hh
  dsimp[F] at *
  intro x y hxy
  dsimp[f]
  apply add_lt_add
  apply hg
  exact hxy
  apply hh
  exact hxy

theorem Exercise_5_4_19_part_one (A: Type):
    let F := {R: BinRel A| ∀ x: A, R x x}
    let f : (BinRel A) → (BinRel A) → (BinRel A) := fun x => fun y => Relation.Comp x y
    closed2 f F:= by
  intro F f R hR R' hR'
  dsimp[f, F] at *
  intro x
  define
  exists x
  constructor
  apply hR
  apply hR'

/-
Exercise_5_4_19_part_two
For symmetry, false
Counterexample
let A = {a , b, c}
Let R = {(a, b), (b, a)}
Let R₁ = {(b, c), (c, b)}

R₁ ∘ R = {(a, c)}
-/

/-
Exercise_5_4_19_part_three
For transitivity, false
Counterexample
let A = {x , y, z, a, b}
Let R = {(x, a), (y, b)}
Let R₁ = {(a, y), (b, z)}

R₁ ∘ R = {(x, y), (y, z)}
-/

/-
Exercise_5_4_20
b and e
-/

theorem Exercise_5_4_21_a  {A : Type} (F : Set (A → A → A)) (B : Set A) :
    ∃ (C : Set A), closure_family2 F B C := by
  set closedSets: Set (Set A) := {D : Set A | B ⊆ D ∧ closed_family2 F D}
  set glb: Set A := (⋂₀ closedSets)
  exists glb
  constructor
  ·
    constructor
    · dsimp[glb, closedSets]
      define
      intro b hb
      define
      intro D ⟨hD, _⟩
      exact hD hb
    ·
      dsimp[closed_family]
      intro f hF
      dsimp[closed, glb, closedSets]
      intro x hx y hy D ⟨hD, hD'⟩
      simp at *
      have hx := hx D hD hD'
      have hy := hy D hD hD'
      apply hD'
      exact hF
      exact hx
      exact hy
  ·
    intro D hD
    dsimp[sub]
    have ⟨hD, hD'⟩ := hD
    dsimp[glb, closedSets]
    intro x hx
    define at hx
    apply hx
    constructor
    · exact hD
    · exact hD'

theorem Exercise_5_4_21_b:
    let f: ℝ → ℝ → ℝ := fun x => fun y => x + y
    let g: ℝ → ℝ → ℝ := fun x => fun y => x * y
    let B := {x : ℝ | ∃ q: ℚ, (q: ℝ) = x} ∪ {Real.sqrt 2}
    let C := {x: ℝ | ∃ q: ℚ, ∃ q': ℚ, (q: ℝ) + (q': ℝ) * Real.sqrt 2 = x}
    closure_family2 {f, g} B C := by
  intro f g B C
  constructor
  ·
    constructor
    ·
      dsimp[B, C]
      intro x hx
      simp at *
      cases hx
      case inl hx =>
        exists 0
        exists 1
        rw[hx]
        simp
      case inr hx =>
        have ⟨q, hq⟩ := hx
        exists q
        exists 0
        rw[← hq]
        simp
    ·
      dsimp[closed_family2]
      intro h hh
      cases hh
      case inl hh =>
        dsimp[closed2]
        intro x hx y hy
        dsimp[C] at *
        rw[hh]
        dsimp[f]
        have ⟨qx, q'x, hqx⟩ := hx
        have ⟨qy, q'y, hqy⟩ := hy
        exists (qx + qy)
        exists (q'x + q'y)
        field_simp
        simp
        rw[add_mul ↑q'x ↑q'y (Real.sqrt 2)]
        have : ↑qx + ↑qy + (↑q'x * √2 + ↑q'y * √2) = (↑qx + ↑q'x * √2) + (↑qy + ↑q'y * √2) := by nlinarith
        rw[this]
        rw[hqx, hqy]
      case inr hh =>
        dsimp[closed2]
        intro x hx y hy
        dsimp[C] at *
        rw[hh]
        dsimp[g]
        have ⟨ax, bx, hqx⟩ := hx
        have ⟨cy, dy, hqy⟩ := hy
        exists (ax * cy + bx * dy * 2)
        exists (ax * dy + cy * bx)
        push_cast
        have : (↑ax * ↑cy + ↑bx * ↑dy * 2) + (↑ax * ↑dy + ↑cy * ↑bx ) * √2  = (↑ax + ↑bx * √2) * (↑cy + ↑dy * √2)  := by
          symm
          calc

           _ = ↑ax * (↑cy + ↑dy * √2) + (↑bx * √2) *  (↑cy + ↑dy * √2) := by linarith
           _ = ↑ax * ↑cy + ↑ax * ↑dy * √2 + (↑bx * √2) * ↑cy + (↑bx * √2) * ↑dy * √2 := by linarith
           _ = ↑ax * ↑cy + ↑ax * ↑dy * √2 + (↑bx * √2) * ↑cy + ↑bx  * ↑dy * (√2 * √2) := by linarith
           _ = (↑ax * ↑cy) + (↑ax * ↑dy * √2) + (↑bx * √2 * ↑cy) + (↑bx * ↑dy * 2) := by
            have : (√2 * √2) = 2 := by
              refine Real.mul_self_sqrt ?_
              norm_num
            rw[this]
           _ = (↑ax * ↑cy) + (↑bx * ↑dy * 2) + (↑ax * ↑dy * √2) + (↑bx * √2 * ↑cy)  := by linarith
           _ = (↑ax * ↑cy) + (↑bx * ↑dy * 2) + ((↑ax * ↑dy ) + (↑bx * ↑cy)) * √2  := by linarith
           _ = (↑ax * ↑cy + ↑bx * ↑dy * 2) + (↑ax * ↑dy + ↑cy * ↑bx) * √2 := by linarith
        rw[this]
        rw[hqx, hqy]
  ·
    intro D ⟨hD, hD'⟩
    dsimp[sub, C]
    intro x hx
    simp at hx
    have ⟨q, q', hq⟩ := hx
    rw[← hq]
    dsimp[closed_family2, closed2] at hD'
    have hfirst: ↑q  ∈ D := by
      apply hD
      dsimp[B]
      simp
    have hsecond: ↑q' * √2 ∈ D := by
      have hfirst' : ↑q' ∈ D := by
        apply hD
        dsimp[B]
        simp
      have hsecond': √2 ∈ D := by
        apply hD
        dsimp[B]
        simp
      apply hD' g (by simp) ↑q' hfirst' √2 hsecond'
    exact hD' f (by simp) ↑q hfirst (↑q' * √2) hsecond

/-
Exercise_5_4_21_c
{a + b * (2)^(1/3) + c (2^(2/3 )) | a, b c ∈ ℚ}
-/
