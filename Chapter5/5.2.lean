import HTPILib.Chap5
import Mathlib.Data.Set.Operations
namespace HTPI.Exercises

/-
Example 5.2.2
1. No no
2. Not one to one, onto
3. one to one, onto
4. one to one, not onto
5. one to one, onto
-/

theorem Example_5_2_3_1 (A B: Type) (f: A → B):
  (¬∃ a₁: A, ∃ a₂: A, f a₁ = f a₂ ∧ a₁ ≠ a₂) ↔
  ∀ a₁ a₂: A, f a₁ = f a₂  → a₁ = a₂ := by
    apply Iff.intro
    ·
        intro h a₁ a₂ haa
        by_contra h'
        push_neg at h'
        contradict h
        exists a₁; exists a₂
    ·
        intro h h'
        have ⟨w₁, ⟨w₂, ⟨hw, hw'⟩⟩⟩  := h'
        contradict hw'
        exact (h w₁ w₂) hw

theorem Example_5_2_3_2 (A B: Type) (f: A → B):
  (∀ b : B, ∃ a: A, f a = b) ↔ Set.range f = Set.univ := by
  apply Iff.intro
  ·
    intro h
    apply Set.ext
    intro b
    apply Iff.intro
    ·
      intro hb
      simp
    ·
      intro hb
      simp
      have ⟨w, hw⟩ := h b
      exists w
  ·
    intro h b
    have hb: b ∈ Set.univ := by simp
    rw[← h] at hb
    simp at hb
    have ⟨w, hw⟩ := hb
    exists w

namespace MyScratch
def A : Type := {x : ℝ // x ≠ -1}
theorem Example_5_2_4 (F: A → ℝ):
    let f: A → ℝ := fun (a: A) => (2 * a.1)  / (a.1 + 1)
    one_to_one f ∧ ¬(onto f) := by
  constructor
  ·
    define
    intro x₁ x₂ h
    simp at h
    have h₁: x₁.1 ≠ (-1: ℝ) := x₁.2
    have h₁': x₂.1 ≠ (-1: ℝ) := x₂.2
    have h₂: (x₁.1 + 1 ≠ 0) := by
      by_contra h'
      have h'': x₁.1 = -1 := Eq.symm (neg_eq_of_add_eq_zero_left h')
      contradiction
    have h₃: (x₂.1 + 1 ≠ 0) := by
      by_contra h'
      have h'': x₂.1 = -1 := Eq.symm (neg_eq_of_add_eq_zero_left h')
      contradiction
    field_simp at h
    rw[left_distrib, right_distrib] at h
    simp at h
    exact Subtype.ext h
  ·
    by_contra h'
    simp[onto] at h'
    have ⟨w, hw⟩ := h' 2
    field_simp at hw
    rw[div_eq_one_iff_eq] at hw
    have t: w.1 ≠ w.1 + (1: ℝ):= by norm_num
    exact t hw
    have h₁': w.1 ≠ (-1: ℝ) := w.2
    have h₂: (w.1 + 1 ≠ 0) := by
      by_contra h'
      have h'': w.1 = -1 := Eq.symm (neg_eq_of_add_eq_zero_left h')
      contradiction
    exact h₂
end MyScratch

theorem Example_5_2_5_1 (A B C: Type) (f: A → B) (g: B → C):
    one_to_one f → one_to_one g → one_to_one (g ∘ f) := by
  intro hf hg
  define
  define at hf
  define at hg
  rintro a₁ a₂ hagf
  have hf := hf a₁ a₂
  have hg := hg (f a₁) (f a₂)
  apply hf
  apply hg
  exact hagf

theorem Example_5_2_5_2 (A B C: Type) (f: A → B) (g: B → C):
    onto f → onto g → onto (g ∘ f) := by
  simp[onto]
  intro hf hg c
  have ⟨b, hb⟩ := hg c
  have ⟨a, ha⟩ := hf b
  exists a
  rw[ha]
  exact hb

/-
  Exercise 5_2_1
  One-to-one
  c
  Onto
  a

  Exercise 5_2_2
  One-to-one
  c
  onto
  b
  c

  Exercise 5_2_3
  One-to-one

  onto
  a, c

  Exercise 5_2_4
  One-to-one
  a b c
  onto
  a b

-/

def A : Type := {x : ℝ // x ≠ 1}
theorem Exercise_5_2_5_a (F: A → A):
    let f: A → A := fun (a: A) => ⟨(a.1 + 1)  / (a.1 - 1), by
      by_contra h
      have ha: a.1 ≠ (1: ℝ) := a.2
      have ha'': (a.1 - 1) ≠ 0 := by
        by_contra h'
        rw[sub_eq_zero] at h'
        contradiction
      field_simp at h
      simp at h
      have h': a.1 + 1 ≠ a.1 - 1 := by linarith
      contradiction
    ⟩
    one_to_one f ∧ (onto f) := by
  constructor
  ·
    define
    intro a₁ a₂ ha
    have ha := congrArg Subtype.val ha
    simp at ha
    have ha₁: a₁.1 ≠ 1 := a₁.2
    have ha₂: a₂.1 ≠ (1) := a₂.2
    have ha₁': (a₁.1 - 1) ≠ 0 := by
      by_contra h'
      rw[sub_eq_zero] at h'
      contradiction
    have ha₂': (a₂.1 - 1) ≠ 0 := by
      by_contra h'
      rw[sub_eq_zero] at h'
      contradiction
    field_simp[ha₁', ha₂'] at ha
    have : (a₁.1: ℝ) = a₂.1 := by linarith
    exact Subtype.ext this
  ·
    define
    intro y
    exists ⟨(y.1 + 1) / (y.1 - 1), by
      simp
      push_neg
      by_contra h'
      have ha: y.1 ≠ (1: ℝ) := y.2
      have ha'': (y.1 - 1) ≠ 0 := by
        by_contra h'
        rw[sub_eq_zero] at h'
        contradiction
      field_simp at h'
      have h': y.1 + 1 ≠ y.1 - 1 := by linarith
      contradiction
    ⟩
    apply Subtype.ext
    simp
    have: (y.1 - 1 ≠ 0 ) := by
      by_contra h
      rw[sub_eq_zero] at h
      exact y.2 h
    field_simp
    linarith

theorem Exercise_5_2_5 (F: A → A):
    let f: A → A := fun (a: A) => ⟨(a.1 + 1)  / (a.1 - 1), by
      by_contra h
      have ha: a.1 ≠ (1: ℝ) := a.2
      have ha'': (a.1 - 1) ≠ 0 := by
        by_contra h'
        rw[sub_eq_zero] at h'
        contradiction
      field_simp at h
      simp at h
      have h': a.1 + 1 ≠ a.1 - 1 := by linarith
      contradiction
    ⟩
    f ∘ f = fun (a: A) => a := by
    simp
    apply funext
    intro a
    apply Subtype.ext
    simp
    have: (a.1 - 1 ≠ 0 ) := by
      by_contra h
      rw[sub_eq_zero] at h
      exact a.2 h
    field_simp
    linarith

theorem Exercise_5_2_6 (a b: ℝ) (ha: a ≠ 0)
    (f: ℝ → ℝ):
    let f := fun x => a * x + b
    one_to_one f ∧ onto f := by
    constructor
    ·
      define
      intro a₁ a₂ haa
      simp at haa
      cases haa
      case inl haa => exact haa
      case inr haa => contradiction
    ·
      define
      intro y
      exists (y - b) / a
      simp
      field_simp
      linarith

theorem Exercise_5_2_7_a (f: {x: ℝ // x > 0} → ℝ):
    let f := fun x: {x: ℝ // x > 0} => (1: ℝ) / x - x
    one_to_one f := by
  define
  intro a₁ a₂ ha
  simp at ha
  have ha₁: a₁.1 ≠ 0 := by
    by_contra h'
    have t := a₁.2
    rw[h'] at t
    contradict t
    push_neg
    norm_num
  have ha₁': 0 < a₁.1 := by exact a₁.2
  have ha₂': 0 < a₂.1 := by exact a₂.2
  have ha₂: a₂.1 ≠ 0 := by
    by_contra h'
    have t := a₂.2
    rw[h'] at t
    contradict t
    push_neg
    norm_num
  cases (Classical.em (a₁.1 ≤ a₂.1))
  case inl h=>
    cases (lt_or_eq_of_le h)
    case inl h =>
      have h' := h
      have ha₁a₂: (0 < 1/(a₁.1 * a₂.1)) := by positivity
      apply Subtype.ext
      rw[← inv_lt_inv₀] at h'
      have y: (a₁.1)⁻¹ - a₁.1 > (a₂.1)⁻¹ - a₂.1 := by linarith
      by_contra
      contradict ha
      push_neg
      rw[ne_iff_gt_or_lt]
      apply Or.inl
      linarith
      exact a₂.2
      exact a₁.2
    case inr h =>
      apply Subtype.ext
      assumption
  case inr h =>
    push_neg at h
    have h' := h
    apply Subtype.ext
    have ha₁a₂: (0 < 1/(a₁.1 * a₂.1)) := by positivity
    rw[← inv_lt_inv₀] at h'
    have y: (a₁.1)⁻¹ - a₁.1 < (a₂.1)⁻¹ - a₂.1 := by linarith
    by_contra
    contradict ha
    push_neg
    rw[ne_iff_gt_or_lt]
    apply Or.inl
    linarith
    exact a₁.2
    exact a₂.2

theorem Exercise_5_2_7_b (f: {x: ℝ // x > 0} → ℝ):
    let f := fun x: {x: ℝ // x > 0} => (1: ℝ) / x - x
    onto f := by
  define
  intro y
  have h: 0 < (-y + √(y^2 + 4))/2  := by
    field_simp
    rw[zero_mul]
    simp
    have ypos2 : 0 ≤ √(y^2 + 4) := by positivity
    cases (Classical.em (0 ≤ y))
    case inl hpos =>
      have h2: 2 ≠ 0 := by norm_num
      have hfinal: y ^ 2 < √(y ^ 2 + 4) ^ 2 := by
        have hyhy: 0 ≤ y^2 + 4 := by positivity
        rw[Real.sq_sqrt hyhy]
        linarith
      rw[(pow_lt_pow_iff_left₀ hpos ypos2 h2)] at hfinal
      exact hfinal
    case inr hneg =>
      push_neg at hneg
      have ypos2 : 0 ≤ √(y^2 + 4) := by positivity
      linarith
  exists ⟨(-y + √(y^2 + 4))/2, h⟩
  field_simp
  have h':(-y + √(y ^ 2 + 4)) ≠ 0 := by linarith
  field_simp
  have hyhy: 0 ≤ y^2 + 4 := by positivity
  have reer := Real.sq_sqrt hyhy
  nlinarith

/-
Exercise_5_2_8_a
 The set of reals whose value is < √2 and > -√2
-/

theorem Exercise_5_2_8_b:
    let f := fun x: ℝ => {y: ℝ | y^2 < x };
    ¬one_to_one f ∧ ¬onto f := by
  constructor
  · define
    push_neg
    exists 0
    exists -1
    constructor
    ·
      have h : {y : ℝ | y ^ 2 < 0} = ∅ := by
        by_contra h'
        push_neg at h'
        have ⟨w, hw⟩ := h'
        simp at hw
        have hw': w ≠ 0 := by
          intro h
          rw[h] at hw
          simp at hw
        rw[← sq_pos_iff] at hw'
        have final := lt_trans hw' hw
        simp at final
      symm
      rw[h]
      by_contra h'
      push_neg at h'
      have ⟨w, hw⟩ := h'
      simp at hw
      have hw': w ≠ 0 := by
          intro h
          rw[h] at hw
          simp at hw
          have : 0 < (1: ℝ) := by norm_num
          have := by apply lt_trans hw this
          simp at this
      rw[← sq_pos_iff] at hw'
      have final := lt_trans hw' hw
      simp at final
      have : 0 < (1: ℝ) := by norm_num
      have := by apply lt_trans final this
      simp at this
    ·
      simp
  · define
    push_neg
    exists {100}
    intro x h
    have h': 100 ∈ {(100: ℝ)} := by rfl
    rw[←h] at h'
    simp at h'
    have h'': 1 ∈ {y : ℝ | y ^ 2 < x} := by
      simp
      have: 1 < 100 ^ 2 := by norm_num
      apply lt_trans _ h'
      norm_num
    rw[h] at h''
    simp at h''

/-
Exercise_5_2_9_a
 {1, 2, 3, 4}
-/

theorem Exercise_5_2_9_b:
  let f: (Set (Set ℝ)) → Set ℝ  := fun x: (Set (Set ℝ)) => ⋃₀ x
  ¬one_to_one f ∧ onto f := by
  constructor
  ·
    define
    push_neg
    exists {{1}, {2}}
    exists {{1, 2}}
    constructor
    ·
      apply Set.ext
      intro x
      constructor
      ·
        intro h
        simp at h
        cases h
        case inl h =>
          rw[h]
          simp
        case inr h =>
          rw[h]
          simp
      · intro h
        simp at h
        simp
        cases h
        case inl h =>
          apply Or.inr h
        case inr h =>
          apply Or.inl h
    ·
      by_contra h'
      have h: {(1: ℝ)} ∈ {{1}, {2}} := by
        simp
      rw[h'] at h
      simp at h
      have h'': (2: ℝ) ∈ {1, 2} := by simp
      rw[←h] at h''
      simp at h''
  · define
    intro Y
    exists {Y}
    simp

theorem Exercise_5_2_10_a (A B C: Type) (f: A → B) (g: B → C):
    onto (g ∘ f) →  onto g := by
  intro h
  define
  define at h
  intro c
  have ⟨b, hb⟩ := h c
  exists f b

theorem Exercise_5_2_10_b (A B C: Type) (f: A → B) (g: B → C):
    one_to_one (g ∘ f) →  one_to_one f := by
  intro h
  define at h
  define
  intro a₁ a₂ ha₁a₂
  have h := h a₁ a₂
  apply h
  simp
  rw[ha₁a₂]

theorem Exercise_5_2_11_a (A B C: Type) (f: A → B) (g: B → C):
    onto f → ¬one_to_one g → ¬one_to_one (g ∘ f) := by
  intro hf hg
  define
  push_neg
  define at hg
  push_neg at hg
  have ⟨b₁, b₂, hb, hb'⟩ := hg
  define at hf
  have ⟨a₁, ha₁⟩ := hf b₁
  have ⟨a₂, ha₂⟩ := hf b₂
  exists a₁
  exists a₂
  constructor
  ·
    simp
    rw[ha₁, ha₂]
    exact hb
  ·
    by_contra h';
    rw[h'] at ha₁
    rw[← ha₁, ← ha₂] at hb'
    contradict hb'
    rfl

theorem Exercise_5_2_11_b (A B C: Type) (f: A → B) (g: B → C):
    ¬ onto f → one_to_one g → ¬onto (g ∘ f) := by
  intro hf hg
  define
  push_neg
  define at hf
  push_neg at hf
  define at hg
  have ⟨b, hb⟩ := hf
  exists g b
  intro a
  have hb' := hb a
  simp
  push_neg
  by_contra h'
  have hg':= (hg (f a) b) h'
  exact hb' hg'

theorem Exercise_5_2_12 (A B: Type) (f: A → B):
    let g := fun x: B => {a: A | f a = x};
    onto f → one_to_one g := by
  intro g hf
  define
  define at hf
  intro b₁ b₂ hb₁b₂
  simp[g] at hb₁b₂
  have ⟨a₁, ha₁⟩ := hf b₁
  have ⟨a₂, ha₂⟩ := hf b₂
  have htemp: a₁ ∈ {a : A | f a = b₂} := by
    have h' : a₁ ∈ {a : A | f a = b₁} := by
      simp
      assumption
    rw[← hb₁b₂]
    assumption
  simp at htemp
  rw[← ha₁, htemp]

/-
onto f is necessary. Otherwise two elements in b
that do not have a value from f and so their range
in g is the empty set but that does not guarante they
are equal
-/

theorem Exercise_5_2_13_a (A B: Type) (C: Set A) (f: A → B):
    one_to_one f → one_to_one (C.restrict f) := by
  intro h
  define
  define at h
  intro a₁ a₂ ha₁a₂
  apply Subtype.ext
  apply h a₁ a₂
  assumption

theorem Exercise_5_2_13_b (A B: Type) (C: Set A) (f: A → B):
    onto (C.restrict f) → onto f := by
  intro h
  define
  define at h
  intro b
  have ⟨c, hc⟩ := h b
  exists c

/-
Exercise_5_2_13_c
counter example of converse of part a
A = {1, 2, 3} B = {7} c = {2}
f = {(1, 7), (2, 7), (3, 7)}

counter example of converse of part b
A = {1, 2, 3} B = {6, 7} c = {2}
f = {(1, 7), (2, 7), (3, 6)}
-/

theorem Exercise_5_2_14_a (A B: Type) (f: A → B)
    (hb: ∃ b: B, ∀ a : A, f a  = b) (hA: Nontrivial A):
    ¬ one_to_one f := by
  define
  push_neg
  have ⟨a₁, a₂, ha₁a₂⟩ := hA
  exists a₁
  exists a₂
  constructor
  ·
    have ⟨b, hb⟩ := hb
    rw[hb a₁, hb a₂]
  · assumption

theorem Exercise_5_2_14_b (A B: Type) (f: A → B)
    (hb: ∃ b: B, ∀ a : A, f a  = b) (hB: Nontrivial B):
    ¬ onto f := by
  define
  push_neg
  have ⟨b₁, b₂, hb₁b₂⟩ := hB
  have ⟨b, hb⟩ := hb
  cases eq_or_ne b b₁
  case inl h' =>
    exists b₂
    intro a
    rw[hb a, h']
    assumption
  case inr h' =>
    exists b₁
    intro a
    rw[hb a]
    assumption

theorem Exercise_5_2_15 (U C: Type) (A B: Set U) (f: U → C) (hAB: A ∩ B = ∅)
    (hA: one_to_one (A.restrict f)) (hB: one_to_one (B.restrict f)):
    one_to_one ((A ∪ B).restrict f) ↔ Set.range (A.restrict f) ∩ Set.range (B.restrict f) = ∅ := by
  constructor
  ·
    intro h
    define at hA
    define at hB
    define at h
    by_contra h'
    push_neg at h'
    have ⟨c, hc, hc'⟩ := h'
    simp at hc
    simp at hc'
    have ⟨a, ha, ha'⟩ := hc
    have ⟨b, hb, hb'⟩ := hc'
    simp at h
    have : f a = f b :=  by rw[ha', hb'];
    have hfinal := h a (Or.inl ha) b (Or.inr hb) (this)
    contradict hAB
    push_neg
    exists a
    constructor
    · assumption
    · rw[hfinal]
      assumption
  · intro h
    define
    simp
    intro x₁ hx₁ x₂ hx₂ hx₁hx₂
    cases hx₁
    case inl hx₁ =>
      cases hx₂
      case inl hx₂ =>
        define at hA
        simp at hA
        apply hA x₁ hx₁ x₂ hx₂
        assumption
      case inr hx₂ =>
        contradict h
        push_neg
        exists f x₁
        constructor
        simp
        exists x₁
        rw[hx₁hx₂]
        simp
        exists x₂
    case inr hx₁ =>
      cases hx₂
      case inl hx₂ =>
        contradict h
        push_neg
        exists f x₁
        constructor
        · simp
          exists x₂
          constructor
          · assumption
          · symm
            assumption
        · simp
          exists x₁
      case inr hx₂ =>
        define at hB
        simp at hB
        apply hB x₁ hx₁ x₂ hx₂
        assumption

theorem Exercise_5_2_16 {A B C : Type}
    (R : Set (A × B)) (S : Set (B × C)) (f : A → C) (g : B → C)
    (h1 : graph f = comp S R) (h2 : graph g = S) (h3 : one_to_one g) :
    is_func_graph R := by
  define
  intro a
  define at h3
  have h': (a, f a) ∈ graph f := by rfl
  rw[h1] at h'
  define at h'
  have ⟨b, hb, hb'⟩ := h'
  exists_unique
  constructor
  · exact hb
  · intro b₁ b₂ hb₁ hb₂
    have hg' : (a, g b₁) ∈ graph f := by
        rw[h1]
        define
        exists b₁
        constructor
        · assumption
        · rw[← h2]
          define
          rfl
    have hg'' : (a, g b₂) ∈ graph f := by
      rw[h1]
      define
      exists b₂
      constructor
      · assumption
      · rw[← h2]
        define
        rfl
    define at hg'
    define at hg''
    apply h3
    rw[← hg', ← hg'']

theorem Exercise_5_2_17a
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : onto f) : reflexive R → reflexive S := by
  intro hR
  define
  define at hR
  intro b
  apply (h1 b b).mpr
  define at h2
  have ⟨a, ha⟩ := h2 b
  exists a
  exists a
  constructor
  · assumption
  · constructor
    · assumption
    · exact hR a

theorem Exercise_5_2_17b
    {A B : Type} (f : A → B) (R : BinRel A) (S : BinRel B)
    (h1 : ∀ (x y : B), S x y ↔ ∃ (u v : A), f u = x ∧ f v = y ∧ R u v)
    (h2 : one_to_one f) : transitive R → transitive S := by
  intro hTransR
  define at hTransR
  define
  intro b₁ b₂ b₃ hb₁b₂ hb₂b₃
  have ⟨a₁, a₂, ha₁, ha₂, ha₁a₂⟩ := (h1 b₁ b₂).mp hb₁b₂
  have ⟨a'₂, a₃, ha'₂, ha₃, ha'₂a₃⟩ := (h1 b₂ b₃).mp hb₂b₃
  apply (h1 b₁ b₃).mpr
  exists a₁
  exists a₃
  constructor
  · assumption
  · constructor
    · assumption
    · apply hTransR a₁ a₂ a₃
      · assumption
      · have : a₂ = a'₂ := by
          apply h2
          rw[ha₂, ha'₂]
        rw[← this] at ha'₂a₃
        assumption

theorem Exercise_5_2_18_a (A: Type) (R: Setoid A) :
  let g := fun x: A => Quotient.mk R x
  onto g := by
  intro g
  define
  apply Quotient.ind
  intro a
  exists a

theorem Exercise_5_2_18_b (A: Type) (R: Setoid A):
  let identity := Setoid.mk (fun x y: A => x = y) (
    by
    constructor
    ·
      intro x
      rfl
    · intro x y hxy
      symm
      assumption
    · intro x y z hxy hyz
      rw[hxy, ← hyz]
  )
    let g := fun x: A => Quotient.mk R x
    one_to_one g ↔ R = identity := by
  apply Iff.intro
  ·
    intro h
    apply Setoid.ext_iff.mpr
    intro a₁ a₂
    apply Iff.intro
    ·
      intro ha₁a₂
      simp
      define at h
      apply h a₁ a₂
      simp
      apply Quotient.sound
      assumption
    · simp
      intro h
      rw[h]
  · intro h
    define
    intro a₁ a₂ ha₁a₂
    simp at ha₁a₂
    have ha₁a₂' := Quotient.exact ha₁a₂
    define at ha₁a₂'
    rw[h] at ha₁a₂'
    simp at ha₁a₂'
    assumption

theorem Exercise_5_2_19 (A B: Type) (f: A → B) (R: Setoid A)
    (hf: ∀ x y: A, R x y → f x = f y):
    let h: Quotient R → B := Quotient.lift f hf
    one_to_one h ↔ ∀ x y: A, f x = f y → R x y := by
  apply Iff.intro
  ·
    intro h x y hxy
    have h' := h (Quotient.mk R x) (Quotient.mk R y) hxy
    apply Quotient.exact
    assumption
  · intro h'
    define
    apply Quotient.ind
    intro x
    apply Quotient.ind
    intro y hxy
    apply Quotient.sound
    apply h' x y
    simp at hxy
    assumption

theorem Exercise_5_2_20_a (A B C: Type) (f: A → B) (g: B → C) (h: B → C)
    (hf: onto f) (hgfhf: g ∘ f = h ∘ f): g = h := by
  apply funext
  intro b
  define at hf
  have ⟨a, ha⟩ := hf b
  rw[← ha]
  have : g (f a) = (g ∘ f) a := by rfl
  rw[this]
  have : h (f a) = (h ∘ f) a := by rfl
  rw[this]
  rw[hgfhf]

theorem Exercise_5_2_20_b (A B C: Type) (hC: Nontrivial C) (f: A → B)
    (hgh: ∀ g h: B → C, g ∘ f = h ∘ f → g = h):
    onto f := by
  define
  intro b
  have ⟨c₁, c₂, hc₁c₂⟩ := hC
  classical
  let g: B → C := fun  x: B => if x = b then c₂ else c₁
  let h: B → C := fun x : B => c₁
  have hgh' := hgh g h
  by_contra h'
  push_neg at h'
  have hgh'': g ∘ f = h ∘ f := by
    apply funext
    intro a
    simp
    cases Classical.em (f a = b)
    case _ =>
      contradict h' a
      assumption
    case inr hfab =>
      push_neg at hfab
      have : g (f a) = c₁ := by
        simp[g]
        intro
        contradict hfab
        assumption
      rw[this]
  have  := hgh' hgh''
  have hg : g b = c₂ := by simp[g]
  have hh : h b = c₁ := by simp[h]
  contradict hc₁c₂
  rw[← hh, ← hg, this]

theorem Exercise_5_2_21a {A B C : Type} (f : B → C) (g h : A → B)
    (h1 : one_to_one f) (h2 : f ∘ g = f ∘ h) : g = h := by
apply funext
intro a
apply h1
have : f (g a) = (f ∘ g) a := by rfl
rw[this]
have : f (h a) = (f ∘ h) a := by rfl
rw[this, h2]

theorem Exercise_5_2_21b {A B C : Type} (f : B → C) (a : A)
    (h1 : ∀ (g h : A → B), f ∘ g = f ∘ h → g = h) :
    one_to_one f := by
    by_contra h'
    define at h'
    push_neg at h'
    have ⟨b₁, b₂, hb₁b₂, hb₁b₂'⟩ := h'
    let g := fun x: A => b₁
    let h := fun x: A => b₂
    have h1' := h1 g h
    have hfgfh : f ∘ g = f ∘ h  := by
      apply funext
      intro a₁
      simp[g, h]
      assumption
    have h1' := h1 g h hfgfh
    have h1'' : g a = b₁ := by simp[g]
    rw[h1'] at h1''
    simp[h] at h1''
    contradict h1''
    push_neg
    symm
    assumption

theorem Exercise_5_2_22_a:
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g}
    R (fun x: ℝ  => x^4 + 1) (fun x: ℝ  => x^2 + 1) ∧ ¬R (fun x: ℝ  => x^3 + 1) (fun x: ℝ  => x^2 + 1) := by
  constructor
  ·
    simp[RelFromExt]
    exists (fun x => (x - 1) * (x - 1) + 1)
    apply funext
    intro x
    simp
    field_simp
  ·
    by_contra h'
    simp[RelFromExt] at h'
    have ⟨h, hh⟩ := h'
    have hh' : (fun (x : ℝ) => x ^ 3 + 1) (1) = 2 := by norm_num
    have hh'' : (fun (x : ℝ) => x ^ 3 + 1) (-1) = 0 := by norm_num
    rw[hh] at hh'
    rw[hh] at hh''
    simp at hh''
    simp at hh'
    rw[hh''] at hh'
    contradict hh'
    push_neg
    norm_num

theorem Exercise_5_22_b:
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g}
    preorder R := by
  define
  constructor
  ·
      intro f
      simp[RelFromExt]
      exists fun x => x
  ·
    intro x y z hxy hyz
    simp[RelFromExt] at *
    have ⟨g₂, hg₂⟩ := hxy
    have ⟨g₁, hg₁⟩ := hyz
    exists fun x => g₂ (g₁ x)
    apply funext
    intro a
    simp
    have : g₁ (z a) = y a := by simp[hg₁]
    rw[this]
    have : g₂ (y a) = x a := by simp[hg₂]
    rw[this]

theorem Exercise_5_22_c:
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g};
    let identity := fun x : ℝ => x;
    ∀ (f: ℝ → ℝ), R f identity := by
  intro R identity f
  simp [R, RelFromExt, identity]
  exists f

theorem Exercise_5_22_d:
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g};
    let identity := fun x : ℝ => x;
    ∀ (f: ℝ → ℝ), R identity f ↔ one_to_one f := by
  intro R identity f
  constructor
  · intro hRiF
    simp [R, RelFromExt, identity] at hRiF
    have ⟨g, hg⟩ := hRiF
    intro x₁ x₂ hx₁x₂
    have h': (g ∘ f) x₁ = (g ∘ f) x₂ := by simp[hx₁x₂]
    rw[← hg] at h'
    simp at h'
    assumption
  · intro hf
    simp[R, RelFromExt]
    classical
    exists fun x => if x ∈ Set.range f then Function.invFun f x else x
    have hf' : Function.Injective f := by apply hf
    apply funext
    simp[identity]
    intro x
    symm
    have hff'' := Function.invFun_comp hf'
    have : Function.invFun f (f x) = (Function.invFun f ∘ f) x := by simp
    rw[this, hff'']
    simp

theorem Exercise_5_22_e (c: ℝ):
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g};
    let g := fun x => c
    ∀ f : ℝ → ℝ, R g f := by
  intro R g f
  simp[R, RelFromExt]
  exists g

theorem Exercise_5_22_f (c: ℝ):
    let R := RelFromExt {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g};
    let g := fun x => c
    ∀ f: ℝ → ℝ, R f g ↔ (∃ k: ℝ, ∀ x : ℝ, f x = k):= by
  intro R g f
  constructor
  ·
    intro hRfg
    simp[R, RelFromExt] at hRfg
    exists f c
    intro x
    have ⟨h, hh⟩ := hRfg
    rw[hh]
    simp[g]
  · intro fconst
    have ⟨k, hk⟩ := fconst
    simp[R, RelFromExt]
    exists fun x => k
    apply funext
    intro x
    simp
    rw[hk x]

theorem Exercise_5_22_g (T: BinRel (Set (ℝ → ℝ))):
    let R := {(f,  g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ h: ℝ → ℝ, f = h ∘ g}
    let S := RelFromExt (R ∩ (inv R))
    (∀ f g: ℝ → ℝ, T (equivClass S f) (equivClass S g) ↔ RelFromExt R f g) ∧ partial_order_on (mod (ℝ → ℝ) S) T →
    largestElt T {f | one_to_one f} (mod (ℝ → ℝ) S) ∧ smallestElt T {f | ∃ c : ℝ, ∀ x: ℝ, f x = c} (mod (ℝ → ℝ) S)  := by
  intro R S ⟨hT ,hT'⟩
  constructor
  ·
    rw[largestElt]
    constructor
    ·
      define
      exists fun x => x
      simp[equivClass, S, RelFromExt, R, inv]
      apply Set.ext
      intro f
      apply Iff.intro
      · -- →
        intro h
        simp at h
        have ⟨h1, h2⟩ := h
        have ⟨g1, hg1⟩ := h1
        have ⟨g2, hg2⟩ := h2
        simp
        apply (Exercise_5_22_d f).mp
        rw[RelFromExt]
        define
        exists g2
      · --- ←
        intro h
        simp at h
        constructor
        ·
          exists f
        apply (Exercise_5_22_d f).mpr
        assumption
    · intro X hX
      simp[mod] at hX
      have ⟨f, hf⟩ := hX
      rw[← hf]
      have : {f : ℝ → ℝ | one_to_one f} = equivClass S (fun x => x) := by
        apply Set.ext
        intro f
        constructor
        ·
          intro hf
          simp at hf
          define
          constructor
          ·
            define
            exists f
          · define
            have:= (Exercise_5_22_d f).mpr hf
            simp[RelFromExt] at this
            assumption
        · intro hf
          have ⟨hf, hf'⟩ := hf
          simp
          apply (Exercise_5_22_d f).mp
          simp[RelFromExt]
          assumption
      rw[this]
      rw[(hT f (fun x => x))]
      simp [RelFromExt]
      simp[R]
      exists f
  ·
    rw[smallestElt]
    constructor
    ·
      simp[mod, equivClass, S, RelFromExt, R, inv]
      exists fun x => 1
      apply Set.ext
      intro f
      constructor
      ·
        intro hf
        simp at hf
        have ⟨hf, hf'⟩ := hf
        have ⟨g, hg⟩ := hf
        simp
        exists g 1
        intro x
        rw[hg]
        simp
      · intro hf
        simp at hf
        simp
        constructor
        ·
          have ⟨c, hc⟩ := hf
          exists fun x => c
          apply funext
          intro x
          rw[ hc x]
          simp
        · exists fun x => 1
    · intro X hX
      define at hX
      have ⟨x, hx⟩ := hX
      have : {f : ℝ → ℝ | ∃ (c : ℝ), ∀ (x : ℝ), f x = c} = (equivClass S fun x => 1) := by
        apply Set.ext
        intro f
        simp
        constructor
        · intro hf
          have ⟨c, hc⟩ := hf
          define
          constructor
          ·
            simp[R]
            exists fun x => c
            apply funext
            intro x
            rw[hc x]
            simp
          · simp[inv, R]
            exists fun x => 1
        ·
          intro hf
          simp[equivClass, S, RelFromExt, inv, R] at hf
          have ⟨hf, hf'⟩ := hf
          have ⟨h, hh⟩ := hf
          exists h 1
          intro x
          rw[hh]
          simp
      rw[this, ← hx]
      rw[hT (fun x => 1) x]
      simp[RelFromExt, R]
      exists fun x => 1

  /-
  Exercise 5_2_23 a
    yes

  Exercise 5_2_23 b
    value -1 does not have a value
  -/
