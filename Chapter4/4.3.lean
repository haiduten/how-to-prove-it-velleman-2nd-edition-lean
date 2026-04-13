import HTPILib.Chap4
namespace HTPI.Exercises


def reflexive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x : A), R x x

def symmetric {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y : A), R x y → R y x

def transitive {A : Type} (R : BinRel A) : Prop :=
  ∀ (x y z : A), R x y → R y z → R x z

def extension {A B : Type} (R : Rel A B) : Set (A × B) :=
  {(a, b) : A × B | R a b}

theorem ext_def {A B : Type} (R : Rel A B) (a : A) (b : B) :
    (a, b) ∈ extension R ↔ R a b := by rfl

section
variable {A: Type}
variable (R: BinRel A)


theorem Example_4_3_4_1: reflexive R ↔ {(x, y) : A × A | x = y} ⊆ extension R := by
  constructor
  · -- mp
    rintro h₀ ⟨x, y⟩ h₁
    define at h₁
    define
    rw[h₁]
    exact h₀ y
  · -- mpr
    rintro h x
    have g: x = x :=  by rfl
    define at h
    have t: (x, x) ∈ {(x, y) : A × A | x = y}:= by
      rfl
    have r := h t
    rw[ext_def] at r
    exact r

theorem Example_4_3_4_2: symmetric R ↔ extension R = inv (extension R) := by
  constructor
  · -- →
    rintro h
    apply Set.ext
    rintro ⟨m, n⟩
    constructor
    · -- →
      rintro h₁
      rw[ext_def] at h₁
      rw[inv]; simp; rw[ext_def]
      exact h m n h₁
    · -- ←
      rintro h₁
      rw[ext_def]
      rw[inv,] at h₁; simp at h₁; rw[ext_def] at h₁
      exact h n m h₁
  · -- ←
    rintro h m n h₁
    rw[←(ext_def R m n)] at h₁
    rw[h] at h₁
    rw[inv] at h₁; simp at h₁
    rw[ext_def] at h₁
    exact h₁

theorem Example_4_3_4_3: transitive R ↔ comp (extension R) (extension R) ⊆ (extension R) := by
  constructor
  · -- mp
    rintro h ⟨m, n⟩ h₁
    rw[ext_def]
    rcases h₁ with ⟨o, h₂, h₃⟩
    rw[ext_def] at h₂
    rw[ext_def] at h₃
    exact h m o n h₂ h₃
  · -- mpr
    rintro h m n o h₁ h₂
    rw[←(ext_def R m n)] at h₁
    rw[←(ext_def R n o)] at h₂
    rw[←(ext_def R m o)]
    exact h (Exists.intro n (And.intro h₁ h₂))

/-
  Exercise 4_3_2
  It is reflexsive and symmetric but not transitive

  Exercise_4_3_4_a
  {(b, d), (d, b), (d, a), (a, c), (c, c)}

  Exercise_4_3_4_b
  {(a, d), (b, d), (a, b), (b, a)}

  Exercise_4_3_4_c
  {(a, a), (b, b), (c, c), (d, d), (b, d), (d, b)}
  reflexsive

  Exercise_4_3_4_D
  {(a, d), (a, c), (a, b), (c, d), (b, d)}
  transitive

  Exercise_4_3_5
  {(a, y), (a , z), (b, x), (c, y), (c, z)}
-/

namespace Exercise_4_3_6

section

def D (r: ℝ): Set (ℝ × ℝ) := {(x, y) | abs (x - y) < r}

theorem Exercise_4_3_6 (r s: ℝ) (hr: 0 < r) (hs: 0 < s): comp (D r) (D s) = D (r + s) := by
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  · -- right
    rintro ⟨o, h₁ ,h₂⟩
    define at h₁
    define at h₂
    define
    rw[←(sub_add_sub_cancel m o n)]
    apply lt_of_le_of_lt (abs_add_le (m - o) (o - n))
    rw[add_comm]
    apply add_lt_add h₂ h₁
  · -- left
    rintro h;
    define at h
    define
    rcases abs_cases (m - n) with ⟨h₁, h₂⟩  | ⟨h₁, h₂⟩
    · -- case 1
      rw[h₁] at h
      by_cases h₃: m - n < s
      · -- case: m - n < s
        by_cases h4 : m - n < r
        use ((m + n) / 2)
        constructor
        define
        rcases abs_cases (m - (m + n) / 2) with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
        rw[h₄]
        linarith
        rw[h₄]
        linarith
        define
        rcases abs_cases ((m + n) / 2 - n) with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
        rw[h₄]
        linarith
        rw[h₄]
        linarith
        use (n + (r  /2))
        constructor
        define
        rcases abs_cases (m - (n + r / 2)) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
        define
        rcases abs_cases (n + r / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
      · -- right case
        by_cases h4 : m - n < r
        use (m - (s / 2))
        constructor
        define
        rcases abs_cases (m - (m - s / 2)) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
        define
        rcases abs_cases (m - s / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
        use ( ((n + r) + (m - s)) / 2)
        constructor
        define
        rcases abs_cases (m - (n + r + (m - s)) / 2) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
        define
        rcases abs_cases ((n + r + (m - s)) / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
        rw[h₅]
        linarith
        rw[h₅]
        linarith
    rw[h₁] at h
    by_cases h₃: -(m - n) < s
    by_cases h₄ : -(m - n)< r
    use ((m + n) / 2)
    constructor
    define
    rcases abs_cases (m - (m + n) / 2) with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
    rw[h₄]
    linarith
    rw[h₄]
    linarith
    define
    rcases abs_cases ((m + n) / 2 - n) with ⟨h₄, h₅⟩ | ⟨h₄, h₅⟩
    rw[h₄]
    linarith
    rw[h₄]
    linarith
    use (n - (r / 2))
    constructor
    define
    rcases abs_cases (m - (n - r / 2)) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith
    define
    rcases abs_cases (n - r / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith
    by_cases h₄ : -(m - n)< r
    use (m + (s / 2))
    constructor
    define
    rcases abs_cases (m - (m + s / 2)) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith
    define
    rcases abs_cases (m + s / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith
    use ( ((n - r) + (m + s)) / 2)
    constructor
    define
    rcases abs_cases (m - (n - r + (m + s)) / 2) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith
    define
    rcases abs_cases ((n - r + (m + s)) / 2 - n) with ⟨h₅, h₆⟩ | ⟨h₅, h₆⟩
    rw[h₅]
    linarith
    rw[h₅]
    linarith

  end

  end Exercise_4_3_6

  theorem Exercise_4_3_7: transitive R ↔ comp (extension R) (extension R) ⊆ (extension R) := by
    constructor
    · -- mp
      rintro h ⟨m, n⟩ h₁
      rw[ext_def]
      rcases h₁ with ⟨o, h₂, h₃⟩
      rw[ext_def] at h₂
      rw[ext_def] at h₃
      exact h m o n h₂ h₃
    · -- mpr
      rintro h m n o h₁ h₂
      rw[←(ext_def R m n)] at h₁
      rw[←(ext_def R n o)] at h₂
      rw[←(ext_def R m o)]
      exact h (Exists.intro n (And.intro h₁ h₂))

  theorem Exercise_4_3_8: transitive R ↔ comp (extension R) (extension R) ⊆ (extension R) := by
    constructor
    · -- mp
      rintro h ⟨m, n⟩ h₁
      rw[ext_def]
      rcases h₁ with ⟨o, h₂, h₃⟩
      rw[ext_def] at h₂
      rw[ext_def] at h₃
      exact h m o n h₂ h₃
    · -- mpr
      rintro h m n o h₁ h₂
      rw[←(ext_def R m n)] at h₁
      rw[←(ext_def R n o)] at h₂
      rw[←(ext_def R m o)]
      exact h (Exists.intro n (And.intro h₁ h₂))


  variable {A B : Type}

  def iA := {(x, y): A × A | x = y}
  def iB := {(x, y): B × B | x = y}

  theorem Exercise_4_3_9_a (R : Rel A B): comp (extension R) (iA) = extension R := by
    apply Set.ext
    rintro ⟨m, n⟩
    constructor
    · -- mp
      rintro ⟨o, h₁, h₂⟩
      rw[← h₁] at h₂
      exact h₂
    · -- mpr
      rintro h; define at h
      use m
      constructor
      rfl
      exact h

  theorem Exercise_4_3_9_b (R : Rel A B): comp (iB) (extension R) = extension R := by
    apply Set.ext
    rintro ⟨m, n⟩
    constructor
    · -- mp
      rintro ⟨o, h₁, h₂⟩
      rw[h₂] at h₁
      exact h₁
    · -- mpr
      rintro h
      use n
      constructor
      exact h
      rfl


  variable (S: BinRel A)
  def D: Set A := Dom (extension S)
  def R': Set A := Ran (extension S)
  def iD: Set (A × A) := {(x, y): A × A | x ∈ D S ∧ y ∈ D S ∧ x = y}
  def iR': Set (A × A) := {(x, y): A × A | x ∈ R' S ∧ y ∈ R' S ∧ x = y}

  def G: Set (A × A)  := extension S

  theorem Exercise_4_3_10:
    iD S ⊆ comp (inv (extension S)) (extension S) ∧ iR' S ⊆ comp (extension S) (inv (extension S)) := by
    constructor
    · -- first prop
      rintro ⟨m, n⟩ ⟨h₁, h₂, h₃⟩
      rw[h₃]
      rcases h₂ with ⟨o, h₃⟩
      use o
      constructor
      exact h₃
      simp[inv]
      exact h₃
    · -- second prop
      rintro ⟨m , n⟩ ⟨h₁, h₂, h₃⟩
      rw[h₃]
      rcases h₂ with ⟨o, h₄⟩
      use o
      constructor
      simp[inv]
      exact h₄
      exact h₄

  theorem Exercise_4_3_11: reflexive R → (extension R) ⊆ comp (extension R) (extension R) := by
    rintro h ⟨m, n⟩ h₁
    use m
    constructor
    exact h m
    exact h₁

  theorem Exercise_4_3_12_a: reflexive R → reflexive (RelFromExt (inv (extension R))) := by
    rintro h m
    rw[RelFromExt_def]
    simp[inv]
    exact h m

  theorem Exercise_4_3_12_b: symmetric R → symmetric (RelFromExt (inv (extension R))) := by
    rintro h m n h₁
    define at h₁
    define
    exact h n m h₁

  theorem Exercise_4_3_12_c: transitive R → transitive (RelFromExt (inv (extension R))) := by
    rintro h m n o h₁ h₂
    define at h₁
    define at h₂
    define
    exact h o n m h₂ h₁

  variable (R1: BinRel A)
  variable (R2: BinRel A)

  theorem Exercise_4_3_13_a: reflexive R1 ∧ reflexive R2 → reflexive (RelFromExt ((extension R1) ∪ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ x
    apply Or.inl (h₁ x)

  theorem Exercise_4_3_13_b: symmetric R1 ∧ symmetric R2 → symmetric (RelFromExt ((extension R1) ∪ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ x y h₃
    define at h₃
    define
    rcases h₃ with h₃ | h₃
    apply Or.inl (h₁ x y h₃)
    apply Or.inr (h₂ x y h₃)

  /-
  Exercise_4_3_13_c: No. Counter example:
  R₁ = {(1, 2), (2, 5), (1, 5)}
  R₂ = {(0, 2), (2, 1), (0, 1)}
  (0, 2)  and (2, 5) ∈ R₁ ∪ R₂ But (0, 5) is not
  -/

  theorem Exercise_4_3_14_a: reflexive R1 ∧ reflexive R2 → reflexive (RelFromExt ((extension R1) ∩ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ x
    constructor
    exact h₁ x
    exact h₂ x

  theorem Exercise_4_3_14_b: reflexive R1 ∧ reflexive R2 → reflexive (RelFromExt ((extension R1) ∩ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ x
    constructor
    exact h₁ x
    exact h₂ x

  theorem Exercise_4_3_14_c: transitive R1 ∧ transitive R2 → transitive (RelFromExt ((extension R1) ∩ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ m n o ⟨h₃, h₄⟩ ⟨h₅, h₆⟩
    constructor
    exact h₁ m n o h₃ h₅
    exact h₂ m n o h₄ h₆

  /-
  Exercise_4_3_15_a: No. Counter example:
  R₁ ={(1, 2), (1, 1), (2, 2)}
  R₂ ={(1, 1), (2, 2)}
  -/

  theorem Exercise_4_3_15_b: symmetric R1 ∧ symmetric R2 → symmetric (RelFromExt ((extension R1) \ (extension R2))) := by
    rintro ⟨h₁, h₂⟩ m n ⟨h₃, h₄⟩
    define
    constructor
    exact h₁ m n h₃
    by_contra h'
    apply h₄
    exact h₂ n m h'

  /-
  Exercise 4_3_15_c: No. Counter example:
  R₁ = {(1, 2), (2, 3), (1, 3)}
  R₂ = {(2, 3), (1, 3)}
  -/

  theorem Exercise_4_3_16 (R S: BinRel A): reflexive R ∧ reflexive S → reflexive (RelFromExt (comp (extension R) (extension S))) := by
    rintro ⟨h₁, h₂⟩ m
    use m
    constructor
    exact h₂ m
    exact h₁ m

  theorem Exercise_4_3_17 (R S: BinRel A) (h₁: symmetric R) (h₂: symmetric S):
    symmetric (RelFromExt (comp (extension R) (extension S))) ↔ comp (extension R) (extension S) = comp (extension S) (extension R) := by
    constructor
    · -- mp
      rintro h₃
      apply Set.ext
      rintro ⟨m, n⟩
      constructor
      rintro ⟨o, h₄, h₅⟩
      rcases (h₃ m n (Exists.intro o (And.intro h₄ h₅))) with ⟨p, h₆, h₇⟩
      use p
      constructor
      exact h₁ p m h₇
      exact h₂ n p h₆
      rintro ⟨o, h₄, h₅⟩
      apply (h₃ n m)
      use o
      constructor
      exact h₂ o n h₅
      exact h₁ m o h₄
    · -- mpr
      rintro h₃ m n h₄
      rw[h₃] at h₄
      rcases h₄ with ⟨o, h₅, h₆⟩
      use o
      constructor
      exact h₂ o n h₆
      exact h₁ m o h₅

  theorem Exercise_4_3_18 (R S: BinRel A) (h₁: transitive R) (h₂: transitive S):
    comp (extension S) (extension R) ⊆ comp (extension R) (extension S) →  transitive (RelFromExt (comp (extension R) (extension S))):= by
    rintro h₃ m n o ⟨p, h₄, h₅⟩ ⟨q, h₆, h₇⟩
    define at h₃
    have h₃: (p, q) ∈ comp (extension R) (extension S):= h₃ (Exists.intro n (And.intro h₅ h₆))
    rcases h₃ with ⟨r, h₈, h₉⟩
    use r
    constructor
    exact h₂ m p r h₄ h₈
    exact h₁ r q o h₉ h₇

  /-
  Exercise_4_3_19_a
  You cannot be sure it is the same y. It could be a different y in Y for (X, Y) and (Y, Z)

  Exercise_4_3_19_b
  A = {1, 2, 3}
  R = {(1, 2), (2, 3), (3, 2) (1, 3)}
  X = {3}
  Y = {1 , 2}
  Z = {3}
  -/

  theorem Exercise_4_3_20 {A : Type} (R : BinRel A) (S : BinRel (Set A))
    (h : ∀ (X Y : Set A), S X Y ↔ X ≠ ∅ ∧ Y ≠ ∅ ∧
    ∀ (x y : A), x ∈ X → y ∈ Y → R x y) :
    transitive R → transitive S := by
    rintro h₁ m n o hs₁ hs₂
    rw[h] at hs₁
    rw[h] at hs₂
    have ⟨mNonEmpty, nNonEmpty, hMN⟩ := hs₁
    have ⟨nNonEmpty, oNonEmpty, hNO⟩ := hs₂
    rw[h]
    constructor
    exact mNonEmpty
    constructor
    exact oNonEmpty
    rw[← Set.nonempty_iff_ne_empty] at mNonEmpty
    rw[← Set.nonempty_iff_ne_empty] at nNonEmpty
    rcases mNonEmpty with ⟨p, hp⟩
    rcases nNonEmpty with ⟨q, hq⟩
    rintro a b ha hb
    apply h₁ a q b
    exact hMN a q ha hq
    exact hNO q b hq hb

  /-
  Empty set has to be excluded because AS∅ and ∅SB are
  vacously true but give no info as whether ASB is true
  -/

  theorem Exercise_4_3_21_a {A : Type} (R : BinRel A) (S : BinRel (Set A))
  (h : ∀ (X Y : Set A), S X Y ↔ ∀ (x : A), ∃ (y : A), x ∈ X → y ∈ Y ∧ R x y) :
  reflexive R → reflexive S := by
    rintro h₁ Q
    rw[h]
    rintro x
    use x
    rintro hx
    constructor
    exact hx
    exact h₁ x

  /-
  Exercise_4_3_21_b. Counter example
  A = {1, 2, 3}
  R = {(1, 2), (2, 1)}
  X = {1}
  Y = {1 , 3}
  (X, Y) ∈ S but (Y, X) ∉ S
  -/

  theorem Exercise_4_3_21_c {A : Type} (R : BinRel A) (S : BinRel (Set A))
  (h : ∀ (X Y : Set A), S X Y ↔ ∀ (x : A), x ∈ X → ∃ (y : A), y ∈ Y ∧ R x y) :
  transitive R → transitive S := by
    rintro h₁ Q P W h₂ h₃
    rw[h]
    rintro q hq
    rw[h] at h₂
    rcases (h₂ q hq) with ⟨p, hp, hqp⟩
    rw[h] at h₃
    rcases (h₃ p hp) with ⟨w, hw, hpw⟩
    use w
    constructor
    exact hw
    apply (h₁ q p w)
    exact hqp
    exact hpw

  /-
  Exercise_4_3_22. Incorrect. You cannot assume there is an element y such that
  xRy. What if R is the ∅? It is vacously reflexive and symmetric but not reflexive
  -/

  theorem Exercise_4_3_23 (U: Type) (A: Set U) (F: Set (Set U)):
  transitive (RelFromExt {(a, b) : U × U | a ∈ A ∧ b ∈ A ∧ ∀ (X: Set U), X ⊆ A \ {a, b} → X ∪ {a} ∈ F → X ∪ {b} ∈ F}) := by
    rintro x y z ⟨hx, hy, hxy⟩ ⟨hy, hz, hyz⟩
    apply And.intro hx
    apply And.intro hz
    rintro X' hX' hX'2
    by_cases xeqz: x = z
    rw[← xeqz]
    exact hX'2
    by_cases xeqy: x = y
    rw[xeqy] at hX'
    rw[xeqy] at hX'2
    exact hyz X' hX' hX'2
    by_cases yeqz: y = z
    rw[yeqz] at hxy
    exact hxy X' hX' hX'2
    by_cases yInX': y ∈ X'
    · -- y ∈ X'
      have h₁: ((X' ∪ {x}) \ {y}) ⊆ A \ {y, z} := by
        intro x' ⟨hx'1, hx'2⟩
        constructor
        rcases hx'1 with hx'1 | hx'1
        exact (hX' hx'1).1
        rw[hx'1]
        exact hx
        define; demorgan
        constructor
        exact hx'2
        rcases hx'1 with hx'1 | hx'1
        have hX' := (hX' hx'1).2
        define at hX'; demorgan at hX'
        exact hX'.2
        define at hx'1
        rw[hx'1]
        define
        exact xeqz
      have hyz := hyz ((X' ∪ {x}) \ {y}) h₁
      have tt : {y} ⊆ (X' ∪ {x}) := by
        rintro y' hy'
        rw[hy']
        apply Or.inl yInX'
      rw[Set.diff_union_of_subset tt] at hyz
      have hyz := hyz hX'2
      have h₂: ((X' ∪ {z}) \ {y}) ⊆ A \ {x, y} := by
        rintro p ⟨hx1 | hx1, hzz⟩
        constructor
        exact (hX' hx1).1
        define; demorgan
        constructor
        have hX' := (hX' hx1).2
        define at hX'
        demorgan at hX'
        exact hX'.1
        exact hzz
        constructor
        rw[hx1]
        exact hz
        define; demorgan
        constructor
        rw[hx1]
        rw[←ne_eq]
        symm
        exact xeqz
        exact hzz
      have hxy := hxy ((X' ∪ {z}) \ {y}) h₂
      have yyy: ((X' ∪ {z}) \ {y} ∪ {x} ∈ F)  = ((X' ∪ {x}) \ {y} ∪ {z} ∈ F) := by
        #check Set.diff_singleton_eq_self
        rw[Set.union_diff_distrib, Set.union_diff_distrib]
        have u: {z} \ {y} = {z} := Set.diff_singleton_eq_self yeqz
        rw[u]
        rw[←ne_eq] at xeqy
        have u: {x} \ {y} = {x} := Set.diff_singleton_eq_self xeqy.symm
        rw[u]
        have u: {z} ∪ {x} = {x} ∪ {z} := union_comm {z} {x}
        rw[Set.union_assoc, Set.union_assoc, u]
      rw[yyy] at hxy
      have hxy := hxy hyz
      have tt : {y} ⊆ (X' ∪ {z}) := by
        rintro y' hy'
        rw[hy']
        apply Or.inl yInX'
      rw[Set.diff_union_of_subset tt] at hxy
      exact hxy
    · -- y ∉ X'
      apply hyz
      intro x' hx'
      constructor
      exact (hX' hx').1
      by_contra h'
      apply yInX'
      rcases h' with h' | h'
      · -- x' = y
        rw[←h']
        exact hx'
      · -- x' ∈ {z}
        by_contra
        apply (hX' hx').2
        apply Or.inr h'
      apply hxy
      rintro x' hx'
      constructor
      exact (hX' hx').1
      by_contra h'
      apply yInX'
      rcases h' with h' | h'
      · -- x' = x
        by_contra
        apply (hX' hx').2
        apply Or.inl h'
      · -- x' = y
        define at h'
        rw[←h']
        exact hx'
      exact hX'2





















  end
