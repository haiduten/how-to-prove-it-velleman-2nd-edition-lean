import HTPILib.Chap4

/-
  Example 4.2.4
  1. E⁻¹ = a course enrolled by some student. If Martin takes Math, then it would be (Math, Martin)
  2. E ∘ L⁻¹ = the dorms that have an occupant enrolled in a a couse. If Martin lives in Hall A and
  is enrolled in math, then an element would be (Hall A, Math)
  3. E⁻¹ ∘ E = pair of students enrolled in same course. Thus (Martin, Martin)
  4. E ∘ E⁻¹ = pair of courses with a common student. Thus, (Math, Math)
  5. T ∘ (E ∘ L⁻¹) a pair of dorm and professor where occupants of the dorm are taught by that professor.
  6. (T ∘ E) ∘ L⁻¹ a pair of dorm and professor where occupatns of the dorm are tauge by that professor
-/

section
def Dom {A B : Type} (R : Set (A × B)) : Set A :=
  {a : A | ∃ (b : B), (a, b) ∈ R}

def Ran {A B : Type} (R : Set (A × B)) : Set B :=
  {b : B | ∃ (a : A), (a, b) ∈ R}

def inv {A B : Type} (R : Set (A × B)) : Set (B × A) :=
  {(b, a) : B × A | (a, b) ∈ R}

def comp {A B C : Type}
    (S : Set (B × C)) (R : Set (A × B)) : Set (A × C) :=
  {(a, c) : A × C | ∃ (x : B), (a, x) ∈ R ∧ (x, c) ∈ S}

variable {U : Type}
variable (A B C D : (Set U))
variable (R: Set (A × B))
variable (S: Set (B × C))
variable (T: Set (C × D))

theorem Example_4_2_5_1: inv (inv R) = R := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  · -- mp
    rintro h
    rw[inv] at h; simp at h
    rw[inv] at h; simp at h
    exact h
  · -- mpr
    rintro h
    rw[inv]; simp
    rw[inv]; simp
    exact h

theorem Example_4_2_5_2: Dom (inv R) = Ran R := by
  apply Set.ext
  intro y
  constructor
  · -- mp
    rintro h; rw[Dom] at h;
    rcases h with ⟨x, hx⟩
    rw[inv] at hx; simp at hx
    rw[Ran]; use x
  · --
    rintro h;
    rcases h with ⟨x, hx⟩
    rw[Dom]
    use x
    rw[inv]; simp
    exact hx

theorem Example_4_2_5_3: Ran (inv R) = Dom R := by
  apply Set.ext
  intro p
  constructor
  · -- mp
    rintro h
    rcases h with ⟨q, h₁⟩;
    rw[inv] at h₁; simp at h₁
    rw[Dom]; use q
  · -- mpr
    rintro h
    rw[Dom] at h
    rcases h with ⟨q, h₁⟩
    rw[Ran]; use q
    rw[inv]
    exact h₁

theorem Example_4_2_5_4: comp T (comp S R) = comp (comp T S) R := by
  apply Set.ext
  rintro ⟨p, q⟩
  constructor
  · -- mp
    rintro ⟨r, ⟨h₁, h₂⟩⟩
    rcases h₁ with ⟨u , ⟨h₃, h4⟩⟩
    use u;
    apply And.intro h₃
    use r
  · -- mpr
    rintro ⟨r, ⟨h₁, h₂⟩⟩
    rcases h₂ with ⟨u , ⟨h₃, h4⟩⟩
    use u; symm
    apply And.intro h4
    use r

theorem Example_4_2_5_5: inv (comp S R) = comp (inv R) (inv S) := by
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  · -- mp
    rintro h
    rw[inv] at h; simp at h
    rcases h with ⟨u, h₁, h₂⟩
    use u
    apply And.intro h₂ h₁
  · -- mpr
    rintro h
    rcases h with ⟨u, h₁, h₂⟩
    rw[inv] at h₁; simp at h₁
    rw[inv] at h₂; simp at h₂
    rw[inv]; simp;
    use u

/-
  Exercise 4_2_1_a
  Domain: (mom, dad, ...)
  Range: (viktor, april)

  Exercise 4_2_1_b
  Domain: (-1, 0, 1, ...)
  Range: (1, 2, 3, ....)

  Exercise 4_2_2_a
  Domain: (yonko, krum)
  range: (maria, rali)

  Exercise 4_2_2_b
  Domain: (0, 1, 2, ....)
  Range: (0, 0.5...)

  Exercise 4_2_3_a
  The pair of students who live in same dorm

  Exercise 4_2_3_b
  Pair of student and college course in which
  the college course has students in the
  same dorm of the student

  Exercise 4_2_4_a
  pair of student and day where student is enrolled
  in a course that meets that day

  Exercise 4_2_4_b
  pair of professor and day where the professor
  teaches a course that meets that day

  Exercise 4_2_5_a
  {(1, 4), (1, 5), (1, 6), (2 , 4), (3, 6)}

  Exercise 4_2_5_b
  {(5, 5), (5, 6), (6, 5), (6, 6), (4, 4)}

  Exercise 4_2_6_a
  {(1, 4), (3, 5), (3, 4)}

  Exercise 4_2_6_b
  {(4, 1), (4, 3), (5, 3)}
-/

theorem Exercise_4_2_7_a: Dom (inv R) = Ran R := by
  apply Set.ext
  intro y
  constructor
  · -- mp
    rintro h; rw[Dom] at h;
    rcases h with ⟨x, hx⟩
    rw[inv] at hx; simp at hx
    rw[Ran]; use x
  · --
    rintro h;
    rcases h with ⟨x, hx⟩
    rw[Dom]
    use x
    rw[inv]; simp
    exact hx

theorem Exercise_4_2_7_b: Ran (inv R) = Dom R := by
  rw [← Example_4_2_5_2]
  rw [Example_4_2_5_1]

theorem Exercise_4_2_7_c: comp T (comp S R) = comp (comp T S) R := by
  apply Set.ext
  rintro ⟨p, q⟩
  constructor
  · -- mp
    rintro ⟨r, ⟨h₁, h₂⟩⟩
    rcases h₁ with ⟨u , ⟨h₃, h4⟩⟩
    use u;
    apply And.intro h₃
    use r
  · -- mpr
    rintro ⟨r, ⟨h₁, h₂⟩⟩
    rcases h₂ with ⟨u , ⟨h₃, h4⟩⟩
    use u; symm
    apply And.intro h4
    use r

theorem Exercise_4_2_7_d: inv (comp S R) = comp (inv R) (inv S) := by
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  · -- mp
    rintro h
    rw[inv] at h; simp at h
    rcases h with ⟨u, h₁, h₂⟩
    use u
    apply And.intro h₂ h₁
  · -- mpr
    rintro h
    rcases h with ⟨u, h₁, h₂⟩
    rw[inv] at h₁; simp at h₁
    rw[inv] at h₂; simp at h₂
    rw[inv]; simp;
    use u

/-
  Exercise_4_2_8
  (a , b) ∈ E ∘ E = a is the enemy of b's enemy
  (a , b) ∈ F = a is b's friend

  E ∘ E ⊆ F
-/

theorem Exercise_4_2_9_a: Dom (comp S R) ⊆ Dom R:= by
  rintro m h
  rcases h with ⟨n, h₁⟩
  rcases h₁ with ⟨o, h₂, h₂⟩
  use o

theorem Exercise_4_2_9_b (h: Ran R ⊆ Dom S): Dom (comp S R) = Dom R := by
  apply Set.ext
  intro m
  constructor
  · -- mp
    rintro h
    rcases h with ⟨n, ⟨o, ho1, ho2⟩⟩
    use o
  · -- mpr
    rintro h₁
    rcases h₁ with ⟨n, hn⟩
    rcases h (Exists.intro m hn) with ⟨o, ho⟩
    use o;
    use n

theorem Exercise_4_2_9_c: Ran (comp S R) ⊆ Ran S := by
  intro m
  rintro h
  rcases h with ⟨n, ⟨o, ho1, ho2⟩⟩
  use o

end

section

variable {U : Type}
variable (A B: (Set U))
variable (R: Set (A × B))
variable (S: Set (A × B))

theorem Exercise_4_2_10_a: R ⊆ (Dom R) ×ˢ (Ran R):= by
  rintro ⟨a, b⟩  h
  constructor
  use b
  use a

theorem Exercise_4_2_10_b (h: R ⊆ S): inv R ⊆ inv S := by
  rintro ⟨a, b⟩ h₁
  define at h₁
  define
  exact h h₁

theorem Exercise_4_2_10_c: inv (R ∪ S) = inv R ∪ (inv S):= by
  apply Set.ext
  rintro ⟨a, b⟩
  constructor
  · -- mp
    rintro h; define at h
    rcases h with h | h
    apply Or.inl h
    apply Or.inr h
  · -- mpr
    rintro (h | h)
    apply Or.inl h
    apply Or.inr h
end

theorem Exercise_4_2_11 (U : Type) (A B C: Set U) (R: Set (A × B)) (S: Set (B × C)):
  comp S R = ∅ ↔ Ran R ∩ (Dom S) = ∅:= by
  contrapose
  push_neg
  constructor
  · -- mp
    rintro ⟨⟨m, n⟩, ⟨o, h₁, h₂⟩⟩
    use o
    constructor
    use m
    use n
  · -- mpr
    rintro ⟨m, ⟨⟨n, h₁⟩, ⟨o, h₂⟩⟩⟩
    use (n, o);
    use m

section
variable {U : Type}
variable (A B C: (Set U))
variable (R: Set (A × B))
variable (S: Set (B × C))
variable (T: Set (B × C))

theorem Exercise_4_2_12_a: (comp S R) \ (comp T R) ⊆ comp (S \ T) R:= by
  rintro ⟨m, n⟩ ⟨⟨o, h₁, h₂⟩, h₃⟩
  use o
  apply And.intro h₁ (And.intro h₂ _)
  by_contra h'
  apply h₃
  use o

/-
Exercise_4_2_12_b
You cannot conlude (a, c) ∉ T ∘ R. In order to do that we must show that
there is no element in B such that (a, b) ∈ R and (b, c) ∈ T. So far we
just showed it for one element. We must prove it for all
-/

/-
Exercise_4_2_12_c
Let R = {(1, 1), (1, 7)}
Let S = {(1, 3)}
Let T = {(7, 3)}
-/

section
variable {U : Type}
variable (A B C:  (Set U))
variable (R: Set (A × B))
variable (S: Set (A × B))
variable (T: Set (B × C))

theorem Exercise_4_2_13_a: (R ∩ S = ∅) → (inv R) ∩ (inv S) = ∅ := by
  contrapose
  push_neg
  rintro ⟨⟨m, n⟩, h₁, h₂⟩
  define at h₁; define at h₂
  use (n, m)
  apply And.intro h₁ h₂

/-
Exercise_4_2_13_b
Let R be a pair of natural numbers st (n, n + 1) {(2, 3), (3, 4), ...}
Let S be a pair of natural numbers st (n, n - 1) {(2, 1), (3, 2), ...}
Let T be a pair of a natural number and boolean indicating if it is prime
{(3, true), (4, false), ...}

Exercise_4_2_13_c
Let R = {(1, 1), (2, 2)}
Let S = {(2, 2), (3, 3)}
Let T = {(1, 1), (3, 3)}
-/
end

section
variable {U : Type}
variable (A B C:  (Set U))
variable (R: Set (A × B))
variable (S: Set (B × C))
variable (T: Set (B × C))

theorem Exercise_4_2_14_a: S ⊆ T → (comp S R) ⊆ comp T  R := by
  rintro h ⟨m, n⟩ ⟨o, h₁, h₂⟩
  use o
  apply And.intro h₁ (h h₂)

theorem Exercise_4_2_14_b: comp (S ∩ T) R ⊆ (comp S R) ∩ (comp T R) := by
  rintro ⟨m, n⟩ ⟨o, h₁, h₂, h₃⟩
  constructor
  repeat
  use o

/-
Exercise 4_2_14_c
S ∘ R ∩ T ∘ R ⊄ (S ∩ T) ∘ R
Let R = {(1, 1), (1, 2)}
Let S = {(2, 9)}
Let T = {(1, 9)}
-/

theorem Exercise_4_2_14_d: comp (S ∪ T) R = (comp S R) ∪ (comp T R) := by
  apply Set.ext
  rintro ⟨m, n⟩
  constructor
  · -- mp
    rintro ⟨u, h₁, h₂ | h₂⟩
    · -- case 1
      left
      use u
    · -- case 2
      right
      use u
  · -- mpr
    rintro (⟨u, h₁, h₂⟩ | ⟨u, h₁, h₂⟩)
    · -- case 1
      use u;
      apply And.intro h₁ (Or.inl h₂)
    · -- case 2
      use u
      apply And.intro h₁ (Or.inr h₂)
end

theorem Exercise_4_2_15 (U: Type) (A B C D: Set U) (R S : Set (U × U)) (h₁: R ⊆ (A ×ˢ B)) (h₂: S ⊆ (C ×ˢ D)):
  (∃ (E: Set U), R ⊆ (A ×ˢ E) ∧ S ⊆ (E ×ˢ D)) ∧
  (∀ (E: Set U), ∀ (E': Set U), R ⊆ (A ×ˢ E) ∧ S ⊆ (E ×ˢ D) ∧ R ⊆ (A ×ˢ E') ∧ S ⊆ (E' ×ˢ D) →
  {(a, c) : U × U | ∃ b ∈ E,  (a, b) ∈ R ∧ (b ,c) ∈ S} = {(a, c) : U × U | ∃ b ∈ E', (a, b) ∈ R ∧ (b ,c) ∈ S}):= by
  constructor
  · -- existence
    use (B ∪ C)
    constructor
    · -- prove for R
      intro ⟨m, n⟩ h
      constructor
      exact (h₁ h).left
      apply Or.inl (h₁ h).right
    · -- prove for S
      intro ⟨m, n⟩ h
      constructor
      apply Or.inr (h₂ h).left
      exact (h₂ h).right
  · -- same composiiton
    rintro  E E' ⟨h₃, h₄, h₅, h₆⟩
    apply Set.ext
    rintro ⟨a, c⟩
    constructor
    · -- →
      rintro ⟨b, h₇, h₈, h₉⟩
      use b
      constructor
      exact (h₅ h₈).right
      apply And.intro h₈ h₉
    · -- →
      rintro ⟨b, h₇, h₈, h₉⟩
      use b
      constructor
      exact (h₃ h₈).right
      apply And.intro h₈ h₉

