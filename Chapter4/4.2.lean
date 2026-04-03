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


end
