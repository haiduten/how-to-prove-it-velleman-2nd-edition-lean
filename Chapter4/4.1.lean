import HTPILib.Chap4

section
variable {U : Type}
variable (A B C D: (Set U))

theorem Example_4_1_3_1: A ×ˢ (B ∩ C) = (A ×ˢ B) ∩ (A ×ˢ C) := by
  apply Set.ext
  intro x
  constructor
  · intro ⟨h1, h2B, h2C⟩
    apply And.intro (And.intro h1 h2B) (And.intro h1 h2C)
  · rintro ⟨⟨h1A, h2A⟩, _, h2C⟩
    apply And.intro h1A (And.intro h2A h2C)
  done

theorem Example_4_1_3_2: A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  repeat
    intro h
    simp at h
    simp
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    apply Or.inl (And.intro hx hy)
    apply Or.inr (And.intro hx hy)

theorem Example_4_1_3_3: (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  repeat
    simp
    rintro hxA hyB hxC hyD
    apply And.intro (And.intro hxA hxC) (And.intro hyB hyD)

theorem Example_4_1_3_4: (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D) := by
  intro ⟨x, y⟩
  simp
  rintro (⟨hx, hy⟩ | ⟨hx, hy⟩)
  left; left; apply And.intro hx hy
  right; right; apply And.intro hx hy

theorem Example_4_1_3_5: ((A ×ˢ ∅) = (∅ ×ˢ A)) ∧ (((∅: Set U) ×ˢ A) = ∅) := by
  constructor
  · -- A ×ˢ ∅ = ∅ ×ˢ A
    apply Set.ext
    intro ⟨x, y⟩
    constructor
    rintro ⟨_ , hy⟩
    contradiction
    rintro ⟨hy, _⟩
    contradiction
  · -- ∅ ×ˢ A = ∅
    apply Set.ext
    intro ⟨x, y⟩
    constructor
    rintro ⟨hx, _⟩
    contradiction
    rintro h
    contradiction

theorem Example_4_1_4: (A ×ˢ B) = (B ×ˢ A) ↔ (A = ∅ ∨ B = ∅ ∨ A = B) := by
  constructor
  · -- A ×ˢ B = B ×ˢ A → A = ∅ ∨ B = ∅ ∨ A = B
    rintro h
    by_cases hA : A = ∅
    · left; exact hA
    · right
      by_cases hB : B = ∅
      · left; exact hB
      · right
        apply Set.ext
        intro x
        constructor
        · -- x ∈ A → x ∈ B
          rintro hxA
          push_neg at hB
          rw [Set.nonempty_def] at hB
          rcases hB with ⟨u, hu⟩
          rw[Set.ext_iff] at h
          exact ((h (x, u)).1 (And.intro hxA hu)).1
        · -- x ∈ B → x ∈ A
          rintro hxB
          push_neg at hA
          rw [Set.nonempty_def] at hA
          rcases hA with ⟨u, hu⟩
          rw[Set.ext_iff] at h
          exact ((h (x, u)).2 (And.intro hxB hu)).1
  · -- A = ∅ ∨ B = ∅ ∨ A = B → A ×ˢ B = B ×ˢ A
    rintro (h | h | h)
    repeat
      rw[h]
      simp
    rw[h]

/-
  Exercise 4_1_1_a
  {(George H. W. Bush, George Bush), (Yonko Radonov, Dimiter Radonov), ...}

  Exercise 4_1_1_b
  {(Chicago, Northwestern), (Berkeley, UC Berkeley), ...}

  Exercise 4_1_2_a
  {(Yonko, Sausalito), (Maria, Chicago), ...}

  Exercise 4_1_2_b
  {(San Fransico, 800,000), (Sofia, 3,000,000), ...}

  Exercise 4_1_3_a
  {(0, -2), (1, -2), ...}

  Exercise 4_1_3_b
  {(1, 0), (2, 1), ...}

  Exercise 4_1_3_c
  {(0, -2), (1, 1), ...}

  Exercise 4_1_4_d
  {(0, -2), (1, -2), ...}

  Exercise 4_1_5
  A = {1, 2, 3}
  B = {1, 4}
  C = {3, 4}
  D = {5}

  A ×ˢ (B ∩ C) = {(1, 4), (2, 4), (3, 4)}
  (A ×ˢ B) ∩ (A ×ˢ C) = {(1, 4), (2, 4), (3, 4)}

  A ×ˢ (B ∪ C) = {(1, 4), (2, 4), (3, 4), (1, 1), (2, 1), (3, 3), (1, 3), (2, 3), (3, 3)}
  (A ×ˢ B) ∪ (A ×ˢ C) = {(1, 4), (2, 4), (3, 4), (1, 1), (2, 1), (3, 3), (1, 3), (2, 3), (3, 3)}

  (A ×ˢ B) ∩ (C ×ˢ D) = ∅
  (A ∩ C) ×ˢ (B ∩ D) = ∅

  (A ×ˢ B) ∪ (C ×ˢ D) ⊆ (A ∪ C) ×ˢ (B ∪ D)
  (A ×ˢ B) ∪ (C ×ˢ D) =  {(1, 1), (2, 1), (3, 1), (1, 4), (2, 4), (3, 4), (3, 5), (4, 5)}
  (A ∪ C) ×ˢ (B ∪ D) = {(1, 1), (2, 1), (3, 1), (4, 1), (1, 4), (2, 4), (3, 4), (4, 4), (1, 5), (2, 5), (3, 5), (4, 5)}
-/

theorem Exercise_4_1_5_a: A ×ˢ (B ∪ C) = (A ×ˢ B) ∪ (A ×ˢ C) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  repeat
    intro h
    simp at h
    simp
    rcases h with ⟨hx, hy⟩ | ⟨hx, hy⟩
    apply Or.inl (And.intro hx hy)
    apply Or.inr (And.intro hx hy)

theorem Exercise_4_1_5_b: (A ×ˢ B) ∩ (C ×ˢ D) = (A ∩ C) ×ˢ (B ∩ D) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  repeat
    simp
    rintro hxA hyB hxC hyD
    apply And.intro (And.intro hxA hxC) (And.intro hyB hyD)

/-
  Exercise 4_1_6
  The cases are not exhaustive. We are missing cases x ∈ A ∧ y ∈ D and x ∈ C ∧ y ∈ B

  Exercise 4_1_7
  m x n
-/

theorem Exercise_4_1_8: A ×ˢ (B \ C) = (A ×ˢ B) \ (A ×ˢ C) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  · -- mp
    simp
    intro hxA hyB hyNotC
    apply And.intro (And.intro hxA hyB)
    intro _; exact hyNotC
  · -- mpr
    simp
    intro hxA hyB hyNotC
    constructor
    exact hxA
    constructor
    exact hyB; exact hyNotC hxA

theorem Exercise_4_1_9: A ×ˢ (B ∆ C) = (A ×ˢ B) ∆ (A ×ˢ C):= by
  apply Set.ext
  intro ⟨x ,y⟩
  simp
  constructor
  · -- mp
    rintro ⟨hx, ⟨hy1, hy2⟩ | ⟨hy1, hy2⟩⟩
    left; apply And.intro (And.intro hx hy1); simp; conditional; apply Or.inr hy2
    right; apply And.intro (And.intro hx hy1); simp; conditional; apply Or.inr hy2
  · -- mpr
    rintro (⟨⟨ha, hb⟩, notH⟩ | ⟨⟨ha, hb⟩, notH⟩)
    · apply And.intro ha
      simp at notH; conditional at notH
      rcases notH with notH | notH
      · contradiction
      · left; apply And.intro hb notH
    · apply And.intro ha
      simp at notH; conditional at notH
      rcases notH with notH | notH
      · contradiction
      · right; apply And.intro hb notH

theorem Exercise_4_1_10: (A \ C) ×ˢ (B \ D) ⊆ (A ×ˢ B) \ (C ×ˢ D):= by
  intro ⟨x, y⟩
  rintro ⟨⟨hx1, hx2⟩ , ⟨hy1, hy2⟩⟩
  apply And.intro (And.intro hx1 hy1)
  simp; conditional; apply Or.inl hx2

theorem Exercise_4_1_11: (A ×ˢ B) \ (C ×ˢ D) = (A ×ˢ (B \ D)) ∪ ((A \ C) ×ˢ B):= by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  · -- mp
    rintro ⟨⟨hx, hy⟩, notH⟩
    simp at notH; conditional at notH;
    rcases notH with notH | notH
    · right; apply And.intro (And.intro hx notH) hy
    · left; apply And.intro hx (And.intro hy notH)
  · -- mpr
    rintro (⟨hx, ⟨hy1, hy2⟩⟩ | ⟨⟨hx1, hx2⟩, hy⟩)
    · apply And.intro (And.intro hx hy1) _
      simp; conditional; apply Or.inr hy2
    · apply And.intro (And.intro hx1 hy) _
      simp; conditional; apply Or.inl hx2

theorem Exercise_4_1_12 (h: (A ×ˢ B) ∩ (C ×ˢ D) = ∅): (A ∩ C = ∅) ∨ (B ∩ D = ∅):= by
  by_cases h': (A ∩ C = ∅)
  · apply Or.inl h'
  · apply Or.inr
    push_neg at h'
    rcases h' with ⟨u, ⟨hA, hC⟩⟩
    rw[Set.ext_iff] at h
    by_contra h'; push_neg at h'
    rcases h' with ⟨v, ⟨hB, hD⟩⟩
    simp at h
    show False from (h u v hA hB hC) hD
end

section
variable {U : Type}
variable (B I: (Set U))
variable (A : U → Set U)

theorem Exercise_4_1_13 (h₀: I ≠ ∅): (⋂ i ∈ I, A i) ×ˢ B = ⋂ i ∈ I, A i ×ˢ B := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  · -- mp
    rintro ⟨hx, hy⟩; simp at hy; simp at hx
    simp
    intro i hI
    apply And.intro (hx i hI) hy
  · -- mpr
    rintro h; simp at h
    push_neg at h₀
    rcases h₀ with ⟨u, hu⟩
    have ⟨j, k⟩ := h u hu
    simp; symm
    apply And.intro k
    intro i hi
    exact (h i hi).1
-- I ≠ ∅ gets used in the reverse direction proving that y ∈ B
end

section
variable {U : Type}
variable (I: (Set U))
variable (A B: U → Set U)

theorem Exercise_4_1_14_a: ⋃ i ∈ I, (A i ×ˢ B i) ⊆ (⋃ i ∈ I, A i) ×ˢ (⋃ i ∈ I, B i) := by
  intro ⟨x, y⟩
  rintro h; simp at h
  rcases h with ⟨i, ⟨hA, hI, hB⟩⟩
  constructor
  repeat
    simp; use i

theorem Exercise_4_1_14_b: ⋃ i ∈ (I ×ˢ I), (A i.1 ×ˢ B i.2) = (⋃ i ∈ I, A i) ×ˢ (⋃ i ∈ I, B i) := by
  apply Set.ext
  intro ⟨x, y⟩
  constructor
  · -- mp
    rintro h; simp at h
    rcases h with ⟨i, ⟨ha, j, ⟨hi, hk⟩, hb⟩⟩
    simp
    constructor
    · use i
    · use j
  · -- mpr
    rintro ⟨hx, hy⟩; simp at hx; simp at hy
    rcases hx with ⟨i, ⟨hi, hA⟩⟩
    rcases hy with ⟨j, ⟨hj, hB⟩⟩
    simp
    use i
    apply And.intro hA
    use j
  done
end

/-
  Exercise 4_1_15
  The proof is incorrect. First we must prove A ⊆ C and then we must prove B ⊆ D.
  When proving A ⊆ C, we have no information about B other than A × B ⊆ C × D. So we cannot instantiate
  an arbitrary element b ∈ B. The theorem is not correct too. Suppose A and D are non-empty sets and B and C are empty sets
  then A ⊆ ∅. False
-/
