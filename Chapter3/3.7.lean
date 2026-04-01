import HTPILib.Chap3
namespace HTPI.Exercises

theorem Exercise_3_7_1 (U : Type) (F: Set (Set U)) :
  ∃! (A : Set U), F ⊆ 𝒫 A ∧ ∀ (B : Set U), F ⊆ 𝒫 B → A ⊆ B := by
  exists_unique
  · -- existence
    apply Exists.intro (⋃₀ F)
    apply And.intro
    · -- prove F ⊆ 𝒫 ⋃₀ F
      fix Y
      assume h1: Y ∈ F
      fix x
      assume h2: x ∈ Y
      define
      apply Exists.intro Y
      show Y ∈ F ∧ x ∈ Y from And.intro h1 h2
      done
    · -- prove ∀ (B : Set U), F ⊆ 𝒫 B → ⋃₀ F ⊆ B
      fix B
      assume h1: F ⊆ 𝒫 B
      fix x
      assume h2: x ∈ ⋃₀ F
      define at h2
      obtain (Q : Set U) (h3: Q ∈ F ∧ x ∈ Q) from h2
      show x ∈ B from h1 h3.left h3.right
      done
    done
  · -- uniqueness
    fix Y
    fix Z
    rintro h1 h2
    have h3: Y ⊆ Z := h1.right Z h2.left
    have h4: Z ⊆ Y := h2.right Y h1.left
    show Y = Z from Set.Subset.antisymm h3 h4
    done
  done

theorem Exercise_3_7_2 :
  ∃! (m : ℝ), 0 < m ∧ (∀ (x : ℝ),
    0 < x → (x / (x + 1) < m)) ∧ (∀ (y: ℝ), 0 < y → (∀ (z: ℝ), 0 < z → z / (z + 1) < y) → m ≤ y) := by
  exists_unique
  · -- existence
    apply Exists.intro 1
    apply And.intro zero_lt_one
    apply And.intro
    · -- prove ∀ x > 0, x / (x + 1) < 1
      fix x
      assume positiveX
      have xPlusOne := lt_add_one x
      have XPlusOnePos := lt_trans positiveX xPlusOne
      have xPlusOne := (div_lt_div_iff_of_pos_right XPlusOnePos).mpr xPlusOne
      rw[div_self (ne_of_gt XPlusOnePos)] at xPlusOne
      exact xPlusOne
    · -- prove 1 ≤ y
      fix y
      assume yPos
      assume ZCondition
      by_contra yLt1
      have yLt1 := not_le.mp yLt1
      rw[←(add_zero y)] at yLt1
      have OneMinusYPos := lt_sub_iff_add_lt'.mpr yLt1
      have OneMinusYNotZero := (ne_of_lt OneMinusYPos).symm
      have ZCondition := ZCondition (y / (1 - y)) (div_pos yPos OneMinusYPos)
      field_simp[OneMinusYNotZero] at ZCondition;
      simp at ZCondition
      done
    done
  · -- uniqueness
    fix Y; fix Z
    assume h1
    assume h2
    have h3 := h1.right.right Z h2.left h2.right.left
    have h4 := h2.right.right Y h1.left h1.right.left
    show Y = Z from eq_of_ge_of_le h4 h3
    done
  done

theorem Exercise_3_7_3 (U: Type) (A B: Set U):
  𝒫 (A \ B) \ (𝒫 A \ 𝒫 B) = {∅} := by
  apply Set.ext
  fix x
  apply Iff.intro
  · -- →
    assume h1
    define at h1
    have h2 := h1.left; have h3 := h1.right
    define at h2
    define at h3; demorgan at h3
    have xInPowerSetA: x ∈ 𝒫 A := by
      by_contra contra; define at contra; quant_neg at contra
      obtain (u: U) hu from contra
      conditional at hu
      have uInA := h2 hu.left
      define at uInA
      show False from hu.right uInA.left
      done
    disj_syll h3 xInPowerSetA
    define at h3
    by_contra contra
    define at contra
    have contra := Set.nonempty_iff_ne_empty.mpr contra
    define at contra
    obtain (a : U) ha from contra
    have h2 := h2 ha; define at h2
    have h3 := h3 ha
    show False from h2.right h3
    done
  · -- ←
    assume h1
    define at h1
    define
    apply And.intro
    · -- x ∈ 𝒫 (A \ B)
      fix y
      contrapos
      assume h2
      rw[h1]
      exact Set.notMem_empty y
      done
    · -- x ∉ 𝒫 A \ 𝒫 B
      rw[h1]
      define; demorgan
      or_right with h5
      fix y
      contrapos
      assume ignore
      exact Set.notMem_empty y
      done
    done
  done

theorem Exercise_3_7_4 (U: Type) (A B C: Set U): ((A ∆ C) ∩ (B ∆ C) = ∅ ↔ A ∩ B ⊆ C ∧ C ⊆ A ∪ B) ∧ ((A ∆ C) ∩ (B ∆ C) = ∅ ↔ A ∆ C ⊆ A ∆ B) := by
  have h: (A ∆ C) ∩ (B ∆ C) = ∅ ↔ A ∩ B ⊆ C ∧ C ⊆ A ∪ B := by
    rw[Set.eq_empty_iff_forall_notMem]
    simp
    constructor
    · -- prove (∀ x ∈ A ∆ C, x ∉ B ∆ C) → A ∩ B ⊆ C ∧ C ⊆ A ∪ B
      rintro h
      constructor
      · -- prove A ∩ B ⊆ C
        rintro x hx
        by_contra h'
        have h₁: x ∈ A ∆ C := by
          rw[Set.symmDiff_def]
          left
          rw[Set.mem_diff]
          constructor; exact hx.1; exact h'
        have h := h x h₁
        apply h
        rw[Set.symmDiff_def]
        left
        constructor; exact hx.2; exact h'
      · --  C ⊆ A ∪ B
        intro x hx
        by_cases ha: x ∈ A
        left; exact ha
        have hh: x ∈ A ∆ C := by
          right; constructor; exact hx; exact ha
        have h := h x hh
        by_contra h'
        apply h
        right; constructor; exact hx
        by_contra h''
        apply h'; right; exact h''
    · -- A ∩ B ⊆ C ∧ C ⊆ A ∪ B → ∀ x ∈ A ∆ C, x ∉ B ∆ C
      rintro ⟨h, h1⟩ x hx
      rw[Set.symmDiff_def, Set.mem_union, Set.mem_diff, Set.mem_diff]; demorgan
      constructor
      demorgan
      rcases hx with hx | hx
      left
      by_contra h'
      apply hx.2
      simp[Set.subset_def] at h
      exact h x hx.1 h'
      apply Or.inr hx.1
      demorgan
      rcases hx with hx | hx
      apply Or.inl hx.2
      right
      have h1:= h1 hx.1
      rcases h1 with h1 | h1
      have ⟨g, k⟩:= hx
      contradiction
      exact h1
  have h₁: A ∩ B ⊆ C ∧ C ⊆ A ∪ B ↔ A ∆ C ⊆ A ∆ B := by
    constructor
    rintro ⟨h₁, h₂⟩ x hx
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    left
    constructor; exact hx1
    by_contra h'
    apply hx2
    simp[Set.subset_def] at h₁
    exact h₁ x hx1 h'
    right
    constructor
    rcases h₂ hx1 with g | g
    contradiction; exact g; exact hx2
    rintro h₀
    constructor
    rintro x ⟨hA, hB⟩
    by_cases h': x ∈ C
    exact h'
    have hAC: x ∈ A ∆ C := by
      left
      apply (Set.mem_diff x).mpr
      constructor
      exact hA
      exact h'
    rcases h₀ hAC with ⟨_, hNb⟩ | ⟨_, hNA⟩
    contradiction
    contradiction
    rintro x hx
    by_cases h': x ∈ A
    apply Or.inl h'
    right
    have hAC: x ∈ A ∆ C := by
      right
      constructor
      exact hx
      exact h'
    rcases h₀ hAC with ⟨ha, _⟩ | ⟨b, _⟩
    contradiction
    exact b
    done
  constructor
  apply h
  rw[h]
  apply h₁


theorem Exercise_3_7_5 (U : Type) (F : Set (Set U))
    (h1 : 𝒫 (⋃₀ F) ⊆ ⋃₀ {𝒫 A | A ∈ F}) :
    ∃ (A : Set U), A ∈ F ∧ ∀ (B : Set U), B ∈ F → B ⊆ A := by
  define at h1;
  have h2: ⋃₀ F ∈ 𝒫 ⋃₀ F := by
    rw[Set.mem_powerset_iff]
    done
  have h3 := h1 h2; define at h3
  obtain i hi from h3; define: i ∈ {x : Set (Set U) | ∃ A ∈ F, 𝒫 A = x} at hi
  obtain G hG from hi.left
  apply Exists.intro G
  apply And.intro hG.left
  have h4 := hi.right
  rw[hG.right.symm] at h4
  rw[Set.mem_powerset_iff] at h4
  fix B
  assume hB
  have h6: B ⊆ ⋃₀ F := Set.subset_sUnion_of_mem hB
  show B ⊆ G from Set.Subset.trans h6 h4
  done
