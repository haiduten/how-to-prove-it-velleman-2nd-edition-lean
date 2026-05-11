import HTPILib.Chap5
namespace HTPI.Exercises

/-
Example 5.1.2
1. Yes
2. No
3. Yes
4. No
5. Yes
6. Yes
7. Yes
-/


theorem Example_5_1_5 (A B C: Type) (f: A → B) (g: B → C):
    is_func_graph (comp (graph g) (graph f)) := by
  rintro x
  exists_unique
  use (g (f x))
  define
  use f x
  constructor
  rw[graph_def]
  rw[graph_def]
  rintro y z hy hz
  rcases hy with ⟨u, hu, hu'⟩
  rcases hz with ⟨q, hq, hq'⟩
  rw[graph_def] at hu
  rw[graph_def] at hq
  rw[hq] at hu
  rw[hu] at hq'
  rw[graph_def] at hu'
  rw[graph_def] at hq'
  rw[← hq', ← hu']

theorem Example_5_1_5_other(A B C: Type) (f: A → B) (g: B → C):
    ∃ (h : A → C), graph h = (comp (graph g) (graph f)) := by
  use fun (x : A) => g (f x)
  apply Set.ext
  rintro ⟨x, y⟩
  constructor
  rintro h
  rw[graph_def] at h
  use f x
  constructor
  rfl
  exact h
  rintro h
  rcases h with ⟨u, hu, hu'⟩
  rw[graph_def]
  rw[graph_def] at hu
  rw[graph_def] at hu'
  rw[hu]
  exact hu'

/-
Exercise_5_1_1
(a) yes
(b) no
(c) yes

Exercise_5_1_2
(a) no
(b) no, yes
(c) yes

Exercise_5_1_3
(a) b, b, a
(b)  0
(c) 3, -4

Exercise_5_1_4
(a) Rome
(b) {2}
(c) (3, 1)

Exercise_5_1_5
L ∘ H  = the identity function of countries
H ∘ L = cities to the capital city of the country where the city is in

Exercise_5_1_6
(f ∘ g) (x) = 1 / ((2x - 1)^2 + 2)
(g ∘ f) (x) = 2 * (1 / (x^2 + 2)) -1
-/


def restrictFunction {A B: Type}  (f : A → B) (C: Set A) : {x : A // x ∈ C} → B :=
  fun  c => f c.1

theorem Exercise_5_1_7_a (A B: Type) (f: A → B) (C: Set A)
    (res: Set (A × B)) (h: res = {(a, b) : A × B| (a, b) ∈ graph f ∧ a ∈ C}):
    (∀ x ∈ C, ∃! (y : B), (x, y) ∈  res) ∧ ∀ c ∈ C, (c, f c) ∈ res := by
  constructor
  rintro c hc
  simp[h, graph_def]
  use f c
  constructor
  simp
  exact hc
  rintro y hy
  exact hy.1.symm
  rintro x hc
  simp[h, graph_def]
  exact hc

theorem Exercise_5_1_7_b (A B: Type) (f: A → B) (C: Set A) (g: {x : A // x ∈ C} → B):
     g = (restrictFunction f C) ↔ graph g ⊆ graph (restrictFunction f C) := by
  constructor
  rintro h
  rw[h]
  rintro h
  apply funext
  rintro x
  define at h
  have h': (x, g x) ∈ graph g := by
    rw[graph_def]
  have h := h h'
  rw[graph_def] at h
  exact h.symm

theorem Exercise_5_1_7_c (h: ℝ → ℝ) (g: ℤ → ℝ)
    (hh: h = fun x => 2 * x + 3)
    (hg: g = fun (x: ℤ)  => 2 * x + (3: ℝ)):
    g =  fun z : ℤ => restrictFunction h Set.univ ⟨(z : ℝ), by simp⟩:= by
  apply funext
  rintro z
  rw[hg]
  simp
  rw[hh, restrictFunction]
  done

theorem Exercise_5_1_8 (A B: Type) (f: A → B)
    (g: Set (A × B)) (hg: g ⊆ graph f):
    ∃ A': Set A, ∀ x ∈ A', ∃! (y : B), (x, y) ∈ {(a, b): A × B | (a, b) ∈ g ∧ a ∈ A' } := by
  use Dom g
  rintro x hx
  use f x
  constructor
  simp
  constructor
  rcases hx with ⟨y , hy⟩
  have hg := hg hy
  rw[graph_def] at hg
  rw[hg]
  exact hy
  exact hx
  rintro y hy
  simp at hy
  have hg := hg hy.1
  rw[graph_def] at hg
  exact hg.symm

theorem Exercise_5_1_9 (U: Type) (A A' B: Set U) (hA: A ⊆ A') (hB: B ≠ ∅)
    (f : Set (U × U)) (hf': ∀ x y: U, (x, y) ∈ f ↔ x ∈ A ∧ y ∈ B) (hf: ∀ x ∈ A, ∃! y ∈ B, (x, y) ∈ f):
    ∃ g : Set (U × U), ∀ x ∈ A', ∃! y ∈ B, (x, y) ∈ g ∧ f ⊆ g := by
  push_neg at hB
  rcases hB with ⟨b', hb'⟩
  use {p | p.1 ∈ A ∧ p ∈ f ∨ (p.1 ∈ (A' \ A) ∧ p.2 = b') }
  rintro x hx
  by_cases hx': x ∈ A
  rcases hf x hx' with ⟨b, ⟨hb, hb'⟩ , hb''⟩
  use b
  simp
  constructor
  constructor
  exact hb
  constructor
  left
  apply And.intro hx' hb'
  rintro ⟨m ,n⟩ hmn
  simp
  constructor
  constructor
  apply ((hf' m n).mp hmn).1
  exact hmn
  rintro y hy hy' hy''
  have hy'' := hy'' hb'
  simp at hy''
  rcases hy' with (hy' | hy')
  rcases hy'' with (hy'' | hy'')
  apply hb''
  apply And.intro hy hy'.2
  contradict hy'.1
  apply hy''.1.2
  rcases hy'' with (hy'' | hy'')
  contradict hy''.1
  apply hy'.1.2
  rw[hy'.2, hy''.2]
  use b'
  simp
  constructor
  constructor
  exact hb'
  constructor
  right
  apply And.intro hx hx'
  rintro ⟨m, n⟩ hmn
  simp
  left
  constructor
  apply ((hf' m n).mp hmn).1
  exact hmn
  rintro y hy hy' hy''
  rcases hy' with (hy' | hy')
  have hy'' := hy'' hy'.2
  simp at hy''
  rcases hy'' with (hy'' | hy'')
  contradict hx'
  apply hy''.1
  apply hy''.2
  apply hy'.2

theorem Exercise_5_1_10 (A B: Type) (f g: A → B) (h: graph f ≠  graph g):
    ¬is_func_graph ((graph f) ∆ (graph g)) := by
  simp[Set.ext_iff] at h
  push_neg at h
  rcases h with ⟨x, y, (hmn | hmn)⟩
  simp[is_func_graph]
  use x
  by_contra h'
  rcases h' with ⟨y' , hy', hy''⟩
  have hy'' := hy'' (g x)
  simp at hy''
  have h: (x, g x) ∈ graph f ∆ graph g  := by
    define
    right
    constructor
    rfl
    define
