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
  have hy''' := hy'' (g x)
  simp at hy'''
  have h: (x, g x) ∈ graph f ∆ graph g  := by
    define
    right
    constructor
    rfl
    define
    rcases hmn with ⟨hmn1, hmn2⟩
    simp[graph] at hmn1
    simp[graph] at hmn2
    push_neg
    push_neg at hmn2
    symm
    rw[hmn1]
    exact hmn2
  have hy''' := hy''' h
  have h': (x, f x) ∈ graph f ∆ graph g := by
    define
    left
    constructor
    rfl
    rcases hmn with ⟨hmn1, hmn2⟩
    simp[graph] at hmn1
    rw[← hmn1] at hmn2
    exact hmn2
  have hy'' := hy'' (f x) h'
  rw[←  hy'''] at hy''
  rcases hmn with ⟨hmn1, hmn2⟩
  simp[graph] at hmn1
  simp[graph] at hmn2
  push_neg at hmn2
  contradict hmn2
  rw[← hmn1]
  exact hy''.symm
  simp[is_func_graph]
  use x
  by_contra h'
  rcases h' with ⟨y' , hy', hy''⟩
  have hy''' := hy'' (f x)
  simp at hy'''
  have h: (x, f x) ∈ graph f ∆ graph g  := by
    define
    left
    constructor
    rfl
    define
    rcases hmn with ⟨hmn1, hmn2⟩
    simp[graph] at hmn1
    simp[graph] at hmn2
    push_neg
    push_neg at hmn1
    symm
    rw[hmn2]
    exact hmn1
  have hy''' := hy''' h
  have h': (x, g x) ∈ graph f ∆ graph g := by
    define
    right
    constructor
    rfl
    rcases hmn with ⟨hmn1, hmn2⟩
    simp[graph] at hmn1
    simp[graph] at hmn2
    simp[graph]
    push_neg
    push_neg at hmn1
    rw[hmn2]
    exact hmn1
  have hy'' := hy'' (g x) h'
  rw[←  hy'''] at hy''
  rcases hmn with ⟨hmn1, hmn2⟩
  simp[graph] at hmn1
  simp[graph] at hmn2
  push_neg at hmn1
  contradict hmn1
  rw[hmn2] at hy''
  exact hy''.symm

theorem Exercise_5_1_11 (A: Type):
    ∃! (X: Set (A × A)), equiv_rel (RelFromExt X) ∧ is_func_graph X := by
  let iA := { (x, y): A × A | x = y }
  use iA
  simp
  constructor
  constructor
  constructor
  rintro x
  simp[RelFromExt]
  rfl
  constructor
  rintro x y hxy
  simp[RelFromExt] at hxy
  simp[RelFromExt]
  define
  define at hxy
  exact hxy.symm
  rintro x y z hxy hyz
  simp[RelFromExt] at hxy
  simp[RelFromExt] at hyz
  simp[RelFromExt]
  define at hxy
  define at hyz
  define
  rw[← hyz]
  exact hxy
  simp[is_func_graph]
  rintro x
  exists_unique
  use x
  define
  rfl
  rintro y z hy hz
  define at hy
  define at hz
  rw[← hy]
  exact hz
  rintro Y hY hY'
  apply Set.ext
  rintro ⟨m ,n⟩
  constructor
  rintro hx
  define
  have h: (m ,m) ∈ Y := by
    rcases hY with ⟨refl, _, _⟩
    exact refl m
  simp[is_func_graph] at hY'
  rcases hY' m with ⟨u , _, hh⟩
  have t := hh m h
  have t' := hh n hx
  rw[t']
  exact t
  rintro h
  define at h
  rw[h]
  rcases hY with ⟨refl, _, _⟩
  exact refl n

theorem Exercise_5_1_12_a (U : Type) (A B C: Set U) (f g: Set (U × U))
    (hf: ∀ x ∈ A, ∃! y ∈ C, (x, y) ∈ f)
    (hg: ∀ x ∈ B, ∃! y ∈ C, (x, y) ∈ g)
    (hf': ∀ x y: U, (x, y) ∈ f ↔ x ∈ A ∧ y ∈ C)
    (hg': ∀ x y: U, (x, y) ∈ g ↔ x ∈ B ∧ y ∈ C)
    (hAB: A ∩ B = ∅):
    ∀ x ∈ A ∪ B, ∃! y ∈  C, (x, y) ∈ (f ∪ g) := by
  rintro x (hx | hx)
  rcases hf x hx with ⟨fx, ⟨h, h'⟩ , h''⟩
  use fx
  simp
  constructor
  constructor
  exact h
  left
  exact h'
  rintro y hy (hy' | hy')
  apply h''
  apply And.intro hy hy'
  contradict hAB
  push_neg
  use x
  constructor
  apply ((hf' x fx).mp h').1
  apply ((hg' x y).mp hy').1
  rcases hg x hx with ⟨gx, ⟨h, h'⟩ , h''⟩
  use gx
  simp
  constructor
  constructor
  exact h
  right
  exact h'
  rintro y hy (hy' | hy')
  contradict hAB
  push_neg
  use x
  constructor
  apply ((hf' x y).mp hy').1
  apply ((hg' x gx).mp h').1
  apply h''
  constructor
  exact hy
  exact hy'

theorem Exercise_5_1_12_b (U : Type) (A B C: Set U) (f g: Set (U × U))
    (hf: ∀ x ∈ A, ∃! y ∈ C, (x, y) ∈ f)
    (hg: ∀ x ∈ B, ∃! y ∈ C, (x, y) ∈ g)
    (hf': ∀ x y: U, (x, y) ∈ f ↔ x ∈ A ∧ y ∈ C)
    (hg': ∀ x y: U, (x, y) ∈ g ↔ x ∈ B ∧ y ∈ C):
    (∀ x ∈ A ∪ B, ∃! y ∈  C, (x, y) ∈ (f ∪ g)) ↔ f ∩ ((A ∩ B) ×ˢ C) = g ∩ ((A ∩ B) ×ˢ C) := by
  constructor
  rintro h
  apply Set.ext
  rintro ⟨m , n⟩
  constructor
  rintro hmn
  constructor
  rcases hmn with ⟨hmn, ⟨ hmn1, hmn1'⟩ , hmn2⟩
  have t: m ∈ A ∪ B := by
    left
    apply hmn1
  rcases h m t with ⟨u, ⟨hu, hu1⟩ , hu'⟩
  rcases hf m  hmn1 with ⟨p, ⟨hp, hp'⟩ , hp''⟩
  rcases hg m  hmn1' with ⟨q, ⟨hq, hq'⟩ , hq''⟩
  simp at hu'
  have t': (m, p) ∈ f ∨ (m, p) ∈ g := by
    left
    exact hp'
  have t'': (m, q) ∈ f ∨ (m, q) ∈ g := by
    right
    exact hq'
  have t1 := hu' p hp t'
  have t2 := hu' q hq t''
  rcases hf m hmn1 with ⟨l, _, hl⟩
  simp at hl
  have hp := hl p hp hp'
  have hn := hl n hmn2 hmn
  rw[t2, ←t1, hp, ← hn] at hq'
  exact hq'
  exact hmn.2
  rintro ⟨hmn, ⟨ hmn1, hmn1'⟩ , hmn2⟩
  constructor
  rcases hf m  hmn1 with ⟨p, ⟨hp, hp'⟩ , hp''⟩
  have t: m ∈ A ∪ B := by
    left
    apply hmn1
  rcases h m t with ⟨u, ⟨hu, hu1⟩ , hu'⟩
  have t': (m, p) ∈ f ∨ (m, p) ∈ g := by
    left
    exact hp'
  have t'': (m, n) ∈ f ∨ (m, n) ∈ g := by
    right
    exact hmn
  simp at hu'
  have t1 := hu' p hp t'
  have t2 := hu' n hmn2 t''
  rw[t2, ← t1]
  exact hp'
  constructor
  constructor
  exact hmn1
  exact hmn1'
  exact hmn2
  rintro h x (hx | hx)
  rcases hf x hx with ⟨u, ⟨hu, hu'⟩, hu2⟩
  use u
  simp
  constructor
  constructor
  exact hu
  left
  exact hu'
  rintro y hy (hy' | hy')
  apply hu2
  apply And.intro hy hy'
  have t: (x, u ) ∈ f ∩ (A ∩ B) ×ˢ C := by
    constructor
    exact hu'
    constructor
    constructor
    exact ((hf' x u).mp hu').1
    exact ((hg' x y).mp hy').1
    exact hu
  rw[h] at t
  rcases t with ⟨t, _⟩
  rcases hg x ((hg' x y).mp hy').1 with ⟨w, hw, hw1⟩
  simp at hw1
  have bb := hw1 u hu t
  have gg := hw1 y hy hy'
  rw[← bb] at gg
  exact gg
  rcases hg x hx with ⟨u, ⟨hu, hu'⟩, hu2⟩
  use u
  simp
  constructor
  constructor
  exact hu
  right
  exact hu'
  rintro y hy (hy' | hy')
  apply hu2
  constructor
  exact hy
  have t: (x, y) ∈  f ∩ (A ∩ B) ×ˢ C := by
    constructor
    exact hy'
    constructor
    constructor
    exact ((hf' x y).mp hy').1
    exact ((hg' x u).mp hu').1
    exact ((hf' x y).mp hy').2
  rw[h] at t
  exact t.1
  rcases hg x ((hg' x u).mp hu').1 with ⟨l, _, hl'⟩
  simp at hl'
  have bb := hl' u hu hu'
  have gg := hl' y hy hy'
  rw[bb, gg]
