import HTPILib.Chap5
import Mathlib.Data.Quot
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

theorem Exercise_5_1_13_a (A B C: Type) (R: A → B)  (S: B → C)
    (h:  Ran (graph R) = Dom (graph S)):
    is_func_graph (comp (graph S) (graph R)) := by
  rintro x
  use S (R x)
  simp
  constructor
  simp[comp]
  use R x
  constructor
  rfl
  rfl
  rintro y hy
  simp[comp] at hy
  rcases hy with ⟨u, hu, hu'⟩
  simp[graph] at hu
  simp[graph] at hu'
  rw[hu]
  rw[hu']

/-
Exercise 5_1_13_b
A = {1}
B = {2, 3}
C = {9}

R = {(1, 2), (1, 3)} // R is not a funciton
S = {(2, 9), (3, 9)} // S is a function

S ∘ R = {(1, 9)} // S ∘ R is a function
-/

theorem Exercise_5_1_14_a (A B: Type) (f: A → B)
    (S: Set (B × B)):
    let R := {(x, y) : A × A | (f x, f y) ∈ S};
    reflexive (RelFromExt S) → reflexive (RelFromExt R) := by
  rintro R h x
  simp[RelFromExt]
  define
  exact h (f x)

theorem Exercise_5_1_14_b (A B: Type) (f: A → B)
    (S: Set (B × B)):
    let R := {(x, y) : A × A | (f x, f y) ∈ S};
    symmetric (RelFromExt S) → symmetric (RelFromExt R) := by
  rintro R h
  rintro x y hxy
  simp[RelFromExt]
  simp[RelFromExt] at hxy
  define
  define at hxy
  exact h (f x) (f y) hxy

theorem Exercise_5_1_14_c (A B: Type) (f: A → B)
    (S: Set (B × B)):
    let R := {(x, y) : A × A | (f x, f y) ∈ S};
    transitive (RelFromExt S) → transitive (RelFromExt R) := by
  rintro R h x y z hxy hyz
  simp[RelFromExt]
  define
  simp[RelFromExt] at hxy
  define at hxy
  simp[RelFromExt] at hyz
  define at hyz
  exact h (f x) (f y) (f z) hxy hyz

/-
Exercise_5_1_15_a
No
A = {1, 2, 3}
B = {a, b, c}
f = {(1, a) , (2, a), (3, a)}
R = {(1, 1), (2, 2), (3, 3)}
S = {(a, a)} // missing b and c
-/

theorem Exercise_5_1_15_b (A B: Type) (f: A → B)
    (R: Set (B × B)):
    let S := {(x, y) : B × B | ∃ u : A, ∃ v: A, f u  = x ∧ f v = y ∧ (x, y) ∈ R};
    symmetric (RelFromExt R) → symmetric (RelFromExt S) := by
  rintro S h x y hxy
  simp[RelFromExt]
  define
  simp[RelFromExt] at hxy
  define at hxy
  rcases hxy with ⟨u, u', hu, hu', huu'⟩
  use u'
  use u
  constructor
  exact hu'
  constructor
  exact hu
  exact h x y huu'

/-
Exercise 5_1_15_c
No
A = {1, 2, 3, 4}
B = {a, b, c}
f = {(1, a), (2, b), (3, b), (4, c)}
R = {(1, 2), (3, 4))}
S = {(a, b), (b, c)}
-/

theorem Exercise_5_1_16_a (A B: Type) (F: Set (A → B))
    (R: Set (B × B)):
    let S := {(f, g): (A → B) × (A → B) | ∀ x : A, (f x, g x) ∈ R};
    reflexive (RelFromExt R) → reflexive (RelFromExt S) := by
  rintro S h
  rintro F
  simp[RelFromExt]
  define
  rintro x
  exact h (F x)

theorem Exercise_5_1_16_b (A B: Type) (F: Set (A → B))
    (R: Set (B × B)):
    let S := {(f, g): (A → B) × (A → B) | ∀ x : A, (f x, g x) ∈ R};
    symmetric (RelFromExt R) → symmetric (RelFromExt S) := by
  rintro S h
  rintro F G hFG
  simp[RelFromExt]
  define
  simp[RelFromExt] at hFG
  define at hFG
  rintro x
  have hFG := hFG x
  exact h (F x) (G x) hFG

theorem Exercise_5_1_16_c (A B: Type) (F: Set (A → B))
    (R: Set (B × B)):
    let S := {(f, g): (A → B) × (A → B) | ∀ x : A, (f x, g x) ∈ R};
    transitive (RelFromExt R) → transitive (RelFromExt S) := by
  rintro S h
  rintro F G H hFG hGH
  simp[RelFromExt]
  define
  simp[RelFromExt] at hFG
  define at hFG
  simp[RelFromExt] at hGH
  define at hGH
  rintro x
  have hFG := hFG x
  have hGH := hGH x
  exact h (F x) (G x) (H x) hFG hGH

theorem Exercise_5_1_17_a (A: Type) (f: A → A)
    (h: ∃ a : A, ∀ x: A, f x = a):
    ∀ g : A → A, comp (graph f) (graph g) = graph f := by
  rcases h with ⟨a, ha⟩
  rintro g
  apply Set.ext
  rintro ⟨m ,n⟩
  constructor
  rintro hmn
  rcases hmn with ⟨u, hu, hu'⟩
  simp[graph_def]
  simp[graph_def] at hu
  simp[graph_def] at hu'
  have ha' := ha u
  rw[hu'] at ha'
  rw[ha']
  exact ha m
  rintro hmn
  simp[comp, graph_def]
  simp[graph_def] at hmn
  have ha' := ha m
  rw[hmn] at ha'
  rw[ha']
  exact ha (g m)

theorem Exercise_5_1_17_b (A: Type) (f: A → A) (a: A)
    (h: ∀ g : A → A, f ∘ g = f):
    ∃ a : A, ∀ x: A, f x = a := by
  use f a
  rintro x
  have h := h fun (x: A) => a
  rw[← h]
  rfl

theorem Exercise_5_1_18_a:
    let F := {(f, g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ a : ℝ, ∀ x > a,  f x = g x}
    (fun (x: ℝ) => |x|, id) ∈ F := by
  define
  use 0
  rintro x hx
  simp
  apply le_of_lt
  exact hx

theorem Exercise_5_1_18_b:
    let F := {(f, g): (ℝ → ℝ) × (ℝ → ℝ) | ∃ a : ℝ, ∀ x > a,  f x = g x}
    equiv_rel (RelFromExt F) := by
  constructor
  rintro x
  simp[RelFromExt]
  constructor
  rintro x y hxy
  simp[RelFromExt] at hxy
  rcases hxy with ⟨a, h⟩
  simp[RelFromExt]
  use a
  rintro x hax
  exact (h x hax).symm
  rintro X Y Z hXY hYZ
  simp[RelFromExt] at hXY
  simp[RelFromExt] at hYZ
  rcases hXY with ⟨a, ha⟩
  rcases hYZ with ⟨a', ha'⟩
  simp[RelFromExt]
  use (max a a')
  rintro x hx
  have hax: a < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    exact hx
    rw[h'] at hx
    exact lt_trans h'' hx
  have ha'x : a' < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    apply Std.lt_of_le_of_lt h'' hx
    rw[h'] at hx
    exact hx
  have ha := ha x hax
  have ha' := ha' x ha'x
  rw[ha]
  exact ha'

theorem Exericse_5_1_19_a:
    ∃ a : ℤ, ∃ c : ℝ, ∀ x > a, |(fun y: ℤ => 7 * y + 3) x| ≤ c * |(fun y: ℤ => y * y) x| := by
  use 100
  use 1
  rintro x hx
  simp
  have t: (0: ℝ) < 7 * x + 3 := by
    have h: (0: ℝ) < 7 := by norm_num
    have hx' : (100 : ℝ) < x := by exact_mod_cast hx
    have y := (mul_lt_mul_iff_of_pos_left h).mpr hx'
    linarith
  rw[ abs_of_pos t]
  apply le_of_lt
  have t: x * x > (100: ℝ) * x := by
    have h: (0: ℝ) < x := by
      have h: (0: ℝ) < 100 := by norm_num
      have hx' : (100 : ℝ) < x := by exact_mod_cast hx
      apply lt_trans h hx'
    have hx' : (100 : ℝ) < x := by exact_mod_cast hx
    have y := (mul_lt_mul_iff_of_pos_right h).mpr hx'
    exact y
  have h: 7 * x + 3 < (100: ℝ) * x := by
    have hx' : (100 : ℝ) < x := by exact_mod_cast hx
    linarith
  exact lt_trans h t

theorem Exericse_5_1_19_b:
    let S := {(f, g): (ℝ → ℝ) × (ℝ → ℝ)|   ∃ a : ℤ, ∃ c > (0: ℝ), ∀ x > a, |f x| ≤ c * |g x| }
    preorder (RelFromExt S) := by
  constructor
  rintro x
  simp[RelFromExt]
  use 1
  use 1
  constructor
  norm_num
  rintro x hx
  linarith
  rintro f g h hfg hgh
  simp[RelFromExt] at hfg
  simp[RelFromExt] at hgh
  rcases hfg with ⟨a , c, h1, h⟩
  rcases hgh with ⟨a', c', h'1, h'⟩
  use max a a'
  use c * c'
  constructor
  have q := (mul_lt_mul_iff_of_pos_right h'1).mpr h1
  linarith
  rintro x hx
  have hax: a < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    exact hx
    rw[h'] at hx
    exact lt_trans h'' hx
  have ha'x : a' < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    apply Std.lt_of_le_of_lt h'' hx
    rw[h'] at hx
    exact hx
  have h := h x hax
  have h' := h' x ha'x
  have h' := (mul_le_mul_iff_of_pos_left h1).mpr h'
  rw[← mul_assoc] at h'
  exact le_trans h h'


/-
It is not anti-symmetric.
Counter example:
f: x
g: 3 * x
(f, g) ∈ S with c = 1 and a = 0
(g, f) ∈ S with c = 3 and a = 0
but f ≠ g
-/

theorem Exericse_5_1_19_c (s t: ℝ) (hs : 0 < s) (ht : 0 < t) (g f₁ f₂: ℝ → ℝ) (S: Set ((ℝ → ℝ)))
    (hS: S = {f: (ℝ → ℝ)| ∃ a > (0: ℝ), ∃ c > (0: ℝ), ∀ x > a, |f x| ≤ c * |g x| })
    (hf₁: f₁ ∈ S) (hf₂: f₂ ∈ S):
    (fun x => s * (f₁ x) + t * (f₂ x)) ∈ S := by
  simp[hS]
  simp[hS] at hf₁
  simp[hS] at hf₂
  rcases hf₁ with ⟨a, ha, c, hc, hac⟩
  rcases hf₂ with ⟨a', ha', c', hc', hac'⟩
  use max a a'
  constructor
  rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
  rw[h']
  assumption
  rw[h']
  assumption
  use (|s * c| + |t * c'| + 1)
  constructor
  rcases abs_cases (s * c) with (⟨hs, hs'⟩ | ⟨hs, hs'⟩)
  rcases lt_or_eq_of_le hs' with (hs' | hs')
  rcases abs_cases (t * c') with (⟨ht, ht'⟩ | ⟨ht, ht'⟩)
  rcases lt_or_eq_of_le ht' with (ht' | ht')
  rw[hs, ht]
  linarith
  rw[hs, ht]
  linarith
  rw[hs, ht]
  linarith
  rcases abs_cases (t * c') with (⟨ht, ht'⟩ | ⟨ht, ht'⟩)
  rw[hs, ht]
  linarith
  rw[hs, ht]
  linarith
  rcases abs_cases (t * c') with (⟨ht, ht'⟩ | ⟨ht, ht'⟩)
  rw[hs, ht]
  linarith
  rw[hs, ht]
  linarith
  rintro x hx
  have hax: a < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    exact hx
    rw[h'] at hx
    exact lt_trans h'' hx
  have ha'x : a' < x := by
    rcases max_cases a a' with (⟨h', h''⟩ | ⟨h', h''⟩)
    rw[h'] at hx
    apply Std.lt_of_le_of_lt h'' hx
    rw[h'] at hx
    exact hx
  have hac := hac x hax
  have hac' := hac' x ha'x
  rw[add_mul, add_mul]
  have h' := abs_add_le (s * f₁ x) (t * f₂ x)
  have h1': |s * f₁ x| ≤ |s * c| * |g x| := by
    rw[abs_mul, abs_mul]
    rw[abs_of_pos hs, (abs_of_pos hc)]
    field_simp
    exact hac
  have h2': |t * f₂ x| ≤ |t * c'| * |g x| := by
    rw[abs_mul, abs_mul]
    rw[abs_of_pos ht, (abs_of_pos hc')]
    field_simp
    exact hac'
  rw[one_mul]
  have h3': |s * f₁ x| + |t * f₂ x| ≤ |s * c| * |g x| + |t * c'| * |g x| := add_le_add h1' h2'
  have h4': |s * c| * |g x| + |t * c'| * |g x| ≤ |s * c| * |g x| + |t * c'| * |g x| + |g x| := by
    rw[add_assoc]
    rw[(add_le_add_iff_left (|s * c| * |g x|))]
    nth_rewrite 1 [← add_zero (|t * c'| * |g x|)]
    rw[(add_le_add_iff_left (|t * c'| * |g x|))]
    simp
  exact le_trans h' (le_trans h3' h4')

theorem Exercise_5_1_20_a (A B: Type) (g: A → B):
    let R := {(x, y): A × A | g x = g y}
    equiv_rel (RelFromExt R) := by
  constructor
  rintro x
  simp[RelFromExt]
  constructor
  rintro x y hxy
  simp[RelFromExt] at hxy
  simp[RelFromExt]
  exact hxy.symm
  rintro x y z hxy hyz
  simp[RelFromExt] at hxy
  simp[RelFromExt] at hyz
  simp[RelFromExt]
  rw[← hyz]
  exact hxy

theorem Exercise_5_1_20_b (A: Type) (R: BinRel A) (hR: equiv_rel R):
    let g := fun (x: A) => equivClass R x
    extension R = {(x, y): A × A | g x = g y} := by
  rcases hR with ⟨refl, symm, trans⟩
  rintro g
  apply Set.ext
  rintro ⟨x , y⟩
  constructor
  rintro hxy
  simp[extension] at hxy
  simp[g, equivClass]
  apply Set.ext
  rintro b
  constructor
  rintro hb
  simp at hb
  simp
  exact trans b x y hb hxy
  rintro hb
  simp
  simp at hb
  exact trans b y x hb (symm x y hxy)
  rintro hxy
  simp[g, equivClass] at hxy
  simp[extension]
  have h': x ∈ {y : A | R y x} := by
    simp
    exact refl x
  rw[hxy] at h'
  simp at h'
  exact h'

theorem Exercise_5_21_a (A B: Type) (R: BinRel A) (hR: equiv_rel R)
    (f: A → B) (hf: ∀ x y: A, R x y → f x = f y):
    ∃! h : (Quot R → B), ∀ x : A, h (Quot.mk R x) = f x := by
  exists_unique
  · use Quot.lift f hf
    intro x
    rfl
  · intro j k hj  hk
    apply funext
    apply Quot.ind
    intro a
    rw[hj a, hk a]

theorem Exercise_5_21_b (A B: Type) (f: A → B) (R: BinRel A) (hR: equiv_rel R)
    (h: Quot R → B) (h': ∀ x : A, h (Quot.mk R x) = f x):
    ∀ x y: A, R x y → f x = f y := by
  intro x y  hxy
  have hx := (h' x).symm
  have hy := (h' y).symm
  rw[hx, hy]
  have : Quot.mk R x = Quot.mk R y := by
    apply Quot.sound
    exact hxy
  rw[this]

theorem Exercise_5_22_a:
    let R (x y: ℕ) := ∃ k : ℕ, x - y = 5 * k
    ∃! h : (Quot R → Quot R), ∀ x : ℕ, h (Quot.mk R x) = (Quot.mk R (x * x)) := by
  intro R
  exists_unique
  · let f := fun (x: ℕ) => Quot.mk R (x * x)
    have hf: ∀ x y: ℕ, R x y → f x = f y := by
      intro x y hxy
      simp[f]
      apply Quot.sound
      simp[R] at *
      have ⟨w, hw⟩ := hxy
      use (w * ( x + y))
      rw[ ← mul_assoc, ← hw]
      simpa [Nat.mul_comm] using Nat.mul_self_sub_mul_self_eq x y
    exists (Quot.lift f hf)
    rintro x
    simp
    simp[f]
  · intro j k hj hk
    apply funext
    apply Quot.ind
    intro a
    have hj := hj a
    have hk := hk a
    rw[hj, hk]

theorem Exercise_5_22_b:
    let R (x y: ℕ) := x % 5 = y % 5;
    ¬∃ h : (Quot R → Quot R), ∀ x : ℕ, h (Quot.mk R x) = Quot.mk R (2 ^ x) := by
  intro R h
  have ⟨f, hg⟩ := h
  have hg1 := hg 1
  have hg2 := hg 6
  have h': (Quot.mk R 1) = (Quot.mk R 6) := by
    apply Quot.sound
    simp[R]
  rw[h'] at hg1
  rw[hg1] at hg2
  simp at hg2
  let k := fun (x: ℕ) => x % 5
  have hk: ∀ x y: ℕ, R x y → k x = k y:= by
    simp only[k]
    intro x y hxy
    simp[R] at hxy
    rw[hxy]
  let o := Quot.lift k hk
  let oresult := o (Quot.mk R 2)
  have hfinal: o (Quot.mk R 2) = oresult := by rfl
  rw[hg2] at hfinal
  simp[oresult, o, k] at hfinal
