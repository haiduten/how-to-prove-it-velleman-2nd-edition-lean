import HTPILib.Chap4
namespace HTPI.Exercises

/-
  Example 4.4.3
  1. partial order
  2. Neither
  3. partial
  4. total

  Example 4.4.5
  1. L-smallest of B is 7. L-minimum of B is 7. There is no L-smallest or L-minimum of C
  2. No D-smallest of B. D-minimum is 3, 4, 5, and 7
  3. S-smallest is {2, 3}. S-minimum is {2, 3}. G-smallest is none. G-minimum is {2} and {3}

-/

section
variable {A: Type}
variable (R: BinRel A)
variable (B: Set A)

theorem Example_4_4_6_1 (h: partial_order R): (∃ (b: A), smallestElt R b B) → ∃! (b: A), smallestElt R b B := by
  rintro ⟨b', ⟨hb, hb1⟩⟩
  exists_unique
  · -- existence
    use b'
    apply And.intro hb hb1
  · -- uniqueness
    rintro b1 b2 ⟨hb1, hb1'⟩ ⟨hb2, hb2'⟩
    apply h.2.2
    exact hb1' b2 hb2
    exact hb2' b1 hb1

theorem Example_4_4_6_2 (b : A)
    (h1 : partial_order R) (h2 : smallestElt R b B) :
    minimalElt R b B ∧ ∀ (c : A), minimalElt R c B → b = c := by
  rcases h2 with ⟨h21, h2⟩
  rcases h1 with ⟨reflexive, _, antisymm⟩
  constructor
  constructor
  exact h21
  push_neg;
  rintro x xinB hx
  apply antisymm
  exact hx
  exact h2 x xinB
  rintro c ⟨hc, hc'⟩
  apply antisymm
  exact h2 c hc
  push_neg at hc'
  rw[hc' b h21 (h2 c hc)]
  apply reflexive

theorem Example_4_4_6_3 (b: A) (h: total_order R) (h₁: minimalElt R b B): smallestElt R b B := by
  rcases h with ⟨⟨reflexive, _ , _⟩ , total_prop⟩
  rcases h₁ with ⟨hb, hb'⟩
  constructor
  exact hb
  push_neg at hb'
  rintro c hc
  rcases (total_prop b c) with total | total
  exact total
  rw[hb' c hc total]
  apply reflexive

/-
Example 4.4.7
1. {5, ...Infinity greater than 5}
2. Does not exist

Example 4.4.10
1. B has upper bound and lower bound. Greatest lower bound is 0. Least upper bound is 1
2. No lower bound. Yes upperbound. No glb and no lub

Exercise 4_4_1
(a) partial order
(b) neither
(c) partial

Exercise 4_4_2
(a) total
(b) neiher
(c) neither

Exercise_4_4_3
(a) minimum element is 2. maximum is 3 and 4. smallest is 2. No largest. no lub. glb is 2
(b) minium is 1. no maximum. smallest is 1. no largest. lub is 2. glb is 1
(c) minimum is {}. no maximum. smallest is {}. no largest. lup is set of naural numbers. glb is {}
-/

def iA := {(x, y): A × A | x = y}
theorem Exercise_4_4_4: antisymmetric R ∧ symmetric R ↔ (extension R) ⊆ iA := by
  constructor
  · -- mp
    rintro ⟨antisym, sym⟩ ⟨m , n⟩ h
    define
    apply antisym
    rw[← (ext_def R m n)]
    exact h
    apply sym
    exact h
  · -- mpr
    rintro h
    constructor
    rintro x y hxy hyx
    rw[←ext_def R x y] at hxy
    exact h hxy
    rintro x y hxy
    rw[←ext_def R x y] at hxy
    rw[h hxy]
    rw[h hxy] at hxy
    exact hxy

theorem Exercise_4_4_5 (B: Set A) (h: partial_order R):
partial_order_on B (RelFromExt ((extension R) ∩ (B ×ˢ B))) := by
  rcases h with ⟨refl, trans, antisym⟩
  constructor
  rintro x hx
  constructor
  apply refl
  constructor
  exact hx
  exact hx
  constructor
  rintro x y z ⟨hx, hy, hz⟩ ⟨hxy, _⟩  ⟨hyz, _⟩
  constructor
  apply trans x y z
  exact hxy
  exact hyz
  constructor
  exact hx
  exact hz
  rintro x y ⟨hx, hy⟩ ⟨hxy, _⟩ ⟨hyx, _⟩
  apply antisym
  exact hxy
  exact hyx

theorem Exercise_4_4_6_a (R₁ R₂: BinRel A) (hR₁: partial_order R₁) (hR₂: partial_order R₂):
partial_order (RelFromExt ((extension R₁) ∩ (extension R₂))) := by
  rcases hR₁ with ⟨reflR₁, transR₁, antisymR₁⟩
  rcases hR₂ with ⟨reflR₂, transR₂, antisymR₂⟩
  constructor
  rintro _
  constructor
  apply reflR₁
  apply reflR₂
  constructor
  rintro x y z ⟨hxyR1 , hxyR2⟩ ⟨hyzR1, hyzR2⟩
  constructor
  apply transR₁
  exact hxyR1
  exact hyzR1
  apply transR₂
  exact hxyR2
  exact hyzR2
  rintro x y hxy hyx
  apply antisymR₁
  exact hxy.1
  exact hyx.1

/-
Exercise_4_4_6_b
Counter example
R₁ = {(1, 1), (2, 2), (1, 2)}
R₂ = {(1, 1), (2, 2), (2, 1}
It fails anti-symmetry
-/
end

namespace Exercise_4_4_7

section
variable {A : Type}
variable {A₁ A₂: Set A}
variable {R₁ R₂: BinRel A}

theorem Exercise_4_4_7_a (hR₁: partial_order_on A₁ R₁) (hA₁: (extension R₁) ⊆ (A₁ ×ˢ A₁)) (hA₂: (extension R₂) ⊆ (A₂ ×ˢ A₂)) (hR₂: partial_order_on A₂ R₂) (h: A₁ ∩ A₂ = ∅):
partial_order_on (A₁ ∪ A₂) (RelFromExt ((extension R₁) ∪ (extension R₂))) := by
  rcases hR₁ with ⟨reflR₁, transR₁, antisymR₁⟩
  rcases hR₂ with ⟨reflR₂, transR₂, antisymR₂⟩
  constructor
  rintro x hx
  rcases hx with hx | hx
  apply Or.inl (reflR₁ x hx)
  apply Or.inr (reflR₂ x hx)
  constructor
  rintro x y z ⟨hx | hx, hy | hy, hz | hz⟩ (hxy | hxy) (hyz | hyz)
  left
  apply transR₁
  exact And.intro hx (And.intro hy hz)
  exact hxy
  exact hyz
  contradict h; push_neg
  use y
  apply And.intro hy
  exact (hA₂ hyz).1
  contradict h; push_neg
  use y
  apply And.intro hy
  exact (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro hy
  exact (hA₂ hxy).2
  contradict h; push_neg
  use z
  apply And.intro (hA₁ hyz).2
  exact hz
  contradict h; push_neg
  use y
  apply And.intro hy
  exact (hA₂ hyz).1
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hxy).2 hy
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hxy).2 hy
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hyz).1 hy
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hxy).1
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hxy).2 hy
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hxy).2 hy
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hxy).1
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hxy).1
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hyz).1
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hyz).1
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hyz).1 hy
  contradict h; push_neg
  use z
  apply And.intro hz (hA₂ hyz).2
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use z
  apply And.intro (hA₁ hyz).2 hz
  right
  apply transR₂
  apply And.intro hx (And.intro hy hz)
  exact hxy
  exact hyz
  rintro x y ⟨hx | hx, hy | hy⟩ (hxy | hxy) (hyx | hyx)
  apply antisymR₁
  apply And.intro hx hy
  apply hxy
  apply hyx
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hyx).2
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hxy).1
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hxy).2
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hyx).1 hy
  contradict h; push_neg
  use y
  apply And.intro (hA₁ hxy).2 hy
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hxy).1
  contradict h; push_neg
  use x
  apply And.intro hx (hA₂ hyx).2
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hyx).2 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hyx).2 hx
  contradict h; push_neg
  use y
  apply And.intro hy (hA₂ hyx).1
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hyx).2 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hxy).1 hx
  contradict h; push_neg
  use x
  apply And.intro (hA₁ hyx).2 hx
  apply antisymR₂
  apply And.intro hx hy
  exact hxy
  exact hyx

theorem Exercise_4_4_7_b (hR₁: partial_order_on A₁ R₁) (hA₁: (extension R₁) ⊆ (A₁ ×ˢ A₁)) (hA₂: (extension R₂) ⊆ (A₂ ×ˢ A₂)) (hR₂: partial_order_on A₂ R₂) (h: A₁ ∩ A₂ = ∅):
partial_order_on (A₁ ∪ A₂) (RelFromExt ((extension R₁) ∪ (extension R₂) ∪ (A₁ ×ˢ A₂))) := by
  rcases hR₁ with ⟨reflR₁, transR₁, antisymR₁⟩
  rcases hR₂ with ⟨reflR₂, transR₂, antisymR₂⟩
  constructor
  rintro x (hx | hx)
  left; left
  exact reflR₁ x hx
  left; right
  exact reflR₂ x hx
  constructor
  rintro x y z ⟨hx | hx, hy | hy, hz | hz⟩ hxy hyz
  define at hxy
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define; demorgan
    right
    by_contra h'
    contradict h; push_neg
    use y
    exact And.intro hy h'
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₂ := by
    by_contra h'
    contradict h; push_neg
    use x
    exact And.intro hx (hA₂ h').1
  disj_syll hxy h'
  define at hyz
  have h': (y, z) ∉ A₁ ×ˢ A₂ := by
    define; demorgan
    right
    by_contra h'
    contradict h; push_neg
    use z
    exact And.intro hz h'
  disj_syll hyz h'
  have h': (y, z) ∉ extension R₂ := by
    by_contra h'
    contradict h; push_neg
    use y
    exact And.intro hy (hA₂ h').1
  disj_syll hyz h'
  left; left
  apply transR₁
  apply And.intro hx (And.intro hy hz)
  exact hxy
  exact hyz
  define at hxy
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define; demorgan
    right
    by_contra h'
    contradict h; push_neg
    use y
    exact And.intro hy h'
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₂ := by
    by_contra h'
    contradict h; push_neg
    use x
    exact And.intro hx (hA₂ h').1
  disj_syll hxy h'
  define at hyz
  have h': (y, z) ∉ extension R₁ ∪ extension R₂ := by
    define; demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use z
    apply And.intro (hA₁ h').2 hz
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').1
  disj_syll hyz h'
  right
  apply And.intro hx hyz.2
  define at hyz
  have h': (y, z) ∉ A₁ ×ˢ A₂ := by
    define; demorgan
    left
    by_contra h'
    contradict h; push_neg
    use y
    exact And.intro h' hy
  disj_syll hyz h'
  have h': (y, z) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
    by_contra h'
    contradict h
    push_neg
    use z
    apply And.intro hz (hA₂ h').2
  contradict h'
  exact hyz
  define at hxy
  have h': (x, y) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').2 hy
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro hx (hA₂ h').1
  disj_syll hxy h'
  define at hyz
  have h': (y, z) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro h' hy
  disj_syll hyz h'
  have h': (y, z) ∉ extension R₁ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
  disj_syll hyz h'
  right
  apply And.intro hx (hA₂ hyz).2
  define at hxy
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    right
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (h')
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro (hA₁ h').1 hx
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').2
  contradict h'
  exact hxy
  define at hxy
  have h': (x, y) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro (hA₁ h').1 hx
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').2
  disj_syll hxy h'
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro h' hx
  contradict h'
  exact hxy
  define at hxy
  have h': (y, z) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
    by_contra h'
    contradict h
    push_neg
    use z
    apply And.intro hz (hA₂ h').2
  disj_syll hyz h'
  have h': (y, z) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro h' hy
  contradict h'
  exact hyz
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro h' hx
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₁ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').2 hy
  disj_syll hxy h'
  have h': (y, z) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro h' hy
  disj_syll hyz h'
  have h': (y, z) ∉ extension R₁ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
  disj_syll hyz h'
  left; right
  apply transR₂
  apply And.intro hx (And.intro hy hz)
  exact hxy
  exact hyz
  rintro x y ⟨hx | hx, hy | hy⟩ hxy hyx
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    right
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy h'
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₂ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').2
  disj_syll hxy h'
  have h': (y, x) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    right
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro hx h'
  disj_syll hyx h'
  have h': (y, x) ∉ extension R₂ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').1
  disj_syll hyx h'
  apply antisymR₁
  apply And.intro hx hy
  exact hxy
  exact hyx
  have h': (y, x) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro hx (hA₂ h').2
  disj_syll hyx h'
  have h': (y, x) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    right
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro hx h'
  contradict h'
  exact hyx
  have h': (x, y) ∉ extension R₁ ∪ extension R₂ := by
    define
    demorgan
    constructor
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro (hA₁ h').1 hx
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy (hA₂ h').2
  disj_syll hxy h'
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    right
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro hy h'
  contradict h'
  exact hxy
  have h': (x, y) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use x
    apply And.intro h' hx
  disj_syll hxy h'
  have h': (x, y) ∉ extension R₁ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').2 hy
  disj_syll hxy h'
  have h': (y, x) ∉ A₁ ×ˢ A₂ := by
    define
    demorgan
    left
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro h' hy
  disj_syll hyx h'
  have h': (y, x) ∉ extension R₁ := by
    by_contra h'
    contradict h
    push_neg
    use y
    apply And.intro (hA₁ h').1 hy
  disj_syll hyx h'
  apply antisymR₂
  apply And.intro hx hy
  exact hxy
  exact hyx

  /-
  Exercise 4_4_7_c
  Part a is not total order
  -/

theorem Exercise_4_4_7_c (hR₁: total_order_on A₁ R₁) (hA₁: (extension R₁) ⊆ (A₁ ×ˢ A₁)) (hA₂: (extension R₂) ⊆ (A₂ ×ˢ A₂)) (hR₂: total_order_on A₂ R₂) (h: A₁ ∩ A₂ = ∅):
∀ (x y : A), x ∈ (A₁ ∪ A₂) ∧ y ∈ (A₁ ∪ A₂) → (x, y) ∈ (extension R₁) ∪ (extension R₂) ∪ (A₁ ×ˢ A₂) ∨ (y, x) ∈ (extension R₁) ∪ (extension R₂) ∪ (A₁ ×ˢ A₂)  := by
  rintro x y ⟨hx | hx, hy | hy⟩
  rcases hR₁ with ⟨_, totalR₁⟩
  rcases totalR₁ x y (And.intro hx hy) with (hxy | hyx)
  left;left;left
  exact hxy
  right;left;left
  exact hyx
  left;right
  constructor
  exact hx
  exact hy
  right;right
  constructor
  exact hy
  exact hx
  rcases hR₂ with ⟨_, totalR₂⟩
  rcases totalR₂ x y (And.intro hx hy) with (hxy | hyx)
  left;left;right
  exact hxy
  right;left;right
  exact hyx

end

theorem Exercise_4_4_8 {A B : Type} (R : BinRel A) (S : BinRel B)
    (T : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      T (a, b) (a', b') ↔ R a a' ∧ S b b') :
    partial_order T := by
  rcases h1 with ⟨reflR, transR, antisymR⟩
  rcases h2 with ⟨reflS, transS, antisymS⟩
  constructor
  rintro ⟨x, y⟩
  rw[h3]
  constructor
  exact reflR x
  exact reflS y
  constructor
  rintro ⟨xA, xB⟩ ⟨yA, yB⟩ ⟨zA, zB⟩ hxy hyz
  rw[h3] at hxy
  rw[h3] at hyz
  rcases hxy with ⟨hxyA, hxyB⟩
  rcases hyz with ⟨hyzA, hyzB⟩
  rw[h3]
  constructor
  apply transR
  exact hxyA
  exact hyzA
  apply transS
  exact hxyB
  exact hyzB
  rintro ⟨xA, xB⟩ ⟨yA, yB⟩ hxy hyx
  rw[h3] at hxy
  rcases hxy with ⟨hxyA, hxyB⟩
  rw[h3] at hyx
  rcases hyx with ⟨hyxA, hyxB⟩
  rw[antisymR xA yA hxyA hyxA]
  rw[antisymS xB yB hxyB hyxB]

/-
 If R and S are total orders, T is not a total order. Counterexample
 A = {a, a'}
 B = {b , b'}
 R = {(a, a), (a', a'), (a, a')}
 S = {(b, b), (b', b'), (b, b')}

 (a', b), (a, b') ∉ T
-/

theorem Exercise_4_4_9 {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : partial_order R) (h2 : partial_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    partial_order L:= by
  rcases h1 with ⟨reflR, transR, antisymR⟩
  rcases h2 with ⟨reflS, transS, antisymS⟩
  constructor
  rintro ⟨xA, xB⟩
  rw[h3]
  constructor
  exact reflR xA
  intro _
  exact reflS xB
  constructor
  rintro ⟨xA, xB⟩ ⟨yA, yB⟩ ⟨zA, zB⟩ hxy hyz
  rw[h3] at hxy
  rw[h3] at hyz
  rcases hxy with ⟨hxyA, hxyB⟩
  rcases hyz with ⟨hyzA, hyzB⟩
  rw[h3]
  constructor
  apply transR
  exact hxyA
  exact hyzA
  rintro h₁
  rw[←h₁] at hyzA
  apply transS
  exact hxyB (antisymR xA yA hxyA hyzA)
  rw[h₁] at hxyA
  rw[h₁] at hyzA
  exact hyzB (antisymR zA yA hxyA hyzA).symm
  rintro ⟨xA, xB⟩ ⟨yA, yB⟩ hxy hyx
  rw[h3] at hxy
  rw[h3] at hyx
  rcases hxy with ⟨hxyA, hxyB⟩
  rcases hyx with ⟨hyxA, hyxB⟩
  have hxEqyA := antisymR xA yA hxyA hyxA
  rw[hxEqyA]
  rw[antisymS xB yB (hxyB hxEqyA) (hyxB hxEqyA.symm)]

theorem Exercise_4_4_9_part {A B : Type} (R : BinRel A) (S : BinRel B)
    (L : BinRel (A × B)) (h1 : total_order R) (h2 : total_order S)
    (h3 : ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ↔ R a a' ∧ (a = a' → S b b')) :
    ∀ (a a' : A) (b b' : B),
      L (a, b) (a', b') ∨ L (a', b') (a, b) := by
  rcases h1 with ⟨⟨reflR⟩,  totalR⟩
  rcases h2 with ⟨⟨reflS⟩,  totalS⟩
  rintro a a' b b'
  rw[h3, h3]
  by_cases haa': a ≠ a'
  rcases totalR a a' with hR | hR
  left
  constructor
  exact hR
  conditional
  left
  exact haa'
  right
  constructor
  exact hR
  conditional
  left
  exact haa'.symm
  rw[not_ne_iff] at haa'
  rcases totalS b b' with hS | hS
  left
  constructor
  rw[haa']
  exact reflR a'
  rintro _
  exact hS
  right
  constructor
  rw[haa']
  exact reflR a'
  rintro _
  exact hS
