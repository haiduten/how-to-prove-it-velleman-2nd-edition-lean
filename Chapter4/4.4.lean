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
(b) minium is 1. no maximum. smallest is 1. no largest. lub is 2. glb us 1
(c)


-/
end
