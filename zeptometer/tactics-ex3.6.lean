open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p := begin
    apply iff.intro,
    intro h,
    split,
        apply and.right,
        exact h,
        apply and.left,
        exact h,
    intro h,
    split,
        apply and.right,
        exact h,
    apply and.left,
    exact h,
end

example : p ∨ q ↔ q ∨ p := begin
    apply iff.intro,
    intro h,
    cases h with hp hq,
    right,
    exact hp,
    left,
    exact hq,
    intro h,
    cases h with hq hp,
    right,
    exact hq,
    left,
    exact hp,
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) := begin
    apply iff.intro,
    intro h,
    apply and.intro,
    apply and.left,
    apply and.left,
    exact h,
    apply and.intro,
    exact (and.right (and.left h)),
    exact (and.right h),
    intro h,
    split,
    split,
    exact (and.left h),
    exact (and.left (and.right h)),
    exact (and.right (and.right h))
end

example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) := begin
    split,
    intro h,
    cases h with a b,
    cases a with c d,
    left, assumption,
    right, left, assumption,
    right, right, assumption,
    intro h,
    cases h with a b,
    left, left, assumption,
    cases b with c d,
    left, right, assumption,
    right, assumption
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := begin
    split,
    intros,
    have h : q ∨ r, from and.right a,
    cases h with hq hr,
    left,
    split,
    exact (and.left a),
    assumption,
    right,
    split,
    exact (and.left a),
    assumption,
    intros,
    cases a,
    split,
    exact (and.left a),
    left,
    exact (and.right a),
    split,
    exact (and.left a),
    right,
    exact (and.right a),
end

example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) := sorry

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) := sorry
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) := sorry
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q := sorry
example : ¬p ∨ ¬q → ¬(p ∧ q) := sorry
example : ¬(p ∧ ¬p) := sorry
example : p ∧ ¬q → ¬(p → q) := sorry
example : ¬p → (p → q) := sorry
example : (¬p ∨ q) → (p → q) := sorry
example : p ∨ false ↔ p := sorry
example : p ∧ false ↔ false := sorry
example : ¬(p ↔ ¬p) := sorry
example : (p → q) → (¬q → ¬p) := sorry

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) := sorry
example : ¬(p ∧ q) → ¬p ∨ ¬q := sorry
example : ¬(p → q) → p ∧ ¬q := sorry
example : (p → q) → (¬p ∨ q) := sorry
example : (¬q → ¬p) → (p → q) := sorry
example : p ∨ ¬p := sorry
example : (((p → q) → p) → p) := sorry