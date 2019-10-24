open classical

variables p q r s : Prop

theorem t1 : p → q → p :=
begin
  intros hp hq,
  exact hp
end

theorem t2 (h₁ : q → r) (h₂ : p → q) : p → r :=
begin
  intro hp,
  apply h₁,
  apply h₂,
  exact hp
end

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hq,
    constructor, repeat { assumption },
  intro h,
  cases h with hq hp,
  constructor, repeat { assumption }
end

example : p ∨ q ↔ q ∨ p :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hq,
      right, exact hp,
    left, exact hq,
  intro h,
  cases h with hq hp,
    right, exact hq,
  left, exact hp
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  apply iff.intro,
  {
    intro h,
    cases h with hpq hr,
    cases hpq with hp hq,
    repeat { split; try { assumption } }
  },
  intro h,
  cases h with hp hqr,
  cases hqr with hq hr,
  repeat { split; try { assumption } }
end
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  apply iff.intro,
  {
    intro h,
    cases h with hpq hr,
    {
      cases hpq with hp hq,
      { apply or.intro_left, assumption},
      apply or.intro_right,
      exact or.intro_left r hq
    },
    apply or.intro_right,
    show q ∨ r,
      exact or.intro_right q hr
  },
  intro h,
  cases h with hp hqr,
  {
    apply or.intro_left,
    exact or.intro_left q hp
  },
  cases hqr with hq hr,
  {
    apply or.intro_left,
    exact or.intro_right p hq
  },
  apply or.intro_right,
  assumption
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hqr,
    cases hqr with hq hr,
      apply or.intro_left,
      split,
      repeat { assumption },
    apply or.intro_right,
    split,
    repeat { assumption },
  intro h,
  cases h with hpq hpr,
    split,
      exact hpq.left,
    exact or.intro_left r hpq.right,
  split,
    exact hpr.left,
  exact or.intro_right q hpr.right
end
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
  apply iff.intro,
    intro h,
    cases h with hp hqr,
      { split; apply or.intro_left; assumption },
    cases hqr with hq hr,
    { split; apply or.intro_right; assumption },
  intro h,
  cases h with hpq hpr,
  cases hpq with hp hq,
    apply or.intro_left,
    assumption,
  cases hpr with hp hr,
    apply or.intro_left,
    assumption,
  apply or.intro_right,
  split; assumption
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
  apply iff.intro,
    intros h hpq,
    exact h hpq.left hpq.right,
  intros h hp hq,
  exact h ⟨hp, hq⟩
end
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
  apply iff.intro,
    intro h,
    split,
      intro,
      exact h (or.intro_left q a),
    intro,
    exact h (or.intro_right p a),
  intros h hpq,
  cases h with hpr hqr,
  cases hpq with hp hq,
    exact hpr hp,
  exact hqr hq
end
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  apply iff.intro,
    intro h,
    split,
      intro,
      exact absurd (or.intro_left q a) h,
    intro,
    exact absurd (or.intro_right p a) h,
  intros h hpq,
  cases hpq with hp hq,
    exact h.left hp,
  exact h.right hq
end
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
  intros h hnpq,
  cases h with hnp hnq,
    exact hnp hnpq.left,
  exact hnq hnpq.right
end
example : ¬(p ∧ ¬p) :=
begin
  intro h,
  exact h.right h.left
end
example : p ∧ ¬q → ¬(p → q) :=
begin
  intros h hpq,
  exact h.right (hpq h.left)
end
example : ¬p → (p → q) :=
begin
  intros,
  contradiction
end
example : (¬p ∨ q) → (p → q) :=
begin
  intros hpq hp,
  cases hpq,
    contradiction,
  assumption
end
example : p ∨ false ↔ p :=
begin
  apply iff.intro,
    intro,
    cases a,
      assumption,
    contradiction,
  intro,
  left,
  assumption
end
example : p ∧ false ↔ false :=
begin
  apply iff.intro,
    intro,
    exact a.right,
  intro,
  contradiction
end
example : ¬(p ↔ ¬p) :=
begin
  intro,
  cases a,
  have hnp: ¬ p,
    intros hp,
    have : ¬ p,
      apply a_mp,
      assumption,
    contradiction,
  have : p,
    apply a_mpr,
    assumption,
  contradiction
end
example : (p → q) → (¬q → ¬p) :=
begin
  intros hpq hnq hp,
  have : q,
    apply hpq,
    assumption,
  contradiction
end

-- these require classical reasoning
example : (p → r ∨ s) → ((p → r) ∨ (p → s)) :=
begin
  intro h,
  apply by_cases,
    intro,
    left,
    assumption,
  intro hnpr,
  right,
  intro hp,
  cases h hp with hr hs,
    have hpr : p → r,
      intros,
      assumption,
    contradiction,
  assumption
end
example : ¬(p ∧ q) → ¬p ∨ ¬q :=
begin
  intro hnpq,
  apply by_cases,
    intro hp,
    right,
    intro hq,
    have : p ∧ q,
      split; assumption,
    contradiction,
  intro hnp,
  left,
  assumption
end
example : ¬(p → q) → p ∧ ¬q :=
begin
  intro h,
  split,
    apply by_cases,
      intro hp,
      assumption,
    intro hnp,
    have : p → q,
      intros,
      contradiction,
    contradiction,
  apply not.intro,
  intro hq,
  have : p → q,
    intros,
    assumption,
  contradiction
end
example : (p → q) → (¬p ∨ q) :=
begin
  intro,
  apply by_cases,
    intro hp,
    right,
    exact a hp,
  intro h,
  left,
  assumption
end
example : (¬q → ¬p) → (p → q) :=
begin
  intros,
  apply by_contradiction,
  intro hnq,
  have : ¬ p,
    apply a,
    assumption,
  contradiction
end
example : p ∨ ¬p :=
begin
  apply em
end
example : p ∨ ¬p :=
begin
  apply by_cases,
    intro hp,
    left,
    assumption,
  intro hnp,
  right,
  assumption
end
example : (((p → q) → p) → p) :=
begin
  intros,
  apply by_cases,
    intro,
    exact a a_1,
  intro,
  apply by_contradiction,
  intro,
  have h : p → q,
    intros,
    contradiction,
  contradiction
end
