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
