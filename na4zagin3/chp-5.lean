section sec_3_redo
open classical

variables p q r s : Prop

-- commutativity of ∧ and ∨
example : p ∧ q ↔ q ∧ p :=
begin
  split; {
    intro h,
    cases h with p q,
    split; assumption
  }
end
example : p ∨ q ↔ q ∨ p :=
begin
  split; {
    intro h,
    cases h with p q; { left; assumption } <|> { right; assumption }
  }
end

-- associativity of ∧ and ∨
example : (p ∧ q) ∧ r ↔ p ∧ (q ∧ r) :=
begin
  split; {
    intro h,
    cases h with h1 h2,
    cases h1 with h11 h12 <|> cases h2 with h22 h23,
    repeat { split }; assumption,
  }
end
example : (p ∨ q) ∨ r ↔ p ∨ (q ∨ r) :=
begin
  split; {
    intro h,
    cases h; try { cases h },
    all_goals {
      { repeat { { left; assumption } <|> right }; assumption } <|>
      { repeat { { right; assumption } <|> left }; assumption } }
  }
end

-- distributivity
example : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) :=
begin
  split,
    intros h,
    cases h with hp hqr,
    cases hqr with hq hr;
    { left; split; assumption } <|> { right; split; assumption },
  intros h,
  cases h; cases h with hq hqr; split;
  { assumption <|> { left; assumption}  <|> { right; assumption} }
end
example : p ∨ (q ∧ r) ↔ (p ∨ q) ∧ (p ∨ r) :=
begin
  split,
    intros h,
    cases h with hp hqr;
    try {cases hqr with hq hr}; {
      split; {left; assumption} <|> {right; assumption}
    },
  intros h,
  cases h with hpq hpr;
  cases hpq with hp hq;
  cases hpr with hp2 hr;
  { assumption <|> {left; assumption}  <|> { right; split; assumption} }
end

-- other properties
example : (p → (q → r)) ↔ (p ∧ q → r) :=
begin
  split,
    intros hpqr hpq,
    cases hpq with hp hq,
    apply hpqr; assumption,
  intros hpqr hp hq,
  apply hpqr; split; assumption,
end
example : ((p ∨ q) → r) ↔ (p → r) ∧ (q → r) :=
begin
  split,
    intros hpqr,
    split; intros hpq; apply hpqr; {{left; assumption} <|> {right; assumption}},
  intros hprqr hpq,
  cases hprqr with hpr hqr,
  cases hpq with hp hq; { apply hpr; assumption } <|> { apply hqr; assumption }
end
example : ¬(p ∨ q) ↔ ¬p ∧ ¬q :=
begin
  split,
    intros hnpq,
    split; intros hpq; apply hnpq; {left; assumption}  <|> { right; assumption},
  intros hnpnq hpq,
  cases hnpnq with hnp hnq,
  cases hpq with hp hq;
  { apply hnp; assumption } <|> { apply hnq; assumption }
end
example : ¬p ∨ ¬q → ¬(p ∧ q) :=
begin
  intros hnpnq hpq,
  cases hpq with hp hq,
  cases hnpnq with hnp hnq;
  { apply hnp; assumption } <|> { apply hnq; assumption }
end
example : ¬(p ∧ ¬p) :=
begin
  intros hpnp,
  cases hpnp with hp hnp,
  apply hnp,
  assumption,
end
example : p ∧ ¬q → ¬(p → q) :=
begin
  intros hpnq hpq,
  cases hpnq with hp hnq,
  apply hnq,
  apply hpq,
  apply hp,
end
example : ¬p → (p → q) :=
begin
  intros hnp hp,
  cases (hnp hp),
end
example : (¬p ∨ q) → (p → q) :=
begin
  intros hnpq hp,
  cases hnpq with hnp hq,
    cases (hnp hp),
  apply hq,
end

example : ¬(p ↔ ¬p) :=
begin
  intro heqpnp,
  cases heqpnp with hpnp hnpp,
  apply hpnp;
    apply hnpp;
      intros p;
        apply hpnp; assumption,
end
end sec_3_redo

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
by split; split <|> left; assumption <|> right; {left; assumption} <|> {right; assumption}

example (p q r : Prop) (hp : p) :
(p ∨ q ∨ r) ∧ (q ∨ p ∨ r) ∧ (q ∨ r ∨ p) :=
begin
  split,
  all_goals { try {split} },
  all_goals { repeat { {left; assumption} <|> right } },
  all_goals { assumption },
end

