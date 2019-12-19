theorem pnp {P: Prop}: ¬(P ↔ ¬P)
:=
begin
  intro h,
  have hnp: ¬P, {
    intro hp,
    exact h.1 hp hp
  },
  exact hnp (h.2 hnp)
end

example:
  (∀ P Q R, (P ↔ Q) ∨ (Q ↔  R) ∨ (R ↔ P))
  → ∀ P, P ∨ ¬P
:=
begin
  intros h P,
  cases h (P ∨ ¬P) ¬(P ∨ ¬P) ¬¬(P ∨ ¬P) with h1 h23, {
    exfalso,
    exact pnp h1,
  },
  cases h23 with h2 h3, {
    exfalso,
    exact pnp h2,
  }, {
    apply h3.1,
    intro H,
    have hnp: ¬P, {
      intro hp,
      apply H,
      left,
      assumption
    },
    apply H,
    right,
    assumption,
  }
end
