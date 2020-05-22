inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀ a : α, rtc a a
| trans : ∀ {a b c : α}, rtc a b → rtc b c → rtc a c

definition weakly_confluent {α : Type} (r: α → α → Prop) : Prop :=
    ∀ {a b c : α}, (r a b ∧ r b c) → ∃ d : α, rtc r b d ∧ rtc r c d

definition confluent {α : Type} (r: α → α → Prop) : Prop :=
    ∀ {a b c : α}, (r a b ∧ r b c) → ∃ d : α, rtc r b d ∧ rtc r c d

theorem newmans_lemma {α : Type} (r : α → α → Prop) :
    weakly_confluent r → well_founded r → confluent r := sorry
