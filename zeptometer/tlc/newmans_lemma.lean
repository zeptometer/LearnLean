-- Reflexive transitive closure
 inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀ a : α, rtc a a
| next : ∀ a b c : α, rtc a b → r b c → rtc a c

lemma rtc_reflexive {α : Type} (r : α → α → Prop) :
    ∀a : α, rtc r a a := assume a, rtc.base r a

lemma rtc_left_next {α : Type} (r : α → α → Prop) :
    ∀a b c: α, r a b → rtc r b c → rtc r a c := begin
    intros a b c r_a_b rtc_r_b_c,
    induction rtc_r_b_c,
        case rtc.base : x {
            apply rtc.next,
            apply rtc.base,
            assumption
        },
        case rtc.next : b x c rtc_r_b_x r_x_c {
            apply rtc.next,
            apply rtc_r_b_c_ih,
            assumption,
            assumption
        }
end

lemma rtc_transitive {α : Type} (r : α → α → Prop) :
    ∀a b c: α, rtc r a b → rtc r b c → rtc r a c := begin
    intros a b c rtc_r_a_b rtc_r_b_c,
    induction rtc_r_a_b,
        case rtc.base : x {
            assumption
        },
        case rtc.next : a x b rtc_r_a_x r_x_b {
            apply rtc_r_a_b_ih,
            apply rtc_left_next,
            assumption,
            assumption
        }
end

-- Main Lemma
definition weakly_confluent {α : Type} (lt: α → α → Prop) : Prop :=
    ∀ (a b c : α), lt b a → lt c b → ∃ d : α, rtc lt d b ∧ rtc lt d c

definition confluent {α : Type} (lt: α → α → Prop) : Prop :=
    ∀ (a b c : α), rtc lt b a → rtc lt c b → ∃ d : α, rtc lt d b ∧ rtc lt d c

lemma newmans_lemma {α : Type}
    {r : α → α → Prop}
    (wc : weakly_confluent r)
    (wf : well_founded r) :
    confluent r :=
    well_founded.fix wf begin
        intros a ih b c blta cltb,
        cases blta,
            case rtc.base {
                existsi c,
                constructor,
                assumption,
                apply rtc.base
            },
        -- main case
        case rtc.next : x r_b_x rtc_r_x_a {
            sorry
        }
    end