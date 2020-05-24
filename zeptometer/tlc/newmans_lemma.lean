-- Reflexive transitive closure
 inductive rtc {α : Type} (r : α → α → Prop) : α → α → Prop
| base : ∀ a : α, rtc a a
| next : ∀ a b c : α, rtc a b → r b c → rtc a c

lemma rtc_reflexive {α : Type} {r : α → α → Prop} :
    ∀a : α, rtc r a a := assume a, rtc.base r a

lemma rtc_left_next {α : Type} {r : α → α → Prop} :
    ∀{a b c: α}, r a b → rtc r b c → rtc r a c := begin
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

lemma rtc_transitive {α : Type} {r : α → α → Prop} :
    ∀{a b c: α}, rtc r a b → rtc r b c → rtc r a c := begin
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
    ∀ {a b c : α}, lt b a → lt c a → ∃ d : α, rtc lt d b ∧ rtc lt d c

definition confluent {α : Type} (lt: α → α → Prop) : Prop :=
    ∀ {a b c : α}, rtc lt b a → rtc lt c a → ∃ d : α, rtc lt d b ∧ rtc lt d c

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
        case rtc.next : x rtc_r_b_x r_x_a {
            cases cltb,
                case rtc.base {
                    existsi b,
                    constructor,
                    apply rtc.base,
                    apply rtc.next,
                    assumption,
                    assumption
                },
            -- main case
            case rtc.next : y rtc_r_c_y r_y_a {
                -- step 1: Get d1 from weak confluence
                have d1exists : ∃d1, rtc r d1 x ∧ rtc r d1 y := 
                    wc r_x_a r_y_a,
                cases d1exists with d1 rtc_r_d1_xandy,
                cases rtc_r_d1_xandy with rtc_r_d1_x rtc_r_d1_y,
                -- step 2: Get d2 from induction hypothesis
                have d2exists : ∃d2, rtc r d2 b ∧ rtc r d2 d1 :=
                    ih x r_x_a rtc_r_b_x rtc_r_d1_x,
                cases d2exists with d2 rtc_r_d2_bandd1,
                cases rtc_r_d2_bandd1 with rtc_r_d2_b rtc_r_d2_d1,
                have rtc_r_d2_y : rtc r d2 y :=
                    rtc_transitive rtc_r_d2_d1 rtc_r_d1_y,
                -- step 3: Get d3 from induction hypothesis
                have d3exists : ∃d3, rtc r d3 c ∧ rtc r d3 d2 :=
                    ih y r_y_a rtc_r_c_y rtc_r_d2_y,
                cases d3exists with d3 rtc_r_d3_candd2,
                cases rtc_r_d3_candd2 with rtc_r_d3_c rtc_r_d3_d2,
                -- step 4: Show d3 is the confluent point
                existsi d3,
                constructor, {
                    exact rtc_transitive rtc_r_d3_d2 rtc_r_d2_b,
                }, {
                    assumption
                }
            }
        }
    end