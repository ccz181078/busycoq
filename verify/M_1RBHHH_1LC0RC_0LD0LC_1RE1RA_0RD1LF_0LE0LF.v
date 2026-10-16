(* 1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm := Eval compute in
  (TM_from_str "1RB---_1LC0RC_0LD0LC_1RE1RA_0RD1LF_0LE0LF").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Open Scope nat_scope.

(* ---------- Elementary block transitions ---------- *)

Lemma rule_E_b (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 0; 0; 1]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 1; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_aa (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 1]%sym *> r) -->+
  (1%sym >> ([1; 1; 0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_ab (l r : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 0; 0; 1]%sym *> r) -->+
  (1%sym >> ([0; 1; 1; 1; 0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_a (l r : side) :
  (1%sym >> ([0; 1]%sym *> l)) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_b (l r : side) :
  (1%sym >> ([1; 1; 0; 1]%sym *> l)) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> l) {{C}}> ([0; 0; 0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_C_nil (r : side) :
  (1%sym >> 0inf%sym) {{C}}> ([0; 0]%sym *> r) -->+
  (1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_E_end (l : side) :
  (1%sym >> l) {{E}}> ([0; 1; 0; 1; 0; 0; 1]%sym *> 0inf%sym) -->+
  l {{E}}> ([1; 0; 0; 0; 1; 0; 0; 1]%sym *> 0inf%sym).
Proof. start_progress. Qed.

Lemma rule_EL_a (l r : side) :
  ([0; 1]%sym *> l) {{E}}> (1%sym >> r) -->+
  l {{E}}> ([1; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_EL_b (l r : side) :
  ([1; 1; 0; 1]%sym *> l) {{E}}> (1%sym >> r) -->+
  l {{E}}> ([1; 0; 0; 0; 1]%sym *> r).
Proof. start_progress. Qed.

Lemma rule_EL_nil (r : side) :
  0inf%sym {{E}}> (1%sym >> r) -->+
  (1%sym >> 0inf%sym) {{E}}> ([0; 1]%sym *> r).
Proof. start_progress. Qed.

(* ---------- Token abbreviations and round combinators ---------- *)

Notation T0 := ([0; 0; 0; 1]%sym).
Notation T1 := ([0; 1; 0; 1]%sym).
Notation T2 := ([0; 1; 0; 0; 0; 1]%sym).

Definition RoundC (r r' : side) : Prop :=
  forall l : side,
    (1%sym >> l) {{E}}> ([0; 1]%sym *> r) -->+
    (1%sym >> l) {{C}}> ([0; 0]%sym *> r').

Definition RoundA (r r_out : side) : Prop :=
  forall l : side,
    (1%sym >> ([0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r) -->+
    (1%sym >> l) {{C}}> ([0; 0]%sym *> r_out).

Lemma roundC_to_roundA {r r' : side} (H : RoundC r r') :
  RoundA r ([0; 1]%sym *> r').
Proof.
  intro l.
  eapply progress_trans; [exact (H ([0; 1]%sym *> l)) |].
  exact (rule_C_a l r').
Qed.

Lemma roundC_T0 (u : side) :
  RoundC (T0 *> u) (T1 *> u).
Proof.
  intro l. exact (rule_E_b l u).
Qed.

Lemma roundA_T0 (u : side) :
  RoundA (T0 *> u) (T1 *> ([0; 1]%sym *> u)).
Proof.
  exact (roundC_to_roundA (roundC_T0 u)).
Qed.

Lemma roundC_T1 {u u' : side} (H : RoundC u u') :
  RoundC (T1 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_aa l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_C_b l u').
Qed.

Lemma roundA_T1 {u u' : side} (H : RoundC u u') :
  RoundA (T1 *> u) (T2 *> u').
Proof.
  exact (roundC_to_roundA (roundC_T1 H)).
Qed.

Lemma roundC_T2 {u u' : side} (H : RoundA u u') :
  RoundC (T2 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_ab l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_C_b l u').
Qed.

Lemma roundA_T2 {u u' : side} (H : RoundA u u') :
  RoundA (T2 *> u) (T2 *> u').
Proof.
  exact (roundC_to_roundA (roundC_T2 H)).
Qed.

Definition RoundE (r r' : side) : Prop :=
  forall l : side,
    (1%sym >> l) {{E}}> ([0; 1]%sym *> r) -->+
    l {{E}}> (1%sym >> r').

Definition RoundEA (r r_out : side) : Prop :=
  forall l : side,
    (1%sym >> ([0; 1]%sym *> l)) {{E}}> ([0; 1]%sym *> r) -->+
    l {{E}}> (1%sym >> r_out).

Lemma roundE_to_roundEA {r r' : side} (H : RoundE r r') :
  RoundEA r ([0; 1]%sym *> r').
Proof.
  intro l.
  eapply progress_trans; [exact (H ([0; 1]%sym *> l)) |].
  exact (rule_EL_a l r').
Qed.

Lemma roundE_end :
  RoundE ([0; 1; 0; 0; 1]%sym *> 0inf%sym) ([0; 0; 0; 1; 0; 0; 1]%sym *> 0inf%sym).
Proof.
  intro l. exact (rule_E_end l).
Qed.

Lemma roundE_T1 {u u' : side} (H : RoundE u u') :
  RoundE (T1 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_aa l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_EL_b l u').
Qed.

Lemma roundEA_T1 {u u' : side} (H : RoundE u u') :
  RoundEA (T1 *> u) (T2 *> u').
Proof.
  exact (roundE_to_roundEA (roundE_T1 H)).
Qed.

Lemma roundE_T2 {u u' : side} (H : RoundEA u u') :
  RoundE (T2 *> u) (T0 *> u').
Proof.
  intro l.
  eapply progress_trans; [exact (rule_E_ab l u) |].
  eapply progress_trans; [exact (H ([1; 1; 0; 1]%sym *> l)) |].
  exact (rule_EL_b l u').
Qed.

Lemma roundEA_T2 {u u' : side} (H : RoundEA u u') :
  RoundEA (T2 *> u) (T2 *> u').
Proof.
  exact (roundE_to_roundEA (roundE_T2 H)).
Qed.

Definition cfgE0 (r : side) : Q * tape :=
  (1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> r).

Lemma sweep_step {r r_out : side} (H : RoundA r r_out) :
  cfgE0 r -->+ cfgE0 r_out.
Proof.
  eapply progress_trans; [exact (H 0inf%sym) |].
  exact (rule_C_nil r_out).
Qed.

Lemma era_end_step {r r_era r_next : side}
    (H1 : RoundEA r r_era) (H2 : RoundC r_era r_next) :
  cfgE0 r -->+ cfgE0 r_next.
Proof.
  eapply progress_trans; [exact (H1 0inf%sym) |].
  eapply progress_trans; [exact (rule_EL_nil r_era) |].
  eapply progress_trans; [exact (H2 0inf%sym) |].
  exact (rule_C_nil r_next).
Qed.

Definition bot : side := [0; 0; 1]%sym *> 0inf%sym.
Definition bota : side := [0; 1; 0; 0; 1]%sym *> 0inf%sym.
Definition botc : side := [0; 1; 1]%sym *> 0inf%sym.

Lemma roundC_bot : RoundC bot botc.
Proof.
  intro l. unfold bot, botc. start_progress.
Qed.

Lemma roundC_botc : RoundC botc bot.
Proof.
  intro l. unfold bot, botc. start_progress.
Qed.

(* ---------- Multi-sweep StepsA and B3 acceleration ---------- *)

Inductive StepsA : nat -> side -> side -> Prop :=
  | StepsA_O (u : side) : StepsA 0 u u
  | StepsA_S (n : nat) (u v w : side) :
      RoundA u v -> StepsA n v w -> StepsA (S n) u w.

Lemma stepsA_trans {a b : nat} {u v w : side}
    (H1 : StepsA a u v) (H2 : StepsA b v w) :
  StepsA (a + b) u w.
Proof.
  induction H1 as [u | n u u1 v H _ IH].
  - exact H2.
  - cbn [Nat.add]. eapply StepsA_S; [exact H | exact (IH H2)].
Qed.

Lemma stepsA_T2 {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (T2 *> u) (T2 *> w).
Proof.
  induction H as [u | n u v w H1 _ IH].
  - apply StepsA_O.
  - eapply StepsA_S; [exact (roundA_T2 H1) | exact IH].
Qed.

Definition B3 (r : side) : side :=
  T2 *> (T2 *> (T2 *> r)).

Fixpoint powB3 (m : nat) (r : side) : side :=
  match m with
  | 0 => r
  | S m' => B3 (powB3 m' r)
  end.

Lemma powB3_B3 (m : nat) (r : side) :
  powB3 m (B3 r) = B3 (powB3 m r).
Proof.
  induction m as [| m IH]; cbn [powB3].
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

Lemma powB3_T2 (m : nat) (r : side) :
  powB3 m (T2 *> r) = T2 *> powB3 m r.
Proof.
  induction m as [| m IH]; cbn [powB3].
  - reflexivity.
  - unfold B3 at 1. rewrite IH. reflexivity.
Qed.

Lemma roundA_B3 {u u' : side} (H : RoundA u u') :
  RoundA (B3 u) (B3 u').
Proof.
  exact (roundA_T2 (roundA_T2 (roundA_T2 H))).
Qed.

Lemma roundA_powB3 (m : nat) {u u' : side} (H : RoundA u u') :
  RoundA (powB3 m u) (powB3 m u').
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (roundA_B3 IH).
Qed.

Lemma roundEA_B3 {u u' : side} (H : RoundEA u u') :
  RoundEA (B3 u) (B3 u').
Proof.
  exact (roundEA_T2 (roundEA_T2 (roundEA_T2 H))).
Qed.

Lemma roundEA_powB3 (m : nat) {u u' : side} (H : RoundEA u u') :
  RoundEA (powB3 m u) (powB3 m u').
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (roundEA_B3 IH).
Qed.

Lemma stepsA_B3 {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (B3 u) (B3 w).
Proof.
  exact (stepsA_T2 (stepsA_T2 (stepsA_T2 H))).
Qed.

Lemma stepsA_powB3 (m : nat) {n : nat} {u w : side} (H : StepsA n u w) :
  StepsA n (powB3 m u) (powB3 m w).
Proof.
  induction m as [| m IH]; cbn [powB3].
  - exact H.
  - exact (stepsA_B3 IH).
Qed.

Lemma step6_022 {v v_C : side} (HC : RoundC v v_C) :
  StepsA 6 (T0 *> (T2 *> (T2 *> v))) (B3 (T0 *> (T2 *> v_C))).
Proof.
  eapply StepsA_S; [exact (roundA_T0 (T2 *> (T2 *> v))) |].
  eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> v)))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T1 *> (T2 *> v)))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 v))))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> v))))) |].
  eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 HC))))) |].
  apply StepsA_O.
Qed.

Lemma finish8_22 {v v_C : side} (HC : RoundC v v_C) :
  StepsA 8 (T0 *> (T2 *> (T2 *> v))) (B3 (T2 *> (T0 *> (T1 *> v_C)))).
Proof.
  assert (H2 : StepsA 2 (T0 *> (T2 *> v_C)) (T2 *> (T0 *> (T1 *> v_C)))).
  { eapply StepsA_S; [exact (roundA_T0 (T2 *> v_C)) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 v_C))) |].
    apply StepsA_O. }
  exact (stepsA_trans (step6_022 HC) (stepsA_B3 H2)).
Qed.

Lemma cross_B3 {u u1 u2 u3 : side}
    (H1 : RoundA u u1) (H2 : RoundA u1 u2) (H3 : RoundA u2 u3) :
  StepsA 12 (T0 *> B3 u) (B3 (B3 (T0 *> u3))).
Proof.
  assert (H4 : StepsA 4 (T0 *> (T1 *> (T0 *> u1))) (T2 *> (T2 *> (T0 *> u3)))).
  { eapply StepsA_S; [exact (roundA_T0 (T1 *> (T0 *> u1))) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T2 H2))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T0 *> u2))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T2 H3))) |].
    apply StepsA_O. }
  exact (stepsA_trans (finish8_22 (roundC_T2 H1)) (stepsA_B3 (stepsA_T2 H4))).
Qed.

Lemma cross_powB3 (m : nat) : forall {u w : side},
  StepsA (3 * m) u w ->
  StepsA (12 * m) (T0 *> powB3 m u) (powB3 (2 * m) (T0 *> w)).
Proof.
  induction m as [| m IH]; intros u w H.
  - cbn in H |- *.
    inverts H.
    apply StepsA_O.
  - replace (3 * S m) with (S (S (S (3 * m)))) in H by lia.
    inverts H as H1 H_1.
    inverts H_1 as H2 H_2.
    inverts H_2 as H3 Hrest.
    pose proof (cross_B3 (roundA_powB3 m H1) (roundA_powB3 m H2) (roundA_powB3 m H3)) as Hc.
    pose proof (stepsA_B3 (stepsA_B3 (IH _ _ Hrest))) as Hrec.
    pose proof (stepsA_trans Hc Hrec) as Htot.
    replace (12 * S m) with (12 + 12 * m) by lia.
    replace (2 * S m) with (S (S (2 * m))) by lia.
    cbn [powB3].
    exact Htot.
Qed.

(* ---------- Era structure and inductive step ---------- *)

Definition fEra (k : nat) (u : side) : side :=
  T2 *> powB3 (k + 1) (T1 *> (T1 *> u)).

Inductive StepEra (k : nat) (u w : side) : Prop :=
  | StepEra_mk (u_E w_0 w_last v_C : side) :
      RoundE u u_E ->
      RoundC ([0; 1]%sym *> u_E) w_0 ->
      StepsA (3 * k + 2) w_0 w_last ->
      RoundC w_last v_C ->
      w = [0; 1]%sym *> v_C ->
      StepEra k u w.

Lemma stepEra_next {k : nat} {u w : side} (H : StepEra k u w) :
  StepEra (2 * (2 * k + 2) + 2) (fEra k u) (fEra (2 * k + 2) w).
Proof.
  destruct H as [u_E w_0 w_last v_C HE HC0 HA HClast Hw].
  eapply StepEra_mk with
    (u_E := T0 *> powB3 (k + 1) (T2 *> (T0 *> u_E)))
    (w_0 := T0 *> powB3 (k + 1) (T2 *> (T1 *> ([0; 1]%sym *> u_E))))
    (w_last := T2 *> powB3 ((2 * k + 2) + 1) (T0 *> (T1 *> v_C)))
    (v_C := T0 *> powB3 ((2 * k + 2) + 1) (T1 *> (T1 *> w))).
  - exact (roundE_T2 (roundEA_powB3 (k + 1) (roundEA_T1 (roundE_T1 HE)))).
  - exact (roundC_T2 (roundA_powB3 (k + 1) (roundA_T2 (roundA_T0 u_E)))).
  - assert (H3 : StepsA (3 * (k + 1)) (T2 *> (T1 *> ([0; 1]%sym *> u_E))) (T2 *> (T2 *> w_last))).
    { replace (3 * (k + 1)) with (S (3 * k + 2)) by lia.
      apply stepsA_T2.
      eapply StepsA_S; [exact (roundA_T1 HC0) | exact (stepsA_T2 HA)]. }
    pose proof (cross_powB3 (k + 1) H3) as Hcross.
    pose proof (stepsA_powB3 (2 * (k + 1)) (finish8_22 HClast)) as Hfin.
    pose proof (stepsA_trans Hcross Hfin) as Htot.
    assert (Heq_t : powB3 (2 * (k + 1)) (B3 (T2 *> (T0 *> (T1 *> v_C)))) =
                    T2 *> powB3 ((2 * k + 2) + 1) (T0 *> (T1 *> v_C))).
    { rewrite powB3_B3.
      change (B3 (powB3 (2 * (k + 1)) (T2 *> (T0 *> (T1 *> v_C)))))
        with (powB3 (S (2 * (k + 1))) (T2 *> (T0 *> (T1 *> v_C)))).
      replace (S (2 * (k + 1))) with ((2 * k + 2) + 1) by lia.
      apply powB3_T2. }
    rewrite Heq_t in Htot.
    replace (12 * (k + 1) + 8) with (3 * (2 * (2 * k + 2) + 2) + 2) in Htot by lia.
    exact Htot.
  - rewrite Hw.
    exact (roundC_T2 (roundA_powB3 ((2 * k + 2) + 1) (roundA_T0 (T1 *> v_C)))).
  - reflexivity.
Qed.

Definition u_m2 : side :=
  T2 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))).

Definition u_m1 : side :=
  T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T1 *> bota))))))))).

Lemma stepEra_m2 : StepEra 2 u_m2 u_m1.
Proof.
  eapply StepEra_mk with
    (u_E := T0 *> (T2 *> (T0 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))
    (w_0 := T0 *> (T2 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
    (w_last := T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T0 *> (T1 *> (T2 *> (T2 *> (T1 *> bota))))))))))
    (v_C := T0 *> (T2 *> (T2 *> (T2 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T1 *> bota)))))))))).
  - exact (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))).
  - exact (roundC_T2 (roundA_T2 (roundA_T0 (T2 *> (T2 *> (T2 *> (T0 *> bot))))))).
  - cbn [Nat.mul Nat.add].
    eapply StepsA_S; [exact (roundA_T0 (T2 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot)))))))) |].
    eapply StepsA_S; [exact (roundA_T1 (roundC_T1 (roundC_T0 (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T0 (T1 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T0 *> (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
    eapply StepsA_S; [exact (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T1 *> bota)))))))))) |].
    apply StepsA_O.
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T1 *> bota)))))))))).
  - reflexivity.
Qed.

Lemma stepEra_m1 : StepEra 6 u_m1 (fEra 2 u_m2).
Proof.
  eapply StepEra_mk with
    (u_E := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T2 *> (T0 *> (T2 *> (T2 *> (T0 *> bot)))))))))))
    (w_0 := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))))))
    (w_last := T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))
    (v_C := T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> (T1 *> (T2 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))).
  - exact (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))))))).
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))))).
  - pose proof (cross_B3
      (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
      (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T2 *> (T2 *> (T0 *> bot))))))))
      (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) as Hc12.
    pose proof (stepsA_B3 (stepsA_B3 (finish8_22 (roundC_T2 (roundA_T0 (T0 *> (T2 *> (T2 *> (T1 *> bota))))))))) as Hf8.
    exact (stepsA_trans Hc12 Hf8).
  - exact (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))).
  - reflexivity.
Qed.

Lemma stepsA_run {n : nat} {v w : side} (H2 : StepsA n v w) :
  forall {u : side}, cfgE0 u -->+ cfgE0 v -> cfgE0 u -->+ cfgE0 w.
Proof.
  induction H2 as [v | n v v1 w Ha _ IH]; intros u H1.
  - exact H1.
  - apply IH. eapply progress_trans; [exact H1 | exact (sweep_step Ha)].
Qed.

Lemma stepEra_run {k : nat} {u w : side} (H : StepEra k u w) :
  cfgE0 u -->+ cfgE0 w.
Proof.
  destruct H as [u_E w_0 w_last v_C HE HC0 HA HClast Hw].
  rewrite Hw.
  assert (H0 : cfgE0 u -->+ cfgE0 w_0) by exact (era_end_step (roundE_to_roundEA HE) HC0).
  assert (H1 : cfgE0 u -->+ cfgE0 w_last) by exact (stepsA_run HA H0).
  eapply progress_trans; [exact H1 | exact (sweep_step (roundC_to_roundA HClast))].
Qed.

Lemma init_to_botc : c0 -->* cfgE0 botc.
Proof.
  unfold cfgE0, botc.
  change ((1%sym >> ([0; 1]%sym *> 0inf%sym)) {{E}}> ([0; 1]%sym *> ([0; 1; 1]%sym *> 0inf%sym)))
    with ((0inf%sym <* [1; 0; 1]%sym) {{E}}> ([0; 1; 0; 1; 1]%sym *> 0inf%sym)).
  solve_init.
Qed.

Lemma botc_to_u0 : cfgE0 botc -->+ cfgE0 (fEra 2 u_m2).
Proof.
  eapply progress_trans; [exact (sweep_step (roundC_to_roundA roundC_botc)) |].
  eapply progress_trans; [exact (era_end_step (roundE_to_roundEA roundE_end) (roundC_T2 (roundC_to_roundA roundC_bot))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 ([0; 1]%sym *> botc))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 roundC_botc))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 bot))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T1 roundE_end)) (roundC_T2 (roundA_T2 (roundA_T0 bot)))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T1 *> bota)))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T1 *> bota))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T1 *> bota))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T1 roundC_bot)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T0 *> botc)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T0 botc)))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> ([0; 1]%sym *> botc))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 roundC_botc))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> bot))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundC_to_roundA roundC_bot)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 ([0; 1]%sym *> botc)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 roundC_botc)))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))) |].
  eapply progress_trans; [exact (era_end_step (roundEA_T2 (roundEA_T2 (roundEA_T1 (roundE_T2 (roundEA_T1 (roundE_T2 (roundEA_T2 (roundEA_T2 (roundEA_T2 (roundEA_T1 roundE_end)))))))))) (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T0 (T2 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T0 (T1 *> (T2 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T1 (roundC_T0 (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T0 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T2 *> (T2 *> (T2 *> (T2 *> (T2 *> (T0 *> bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 bot)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T0 *> (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T2 (roundA_T0 (T2 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T0 *> (T1 *> (T1 *> (T0 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T2 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota)))))))))))))))))) |].
  eapply progress_trans; [exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T1 (roundC_T1 (roundC_T0 (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))) |].
  exact (sweep_step (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T2 (roundA_T0 (T1 *> (T0 *> (T1 *> (T2 *> (T2 *> (T2 *> (T1 *> bota))))))))))))))))))).
Qed.

(* ---------- Top-level invariant and non-halting ---------- *)

Definition Hub (s : nat * side * side) : Q * tape :=
  let '(k, u, w) := s in cfgE0 u.

Definition InvP (s : nat * side * side) : Prop :=
  let '(k, u, w) := s in StepEra k u w /\ StepEra (2 * k + 2) w (fEra k u).

Lemma start : c0 -->* Hub (14, fEra 2 u_m2, fEra 6 u_m1).
Proof.
  unfold Hub.
  eapply evstep_trans; [exact init_to_botc |].
  apply progress_evstep.
  exact botc_to_u0.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := Hub (14, fEra 2 u_m2, fEra 6 u_m1)).
  - exact start.
  - eapply progress_nonhalt_cond with
      (C := Hub) (P := InvP) (i0 := (14, fEra 2 u_m2, fEra 6 u_m1)).
    + intros [[k u] w] [H1 H2].
      exists (2 * k + 2, w, fEra k u).
      split.
      * exact (stepEra_run H1).
      * split; [exact H2 | exact (stepEra_next H1)].
    + split; [exact (stepEra_next stepEra_m2) | exact (stepEra_next stepEra_m1)].
Qed.

Print Assumptions nonhalt.
