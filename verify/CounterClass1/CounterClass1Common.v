Require Import Lia.
Require Import Compare_dec.
Require Import PeanoNat.
Require Import List.
Require Import Bool.
From BusyCoq Require Import LibTactics.

Open Scope nat.
Import ListNotations.

(* The row/particle machinery only needs the carry rule and the two ordinary
   overflow rules.  Keeping that smaller interface explicit lets the K5
   system reuse the same Boolean-pointer proofs after shifting its fourth
   parameter by one. *)
Record K4CoreRules (P: nat -> nat -> nat -> nat -> Prop) := {
  k4core_inc01: forall a c d,
    P a 0 (1+c) d -> P (1+a) 0 c (4+d);
  k4core_rov: forall a b c d c' d',
    P a b c (3+d) -> P c d c' d' -> P a (2+b) c' (1+d');
  k4core_rov': forall a b c d c' d',
    P a b c (4+d) -> P c d (1+c') d' -> P a (2+b) c' (4+d')
}.

Arguments k4core_inc01 {P} _ _ _ _ _.
Arguments k4core_rov {P} _ _ _ _ _ _ _ _ _.
Arguments k4core_rov' {P} _ _ _ _ _ _ _ _ _.

Record K4SimpleRules (P: nat -> nat -> nat -> nat -> Prop) := {
  k4_inc01: forall a c d,
    P a 0 (1+c) d -> P (1+a) 0 c (4+d);
  k4_inc1: forall a c d,
    P a 1 c d -> P (1+a) 0 c (1+d);
  k4_inc00_1: forall a b c,
    P a b (1+c) 1 -> P a (2+b) c 5;
  k4_inc00_2: forall a b c,
    P a b (2+c) 2 -> P a (2+b) c 8;
  k4_rov: forall a b c d c' d',
    P a b c (3+d) -> P c d c' d' -> P a (2+b) c' (1+d');
  k4_rov': forall a b c d c' d',
    P a b c (4+d) -> P c d (1+c') d' -> P a (2+b) c' (4+d');
  k4_lov1: forall a n,
    P a 0 0 (n*2) -> P (1+a) 1 (1+n) 1;
  k4_lov2: forall a b c d c' d' n,
    P a b c (5+d) -> P c d c' (4+d') ->
    P c' d' 0 (1+n*2) -> P a (3+b) (2+n) 1
}.

Arguments k4_inc01 {P} _ _ _ _ _.
Arguments k4_inc1 {P} _ _ _ _ _.
Arguments k4_inc00_1 {P} _ _ _ _ _.
Arguments k4_inc00_2 {P} _ _ _ _ _.
Arguments k4_rov {P} _ _ _ _ _ _ _ _ _.
Arguments k4_rov' {P} _ _ _ _ _ _ _ _ _.
Arguments k4_lov1 {P} _ _ _ _.
Arguments k4_lov2 {P} _ _ _ _ _ _ _ _ _ _ _.

Definition k4_core_of_simple {P} (R:K4SimpleRules P): K4CoreRules P :=
  {| k4core_inc01 := k4_inc01 R;
     k4core_rov := k4_rov R;
     k4core_rov' := k4_rov' R |}.

Coercion k4_core_of_simple : K4SimpleRules >-> K4CoreRules.

Record K4DirectRules (P: nat -> nat -> nat -> nat -> Prop) := {
  k4d_simple: K4SimpleRules P;
  k4d_rst0: P 0 1 0 5;
  k4d_lov3: forall a b d n,
    P a b 0 (4+d) -> P 0 d 0 (3+n*2) -> P a (6+b) (4+n) 1
}.

Arguments k4d_simple {P} _.
Arguments k4d_rst0 {P} _.
Arguments k4d_lov3 {P} _ _ _ _ _ _ _.

Definition K4OddPhase P (m q:nat) : Prop :=
  forall a t, a < m -> a+t=m+q ->
  P a (2*t+1) (m-q) (4*q+5).

Definition K4EvenPhase P (m q:nat) : Prop :=
  forall k t, k+t=q+1 ->
  P (m+k) (2*t) (m-q) (4*q+6).

Definition K4Phase P (m:nat) : Prop :=
  forall q, 2 <= q <= m ->
  K4OddPhase P m q /\ K4EvenPhase P m q.

Definition K4Prelude P (m:nat) : Prop :=
  P (m+1) 2 (m-2) 12 /\
  P m 2 (m-1) 8 /\
  P (m-1) 1 (m+1) 1 /\
  P m 4 (m-1) 10.

Definition K4Ready P (m:nat) : Prop :=
  K4Phase P m /\ K4Prelude P m.

(* TM2 and TM7 have one exceptional left segment at q=2.  It is absorbed
   before q=3, so their stable phase starts at q=3. *)
Definition K4Phase3 P (m:nat) : Prop :=
  forall q, 3 <= q <= m ->
  K4OddPhase P m q /\ K4EvenPhase P m q.

Definition K4Ready3 P (m:nat) : Prop :=
  K4Phase3 P m /\
  P m 4 (m-1) 10 /\
  P (m-1) 7 (m-2) 13.

Definition K4DirectBaseFacts P: Prop :=
  P 0 11 1 13 /\ P 1 9 1 13 /\ P 2 7 1 13 /\
  P 3 6 1 14 /\ P 4 4 1 14 /\ P 5 2 1 14 /\ P 6 0 1 14 /\
  P 4 2 1 12 /\ P 3 2 2 8 /\ P 2 1 4 1 /\ P 3 4 2 10 /\
  P 2 5 2 9 /\ P 0 13 0 17.

Definition K4Ready3BaseFacts P: Prop :=
  P 0 13 0 17 /\ P 1 11 0 17 /\ P 2 9 0 17 /\
  P 3 8 0 18 /\ P 4 6 0 18 /\ P 5 4 0 18 /\
  P 6 2 0 18 /\ P 7 0 0 18 /\
  P 3 4 2 10 /\ P 2 7 1 13.

Section SimpleK4.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4SimpleRules P.

Lemma k4_odd_phase_S m q:
  2 <= q < m ->
  K4OddPhase P m q -> K4OddPhase P m (S q).
Proof.
  intros Hq HO a [|t] Ha Hat.
  1: lia.
  applys_eq (k4_rov' R a (2*t+1) (m-q) (4*q+1)
    (m-S q) (4*q+5)); try lia.
  - applys_eq (HO a t); lia.
  - applys_eq (HO (m-q) (2*q)); lia.
Qed.

Lemma k4_even_phase_S m q:
  2 <= q < m -> K4OddPhase P m (S q) ->
  K4EvenPhase P m q -> K4EvenPhase P m (S q).
Proof.
  intros Hq HO HE k [|t] Hkt.
  - applys_eq (k4_inc01 R (m+q+1) (m-S q) (4*q+6)); try lia.
    applys_eq (HE (q+1) 0); lia.
  - applys_eq (k4_rov R (m+k) (2*t) (m-q) (4*q+3)
      (m-S q) (4*q+9)); try lia.
    + applys_eq (HE k t); lia.
    + applys_eq (HO (m-q) (2*q+1)); lia.
Qed.

Lemma k4_phase_iter m q n:
  2 <= q -> q+n <= m ->
  K4OddPhase P m q -> K4EvenPhase P m q ->
  K4OddPhase P m (q+n) /\ K4EvenPhase P m (q+n).
Proof.
  intros Hq Hn HO HE.
  induction n as [|n IH].
  - replace (q+0) with q by lia. exact (conj HO HE).
  - destruct IH as [HO' HE']; try lia.
    replace (q+S n) with (S (q+n)) by lia.
    split.
    + apply k4_odd_phase_S with (q:=q+n); try assumption; lia.
    + apply k4_even_phase_S with (q:=q+n); try assumption; try lia.
      apply k4_odd_phase_S with (q:=q+n); try assumption; lia.
Qed.

Lemma k4_phase_from_base m:
  2 <= m -> K4OddPhase P m 2 -> K4EvenPhase P m 2 -> K4Phase P m.
Proof.
  intros Hm HO HE q Hq.
  replace q with (2+(q-2)) by lia.
  apply k4_phase_iter; assumption || lia.
Qed.

Lemma k4_phase3_from_base m:
  3 <= m -> K4OddPhase P m 3 -> K4EvenPhase P m 3 -> K4Phase3 P m.
Proof.
  intros Hm HO HE q Hq.
  replace q with (3+(q-3)) by lia.
  apply k4_phase_iter; assumption || lia.
Qed.

Lemma k4_ready3_from_facts:
  K4DirectBaseFacts P -> K4Ready P 3.
Proof.
  intros [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10
    [H11 H12]]]]]]]]]]]].
  split.
  - apply k4_phase_from_base; try lia.
    + intros a t Ha Hat.
      assert (a=0 \/ a=1 \/ a=2) as Ha' by lia.
      destruct Ha' as [Ha'|[Ha'|Ha']]; subst a.
      * replace t with 5 by lia. exact H0.
      * replace t with 4 by lia. exact H1.
      * replace t with 3 by lia. exact H2.
    + intros k t Hkt.
      assert (k=0 \/ k=1 \/ k=2 \/ k=3) as Hk by lia.
      destruct Hk as [Hk|[Hk|[Hk|Hk]]]; subst k.
      * replace t with 3 by lia. exact H3.
      * replace t with 2 by lia. exact H4.
      * replace t with 1 by lia. exact H5.
      * replace t with 0 by lia. exact H6.
  - unfold K4Prelude; repeat split; assumption.
Qed.

Lemma k4_ready3_base_from_facts:
  K4Ready3BaseFacts P -> K4Ready3 P 3.
Proof.
  intros [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 H9]]]]]]]]].
  split.
  - apply k4_phase3_from_base; try lia.
    + intros a t Ha Hat.
      assert (a=0 \/ a=1 \/ a=2) as Ha' by lia.
      destruct Ha' as [Ha'|[Ha'|Ha']]; subst a.
      * replace t with 6 by lia. exact H0.
      * replace t with 5 by lia. exact H1.
      * replace t with 4 by lia. exact H2.
    + intros k t Hkt.
      assert (k=0 \/ k=1 \/ k=2 \/ k=3 \/ k=4) as Hk by lia.
      destruct Hk as [Hk|[Hk|[Hk|[Hk|Hk]]]]; subst k.
      * replace t with 4 by lia. exact H3.
      * replace t with 3 by lia. exact H4.
      * replace t with 2 by lia. exact H5.
      * replace t with 1 by lia. exact H6.
      * replace t with 0 by lia. exact H7.
  - exact (conj H8 H9).
Qed.

Lemma k4_phase_next_base m:
  2 <= m -> K4Phase P m ->
  (forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+5) 1) ->
  K4OddPhase P (2*m+3) 2 /\ K4EvenPhase P (2*m+3) 2 /\
  K4Prelude P (2*m+3).
Proof.
  intros Hm HP HL.
  destruct (HP m) as [HO HE]; try lia.
  assert (HZ := HO 0 (2*m) ltac:(lia) ltac:(lia)).
  assert (HB: forall k t, k+t=m+2 ->
    P (m+k) (2*t+1) (2*m+4) 1).
  { intros k [|t] Hkt.
    - applys_eq (k4_lov1 R (2*m+1) (2*m+3)); try lia.
      applys_eq (HE (m+1) 0); lia.
    - applys_eq (k4_lov2 R (m+k) (2*t) 0 (4*m+1)
        0 (4*m+1) (2*m+2)); try lia.
      1: applys_eq (HE k t); lia.
      all: applys_eq HZ; lia. }
  assert (HC: P (2*m+3) 0 (2*m+4) 2).
  { applys_eq (k4_inc1 R (2*m+2) (2*m+4) 1); try lia.
    applys_eq (HB (m+2) 0); lia. }
  assert (HR: forall k t, k+t=m+2 ->
    P (m+k) (2*t+3) (2*m+3) 5).
  { intros k t Hkt.
    applys_eq (k4_inc00_1 R (m+k) (2*t+1) (2*m+3)); try lia.
    applys_eq (HB k t); lia. }
  assert (HD0: P (2*m+3) 2 (2*m+2) 8).
  { applys_eq (k4_inc00_2 R (2*m+3) 0 (2*m+2)); try lia.
    applys_eq HC; lia. }
  assert (HD1: P (2*m+4) 0 (2*m+3) 6).
  { applys_eq (k4_inc01 R (2*m+3) (2*m+3) 2); try lia.
    applys_eq HC; lia. }
  assert (HL9: forall a t, a<m -> a+t=2*m ->
    P a (2*t+9) (2*m+4) 5).
  { intros a t Ha Hat.
    applys_eq (k4_inc00_1 R a (2*t+7) (2*m+4)); try lia.
    applys_eq (HL a t); lia. }
  assert (HR9: forall k t, k+t=m+2 ->
    P (m+k) (2*t+5) (2*m+2) 9).
  { intros k t Hkt.
    applys_eq (k4_rov R (m+k) (2*t+3) (2*m+3) 2
      (2*m+2) 8); try lia.
    - applys_eq (HR k t); lia.
    - applys_eq HD0; lia. }
  assert (HDIAG: P (2*m+2) 5 (2*m+2) 9).
  { applys_eq (HR9 (m+2) 0); lia. }
  assert (HF0: P (2*m+3) 4 (2*m+2) 10).
  { applys_eq (k4_rov R (2*m+3) 2 (2*m+2) 5
      (2*m+2) 9); try lia.
    - applys_eq HD0; lia.
    - applys_eq HDIAG; lia. }
  assert (HF1: P (2*m+4) 2 (2*m+1) 12).
  { applys_eq (k4_rov' R (2*m+4) 0 (2*m+3) 2
      (2*m+1) 8); try lia.
    - applys_eq HD1; lia.
    - applys_eq HD0; lia. }
  assert (HF2: P (2*m+5) 0 (2*m+2) 10).
  { applys_eq (k4_inc01 R (2*m+4) (2*m+2) 6); try lia.
    applys_eq HD1; lia. }
  assert (HOn: K4OddPhase P (2*m+3) 2).
  { intros a t Ha Hat.
    destruct (Compare_dec.le_lt_dec m a) as [Ham|Ham].
    - applys_eq (k4_rov' R a (2*(t-3)+5) (2*m+2) 5
        (2*m+1) 9); try lia.
      + applys_eq (HR9 (a-m) (t-3)); lia.
      + applys_eq HDIAG; lia.
    - applys_eq (k4_rov R a (2*(t-5)+9) (2*m+4) 2
        (2*m+1) 12); try lia.
      + applys_eq (HL9 a (t-5)); lia.
      + applys_eq HF1; lia. }
  assert (HEn: K4EvenPhase P (2*m+3) 2).
  { intros [|[|[|[|k]]]] t Hkt; try lia.
    - assert (t=3) by lia; subst t.
      applys_eq (k4_rov R (2*m+3) 4 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF0; lia.
      applys_eq (HOn (2*m+2) 3); lia.
    - assert (t=2) by lia; subst t.
      applys_eq (k4_rov R (2*m+4) 2 (2*m+1) 9
        (2*m+1) 13); try lia.
      1: applys_eq HF1; lia.
      applys_eq (HOn (2*m+1) 4); lia.
    - assert (t=1) by lia; subst t.
      applys_eq (k4_rov R (2*m+5) 0 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF2; lia.
      applys_eq (HOn (2*m+2) 3); lia.
    - assert (t=0) by lia; subst t.
      applys_eq (k4_inc01 R (2*m+5) (2*m+1) 10); try lia.
      applys_eq HF2; lia. }
  split; [exact HOn|].
  split; [exact HEn|].
  repeat split.
  - applys_eq HF1; lia.
  - applys_eq HD0; lia.
  - applys_eq (HB (m+2) 0); lia.
  - applys_eq HF0; lia.
Qed.

Lemma k4_ready_next m:
  2 <= m -> K4Ready P m ->
  (forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+5) 1) ->
  K4Ready P (2*m+3).
Proof.
  intros Hm [HP _] HL.
  destruct (k4_phase_next_base m Hm HP HL) as [HO [HE Hpre]].
  split.
  - apply k4_phase_from_base; try lia; assumption.
  - exact Hpre.
Qed.

Lemma k4_phase_next_base5 m:
  2 <= m -> K4Phase P m ->
  (forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+3) 5) ->
  K4OddPhase P (2*m+3) 2 /\ K4EvenPhase P (2*m+3) 2 /\
  K4Prelude P (2*m+3).
Proof.
  intros Hm HP HL5.
  destruct (HP m) as [HO HE]; try lia.
  assert (HZ := HO 0 (2*m) ltac:(lia) ltac:(lia)).
  assert (HB: forall k t, k+t=m+2 ->
    P (m+k) (2*t+1) (2*m+4) 1).
  { intros k [|t] Hkt.
    - applys_eq (k4_lov1 R (2*m+1) (2*m+3)); try lia.
      applys_eq (HE (m+1) 0); lia.
    - applys_eq (k4_lov2 R (m+k) (2*t) 0 (4*m+1)
        0 (4*m+1) (2*m+2)); try lia.
      1: applys_eq (HE k t); lia.
      all: applys_eq HZ; lia. }
  assert (HC: P (2*m+3) 0 (2*m+4) 2).
  { applys_eq (k4_inc1 R (2*m+2) (2*m+4) 1); try lia.
    applys_eq (HB (m+2) 0); lia. }
  assert (HR5: forall k t, k+t=m+2 ->
    P (m+k) (2*t+3) (2*m+3) 5).
  { intros k t Hkt.
    applys_eq (k4_inc00_1 R (m+k) (2*t+1) (2*m+3)); try lia.
    applys_eq (HB k t); lia. }
  assert (HD0: P (2*m+3) 2 (2*m+2) 8).
  { applys_eq (k4_inc00_2 R (2*m+3) 0 (2*m+2)); try lia.
    applys_eq HC; lia. }
  assert (HD1: P (2*m+4) 0 (2*m+3) 6).
  { applys_eq (k4_inc01 R (2*m+3) (2*m+3) 2); try lia.
    applys_eq HC; lia. }
  assert (H5: forall a t, a<2*m+3 -> a+t=2*m+3 ->
    P a (2*t+1) (2*m+3) 5).
  { intros a t Ha Hat.
    destruct (Compare_dec.le_lt_dec m a) as [Ham|Ham].
    - applys_eq (HR5 (a-m) (t-1)); lia.
    - applys_eq (HL5 a (t-3)); lia. }
  assert (H9: forall a t, a<2*m+3 -> a+t=2*m+4 ->
    P a (2*t+1) (2*m+2) 9).
  { intros a t Ha Hat.
    applys_eq (k4_rov R a (2*(t-1)+1) (2*m+3) 2
      (2*m+2) 8); try lia.
    - applys_eq (H5 a (t-1)); lia.
    - applys_eq HD0; lia. }
  assert (HDIAG: P (2*m+2) 5 (2*m+2) 9).
  { applys_eq (H9 (2*m+2) 2); lia. }
  assert (HF0: P (2*m+3) 4 (2*m+2) 10).
  { applys_eq (k4_rov R (2*m+3) 2 (2*m+2) 5
      (2*m+2) 9); try lia.
    - applys_eq HD0; lia.
    - applys_eq HDIAG; lia. }
  assert (HF1: P (2*m+4) 2 (2*m+1) 12).
  { applys_eq (k4_rov' R (2*m+4) 0 (2*m+3) 2
      (2*m+1) 8); try lia.
    - applys_eq HD1; lia.
    - applys_eq HD0; lia. }
  assert (HF2: P (2*m+5) 0 (2*m+2) 10).
  { applys_eq (k4_inc01 R (2*m+4) (2*m+2) 6); try lia.
    applys_eq HD1; lia. }
  assert (HOn: K4OddPhase P (2*m+3) 2).
  { intros a t Ha Hat.
    applys_eq (k4_rov' R a (2*(t-1)+1) (2*m+2) 5
      (2*m+1) 9); try lia.
    - applys_eq (H9 a (t-1)); lia.
    - applys_eq HDIAG; lia. }
  assert (HEn: K4EvenPhase P (2*m+3) 2).
  { intros [|[|[|[|k]]]] t Hkt; try lia.
    - assert (t=3) by lia; subst t.
      applys_eq (k4_rov R (2*m+3) 4 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF0; lia.
      applys_eq (HOn (2*m+2) 3); lia.
    - assert (t=2) by lia; subst t.
      applys_eq (k4_rov R (2*m+4) 2 (2*m+1) 9
        (2*m+1) 13); try lia.
      1: applys_eq HF1; lia.
      applys_eq (HOn (2*m+1) 4); lia.
    - assert (t=1) by lia; subst t.
      applys_eq (k4_rov R (2*m+5) 0 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF2; lia.
      applys_eq (HOn (2*m+2) 3); lia.
    - assert (t=0) by lia; subst t.
      applys_eq (k4_inc01 R (2*m+5) (2*m+1) 10); try lia.
      applys_eq HF2; lia. }
  split; [exact HOn|].
  split; [exact HEn|].
  repeat split.
  - applys_eq HF1; lia.
  - applys_eq HD0; lia.
  - applys_eq (HB (m+2) 0); lia.
  - applys_eq HF0; lia.
Qed.

Lemma k4_ready_next5 m:
  2 <= m -> K4Ready P m ->
  (forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+3) 5) ->
  K4Ready P (2*m+3).
Proof.
  intros Hm [HP _] HL.
  destruct (k4_phase_next_base5 m Hm HP HL) as [HO [HE Hpre]].
  split.
  - apply k4_phase_from_base; try lia; assumption.
  - exact Hpre.
Qed.

Variable P0: nat -> nat -> Prop.
Variable P0Ov': forall a b c d,
  P0 a (4+b) -> P a b (1+c) d -> P0 c (4+d).

Lemma k4_p0_sweep m q n:
  2 <= q -> q+n=m -> K4Phase P m ->
  P0 (m-q) (4*q+5) -> P0 0 (4*m+5).
Proof.
  intros Hq Hqn HP H0.
  induction n as [|n IH] in q, Hq, Hqn, H0 |- *.
  - applys_eq H0; lia.
  - apply IH with (q:=S q); try lia.
    applys_eq (P0Ov' (m-q) (4*q+1) (m-S q) (4*q+5)); try lia.
    + applys_eq H0; lia.
    + applys_eq (proj1 (HP q ltac:(lia)) (m-q) (2*q)); lia.
Qed.

Lemma k4_p0_sweep3 m q n:
  3 <= q -> q+n=m -> K4Phase3 P m ->
  P0 (m-q) (4*q+5) -> P0 0 (4*m+5).
Proof.
  intros Hq Hqn HP H0.
  induction n as [|n IH] in q, Hq, Hqn, H0 |- *.
  - applys_eq H0; lia.
  - apply IH with (q:=S q); try lia.
    applys_eq (P0Ov' (m-q) (4*q+1) (m-S q) (4*q+5)); try lia.
    + applys_eq H0; lia.
    + applys_eq (proj1 (HP q ltac:(lia)) (m-q) (2*q)); lia.
Qed.

End SimpleK4.

Section SpecialK4.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4SimpleRules P.

Lemma k4_bridge3_to7 m:
  3 <= m -> K4Phase3 P m ->
  (forall a t, a<m -> a+t=2*m ->
    P a (2*t+5) (2*m+3) 3) ->
  forall a t, a<m -> a+t=2*m ->
    P a (2*t+9) (2*m+3) 7.
Proof.
  intros Hm HP HL a t Ha Hat.
  destruct (HP m) as [HO HE]; try lia.
  assert (HZ := HO 0 (2*m) ltac:(lia) ltac:(lia)).
  assert (HB: forall k t, k+t=m+2 ->
    P (m+k) (2*t+1) (2*m+4) 1).
  { intros k [|u] Hkt.
    - applys_eq (k4_lov1 R (2*m+1) (2*m+3)); try lia.
      applys_eq (HE (m+1) 0); lia.
    - applys_eq (k4_lov2 R (m+k) (2*u) 0 (4*m+1)
        0 (4*m+1) (2*m+2)); try lia.
      1: applys_eq (HE k u); lia.
      all: applys_eq HZ; lia. }
  assert (HC: P (2*m+3) 0 (2*m+4) 2).
  { applys_eq (k4_inc1 R (2*m+2) (2*m+4) 1); try lia.
    applys_eq (HB (m+2) 0); lia. }
  assert (HD1: P (2*m+4) 0 (2*m+3) 6).
  { applys_eq (k4_inc01 R (2*m+3) (2*m+3) 2); try lia.
    applys_eq HC; lia. }
  assert (H1: P a (2*t+7) (2*m+4) 3).
  { applys_eq (k4_rov R a (2*t+5) (2*m+3) 0
      (2*m+4) 2); try lia.
    - applys_eq (HL a t); lia.
    - applys_eq HC; lia. }
  applys_eq (k4_rov R a (2*t+7) (2*m+4) 0
    (2*m+3) 6); try lia.
  - exact H1.
  - exact HD1.
Qed.

Lemma k4_ready3_next m:
  3 <= m -> K4Ready3 P m ->
  (forall a t, a<m -> a+t=2*m ->
    P a (2*t+9) (2*m+3) 7) ->
  K4Ready3 P (2*m+3).
Proof.
  intros Hm [HP _] HL.
  destruct (HP m) as [HO HE]; try lia.
  assert (HZ := HO 0 (2*m) ltac:(lia) ltac:(lia)).
  assert (HB: forall k t, k+t=m+2 ->
    P (m+k) (2*t+1) (2*m+4) 1).
  { intros k [|t] Hkt.
    - applys_eq (k4_lov1 R (2*m+1) (2*m+3)); try lia.
      applys_eq (HE (m+1) 0); lia.
    - applys_eq (k4_lov2 R (m+k) (2*t) 0 (4*m+1)
        0 (4*m+1) (2*m+2)); try lia.
      1: applys_eq (HE k t); lia.
      all: applys_eq HZ; lia. }
  assert (HC: P (2*m+3) 0 (2*m+4) 2).
  { applys_eq (k4_inc1 R (2*m+2) (2*m+4) 1); try lia.
    applys_eq (HB (m+2) 0); lia. }
  assert (HR: forall k t, k+t=m+2 ->
    P (m+k) (2*t+3) (2*m+3) 5).
  { intros k t Hkt.
    applys_eq (k4_inc00_1 R (m+k) (2*t+1) (2*m+3)); try lia.
    applys_eq (HB k t); lia. }
  assert (HD0: P (2*m+3) 2 (2*m+2) 8).
  { applys_eq (k4_inc00_2 R (2*m+3) 0 (2*m+2)); try lia.
    applys_eq HC; lia. }
  assert (HD1: P (2*m+4) 0 (2*m+3) 6).
  { applys_eq (k4_inc01 R (2*m+3) (2*m+3) 2); try lia.
    applys_eq HC; lia. }
  assert (HR9: forall k t, k+t=m+2 ->
    P (m+k) (2*t+5) (2*m+2) 9).
  { intros k t Hkt.
    applys_eq (k4_rov R (m+k) (2*t+3) (2*m+3) 2
      (2*m+2) 8); try lia.
    - applys_eq (HR k t); lia.
    - applys_eq HD0; lia. }
  assert (HDIAG: P (2*m+2) 5 (2*m+2) 9).
  { applys_eq (HR9 (m+2) 0); lia. }
  assert (HF0: P (2*m+3) 4 (2*m+2) 10).
  { applys_eq (k4_rov R (2*m+3) 2 (2*m+2) 5
      (2*m+2) 9); try lia.
    - applys_eq HD0; lia.
    - applys_eq HDIAG; lia. }
  assert (HF1: P (2*m+4) 2 (2*m+1) 12).
  { applys_eq (k4_rov' R (2*m+4) 0 (2*m+3) 2
      (2*m+1) 8); try lia.
    - applys_eq HD1; lia.
    - applys_eq HD0; lia. }
  assert (HF2: P (2*m+5) 0 (2*m+2) 10).
  { applys_eq (k4_inc01 R (2*m+4) (2*m+2) 6); try lia.
    applys_eq HD1; lia. }
  assert (HLeft: forall a t, a<m -> a+t=2*m ->
    P a (2*t+11) (2*m+2) 11).
  { intros a t Ha Hat.
    applys_eq (k4_rov R a (2*t+9) (2*m+3) 4
      (2*m+2) 10); try lia.
    - applys_eq (HL a t); lia.
    - applys_eq HF0; lia. }
  assert (HRight: forall k t, k+t=m+2 ->
    P (m+k) (2*t+7) (2*m+1) 13).
  { intros k t Hkt.
    applys_eq (k4_rov' R (m+k) (2*t+5) (2*m+2) 5
      (2*m+1) 9); try lia.
    - applys_eq (HR9 k t); lia.
    - applys_eq HDIAG; lia. }
  assert (HHigh: forall a t,
    m <= a -> a < 2*m+3 -> a+t=2*m+5 ->
    P a (2*t+1) (2*m+1) 13).
  { intros a t Ha0 Ha1 Hat.
    applys_eq (HRight (a-m) (t-3)); lia. }
  assert (HLow: forall a t, a<m -> a+t=2*m+5 ->
    P a (2*t+1) (2*m+2) 11).
  { intros a t Ha Hat.
    applys_eq (HLeft a (t-5)); lia. }
  assert (HOn: K4OddPhase P (2*m+3) 3).
  { intros a t Ha Hat.
    destruct (Compare_dec.le_lt_dec m a) as [Ham|Ham].
    - applys_eq (k4_rov' R a (2*t-1) (2*m+1) 9
        (2*m) 13); try lia.
      + applys_eq (HHigh a (t-1)); lia.
      + applys_eq (HHigh (2*m+1) 4); lia.
    - applys_eq (k4_rov' R a (2*t-1) (2*m+2) 7
        (2*m) 13); try lia.
      + applys_eq (HLow a (t-1)); lia.
      + applys_eq (HHigh (2*m+2) 3); lia. }
  assert (HEn2: K4EvenPhase P (2*m+3) 2).
  { intros [|[|[|[|k]]]] t Hkt; try lia.
    - assert (t=3) by lia; subst t.
      applys_eq (k4_rov R (2*m+3) 4 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF0; lia.
      applys_eq (HHigh (2*m+2) 3); lia.
    - assert (t=2) by lia; subst t.
      applys_eq (k4_rov R (2*m+4) 2 (2*m+1) 9
        (2*m+1) 13); try lia.
      1: applys_eq HF1; lia.
      applys_eq (HHigh (2*m+1) 4); lia.
    - assert (t=1) by lia; subst t.
      applys_eq (k4_rov R (2*m+5) 0 (2*m+2) 7
        (2*m+1) 13); try lia.
      1: applys_eq HF2; lia.
      applys_eq (HHigh (2*m+2) 3); lia.
    - assert (t=0) by lia; subst t.
      applys_eq (k4_inc01 R (2*m+5) (2*m+1) 10); try lia.
      applys_eq HF2; lia. }
  assert (HEn: K4EvenPhase P (2*m+3) 3).
  { apply (k4_even_phase_S P R (2*m+3) 2); try lia; assumption. }
  split.
  - apply k4_phase3_from_base; try lia; assumption.
  - split.
    + applys_eq HF0; lia.
    + applys_eq (HHigh (2*m+2) 3); lia.
Qed.

End SpecialK4.

Section DirectK4.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable D: K4DirectRules P.

Lemma k4_direct_base_facts: K4DirectBaseFacts P.
Proof.
  pose (R := k4d_simple D).
  assert (H0: P 0 1 0 5) by exact (k4d_rst0 D).
  assert (H1: P 0 7 5 1) by (eapply (k4d_lov3 D); exact H0).
  assert (H2: P 0 9 4 5) by (eapply (k4_inc00_1 R); exact H1).
  assert (H3: P 1 0 0 6) by (eapply (k4_inc1 R); exact H0).
  assert (H4: P 2 1 4 1) by (eapply (k4_lov1 R); exact H3).
  assert (H5: P 3 0 4 2) by (eapply (k4_inc1 R); exact H4).
  assert (H6: P 4 0 3 6) by (eapply (k4_inc01 R); exact H5).
  assert (H7: P 3 2 2 8) by (eapply (k4_inc00_2 R); exact H5).
  assert (H8: P 4 2 1 12) by (eapply (k4_rov' R); [exact H6|exact H7]).
  assert (H9: P 0 11 1 13) by (eapply (k4_rov R); [exact H2|exact H8]).
  assert (H10: P 1 3 4 1) by (eapply (k4_lov2 R); exact H3 || exact H0).
  assert (H11: P 1 5 3 5) by (eapply (k4_inc00_1 R); exact H10).
  assert (H12: P 1 7 2 9) by (eapply (k4_rov R); [exact H11|exact H7]).
  assert (H13: P 2 3 3 5) by (eapply (k4_inc00_1 R); exact H4).
  assert (H14: P 2 5 2 9) by (eapply (k4_rov R); [exact H13|exact H7]).
  assert (H15: P 1 9 1 13) by (eapply (k4_rov' R); [exact H12|exact H14]).
  assert (H16: P 2 7 1 13) by (eapply (k4_rov' R); exact H14).
  assert (H17: P 3 4 2 10) by (eapply (k4_rov R); [exact H7|exact H14]).
  assert (H18: P 3 6 1 14) by (eapply (k4_rov R); [exact H17|exact H16]).
  assert (H19: P 4 4 1 14) by (eapply (k4_rov R); [exact H8|exact H15]).
  assert (H20: P 5 0 2 10) by (eapply (k4_inc01 R); exact H6).
  assert (H21: P 5 2 1 14) by (eapply (k4_rov R); [exact H20|exact H16]).
  assert (H22: P 6 0 1 14) by (eapply (k4_inc01 R); exact H20).
  assert (H23: P 0 13 0 17) by (eapply (k4_rov' R); [exact H9|exact H15]).
  unfold K4DirectBaseFacts; repeat split; assumption.
Qed.

Lemma k4_direct_ready3: K4Ready P 3.
Proof.
  pose proof k4_direct_base_facts as
    [H0 [H1 [H2 [H3 [H4 [H5 [H6 [H7 [H8 [H9 [H10 [_ _]]]]]]]]]]]].
  split.
  - apply (k4_phase_from_base P (k4d_simple D)); try lia.
    + intros a t Ha Hat.
      assert (a=0 \/ a=1 \/ a=2) as Ha' by lia.
      destruct Ha' as [Ha'|[Ha'|Ha']]; subst a.
      * replace t with 5 by lia. exact H0.
      * replace t with 4 by lia. exact H1.
      * replace t with 3 by lia. exact H2.
    + intros k t Hkt.
      assert (k=0 \/ k=1 \/ k=2 \/ k=3) as Hk by lia.
      destruct Hk as [Hk|[Hk|[Hk|Hk]]]; subst k.
      * replace t with 3 by lia. exact H3.
      * replace t with 2 by lia. exact H4.
      * replace t with 1 by lia. exact H5.
      * replace t with 0 by lia. exact H6.
  - unfold K4Prelude; repeat split; assumption.
Qed.

Lemma k4_direct_left_bridge m:
  2 <= m -> K4Phase P m ->
  forall a t, a<m -> a+t=2*m -> P a (2*t+7) (2*m+5) 1.
Proof.
  intros Hm HP a t Ha Hat.
  destruct (HP m) as [HO _]; try lia.
  applys_eq (k4d_lov3 D a (2*t+1) (4*m+1) (2*m+1)); try lia.
  - applys_eq (HO a t); lia.
  - applys_eq (HO 0 (2*m)); lia.
Qed.

Lemma k4_direct_ready_next m:
  2 <= m -> K4Ready P m -> K4Ready P (2*m+3).
Proof.
  intros Hm HR.
  apply (k4_ready_next P (k4d_simple D) m Hm HR).
  apply k4_direct_left_bridge; [exact Hm|exact (proj1 HR)].
Qed.

End DirectK4.

(* A row of the P table at fixed input weight [w].  The Boolean word only
   selects the coordinates for which facts are retained; no absence claim is
   made about the other coordinates.  Keeping [d] existential avoids Nat.sub
   in all subsequent arithmetic. *)
Definition K4ExactRow (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (v: bool) (w c d: nat) : Prop :=
  2*c+d=w+4 /\
  forall a b, a < length B -> nth a B false = v ->
    2*a+b=w -> P a b c d.

Definition K4Row (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (v: bool) (w c: nat) : Prop :=
  exists d, K4ExactRow P B v w c d.

Definition K4RowExcept (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (v: bool) (skip w c: nat) : Prop :=
  exists d,
    2*c+d=w+4 /\
    forall a b, a < length B -> a <> skip -> nth a B false = v ->
      2*a+b=w -> P a b c d.

(* The two alternating regular K4 frontiers.  Here H=2*S+D; using D as an
   explicit parameter keeps all exceptional outputs in linear Nat
   arithmetic.  These are inclusions of P facts, never assertions that other
   P instances are absent. *)
Definition K4Type4Front (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (H S D: nat) : Prop :=
  H=2*S+D /\
  K4Row P B true (2*H+9) (H+1) /\
  K4Row P B false (2*H+10) H /\
  P (H+1) 8 (H+1) 12 /\
  P (H+2) 6 (H-1) 16 /\
  P (H+3) 4 H 14 /\
  P (H+4) 2 (H+1) 12 /\
  P (H+5) 0 (D-2) (4*S+18).

Definition K4Type2Front (P: nat -> nat -> nat -> nat -> Prop)
    (B: list bool) (H S D: nat) : Prop :=
  H=2*S+D /\
  K4Row P B false (2*H+6) (H+1) /\
  P (H+1) 4 (H+1) 8 /\
  P (H+2) 2 (H+2) 6 /\
  P (H+3) 0 D (4*S+10) /\
  K4RowExcept P B true (H-1) (2*H+7) (H+2) /\
  P (H-1) 9 D (4*S+11).

Definition k4_next_x (B: list bool) (x y: nat) : nat :=
  if nth x B false then x-1 else y.

Definition k4_next_y (B: list bool) (x y: nat) : nat :=
  if nth y B false then k4_next_x B x y else y-1.

Section K4Rows.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4CoreRules P.

Lemma k4_exact_row_rov B v w c e c' d':
  2*length B <= w+2 ->
  K4ExactRow P B v w c (3+e) ->
  P c e c' d' ->
  2*c'+d'=2*c+e+4 ->
  K4ExactRow P B v (w+2) c' (1+d').
Proof.
  intros Hlen [Hw HR] HP Hwidth; split; try lia.
  intros a b Hal Hab Haw.
  assert (2 <= b) by lia.
  applys_eq (k4core_rov R a (b-2) c e c' d'); try lia.
  - applys_eq (HR a (b-2)); try assumption; lia.
  - exact HP.
Qed.

Lemma k4_exact_row_rov' B v w c e c' d':
  2*length B <= w+2 ->
  K4ExactRow P B v w c (4+e) ->
  P c e (1+c') d' ->
  2*(1+c')+d'=2*c+e+4 ->
  K4ExactRow P B v (w+2) c' (4+d').
Proof.
  intros Hlen [Hw HR] HP Hwidth; split; try lia.
  intros a b Hal Hab Haw.
  assert (2 <= b) by lia.
  applys_eq (k4core_rov' R a (b-2) c e c' d'); try lia.
  - applys_eq (HR a (b-2)); try assumption; lia.
  - exact HP.
Qed.

Lemma k4_rows_step B u x y:
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  x < length B -> y < length B ->
  (nth x B false = true -> 0 < x) ->
  (nth y B false = false -> 0 < y) ->
  2*x <= u -> 2*y <= u+1 ->
  2*length B <= u+2 ->
  K4Row P B true (u+2) (k4_next_x B x y) /\
  K4Row P B false (u+3) (k4_next_y B x y).
Proof.
  intros [dx [Hdx HT]] [dy [Hdy HF]] Hxl Hyl HX HY Hxu Hyu Hlen.
  unfold k4_next_x, k4_next_y.
  destruct (nth x B false) eqn:Hbx,
           (nth y B false) eqn:Hby.
  all: unfold k4_next_x; try rewrite Hbx; cbn.
  - assert (Hx: 0 < x) by (apply HX; reflexivity).
    assert (Hdx4: 4 <= dx) by lia.
    assert (Hdy3: 3 <= dy) by lia.
    assert (Hxm: 1+(x-1)=x) by lia.
    assert (HT': K4Row P B true (u+2) (x-1)).
    { exists (4+dx); split; try lia.
      intros a b Hal Hab Haw.
      assert (2 <= b) by (assert (a < length B) by exact Hal; lia).
      applys_eq (k4core_rov' R a (b-2) x (dx-4) (x-1) dx); try lia.
      + applys_eq (HT a (b-2)); try assumption; lia.
      + applys_eq (HT x (dx-4)); try assumption; lia. }
    split; [exact HT'|].
    destruct HT' as [dz [Hdz HTz]].
    exists (1+dz); split; try lia.
    intros a b Hal Hab Haw.
    assert (2 <= b) by lia.
    applys_eq (k4core_rov R a (b-2) y (dy-3) (x-1) dz); try lia.
    + applys_eq (HF a (b-2)); try assumption; lia.
    + applys_eq (HTz y (dy-3)); try assumption; lia.
  - assert (Hx: 0 < x) by (apply HX; reflexivity).
    assert (Hy: 0 < y) by (apply HY; reflexivity).
    assert (Hdx4: 4 <= dx) by lia.
    assert (Hdy4: 4 <= dy) by lia.
    assert (Hxm: 1+(x-1)=x) by lia.
    assert (Hym: 1+(y-1)=y) by lia.
    assert (HT': K4Row P B true (u+2) (x-1)).
    { exists (4+dx); split; try lia.
      intros a b Hal Hab Haw.
      assert (2 <= b) by lia.
      applys_eq (k4core_rov' R a (b-2) x (dx-4) (x-1) dx); try lia.
      + applys_eq (HT a (b-2)); try assumption; lia.
      + applys_eq (HT x (dx-4)); try assumption; lia. }
    split; [exact HT'|].
    exists (4+dy); split; try lia.
    intros a b Hal Hab Haw.
    assert (2 <= b) by lia.
    applys_eq (k4core_rov' R a (b-2) y (dy-4) (y-1) dy); try lia.
    + applys_eq (HF a (b-2)); try assumption; lia.
    + applys_eq (HF y (dy-4)); try assumption; lia.
  - assert (Hdx3: 3 <= dx) by lia.
    assert (Hdy3: 3 <= dy) by lia.
    assert (HT': K4Row P B true (u+2) y).
    { exists (1+dy); split; try lia.
      intros a b Hal Hab Haw.
      assert (2 <= b) by lia.
      applys_eq (k4core_rov R a (b-2) x (dx-3) y dy); try lia.
      + applys_eq (HT a (b-2)); try assumption; lia.
      + applys_eq (HF x (dx-3)); try assumption; lia. }
    split; [exact HT'|].
    destruct HT' as [dz [Hdz HTz]].
    exists (1+dz); split; try lia.
    intros a b Hal Hab Haw.
    assert (2 <= b) by lia.
    applys_eq (k4core_rov R a (b-2) y (dy-3) y dz); try lia.
    + applys_eq (HF a (b-2)); try assumption; lia.
    + applys_eq (HTz y (dy-3)); try assumption; lia.
  - assert (Hy: 0 < y) by (apply HY; reflexivity).
    assert (Hdx3: 3 <= dx) by lia.
    assert (Hdy4: 4 <= dy) by lia.
    assert (Hym: 1+(y-1)=y) by lia.
    assert (HT': K4Row P B true (u+2) y).
    { exists (1+dy); split; try lia.
      intros a b Hal Hab Haw.
      assert (2 <= b) by lia.
      applys_eq (k4core_rov R a (b-2) x (dx-3) y dy); try lia.
      + applys_eq (HT a (b-2)); try assumption; lia.
      + applys_eq (HF x (dx-3)); try assumption; lia. }
    split; [exact HT'|].
    exists (4+dy); split; try lia.
    intros a b Hal Hab Haw.
    assert (2 <= b) by lia.
    applys_eq (k4core_rov' R a (b-2) y (dy-4) (y-1) dy); try lia.
    + applys_eq (HF a (b-2)); try assumption; lia.
    + applys_eq (HF y (dy-4)); try assumption; lia.
Qed.

(* A half-open interval of columns carrying one affine row.  This is used for
   the right suffix which is being created while the two old-word rows scan
   left.  It deliberately says nothing about columns outside [lo,hi). *)
Definition K4Range (P: nat -> nat -> nat -> nat -> Prop)
    (lo hi w c: nat) : Prop :=
  exists d,
    2*c+d=w+4 /\
    forall a b, lo <= a -> a < hi -> 2*a+b=w -> P a b c d.

(* One growing-suffix step.  The old exceptional endpoint is absorbed into
   the false row, while [PInc01] creates the next endpoint.  [Halign] is the
   exact Boolean/pointer compatibility needed for that absorption; keeping it
   explicit prevents us from silently assuming a relation which holds only
   on the concrete trajectory. *)
Lemma k4_growing_range_step B u x y lo e z de:
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4Range P lo e (u+1) y ->
  P e 0 (S z) de ->
  2*e=u+1 -> 2*(S z)+de=u+5 ->
  S z < length B ->
  x < length B -> y < length B -> 0 < y ->
  (nth x B false = true -> 0 < x) ->
  (nth y B false = false -> 0 < y) ->
  2*x <= u -> 2*y <= u+1 -> 2*length B <= u+2 ->
  k4_next_y B x y =
    (if nth (S z) B false then k4_next_x B x y else y-1) ->
  K4Row P B true (u+2) (k4_next_x B x y) /\
  K4Row P B false (u+3) (k4_next_y B x y) /\
  K4Range P lo (S e) (u+3) (k4_next_y B x y) /\
  P (S e) 0 z (de+4).
Proof.
  intros RT RF [dr [Hdr RR]] HE Hew Heout Hzl Hxl Hyl Hypos Hx0 Hy0
    Hxu Hyu Hlen Halign.
  destruct RT as [dt [Hdt RT]].
  destruct RF as [df [Hdf RF]].
  assert (Hdrf: dr=df) by lia; subst dr.
  destruct (k4_rows_step B u x y
    (ex_intro _ dt (conj Hdt RT)) (ex_intro _ df (conj Hdf RF))
    Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen) as [RT' RF'].
  destruct RT' as [dt' [Hdt' RT']].
  destruct RF' as [df' [Hdf' RF']].
  repeat split.
  - exists dt'. split; assumption.
  - exists df'. split; assumption.
  - exists df'. split; [exact Hdf'|].
    intros a b Hlo Hhi Haw.
    assert (Hb2: 2 <= b) by lia.
    destruct (Nat.eq_dec a e) as [->|Hae].
    + destruct (nth (S z) B false) eqn:Hz.
      * assert (Hde3: 3 <= de) by lia.
        cbn in Halign.
        applys_eq (k4core_rov R e 0 (S z) (de-3)
          (k4_next_x B x y) dt'); try lia.
        -- applys_eq HE; lia.
        -- applys_eq (RT' (S z) (de-3)); try assumption; lia.
      * assert (Hde4: 4 <= de) by lia.
        cbn in Halign.
        applys_eq (k4core_rov' R e 0 (S z) (de-4) (y-1) df);
          try lia.
        -- applys_eq HE; lia.
        -- applys_eq (RF (S z) (de-4)); try assumption; lia.
    + destruct (nth y B false) eqn:Hy.
      * assert (Hdf3: 3 <= df) by lia.
        assert (Hnext: k4_next_y B x y=k4_next_x B x y).
        { unfold k4_next_y. rewrite Hy. reflexivity. }
        applys_eq (k4core_rov R a (b-2) y (df-3)
          (k4_next_x B x y) dt'); try lia.
        -- replace (3+(df-3)) with df by lia.
           apply RR; try assumption; lia.
        -- applys_eq (RT' y (df-3)); try assumption; lia.
      * assert (Hdf4: 4 <= df) by lia.
        assert (Hnext: k4_next_y B x y=y-1).
        { unfold k4_next_y. rewrite Hy. reflexivity. }
        applys_eq (k4core_rov' R a (b-2) y (df-4) (y-1) df);
          try lia.
        -- replace (4+(df-4)) with df by lia.
           apply RR; try assumption; lia.
        -- applys_eq (RF y (df-4)); try assumption; lia.
  - applys_eq (k4core_inc01 R e z de); try lia.
    exact HE.
Qed.

Inductive K4GrowingTrace (B: list bool):
    nat -> nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| K4GrowingDone u x y:
    K4GrowingTrace B u x y 0 0 x y
| K4GrowingMore u x y z n xf yf:
    S z < length B -> x < length B -> y < length B -> 0 < y ->
    (nth x B false = true -> 0 < x) ->
    (nth y B false = false -> 0 < y) ->
    2*x <= u -> 2*y <= u+1 -> 2*length B <= u+2 ->
    k4_next_y B x y =
      (if nth (S z) B false then k4_next_x B x y else y-1) ->
    K4GrowingTrace B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) z n xf yf ->
    K4GrowingTrace B u x y (S z) (S n) xf yf.

Lemma k4_growing_trace_rows B u x y q n xf yf lo e de:
  K4GrowingTrace B u x y q n xf yf ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4Range P lo e (u+1) y ->
  P e 0 q de ->
  2*e=u+1 -> 2*q+de=u+5 ->
  K4Row P B true (u+2*n) xf /\
  K4Row P B false (u+2*n+1) yf /\
  K4Range P lo (e+n) (u+2*n+1) yf /\
  P (e+n) 0 0 (de+4*n).
Proof.
  intros HT.
  revert lo e de.
  induction HT; intros lo e de RT RF RR HE Hew Heout.
  - cbn. split; [applys_eq RT; lia|].
    split; [applys_eq RF; lia|].
    split; [applys_eq RR; lia|applys_eq HE; lia].
  - destruct (k4_growing_range_step B u x y lo e z de RT RF RR HE
      Hew Heout H H0 H1 H2 H3 H4 H5 H6 H7 H8) as
      [RT' [RF' [RR' HE']]].
    assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF'; lia).
    assert (RR'': K4Range P lo (S e) (u+2+1)
        (k4_next_y B x y)) by (applys_eq RR'; lia).
    destruct (IHHT lo (S e) (de+4) RT' RF'' RR'' HE') as
      [RTf [RFf [RRf HEf]]]; try lia.
    split; [applys_eq RTf; lia|].
    split; [applys_eq RFf; lia|].
    split; [applys_eq RRf; lia|applys_eq HEf; lia].
Qed.

Definition k4_follow (B: list bool) (x y z: nat) : nat :=
  if nth z B false then k4_next_x B x y else y-1.

(* Four reachable relative positions of a follower after its first step. *)
Definition K4FollowerOK (B: list bool) (x y z: nat) : Prop :=
  (x=y /\ z=x) \/
  (x=S y /\ z=y /\ (0<y \/ nth y B false=true)) \/
  (x=S y /\ z=x /\ 0<y /\ nth x B false=false) \/
  (x=y /\ S z=x /\ nth x B false=true).

Lemma k4_follower_step_eq_or B x y z:
  K4FollowerOK B x y z ->
  k4_follow B x y z = k4_next_y B x y \/
  (x=S y /\ z=x /\ nth x B false=false /\ nth y B false=true).
Proof.
  unfold K4FollowerOK.
  intros [[Hxy Hzx] |
    [[Hxy [Hzy Hy]] | [[Hxy [Hzx [Hy Hx]]] | [Hxy [Hzx Hx]]]]].
  - left. subst. unfold k4_follow, k4_next_y. reflexivity.
  - left. subst. unfold k4_follow, k4_next_y. reflexivity.
  - subst x z. unfold k4_follow, k4_next_y, k4_next_x.
    rewrite Hx. cbn. destruct (nth y B false) eqn:E; [right|left];
      repeat split; try assumption; lia.
  - left. subst x. unfold k4_follow, k4_next_y, k4_next_x.
    rewrite Hx. cbn. destruct (nth z B false); lia.
Qed.

(* The four follower states synchronize after at most two ordinary rows.
   This is the finite-state fact which lets a freshly emitted right column
   join an older column without exposing the intervening RLE boundaries. *)
Lemma k4_follower_two B x y z:
  K4FollowerOK B x y z ->
  k4_follow B (k4_next_x B x y) (k4_next_y B x y)
    (k4_follow B x y z) =
  k4_next_y B (k4_next_x B x y) (k4_next_y B x y).
Proof.
  intros HOK.
  destruct (k4_follower_step_eq_or B x y z HOK) as [E|E].
  - rewrite E. unfold k4_follow, k4_next_y. reflexivity.
  - destruct E as [Hxy [Hzx [Hx Hy]]]. subst x z.
    unfold k4_follow, k4_next_y, k4_next_x.
    rewrite Hx, Hy. cbn.
    destruct (nth (y-1) B false); rewrite Hy; reflexivity.
Qed.

Lemma k4_follower_behind_step B x y q:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> q+2<=y ->
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y)
    (k4_follow B x y q).
Proof.
  intros HB Hxy Hq.
  assert (Heq: x=y \/ x=S y) by lia.
  destruct Heq as [Heq|Heq]; subst x.
  - unfold K4FollowerOK, k4_follow, k4_next_y, k4_next_x.
    destruct (nth y B false) eqn:EY,
             (nth q B false) eqn:EQ; cbn.
    + left; lia.
    + left; lia.
    + right; right; left. repeat split; try lia; assumption.
    + right; left. repeat split; try lia.
  - assert (Hnx: k4_next_x B (S y) y=y).
    { unfold k4_next_x. destruct (nth (S y) B false); lia. }
    unfold K4FollowerOK, k4_follow, k4_next_y.
    rewrite Hnx.
    destruct (nth y B false) eqn:EY,
             (nth q B false) eqn:EQ; cbn.
    + left; lia.
    + right; right; right. repeat split; try lia; assumption.
    + right; right; left. repeat split; try lia; assumption.
    + right; left. repeat split; try lia.
Qed.

Lemma k4_synced_decrement_ok B x y:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> 0<y ->
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y) (y-1).
Proof.
  intros HB Hxy Hy.
  assert (x=y \/ x=S y) as E by lia. destruct E as [E|E]; subst x.
  - unfold K4FollowerOK, k4_next_x, k4_next_y.
    destruct (nth y B false) eqn:E; cbn.
    + unfold k4_next_x. rewrite E. cbn. left. split; reflexivity.
    + unfold k4_next_x. rewrite E. cbn. right; left. repeat split; try lia.
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
  - assert (E: k4_next_x B (S y) y=y).
    { unfold k4_next_x. destruct (nth (S y) B false); lia. }
    unfold K4FollowerOK, k4_next_y. rewrite E.
    destruct (nth y B false) eqn:Ey; cbn.
    + right; right; right. repeat split; try lia; assumption.
    + right; left. repeat split; try lia.
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
Qed.

Lemma k4_follower_ok_step B x y z:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  (x<>0 \/ y<>0) ->
  K4FollowerOK B x y z ->
  (nth z B false=false -> 0<y) /\
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y)
    (k4_follow B x y z).
Proof.
  intros HB Hnz HOK. unfold K4FollowerOK in HOK |- *.
  destruct HOK as [[Hxy Hzx] |
    [[Hxy [Hzy Hy]] | [[Hxy [Hzx [Hy Hx]]] | [Hxy [Hzx Hx]]]]].
  - subst x z.
    destruct (nth y B false) eqn:E.
    all: unfold k4_follow, k4_next_y, k4_next_x; rewrite E; cbn.
    + split; [congruence|left; split; reflexivity].
    + assert (0<y) by lia.
      split; [lia|right; left; repeat split; try lia].
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
  - subst x z.
    destruct (nth (S y) B false) eqn:EX,
             (nth y B false) eqn:EY.
    all: unfold k4_follow, k4_next_y, k4_next_x;
      rewrite EX, EY; cbn.
    + split; [congruence|left; lia].
    + assert (Hyp: 0<y) by (destruct Hy; lia || congruence).
      split; [lia|].
      right; left. repeat split; try lia.
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
    + split; [congruence|left; lia].
    + assert (Hyp: 0<y) by (destruct Hy; lia || congruence).
      split; [lia|].
      right; left. repeat split; try lia.
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
  - subst x z.
    destruct (nth y B false) eqn:EY.
    all: unfold k4_follow, k4_next_y, k4_next_x;
      rewrite Hx, EY; cbn.
    + split; [lia|]. right; right; right. repeat split; try lia.
    + split; [lia|]. right; left. repeat split; try lia.
      destruct y; [lia|]. destruct y.
      * destruct HB; [right; assumption|congruence].
      * left; lia.
  - subst x.
    destruct (nth z B false) eqn:EZ.
    all: unfold k4_follow, k4_next_y, k4_next_x;
      rewrite Hx, EZ; cbn.
    + split; [congruence|left; lia].
    + split; [lia|left; split; reflexivity].
Qed.

Inductive K4FollowTrace (B: list bool):
    nat -> nat -> nat -> nat -> nat -> Prop :=
| K4FollowDone u:
    K4FollowTrace B u 0 0 0 0
| K4FollowMore u x y z n:
    z < length B ->
    (nth z B false=false -> 0<y) ->
    x < length B -> y < length B ->
    (nth x B false=true -> 0<x) ->
    (nth y B false=false -> 0<y) ->
    2*x<=u -> 2*y<=u+1 -> 2*length B<=u+2 ->
    K4FollowTrace B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_follow B x y z) n ->
    K4FollowTrace B u x y z (S n).

Definition K4Particle (P: nat -> nat -> nat -> nat -> Prop)
    (u a z: nat) : Prop :=
  exists b d, 2*a+b=u+1 /\ 2*z+d=u+5 /\ P a b z d.

Lemma k4_particle_step B u x y z a:
  K4Row P B true (u+2) (k4_next_x B x y) ->
  K4Row P B false (u+1) y ->
  z < length B ->
  (nth z B false=false -> 0<y) ->
  2*length B<=u+2 ->
  K4Particle P u a z ->
  K4Particle P (u+2) a (k4_follow B x y z).
Proof.
  intros [dt [Hdt RT]] [df [Hdf RF]] Hzl Hz0 Hlen
    [b [d [Hab [Hzd HP]]]].
  assert (Hd5: 5<=d) by lia.
  destruct (nth z B false) eqn:Hz.
  - exists (b+2), (1+dt). split; [lia|]. split.
    + unfold k4_follow. rewrite Hz. cbn. lia.
    + unfold k4_follow. rewrite Hz. cbn.
    applys_eq (k4core_rov R a b z (d-3) (k4_next_x B x y) dt);
      try lia.
      * applys_eq HP; lia.
      * applys_eq (RT z (d-3)); try assumption; lia.
  - assert (Hy: 0<y) by (apply Hz0; reflexivity).
    exists (b+2), (4+df). split; [lia|]. split.
    + unfold k4_follow. rewrite Hz. cbn. lia.
    + unfold k4_follow. rewrite Hz. cbn.
      applys_eq (k4core_rov' R a b z (d-4) (y-1) df); try lia.
      * applys_eq HP; lia.
      * applys_eq (RF z (d-4)); try assumption; lia.
Qed.

Lemma k4_follow_trace_particle B u x y z n:
  K4FollowTrace B u x y z n ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  forall a, K4Particle P u a z -> K4Particle P (u+2*n) a 0.
Proof.
  intros HT.
  induction HT; intros RT RF a HP.
  - cbn. applys_eq HP; lia.
  - destruct (k4_rows_step B u x y RT RF H1 H2 H3 H4 H5 H6 H7)
      as [RT' RF'].
    assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF'; lia).
    applys_eq (IHHT RT' RF'' a); try lia.
    eapply k4_particle_step; eauto.
Qed.

Lemma k4_type4_prefix_start B H S D:
  2 <= H -> length B=H+1 ->
  nth H B false = true -> nth (H-1) B false = true ->
  K4Type4Front P B H S D ->
  K4Row P B true (2*H+17) (H-2) /\
  K4Row P B false (2*H+18) (H-2).
Proof.
  intros HH Hlen Hlast Hpen
    [_ [RT [RF [E1 [_ [_ [_ _]]]]]]].
  destruct RT as [dt [Hdt RT]].
  destruct RF as [df [Hdf RF]].
  assert (dt=11) by lia; subst dt.
  assert (df=14) by lia; subst df.
  assert (TH: P H 9 (H+1) 11) by
    (apply RT; try lia; assumption).
  assert (TH1: P (H-1) 11 (H+1) 11) by
    (apply RT; try lia; assumption).
  assert (E2: P (H+1) 10 H 16).
  { applys_eq (k4core_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq E1; lia. }
  assert (RT1: K4ExactRow P B true (2*H+11) (H+1) 13).
  { applys_eq (k4_exact_row_rov B true (2*H+9) (H+1) 8 (H+1) 12);
      try lia; try exact E1.
    split; assumption. }
  assert (T1H: P H 11 (H+1) 13) by
    (apply (proj2 RT1); try lia; assumption).
  assert (RF1: K4ExactRow P B false (2*H+12) (H+1) 14).
  { applys_eq (k4_exact_row_rov B false (2*H+10) H 11 (H+1) 13);
      try lia; try exact T1H.
    split; assumption. }
  assert (RT2: K4ExactRow P B true (2*H+13) H 17).
  { applys_eq (k4_exact_row_rov B true (2*H+11) (H+1) 10 H 16);
      try lia; assumption. }
  assert (RF2: K4ExactRow P B false (2*H+14) (H-1) 20).
  { applys_eq (k4_exact_row_rov' B false (2*H+12) (H+1) 10 (H-1) 16);
      try lia.
    - exact RF1.
    - applys_eq E2; lia. }
  assert (T2H: P H 13 H 17) by
    (apply (proj2 RT2); try lia; assumption).
  assert (RT3: K4ExactRow P B true (2*H+15) (H-1) 21).
  { applys_eq (k4_exact_row_rov' B true (2*H+13) H 13 (H-1) 17);
      try lia.
    - exact RT2.
    - applys_eq T2H; lia. }
  assert (T3H1: P (H-1) 17 (H-1) 21) by
    (apply (proj2 RT3); try lia; assumption).
  assert (RF3: K4ExactRow P B false (2*H+16) (H-1) 22).
  { applys_eq (k4_exact_row_rov B false (2*H+14) (H-1) 17 (H-1) 21);
      try lia; assumption. }
  assert (RF3': K4Row P B false (2*H+15+1) (H-1)).
  { exists 22. applys_eq RF3; lia. }
  destruct (k4_rows_step B (2*H+15) (H-1) (H-1)
    (ex_intro _ 21 RT3) RF3') as [RN1 RN0]; try lia.
  unfold k4_next_x, k4_next_y in RN1, RN0.
  rewrite Hpen in RN1, RN0. cbn in RN1, RN0.
  unfold k4_next_x in RN0. rewrite Hpen in RN0. cbn in RN0.
  split.
  - replace (2*H+17) with (2*H+15+2) by lia.
    replace (H-2) with (H-1-1) by lia. exact RN1.
  - replace (2*H+18) with (2*H+15+3) by lia.
    replace (H-2) with (H-1-1) by lia. exact RN0.
Qed.

Lemma k4_type2_prefix_start B H S D:
  2 <= H -> length B=H+1 ->
  nth H B false = true ->
  D < length B -> D <> H-1 -> nth D B false = true ->
  K4Type2Front P B H S D ->
  K4Row P B true (2*H+13) H /\
  K4Row P B false (2*H+14) H.
Proof.
  intros HH Hlen Hlast HDl HDn HDbit
    [Hhs [RF0 [E1 [E2 [E3 [RT0 Dent]]]]]].
  destruct RF0 as [df [Hdf RF0]].
  destruct RT0 as [dt [Hdt RT0]].
  assert (df=8) by lia; subst df.
  assert (dt=7) by lia; subst dt.
  assert (A: P (H+2) 4 (H+1) 10).
  { applys_eq (k4core_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia;
      applys_eq E2; lia. }
  assert (TD: P D (4*S+7) (H+2) 7).
  { apply RT0; try assumption; lia. }
  assert (Dent': P (H-1) 11 (H+1) 11).
  { applys_eq (k4core_rov' R (H-1) 9 D (4*S+7) (H+1) 7); try lia.
    - applys_eq Dent; lia.
    - applys_eq TD; lia. }
  assert (RT1: K4ExactRow P B true (2*H+9) (H+1) 11).
  { split; try lia.
    intros a b Hal Hab Haw.
    destruct (Nat.eq_dec a (H-1)) as [->|Han].
    - applys_eq Dent'; lia.
    - assert (2 <= b) by lia.
      applys_eq (k4core_rov R a (b-2) (H+2) 4 (H+1) 10); try lia.
      + applys_eq (RT0 a (b-2)); try assumption; lia.
      + exact A. }
  assert (TH: P H 9 (H+1) 11) by
    (apply (proj2 RT1); try lia; assumption).
  assert (B1: P (H+1) 6 H 12).
  { applys_eq (k4core_rov' R (H+1) 4 (H+1) 4 H 8); try lia;
      applys_eq E1; lia. }
  assert (B2: P (H+1) 8 (H+1) 12).
  { applys_eq (k4core_rov R (H+1) 6 H 9 (H+1) 11); try lia.
    - exact B1.
    - exact TH. }
  assert (RT2: K4ExactRow P B true (2*H+11) (H+1) 13).
  { applys_eq (k4_exact_row_rov B true (2*H+9) (H+1) 8 (H+1) 12);
      try lia; assumption. }
  assert (RF1: K4ExactRow P B false (2*H+8) H 12).
  { applys_eq (k4_exact_row_rov' B false (2*H+6) (H+1) 4 H 8);
      try lia.
    - split; assumption.
    - applys_eq E1; lia. }
  assert (RF2: K4ExactRow P B false (2*H+10) (H+1) 12).
  { applys_eq (k4_exact_row_rov B false (2*H+8) H 9 (H+1) 11);
      try lia; assumption. }
  assert (RF3: K4ExactRow P B false (2*H+12) H 16).
  { applys_eq (k4_exact_row_rov' B false (2*H+10) (H+1) 8 H 12);
      try lia.
    - exact RF2.
    - applys_eq B2; lia. }
  assert (B3: P (H+1) 10 H 16).
  { applys_eq (k4core_rov' R (H+1) 8 (H+1) 8 H 12); try lia;
      applys_eq B2; lia. }
  assert (TH2: P H 11 (H+1) 13) by
    (apply (proj2 RT2); try lia; assumption).
  assert (RT3: K4ExactRow P B true (2*H+13) H 17).
  { applys_eq (k4_exact_row_rov B true (2*H+11) (H+1) 10 H 16);
      try lia; assumption. }
  assert (TH3: P H 13 H 17) by
    (apply (proj2 RT3); try lia; assumption).
  assert (RF4: K4ExactRow P B false (2*H+14) H 18).
  { applys_eq (k4_exact_row_rov B false (2*H+12) H 13 H 17);
      try lia; assumption. }
  split; [exists 17|exists 18]; assumption.
Qed.

End K4Rows.

Fixpoint k4_rdrops (B: list bool) (p: nat) : nat :=
  match p with
  | 0 => 0
  | S q =>
      (if nth q B false && negb (nth (S q) B false) then 1 else 0) +
      k4_rdrops B q
  end.

Inductive K4PointerTrace (B: list bool):
    nat -> nat -> nat -> nat -> Prop :=
| K4PointerDone u:
    K4PointerTrace B u 0 0 0
| K4PointerMore u x y n:
    x < length B -> y < length B ->
    (nth x B false = true -> 0 < x) ->
    (nth y B false = false -> 0 < y) ->
    2*x <= u -> 2*y <= u+1 ->
    2*length B <= u+2 ->
    (x<>0 \/ y<>0) ->
    K4PointerTrace B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) n ->
    K4PointerTrace B u x y (S n).

(* A finite prefix of the same deterministic pointer dynamics.  Unlike
   [K4PointerTrace], its endpoint need not be [(0,0)]; it is used to split a
   long scan at the two right-edge generators. *)
Inductive K4PointerPrefix (B: list bool):
    nat -> nat -> nat -> nat -> nat -> nat -> Prop :=
| K4PointerPrefixDone u x y:
    K4PointerPrefix B u x y 0 x y
| K4PointerPrefixMore u x y n xf yf:
    x < length B -> y < length B ->
    (nth x B false = true -> 0 < x) ->
    (nth y B false = false -> 0 < y) ->
    2*x <= u -> 2*y <= u+1 ->
    2*length B <= u+2 ->
    (x<>0 \/ y<>0) ->
    K4PointerPrefix B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) n xf yf ->
    K4PointerPrefix B u x y (S n) xf yf.

Section K4PointerFacts.

Variable B: list bool.
Hypothesis Bbase: nth 0 B false = true \/ nth 1 B false = true.

Lemma k4_pointer_scan p:
  (forall u,
    p < length B -> 2*length B <= u+2 -> 2*p <= u ->
    K4PointerTrace B u p p (p+k4_rdrops B p)) /\
  (forall u,
    S p < length B -> nth (S p) B false = false ->
    2*length B <= u+2 -> 2*S p <= u ->
    K4PointerTrace B u (S p) p (p+k4_rdrops B (S p))).
Proof.
  induction p as [|p [HD HO]].
  - split.
    + intros. cbn. constructor.
    + intros u Hl Hbit Hlen Hu.
      assert (H0: nth 0 B false = true) by
        (destruct Bbase; assumption || congruence).
      cbn [k4_rdrops]. rewrite H0, Hbit. cbn.
      apply K4PointerMore.
      * exact Hl.
      * lia.
      * intros; lia.
      * intros H; congruence.
      * lia.
      * lia.
      * exact Hlen.
      * lia.
      * unfold k4_next_y, k4_next_x. rewrite Hbit, H0. cbn.
        constructor.
  - assert (HD': forall u,
      S p < length B -> 2*length B <= u+2 -> 2*S p <= u ->
      K4PointerTrace B u (S p) (S p)
        (S p+k4_rdrops B (S p))).
    { intros u Hl Hlen Hu.
      destruct (nth (S p) B false) eqn:Hbit.
      - cbn [k4_rdrops]. rewrite Hbit. cbn.
        apply K4PointerMore.
        + exact Hl.
        + exact Hl.
        + intros; lia.
        + intros H; congruence.
        + exact Hu.
        + lia.
        + exact Hlen.
        + lia.
        + unfold k4_next_y, k4_next_x. rewrite Hbit. cbn.
          rewrite Bool.andb_false_r. cbn.
          applys_eq (HD (u+2)); try lia.
      - cbn [k4_rdrops]. rewrite Hbit.
        destruct (nth p B false) eqn:Hprev; cbn.
        + apply K4PointerMore.
          * exact Hl.
          * lia.
          * intros H; congruence.
          * intros; lia.
          * exact Hu.
          * lia.
          * exact Hlen.
          * lia.
          * unfold k4_next_y, k4_next_x. try rewrite Hbit. try rewrite Hprev. cbn.
            applys_eq (HO (u+2)); try lia; try assumption.
            cbn [k4_rdrops]. try rewrite Hbit. try rewrite Hprev. cbn. lia.
        + apply K4PointerMore.
          * exact Hl.
          * lia.
          * intros H; congruence.
          * intros; lia.
          * exact Hu.
          * lia.
          * exact Hlen.
          * lia.
          * unfold k4_next_y, k4_next_x. try rewrite Hbit. try rewrite Hprev. cbn.
            applys_eq (HO (u+2)); try lia; try assumption.
            cbn [k4_rdrops]. try rewrite Hbit. try rewrite Hprev. cbn. lia. }
    split; [exact HD'|].
    intros u Hl Hbit Hlen Hu.
    destruct (nth (S p) B false) eqn:Hprev.
    + cbn [k4_rdrops]. rewrite Hbit, Hprev. cbn.
      apply K4PointerMore.
      * exact Hl.
      * lia.
      * intros H; congruence.
      * intros H; congruence.
      * exact Hu.
      * lia.
      * exact Hlen.
      * lia.
      * unfold k4_next_y, k4_next_x. try rewrite Hbit. try rewrite Hprev. cbn.
        applys_eq (HD' (u+2)); try lia.
        cbn [k4_rdrops]. try rewrite Hbit. try rewrite Hprev. cbn. lia.
    + cbn [k4_rdrops]. rewrite Hbit, Hprev. cbn.
      apply K4PointerMore.
      * exact Hl.
      * lia.
      * intros H; congruence.
      * intros; lia.
      * exact Hu.
      * lia.
      * exact Hlen.
      * lia.
      * unfold k4_next_y, k4_next_x. try rewrite Hbit. try rewrite Hprev. cbn.
        applys_eq (HO (u+2)); try lia; try assumption.
        cbn [k4_rdrops]. try rewrite Hbit. try rewrite Hprev. cbn. lia.
Qed.

End K4PointerFacts.

Section K4TraceRows.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4CoreRules P.

Lemma k4_pointer_trace_rows B u x y n:
  K4PointerTrace B u x y n ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4Row P B true (u+2*n) 0 /\
  K4Row P B false (u+2*n+1) 0.
Proof.
  intros HT.
  induction HT; intros HR1 HR0.
  - split.
    + applys_eq HR1; lia.
    + applys_eq HR0; lia.
  - destruct (k4_rows_step P R B u x y HR1 HR0 H H0 H1 H2 H3 H4 H5)
      as [HR1' HR0'].
    assert (HR0'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq HR0'; lia).
    destruct (IHHT HR1' HR0'') as [HA HB].
    split.
    + applys_eq HA; lia.
    + applys_eq HB; lia.
Qed.

End K4TraceRows.

Lemma k4_pointer_follow_ok B u x y n z:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  K4PointerTrace B u x y n ->
  K4FollowerOK B x y z ->
  K4FollowTrace B u x y z n.
Proof.
  intros HB HT. revert z. induction HT; intros z HOK.
  - assert (z=0).
    { unfold K4FollowerOK in HOK.
      destruct HOK as [[Hxy Hzx] |
        [[Hxy [Hzy Hy]] | [[Hxy [Hzx [Hy Hx]]] | [Hxy [Hzx Hx]]]]];
        lia. }
    subst. constructor.
  - destruct (k4_follower_ok_step B x y z HB H6 HOK) as [Hz0 HOK'].
    assert (Hzl: z<length B).
    { unfold K4FollowerOK in HOK.
      destruct HOK as [[Hxy Hzx] |
        [[Hxy [Hzy Hy]] | [[Hxy [Hzx [Hy Hx]]] | [Hxy [Hzx Hx]]]]];
        lia. }
    eapply K4FollowMore.
    + exact Hzl.
    + exact Hz0.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + exact (IHHT _ HOK').
Qed.

Lemma k4_pointer_follow_lag B u p q n:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  2<=p -> q+2<=p ->
  K4PointerTrace B u p p n ->
  K4FollowTrace B u p p q n.
Proof.
  intros HB Hp Hq HT. inverts HT.
  - lia.
  - assert (HOK: K4FollowerOK B (k4_next_x B p p)
        (k4_next_y B p p) (k4_follow B p p q)).
    { unfold K4FollowerOK, k4_follow, k4_next_y, k4_next_x.
      destruct (nth p B false) eqn:EP,
               (nth q B false) eqn:EQ; cbn.
      - left; lia.
      - left; lia.
      - right; right; left. repeat split; try lia; assumption.
      - right; left. repeat split; try lia. }
    eapply K4FollowMore.
    + lia.
    + intros; lia.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + eapply k4_pointer_follow_ok; eauto.
Qed.

Lemma k4_pointer_follow_behind B u x y q n:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> 2<=y -> q+2<=y ->
  K4PointerTrace B u x y n ->
  K4FollowTrace B u x y q n.
Proof.
  intros HB Hxy Hy Hq HT. inverts HT.
  - lia.
  - assert (Heq: x=y \/ x=S y) by lia.
    assert (HOK: K4FollowerOK B (k4_next_x B x y)
        (k4_next_y B x y) (k4_follow B x y q)).
    { destruct Heq as [Heq|Heq]; subst x.
      - unfold K4FollowerOK, k4_follow, k4_next_y, k4_next_x.
        destruct (nth y B false) eqn:EY,
                 (nth q B false) eqn:EQ; cbn.
        + left; lia.
        + left; lia.
        + right; right; left. repeat split; try lia; assumption.
        + right; left. repeat split; try lia.
      - assert (Hnx: k4_next_x B (S y) y=y).
        { unfold k4_next_x. destruct (nth (S y) B false); lia. }
        unfold K4FollowerOK, k4_follow, k4_next_y.
        rewrite Hnx.
        destruct (nth y B false) eqn:EY,
                 (nth q B false) eqn:EQ; cbn.
        + left; lia.
        + right; right; right. repeat split; try lia; assumption.
        + right; right; left. repeat split; try lia; assumption.
        + right; left. repeat split; try lia. }
    eapply K4FollowMore.
    + lia.
    + intros; lia.
    + exact H.
    + exact H0.
    + exact H1.
    + exact H2.
    + exact H3.
    + exact H4.
    + exact H5.
    + eapply k4_pointer_follow_ok; eauto.
Qed.

Lemma k4_pointer_pair_step B x y:
  y<=x<=S y ->
  y-1 <= k4_next_y B x y /\
  k4_next_y B x y <= k4_next_x B x y <= S (k4_next_y B x y).
Proof.
  intros Hxy.
  unfold k4_next_y, k4_next_x.
  destruct (nth x B false), (nth y B false); cbn; lia.
Qed.

Lemma k4_pointer_trace_uncons B u x y n:
  (x<>0 \/ y<>0) ->
  K4PointerTrace B u x y n ->
  exists m,
    n=S m /\
    x<length B /\ y<length B /\
    (nth x B false=true -> 0<x) /\
    (nth y B false=false -> 0<y) /\
    2*x<=u /\ 2*y<=u+1 /\ 2*length B<=u+2 /\
    K4PointerTrace B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) m.
Proof.
  intros Hnz HT. inverts HT; [lia|].
  eexists. repeat split; eauto.
Qed.

Lemma k4_pointer_trace_split B u x y n q:
  q<=n -> K4PointerTrace B u x y n ->
  exists xf yf m,
    n=q+m /\
    K4PointerPrefix B u x y q xf yf /\
    K4PointerTrace B (u+2*q) xf yf m.
Proof.
  revert B u x y n.
  induction q as [|q IH]; intros B u x y n Hqn HT.
  - exists x,y,n. cbn. split; [lia|]. split.
    + constructor.
    + applys_eq HT; lia.
  - assert (Hnz: x<>0 \/ y<>0).
    { destruct HT; [lia|assumption]. }
    destruct (k4_pointer_trace_uncons B u x y n Hnz HT) as
      [n' [Hn [Hxl [Hyl [Hx0 [Hy0 [Hxu [Hyu [Hlen HT']]]]]]]]].
    subst n.
    destruct (IH B (u+2) (k4_next_x B x y) (k4_next_y B x y) n')
      as (xf&yf&m&Hnm&HP&HTf); try assumption; try lia.
    exists xf,yf,m. split; [lia|]. split.
    + econstructor; eauto.
    + applys_eq HTf; lia.
Qed.

Section K4PointerAdvance.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4CoreRules P.

(* Split a pointer scan after [q] rows while transporting both semantic rows.
   The last inequality records the only quantitative fact needed at the
   split: the false-row pointer falls by at most one per step. *)
Lemma k4_pointer_advance B u x y n q:
  q<=n ->
  K4PointerTrace B u x y n ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  y<=x<=S y ->
  exists x' y' m,
    n=q+m /\
    K4PointerTrace B (u+2*q) x' y' m /\
    K4Row P B true (u+2*q) x' /\
    K4Row P B false (u+2*q+1) y' /\
    y'<=x'<=S y' /\
    y-q<=y'.
Proof.
  revert B u x y n.
  induction q as [|q IH]; intros B u x y n Hqn HT RT RF Hxy.
  - exists x,y,n.
    split; [lia|].
    split; [applys_eq HT; lia|].
    split; [applys_eq RT; lia|].
    split; [applys_eq RF; lia|].
    split; [exact Hxy|lia].
  - assert (Hnz: x<>0 \/ y<>0).
    { destruct HT; [lia|assumption]. }
    destruct (k4_pointer_trace_uncons B u x y n Hnz HT) as
      [n' [Hn [Hxl [Hyl [Hx0 [Hy0 [Hxu [Hyu [Hlen HT']]]]]]]]].
    subst n.
    destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
      as [RT' RF'].
    assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF'; lia).
    destruct (k4_pointer_pair_step B x y Hxy) as [Hlower Hpair].
    destruct (IH B (u+2) (k4_next_x B x y) (k4_next_y B x y) n')
      as (xf&yf&m&Hnm&HTf&RTf&RFf&Hpairf&Hlowerf);
      try assumption; try lia.
    exists xf,yf,m.
    split; [lia|].
    split; [applys_eq HTf; lia|].
    split; [applys_eq RTf; lia|].
    split; [applys_eq RFf; lia|].
    split; [exact Hpairf|lia].
Qed.

End K4PointerAdvance.

Section K4PointerPrefixRows.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4CoreRules P.

Lemma k4_pointer_prefix_rows B u x y n xf yf:
  K4PointerPrefix B u x y n xf yf ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4Row P B true (u+2*n) xf /\
  K4Row P B false (u+2*n+1) yf.
Proof.
  intros HP. induction HP; intros RT RF.
  - cbn. split.
    + applys_eq RT; lia.
    + applys_eq RF; lia.
  - destruct (k4_rows_step P R B u x y RT RF H H0 H1 H2 H3 H4 H5)
      as [RT' RF'].
    assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF'; lia).
    destruct (IHHP RT' RF'') as [RTf RFf].
    split.
    + applys_eq RTf; lia.
    + applys_eq RFf; lia.
Qed.

Lemma k4_pointer_prefix_synced_particle B u x y n xf yf a:
  K4PointerPrefix B u x y n xf yf ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4Particle P u a y ->
  K4Particle P (u+2*n) a yf.
Proof.
  intros HP. induction HP; intros RT RF HA.
  - cbn. applys_eq HA; lia.
  - destruct (k4_rows_step P R B u x y RT RF H H0 H1 H2 H3 H4 H5)
      as [RT' RF'].
    assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF'; lia).
    assert (HA': K4Particle P (u+2) a (k4_next_y B x y)).
    { applys_eq (k4_particle_step P R B u x y y a RT' RF H0 H2 H5 HA);
        unfold k4_follow, k4_next_y; reflexivity || lia. }
    applys_eq (IHHP RT' RF'' HA'); lia.
Qed.

Lemma k4_pointer_prefix_uncons B u x y n xf yf:
  K4PointerPrefix B u x y (S n) xf yf ->
  x<length B /\ y<length B /\
  (nth x B false=true -> 0<x) /\
  (nth y B false=false -> 0<y) /\
  2*x<=u /\ 2*y<=u+1 /\ 2*length B<=u+2 /\
  (x<>0 \/ y<>0) /\
  K4PointerPrefix B (u+2) (k4_next_x B x y)
    (k4_next_y B x y) n xf yf.
Proof.
  intros HP. inverts HP. repeat split; eauto.
Qed.

Lemma k4_follower_ok_bound B x y z:
  x<length B -> y<length B -> K4FollowerOK B x y z -> z<length B.
Proof.
  unfold K4FollowerOK. intros Hx Hy
    [[E F] | [[E [F G]] | [[E [F [G I]]] | [E [F G]]]]]; lia.
Qed.

(* A live follower has joined the low pointer after two prefix steps; all
   remaining steps can then use the simpler synchronized-particle lemma. *)
Lemma k4_pointer_prefix_live_particle B u x y n xf yf z a:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  K4PointerPrefix B u x y (2+n) xf yf ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  K4FollowerOK B x y z ->
  K4Particle P u a z ->
  K4Particle P (u+2*(2+n)) a yf.
Proof.
  intros HB HP RT RF HOK HA.
  destruct (k4_pointer_prefix_uncons B u x y (1+n) xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
    (applys_eq RF1; lia).
  destruct (k4_follower_ok_step B x y z HB Hnz HOK) as [Hz0 HOK1].
  assert (Hzl: z<length B) by
    exact (k4_follower_ok_bound B x y z Hxl Hyl HOK).
  assert (HA1: K4Particle P (u+2) a (k4_follow B x y z)).
  { exact (k4_particle_step P R B u x y z a RT1 RF Hzl Hz0 Hlen HA). }
  destruct (k4_pointer_prefix_uncons B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) n xf yf HP1) as
    (Hx1l&Hy1l&Hx10&Hy10&Hx1u&Hy1u&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step P R B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) RT1 RF1' Hx1l Hy1l Hx10 Hy10
      Hx1u Hy1u Hlen1) as [RT2 RF2].
  assert (RF2': K4Row P B false (u+4+1)
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RF2; lia).
  destruct (k4_follower_ok_step B _ _ _ HB Hnz1 HOK1) as [Hz10 HOK2].
  assert (Hz1l: k4_follow B x y z<length B) by
    exact (k4_follower_ok_bound B _ _ _ Hx1l Hy1l HOK1).
  assert (HA2: K4Particle P (u+4) a
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y))).
  { rewrite <- (k4_follower_two B x y z HOK).
    applys_eq (k4_particle_step P R B (u+2) (k4_next_x B x y)
      (k4_next_y B x y) (k4_follow B x y z) a
      RT2 RF1' Hz1l Hz10 Hlen1 HA1); lia. }
  assert (HP2': K4PointerPrefix B (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))
      (k4_next_y B (k4_next_x B x y) (k4_next_y B x y)) n xf yf) by
    (applys_eq HP2; lia).
  assert (RT2': K4Row P B true (u+4)
      (k4_next_x B (k4_next_x B x y) (k4_next_y B x y))) by
    (applys_eq RT2; lia).
  applys_eq (k4_pointer_prefix_synced_particle B (u+4)
    _ _ n xf yf a HP2' RT2' RF2' HA2); lia.
Qed.

End K4PointerPrefixRows.

Section K4GeneratedParticles.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable R: K4CoreRules P.

Lemma k4_generated_particles B u x y q n e de:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> q+2<=y ->
  K4PointerTrace B u x y n ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  P e 0 q de -> 2*e=u+1 -> 2*q+de=u+5 ->
  forall j, j<=q -> K4Particle P (u+2*n) (e+j) 0.
Proof.
  revert B u x y n e de.
  induction q as [|q IH]; intros B u x y n e de
    HB Hxy Hqy HT RT RF HE Hew Heout j Hj.
  - assert (j=0) by lia; subst j.
    assert (HP: K4Particle P u e 0).
    { exists 0,de. repeat split; assumption || lia. }
    eapply (k4_follow_trace_particle P R).
    + eapply k4_pointer_follow_behind; eauto; lia.
    + exact RT.
    + exact RF.
    + applys_eq HP; lia.
  - assert (HP: K4Particle P u e (S q)).
    { exists 0,de. repeat split; assumption || lia. }
    destruct j as [|j].
    + eapply (k4_follow_trace_particle P R).
      * eapply k4_pointer_follow_behind; eauto; lia.
      * exact RT.
      * exact RF.
      * applys_eq HP; lia.
    + destruct (k4_pointer_trace_uncons B u x y n) as
        [m [Hn [Hxl [Hyl [Hx0 [Hy0 [Hxu [Hyu [Hlen HT']]]]]]]]];
        try lia; try exact HT.
      subst n.
      destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0
        Hxu Hyu Hlen)
        as [RT' RF'].
      assert (RF'': K4Row P B false (u+2+1) (k4_next_y B x y)) by
        (applys_eq RF'; lia).
      assert (HE': P (S e) 0 q (de+4)).
      { applys_eq (k4core_inc01 R e q de); try lia. exact HE. }
      destruct (k4_pointer_pair_step B x y Hxy) as [Hylow Hpair].
      assert (Hrec: K4Particle P ((u+2)+2*m) ((S e)+j) 0).
      { eapply IH; eauto; lia. }
      applys_eq Hrec; lia.
Qed.

(* Stop the first right-edge generator three pointer rows after its counter
   reaches zero.  By then every emitted column, including the former zero
   endpoint, has synchronized with the same low pointer. *)
Lemma k4_generated_synced B u x y q e de xf yf:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> q+2<=y ->
  K4PointerPrefix B u x y (q+3) xf yf ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  P e 0 q de -> 2*e=u+1 -> 2*q+de=u+5 ->
  forall j, j<=q -> K4Particle P (u+2*(q+3)) (e+j) yf.
Proof.
  revert B u x y e de xf yf.
  induction q as [|q IH]; intros B u x y e de xf yf
    HB Hxy Hqy HP RT RF HE Hew Heout j Hj.
  - assert (j=0) by lia. subst j.
    destruct (k4_pointer_prefix_uncons B u x y 2 xf yf HP) as
      (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
    destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
      as [RT1 RF1].
    assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF1; lia).
    assert (HOK1: K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y)
        (k4_follow B x y 0)) by
      (eapply k4_follower_behind_step; eauto).
    assert (HA: K4Particle P u e 0).
    { exists 0,de. repeat split; assumption || lia. }
    assert (HA1: K4Particle P (u+2) e (k4_follow B x y 0)).
    { eapply (k4_particle_step P R); eauto; intros; lia. }
    applys_eq (k4_pointer_prefix_live_particle P R B (u+2) _ _ 0 xf yf
      _ e HB HP1 RT1 RF1' HOK1 HA1); lia.
  - destruct j as [|j].
    + destruct (k4_pointer_prefix_uncons B u x y (q+3) xf yf HP) as
        (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
      destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
        as [RT1 RF1].
      assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
        (applys_eq RF1; lia).
      assert (HOK1: K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y)
          (k4_follow B x y (S q))) by
        (eapply k4_follower_behind_step; eauto).
      assert (HA: K4Particle P u e (S q)).
      { exists 0,de. repeat split; assumption || lia. }
      assert (Hz0: nth (S q) B false=false -> 0<y) by (intros; lia).
      assert (Hzl: S q<length B) by lia.
      assert (HA1: K4Particle P (u+2) e (k4_follow B x y (S q))).
      { exact (k4_particle_step P R B u x y (S q) e
          RT1 RF Hzl Hz0 Hlen HA). }
      assert (HP1': K4PointerPrefix B (u+2) (k4_next_x B x y)
          (k4_next_y B x y) (2+(q+1)) xf yf) by
        (applys_eq HP1; lia).
      applys_eq (k4_pointer_prefix_live_particle P R B (u+2) _ _ (q+1)
        xf yf _ e HB HP1' RT1 RF1' HOK1 HA1); lia.
    + destruct (k4_pointer_prefix_uncons B u x y (q+3) xf yf HP) as
        (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
      destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
        as [RT1 RF1].
      assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
        (applys_eq RF1; lia).
      assert (HE': P (S e) 0 q (de+4)).
      { applys_eq (k4core_inc01 R e q de); try lia. exact HE. }
      destruct (k4_pointer_pair_step B x y Hxy) as [Hlower Hpair].
      assert (Hqy': q+2<=k4_next_y B x y) by lia.
      assert (Hew': 2*S e=(u+2)+1) by lia.
      assert (Heout': 2*q+(de+4)=(u+2)+5) by lia.
      applys_eq (IH B (u+2) (k4_next_x B x y) (k4_next_y B x y)
        (S e) (de+4) xf yf HB Hpair Hqy' HP1 RT1 RF1' HE'
        Hew' Heout' j); lia.
Qed.

(* Once a decreasing endpoint points into a synchronized first segment, one
   ordinary overflow turns the old endpoint into a live follower while
   [PInc01] creates the next endpoint. *)
Lemma k4_endpoint_absorb B u x y A C de:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y ->
  0<y -> 0<C -> 4<=de ->
  K4Particle P u C y ->
  P A 0 C de -> 2*A=u+1 -> 2*C+de=u+5 ->
  K4Particle P (u+2) A (y-1) /\
  K4FollowerOK B (k4_next_x B x y) (k4_next_y B x y) (y-1) /\
  P (S A) 0 (C-1) (de+4).
Proof.
  intros HB Hxy Hy HC Hde [b [d [HCb [Hyd HD]]]] HE HEw HCw.
  assert (Hb: b=de-4) by lia. subst b.
  assert (HA: P A 2 (y-1) (d+4)).
  { applys_eq (k4core_rov' R A 0 C (de-4) (y-1) d); try lia.
    - applys_eq HE; lia.
    - applys_eq HD; lia. }
  split.
  - exists 2,(d+4). repeat split; try assumption; lia.
  - split.
    + apply k4_synced_decrement_ok; assumption.
    + applys_eq (k4core_inc01 R A (C-1) de); try lia.
      applys_eq HE; lia.
Qed.

(* Iterate the synchronized-driver step while at least two pointer rows remain.
   Every absorbed endpoint is handed immediately to the live-particle lemma;
   only a constant two-row boundary is returned to the caller. *)
Lemma k4_pointer_prefix_long_y B u x y n xf yf:
  y<=x<=S y -> K4PointerPrefix B u x y (3+n) xf yf -> 0<y.
Proof.
  intros Hpair HP.
  destruct (k4_pointer_prefix_uncons B u x y (2+n) xf yf HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct y; [|lia].
  assert (x=0 \/ x=1) by lia. destruct H as [E|E]; subst x.
  - destruct Hnz; contradiction.
  - assert (HX: k4_next_x B 1 0=0) by
      (unfold k4_next_x; destruct (nth 1 B false); reflexivity).
    assert (HY: k4_next_y B 1 0=0) by
      (unfold k4_next_y; rewrite HX; destruct (nth 0 B false); reflexivity).
    rewrite HX,HY in HP1.
    destruct (k4_pointer_prefix_uncons B (u+2) 0 0 (1+n) xf yf HP1) as
      (_&_&_&_&_&_&_&Hnz1&_).
    destruct Hnz1; contradiction.
Qed.

Lemma k4_endpoint_early B u x y n E C de:
  (nth 0 B false=true \/ nth 1 B false=true) ->
  y<=x<=S y -> n+2<=C -> 4<=de ->
  K4PointerPrefix B u x y (n+2) 0 0 ->
  K4Row P B true u x ->
  K4Row P B false (u+1) y ->
  (forall j, j<=n+2 -> K4Particle P u (C-j) y) ->
  P E 0 C de -> 2*E=u+1 -> 2*C+de=u+5 ->
  exists xn yn,
    K4PointerPrefix B u x y n xn yn /\
    K4PointerPrefix B (u+2*n) xn yn 2 0 0 /\
    K4Row P B true (u+2*n) xn /\
    K4Row P B false (u+2*n+1) yn /\
    yn<=xn<=S yn /\
    (forall j, j<=2 -> K4Particle P (u+2*n) (C-n-j) yn) /\
    P (E+n) 0 (C-n) (de+4*n) /\
    (forall j, j<n -> K4Particle P (u+2*(n+2)) (E+j) 0).
Proof.
  revert B u x y E C de.
  induction n as [|n IH]; intros B u x y E C de HB Hxy HnC Hde
    HP RT RF HD HE HEw HCw.
  - exists x,y. cbn.
    split; [constructor|].
    split; [applys_eq HP; lia|].
    split; [applys_eq RT; lia|].
    split; [applys_eq RF; lia|].
    split; [exact Hxy|].
    split.
    + intros j Hj. applys_eq (HD j); lia.
    + split; [applys_eq HE; lia|].
      intros j Hj. lia.
  - destruct (k4_pointer_prefix_uncons B u x y (n+2) 0 0 HP) as
      (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
    destruct (k4_rows_step P R B u x y RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
      as [RT1 RF1].
    assert (RF1': K4Row P B false (u+2+1) (k4_next_y B x y)) by
      (applys_eq RF1; lia).
    destruct (k4_pointer_pair_step B x y Hxy) as [Hlower Hpair].
    assert (Hy: 0<y).
    { apply (k4_pointer_prefix_long_y B u x y n 0 0 Hxy).
      replace (3+n) with (S n+2) by lia. exact HP. }
    assert (HCp: K4Particle P u C y) by
      (applys_eq (HD 0); lia).
    destruct (k4_endpoint_absorb B u x y E C de HB Hxy)
      as [HElive [HOK HEnext]]; try assumption; try lia.
    assert (HP1': K4PointerPrefix B (u+2) (k4_next_x B x y)
        (k4_next_y B x y) (2+n) 0 0) by (applys_eq HP1; lia).
    assert (HEzero: K4Particle P (u+2*((S n)+2)) E 0).
    { applys_eq (k4_pointer_prefix_live_particle P R B (u+2) _ _ n 0 0
        (y-1) E HB HP1' RT1 RF1' HOK HElive); lia. }
    assert (HD1: forall j, j<=n+2 ->
        K4Particle P (u+2) ((C-1)-j) (k4_next_y B x y)).
    { intros j Hj.
      assert (HCj: C-1-j=C-S j) by lia.
      rewrite HCj.
      assert (Hsrc: K4Particle P u (C-S j) y).
      { apply HD. lia. }
      applys_eq (k4_particle_step P R B u x y y (C-S j)
        RT1 RF Hyl Hy0 Hlen Hsrc);
        unfold k4_follow, k4_next_y; reflexivity || lia. }
    assert (HnC1: n+2<=C-1) by lia.
    assert (HEw1: 2*S E=(u+2)+1) by lia.
    assert (HCw1: 2*(C-1)+(de+4)=(u+2)+5) by lia.
    destruct (IH B (u+2) (k4_next_x B x y) (k4_next_y B x y)
      (S E) (C-1) (de+4) HB Hpair HnC1 ltac:(lia)
      HP1 RT1 RF1' HD1 HEnext HEw1 HCw1) as
      (xn&yn&Hreach&Htail&RTn&RFn&Hpairn&HDn&HEn&Hzeros).
    exists xn,yn.
    split.
    + econstructor; eauto.
    + split; [applys_eq Htail; lia|].
    split; [applys_eq RTn; lia|].
    split; [applys_eq RFn; lia|].
    split; [exact Hpairn|].
    split.
    * intros j Hj. applys_eq (HDn j); lia.
    * split; [applys_eq HEn; lia|].
      intros j Hj. destruct j as [|j].
      -- applys_eq HEzero; lia.
      -- applys_eq (Hzeros j); lia.
Qed.

(* The two phase kinds have different final two pointer rows.  In the T4
   ending the penultimate endpoint survives as the unique new dent; in the
   T2 ending it is absorbed by the second true row. *)
Lemma k4_endpoint_last2_t4 B u E C de:
  nth 0 B false=true -> nth 1 B false=false -> nth 2 B false=false ->
  4<=C -> 4<=de ->
  K4PointerPrefix B u 2 1 2 0 0 ->
  K4Row P B true u 2 -> K4Row P B false (u+1) 1 ->
  (forall j, j<=2 -> K4Particle P u (C-j) 1) ->
  P E 0 C de -> 2*E=u+1 -> 2*C+de=u+5 ->
  (forall j, j<=2 -> K4Particle P (u+4) (C-j) 0) /\
  K4Particle P (u+2) (C-1) 0 /\
  K4Particle P (u+4) E 0 /\
  P (S E) 0 (C-1) (de+4) /\
  P (E+2) 0 (C-2) (de+8).
Proof.
  intros B0 B1 B2 HC Hde HP RT RF HD HE HEw HCw.
  destruct (k4_pointer_prefix_uncons B u 2 1 1 0 0 HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step P R B u 2 1 RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (HX: k4_next_x B 2 1=1) by
    (unfold k4_next_x; rewrite B2; reflexivity).
  assert (HY: k4_next_y B 2 1=0) by
    (unfold k4_next_y; rewrite B1; reflexivity).
  assert (RF1': K4Row P B false (u+2+1) 0) by
    (rewrite HY in RF1; applys_eq RF1; lia).
  assert (RT1': K4Row P B true (u+2) 1) by
    (rewrite HX in RT1; exact RT1).
  assert (HCp: K4Particle P u C 1) by (applys_eq (HD 0); lia).
  destruct (k4_endpoint_absorb B u 2 1 E C de
    ltac:(auto) ltac:(lia) ltac:(lia) ltac:(lia) Hde HCp HE HEw HCw)
    as [HElive [HOK HEnext]].
  assert (HP1': K4PointerPrefix B (u+2) 1 0 1 0 0) by
    (rewrite HX,HY in HP1; exact HP1).
  assert (HCpre: K4Particle P (u+2) (C-1) 0).
  { applys_eq (k4_particle_step P R B u 2 1 1 (C-1)
      RT1 RF Hyl Hy0 Hlen (HD 1 ltac:(lia)));
      unfold k4_follow; rewrite B1; cbn; lia || reflexivity. }
  assert (HEzero: K4Particle P (u+4) E 0).
  { applys_eq (k4_pointer_prefix_synced_particle P R B (u+2) 1 0 1 0 0 E
      HP1' RT1' RF1' HElive); lia. }
  split.
  - intros j Hj. applys_eq (k4_pointer_prefix_synced_particle P R B u 2 1
      2 0 0 (C-j) HP RT RF (HD j Hj)); lia.
  - split; [exact HCpre|]. split; [exact HEzero|]. split; [exact HEnext|].
    applys_eq (k4core_inc01 R (S E) (C-2) (de+4)); try lia.
    applys_eq HEnext; lia.
Qed.

Lemma k4_endpoint_last2_t2 B u E C de:
  nth 0 B false=false -> nth 1 B false=true -> nth 2 B false=true ->
  4<=C -> 4<=de ->
  K4PointerPrefix B u 2 2 2 0 0 ->
  K4Row P B true u 2 -> K4Row P B false (u+1) 2 ->
  (forall j, j<=2 -> K4Particle P u (C-j) 2) ->
  P E 0 C de -> 2*E=u+1 -> 2*C+de=u+5 ->
  (forall j, j<=2 -> K4Particle P (u+4) (C-j) 0) /\
  K4Particle P (u+4) E 0 /\
  K4Particle P (u+4) (S E) 0 /\
  P (E+2) 0 (C-2) (de+8).
Proof.
  intros B0 B1 B2 HC Hde HP RT RF HD HE HEw HCw.
  destruct (k4_pointer_prefix_uncons B u 2 2 1 0 0 HP) as
    (Hxl&Hyl&Hx0&Hy0&Hxu&Hyu&Hlen&Hnz&HP1).
  destruct (k4_rows_step P R B u 2 2 RT RF Hxl Hyl Hx0 Hy0 Hxu Hyu Hlen)
    as [RT1 RF1].
  assert (HX: k4_next_x B 2 2=1) by
    (unfold k4_next_x; rewrite B2; reflexivity).
  assert (HY: k4_next_y B 2 2=1) by
    (unfold k4_next_y; rewrite B2,HX; reflexivity).
  rewrite HX in RT1. rewrite HY in RF1,HP1.
  rewrite HX in HP1.
  assert (RF1': K4Row P B false (u+2+1) 1) by
    (applys_eq RF1; lia).
  assert (RT1e: K4Row P B true (u+2) (k4_next_x B 2 2)) by
    (rewrite HX; exact RT1).
  assert (HCp: K4Particle P u C 2) by (applys_eq (HD 0); lia).
  destruct (k4_endpoint_absorb B u 2 2 E C de
    ltac:(auto) ltac:(lia) ltac:(lia) ltac:(lia) Hde HCp HE HEw HCw)
    as [HElive [HOK HEnext]].
  assert (HCm1: K4Particle P (u+2) (C-1) 1).
  { applys_eq (k4_particle_step P R B u 2 2 2 (C-1)
      RT1e RF Hyl Hy0 Hlen (HD 1 ltac:(lia)));
      unfold k4_follow, k4_next_x, k4_next_y;
      rewrite B2; cbn; lia || reflexivity. }
  destruct (k4_pointer_prefix_uncons B (u+2) 1 1 0 0 0 HP1) as
    (Hx1l&Hy1l&Hx10&Hy10&Hx1u&Hy1u&Hlen1&Hnz1&HP2).
  destruct (k4_rows_step P R B (u+2) 1 1 RT1 RF1' Hx1l Hy1l Hx10 Hy10
    Hx1u Hy1u Hlen1) as [RT2 RF2].
  destruct (k4_endpoint_absorb B (u+2) 1 1 (S E) (C-1) (de+4)
    ltac:(auto) ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)
    HCm1 HEnext ltac:(lia) ltac:(lia)) as [HE1zero [HOK1 HEfinal]].
  assert (HEzero: K4Particle P (u+4) E 0).
  { applys_eq (k4_pointer_prefix_synced_particle P R B (u+2) 1 1 1 0 0 E
      HP1 RT1 RF1' HElive); lia. }
  split.
  - intros j Hj. applys_eq (k4_pointer_prefix_synced_particle P R B u 2 2
      2 0 0 (C-j) HP RT RF (HD j Hj)); lia.
  - split; [exact HEzero|]. split.
    + applys_eq HE1zero; lia.
    + applys_eq HEfinal; lia.
Qed.

End K4GeneratedParticles.

(* RLE description used by the complete complex-K4 phase invariant.  The
   stronger final inequality is deliberately much stronger than mere
   positivity: unlike [H-2*S >= number_of_runs], it is preserved when the
   two alternating phase kinds update their true-to-false boundary counts by
   different amounts. *)
Inductive K4Kind := K4T4 | K4T2.

Definition k4_gap (kind: K4Kind) : nat :=
  match kind with K4T4 => 6 | K4T2 => 5 end.

Definition k4_first_bit (kind: K4Kind) : bool :=
  match kind with K4T4 => true | K4T2 => false end.

Definition k4_run_count (kind: K4Kind) (k: nat) : nat :=
  match kind with K4T4 => 2*k+1 | K4T2 => 2*k+2 end.

Definition k4_next_kind (kind: K4Kind) : K4Kind :=
  match kind with K4T4 => K4T2 | K4T2 => K4T4 end.

Definition k4_next_k (kind: K4Kind) (k: nat) : nat :=
  match kind with K4T4 => k+1 | K4T2 => k+2 end.

Definition K4HeadBits (kind: K4Kind) (B: list bool) : Prop :=
  match kind with
  | K4T4 => nth 0 B false=true /\ nth 1 B false=false /\
      nth 2 B false=false
  | K4T2 => nth 0 B false=false /\ nth 1 B false=true /\
      nth 2 B false=true
  end.

Fixpoint k4_sum (xs: list nat) : nat :=
  match xs with
  | [] => 0
  | x::xs => x+k4_sum xs
  end.

Fixpoint k4_bits (bit: bool) (runs: list nat) : list bool :=
  match runs with
  | [] => []
  | n::runs => repeat bit n ++ k4_bits (negb bit) runs
  end.

Fixpoint k4_after (bit: bool) (runs: list nat) : bool :=
  match runs with
  | [] => bit
  | _::runs => k4_after (negb bit) runs
  end.

Lemma k4_bits_length bit runs:
  length (k4_bits bit runs)=k4_sum runs.
Proof.
  induction runs as [|n runs IH] in bit |- *; cbn; rewrite ?length_app,
    ?repeat_length, ?IH; lia.
Qed.

Lemma k4_bits_negb bit runs:
  map negb (k4_bits bit runs)=k4_bits (negb bit) runs.
Proof.
  induction runs as [|n runs IH] in bit |- *; cbn.
  - reflexivity.
  - rewrite map_app, map_repeat, IH. reflexivity.
Qed.

Lemma k4_bits_app bit xs ys:
  k4_bits bit (xs++ys)=
    k4_bits bit xs++k4_bits (k4_after bit xs) ys.
Proof.
  induction xs as [|n xs IH] in bit |- *; cbn.
  - reflexivity.
  - rewrite IH, app_assoc. reflexivity.
Qed.

Lemma k4_after_even k bit runs:
  length runs=2*k -> k4_after bit runs=bit.
Proof.
  induction k as [|k IH] in bit, runs |- *; intros Hlen.
  - destruct runs; cbn in *; congruence.
  - destruct runs as [|x [|y runs]]; cbn in Hlen; try lia.
    cbn. replace (negb (negb bit)) with bit by (destruct bit; reflexivity).
    apply IH. lia.
Qed.

Lemma k4_after_odd k bit runs:
  length runs=2*k+1 -> k4_after bit runs=negb bit.
Proof.
  intros Hlen. destruct runs as [|x runs]; cbn in Hlen; try lia.
  cbn. apply k4_after_even with (k:=k). lia.
Qed.

Definition K4RunShape (kind: K4Kind) (runs: list nat)
    (H S D k: nat) : Prop :=
  Forall (fun n => 0<n) runs /\
  length runs=k4_run_count kind k /\
  k4_sum runs=H+1 /\
  last runs 0=S /\
  H=2*S+D /\
  4*S+3*k+11 <= H /\
  1 <= k /\ 3 <= S.

Lemma k4_sum_app xs ys:
  k4_sum (xs++ys)=k4_sum xs+k4_sum ys.
Proof.
  induction xs; cbn; lia.
Qed.

Lemma k4_run_shape_next kind runs H S D k:
  K4RunShape kind runs H S D k ->
  K4RunShape (k4_next_kind kind)
    (runs++[D+3; 1; 2*S+k+3])
    (2*H+k+7) (2*S+k+3) (2*D+1-k) (k4_next_k kind k).
Proof.
  intros [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk HS]]]]]]].
  assert (Hdk: k <= 2*D+1) by lia.
  assert (Hlast':
    last (runs++[D+3; 1; 2*S+k+3]) 0=2*S+k+3).
  { replace (runs++[D+3; 1; 2*S+k+3])
      with ((runs++[D+3; 1])++[2*S+k+3]).
    - apply last_last.
    - symmetry.
      change ((runs ++ ([D+3; 1] ++ [2*S+k+3])) =
        ((runs++[D+3; 1])++[2*S+k+3])).
      apply app_assoc. }
  destruct kind; cbn in *; repeat split; try lia.
  all: try (apply Forall_app; split; [exact Hpos|repeat constructor; lia]).
  all: try (rewrite length_app; cbn; lia).
  all: try (rewrite k4_sum_app; cbn; lia).
  all: try exact Hlast'.
Qed.

(* The semantic scan does not inspect the RLE decomposition itself.  In
   particular it does not need the old final run to equal [S].  Keeping this
   weaker interface separate is useful for the one exceptional finite phase
   immediately before the stable RLE recurrence. *)
Definition K4ScanData (P: nat -> nat -> nat -> nat -> Prop)
    (kind: K4Kind) (B: list bool) (H S D k: nat) : Prop :=
  let g := k4_gap kind in
  let u := 2*H+2*g+5 in
  let p := H-g+4 in
  length B=H+1 /\
  H=2*S+D /\
  4*S+3*k+11 <= H /\
  1 <= k /\ 2 <= S /\
  (nth 0 B false=true \/ nth 1 B false=true) /\
  k4_rdrops B p=k /\
  K4ExactRow P B true u p (4*g+1) /\
  K4ExactRow P B false (u+1) p (4*g+2) /\
  (forall j, j <= g+1 ->
    P (H+g+2-j) (2+2*j) p (4*g+2)) /\
  P (H+g+3) 0 (D-g) (4*S+4*g+10).

Definition K4ScanStart (P: nat -> nat -> nat -> nat -> Prop)
    (kind: K4Kind) (runs: list nat) (B: list bool)
    (H S D k: nat) : Prop :=
  let g := k4_gap kind in
  let u := 2*H+2*g+5 in
  let p := H-g+4 in
  K4RunShape kind runs H S D k /\
  B=k4_bits (k4_first_bit kind) runs /\
  hd 0 runs=1 /\
  (nth 0 B false=true \/ nth 1 B false=true) /\
  k4_rdrops B p=k /\
  K4ExactRow P B true u p (4*g+1) /\
  K4ExactRow P B false (u+1) p (4*g+2) /\
  (forall j, j <= g+1 ->
    P (H+g+2-j) (2+2*j) p (4*g+2)) /\
  P (H+g+3) 0 (D-g) (4*S+4*g+10).

Lemma k4_scan_start_data P kind runs B H S D k:
  K4ScanStart P kind runs B H S D k ->
  K4ScanData P kind B H S D k.
Proof.
  unfold K4ScanStart,K4ScanData.
  destruct kind; cbn.
  all: intros [HS [HB [Hhead [Hbase [Hdrop Hrest]]]]];
    destruct HS as [Hpos [Hcount [Hsum [Hlast
      [Hhs [Hlarge [Hk Hs]]]]]]];
    destruct Hrest as [RT [RF [Htail Hex]]];
    split; [rewrite HB,k4_bits_length,Hsum; reflexivity|];
    split; [exact Hhs|];
    split; [exact Hlarge|];
    split; [exact Hk|];
    split; [lia|];
    split; [exact Hbase|];
    split; [exact Hdrop|];
    split; [exact RT|];
    split; [exact RF|];
    split; assumption.
Qed.

Lemma k4_scan_start_end P (R: K4SimpleRules P)
    kind runs B H S D k:
  K4ScanStart P kind runs B H S D k ->
  K4Row P B true (4*H+2*k+13) 0 /\
  K4Row P B false (4*H+2*k+14) 0.
Proof.
  unfold K4ScanStart.
  destruct kind; cbn.
  all: intros [HS [HB [Hhead [Hbase [Hdrop [RT [RF [Htail Hex]]]]]]]];
    destruct HS as [Hpos [Hcount [Hsum [Hlast [Hhs [Hlarge [Hk Hs]]]]]]];
    assert (Hlen: length B=H+1) by
      (rewrite HB, k4_bits_length, Hsum; reflexivity).
  - destruct (k4_pointer_scan B Hbase (H-2)) as [Hscan _].
    assert (HRD: k4_rdrops B (H-2)=k).
    { replace (H-2) with (H-6+4) by lia. exact Hdrop. }
    assert (HT: K4PointerTrace B (2*H+17) (H-2) (H-2) (H-2+k)).
    { applys_eq (Hscan (2*H+17)).
      all: try rewrite Hlen. all: try rewrite HRD. all: lia. }
    assert (RT': K4Row P B true (2*H+17) (H-2)).
    { exists 25. applys_eq RT; lia. }
    assert (RF': K4Row P B false (2*H+17+1) (H-2)).
    { exists 26. applys_eq RF; lia. }
    destruct (k4_pointer_trace_rows P R B _ _ _ _ HT
      RT' RF') as [HX HY].
    split.
    + assert (Heq: 2*H+17+2*(H-2+k)=4*H+2*k+13) by lia.
      rewrite Heq in HX. exact HX.
    + assert (Heq: 2*H+17+2*(H-2+k)+1=4*H+2*k+14) by lia.
      rewrite Heq in HY. exact HY.
  - destruct (k4_pointer_scan B Hbase (H-1)) as [Hscan _].
    assert (HRD: k4_rdrops B (H-1)=k).
    { replace (H-1) with (H-5+4) by lia. exact Hdrop. }
    assert (HT: K4PointerTrace B (2*H+15) (H-1) (H-1) (H-1+k)).
    { applys_eq (Hscan (2*H+15)).
      all: try rewrite Hlen. all: try rewrite HRD. all: lia. }
    assert (RT': K4Row P B true (2*H+15) (H-1)).
    { exists 21. applys_eq RT; lia. }
    assert (RF': K4Row P B false (2*H+15+1) (H-1)).
    { exists 22. applys_eq RF; lia. }
    destruct (k4_pointer_trace_rows P R B _ _ _ _ HT
      RT' RF') as [HX HY].
    split.
    + assert (Heq: 2*H+15+2*(H-1+k)=4*H+2*k+13) by lia.
      rewrite Heq in HX. exact HX.
    + assert (Heq: 2*H+15+2*(H-1+k)+1=4*H+2*k+14) by lia.
      rewrite Heq in HY. exact HY.
Qed.

Definition k4_base_runs : list nat :=
  [1; 2; 6; 12; 24; 48; 96; 191; 2; 1; 381; 1; 11].

Definition k4_base_bits : list bool := k4_bits true k4_base_runs.

Definition k4_prebase_runs : list nat :=
  [1; 2; 6; 12; 24; 48; 96; 191; 2; 1].

Definition k4_prebase_bits : list bool := k4_bits false k4_prebase_runs.

Lemma k4_prebase_head_bits: K4HeadBits K4T2 k4_prebase_bits.
Proof. vm_compute. auto. Qed.

Lemma k4_base_shape:
  K4RunShape K4T4 k4_base_runs 775 11 753 6.
Proof.
  unfold K4RunShape, k4_base_runs, k4_run_count.
  cbn. repeat split; repeat constructor; lia.
Qed.

Lemma k4_base_head:
  hd 0 k4_base_runs=1.
Proof. reflexivity. Qed.

Lemma k4_base_pointer_facts:
  (nth 0 k4_base_bits false=true \/ nth 1 k4_base_bits false=true) /\
  k4_rdrops k4_base_bits (775-6+4)=6.
Proof. vm_compute. auto. Qed.

Lemma k4_base_head_bits: K4HeadBits K4T4 k4_base_bits.
Proof. vm_compute. auto. Qed.

Lemma k4_base_boundary_bits:
  length k4_base_bits=776 /\
  nth 775 k4_base_bits false=true /\
  nth 774 k4_base_bits false=true /\
  (forall z, 748<=z<=756 -> nth z k4_base_bits false=true).
Proof.
  repeat split; try vm_compute; try reflexivity.
  intros z Hz.
  replace z with (748+(z-748)) by lia.
  set (n:=z-748).
  assert (n<=8) by (unfold n; lia).
  do 9 (destruct n as [|n]; [reflexivity|]).
  lia.
Qed.

(* Common endpoint of the unbounded scan.  At weight [2*H-1] the zero row is
   exactly the false part of the next word.  The following true row is zero
   except for its right endpoint, and in a T2 phase also for the penultimate
   dent.  These are inclusions only. *)
Definition K4EndFan (P: nat -> nat -> nat -> nat -> Prop)
    (kind: K4Kind) (B: list bool) (H S D: nat) : Prop :=
  H=2*S+D /\
  K4ExactRow P B false (2*H-1) 0 (2*H+3) /\
  (kind=K4T2 -> P 0 (2*H-1) 0 (2*H+3)) /\
  (forall a b, a < length B -> nth a B false=true -> a<>H ->
    (kind=K4T2 -> a<>H-1) -> 2*a+b=2*H ->
    P a b 0 (2*H+4)) /\
  P H 0 (D+3) (4*S-2) /\
  (kind=K4T2 -> P (H-1) 0 (D+4) (4*S-6)) /\
  (kind=K4T2 -> P (D+4) (4*S-10) 0 (2*H+2)).

Inductive K4Mode := K4Low2 | K4Low8 | K4Low0 | K4Low4.

Definition k4_mode_lov3_c (mode: K4Mode) (n: nat) : nat :=
  match mode with
  | K4Low2 => n+3
  | K4Low8 => n
  | K4Low0 => n+4
  | K4Low4 => n+2
  end.

Definition k4_mode_lov4_c (mode: K4Mode) (n: nat) : nat :=
  match mode with
  | K4Low2 => n+2
  | K4Low8 => n
  | K4Low0 => n+3
  | K4Low4 => n+1
  end.

Definition k4_mode_d (mode: K4Mode) : nat :=
  match mode with K4Low2 => 2 | K4Low8 => 8 | K4Low0 => 0 | K4Low4 => 4 end.

Definition k4_mode_lov4_input (mode: K4Mode) (n: nat) : nat :=
  match mode with K4Low8 => (1+n)*2 | _ => n*2 end.

Record K4ComplexRules (P: nat -> nat -> nat -> nat -> Prop)
    (mode: K4Mode) := {
  k4c_simple: K4SimpleRules P;
  k4c_inc00_0: mode=K4Low0 -> forall a b c,
    P a b (1+c) 0 -> P a (2+b) c 4;
  k4c_lov1': forall a b c d n,
    P a b c (4+d) -> P c d 0 (n*2) -> P a (3+b) (1+n) 1;
  k4c_lov3: forall a b c d n,
    P a b c (4+d) -> P c d 0 (3+n*2) ->
    P a (5+b) (k4_mode_lov3_c mode n) (k4_mode_d mode);
  k4c_lov4: forall a b c d c' d' n,
    P a b c (5+d) -> P c d c' (4+d') ->
    P c' d' 0 (k4_mode_lov4_input mode n) ->
    P a (5+b) (k4_mode_lov4_c mode n) (k4_mode_d mode);
  k4c_lov5: forall a b c d c' d' c'' d'' n,
    P a b c (5+d) -> P c d c' (5+d') ->
    P c' d' c'' (4+d'') -> P c'' d'' 0 (1+n*2) ->
    P a (5+b) (k4_mode_lov3_c mode n) (k4_mode_d mode)
}.

Arguments k4c_simple {P mode} _.
Arguments k4c_inc00_0 {P mode} _ _ _ _ _ _.
Arguments k4c_lov1' {P mode} _ _ _ _ _ _ _ _.
Arguments k4c_lov3 {P mode} _ _ _ _ _ _ _ _.
Arguments k4c_lov4 {P mode} _ _ _ _ _ _ _ _ _ _ _.
Arguments k4c_lov5 {P mode} _ _ _ _ _ _ _ _ _ _ _ _ _.

Section K4Low2Boundary.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable C: K4ComplexRules P K4Low2.

Lemma k4_low2_end_t2_front B H S D:
  3 <= S -> length B=H+1 ->
  nth 0 B false=false -> nth H B false=true ->
  nth (D+1) B false=true -> nth (D+2) B false=true ->
  nth (D+3) B false=true ->
  K4EndFan P K4T2 B H S D ->
  K4Type2Front P B H S D.
Proof.
  intros HS Hlen HB0 HBH HD1 HD2 HD3
    [Hhs [RF [Z [RT [EH [EHm1 ED4]]]]]].
  specialize (Z eq_refl).
  pose (R:=k4c_simple C).
  destruct RF as [HRFw RF].
  assert (FR: K4ExactRow P B false (2*H+6) (H+1) 8).
  { split; try lia. intros a b Hal Hab Haw.
    assert (Han: a<>H) by (intros ->; congruence).
    assert (7<=b) by lia.
    applys_eq (k4_inc00_2 R a (b-2) (H+1)); try lia.
    applys_eq (k4c_lov3 C a (b-7) 0 (2*H-1) H); cbn; try lia.
    - applys_eq (RF a (b-7)); try assumption; lia.
    - applys_eq Z; lia. }
  assert (TZ: forall a b, a < length B -> nth a B false=true ->
      a<>H -> a<>H-1 -> 2*a+b=2*H -> P a b 0 (2*H+4)).
  { intros. apply RT; try assumption. intros; assumption. }
  assert (T1: P (D+1) (4*S-2) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (T2: P (D+2) (4*S-4) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (T3: P (D+3) (4*S-6) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (C1: P (H+1) 0 (D+2) (4*S+2)).
  { applys_eq (k4_inc01 R H (D+2) (4*S-2)); try lia.
    applys_eq EH; lia. }
  assert (C2: P (H+2) 0 (D+1) (4*S+6)).
  { applys_eq (k4_inc01 R (H+1) (D+1) (4*S+2)); try lia.
    applys_eq C1; lia. }
  assert (C3: P (H+3) 0 D (4*S+10)).
  { applys_eq (k4_inc01 R (H+2) D (4*S+6)); try lia.
    applys_eq C2; lia. }
  assert (L1: P (D+1) (4*S+1) (H+3) 1).
  { applys_eq (k4_lov2 R (D+1) (4*S-2) 0 (2*H-1)
      0 (2*H-1) (H+1)); try lia.
    - applys_eq T1; lia.
    - applys_eq Z; lia.
    - applys_eq Z; lia. }
  assert (I1: P (D+1) (4*S+3) (H+2) 5).
  { applys_eq (k4_inc00_1 R (D+1) (4*S+1) (H+2)); try lia.
    applys_eq L1; lia. }
  assert (E2: P (H+2) 2 (H+2) 6).
  { applys_eq (k4_rov R (H+2) 0 (D+1) (4*S+3) (H+2) 5);
      try lia.
    - applys_eq C2; lia.
    - applys_eq I1; lia. }
  assert (L2: P (D+2) (4*S-1) (H+3) 1).
  { applys_eq (k4_lov2 R (D+2) (4*S-4) 0 (2*H-1)
      0 (2*H-1) (H+1)); try lia.
    - applys_eq T2; lia.
    - applys_eq Z; lia.
    - applys_eq Z; lia. }
  assert (Q1: P (H+1) 2 (H+3) 2).
  { applys_eq (k4_rov R (H+1) 0 (D+2) (4*S-1) (H+3) 1);
      try lia.
    - applys_eq C1; lia.
    - applys_eq L2; lia. }
  assert (E1: P (H+1) 4 (H+1) 8).
  { applys_eq (k4_inc00_2 R (H+1) 2 (H+1)); try lia.
    applys_eq Q1; lia. }
  assert (LH: P H 3 (H+3) 1).
  { applys_eq (k4c_lov1' C H 0 (D+3) (4*S-6) (H+2)); try lia.
    - applys_eq EH; lia.
    - applys_eq T3; lia. }
  assert (IH: P H 5 (H+2) 5).
  { applys_eq (k4_inc00_1 R H 3 (H+2)); try lia.
    applys_eq LH; lia. }
  assert (TH: P H 7 (H+2) 7).
  { applys_eq (k4_rov R H 5 (H+2) 2 (H+2) 6); try lia.
    - applys_eq IH; lia.
    - applys_eq E2; lia. }
  assert (LD: P (H-1) 3 (H+2) 1).
  { applys_eq (k4c_lov1' C (H-1) 0 (D+4) (4*S-10) (H+1));
      try lia.
    - applys_eq (EHm1 eq_refl); lia.
    - applys_eq (ED4 eq_refl); lia. }
  assert (ID: P (H-1) 5 (H+1) 5).
  { applys_eq (k4_inc00_1 R (H-1) 3 (H+1)); try lia.
    applys_eq LD; lia. }
  assert (QD: P (H-1) 7 (H+3) 3).
  { applys_eq (k4_rov R (H-1) 5 (H+1) 2 (H+3) 2); try lia.
    - applys_eq ID; lia.
    - applys_eq Q1; lia. }
  assert (Dent: P (H-1) 9 D (4*S+11)).
  { applys_eq (k4_rov R (H-1) 7 (H+3) 0 D (4*S+10)); try lia.
    - applys_eq QD; lia.
    - applys_eq C3; lia. }
  assert (TR: K4RowExcept P B true (H-1) (2*H+7) (H+2)).
  { exists 7. split; try lia. intros a b Hal Han Hab Haw.
    destruct (Nat.eq_dec a H) as [->|HaH]; [applys_eq TH; lia|].
    assert (7<=b) by lia.
    applys_eq (k4_rov R a (b-2) (H+2) 2 (H+2) 6); try lia.
    - applys_eq (k4_inc00_1 R a (b-4) (H+2)); try lia.
      applys_eq (k4_lov2 R a (b-7) 0 (2*H-1)
        0 (2*H-1) (H+1)); try lia.
      + applys_eq (TZ a (b-7)); try assumption; lia.
      + applys_eq Z; lia.
      + applys_eq Z; lia.
    - exact E2. }
  repeat split; try assumption.
  exists 8. exact FR.
Qed.

Lemma k4_low2_end_t4_front B H S D:
  3 <= S -> 2 <= D -> length B=H+1 ->
  nth 0 B false=true -> nth H B false=true ->
  nth (D-1) B false=true -> nth D B false=true ->
  nth (D+1) B false=true -> nth (D+2) B false=true ->
  nth (D+3) B false=true ->
  K4EndFan P K4T4 B H S D ->
  K4Type4Front P B H S D.
Proof.
  intros HS HD Hlen HB0 HBH HDm1 HD0 HD1 HD2 HD3
    [Hhs [RF [Z [RT [EH [_ _]]]]]].
  pose (R:=k4c_simple C).
  destruct RF as [HRFw RF].
  assert (HH: 0 < H) by lia.
  assert (TZ: forall a b, a < length B -> nth a B false=true ->
      a<>H -> 2*a+b=2*H -> P a b 0 (2*H+4)).
  { intros. apply RT; try assumption. intros E. discriminate E. }
  assert (ZT: P 0 (2*H) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (TDm1: P (D-1) (4*S+2) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (TD0: P D (4*S) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (TD1: P (D+1) (4*S-2) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (TD2: P (D+2) (4*S-4) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (TD3: P (D+3) (4*S-6) 0 (2*H+4)).
  { apply TZ; try assumption; lia. }
  assert (C1: P (H+1) 0 (D+2) (4*S+2)).
  { applys_eq (k4_inc01 R H (D+2) (4*S-2)); try lia.
    applys_eq EH; lia. }
  assert (C2: P (H+2) 0 (D+1) (4*S+6)).
  { applys_eq (k4_inc01 R (H+1) (D+1) (4*S+2)); try lia.
    applys_eq C1; lia. }
  assert (C3: P (H+3) 0 D (4*S+10)).
  { applys_eq (k4_inc01 R (H+2) D (4*S+6)); try lia.
    applys_eq C2; lia. }
  assert (C4: P (H+4) 0 (D-1) (4*S+14)).
  { applys_eq (k4_inc01 R (H+3) (D-1) (4*S+10)); try lia.
    applys_eq C3; lia. }
  assert (C5: P (H+5) 0 (D-2) (4*S+18)).
  { applys_eq (k4_inc01 R (H+4) (D-2) (4*S+14)); try lia.
    applys_eq C4; lia. }
  assert (L1: P (D+1) (4*S+1) (H+3) 1).
  { applys_eq (k4c_lov1' C (D+1) (4*S-2) 0 (2*H) (H+2));
      try lia.
    - applys_eq TD1; lia.
    - applys_eq ZT; lia. }
  assert (I1: P (D+1) (4*S+3) (H+2) 5).
  { applys_eq (k4_inc00_1 R (D+1) (4*S+1) (H+2)); try lia.
    applys_eq L1; lia. }
  assert (E2: P (H+2) 2 (H+2) 6).
  { applys_eq (k4_rov R (H+2) 0 (D+1) (4*S+3) (H+2) 5);
      try lia.
    - applys_eq C2; lia.
    - applys_eq I1; lia. }
  assert (E2': P (H+2) 4 (H+1) 10).
  { applys_eq (k4_rov' R (H+2) 2 (H+2) 2 (H+1) 6); try lia.
    - applys_eq E2; lia.
    - applys_eq E2; lia. }
  assert (L2: P (D+2) (4*S-1) (H+3) 1).
  { applys_eq (k4c_lov1' C (D+2) (4*S-4) 0 (2*H) (H+2));
      try lia.
    - applys_eq TD2; lia.
    - applys_eq ZT; lia. }
  assert (Q1: P (H+1) 2 (H+3) 2).
  { applys_eq (k4_rov R (H+1) 0 (D+2) (4*S-1) (H+3) 1);
      try lia.
    - applys_eq C1; lia.
    - applys_eq L2; lia. }
  assert (E1: P (H+1) 4 (H+1) 8).
  { applys_eq (k4_inc00_2 R (H+1) 2 (H+1)); try lia.
    applys_eq Q1; lia. }
  assert (E1': P (H+1) 6 H 12).
  { applys_eq (k4_rov' R (H+1) 4 (H+1) 4 H 8); try lia.
    - applys_eq E1; lia.
    - applys_eq E1; lia. }
  assert (LH: P H 3 (H+3) 1).
  { applys_eq (k4c_lov1' C H 0 (D+3) (4*S-6) (H+2)); try lia.
    - applys_eq EH; lia.
    - applys_eq TD3; lia. }
  assert (IH: P H 5 (H+2) 5).
  { applys_eq (k4_inc00_1 R H 3 (H+2)); try lia.
    applys_eq LH; lia. }
  assert (QH: P H 7 (H+2) 7).
  { applys_eq (k4_rov R H 5 (H+2) 2 (H+2) 6); try lia.
    - applys_eq IH; lia.
    - applys_eq E2; lia. }
  assert (TH: P H 9 (H+1) 11).
  { applys_eq (k4_rov R H 7 (H+2) 4 (H+1) 10); try lia.
    - applys_eq QH; lia.
    - applys_eq E2'; lia. }
  assert (X1: P (H+1) 8 (H+1) 12).
  { applys_eq (k4_rov R (H+1) 6 H 9 (H+1) 11); try lia.
    - applys_eq E1'; lia.
    - applys_eq TH; lia. }
  assert (X2: P (H+2) 6 (H-1) 16).
  { applys_eq (k4_rov' R (H+2) 4 (H+1) 6 (H-1) 12); try lia.
    - applys_eq E2'; lia.
    - applys_eq E1'; lia. }
  assert (L0: P D (4*S+3) (H+3) 1).
  { applys_eq (k4c_lov1' C D (4*S) 0 (2*H) (H+2)); try lia.
    - applys_eq TD0; lia.
    - applys_eq ZT; lia. }
  assert (I0: P D (4*S+5) (H+2) 5).
  { applys_eq (k4_inc00_1 R D (4*S+3) (H+2)); try lia.
    applys_eq L0; lia. }
  assert (Q0: P D (4*S+7) (H+2) 7).
  { applys_eq (k4_rov R D (4*S+5) (H+2) 2 (H+2) 6); try lia.
    - applys_eq I0; lia.
    - applys_eq E2; lia. }
  assert (Q0': P D (4*S+9) (H+1) 11).
  { applys_eq (k4_rov R D (4*S+7) (H+2) 4 (H+1) 10); try lia.
    - applys_eq Q0; lia.
    - applys_eq E2'; lia. }
  assert (X3a: P (H+3) 2 (H+2) 8).
  { applys_eq (k4_rov R (H+3) 0 D (4*S+7) (H+2) 7); try lia.
    - applys_eq C3; lia.
    - applys_eq Q0; lia. }
  assert (X3: P (H+3) 4 H 14).
  { applys_eq (k4_rov' R (H+3) 2 (H+2) 4 H 10); try lia.
    - applys_eq X3a; lia.
    - applys_eq E2'; lia. }
  assert (Lm1: P (D-1) (4*S+5) (H+3) 1).
  { applys_eq (k4c_lov1' C (D-1) (4*S+2) 0 (2*H) (H+2));
      try lia.
    - applys_eq TDm1; lia.
    - applys_eq ZT; lia. }
  assert (Im1: P (D-1) (4*S+7) (H+2) 5).
  { applys_eq (k4_inc00_1 R (D-1) (4*S+5) (H+2)); try lia.
    applys_eq Lm1; lia. }
  assert (Qm1: P (D-1) (4*S+9) (H+2) 7).
  { applys_eq (k4_rov R (D-1) (4*S+7) (H+2) 2 (H+2) 6);
      try lia.
    - applys_eq Im1; lia.
    - applys_eq E2; lia. }
  assert (Qm1': P (D-1) (4*S+11) (H+1) 11).
  { applys_eq (k4_rov R (D-1) (4*S+9) (H+2) 4 (H+1) 10);
      try lia.
    - applys_eq Qm1; lia.
    - applys_eq E2'; lia. }
  assert (X4: P (H+4) 2 (H+1) 12).
  { applys_eq (k4_rov R (H+4) 0 (D-1) (4*S+11) (H+1) 11);
      try lia.
    - applys_eq C4; lia.
    - applys_eq Qm1'; lia. }
  assert (TR: K4ExactRow P B true (2*H+9) (H+1) 11).
  { split; try lia. intros a b Hal Hab Haw.
    destruct (Nat.eq_dec a H) as [->|HaH]; [applys_eq TH; lia|].
    assert (9<=b) by lia.
    assert (TZa: P a (b-9) 0 (2*H+4)).
    { apply TZ; try assumption; lia. }
    assert (La: P a (b-6) (H+3) 1).
    { applys_eq (k4c_lov1' C a (b-9) 0 (2*H) (H+2)); try lia.
      - applys_eq TZa; lia.
      - applys_eq ZT; lia. }
    assert (Ia: P a (b-4) (H+2) 5).
    { applys_eq (k4_inc00_1 R a (b-6) (H+2)); try lia.
      applys_eq La; lia. }
    assert (Qa: P a (b-2) (H+2) 7).
    { applys_eq (k4_rov R a (b-4) (H+2) 2 (H+2) 6); try lia.
      - applys_eq Ia; lia.
      - applys_eq E2; lia. }
    applys_eq (k4_rov R a (b-2) (H+2) 4 (H+1) 10); try lia.
    - applys_eq Qa; lia.
    - applys_eq E2'; lia. }
  assert (FR: K4ExactRow P B false (2*H+10) H 14).
  { split; try lia. intros a b Hal Hab Haw.
    assert (HaH: a<>H) by (intros ->; congruence).
    assert (11<=b) by lia.
    assert (Fa: P a (b-11) 0 (2*H+3)).
    { apply RF; try assumption; lia. }
    assert (Fa1: P a (b-9) 0 (2*H+5)).
    { applys_eq (k4_rov R a (b-11) 0 (2*H) 0 (2*H+4)); try lia.
      - applys_eq Fa; lia.
      - applys_eq ZT; lia. }
    assert (Fa2: P a (b-4) (H+4) 2).
    { applys_eq (k4c_lov4 C a (b-9) 0 (2*H) 0 (2*H)
          (H+2)); cbn; try lia.
      - applys_eq Fa1; lia.
      - applys_eq ZT; lia.
      - applys_eq ZT; lia. }
    assert (Fa3: P a (b-2) (H+2) 8).
    { applys_eq (k4_inc00_2 R a (b-4) (H+2)); try lia.
      applys_eq Fa2; lia. }
    applys_eq (k4_rov' R a (b-2) (H+2) 4 H 10); try lia.
    - applys_eq Fa3; lia.
    - applys_eq E2'; lia. }
  unfold K4Type4Front.
  repeat split.
  - exact Hhs.
  - exists 11. exact TR.
  - exists 14. exact FR.
  - exact X1.
  - exact X2.
  - exact X3.
  - exact X4.
  - exact C5.
Qed.

End K4Low2Boundary.
