Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K5Common
  BusyCoq.CounterClass1.CounterClass1K4FiniteN.
Require Import NArith ZArith Bool Lia List.
From BusyCoq Require Import LibTactics.

Open Scope N_scope.
Import ListNotations.

Definition k5n_c_rst01 (a b:N) : option K4NResult :=
  if (a=?1) && (b=?0) then Some (0,7) else None.

Definition k5n_c_rst0 (a b:N) : option K4NResult :=
  if (a=?0) && (b=?1) then Some (0,6) else None.

Definition k5n_c_inc01 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub a 1 with
  | Some a' => if b=?0 then
      match k4n_get t a' 0 with
      | Some (c0,d) => match k4n_sub c0 1 with
                       | Some c => Some (c,4+d) | None => None end
      | None => None end
    else None
  | None => None end.

Definition k5n_c_rov (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 4 with
      | Some d0' => match k4n_get t c0 d0' with
                    | Some (c,d) => Some (c,1+d) | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_rov' (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 5 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c0',d) => match k4n_sub c0' 1 with
                          | Some c => Some (c,4+d) | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov1 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub a 3 with
  | Some a' => if b=?0 then match k4n_get t a' 0 with
    | Some (c,z0) => if c=?0 then match k4n_sub z0 3 with
      | Some z => if N.even z then Some (N.div2 z,9) else None
      | None => None end else None
    | None => None end else None
  | None => None end.

Definition k5n_c_lov2 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub a 1 with
  | Some a' => if b=?3 then match k4n_get t a' 0 with
    | Some (c,z0) => if c=?0 then match k4n_sub z0 1 with
      | Some z => if N.even z then Some (N.div2 z,6) else None
      | None => None end else None
    | None => None end else None
  | None => None end.

Definition k5n_c_lov2' (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 5 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c,z0) => if c=?0 then match k4n_sub z0 1 with
          | Some z => if N.even z then Some (N.div2 z,6) else None
          | None => None end else None
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov3 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub a 2 with
  | Some a' => if b=?2 then match k4n_get t a' 0 with
    | Some (c,z0) => if c=?0 then match k4n_sub z0 3 with
      | Some z => if N.even z then Some (N.div2 z,9) else None
      | None => None end else None
    | None => None end else None
  | None => None end.

Definition k5n_c_lov3' (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 4 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 7 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 5 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c,z0) => if c=?0 then match k4n_sub z0 3 with
              | Some z => if N.even z then Some (N.div2 z,9) else None
              | None => None end else None
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov5 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 7 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 5 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c,z) => if (c=?0) && N.even z
                        then Some (1+N.div2 z,5) else None
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov4 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 6 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 5 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c,z) => if (c=?0) && N.even z
                            then Some (N.div2 z,6) else None
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov6 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 7 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 6 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 5 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c,z0) => if c=?0 then match k4n_sub z0 1 with
              | Some z => if N.even z then Some (2+N.div2 z,5) else None
              | None => None end else None
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov7 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 8 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 5 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c,z0) => if c=?0 then match k4n_sub z0 3 with
              | Some z => if N.even z then Some (N.div2 z,8) else None
              | None => None end else None
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov8 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 4 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 7 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 6 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c2,d2) => match k4n_sub d2 5 with
              | Some d2' => match k4n_get t c2 d2' with
                | Some (c,z0) => if c=?0 then match k4n_sub z0 2 with
                  | Some z => if N.even z then Some (N.div2 z,9) else None
                  | None => None end else None
                | None => None end
              | None => None end
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_c_lov9 (t:K4NTable) (a b:N) : option K4NResult :=
  match k4n_sub b 4 with
  | Some b' => match k4n_get t a b' with
    | Some (c0,d0) => match k4n_sub d0 6 with
      | Some d0' => match k4n_get t c0 d0' with
        | Some (c1,d1) => match k4n_sub d1 7 with
          | Some d1' => match k4n_get t c1 d1' with
            | Some (c2,d2) => match k4n_sub d2 6 with
              | Some d2' => match k4n_get t c2 d2' with
                | Some (c3,d3) => match k4n_sub d3 5 with
                  | Some d3' => match k4n_get t c3 d3' with
                    | Some (c,z) => if (c=?0) && N.even z then
                        match k4n_get t (1+N.div2 z) 0 with
                        | Some (cf,df) => Some (cf,1+df) | None => None end
                      else None
                    | None => None end
                  | None => None end
                | None => None end
              | None => None end
            | None => None end
          | None => None end
        | None => None end
      | None => None end
    | None => None end
  | None => None end.

Definition k5n_cell (t:K4NTable) (a b:N) : option K4NResult :=
  k4n_or_else (k5n_c_rst01 a b) (k4n_or_else (k5n_c_rst0 a b)
  (k4n_or_else (k5n_c_inc01 t a b) (k4n_or_else (k5n_c_rov t a b)
  (k4n_or_else (k5n_c_rov' t a b) (k4n_or_else (k5n_c_lov1 t a b)
  (k4n_or_else (k5n_c_lov2 t a b) (k4n_or_else (k5n_c_lov2' t a b)
  (k4n_or_else (k5n_c_lov3 t a b) (k4n_or_else (k5n_c_lov3' t a b)
  (k4n_or_else (k5n_c_lov5 t a b) (k4n_or_else (k5n_c_lov4 t a b)
  (k4n_or_else (k5n_c_lov6 t a b) (k4n_or_else (k5n_c_lov7 t a b)
  (k4n_or_else (k5n_c_lov8 t a b) (k5n_c_lov9 t a b))))))))))))))).

Lemma k5n_sub_nat x k y:
  k4n_sub x k=Some y ->
  N.to_nat x=(N.to_nat k+N.to_nat y)%nat.
Proof.
  intros H. pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ H)) as E.
  rewrite N2Nat.inj_add in E. exact E.
Qed.

Section K5NSound.

Variable P:nat->nat->nat->nat->Prop.
Variable R:K5Rules P.
Variable t:K4NTable.
Variable Ht:K4NTableSound P t.

Lemma k5n_c_rst01_sound a b c d:
  k5n_c_rst01 a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_rst01. destruct ((a=?1)&&(b=?0)) eqn:E; intros H;
    try discriminate. inverts H. rewrite Bool.andb_true_iff,!N.eqb_eq in E.
  destruct E as [-> ->]. exact (k5_rst01 P R).
Qed.

Lemma k5n_c_rst0_sound a b c d:
  k5n_c_rst0 a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_rst0. destruct ((a=?0)&&(b=?1)) eqn:E; intros H;
    try discriminate. inverts H. rewrite Bool.andb_true_iff,!N.eqb_eq in E.
  destruct E as [-> ->]. exact (k5_rst0 P R).
Qed.

Lemma k5n_c_inc01_sound a b c d:
  k5n_c_inc01 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_inc01.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?0) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub c0 1) as [c'|] eqn:Ec; intros H; try discriminate.
  inverts H. apply N.eqb_eq in Eb. subst b.
  pose proof (k5n_sub_nat _ _ _ Ea) as Ha.
  pose proof (k5n_sub_nat _ _ _ Ec) as Hc.
  change (N.to_nat a=(1+N.to_nat a')%nat) in Ha.
  change (N.to_nat c0=(1+N.to_nat c)%nat) in Hc.
  change (P (N.to_nat a) 0 (N.to_nat c)
    (N.to_nat (4+d0))). rewrite N2Nat.inj_add. cbn. rewrite Ha.
  apply (k5_inc01 R).
  change (P (N.to_nat a') 0 (S (N.to_nat c)) (N.to_nat d0)).
  replace (S (N.to_nat c)) with (N.to_nat c0) by lia.
  exact (Ht a' 0 c0 d0 E0).
Qed.

Lemma k5n_c_rov_sound a b c d:
  k5n_c_rov t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_rov.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c' d']|] eqn:E1;
    intros H; try discriminate. inverts H.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed) as Hd.
  change (P (N.to_nat a) (N.to_nat b) (N.to_nat c)
    (N.to_nat (1+d'))). rewrite N2Nat.inj_add. cbn in Hb,Hd|-*.
  applys_eq (k5_rov R (N.to_nat a) (N.to_nat b') (N.to_nat c0)
    (N.to_nat d0') (N.to_nat c) (N.to_nat d'));
    try lia; [applys_eq (Ht _ _ _ _ E0)|exact (Ht _ _ _ _ E1)]; lia.
Qed.

Lemma k5n_c_rov'_sound a b c d:
  k5n_c_rov' t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_rov'.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c0' d']|] eqn:E1;
    try discriminate.
  destruct (k4n_sub c0' 1) as [c'|] eqn:Ec; intros H; try discriminate.
  inverts H.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed) as Hd.
  pose proof (k5n_sub_nat _ _ _ Ec) as Hc.
  change (P (N.to_nat a) (N.to_nat b) (N.to_nat c)
    (N.to_nat (4+d'))). rewrite N2Nat.inj_add. cbn in Hb,Hd,Hc|-*.
  applys_eq (k5_rov' R (N.to_nat a) (N.to_nat b') (N.to_nat c0)
    (N.to_nat d0') (N.to_nat c) (N.to_nat d'));
    try lia; [applys_eq (Ht _ _ _ _ E0)|applys_eq (Ht _ _ _ _ E1)]; lia.
Qed.

Lemma k5n_c_lov1_sound a b c d:
  k5n_c_lov1 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov1.
  destruct (k4n_sub a 3) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?0) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 z0]|] eqn:E0; try discriminate.
  destruct (c0=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 3) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Eb,Ec. subst b c0.
  pose proof (k5n_sub_nat _ _ _ Ea) as Ha.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Ha,Hz|-*.
  applys_eq (k5_lov1 R (N.to_nat a') (Nat.div2 (N.to_nat z)));
    try lia. applys_eq (Ht a' 0 0 z0 E0); lia.
Qed.

Lemma k5n_c_lov2_sound a b c d:
  k5n_c_lov2 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov2.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?3) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 z0]|] eqn:E0; try discriminate.
  destruct (c0=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 1) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Eb,Ec. subst b c0.
  pose proof (k5n_sub_nat _ _ _ Ea) as Ha.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Ha,Hz|-*.
  applys_eq (k5_lov2 R (N.to_nat a') (Nat.div2 (N.to_nat z)));
    try lia. applys_eq (Ht a' 0 0 z0 E0); lia.
Qed.

Lemma k5n_c_lov2'_sound a b c d:
  k5n_c_lov2' t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov2'.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 z0]|] eqn:E1; try discriminate.
  destruct (c1=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 1) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c1.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed) as Hd.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Hb,Hd,Hz|-*.
  applys_eq (@k5_lov2' P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (Nat.div2 (N.to_nat z)));
    try lia; [applys_eq (Ht a b' c0 d0 E0)|
      applys_eq (Ht c0 d0' 0 z0 E1)]; lia.
Qed.

Lemma k5n_c_lov3_sound a b c d:
  k5n_c_lov3 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov3.
  destruct (k4n_sub a 2) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?2) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 z0]|] eqn:E0; try discriminate.
  destruct (c0=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 3) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Eb,Ec. subst b c0.
  pose proof (k5n_sub_nat _ _ _ Ea) as Ha.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Ha,Hz|-*.
  applys_eq (k5_lov3 R (N.to_nat a') (Nat.div2 (N.to_nat z)));
    try lia. applys_eq (Ht a' 0 0 z0 E0); lia.
Qed.

Lemma k5n_c_lov3'_sound a b c d:
  k5n_c_lov3' t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov3'.
  destruct (k4n_sub b 4) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 7) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 5) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z0]|] eqn:E2; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 3) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Hb,Hd0,Hd1,Hz|-*.
  applys_eq (@k5_lov3' P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z))); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' 0 z0 E2); lia.
Qed.

Lemma k5n_c_lov5_sound a b c d:
  k5n_c_lov5 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov5.
  destruct (k4n_sub b 7) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 z]|] eqn:E1; try discriminate.
  destruct ((c1=?0)&&N.even z) eqn:Ec; intros H; try discriminate.
  inverts H. rewrite Bool.andb_true_iff,N.eqb_eq in Ec.
  destruct Ec as [-> He].
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed) as Hd.
  pose proof (k4n_even_div2 z He) as Heven.
  change (P (N.to_nat a) (N.to_nat b) (N.to_nat (1+N.div2 z)) 5).
  rewrite N2Nat.inj_add,N2Nat.inj_div2. cbn in Hb,Hd|-*.
  applys_eq (@k5_lov5 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (Nat.div2 (N.to_nat z)));
    try lia; [applys_eq (Ht a b' c0 d0 E0)|
      applys_eq (Ht c0 d0' 0 z E1)]; lia.
Qed.

Lemma k5n_c_lov4_sound a b c d:
  k5n_c_lov4 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov4.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 6) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 5) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z]|] eqn:E2; try discriminate.
  destruct ((c2=?0)&&N.even z) eqn:Ec; intros H; try discriminate.
  inverts H. rewrite Bool.andb_true_iff,N.eqb_eq in Ec.
  destruct Ec as [-> He].
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Hb,Hd0,Hd1|-*.
  applys_eq (@k5_lov4 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z))); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' 0 z E2); lia.
Qed.

Lemma k5n_c_lov6_sound a b c d:
  k5n_c_lov6 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov6.
  destruct (k4n_sub b 7) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 6) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 5) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z0]|] eqn:E2; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 1) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  change (P (N.to_nat a) (N.to_nat b) (N.to_nat (2+N.div2 z)) 5).
  rewrite N2Nat.inj_add,N2Nat.inj_div2. cbn in Hb,Hd0,Hd1,Hz|-*.
  applys_eq (@k5_lov6 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z))); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' 0 z0 E2); lia.
Qed.

Lemma k5n_c_lov7_sound a b c d:
  k5n_c_lov7 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov7.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 8) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 5) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z0]|] eqn:E2; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 3) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Hb,Hd0,Hd1,Hz|-*.
  applys_eq (@k5_lov7 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z))); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' 0 z0 E2); lia.
Qed.

Lemma k5n_c_lov8_sound a b c d:
  k5n_c_lov8 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov8.
  destruct (k4n_sub b 4) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 7) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 6) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 d2]|] eqn:E2; try discriminate.
  destruct (k4n_sub d2 5) as [d2'|] eqn:Ed2; try discriminate.
  destruct (k4n_get t c2 d2') as [[c3 z0]|] eqn:E3; try discriminate.
  destruct (c3=?0) eqn:Ec; try discriminate.
  destruct (k4n_sub z0 2) as [z|] eqn:Ez; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c3.
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k5n_sub_nat _ _ _ Ed2) as Hd2.
  pose proof (k5n_sub_nat _ _ _ Ez) as Hz.
  pose proof (k4n_even_div2 z He) as Heven.
  rewrite N2Nat.inj_div2. cbn in Hb,Hd0,Hd1,Hd2,Hz|-*.
  applys_eq (@k5_lov8 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (N.to_nat c2) (N.to_nat d2') (Nat.div2 (N.to_nat z))); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' c2 d2 E2); lia.
  - applys_eq (Ht c2 d2' 0 z0 E3); lia.
Qed.

Lemma k5n_c_lov9_sound a b c d:
  k5n_c_lov9 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_c_lov9.
  destruct (k4n_sub b 4) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 6) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 7) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 d2]|] eqn:E2; try discriminate.
  destruct (k4n_sub d2 6) as [d2'|] eqn:Ed2; try discriminate.
  destruct (k4n_get t c2 d2') as [[c3 d3]|] eqn:E3; try discriminate.
  destruct (k4n_sub d3 5) as [d3'|] eqn:Ed3; try discriminate.
  destruct (k4n_get t c3 d3') as [[c4 z]|] eqn:E4; try discriminate.
  destruct ((c4=?0)&&N.even z) eqn:Ec; try discriminate.
  destruct (k4n_get t (1+N.div2 z) 0) as [[cf df]|] eqn:E5;
    intros H; try discriminate. inverts H.
  rewrite Bool.andb_true_iff,N.eqb_eq in Ec. destruct Ec as [-> He].
  pose proof (k5n_sub_nat _ _ _ Eb) as Hb.
  pose proof (k5n_sub_nat _ _ _ Ed0) as Hd0.
  pose proof (k5n_sub_nat _ _ _ Ed1) as Hd1.
  pose proof (k5n_sub_nat _ _ _ Ed2) as Hd2.
  pose proof (k5n_sub_nat _ _ _ Ed3) as Hd3.
  pose proof (k4n_even_div2 z He) as Heven.
  change (P (N.to_nat a) (N.to_nat b) (N.to_nat c)
    (N.to_nat (1+df))).
  rewrite N2Nat.inj_add. cbn in Hb,Hd0,Hd1,Hd2,Hd3|-*.
  applys_eq (@k5_lov9 P R (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (N.to_nat c2) (N.to_nat d2') (N.to_nat c3) (N.to_nat d3')
    (Nat.div2 (N.to_nat z)) (N.to_nat c) (N.to_nat df)); try lia.
  - applys_eq (Ht a b' c0 d0 E0); lia.
  - applys_eq (Ht c0 d0' c1 d1 E1); lia.
  - applys_eq (Ht c1 d1' c2 d2 E2); lia.
  - applys_eq (Ht c2 d2' c3 d3 E3); lia.
  - applys_eq (Ht c3 d3' 0 z E4); lia.
  - pose proof (Ht (1+N.div2 z) 0 c df E5) as HP.
    rewrite N2Nat.inj_add,N2Nat.inj_div2 in HP. cbn in HP. exact HP.
Qed.

Lemma k5n_cell_sound a b c d:
  k5n_cell t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k5n_cell,k4n_or_else.
  destruct (k5n_c_rst01 a b) as [[x y]|] eqn:E0.
  { intros H; inverts H. eapply k5n_c_rst01_sound; eauto. }
  destruct (k5n_c_rst0 a b) as [[x y]|] eqn:E1.
  { intros H; inverts H. eapply k5n_c_rst0_sound; eauto. }
  destruct (k5n_c_inc01 t a b) as [[x y]|] eqn:E2.
  { intros H; inverts H. eapply k5n_c_inc01_sound; eauto. }
  destruct (k5n_c_rov t a b) as [[x y]|] eqn:E3.
  { intros H; inverts H. eapply k5n_c_rov_sound; eauto. }
  destruct (k5n_c_rov' t a b) as [[x y]|] eqn:E4.
  { intros H; inverts H. eapply k5n_c_rov'_sound; eauto. }
  destruct (k5n_c_lov1 t a b) as [[x y]|] eqn:E5.
  { intros H; inverts H. eapply k5n_c_lov1_sound; eauto. }
  destruct (k5n_c_lov2 t a b) as [[x y]|] eqn:E6.
  { intros H; inverts H. eapply k5n_c_lov2_sound; eauto. }
  destruct (k5n_c_lov2' t a b) as [[x y]|] eqn:E7.
  { intros H; inverts H. eapply k5n_c_lov2'_sound; eauto. }
  destruct (k5n_c_lov3 t a b) as [[x y]|] eqn:E8.
  { intros H; inverts H. eapply k5n_c_lov3_sound; eauto. }
  destruct (k5n_c_lov3' t a b) as [[x y]|] eqn:E9.
  { intros H; inverts H. eapply k5n_c_lov3'_sound; eauto. }
  destruct (k5n_c_lov5 t a b) as [[x y]|] eqn:E10.
  { intros H; inverts H. eapply k5n_c_lov5_sound; eauto. }
  destruct (k5n_c_lov4 t a b) as [[x y]|] eqn:E11.
  { intros H; inverts H. eapply k5n_c_lov4_sound; eauto. }
  destruct (k5n_c_lov6 t a b) as [[x y]|] eqn:E12.
  { intros H; inverts H. eapply k5n_c_lov6_sound; eauto. }
  destruct (k5n_c_lov7 t a b) as [[x y]|] eqn:E13.
  { intros H; inverts H. eapply k5n_c_lov7_sound; eauto. }
  destruct (k5n_c_lov8 t a b) as [[x y]|] eqn:E14.
  { intros H; inverts H. eapply k5n_c_lov8_sound; eauto. }
  eapply k5n_c_lov9_sound; eauto.
Qed.

End K5NSound.

Definition k5n_layer_step (src:K4NTable) (w:N)
    (s:N*K4NTable) : N*K4NTable :=
  let '(a,out):=s in
  let b:=w-2*a in
  let out':=match k5n_cell src a b with
    | Some v => K4NMap.hmap_set (a,b) v out
    | None => out end in
  (N.succ a,out').

Definition k5n_make_layer (src:K4NTable) (w:N) : K4NTable :=
  snd (N.iter (N.succ (N.div2 w)) (k5n_layer_step src w) (0,src)).

Definition k5n_build_step (s:N*K4NTable) : N*K4NTable :=
  let '(w,t):=s in (N.succ w,k5n_make_layer t w).

Definition k5n_table_size:Uint63.int :=
  Eval compute in Uint63.of_Z (Z.of_N 32767).

Definition k5n_build (last:N) : K4NTable :=
  snd (N.iter (N.succ last) k5n_build_step
    (0,K4NMap.hmap_make k5n_table_size)).

Lemma k5n_layer_step_sound P (R:K5Rules P) src w s:
  K4NTableSound P src -> K4NTableOK P (snd s) ->
  K4NTableOK P (snd (k5n_layer_step src w s)).
Proof.
  intros Hsrc Hout. destruct s as [a out]. cbn [k5n_layer_step] in *.
  destruct (k5n_cell src a (w-2*a)) as [[c d]|] eqn:E; [|exact Hout].
  eapply k4n_set_sound; [exact Hout|].
  exact (k5n_cell_sound P R src Hsrc _ _ _ _ E).
Qed.

Lemma k5n_make_layer_sound P (R:K5Rules P) src w:
  K4NTableOK P src -> K4NTableOK P (k5n_make_layer src w).
Proof.
  intros Hsrc. unfold k5n_make_layer.
  eapply (k4n_iter_preserve (fun s => K4NTableOK P (snd s)));
    [exact Hsrc|].
  intros s Hs. eapply k5n_layer_step_sound; eauto. exact (proj2 Hsrc).
Qed.

Lemma k5n_build_step_sound P (R:K5Rules P) s:
  K4NTableOK P (snd s) -> K4NTableOK P (snd (k5n_build_step s)).
Proof.
  destruct s as [w t]. cbn [k5n_build_step].
  intros H. exact (k5n_make_layer_sound P R t w H).
Qed.

Lemma k5n_make_sound P:
  K4NTableOK P (K4NMap.hmap_make k5n_table_size).
Proof.
  split.
  - apply K4NMap.hmap_make_WF.
  - intros a b c d H. unfold k4n_get in H.
    rewrite K4NMap.hmap_get_make in H. discriminate.
Qed.

Lemma k5n_build_sound P (R:K5Rules P) last:
  K4NTableOK P (k5n_build last).
Proof.
  unfold k5n_build.
  eapply (k4n_iter_preserve (fun s => K4NTableOK P (snd s))).
  - apply k5n_make_sound.
  - intros s Hs. exact (k5n_build_step_sound P R s Hs).
Qed.

Definition k5_base_runs:list nat :=
  [1%nat;2%nat;5%nat;10%nat;20%nat;39%nat;1%nat;8%nat].
Definition k5_base_bits:list bool := k4_bits false k5_base_runs.

Definition k5n_base_bit (a:N) : bool :=
  k4n_between 1 3 a || k4n_between 8 18 a ||
  k4n_between 38 77 a || k4n_between 78 86 a.

Definition k5n_base_row_test (t:K4NTable) (a:N) : bool :=
  if k5n_base_bit a
  then k4n_lookup_eqb t a (183-2*a) (85,18)
  else k4n_lookup_eqb t a (184-2*a) (85,19).

Definition k5n_base_tail_test (t:K4NTable) (j:N) : bool :=
  if j=?0 then k4n_lookup_eqb t 86 12 (85,19) else
  if j=?1 then k4n_lookup_eqb t 87 10 (84,21) else
  if j=?2 then k4n_lookup_eqb t 88 8 (84,21) else
  if j=?3 then k4n_lookup_eqb t 89 6 (85,19) else
  if j=?4 then k4n_lookup_eqb t 90 4 (84,21) else
  if j=?5 then k4n_lookup_eqb t 91 2 (85,19) else false.

Definition k5n_base_check (t:K4NTable) : bool :=
  let rows:=snd (N.iter 86 (k4n_check_step (k5n_base_row_test t))
    (0,true)) in
  if rows then
    let tails:=snd (N.iter 6 (k4n_check_step (k5n_base_tail_test t))
      (0,true)) in
    if tails then k4n_lookup_eqb t 92 0 (64,61) else false
  else false.

Definition k5n_base_184:=k5n_build 184.

Lemma k5n_base_bit_spec a:
  (a<86)%nat ->
  k5n_base_bit (N.of_nat a)=nth a k5_base_bits false.
Proof.
  intros H. unfold k5_base_bits.
  rewrite k4n_bits_nth by (unfold k5_base_runs; cbn; lia).
  unfold k5n_base_bit,k4n_between.
  change
    ((N.of_nat 1<=?N.of_nat a)&&(N.of_nat a<?N.of_nat 3)||
     (N.of_nat 8<=?N.of_nat a)&&(N.of_nat a<?N.of_nat 18)||
     (N.of_nat 38<=?N.of_nat a)&&(N.of_nat a<?N.of_nat 77)||
     (N.of_nat 78<=?N.of_nat a)&&(N.of_nat a<?N.of_nat 86)=
     k4n_bit_at false k5_base_runs a)%bool.
  rewrite !k4n_leb_of_nat,!k4n_ltb_of_nat.
  unfold k5_base_runs. repeat rewrite k4n_bit_at_cons.
  rewrite k4n_bit_at_nil.
  destruct (Nat.lt_ge_cases a 1); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 3); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 8); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 18); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 38); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 77); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 78); [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 86); k4n_bool_lia.
Qed.

Lemma k5n_base_check_sound P t:
  K4NTableSound P t -> k5n_base_check t=true ->
  K5ScanStart P K4T2 k5_base_runs k5_base_bits 85 8 69 3.
Proof.
  intros Ht Hcheck. unfold k5n_base_check in Hcheck.
  destruct (snd (N.iter 86 (k4n_check_step (k5n_base_row_test t))
    (0,true))) eqn:Hrows; try discriminate.
  destruct (snd (N.iter 6 (k4n_check_step (k5n_base_tail_test t))
    (0,true))) eqn:Htails; try discriminate.
  assert (HR:forall a, (a<86)%N -> k5n_base_row_test t a=true).
  { apply k4n_check_iter_true. exact Hrows. }
  assert (HT:forall j, (j<6)%N -> k5n_base_tail_test t j=true).
  { apply k4n_check_iter_true. exact Htails. }
  assert (Hlen:length k5_base_bits=86%nat) by
    (vm_compute; reflexivity).
  assert (Hrowt:K4ExactRow (K5Q P) k5_base_bits true 183 85 17).
  { split; [lia|]. intros a b Ha Hbit Hab.
    specialize (HR (N.of_nat a) ltac:(
      replace 86%N with (N.of_nat 86%nat) by reflexivity;
      apply k4n_of_nat_lt; lia)).
    unfold k5n_base_row_test in HR.
    rewrite k5n_base_bit_spec,Hbit in HR by exact Ha.
    pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht HR) as HP.
    rewrite Nat2N.id in HP.
    replace (N.to_nat 85) with 85%nat in HP by reflexivity.
    replace (N.to_nat 18) with 18%nat in HP by reflexivity.
    unfold K5Q. replace (N.to_nat (183-2*N.of_nat a)) with b in HP.
    - exact HP.
    - rewrite N2Nat.inj_sub,N2Nat.inj_mul,Nat2N.id.
      cbn. lia. }
  assert (Hrowf:K4ExactRow (K5Q P) k5_base_bits false 184 85 18).
  { split; [lia|]. intros a b Ha Hbit Hab.
    specialize (HR (N.of_nat a) ltac:(
      replace 86%N with (N.of_nat 86%nat) by reflexivity;
      apply k4n_of_nat_lt; lia)).
    unfold k5n_base_row_test in HR.
    rewrite k5n_base_bit_spec,Hbit in HR by exact Ha.
    pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht HR) as HP.
    rewrite Nat2N.id in HP.
    replace (N.to_nat 85) with 85%nat in HP by reflexivity.
    replace (N.to_nat 19) with 19%nat in HP by reflexivity.
    unfold K5Q. replace (N.to_nat (184-2*N.of_nat a)) with b in HP.
    - exact HP.
    - rewrite N2Nat.inj_sub,N2Nat.inj_mul,Nat2N.id.
      cbn. lia. }
  assert (Htail:K5Tail P 85).
  { assert (T0:=HT 0 ltac:(vm_compute; reflexivity)).
    assert (T1:=HT 1 ltac:(vm_compute; reflexivity)).
    assert (T2:=HT 2 ltac:(vm_compute; reflexivity)).
    assert (T3:=HT 3 ltac:(vm_compute; reflexivity)).
    assert (T4:=HT 4 ltac:(vm_compute; reflexivity)).
    assert (T5:=HT 5 ltac:(vm_compute; reflexivity)).
    cbn [k5n_base_tail_test] in T0,T1,T2,T3,T4,T5.
    unfold K5Tail. repeat split.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T0) as X;
        cbn in X; exact X.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T1) as X;
        cbn in X; exact X.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T2) as X;
        cbn in X; exact X.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T3) as X;
        cbn in X; exact X.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T4) as X;
        cbn in X; exact X.
    - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht T5) as X;
        cbn in X; exact X. }
  assert (Hend:P 92%nat 0%nat 64%nat 61%nat).
  { pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht Hcheck) as X.
    cbn in X. exact X. }
  unfold K5ScanStart. split.
  - unfold K5RunShape,k5_base_runs. cbn.
    repeat split; try (repeat constructor); lia.
  - split; [reflexivity|]. split; [reflexivity|].
    unfold K5ScanPayload. split.
    + vm_compute. auto.
    + split; [vm_compute; reflexivity|].
      split; [exact Hrowt|]. split; [exact Hrowf|].
      split; assumption.
Qed.

Lemma k5n_base_184_check:k5n_base_check k5n_base_184=true.
Proof. native_compute. reflexivity. Qed.

Lemma k5n_base_start P (R:K5Rules P):
  K5ScanStart P K4T2 k5_base_runs k5_base_bits 85 8 69 3.
Proof.
  apply (k5n_base_check_sound P k5n_base_184).
  - exact (proj2 (k5n_build_sound P R 184)).
  - exact k5n_base_184_check.
Qed.
