Require Import BusyCoq.CounterClass1.CounterClass1Common.
Require Import NArith ZArith Bool Lia List.
From BusyCoq Require Import HashTable.
From BusyCoq Require Import LibTactics.

Open Scope N_scope.

Module K4NKey <: HashableType.
  Definition K := N.
  Definition K_hash := HashConcat.N_hash.
  Definition K_eq := N.eqb.
  Lemma K_eq_spec a b: Bool.reflect (a=b) (K_eq a b).
  Proof. apply N.eqb_spec. Qed.
End K4NKey.

Module K4NPairKey := ProdHash K4NKey K4NKey.

Module K4NValue <: ValueType.
  Definition V := (N*N)%type.
End K4NValue.

Module K4NMap := HashMap K4NPairKey K4NValue.

Definition K4NTable := K4NMap.hmap_t.
Definition K4NResult := (N*N)%type.

Definition k4n_get (t: K4NTable) (a b: N) : option K4NResult :=
  K4NMap.hmap_get (a,b) t.

Definition K4NTableSound (P: nat -> nat -> nat -> nat -> Prop)
    (t: K4NTable) : Prop :=
  forall a b c d, k4n_get t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).

Definition k4n_sub (x k: N) : option N :=
  if (k <=? x)%N then Some (x-k) else None.

Lemma k4n_sub_some x k y:
  k4n_sub x k=Some y -> x=k+y.
Proof.
  unfold k4n_sub. destruct (k<=?x) eqn:E; intros H; try discriminate.
  inverts H. rewrite N.add_comm,N.sub_add; [reflexivity|].
  apply N.leb_le. exact E.
Qed.

Lemma k4n_even_div2 n:
  N.even n=true -> N.to_nat n=(Nat.div2 (N.to_nat n)*2)%nat.
Proof.
  intros H. apply N.even_spec in H as [m ->].
  rewrite N2Nat.inj_mul. cbn. rewrite Nat.div2_double. lia.
Qed.

Lemma k4n_odd_div2 n:
  N.odd n=true -> N.to_nat n=(1+Nat.div2 (N.to_nat n)*2)%nat.
Proof.
  intros H. apply N.odd_spec in H as [m ->].
  rewrite N2Nat.inj_add,N2Nat.inj_mul. cbn.
  replace (Pos.to_nat 2) with 2%nat by reflexivity.
  replace (Pos.to_nat 1) with 1%nat by reflexivity.
  assert ((2*N.to_nat m+1)%nat=S (2*N.to_nat m)) as E by lia.
  rewrite E.
  rewrite Nat.div2_succ_double. lia.
Qed.

Definition k4n_or_else {A} (x y: option A) : option A :=
  match x with Some v => Some v | None => y end.

Definition k4n_c_rst (a b: N) : option K4NResult :=
  if (a =? 0) && (b =? 1) then Some (0,5) else None.

Definition k4n_c_inc01 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub a 1 with
  | Some a' =>
      if b =? 0 then
        match k4n_get t a' 0 with
        | Some (c0,d0) =>
            match k4n_sub c0 1 with
            | Some c => Some (c,4+d0)
            | None => None
            end
        | None => None
        end
      else None
  | None => None
  end.

Definition k4n_c_inc1 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub a 1 with
  | Some a' =>
      if b =? 0 then
        match k4n_get t a' 1 with
        | Some (c,d) => Some (c,1+d)
        | None => None
        end
      else None
  | None => None
  end.

Definition k4n_c_inc00_1 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub c0 1 with
          | Some c => if d0 =? 1 then Some (c,5) else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_inc00_2 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub c0 2 with
          | Some c => if d0 =? 2 then Some (c,8) else None
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_rov (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 3 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c,d) => Some (c,1+d)
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_rov' (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 2 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 4 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c0',d) =>
                  match k4n_sub c0' 1 with
                  | Some c => Some (c,4+d)
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_lov1 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub a 1 with
  | Some a' =>
      if b =? 1 then
        match k4n_get t a' 0 with
        | Some (c,d) =>
            if c =? 0 then
              if N.even d then Some (1+N.div2 d,1) else None
            else None
        | None => None
        end
      else None
  | None => None
  end.

Definition k4n_c_lov1' (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 3 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 4 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c,d) =>
                  if c =? 0 then
                    if N.even d then Some (1+N.div2 d,1) else None
                  else None
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_lov2 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 3 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 5 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c1,d1) =>
                  match k4n_sub d1 4 with
                  | Some d1' =>
                      match k4n_get t c1 d1' with
                      | Some (c,z) =>
                          if c =? 0 then
                            if N.odd z then Some (2+N.div2 z,1) else None
                          else None
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_lov3 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 4 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c,z0) =>
                  match k4n_sub z0 3 with
                  | Some z =>
                      if c =? 0 then
                        if N.even z then Some (3+N.div2 z,2) else None
                      else None
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_lov4 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 5 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c1,d1) =>
                  match k4n_sub d1 4 with
                  | Some d1' =>
                      match k4n_get t c1 d1' with
                      | Some (c,z) =>
                          if c =? 0 then
                            if N.even z then Some (2+N.div2 z,2) else None
                          else None
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Definition k4n_c_lov5 (t: K4NTable) (a b: N) : option K4NResult :=
  match k4n_sub b 5 with
  | Some b' =>
      match k4n_get t a b' with
      | Some (c0,d0) =>
          match k4n_sub d0 5 with
          | Some d0' =>
              match k4n_get t c0 d0' with
              | Some (c1,d1) =>
                  match k4n_sub d1 5 with
                  | Some d1' =>
                      match k4n_get t c1 d1' with
                      | Some (c2,d2) =>
                          match k4n_sub d2 4 with
                          | Some d2' =>
                              match k4n_get t c2 d2' with
                              | Some (c,z) =>
                                  if c =? 0 then
                                    if N.odd z then Some (3+N.div2 z,2)
                                    else None
                                  else None
                              | None => None
                              end
                          | None => None
                          end
                      | None => None
                      end
                  | None => None
                  end
              | None => None
              end
          | None => None
          end
      | None => None
      end
  | None => None
  end.

Section K4NCommonSound.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable mode: K4Mode.
Variable C: K4ComplexRules P mode.
Let R := k4c_simple C.
Variable Hrst: P 0 1 0 5.
Variable t: K4NTable.
Variable Ht: K4NTableSound P t.

Lemma k4n_c_rst_sound a b c d:
  k4n_c_rst a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_rst. destruct (a=?0) eqn:Ea; [|discriminate].
  destruct (b=?1) eqn:Eb; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ea,Eb. subst. exact Hrst.
Qed.

Lemma k4n_c_inc01_sound a b c d:
  k4n_c_inc01 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_inc01.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?0) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub c0 1) as [c'|] eqn:Ec; intros H; try discriminate.
  inverts H. apply N.eqb_eq in Eb. subst b.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ea)) as Ha.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ec)) as Hc.
  rewrite !N2Nat.inj_add in Ha,Hc.
  pose proof (N2Nat.inj_add 4 d0) as Hdadd. cbn in Hdadd.
  rewrite Hdadd,Ha.
  apply (k4_inc01 R). applys_eq (Ht _ _ _ _ E0). lia.
Qed.

Lemma k4n_c_inc1_sound a b c d:
  k4n_c_inc1 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_inc1.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?0) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 1) as [[c0 d0]|] eqn:E0; intros H;
    try discriminate. inverts H. apply N.eqb_eq in Eb. subst b.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ea)) as Ha.
  rewrite N2Nat.inj_add in Ha.
  pose proof (N2Nat.inj_add 1 d0) as Hdadd. cbn in Hdadd.
  rewrite Hdadd,Ha. apply (k4_inc1 R). exact (Ht _ _ _ _ E0).
Qed.

Lemma k4n_c_inc00_1_sound a b c d:
  k4n_c_inc00_1 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_inc00_1.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub c0 1) as [c'|] eqn:Ec; try discriminate.
  destruct (d0=?1) eqn:Ed; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ed. subst d0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ec)) as Hc.
  rewrite !N2Nat.inj_add in Hb,Hc.
  rewrite Hb. apply (k4_inc00_1 R).
  applys_eq (Ht _ _ _ _ E0); lia.
Qed.

Lemma k4n_c_inc00_2_sound a b c d:
  k4n_c_inc00_2 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_inc00_2.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub c0 2) as [c'|] eqn:Ec; try discriminate.
  destruct (d0=?2) eqn:Ed; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ed. subst d0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ec)) as Hc.
  rewrite !N2Nat.inj_add in Hb,Hc.
  rewrite Hb. apply (k4_inc00_2 R).
  applys_eq (Ht _ _ _ _ E0); lia.
Qed.

Lemma k4n_c_rov_sound a b c d:
  k4n_c_rov t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_rov.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 3) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; intros H;
    try discriminate. inverts H.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed)) as Hd.
  rewrite !N2Nat.inj_add in Hb,Hd. cbn in Hb,Hd.
  change (N.to_nat d0=(3+N.to_nat d0')%nat) in Hd.
  pose proof (N2Nat.inj_add 1 d1) as Hdadd. cbn in Hdadd.
  rewrite Hb,Hdadd. eapply (k4_rov R).
  - rewrite <- Hd. exact (Ht _ _ _ _ E0).
  - exact (Ht _ _ _ _ E1).
Qed.

Lemma k4n_c_rov'_sound a b c d:
  k4n_c_rov' t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_rov'.
  destruct (k4n_sub b 2) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub c1 1) as [c'|] eqn:Ec; intros H; try discriminate.
  inverts H.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed)) as Hd.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ec)) as Hc.
  rewrite !N2Nat.inj_add in Hb,Hd,Hc. cbn in Hb,Hd,Hc.
  replace (Pos.to_nat 1) with 1%nat in Hc by reflexivity.
  change (N.to_nat d0=(4+N.to_nat d0')%nat) in Hd.
  pose proof (N2Nat.inj_add 4 d1) as Hdadd. cbn in Hdadd.
  rewrite Hb,Hdadd. eapply (k4_rov' R).
  - rewrite <- Hd. exact (Ht _ _ _ _ E0).
  - rewrite <- Hc. exact (Ht _ _ _ _ E1).
Qed.

Lemma k4n_c_lov1_sound a b c d:
  k4n_c_lov1 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov1.
  destruct (k4n_sub a 1) as [a'|] eqn:Ea; try discriminate.
  destruct (b=?1) eqn:Eb; try discriminate.
  destruct (k4n_get t a' 0) as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (c0=?0) eqn:Ec; try discriminate.
  destruct (N.even d0) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Eb,Ec. subst b c0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ea)) as Ha.
  rewrite N2Nat.inj_add in Ha. cbn in Ha.
  pose proof (N2Nat.inj_add 1 (N.div2 d0)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  rewrite Hout,Ha. apply (k4_lov1 R).
  rewrite <- (k4n_even_div2 d0 He). exact (Ht _ _ _ _ E0).
Qed.

Lemma k4n_c_lov1'_sound a b c d:
  k4n_c_lov1' t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov1'.
  destruct (k4n_sub b 3) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d0'|] eqn:Ed; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (c1=?0) eqn:Ec; try discriminate.
  destruct (N.even d1) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed)) as Hd.
  rewrite !N2Nat.inj_add in Hb,Hd. cbn in Hb,Hd.
  change (N.to_nat d0=(4+N.to_nat d0')%nat) in Hd.
  pose proof (N2Nat.inj_add 1 (N.div2 d1)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  rewrite Hb,Hout. eapply (k4c_lov1' C).
  - rewrite <- Hd. exact (Ht _ _ _ _ E0).
  - rewrite <- (k4n_even_div2 d1 He). exact (Ht _ _ _ _ E1).
Qed.

Lemma k4n_c_lov2_sound a b c d:
  k4n_c_lov2 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov2.
  destruct (k4n_sub b 3) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 4) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z]|] eqn:E2; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (N.odd z) eqn:Ho; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed0)) as Hd0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed1)) as Hd1.
  rewrite !N2Nat.inj_add in Hb,Hd0,Hd1. cbn in Hb,Hd0,Hd1.
  change (N.to_nat d0=(5+N.to_nat d0')%nat) in Hd0.
  change (N.to_nat d1=(4+N.to_nat d1')%nat) in Hd1.
  pose proof (N2Nat.inj_add 2 (N.div2 z)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  rewrite Hb,Hout. eapply (k4_lov2 R).
  - rewrite <- Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <- Hd1. exact (Ht _ _ _ _ E1).
  - rewrite <- (k4n_odd_div2 z Ho). exact (Ht _ _ _ _ E2).
Qed.

End K4NCommonSound.

Section K4NLow2Sound.

Variable P: nat -> nat -> nat -> nat -> Prop.
Variable C: K4ComplexRules P K4Low2.
Let R := k4c_simple C.
Variable Hrst: P 0 1 0 5.
Variable t: K4NTable.
Variable Ht: K4NTableSound P t.

Lemma k4n_c_lov3_sound a b c d:
  k4n_c_lov3 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov3.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 4) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 z0]|] eqn:E1; try discriminate.
  destruct (k4n_sub z0 3) as [z|] eqn:Ez; try discriminate.
  destruct (c1=?0) eqn:Ec; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed0)) as Hd0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ez)) as Hz.
  rewrite !N2Nat.inj_add in Hb,Hd0,Hz. cbn in Hb,Hd0,Hz.
  change (N.to_nat d0=(4+N.to_nat d0')%nat) in Hd0.
  change (N.to_nat z0=(3+N.to_nat z)%nat) in Hz.
  pose proof (N2Nat.inj_add 3 (N.div2 z)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  replace (Pos.to_nat 5) with 5%nat in Hb by reflexivity.
  replace (Pos.to_nat 3) with 3%nat in Hout by reflexivity.
  rewrite Hb,Hout. replace (N.to_nat 2) with 2%nat by reflexivity.
  applys_eq (k4c_lov3 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov3_c k4_mode_d]; try lia.
  - rewrite <- Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <- (k4n_even_div2 z He), <- Hz. exact (Ht _ _ _ _ E1).
Qed.

Lemma k4n_c_lov4_sound a b c d:
  k4n_c_lov4 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov4.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 4) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z]|] eqn:E2; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed0)) as Hd0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed1)) as Hd1.
  rewrite !N2Nat.inj_add in Hb,Hd0,Hd1. cbn in Hb,Hd0,Hd1.
  change (N.to_nat d0=(5+N.to_nat d0')%nat) in Hd0.
  change (N.to_nat d1=(4+N.to_nat d1')%nat) in Hd1.
  pose proof (N2Nat.inj_add 2 (N.div2 z)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  replace (Pos.to_nat 5) with 5%nat in Hb by reflexivity.
  replace (Pos.to_nat 2) with 2%nat in Hout by reflexivity.
  rewrite Hb,Hout. replace (N.to_nat 2) with 2%nat by reflexivity.
  applys_eq (k4c_lov4 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov4_c k4_mode_lov4_input k4_mode_d]; try lia.
  - rewrite <- Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <- Hd1. exact (Ht _ _ _ _ E1).
  - rewrite <- (k4n_even_div2 z He). exact (Ht _ _ _ _ E2).
Qed.

Lemma k4n_c_lov5_sound a b c d:
  k4n_c_lov5 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n_c_lov5.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 5) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 d2]|] eqn:E2; try discriminate.
  destruct (k4n_sub d2 4) as [d2'|] eqn:Ed2; try discriminate.
  destruct (k4n_get t c2 d2') as [[c3 z]|] eqn:E3; try discriminate.
  destruct (c3=?0) eqn:Ec; try discriminate.
  destruct (N.odd z) eqn:Ho; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c3.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed0)) as Hd0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed1)) as Hd1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed2)) as Hd2.
  rewrite !N2Nat.inj_add in Hb,Hd0,Hd1,Hd2. cbn in Hb,Hd0,Hd1,Hd2.
  change (N.to_nat d0=(5+N.to_nat d0')%nat) in Hd0.
  change (N.to_nat d1=(5+N.to_nat d1')%nat) in Hd1.
  change (N.to_nat d2=(4+N.to_nat d2')%nat) in Hd2.
  pose proof (N2Nat.inj_add 3 (N.div2 z)) as Hout.
  rewrite N2Nat.inj_div2 in Hout. cbn in Hout.
  replace (Pos.to_nat 5) with 5%nat in Hb by reflexivity.
  replace (Pos.to_nat 3) with 3%nat in Hout by reflexivity.
  rewrite Hb,Hout. replace (N.to_nat 2) with 2%nat by reflexivity.
  applys_eq (k4c_lov5 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (N.to_nat c2) (N.to_nat d2') (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov3_c k4_mode_d]; try lia.
  - rewrite <- Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <- Hd1. exact (Ht _ _ _ _ E1).
  - rewrite <- Hd2. exact (Ht _ _ _ _ E2).
  - rewrite <- (k4n_odd_div2 z Ho). exact (Ht _ _ _ _ E3).
Qed.

End K4NLow2Sound.

Definition k4n_cell (t: K4NTable) (a b: N) : option K4NResult :=
  k4n_or_else (k4n_c_rst a b)
  (k4n_or_else (k4n_c_inc01 t a b)
  (k4n_or_else (k4n_c_inc1 t a b)
  (k4n_or_else (k4n_c_inc00_1 t a b)
  (k4n_or_else (k4n_c_inc00_2 t a b)
  (k4n_or_else (k4n_c_rov t a b)
  (k4n_or_else (k4n_c_rov' t a b)
  (k4n_or_else (k4n_c_lov1 t a b)
  (k4n_or_else (k4n_c_lov1' t a b)
  (k4n_or_else (k4n_c_lov2 t a b)
  (k4n_or_else (k4n_c_lov3 t a b)
  (k4n_or_else (k4n_c_lov4 t a b)
                (k4n_c_lov5 t a b)))))))))))).

Lemma k4n_cell_sound (P: nat -> nat -> nat -> nat -> Prop)
    (C: K4ComplexRules P K4Low2)
    (Hrst: P 0%nat 1%nat 0%nat 5%nat) t:
  K4NTableSound P t -> forall a b c d,
  k4n_cell t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  intros Ht a b c d. unfold k4n_cell,k4n_or_else.
  destruct (k4n_c_rst a b) as [[x y]|] eqn:E0.
  { intros H; inverts H. eapply k4n_c_rst_sound; eauto. }
  destruct (k4n_c_inc01 t a b) as [[x y]|] eqn:E1.
  { intros H; inverts H. eapply k4n_c_inc01_sound; eauto. }
  destruct (k4n_c_inc1 t a b) as [[x y]|] eqn:E2.
  { intros H; inverts H. eapply k4n_c_inc1_sound; eauto. }
  destruct (k4n_c_inc00_1 t a b) as [[x y]|] eqn:E3.
  { intros H; inverts H. eapply k4n_c_inc00_1_sound; eauto. }
  destruct (k4n_c_inc00_2 t a b) as [[x y]|] eqn:E4.
  { intros H; inverts H. eapply k4n_c_inc00_2_sound; eauto. }
  destruct (k4n_c_rov t a b) as [[x y]|] eqn:E5.
  { intros H; inverts H. eapply k4n_c_rov_sound; eauto. }
  destruct (k4n_c_rov' t a b) as [[x y]|] eqn:E6.
  { intros H; inverts H. eapply k4n_c_rov'_sound; eauto. }
  destruct (k4n_c_lov1 t a b) as [[x y]|] eqn:E7.
  { intros H; inverts H. eapply k4n_c_lov1_sound; eauto. }
  destruct (k4n_c_lov1' t a b) as [[x y]|] eqn:E8.
  { intros H; inverts H. eapply k4n_c_lov1'_sound; eauto. }
  destruct (k4n_c_lov2 t a b) as [[x y]|] eqn:E9.
  { intros H; inverts H. eapply k4n_c_lov2_sound; eauto. }
  destruct (k4n_c_lov3 t a b) as [[x y]|] eqn:E10.
  { intros H; inverts H. eapply k4n_c_lov3_sound; eauto. }
  destruct (k4n_c_lov4 t a b) as [[x y]|] eqn:E11.
  { intros H; inverts H. eapply k4n_c_lov4_sound; eauto. }
  eapply k4n_c_lov5_sound; eauto.
Qed.

Definition K4NTableOK (P: nat -> nat -> nat -> nat -> Prop)
    (t: K4NTable) : Prop :=
  K4NMap.hmap_WF t /\ K4NTableSound P t.

Lemma k4n_set_sound (P: nat -> nat -> nat -> nat -> Prop)
    t a b c d:
  K4NTableOK P t ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d) ->
  K4NTableOK P (K4NMap.hmap_set (a,b) (c,d) t).
Proof.
  intros [Hwf Hsound] HP. split.
  - apply K4NMap.hmap_set_WF. exact Hwf.
  - intros a' b' c' d' Hget. unfold k4n_get in Hget.
    destruct (K4NPairKey.K_eq_spec (a',b') (a,b)) as [E|E].
    + inverts E. rewrite K4NMap.hmap_get_set_same in Hget by exact Hwf.
      inverts Hget. exact HP.
    + rewrite K4NMap.hmap_get_set_other in Hget by assumption.
      exact (Hsound _ _ _ _ Hget).
Qed.

Definition k4n_layer_step (src: K4NTable) (w: N)
    (s: N*K4NTable) : N*K4NTable :=
  let '(a,out) := s in
  let b := w-2*a in
  let out' :=
    match k4n_cell src a b with
    | Some v => K4NMap.hmap_set (a,b) v out
    | None => out
    end in
  (N.succ a,out').

Definition k4n_make_layer (src: K4NTable) (w: N) : K4NTable :=
  snd (N.iter (N.succ (N.div2 w)) (k4n_layer_step src w) (0,src)).

Definition k4n_build_step (s: N*K4NTable) : N*K4NTable :=
  let '(w,t) := s in (N.succ w,k4n_make_layer t w).

Definition k4n_table_size : Uint63.int :=
  Eval compute in Uint63.of_Z (Z.of_N 131071).

Definition k4n_build (last: N) : K4NTable :=
  snd (N.iter (N.succ last) k4n_build_step
    (0,K4NMap.hmap_make k4n_table_size)).

Lemma k4n_iter_preserve {A} (I: A -> Prop) (f: A -> A) n x:
  I x -> (forall y, I y -> I (f y)) -> I (N.iter n f x).
Proof.
  intros Hx Hf. induction n using N.peano_ind.
  - exact Hx.
  - rewrite N.iter_succ. apply Hf. exact IHn.
Qed.

Lemma k4n_layer_step_sound (P: nat -> nat -> nat -> nat -> Prop)
    (C: K4ComplexRules P K4Low2) (Hrst: P 0%nat 1%nat 0%nat 5%nat)
    src w s:
  K4NTableSound P src -> K4NTableOK P (snd s) ->
  K4NTableOK P (snd (k4n_layer_step src w s)).
Proof.
  intros Hsrc Hout. destruct s as [a out]. cbn [k4n_layer_step] in *.
  destruct (k4n_cell src a (w-2*a)) as [[c d]|] eqn:E; [|exact Hout].
  eapply k4n_set_sound; [exact Hout|].
  eapply k4n_cell_sound; eauto.
Qed.

Lemma k4n_make_layer_sound (P: nat -> nat -> nat -> nat -> Prop)
    (C: K4ComplexRules P K4Low2) (Hrst: P 0%nat 1%nat 0%nat 5%nat)
    src w:
  K4NTableOK P src -> K4NTableOK P (k4n_make_layer src w).
Proof.
  intros Hsrc. unfold k4n_make_layer.
  eapply (k4n_iter_preserve (fun s => K4NTableOK P (snd s)));
    [exact Hsrc|].
  intros s Hs. eapply k4n_layer_step_sound; eauto. exact (proj2 Hsrc).
Qed.

Lemma k4n_build_step_sound (P: nat -> nat -> nat -> nat -> Prop)
    (C: K4ComplexRules P K4Low2) (Hrst: P 0%nat 1%nat 0%nat 5%nat) s:
  K4NTableOK P (snd s) -> K4NTableOK P (snd (k4n_build_step s)).
Proof.
  destruct s as [w t]. cbn [k4n_build_step].
  intros H. eapply (@k4n_make_layer_sound P C Hrst). exact H.
Qed.

Lemma k4n_make_sound (P: nat -> nat -> nat -> nat -> Prop):
  K4NTableOK P (K4NMap.hmap_make k4n_table_size).
Proof.
  split.
  - apply K4NMap.hmap_make_WF.
  - intros a b c d H. unfold k4n_get in H.
    rewrite K4NMap.hmap_get_make in H. discriminate.
Qed.

Lemma k4n_build_sound (P: nat -> nat -> nat -> nat -> Prop)
    (C: K4ComplexRules P K4Low2) (Hrst: P 0%nat 1%nat 0%nat 5%nat)
    last:
  K4NTableOK P (k4n_build last).
Proof.
  unfold k4n_build.
  eapply (k4n_iter_preserve (fun s => K4NTableOK P (snd s))).
  - apply k4n_make_sound.
  - intros s Hs. eapply k4n_build_step_sound; eauto.
Qed.

Definition k4n_value_eqb (x y: K4NResult) : bool :=
  (fst x =? fst y) && (snd x =? snd y).

Definition k4n_lookup_eqb (t: K4NTable) (a b: N) (v: K4NResult) : bool :=
  match k4n_get t a b with
  | Some v' => k4n_value_eqb v' v
  | None => false
  end.

Definition k4n_between (lo hi x: N) : bool :=
  (lo <=? x) && (x <? hi).

Definition k4n_prebase_bit (a: N) : bool :=
  k4n_between 1 3 a || k4n_between 9 21 a ||
  k4n_between 45 93 a || k4n_between 189 380 a ||
  k4n_between 382 383 a.

Definition k4n_check_step (f: N -> bool) (s: N*bool) : N*bool :=
  let '(a,ok) := s in
  let ok' := if ok then f a else false in
  (N.succ a,ok').

Definition k4n_row_test (t: K4NTable) (a: N) : bool :=
  if k4n_prebase_bit a
  then k4n_lookup_eqb t a (779-2*a) (381,21)
  else k4n_lookup_eqb t a (780-2*a) (381,22).

Definition k4n_tail_test (t: K4NTable) (j: N) : bool :=
  k4n_lookup_eqb t (389-j) (2+2*j) (381,22).

Definition k4n_rows_step (t: K4NTable) := k4n_check_step (k4n_row_test t).
Definition k4n_tail_step (t: K4NTable) := k4n_check_step (k4n_tail_test t).

Lemma k4n_check_step_index f s:
  fst (k4n_check_step f s)=N.succ (fst s).
Proof. destruct s. reflexivity. Qed.

Lemma k4n_check_iter_index f n i ok:
  fst (N.iter n (k4n_check_step f) (i,ok))=i+n.
Proof.
  induction n using N.peano_ind.
  - cbn. rewrite N.add_0_r. reflexivity.
  - rewrite N.iter_succ,k4n_check_step_index,IHn,N.add_succ_r.
    reflexivity.
Qed.

Lemma k4n_check_iter_true f n:
  snd (N.iter n (k4n_check_step f) (0,true))=true ->
  forall j, (j<n)%N -> f j=true.
Proof.
  induction n using N.peano_ind; intros H j Hj.
  - nia.
  - rewrite N.iter_succ in H.
    remember (N.iter n (k4n_check_step f) (0,true)) as s eqn:E.
    destruct s as [i ok]. cbn [k4n_check_step] in H.
    destruct ok; cbn in H; try discriminate.
    assert (Hi: i=n).
    { pose proof (k4n_check_iter_index f n 0 true) as Hindex.
      rewrite <- E in Hindex. cbn in Hindex. exact Hindex. }
    subst i. apply N.lt_succ_r in Hj. apply N.lt_eq_cases in Hj.
    destruct Hj as [Hj|Hj].
    + apply IHn; [reflexivity|exact Hj].
    + subst j. exact H.
Qed.

Lemma k4n_value_eqb_eq x y:
  k4n_value_eqb x y=true -> x=y.
Proof.
  destruct x as [x1 x2],y as [y1 y2]. unfold k4n_value_eqb. cbn.
  rewrite and_true_iff,!N.eqb_eq. intros [-> ->]. reflexivity.
Qed.

Lemma k4n_lookup_eqb_sound P t a b c d:
  K4NTableSound P t -> k4n_lookup_eqb t a b (c,d)=true ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  intros Ht H. unfold k4n_lookup_eqb in H.
  destruct (k4n_get t a b) as [[c' d']|] eqn:E; try discriminate.
  apply k4n_value_eqb_eq in H. inverts H. exact (Ht _ _ _ _ E).
Qed.

Lemma k4n_of_nat_lt n m:
  (n<m)%nat -> (N.of_nat n<N.of_nat m)%N.
Proof.
  intros H. unfold N.lt. rewrite <- Nat2N.inj_compare.
  apply Nat.compare_lt_iff. exact H.
Qed.

Lemma k4n_leb_of_nat n m:
  (N.of_nat n<=?N.of_nat m)%N=Nat.leb n m.
Proof.
  unfold N.leb. rewrite <- Nat2N.inj_compare.
  symmetry. apply Nat.leb_compare.
Qed.

Lemma k4n_ltb_of_nat n m:
  (N.of_nat n<?N.of_nat m)%N=Nat.ltb n m.
Proof.
  unfold N.ltb. rewrite <- Nat2N.inj_compare.
  symmetry. apply Nat.ltb_compare.
Qed.

Fixpoint k4n_bit_at (bit: bool) (runs: list nat) (i: nat) : bool :=
  match runs with
  | nil => false
  | n::runs =>
      if Nat.ltb i n then bit else k4n_bit_at (negb bit) runs (i-n)%nat
  end.

Lemma k4n_bit_at_cons bit n runs i:
  k4n_bit_at bit (n::runs) i=
  if Nat.ltb i n then bit else k4n_bit_at (negb bit) runs (i-n)%nat.
Proof. reflexivity. Qed.

Lemma k4n_bit_at_nil bit i: k4n_bit_at bit nil i=false.
Proof. reflexivity. Qed.

Lemma k4n_bits_nth (bit:bool) (runs:list nat) (i:nat):
  (i<k4_sum runs)%nat ->
  nth i (k4_bits bit runs) false=k4n_bit_at bit runs i.
Proof.
  induction runs as [|n runs IH] in bit,i |- *; cbn; intros Hi; try lia.
  change (nth i (repeat bit n++k4_bits (negb bit) runs) false=
    if Nat.ltb i n then bit else k4n_bit_at (negb bit) runs (i-n)%nat).
  destruct (Nat.ltb i n) eqn:E.
  - rewrite Nat.ltb_lt in E.
    rewrite app_nth1 by (rewrite repeat_length; exact E).
    rewrite nth_repeat_lt by exact E.
    reflexivity.
  - rewrite Nat.ltb_ge in E.
    rewrite app_nth2 by (rewrite repeat_length; lia).
    rewrite repeat_length.
    apply IH. lia.
Qed.

Ltac k4n_bool_lia :=
  repeat match goal with
    | |- context [Nat.ltb ?x ?y] =>
        first
        [ replace (Nat.ltb x y) with true by
            (symmetry; apply Nat.ltb_lt; lia)
        | replace (Nat.ltb x y) with false by
            (symmetry; apply Nat.ltb_ge; lia) ]
    | |- context [Nat.leb ?x ?y] =>
        first
        [ replace (Nat.leb x y) with true by
            (symmetry; apply Nat.leb_le; lia)
        | replace (Nat.leb x y) with false by
            (symmetry; apply Nat.leb_gt; lia) ]
    end;
  cbn; try reflexivity; try lia.

Lemma k4n_prebase_bit_spec a:
  (a<383)%nat ->
  k4n_prebase_bit (N.of_nat a)=nth a k4_prebase_bits false.
Proof.
  intros H. unfold k4_prebase_bits.
  rewrite k4n_bits_nth by (unfold k4_prebase_runs; cbn; lia).
  unfold k4n_prebase_bit,k4n_between.
  change
    ((N.of_nat 1<=?N.of_nat a) && (N.of_nat a<?N.of_nat 3) ||
     (N.of_nat 9<=?N.of_nat a) && (N.of_nat a<?N.of_nat 21) ||
     (N.of_nat 45<=?N.of_nat a) && (N.of_nat a<?N.of_nat 93) ||
     (N.of_nat 189<=?N.of_nat a) && (N.of_nat a<?N.of_nat 380) ||
     (N.of_nat 382<=?N.of_nat a) && (N.of_nat a<?N.of_nat 383) =
     k4n_bit_at false k4_prebase_runs a)%bool.
  rewrite !k4n_leb_of_nat,!k4n_ltb_of_nat.
  unfold k4_prebase_runs.
  repeat rewrite k4n_bit_at_cons. rewrite k4n_bit_at_nil.
  destruct (Nat.lt_ge_cases a 1) as [Ha|Ha]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 3) as [Ha'|Ha']; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 9) as [Ha''|Ha'']; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 21) as [Ha3|Ha3]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 45) as [Ha4|Ha4]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 93) as [Ha5|Ha5]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 189) as [Ha6|Ha6]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 380) as [Ha7|Ha7]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 382) as [Ha8|Ha8]; [k4n_bool_lia|].
  destruct (Nat.lt_ge_cases a 383) as [Ha9|Ha9]; k4n_bool_lia.
Qed.

Definition k4n_prebase_check (t: K4NTable) : bool :=
  let rows := snd (N.iter 383 (k4n_rows_step t) (0,true)) in
  if rows then
    let tails := snd (N.iter 7 (k4n_tail_step t) (0,true)) in
    if tails then k4n_lookup_eqb t 390 0 (373,38) else false
  else false.

Definition k4n_low2_780 := k4n_build 780.

Lemma k4n_prebase_check_sound P t:
  K4NTableSound P t -> k4n_prebase_check t=true ->
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4.
Proof.
  intros Ht Hcheck. unfold k4n_prebase_check in Hcheck.
  destruct (snd (N.iter 383 (k4n_rows_step t) (0,true))) eqn:Hrows;
    try discriminate.
  destruct (snd (N.iter 7 (k4n_tail_step t) (0,true))) eqn:Htails;
    try discriminate.
  assert (HR: forall a, (a<383)%N -> k4n_row_test t a=true).
  { apply k4n_check_iter_true. exact Hrows. }
  assert (HT: forall j, (j<7)%N -> k4n_tail_test t j=true).
  { apply k4n_check_iter_true. exact Htails. }
  assert (Hlen: length k4_prebase_bits=383%nat) by
    (vm_compute; reflexivity).
  assert (Hhead: nth 0 k4_prebase_bits false=true \/
      nth 1 k4_prebase_bits false=true) by (vm_compute; auto).
  assert (Hdrop: k4_rdrops k4_prebase_bits 381=4%nat) by
    (vm_compute; reflexivity).
  unfold K4ScanData,K4ExactRow. cbn [k4_gap].
  repeat split; try lia; try assumption.
  - intros a b Ha Hbit Hab.
    specialize (HR (N.of_nat a) ltac:(
      replace 383%N with (N.of_nat 383%nat) by (vm_compute; reflexivity);
      apply k4n_of_nat_lt; lia)).
    unfold k4n_row_test in HR.
    rewrite k4n_prebase_bit_spec,Hbit in HR by exact Ha.
    pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht HR) as HP.
    rewrite Nat2N.id in HP.
    replace (N.to_nat 381) with 381%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat 21) with 21%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat (779-2*N.of_nat a)) with b in HP.
    + exact HP.
    + rewrite N2Nat.inj_sub,N2Nat.inj_mul,Nat2N.id.
      replace (N.to_nat 779) with 779%nat by (vm_compute; reflexivity).
      replace (N.to_nat 2) with 2%nat by (vm_compute; reflexivity). lia.
  - intros a b Ha Hbit Hab.
    specialize (HR (N.of_nat a) ltac:(
      replace 383%N with (N.of_nat 383%nat) by (vm_compute; reflexivity);
      apply k4n_of_nat_lt; lia)).
    unfold k4n_row_test in HR.
    rewrite k4n_prebase_bit_spec,Hbit in HR by exact Ha.
    pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht HR) as HP.
    rewrite Nat2N.id in HP.
    replace (N.to_nat 381) with 381%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat 22) with 22%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat (780-2*N.of_nat a)) with b in HP.
    + exact HP.
    + rewrite N2Nat.inj_sub,N2Nat.inj_mul,Nat2N.id.
      replace (N.to_nat 780) with 780%nat by (vm_compute; reflexivity).
      replace (N.to_nat 2) with 2%nat by (vm_compute; reflexivity). lia.
  - intros j Hj.
    specialize (HT (N.of_nat j) ltac:(
      replace 7%N with (N.of_nat 7%nat) by (vm_compute; reflexivity);
      apply k4n_of_nat_lt; lia)).
    unfold k4n_tail_test in HT.
    pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht HT) as HP.
    rewrite ?N2Nat.inj_sub,?N2Nat.inj_add,?N2Nat.inj_mul,?Nat2N.id in HP.
    replace (N.to_nat 389) with 389%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat 2) with 2%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat 381) with 381%nat in HP by (vm_compute; reflexivity).
    replace (N.to_nat 22) with 22%nat in HP by (vm_compute; reflexivity).
    applys_eq HP; lia.
  - pose proof (k4n_lookup_eqb_sound P t _ _ _ _ Ht Hcheck) as HP.
    applys_eq HP; vm_compute.
Qed.

Lemma k4n_low2_780_check: k4n_prebase_check k4n_low2_780=true.
Proof. native_compute. reflexivity. Qed.

Lemma k4n_low2_prebase_data P (C: K4ComplexRules P K4Low2)
    (Hrst: P 0%nat 1%nat 0%nat 5%nat):
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4.
Proof.
  exact (@k4n_prebase_check_sound P k4n_low2_780
    (proj2 (@k4n_build_sound P C Hrst 780)) k4n_low2_780_check).
Qed.
