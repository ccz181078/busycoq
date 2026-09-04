Require Import BusyCoq.CounterClass1.CounterClass1Common BusyCoq.CounterClass1.CounterClass1K4FiniteN.
Require Import NArith Lia Bool.
From BusyCoq Require Import LibTactics.

Open Scope N_scope.

Definition k4n4_c_lov3 (t:K4NTable) (a b:N) : option K4NResult :=
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
                      if (c=?0) && N.even z then Some (N.div2 z+2,4)
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

Definition k4n4_c_lov4 (t:K4NTable) (a b:N) : option K4NResult :=
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
                      | Some (c,z0) =>
                          match k4n_sub z0 0 with
                          | Some z =>
                              if (c=?0) && N.even z
                              then Some (N.div2 z+1,4) else None
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

Definition k4n4_c_lov5 (t:K4NTable) (a b:N) : option K4NResult :=
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
                                  if (c=?0) && N.odd z
                                  then Some (N.div2 z+2,4) else None
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

Section K4NLow4Sound.

Variable P:nat->nat->nat->nat->Prop.
Variable C:K4ComplexRules P K4Low4.
Let R:=k4c_simple C.
Variable t:K4NTable.
Variable Ht:K4NTableSound P t.

Lemma k4n4_c_lov3_sound a b c d:
  k4n4_c_lov3 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n4_c_lov3.
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
  rewrite N2Nat.inj_add,N2Nat.inj_div2. cbn. rewrite Hb.
  applys_eq (k4c_lov3 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov3_c k4_mode_d]; try lia.
  - rewrite <-Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <-(k4n_even_div2 z He),<-Hz. exact (Ht _ _ _ _ E1).
Qed.

Lemma k4n4_c_lov4_sound a b c d:
  k4n4_c_lov4 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n4_c_lov4.
  destruct (k4n_sub b 5) as [b'|] eqn:Eb; try discriminate.
  destruct (k4n_get t a b') as [[c0 d0]|] eqn:E0; try discriminate.
  destruct (k4n_sub d0 5) as [d0'|] eqn:Ed0; try discriminate.
  destruct (k4n_get t c0 d0') as [[c1 d1]|] eqn:E1; try discriminate.
  destruct (k4n_sub d1 4) as [d1'|] eqn:Ed1; try discriminate.
  destruct (k4n_get t c1 d1') as [[c2 z0]|] eqn:E2; try discriminate.
  destruct (k4n_sub z0 0) as [z|] eqn:Ez; try discriminate.
  destruct (c2=?0) eqn:Ec; try discriminate.
  destruct (N.even z) eqn:He; intros H; try discriminate. inverts H.
  apply N.eqb_eq in Ec. subst c2.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Eb)) as Hb.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed0)) as Hd0.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ed1)) as Hd1.
  pose proof (f_equal N.to_nat (k4n_sub_some _ _ _ Ez)) as Hz.
  rewrite !N2Nat.inj_add in Hb,Hd0,Hd1,Hz. cbn in Hb,Hd0,Hd1,Hz.
  change (N.to_nat d0=(5+N.to_nat d0')%nat) in Hd0.
  change (N.to_nat d1=(4+N.to_nat d1')%nat) in Hd1.
  change (N.to_nat z0=(0+N.to_nat z)%nat) in Hz.
  rewrite N2Nat.inj_add,N2Nat.inj_div2. cbn. rewrite Hb.
  applys_eq (k4c_lov4 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov4_c k4_mode_lov4_input k4_mode_d]; try lia.
  - rewrite <-Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <-Hd1. exact (Ht _ _ _ _ E1).
  - pose proof (k4n_even_div2 z He).
    applys_eq (Ht _ _ _ _ E2); lia.
Qed.

Lemma k4n4_c_lov5_sound a b c d:
  k4n4_c_lov5 t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  unfold k4n4_c_lov5.
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
  rewrite N2Nat.inj_add,N2Nat.inj_div2. cbn. rewrite Hb.
  applys_eq (k4c_lov5 C (N.to_nat a) (N.to_nat b')
    (N.to_nat c0) (N.to_nat d0') (N.to_nat c1) (N.to_nat d1')
    (N.to_nat c2) (N.to_nat d2') (Nat.div2 (N.to_nat z)));
    cbn [k4_mode_lov3_c k4_mode_d]; try lia.
  - rewrite <-Hd0. exact (Ht _ _ _ _ E0).
  - rewrite <-Hd1. exact (Ht _ _ _ _ E1).
  - rewrite <-Hd2. exact (Ht _ _ _ _ E2).
  - rewrite <-(k4n_odd_div2 z Ho). exact (Ht _ _ _ _ E3).
Qed.

End K4NLow4Sound.

Definition k4n4_cell (t:K4NTable) (a b:N) : option K4NResult :=
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
  (k4n_or_else (k4n4_c_lov3 t a b)
  (k4n_or_else (k4n4_c_lov4 t a b)
                (k4n4_c_lov5 t a b)))))))))))).

Lemma k4n4_cell_sound P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat) t:
  K4NTableSound P t -> forall a b c d,
  k4n4_cell t a b=Some (c,d) ->
  P (N.to_nat a) (N.to_nat b) (N.to_nat c) (N.to_nat d).
Proof.
  intros Ht a b c d. unfold k4n4_cell,k4n_or_else.
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
  destruct (k4n4_c_lov3 t a b) as [[x y]|] eqn:E10.
  { intros H; inverts H. eapply k4n4_c_lov3_sound; eauto. }
  destruct (k4n4_c_lov4 t a b) as [[x y]|] eqn:E11.
  { intros H; inverts H. eapply k4n4_c_lov4_sound; eauto. }
  eapply k4n4_c_lov5_sound; eauto.
Qed.

Definition k4n4_layer_step (src:K4NTable) (w:N)
    (s:N*K4NTable) : N*K4NTable :=
  let '(a,out):=s in
  let b:=w-2*a in
  let out':=
    match k4n4_cell src a b with
    | Some v => K4NMap.hmap_set (a,b) v out
    | None => out
    end in
  (N.succ a,out').

Definition k4n4_make_layer (src:K4NTable) (w:N) : K4NTable :=
  snd (N.iter (N.succ (N.div2 w)) (k4n4_layer_step src w) (0,src)).

Definition k4n4_build_step (s:N*K4NTable) : N*K4NTable :=
  let '(w,t):=s in (N.succ w,k4n4_make_layer t w).

Definition k4n4_build (last:N) : K4NTable :=
  snd (N.iter (N.succ last) k4n4_build_step
    (0,K4NMap.hmap_make k4n_table_size)).

Lemma k4n4_layer_step_sound P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat) src w s:
  K4NTableSound P src -> K4NTableOK P (snd s) ->
  K4NTableOK P (snd (k4n4_layer_step src w s)).
Proof.
  intros Hsrc Hout. destruct s as [a out]. cbn [k4n4_layer_step] in *.
  destruct (k4n4_cell src a (w-2*a)) as [[c d]|] eqn:E; [|exact Hout].
  eapply k4n_set_sound; [exact Hout|].
  eapply k4n4_cell_sound; eauto.
Qed.

Lemma k4n4_make_layer_sound P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat) src w:
  K4NTableOK P src -> K4NTableOK P (k4n4_make_layer src w).
Proof.
  intros Hsrc. unfold k4n4_make_layer.
  eapply (k4n_iter_preserve (fun s=>K4NTableOK P (snd s)));
    [exact Hsrc|].
  intros s Hs. eapply k4n4_layer_step_sound; eauto. exact (proj2 Hsrc).
Qed.

Lemma k4n4_build_step_sound P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat) s:
  K4NTableOK P (snd s) -> K4NTableOK P (snd (k4n4_build_step s)).
Proof.
  destruct s as [w t]. cbn [k4n4_build_step].
  intros H. eapply (@k4n4_make_layer_sound P C Hrst). exact H.
Qed.

Lemma k4n4_build_sound P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat) last:
  K4NTableOK P (k4n4_build last).
Proof.
  unfold k4n4_build.
  eapply (k4n_iter_preserve (fun s=>K4NTableOK P (snd s))).
  - apply k4n_make_sound.
  - intros s Hs. eapply k4n4_build_step_sound; eauto.
Qed.

Definition k4n_low4_780:=k4n4_build 780.

Lemma k4n_low4_780_check:k4n_prebase_check k4n_low4_780=true.
Proof. native_compute. reflexivity. Qed.

Lemma k4n_low4_prebase_data P (C:K4ComplexRules P K4Low4)
    (Hrst:P 0%nat 1%nat 0%nat 5%nat):
  K4ScanData P K4T2 k4_prebase_bits 382 2 378 4.
Proof.
  exact (@k4n_prebase_check_sound P k4n_low4_780
    (proj2 (@k4n4_build_sound P C Hrst 780)) k4n_low4_780_check).
Qed.
