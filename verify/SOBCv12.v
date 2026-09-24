(* test_19a: shared modular certificate, invariant, and both machine proofs. *)

From Coq Require Import ZArith Zpow_facts Lia List FMapPositive.
From BusyCoq Require Import Helper Eqb.
Import ListNotations.
Open Scope Z_scope.

Module SPrimeCert.

(* These are Z-only proofs: keep the standard arithmetic hooks here. *)
Local Ltac Zify.zify_pre_hook ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition zrange n := map Z.of_nat (seq 0 n).

Lemma in_zrange n z : In z (zrange n) <-> 0 <= z < Z.of_nat n.
Proof.
  unfold zrange. rewrite in_map_iff. split.
  - intros [k [<- H]]. apply in_seq in H. lia.
  - intros H. exists (Z.to_nat z). rewrite Z2Nat.id by lia.
    split; [reflexivity|apply in_seq; lia].
Qed.

Definition sqkey m x := Z.to_pos (1+(x*x) mod m).
Fixpoint square_map m xs : PositiveMap.t unit :=
  match xs with
  | [] => PositiveMap.empty unit
  | x::xs => PositiveMap.add (sqkey m x) tt (square_map m xs)
  end.

Lemma square_map_in m xs x :
  In x xs -> PositiveMap.find (sqkey m x) (square_map m xs) = Some tt.
Proof.
  induction xs as [|y xs IH]; cbn; [tauto|].
  intros [<-|H].
  - apply PositiveMap.gss.
  - rewrite PositiveMapAdditionalFacts.gsspec.
    destruct PositiveMap.E.eq_dec; auto.
Qed.

Definition qr m := square_map m (zrange (Z.to_nat m)).
Definition squareb m d := PositiveMap.mem (Z.to_pos (1+d mod m)) (qr m).

Lemma squareb_spec m x : 0 < m -> squareb m (x*x) = true.
Proof.
  intros Hm. unfold squareb.
  replace ((x*x) mod m) with (((x mod m)*(x mod m)) mod m)
    by (rewrite <- Z.mul_mod by lia; reflexivity).
  change (PositiveMap.mem (sqkey m (x mod m)) (qr m) = true).
  rewrite PositiveMap.mem_find. unfold qr.
  rewrite square_map_in; [reflexivity|].
  apply in_zrange. rewrite Z2Nat.id by lia. apply Z.mod_pos_bound; lia.
Qed.

Definition powm m e := Zpow_mod 2 e m.

Lemma powm_spec m e : 0 <= e -> 0 < m -> powm m e = 2^e mod m.
Proof.
  intros He Hm. apply Zpow_mod_correct; lia.
Qed.

Lemma pow_period m p e :
  0 < m -> 0 < p -> 0 <= e -> 2^p mod m = 1 ->
  2^e mod m = 2^(e mod p) mod m.
Proof.
  intros Hm Hp He Hper.
  assert (1 < m) by (pose proof (Z.mod_pos_bound (2^p) m Hm); lia).
  assert (0 <= e/p) by (apply Z.div_pos; lia).
  pose proof (Z.mod_pos_bound e p Hp).
  rewrite (Z.div_mod e p) at 1 by lia.
  rewrite Z.pow_add_r, Z.pow_mul_r by nia.
  rewrite Z.mul_mod by lia.
  rewrite Zpower_mod, Hper, Z.pow_1_l by lia.
  rewrite (Z.mod_small 1 m) by lia.
  rewrite Z.mul_1_l, Z.mod_mod by lia. reflexivity.
Qed.

Definition row := (Z*Z*Z*Z)%type.
Definition reduce p '(l,n,x,r) : row := (l mod p,n mod p,x mod p,r).
Definition arg n x r :=
  if r =? 1 then x-2*n*(n+1) else x-2*(n+1)*(n+1).
Definition disc '(l,n,x,r) :=
  2^(l+2*n+r+3) - (2*r-1)*2^(2*n+2) - 5*2^(arg n x r) + 1.
Definition eval_mod p m '(l,n,x,r) :=
  (powm m ((l+2*n+r+3) mod p) - (2*r-1)*powm m ((2*n+2) mod p)
   -5*powm m ((arg n x r) mod p)+1) mod m.

Ltac mod_poly :=
  repeat first [apply Zplus_eqm | apply Zminus_eqm | apply Zmult_eqm | apply Zopp_eqm |
                apply Zmod_eqm | reflexivity].

Lemma arg_mod p n x r :
  arg (n mod p) (x mod p) r mod p = arg n x r mod p.
Proof.
  unfold arg. destruct (r =? 1); mod_poly.
Qed.

Lemma eval_reduce p m s : eval_mod p m (reduce p s) = eval_mod p m s.
Proof.
  destruct s as [[[l n] x] r]. unfold eval_mod, reduce.
  rewrite arg_mod.
  assert (H1: (l mod p+2*(n mod p)+r+3) mod p = (l+2*n+r+3) mod p)
    by mod_poly.
  assert (H2: (2*(n mod p)+2) mod p = (2*n+2) mod p)
    by mod_poly.
  now rewrite H1,H2.
Qed.

Definition exponents_ok '(l,n,x,r) :=
  0 <= l+2*n+r+3 /\ 0 <= 2*n+2 /\ 0 <= arg n x r.

Lemma eval_mod_spec p m s :
  0 < p -> 0 < m -> powm m p = 1 -> exponents_ok s ->
  eval_mod p m s = disc s mod m.
Proof.
  destruct s as [[[l n] x] r]. intros Hp Hm Hper [H1 [H2 H3]].
  rewrite powm_spec in Hper by lia. unfold eval_mod, disc.
  rewrite !powm_spec by (try apply Z.mod_pos_bound; lia).
  rewrite <- !(pow_period m p) by assumption.
  mod_poly.
Qed.

Definition passes p m (squares : PositiveMap.t unit) s :=
  PositiveMap.mem (Z.to_pos (1+eval_mod p m s)) squares.

Lemma passes_square p m s y :
  0 < p -> 0 < m -> powm m p = 1 -> exponents_ok s -> disc s = y*y ->
  passes p m (qr m) (reduce p s) = true.
Proof.
  intros Hp Hm Hper Hok Hsq. unfold passes.
  rewrite eval_reduce, eval_mod_spec by assumption.
  rewrite Hsq. apply squareb_spec; assumption.
Qed.

Definition valid p m := (0 <? m) && (powm m p =? 1).

Fixpoint sieve p ms xs :=
  match ms with
  | [] => xs
  | m::ms => let squares := qr m in
    sieve p ms (filter (passes p m squares) xs)
  end.

Lemma sieve_square p ms xs s y :
  0 < p -> forallb (valid p) ms = true -> exponents_ok s -> disc s = y*y ->
  In (reduce p s) xs -> In (reduce p s) (sieve p ms xs).
Proof.
  intros Hp Hms Hok Hsq. revert xs.
  induction ms as [|m ms IH]; cbn [sieve]; intros xs Hin; [assumption|].
  rewrite forallb_forall in Hms.
  assert (Hm : valid p m = true) by (apply Hms; left; reflexivity).
  unfold valid in Hm. apply and_true_iff in Hm.
  destruct Hm as [Hm Hper]. apply Z.ltb_lt in Hm. apply Z.eqb_eq in Hper.
  apply IH.
  - apply forallb_forall. intros z Hz. apply Hms; right; assumption.
  - apply filter_In. split; [assumption|eapply passes_square; eassumption].
Qed.

Definition mods96 : list Z := [9;5;7;13;17;97;193;241;257;673;65537].
Definition mods288 : list Z := [27;19;37;73;109;433;577;1153;6337;38737].
Definition mods1440 : list Z :=
  [11;31;41;61;151;181;331;631;1321;23041;23311;37441;54001;61681].

Lemma moduli_valid :
  forallb (valid 96) mods96 = true /\
  forallb (valid 288) mods288 = true /\
  forallb (valid 1440) mods1440 = true.
Proof. vm_compute; auto. Qed.

Definition inputb x := (x mod 32 =? 11) || (x mod 32 =? 15) || (x mod 32 =? 31).
Definition exceptional (s:row) := let '(l,n,x,r) := s in
  (x mod 96 =? 15) || ((x mod 96 =? 11) && (l mod 2 =? 1)).
Definition box ls ns xs rs : list row :=
  flat_map (fun l => flat_map (fun n => flat_map (fun x =>
    map (fun r => (l,n,x,r)) rs) xs) ns) ls.
Definition stage1 := sieve 96 mods96
  (box (zrange 96) (zrange 96) (filter inputb (zrange 96)) [1;2]).
Definition lift p k xs : list row :=
  flat_map (fun '(l,n,x,r) =>
    box (map (fun i => l+p*i) (zrange k))
        (map (fun i => n+p*i) (zrange k))
        (map (fun i => x+p*i) (zrange k)) [r]) xs.
Definition stage2 := sieve 288 mods288 (lift 96 3 stage1).

Definition survivors : list row :=
  [(1,1,11,2);(1,145,11,2);(287,2,15,1);(287,140,15,2);
   (287,146,15,1);(287,284,15,2);(12,115,127,1);(12,259,127,1);
   (143,140,159,2);(143,284,159,2);(53,33,63,2);(53,177,63,2)].

Definition row_eqb '(l,n,x,r) '(l',n',x',r') :=
  (l =? l') && (n =? n') && (x =? x') && (r =? r').
Definition subsetb xs ys := forallb (fun x => existsb (row_eqb x) ys) xs.

Lemma certificate_first : subsetb stage2 survivors = true.
Proof. native_check_eq. Qed.

Lemma certificate_last :
  sieve 1440 mods1440 (lift 288 5 (filter (fun s => negb (exceptional s)) survivors)) = [].
Proof. native_check_eq. Qed.

End SPrimeCert.

From Coq Require Import ZArith Znumtheory Lia List Arith.
From BusyCoq Require Import Eqb.
Import ListNotations SPrimeCert.
Open Scope Z_scope.

Module SPrimeMath.

Local Ltac Zify.zify_pre_hook ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Lemma box_in ls ns xs rs l n x r :
  In l ls -> In n ns -> In x xs -> In r rs -> In (l,n,x,r) (box ls ns xs rs).
Proof.
  intros Hl Hn Hx Hr. unfold box.
  apply in_flat_map. exists l; split; [assumption|].
  apply in_flat_map. exists n; split; [assumption|].
  apply in_flat_map. exists x; split; [assumption|].
  apply in_map; assumption.
Qed.

Lemma lift_in p k xs s :
  0 < p -> (0 < k)%nat -> In (reduce p s) xs ->
  In (reduce (p*Z.of_nat k) s) (lift p k xs).
Proof.
  destruct s as [[[l n] x] r]. intros Hp Hk Hin.
  unfold lift. apply in_flat_map. exists (reduce p (l,n,x,r)).
  split; [assumption|]. unfold reduce.
  rewrite !Z.rem_mul_r by lia. apply box_in; [| | |now left].
  all: apply in_map_iff; eexists; split; [reflexivity|].
  all: apply in_zrange; apply Z.mod_pos_bound; lia.
Qed.

Lemma mod_factor x p k : 0 < p -> 0 < k -> (x mod (p*k)) mod p = x mod p.
Proof.
  intros. symmetry. apply Zmod_div_mod; try nia.
  exists k; ring.
Qed.

Lemma row_eqb_spec s t : row_eqb s t = true <-> s=t.
Proof.
  destruct s as [[[l n] x] r], t as [[[l' n'] x'] r'].
  unfold row_eqb. repeat rewrite and_true_iff.
  rewrite !Z.eqb_eq. intuition congruence.
Qed.

Lemma subsetb_spec xs ys : subsetb xs ys = true -> forall s, In s xs -> In s ys.
Proof.
  unfold subsetb. rewrite forallb_forall. intros H s Hs.
  specialize (H s Hs). apply existsb_exists in H.
  destruct H as [t [Ht E]]. apply row_eqb_spec in E; congruence.
Qed.

Local Opaque sieve.

Lemma certificate_nonsquare l n x r y :
  exponents_ok (l,n,x,r) -> (r=1 \/ r=2) -> inputb x = true ->
  exceptional (l,n,x,r) = false -> disc (l,n,x,r) <> y*y.
Proof.
  intros Hok Hr Hx Hex Hsq.
  destruct moduli_valid as [H96 [H288 H1440]].
  assert (I1 : In (reduce 96 (l,n,x,r)) stage1).
  { apply sieve_square with (y:=y); try assumption; [lia|].
    unfold reduce. apply box_in.
    1,2: apply in_zrange; apply Z.mod_pos_bound; lia.
    - apply filter_In. split; [apply in_zrange; apply Z.mod_pos_bound; lia|].
      unfold inputb. change (96) with (32*3).
      rewrite mod_factor by lia. exact Hx.
    - simpl. lia. }
  assert (I2 : In (reduce 288 (l,n,x,r)) survivors).
  { apply (subsetb_spec _ _ certificate_first).
    apply (sieve_square 288 mods288 (lift 96 3 stage1) (l,n,x,r) y).
    - lia.
    - exact H288.
    - exact Hok.
    - exact Hsq.
    - apply (lift_in 96 3); [lia|lia|exact I1]. }
  assert (I3 : In (reduce 288 (l,n,x,r))
                   (filter (fun s => negb (exceptional s)) survivors)).
  { apply filter_In. split; [assumption|].
    apply Bool.negb_true_iff. unfold reduce, exceptional in *.
    replace ((x mod 288) mod 96) with (x mod 96)
      by (symmetry; apply (mod_factor x 96 3); lia).
    replace ((l mod 288) mod 2) with (l mod 2)
      by (symmetry; apply (mod_factor l 2 144); lia).
    exact Hex. }
  assert (I4 : In (reduce 1440 (l,n,x,r))
    (sieve 1440 mods1440 (lift 288 5 (filter (fun s => negb (exceptional s)) survivors)))).
  { apply (sieve_square 1440 mods1440
      (lift 288 5 (filter (fun s => negb (exceptional s)) survivors)) (l,n,x,r) y).
    - lia.
    - exact H1440.
    - exact Hok.
    - exact Hsq.
    - apply (lift_in 288 5); [lia|lia|exact I3]. }
  rewrite certificate_last in I4. contradiction.
Qed.

Lemma pow4_not_double_square k u :
  u mod 2 = 1 -> forall q, 4^Z.of_nat k*u <> 2*q*q.
Proof.
  intros Hu. induction k as [|k IH]; intros q E.
  - cbn [Z.of_nat Z.pow] in E. replace u with ((q*q)*2) in Hu by nia.
    rewrite Z.mod_mul in Hu by lia. discriminate.
  - rewrite Nat2Z.inj_succ, Z.pow_succ_r in E by lia.
    assert (Hq : Z.Even (q*q)).
    { exists (4^Z.of_nat k*u). nia. }
    apply Z.even_spec in Hq. rewrite Z.even_mul in Hq.
    rewrite Bool.orb_diag in Hq.
    apply Z.even_spec in Hq. destruct Hq as [v Hv].
    apply (IH v). nia.
Qed.

Definition good128 x := x mod 128=47 \/ x mod 128=63 \/ x mod 128=107 \/ x mod 128=127.
Record Weak l x : Prop := {
  weak_length : 18 <= l;
  weak_range : 0 < x < 2^l;
  weak_low : good128 x;
  weak_exception : exceptional (l,0,x,1) = false
}.
Record Inv l x : Prop := {
  inv_weak : Weak l x;
  inv_half : forall q, x+1 <> 2*q*q;
  inv_disc : forall q, 2*x+3 <> q*q
}.

Definition input n a r :=
  if r =? 1 then 2*n*(n+1)+a+1 else 2*(n+1)*(n+1)+a+1.
Definition length_next l n r := l+2*n+r+2.
Definition value_next l n a r :=
  2^(length_next l n r) - (2*r-1)*2^(2*n+1) - 5*2^a - 1.

Lemma good128_odd x : good128 x -> x mod 2 = 1.
Proof.
  intros H. unfold good128 in H.
  rewrite <- (mod_factor x 2 64) by lia.
  change ((x mod 128) mod 2=1).
  destruct H as [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

Lemma next_rule l x : Inv l x ->
  exists n a r, 1<=n /\ 0<=a<=2*n-2 /\ (r=1 \/ r=2) /\ x=input n a r.
Proof.
  intros [[Hl Hrange Hlow Hex] Hhalf Hdisc].
  pose proof (good128_odd x Hlow) as Hodd.
  pose proof (Z.div_mod x 2 ltac:(lia)) as Hdiv.
  set (y := x/2+1).
  assert (Hy : 1<=y /\ x=2*y-1) by (unfold y; lia).
  pose proof (Z.sqrt_spec y ltac:(lia)) as Hsqrt.
  pose proof (Z.sqrt_nonneg y) as Hsqrt0.
  set (q := Z.sqrt y) in *.
  cbn zeta in Hsqrt.
  assert (Hyq : q*q<y) by (specialize (Hhalf q); nia).
  assert (Hadj : y<>q*(q+1)) by (specialize (Hdisc (2*q+1)); nia).
  destruct (Z_lt_ge_dec y (q*(q+1))).
  - exists (q-1), (x-2*q*q-1), 2. unfold input; cbn [Z.eqb Pos.eqb].
    repeat split; try nia; auto.
  - exists q, (x-2*q*(q+1)-1), 1. unfold input; cbn [Z.eqb Pos.eqb].
    repeat split; try nia; auto.
Qed.

Definition all2 p (f:Z->Z->bool) :=
  forallb (fun n => forallb (f n) (zrange p)) (zrange p).

Lemma all2_spec p f : all2 p f = true ->
  forall n a, 0<=n<Z.of_nat p -> 0<=a<Z.of_nat p -> f n a = true.
Proof.
  unfold all2. rewrite forallb_forall.
  intros H n a Hn Ha. specialize (H n (proj2 (in_zrange p n) Hn)).
  rewrite forallb_forall in H. apply H. apply in_zrange; assumption.
Qed.

Definition good128b x :=
  (x mod 128 =? 47) || (x mod 128 =? 63) || (x mod 128 =? 107) || (x mod 128 =? 127).
Definition paramsb n a r :=
  if good128b (input n a r) then
    (a mod 2 =? 0) &&
      (if r =? 1 then a mod 4 =? 2 else negb ((a =? 0) || (a =? 2)))
  else true.

Lemma params_checked : all2 128 (fun n a => paramsb n a 1 && paramsb n a 2) = true.
Proof. native_check_eq. Qed.

Lemma input_mod p n a r :
  input (n mod p) (a mod p) r mod p = input n a r mod p.
Proof. unfold input. destruct (r =? 1); mod_poly. Qed.

Lemma short_or_true (a b:bool) : (a || b)=true <-> a=true \/ b=true.
Proof. destruct a,b; cbn; tauto. Qed.

Lemma good128b_spec x : good128b x = true <-> good128 x.
Proof.
  unfold good128b, good128.
  rewrite !short_or_true, !Z.eqb_eq. tauto.
Qed.

Lemma mod128_2 a : a mod 128 mod 2 = a mod 2.
Proof. apply (mod_factor a 2 64); lia. Qed.
Lemma mod128_4 a : a mod 128 mod 4 = a mod 4.
Proof. apply (mod_factor a 4 32); lia. Qed.

Lemma parameters n a r :
  1<=n -> 0<=a<=2*n-2 -> (r=1 \/ r=2) -> good128 (input n a r) ->
  3<=n /\ 2<=a /\ a mod 2=0 /\
  (r=1 -> a mod 4=2) /\ (r=2 -> 4<=a).
Proof.
  intros Hn Ha Hr Hlow.
  pose proof (Z.div_mod a 2 ltac:(lia)) as Hdiv2.
  pose proof (Z.div_mod a 4 ltac:(lia)) as Hdiv4.
  pose proof (all2_spec 128 _ params_checked (n mod 128) (a mod 128)
    (Z.mod_pos_bound n 128 ltac:(lia)) (Z.mod_pos_bound a 128 ltac:(lia))) as H.
  apply and_true_iff in H. destruct H as [H1 H2].
  assert (Hgood : good128b (input (n mod 128) (a mod 128) r)=true).
  { unfold good128b. rewrite !input_mod. apply good128b_spec; assumption. }
  assert (Hp : a mod 2=0 /\ (r=1 -> a mod 4=2) /\ (r=2 -> 4<=a)).
  { destruct Hr as [-> | ->].
    - unfold paramsb in H1. rewrite Hgood in H1. change ((a mod 128 mod 2 =? 0) && (a mod 128 mod 4 =? 2) = true) in H1.
      apply and_true_iff in H1. destruct H1 as [Hmod Hfour].
      apply Z.eqb_eq in Hmod,Hfour.
      rewrite mod128_2 in Hmod.
      rewrite mod128_4 in Hfour. intuition lia.
    - unfold paramsb in H2. rewrite Hgood in H2. change ((a mod 128 mod 2 =? 0) && negb ((a mod 128 =? 0) || (a mod 128 =? 2)) = true) in H2.
      apply and_true_iff in H2. destruct H2 as [Hmod Hne].
      apply Z.eqb_eq in Hmod. rewrite mod128_2 in Hmod.
      apply Bool.negb_true_iff in Hne. apply or_false_iff in Hne.
      destruct Hne as [H0 H2]. apply Z.eqb_neq in H0,H2.
      assert (4<=a).
      { destruct (Z_lt_ge_dec a 4); [|lia]. rewrite Z.mod_small in H0,H2 by lia. lia. }
      intuition lia. }
  assert (Ha2 : 2<=a).
  { destruct Hp as [He [Hf Hg]]. destruct Hr as [-> | ->].
    - specialize (Hf eq_refl). lia.
    - specialize (Hg eq_refl). lia. }
  assert (Hbig : 47<=input n a r).
  { pose proof (Z.mod_le (input n a r) 128).
    unfold good128 in Hlow. unfold input in *.
    destruct (r =? 1); nia. }
  assert (3<=n).
  { unfold input in Hbig. destruct (r =? 1); nia. }
  tauto.
Qed.

Lemma power128 e : 7<=e -> 2^e mod 128=0.
Proof.
  intros He. replace e with ((e-7)+7) at 1 by lia.
  rewrite Z.pow_add_r by lia. change ((2^(e-7)*128) mod 128=0).
  apply Z.mod_mul; lia.
Qed.

Lemma power96 e : 5<=e ->
  2^e mod 96 = if e mod 2 =? 0 then 64 else 32.
Proof.
  intros He. replace e with (5+(e-5)) at 1 by lia.
  rewrite Z.pow_add_r by lia.
  change ((32*2^(e-5)) mod (32*3)=if e mod 2 =? 0 then 64 else 32).
  rewrite Z.mul_mod_distr_l by lia.
  rewrite (pow_period 3 2 (e-5)) by (try reflexivity; lia).
  rewrite (Zminus_mod e 5 2).
  pose proof (Z.mod_pos_bound e 2 ltac:(lia)).
  assert (e mod 2=0 \/ e mod 2=1) as [H0|H1] by lia;
    rewrite H0 || rewrite H1; reflexivity.
Qed.

Definition oddpart l n a r :=
  2^(2*n+1-a)*(2^(l+r+1)-(2*r-1))-5.

Lemma output_factor l n a r :
  0<=a<=2*n-2 -> 0<=l -> (r=1 \/ r=2) ->
  value_next l n a r+1 = 2^a*oddpart l n a r.
Proof.
  intros Ha Hl Hr. unfold value_next, oddpart, length_next.
  replace (l+2*n+r+2) with (a+(2*n+1-a)+(l+r+1)) by lia.
  replace (2*n+1) with (a+(2*n+1-a)) at 2 by lia.
  rewrite !Z.pow_add_r by lia. ring.
Qed.

Lemma oddpart_good l n a r :
  0<=a<=2*n-2 -> 18<=l -> (r=1 \/ r=2) ->
  0<oddpart l n a r /\ oddpart l n a r mod 2=1.
Proof.
  intros Ha Hl Hr.
  assert (H1 : 8<=2^(2*n+1-a)).
  { change (2^3<=2^(2*n+1-a)). apply Z.pow_le_mono_r; lia. }
  assert (H2 : 16<=2^(l+r+1)).
  { change (2^4<=2^(l+r+1)). apply Z.pow_le_mono_r; lia. }
  split; unfold oddpart; [destruct Hr; nia|].
  assert (He : 2^(2*n+1-a) mod 2=0).
  { replace (2*n+1-a) with ((2*n-a)+1) by lia.
    rewrite Z.pow_add_r by lia. change ((2^(2*n-a)*2) mod 2=0).
    apply Z.mod_mul; lia. }
  rewrite Zminus_mod, Z.mul_mod, He by lia. reflexivity.
Qed.

Lemma output_bounds l n a r :
  2<=a<=2*n-2 -> 18<=l -> (r=1 \/ r=2) ->
  18<=length_next l n r /\ 0<value_next l n a r<2^(length_next l n r) /\
  (a mod 2=0 -> forall q, value_next l n a r+1<>2*q*q).
Proof.
  intros Ha Hl Hr.
  pose proof (output_factor l n a r ltac:(lia) ltac:(lia) Hr) as E.
  destruct (oddpart_good l n a r ltac:(lia) Hl Hr) as [Hu Huodd].
  assert (Hfour : 4<=2^a).
  { change (2^2<=2^a). apply Z.pow_le_mono_r; lia. }
  assert (Hmiddle : 0<2^(2*n+1)) by (apply Z.pow_pos_nonneg; lia).
  repeat split.
  - unfold length_next; lia.
  - nia.
  - unfold value_next. destruct Hr; nia.
  - intros Haodd q Heq.
    pose proof (Z.div_mod a 2 ltac:(lia)).
    assert (Hk : 0<=a/2) by (apply Z.div_pos; lia).
    apply (pow4_not_double_square (Z.to_nat (a/2)) _ Huodd q).
    rewrite Z2Nat.id by lia.
    replace 4 with (2^2) by reflexivity.
    rewrite <- Z.pow_mul_r by lia.
    replace (2*(a/2)) with a by lia. lia.
Qed.

Lemma output_mod m l n a r :
  value_next l n a r mod m =
  ((2^(length_next l n r) mod m) - (2*r-1)*(2^(2*n+1) mod m)
    -5*(2^a mod m)-1) mod m.
Proof. unfold value_next. symmetry. mod_poly. Qed.

Lemma output_low l n a r :
  18<=l -> 3<=n -> 2<=a -> a mod 2=0 -> (r=1 \/ r=2) ->
  (r=1 -> a mod 4=2) -> (r=2 -> 4<=a) ->
  good128 (value_next l n a r) /\
  exceptional (length_next l n r,0,value_next l n a r,1)=false.
Proof.
  intros Hl Hn Ha He Hr Hfour Hge4.
  pose proof (Z.div_mod a 2 ltac:(lia)) as Hdiv2.
  pose proof (Z.div_mod a 4 ltac:(lia)) as Hdiv4.
  assert (HL : 7<=length_next l n r) by (unfold length_next; lia).
  assert (H128 : value_next l n a r mod 128 = (-5*(2^a mod 128)-1) mod 128).
  { rewrite output_mod, (power128 _ HL), (power128 (2*n+1)) by lia.
    f_equal; ring. }
  split.
  - unfold good128. rewrite H128.
    assert (a=2 \/ a=4 \/ a=6 \/ 8<=a) as [->|[->|[->|Ha8]]] by lia.
    1,2,3: vm_compute; tauto.
    rewrite power128 by lia. vm_compute; tauto.
  - pose proof (Z.mod_pos_bound (length_next l n r) 2 ltac:(lia)) as Hpar.
    assert (Hnpar : (2*n+1) mod 2=1).
    { replace (2*n+1) with (1+n*2) by ring.
      rewrite Z.mod_add by lia. reflexivity. }
    assert (Hn96 : 2^(2*n+1) mod 96=32) by (rewrite power96,Hnpar by lia; reflexivity).
    assert (Ha96 : 6<=a -> 2^a mod 96=64) by (intros; rewrite power96,He by lia; reflexivity).
    assert (Hpar2 : length_next l n r mod 2=0 \/ length_next l n r mod 2=1) by lia.
    destruct Hr as [-> | ->].
    + specialize (Hfour eq_refl). assert (a=2 \/ 6<=a) as [->|Ha6] by lia;
        unfold exceptional; rewrite !output_mod, Hn96;
        rewrite (power96 (length_next l n 1)) by lia.
      * destruct Hpar2 as [H|H]; rewrite H; reflexivity.
      * rewrite Ha96 by assumption. destruct Hpar2 as [H|H]; rewrite H; reflexivity.
    + specialize (Hge4 eq_refl). assert (a=4 \/ 6<=a) as [->|Ha6] by lia;
        unfold exceptional; rewrite !output_mod, Hn96;
        rewrite (power96 (length_next l n 2)) by lia.
      * destruct Hpar2 as [H|H]; rewrite H; reflexivity.
      * rewrite Ha96 by assumption. destruct Hpar2 as [H|H]; rewrite H; reflexivity.
Qed.

Lemma input_arg n a r : arg n (input n a r) r = a+1.
Proof. unfold arg,input. destruct (r =? 1); ring. Qed.

Lemma output_disc l n a r :
  0<=a -> 0<=n -> 0<=l -> (r=1 \/ r=2) ->
  2*value_next l n a r+3=disc (l,n,input n a r,r).
Proof.
  intros. unfold value_next, disc, length_next. rewrite input_arg.
  replace (l+2*n+r+3) with (l+2*n+r+2+1) by lia.
  replace (2*n+2) with (2*n+1+1) by lia.
  rewrite !Z.pow_add_r by lia. change (2^1) with 2. ring.
Qed.

Lemma preserves l n a r :
  Weak l (input n a r) -> 1<=n -> 0<=a<=2*n-2 -> (r=1 \/ r=2) ->
  Inv (length_next l n r) (value_next l n a r).
Proof.
  intros [Hl Hrange Hlow Hex] Hn Ha Hr.
  destruct (parameters n a r Hn Ha Hr Hlow) as [Hn3 [Ha2 [He [Hfour Hge4]]]].
  destruct (output_bounds l n a r ltac:(lia) Hl Hr) as [HL [HX Hhalf]].
  destruct (output_low l n a r Hl Hn3 Ha2 He Hr Hfour Hge4) as [Hlow' Hex'].
  constructor.
  - constructor; assumption.
  - apply Hhalf; assumption.
  - intros q. rewrite output_disc by lia. apply certificate_nonsquare; try assumption.
    + unfold exponents_ok. rewrite input_arg. lia.
    + unfold inputb.
      rewrite <- (mod_factor (input n a r) 32 4) by lia.
      change ((input n a r mod 128 mod 32 =? 11) ||
        (input n a r mod 128 mod 32 =? 15) ||
        (input n a r mod 128 mod 32 =? 31) = true).
      unfold good128 in Hlow.
      destruct Hlow as [H|[H|[H|H]]]; rewrite H; reflexivity.
Qed.

Lemma nat_output l n a b r :
  0<=l -> 0<=a -> 0<=b -> a+b=2*n-2 -> (r=1 \/ r=2) ->
  (Z.to_nat (length_next l n r), Z.to_nat (value_next l n a r)) =
  ((Z.to_nat l+Z.to_nat a+Z.to_nat b+Z.to_nat (r+4))%nat,
   (2^(Z.to_nat l+Z.to_nat a+Z.to_nat b)*Z.to_nat (2^(r+4))
    -2^(Z.to_nat a+Z.to_nat b)*Z.to_nat ((2*r-1)*8)
    -2^Z.to_nat a*5-1)%nat).
Proof.
  intros Hl Ha Hb Hab Hr.
  assert (EL : length_next l n r=l+a+b+(r+4)) by (unfold length_next; lia).
  assert (EX : value_next l n a r =
    2^(l+a+b)*2^(r+4)-2^(a+b)*((2*r-1)*8)-2^a*5-1).
  { unfold value_next. rewrite EL.
    replace (2*n+1) with (a+b+3) by lia.
    rewrite !Z.pow_add_r by lia. change (2^3) with 8. ring. }
  rewrite EL,EX.
  rewrite !Z2Nat.inj_sub by (try (apply Z.mul_nonneg_nonneg); try (apply Z.pow_nonneg); lia).
  rewrite !Z2Nat.inj_mul by (try (apply Z.pow_nonneg); lia).
  rewrite !Z2Nat.inj_pow by lia.
  rewrite !Z2Nat.inj_add by lia. reflexivity.
Qed.

Lemma input_nat0 n a : 0<=n -> 0<=a ->
  Z.to_nat (input n a 1) = (Z.to_nat n*(Z.to_nat n+1)*2+(Z.to_nat a+1))%nat.
Proof.
  intros. unfold input. change (1 =? 1) with true. cbn iota.
  repeat first [rewrite Z2Nat.inj_add by nia | rewrite Z2Nat.inj_mul by nia].
  change (Z.to_nat 2) with 2%nat. change (Z.to_nat 1) with 1%nat.
  ring.
Qed.

Lemma input_nat1 n a : 0<=n -> 0<=a ->
  Z.to_nat (input n a 2) =
    (Z.to_nat n*(Z.to_nat n+1)*2+((Z.to_nat n*2+1)+(Z.to_nat a+2)))%nat.
Proof.
  intros. unfold input. change (2 =? 1) with false. cbn iota.
  repeat first [rewrite Z2Nat.inj_add by nia | rewrite Z2Nat.inj_mul by nia].
  change (Z.to_nat 2) with 2%nat. change (Z.to_nat 1) with 1%nat.
  ring.
Qed.

Lemma bound_nat l x : 0<=l -> 0<=x<2^l ->
  (Z.to_nat x < 2^Z.to_nat l)%nat.
Proof.
  intros Hl Hx. change 2%nat with (Z.to_nat 2).
  rewrite <- Z2Nat.inj_pow by lia. apply Z2Nat.inj_lt; lia.
Qed.

Lemma initial1 : Inv 18 260799.
Proof.
  constructor.
  - constructor; unfold good128,exceptional; vm_compute; intuition congruence.
  - intros q Hq.
    assert (E : 130400=q*q) by lia.
    pose proof (squareb_spec 3 q ltac:(lia)). rewrite <- E in H.
    vm_compute in H. discriminate.
  - intros q Hq.
    pose proof (squareb_spec 9 q ltac:(lia)). rewrite <- Hq in H.
    vm_compute in H. discriminate.
Qed.

Lemma initial2_weak : Weak 31 2144731135.
Proof. constructor; unfold good128,exceptional; vm_compute; intuition congruence. Qed.

End SPrimeMath.

From BusyCoq Require Import Individual62.
Require Import ZifyNat Lia.
Require Import ZArith.
Require Import String.
Require Import List.
From BusyCoq Require Import BinaryCounter_v2 Longitudinal.
From BusyCoq Require Import NatMod.
From BusyCoq Require Import SimplTape.
Import SPrimeMath.

Open Scope nat_scope.
Open Scope sym.
Open Scope list.


Module TM1.

Definition tm := Eval compute in (TM_from_str "1RB1LC_1LA1RB_1LD0LA_1RE0RF_---1RD_0RE1RB").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC len n := BinDec [0;1] [1;1] len n ([1]*>0inf).

Notation "l |> r" := (l<*[] {{B}}> r) (at level 30).
Notation "l <| r" := (l <{{A}} []*>r) (at level 30).

Notation hL := (A,[]).
Notation hR := (B,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition LC0 a b :=
  0inf <* <[1;1]^^a <* <[0;0] <* <[1;1]^^b <* <[1;0;1;1;1].

Definition LC1 a b :=
  0inf <* <[1;1]^^a <* <[0;0] <* <[1;1]^^b <* <[0;1;1;1;1].

Lemma ROv0 a b len:
  LC0 (2+a) (1+b) |> RC len 0 -->+
  LC0 1 0 |> RC (len+1+1+b+1+1+1+a) (((((((2^len-1)*2+1)*2+1)*2^b-1)*2*2+1)*2+1)*2^a-1).
Proof.
  unfold LC0,RC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Lemma ROv1 a b len:
  LC1 (2+a) (2+b) |> RC len 0 -->+
  LC0 1 0 |> RC (len+1+1+1+b+1+1+1+a) (((((((2^len-1)*2+1)*2*2+1)*2^b-1)*2*2+1)*2+1)*2^a-1).
Proof.
  unfold LC1,LC0,RC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Lemma LIncs0 n a:
  sideRLs tm' (hLR^^n) (LC0 1 (n+a)) (LC0 (n+1) a).
Proof.
  unfold LC0.
  gen a.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHn (S a)); flia.
  esx.
Qed.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 0 (n+a)) (LC1 n a).
Proof.
  unfold LC1.
  gen a.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHn (S a)); flia.
  esx.
Qed.

Lemma LIncsOv0 a:
  sideRLs tm' (hLR^^(a+1)) (LC0 1 a) (LC1 0 (2+a)).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (LIncs0 a 0); flia.
  unfold LC0,LC1.
  esx.
Qed.

Lemma LIncsOv1 a:
  sideRLs tm' (hLR^^(a+1)) (LC1 0 a) (LC0 1 a).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (LIncs1 a 0); flia.
  unfold LC0,LC1.
  esx.
Qed.

Lemma LIncsOv01 a:
  sideRLs tm' (hLR^^(a*2+4)) (LC0 1 a) (LC0 1 (2+a)).
Proof.
  replace (a*2+4) with ((a+1)+((2+a)+1)) by lia.
  eapply sideRLs_trans_add.
  1: apply LIncsOv0.
  apply LIncsOv1.
Qed.

Lemma LIncsOvs01 a:
  sideRLs tm' (hLR^^(a*(a+1)*2)) (LC0 1 0) (LC0 1 (a*2)).
Proof.
  induction a.
  1: esx.
  replace (S a*(S a+1)*2) with (a*(a+1)*2+(a*2*2+4)) by lia.
  eapply sideRLs_trans_add.
  1: apply IHa.
  apply LIncsOv01.
Qed.

Lemma LIncsOvs01' a c:
  c<=a*2 ->
  sideRLs tm' (hLR^^(a*(a+1)*2+c)) (LC0 1 0) (LC0 (c+1) (a*2-c)).
Proof.
  intros.
  eapply sideRLs_trans_add.
  1: apply LIncsOvs01.
  applys_eq (LIncs0 c (a*2-c)); flia.
Qed.

Lemma LIncsOvs01'' a c:
  c<=2+a*2 ->
  sideRLs tm' (hLR^^(a*(a+1)*2+((a*2+1)+c))) (LC0 1 0) (LC1 (c) (2+a*2-c)).
Proof.
  intros.
  eapply sideRLs_trans_add.
  1: apply LIncsOvs01.
  eapply sideRLs_trans_add.
  1: apply LIncsOv0.
  applys_eq (LIncs1 c (2+a*2-c)); flia.
Qed.

Lemma RIncs len n:
  n<2^len ->
  sideRLs tm (hRL^^n) (RC len n) (RC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    econstructor.
    2: apply IHn; lia.
    unfold sideRL.
    intros.
    apply RBinDec_spec; try assumption.
    es.
Qed.

Lemma Incs_0 n c len:
  c<=n*2 ->
  n*(n+1)*2+c<2^len ->
  LC0 1 0 |> RC len (n*(n+1)*2+c) -->*
  LC0 (c+1) (n*2-c) |> RC len 0.
Proof.
  intros.
  eapply (sideRLs_concat_1 (RIncs len _ _) (LIncsOvs01' _ _ H)).
  Unshelve.
  auto 1.
Qed.

Lemma Incs_1 n c len:
  c<=2+n*2 ->
  n*(n+1)*2+((n*2+1)+c)<2^len ->
  LC0 1 0 |> RC len (n*(n+1)*2+((n*2+1)+c)) -->*
  LC1 c (2+n*2-c) |> RC len 0.
Proof.
  intros.
  eapply (sideRLs_concat_1 (RIncs len _ _) (LIncsOvs01'' _ _ H)).
  Unshelve.
  auto 1.
Qed.

Definition S' '(len,n) := LC0 1 0 |> RC len n.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep0 n c len x a b:
  1<=c ->
  c+1<=n*2 ->
  x=n*(n+1)*2+c ->
  x<2^len ->
  a=c-1 ->
  b=n*2-(c+1) ->
  S' (len,x) -->+
  S' (len+a+b+5,2^(len+a+b)*32-2^(a+b)*8-2^a*5-1).
Proof.
  intros.
  unfold S'.
  subst x.
  follow Incs_0.
  1: lia.
  replace (c+1) with (2+a) by lia.
  replace (n*2-c) with (1+b) by lia.
  follow10 ROv0.
  rw_pa.
  finish.
Qed.

Lemma BigStep1 n c len x a b:
  2<=c<=n*2 ->
  x=n*(n+1)*2+((n*2+1)+c) ->
  x<2^len ->
  a=c-2 ->
  b=n*2-c ->
  S' (len,x) -->+
  S' (len+a+b+6,2^(len+a+b)*64-2^(a+b)*24-2^a*5-1).
Proof.
  intros.
  unfold S'.
  subst x.
  follow Incs_1.
  1: lia.
  replace (2+n*2-c) with (2+b) by lia.
  replace (c) with (2+a) by lia.
  follow10 ROv1.
  rw_pa.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (0+7+1+1+1+1+1+6,(((((0+1)*2^7-1)*2*2+1)*2*2+1)*2+1)*2^6-1).
Proof.
  unfold S',RC.
  rewrite BinDec_mulpow2sub1' by lia.
  rw_Bin.
  all: solve_pow2_lt.
  esx.
Qed.

Definition Config '(l,x) := S' (Z.to_nat l,Z.to_nat x).

Lemma Step l n a r :
  Weak l (input n a r) -> (1<=n)%Z -> (0<=a<=2*n-2)%Z -> (r=1 \/ r=2)%Z ->
  Config (l,input n a r) -->+ Config (length_next l n r,value_next l n a r).
Proof.
  intros W Hn Ha Hr. destruct W as [Hl Hx Hlow Hex]. unfold Config.
  rewrite (nat_output l n a (2*n-2-a)%Z r) by lia.
  assert (Hab : Z.to_nat a+Z.to_nat (2*n-2-a)%Z+2=Z.to_nat n*2).
  { apply Nat2Z.inj. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia. lia. }
  destruct Hr as [-> | ->].
  - eapply BigStep0 with (n:=Z.to_nat n) (c:=Z.to_nat a+1).
    + lia.
    + lia.
    + apply input_nat0; lia.
    + apply bound_nat; lia.
    + lia.
    + lia.
  - eapply BigStep1 with (n:=Z.to_nat n) (c:=Z.to_nat a+2).
    + lia.
    + apply input_nat1; lia.
    + apply bound_nat; lia.
    + lia.
    + lia.
Qed.

Lemma invariant_nonhalt l x : Inv l x -> ~halts tm (Config (l,x)).
Proof.
  apply (progress_nonhalt_cond tm (Z*Z) (l,x) Config (fun '(l,x) => Inv l x)).
  intros [l' x'] HI.
  destruct (next_rule l' x' HI) as [n [a [r [Hn [Ha [Hr ->]]]]]].
  exists (length_next l' n r,value_next l' n a r). split.
  - apply Step; try assumption. apply inv_weak; assumption.
  - apply preserves; try assumption. apply inv_weak; assumption.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (Config (18%Z,260799%Z))).
  apply invariant_nonhalt, initial1.
Qed.

End TM1.


Module TM2.

Definition tm := Eval compute in (TM_from_str "1LB1RA_1RA1LC_1LD0LB_1RE0RF_---1RD_0RE1RA").

Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition RC len n := BinDec [0;1] [1;1] len n ([1]*>0inf).

Notation "l |> r" := (l<*[] {{A}}> r) (at level 30).
Notation "l <| r" := (l <{{B}} []*>r) (at level 30).

Notation hL := (B,[]).
Notation hR := (A,[]).
Notation hLR := [(hL,hR)].
Notation hRL := [(hR,hL)].

Definition tm' := flip tm.

Definition LC0 a b :=
  0inf <* <[1;1]^^a <* <[0;0] <* <[1;1]^^b <* <[1;0;1;1;1].

Definition LC1 a b :=
  0inf <* <[1;1]^^a <* <[0;0] <* <[1;1]^^b <* <[0;1;1;1;1].

Lemma ROv0 a b len:
  LC0 (2+a) (1+b) |> RC len 0 -->+
  LC0 1 0 |> RC (len+1+1+b+1+1+1+a) (((((((2^len-1)*2+1)*2+1)*2^b-1)*2*2+1)*2+1)*2^a-1).
Proof.
  unfold LC0,RC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Lemma ROv1 a b len:
  LC1 (2+a) (2+b) |> RC len 0 -->+
  LC0 1 0 |> RC (len+1+1+1+b+1+1+1+a) (((((((2^len-1)*2+1)*2*2+1)*2^b-1)*2*2+1)*2+1)*2^a-1).
Proof.
  unfold LC1,LC0,RC.
  rw_Bin; solve_pow2_lt.
  es.
Qed.

Lemma LIncs0 n a:
  sideRLs tm' (hLR^^n) (LC0 1 (n+a)) (LC0 (n+1) a).
Proof.
  unfold LC0.
  gen a.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHn (S a)); flia.
  esx.
Qed.

Lemma LIncs1 n a:
  sideRLs tm' (hLR^^n) (LC1 0 (n+a)) (LC1 n a).
Proof.
  unfold LC1.
  gen a.
  induction n; intros.
  1: esx.
  eapply sideRLs_trans_S.
  1: applys_eq (IHn (S a)); flia.
  esx.
Qed.

Lemma LIncsOv0 a:
  sideRLs tm' (hLR^^(a+1)) (LC0 1 a) (LC1 0 (2+a)).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (LIncs0 a 0); flia.
  unfold LC0,LC1.
  esx.
Qed.

Lemma LIncsOv1 a:
  sideRLs tm' (hLR^^(a+1)) (LC1 0 a) (LC0 1 a).
Proof.
  eapply sideRLs_trans_add.
  1: applys_eq (LIncs1 a 0); flia.
  unfold LC0,LC1.
  esx.
Qed.

Lemma LIncsOv01 a:
  sideRLs tm' (hLR^^(a*2+4)) (LC0 1 a) (LC0 1 (2+a)).
Proof.
  replace (a*2+4) with ((a+1)+((2+a)+1)) by lia.
  eapply sideRLs_trans_add.
  1: apply LIncsOv0.
  apply LIncsOv1.
Qed.

Lemma LIncsOvs01 a:
  sideRLs tm' (hLR^^(a*(a+1)*2)) (LC0 1 0) (LC0 1 (a*2)).
Proof.
  induction a.
  1: esx.
  replace (S a*(S a+1)*2) with (a*(a+1)*2+(a*2*2+4)) by lia.
  eapply sideRLs_trans_add.
  1: apply IHa.
  apply LIncsOv01.
Qed.

Lemma LIncsOvs01' a c:
  c<=a*2 ->
  sideRLs tm' (hLR^^(a*(a+1)*2+c)) (LC0 1 0) (LC0 (c+1) (a*2-c)).
Proof.
  intros.
  eapply sideRLs_trans_add.
  1: apply LIncsOvs01.
  applys_eq (LIncs0 c (a*2-c)); flia.
Qed.

Lemma LIncsOvs01'' a c:
  c<=2+a*2 ->
  sideRLs tm' (hLR^^(a*(a+1)*2+((a*2+1)+c))) (LC0 1 0) (LC1 (c) (2+a*2-c)).
Proof.
  intros.
  eapply sideRLs_trans_add.
  1: apply LIncsOvs01.
  eapply sideRLs_trans_add.
  1: apply LIncsOv0.
  applys_eq (LIncs1 c (2+a*2-c)); flia.
Qed.

Lemma RIncs len n:
  n<2^len ->
  sideRLs tm (hRL^^n) (RC len n) (RC len 0).
Proof.
  induction n; intros.
  - esx.
  - cbn[lpow].
    econstructor.
    2: apply IHn; lia.
    unfold sideRL.
    intros.
    apply RBinDec_spec; try assumption.
    es.
Qed.

Lemma Incs_0 n c len:
  c<=n*2 ->
  n*(n+1)*2+c<2^len ->
  LC0 1 0 |> RC len (n*(n+1)*2+c) -->*
  LC0 (c+1) (n*2-c) |> RC len 0.
Proof.
  intros.
  eapply (sideRLs_concat_1 (RIncs len _ _) (LIncsOvs01' _ _ H)).
  Unshelve.
  auto 1.
Qed.

Lemma Incs_1 n c len:
  c<=2+n*2 ->
  n*(n+1)*2+((n*2+1)+c)<2^len ->
  LC0 1 0 |> RC len (n*(n+1)*2+((n*2+1)+c)) -->*
  LC1 c (2+n*2-c) |> RC len 0.
Proof.
  intros.
  eapply (sideRLs_concat_1 (RIncs len _ _) (LIncsOvs01'' _ _ H)).
  Unshelve.
  auto 1.
Qed.

Definition S' '(len,n) := LC0 1 0 |> RC len n.

Ltac rw_pa := repeat rewrite Nat.pow_add_r in *.

Lemma BigStep0 n c len x a b:
  1<=c ->
  c+1<=n*2 ->
  x=n*(n+1)*2+c ->
  x<2^len ->
  a=c-1 ->
  b=n*2-(c+1) ->
  S' (len,x) -->+
  S' (len+a+b+5,2^(len+a+b)*32-2^(a+b)*8-2^a*5-1).
Proof.
  intros.
  unfold S'.
  subst x.
  follow Incs_0.
  1: lia.
  replace (c+1) with (2+a) by lia.
  replace (n*2-c) with (1+b) by lia.
  follow10 ROv0.
  rw_pa.
  finish.
Qed.

Lemma BigStep1 n c len x a b:
  2<=c<=n*2 ->
  x=n*(n+1)*2+((n*2+1)+c) ->
  x<2^len ->
  a=c-2 ->
  b=n*2-c ->
  S' (len,x) -->+
  S' (len+a+b+6,2^(len+a+b)*64-2^(a+b)*24-2^a*5-1).
Proof.
  intros.
  unfold S'.
  subst x.
  follow Incs_1.
  1: lia.
  replace (2+n*2-c) with (2+b) by lia.
  replace (c) with (2+a) by lia.
  follow10 ROv1.
  rw_pa.
  finish.
Qed.

Lemma init:
  c0 -->*
  S' (3+1+3+1,(((2^3-1)*2+1)*2^3-1)*2).
Proof.
  unfold S',RC.
  rw_Bin.
  all: solve_pow2_lt.
  esx.
Qed.

Definition Config '(l,x) := S' (Z.to_nat l,Z.to_nat x).

Lemma Step l n a r :
  Weak l (input n a r) -> (1<=n)%Z -> (0<=a<=2*n-2)%Z -> (r=1 \/ r=2)%Z ->
  Config (l,input n a r) -->+ Config (length_next l n r,value_next l n a r).
Proof.
  intros W Hn Ha Hr. destruct W as [Hl Hx Hlow Hex]. unfold Config.
  rewrite (nat_output l n a (2*n-2-a)%Z r) by lia.
  assert (Hab : Z.to_nat a+Z.to_nat (2*n-2-a)%Z+2=Z.to_nat n*2).
  { apply Nat2Z.inj. rewrite !Nat2Z.inj_add, !Nat2Z.inj_mul.
    rewrite !Z2Nat.id by lia. lia. }
  destruct Hr as [-> | ->].
  - eapply BigStep0 with (n:=Z.to_nat n) (c:=Z.to_nat a+1).
    + lia.
    + lia.
    + apply input_nat0; lia.
    + apply bound_nat; lia.
    + lia.
    + lia.
  - eapply BigStep1 with (n:=Z.to_nat n) (c:=Z.to_nat a+2).
    + lia.
    + apply input_nat1; lia.
    + apply bound_nat; lia.
    + lia.
    + lia.
Qed.

Lemma invariant_nonhalt l x : Inv l x -> ~halts tm (Config (l,x)).
Proof.
  apply (progress_nonhalt_cond tm (Z*Z) (l,x) Config (fun '(l,x) => Inv l x)).
  intros [l' x'] HI.
  destruct (next_rule l' x' HI) as [n [a [r [Hn [Ha [Hr ->]]]]]].
  exists (length_next l' n r,value_next l' n a r). split.
  - apply Step; try assumption. apply inv_weak; assumption.
  - apply preserves; try assumption. apply inv_weak; assumption.
Qed.

Lemma enter_weak : c0 -->* Config (31%Z,2144731135%Z).
Proof.
  change (c0 -->* Config (length_next 8 10 1,value_next 8 10 17 1)).
  unfold Config. rewrite (nat_output 8 10 17 1 1) by lia.
  follow init.
  apply progress_evstep.
  apply (BigStep0 10 18 8 238 17 1); lia.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply enter_weak|].
  change (~halts tm (Config (31%Z,input 32746 64610 1))).
  eapply multistep_nonhalt.
  - apply progress_evstep, Step; [exact initial2_weak|lia|lia|auto].
  - apply invariant_nonhalt, preserves; [exact initial2_weak|lia|lia|auto].
Qed.

End TM2.
