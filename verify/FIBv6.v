From BusyCoq Require Import Individual62 Longitudinal ES_v3.
Require Import String List Lia ZifyNat Bool.Bool btauto.Btauto NArith PeanoNat Wf_nat.
Import ListNotations.

Module PrefixXor.
Local Open Scope nat_scope.
Fixpoint integral (f:nat->bool) n :=
  match n with 0 => f 0 | S n => xorb (integral f n) (f (S n)) end.
Fixpoint row t (f:nat->bool) : nat->bool :=
  match t with 0 => f | S t => integral (row t f) end.

Lemma integral_ext f g n :
  (forall j, j<=n -> f j=g j) -> integral f n=integral g n.
Proof.
  induction n; cbn; intro H; [apply H; lia|].
  rewrite IHn, H; auto; intros; apply H; lia.
Qed.
Lemma local_rule f t n :
  row t f (S n)=xorb (row (S t) f (S n)) (row (S t) f n).
Proof. cbn[row integral]; btauto. Qed.
Lemma twice_shift f n :
  integral (integral f) (S (S n))=
  xorb (integral (integral f) n) (f (S (S n))).
Proof. cbn[integral]; btauto. Qed.
Lemma twice f n :
  integral (integral f) (n*2)=integral (fun j=>f (j*2)) n /\
  integral (integral f) (1+n*2)=integral (fun j=>f (1+j*2)) n.
Proof.
  induction n as [|n [IH0 IH1]].
  - cbn[integral Nat.mul Nat.add]; split; btauto.
  - cbn[Nat.mul Nat.add]; split; rewrite twice_shift.
    + rewrite IH0; reflexivity.
    + cbn[Nat.add] in IH1; rewrite IH1; reflexivity.
Qed.
Lemma row_double t f n :
  row (t*2) f (n*2)=row t (fun j=>f (j*2)) n /\
  row (t*2) f (1+n*2)=row t (fun j=>f (1+j*2)) n.
Proof.
  gen n; induction t as [|t IH]; intro n; [split; reflexivity|].
  change (integral (integral (row (t*2) f)) (n*2)=
            integral (row t (fun j=>f (j*2))) n /\
          integral (integral (row (t*2) f)) (1+n*2)=
            integral (row t (fun j=>f (1+j*2))) n).
  destruct (twice (row (t*2) f) n) as [E0 E1]; rewrite E0,E1.
  split; apply integral_ext; intros j _; [apply (proj1 (IH j))|apply (proj2 (IH j))].
Qed.

Lemma integral_xor f g n :
  integral (fun j=>xorb (f j) (g j)) n=xorb (integral f n) (integral g n).
Proof. induction n; cbn; [reflexivity|rewrite IHn; btauto]. Qed.
Lemma row_xor t f g n :
  row t (fun j=>xorb (f j) (g j)) n=xorb (row t f n) (row t g n).
Proof.
  gen n; induction t; intro n; [reflexivity|].
  change (integral (row t (fun j=>xorb (f j) (g j))) n=
    xorb (integral (row t f) n) (integral (row t g) n)).
  rewrite <-(integral_xor (row t f) (row t g)); apply integral_ext; auto.
Qed.
Lemma row_ext f g t n :
  (forall j, j<=n -> f j=g j) -> row t f n=row t g n.
Proof.
  gen n; induction t; intros n H; [apply H; lia|].
  apply integral_ext; intros j Hj; apply IHt; intros; apply H; lia.
Qed.
Lemma integral_false n : integral (fun _=>false) n=false.
Proof. induction n; cbn; [reflexivity|rewrite IHn; reflexivity]. Qed.
Lemma integral_pairs f n :
  integral f (1+n*2)=integral (fun j=>xorb (f (j*2)) (f (1+j*2))) n.
Proof.
  induction n; [reflexivity|].
  change (xorb (xorb (integral f (1+n*2)) (f (S n*2))) (f (1+S n*2))=
    integral (fun j=>xorb (f (j*2)) (f (1+j*2))) (S n)).
  rewrite IHn; cbn[integral]; btauto.
Qed.

(* Coefficients of (1+X)^(-1-t), without a power-series library. *)
Definition coeff t n := row t (fun _=>true) n.
Lemma coeff_double t n :
  coeff (t*2) (n*2)=coeff t n /\ coeff (t*2) (1+n*2)=coeff t n.
Proof. apply row_double. Qed.
Lemma coeff_odd_odd t n : coeff (1+t*2) (1+n*2)=false.
Proof.
  unfold coeff; change (integral (row (t*2) (fun _=>true)) (1+n*2)=false).
  rewrite integral_pairs, <-integral_false with (n:=n); apply integral_ext.
  intros j _; destruct (coeff_double t j) as [E0 E1].
  unfold coeff in E0,E1; rewrite E0,E1; btauto.
Qed.
Lemma coeff_odd_even t n : coeff (1+t*2) (n*2)=coeff t n.
Proof.
  assert (E: xorb (coeff (1+t*2) (n*2)) (coeff (t*2) (1+n*2))=
    coeff (1+t*2) (1+n*2)) by reflexivity.
  rewrite coeff_odd_odd, (proj2 (coeff_double t n)) in E; apply xorb_eq, E.
Qed.

Fixpoint morse_pos p :=
  match p with xH=>false | xO p=>morse_pos p | xI p=>negb (morse_pos p) end.
Definition morse n := match N.of_nat n with N0=>true | Npos p=>morse_pos p end.
Lemma morse_double n : morse (n*2)=morse n.
Proof.
  unfold morse; rewrite Nat.mul_comm, Nat2N.inj_double; destruct (N.of_nat n); reflexivity.
Qed.
Lemma morse_odd n : morse (1+n*2)=xorb (morse n) true.
Proof.
  unfold morse; rewrite Nat.mul_comm; change (match N.of_nat (S (2*n)) with
    N0=>true | Npos p=>morse_pos p end=
    xorb (match N.of_nat n with N0=>true | Npos p=>morse_pos p end) true).
  rewrite Nat2N.inj_succ_double; destruct (N.of_nat n); cbn; btauto.
Qed.
Definition Z t n := row t morse n.
Lemma Z_double t n :
  Z (t*2) (n*2)=Z t n /\ Z (t*2) (1+n*2)=xorb (Z t n) (coeff t n).
Proof.
  unfold Z,coeff; destruct (row_double t morse n) as [E0 E1]; rewrite E0,E1.
  split; [|rewrite <-row_xor]; apply row_ext; intros; auto using morse_double,morse_odd.
Qed.
Lemma Z_odd_odd t n : Z (1+t*2) (1+n*2)=coeff (S t) n.
Proof.
  unfold Z; change (integral (row (t*2) morse) (1+n*2)=integral (row t (fun _=>true)) n).
  rewrite integral_pairs; apply integral_ext; intros j _.
  destruct (Z_double t j) as [E0 E1]; unfold Z,coeff in E0,E1; rewrite E0,E1; btauto.
Qed.
Lemma Z_odd_even t n :
  Z (1+t*2) (n*2)=xorb (Z t n) (xorb (coeff t n) (coeff (S t) n)).
Proof.
  assert (E: xorb (Z (1+t*2) (n*2)) (Z (t*2) (1+n*2))=
    Z (1+t*2) (1+n*2)) by reflexivity.
  rewrite Z_odd_odd, (proj2 (Z_double t n)) in E; rewrite <-E; btauto.
Qed.

Lemma binary_ind (P:nat->Prop) : P 0 ->
  (forall n, P n -> P (n*2)) -> (forall n, P n -> P (1+n*2)) -> forall n, P n.
Proof.
  intros H0 H2 H1 n; rewrite <-(Nat2N.id n).
  generalize (N.of_nat n); intro x; induction x using N.binary_ind.
  - exact H0.
  - rewrite N2Nat.inj_double, Nat.mul_comm; apply H2, IHx.
  - rewrite N2Nat.inj_succ_double, Nat.mul_comm; apply H1, IHx.
Qed.
Lemma coeff_cross n : coeff (S n) (1+n*2)=false.
Proof.
  induction n using binary_ind; [reflexivity| |].
  - change (coeff (1+n*2) (1+(n*2)*2)=false); apply coeff_odd_odd.
  - replace (S (1+n*2)) with (S n*2) by lia.
    rewrite (proj2 (coeff_double (S n) (1+n*2))); exact IHn.
Qed.
Lemma coeff_next n : coeff (S n) (2+n*2)=coeff n (2+n*2).
Proof.
  change (xorb (coeff (S n) (1+n*2)) (coeff n (2+n*2))=coeff n (2+n*2)).
  rewrite coeff_cross; reflexivity.
Qed.
Lemma diagonals t :
  Z t (t*2)=coeff t (t*2) /\ Z t (1+t*2)=false /\ Z t (2+t*2)=false.
Proof.
  induction t as [|t [IH0 [IH1 IH2]]|t [IH0 [IH1 IH2]]] using binary_ind.
  - repeat split; reflexivity.
  - rewrite (proj1 (Z_double t (t*2))), (proj1 (coeff_double t (t*2))),
      (proj2 (Z_double t (t*2))), IH0.
    replace (2+t*2*2) with ((1+t*2)*2) by lia.
    rewrite (proj1 (Z_double t (1+t*2))), IH1; repeat split; try reflexivity; btauto.
  - replace (2+(1+t*2)*2) with ((2+t*2)*2) by lia.
    rewrite Z_odd_even, Z_odd_odd, Z_odd_even, coeff_odd_even,
      IH1, IH2, coeff_cross, coeff_next.
    repeat split; btauto.
Qed.

Definition good t := coeff t (t*2).
Lemma good_double t : good (t*2)=good t.
Proof. apply (proj1 (coeff_double t (t*2))). Qed.
Lemma good_four_one t : good (1+t*4)=good t.
Proof.
  unfold good; replace (1+t*4) with (1+(t*2)*2) by lia.
  rewrite coeff_odd_even, (proj2 (coeff_double t (t*2))); reflexivity.
Qed.
Lemma good_four_three t : good (3+t*4)=false.
Proof.
  unfold good; replace (3+t*4) with (1+(1+t*2)*2) by lia.
  rewrite coeff_odd_even, coeff_odd_odd; reflexivity.
Qed.
Lemma parity_cases n : exists k, n=k*2 \/ n=1+k*2.
Proof.
  destruct (Nat.Even_or_Odd n) as [[k H]|[k H]]; exists k; [left|right]; lia.
Qed.

Record platform t lo hi : Prop := {
  platform_bits : forall j, lo<=j<=hi -> Z t j=true;
  platform_coeff : forall j, lo<=j<hi -> coeff t j=false
}.
Lemma platform_double t lo hi : platform t lo hi -> platform (t*2) (lo*2) (hi*2).
Proof.
  intros [HZ HC]; constructor; intros j Hj; destruct (parity_cases j) as [k [-> | ->]].
  - rewrite (proj1 (Z_double t k)); apply HZ; lia.
  - rewrite (proj2 (Z_double t k)), HZ, HC by lia; reflexivity.
  - rewrite (proj1 (coeff_double t k)); apply HC; lia.
  - rewrite (proj2 (coeff_double t k)); apply HC; lia.
Qed.
Lemma platform_base u : good u=true -> platform (1+u*4) (1+u*8) (2+u*8).
Proof.
  intro H; constructor; intros j Hj.
  - assert (j=1+u*8 \/ j=2+u*8) as [-> | ->] by lia.
    + replace (1+u*4) with (1+(u*2)*2) by lia.
      replace (1+u*8) with (1+(u*4)*2) by lia.
      rewrite Z_odd_odd.
      replace (u*4) with ((u*2)*2) by lia.
      change (coeff (1+u*2) ((u*2)*2)=true); rewrite coeff_odd_even; exact H.
    + replace (2+u*8) with ((1+u*4)*2) by lia.
      rewrite (proj1 (diagonals (1+u*4))); change (good (1+u*4)=true).
      rewrite good_four_one; exact H.
  - assert (j=1+u*8) by lia; subst j.
    replace (1+u*4) with (1+(u*2)*2) by lia.
    replace (1+u*8) with (1+(u*4)*2) by lia; apply coeff_odd_odd.
Qed.
Lemma platform_scale k t lo hi :
  platform t lo hi -> platform (t*4^k) (lo*4^k) (hi*4^k).
Proof.
  induction k; intro H.
  - cbn[Nat.pow]; rewrite !Nat.mul_1_r; exact H.
  - specialize (IHk H); apply platform_double, platform_double in IHk.
    applys_eq IHk; cbn[Nat.pow]; nia.
Qed.

(* 4^k=1+3*gap k. The two possible low-bit scales are 4^k and 2*4^k;
   this keeps division and modulus out of the interval proof. *)
Fixpoint gap k := match k with 0=>0 | S k=>1+gap k*4 end.
Lemma gap_power k : 4^k=1+gap k*3.
Proof. induction k; cbn[Nat.pow gap]; lia. Qed.
Lemma gap_good k : good (gap k)=true.
Proof. induction k; [reflexivity|cbn[gap]; rewrite good_four_one; exact IHk]. Qed.
Lemma gap_pred_good k : 0<gap k -> good (gap k-1)=true.
Proof.
  destruct k; [cbn; lia|]; intros _; cbn[gap].
  replace (1+gap k*4-1) with ((gap k*2)*2) by lia.
  rewrite !good_double; apply gap_good.
Qed.
Lemma gap_twice_pred_good k : 0<gap k -> good (gap k*2-1)=true.
Proof.
  destruct k; [cbn; lia|]; intros _; cbn[gap].
  replace ((1+gap k*4)*2-1) with (1+(gap k*2)*4) by lia.
  rewrite good_four_one, good_double; apply gap_good.
Qed.
Lemma gap_prefix_good k u : good u=true -> good (u*2*4^k+gap k)=true.
Proof.
  intro H; induction k.
  - cbn[Nat.pow gap]; rewrite Nat.add_0_r, Nat.mul_1_r, good_double; exact H.
  - replace (u*2*4^(S k)+gap (S k)) with (1+(u*2*4^k+gap k)*4)
      by (cbn[Nat.pow gap]; nia).
    rewrite good_four_one; exact IHk.
Qed.
Lemma good_decompose d : 0<d -> good d=true ->
  exists u k, good u=true /\ (d=(1+u*4)*4^k \/ d=((1+u*4)*4^k)*2).
Proof.
  induction d using binary_ind; intros Hd H.
  - lia.
  - rewrite good_double in H; destruct IHd as [u [k [Hu [E|E]]]]; try lia; auto.
    + exists u,k; auto.
    + exists u,(S k); split; [exact Hu|left]; cbn[Nat.pow]; nia.
  - destruct (parity_cases d) as [u [-> | ->]].
    + replace (1+u*2*2) with (1+u*4) in * by lia.
      rewrite good_four_one in H; exists u,0; split; [exact H|left]; cbn; lia.
    + replace (1+(1+u*2)*2) with (3+u*4) in H by lia.
      rewrite good_four_three in H; discriminate.
Qed.

Lemma good_interval d : 0<d -> good d=true -> exists a L,
  d=a+1+L /\ L<=a /\ good a=true /\ good L=true /\
  (0<L -> good (L-1)=true) /\
  (forall j, (a+1)*2<=j+L+1 -> j<=d*2 -> Z d j=true).
Proof.
  intros Hd H; destruct (good_decompose _ Hd H) as [u [k [Hu [-> | ->]]]];
    pose proof (gap_power k) as HQ;
    pose proof (gap_prefix_good k u Hu) as HA;
    pose proof (platform_scale k _ _ _ (platform_base u Hu)) as HP.
  - exists ((u*2*4^k+gap k)*2),(gap k); repeat split.
    + nia.
    + lia.
    + rewrite good_double; exact HA.
    + apply gap_good.
    + apply gap_pred_good.
    + intros j Hj Hmax; apply (platform_bits _ _ _ HP); nia.
  - exists (1+(u*2*4^k+gap k)*4),(gap k*2); repeat split.
    + nia.
    + lia.
    + rewrite good_four_one; exact HA.
    + rewrite good_double; apply gap_good.
    + intro HL; apply gap_twice_pred_good; lia.
    + intros j Hj Hmax; apply (platform_bits _ _ _ (platform_double _ _ _ HP)); nia.
Qed.

Definition duplicate (f:nat->bool) n := f (Nat.div2 n).
Lemma duplicate_even f n : duplicate f (n*2)=f n.
Proof. unfold duplicate; rewrite Nat.mul_comm,Nat.div2_double; reflexivity. Qed.
Lemma duplicate_odd f n : duplicate f (1+n*2)=f n.
Proof. unfold duplicate; rewrite Nat.mul_comm; apply f_equal, Nat.div2_succ_double. Qed.
Lemma duplicate_rows f t n :
  row (t*2) (duplicate f) (n*2)=row t f n /\
  row (t*2) (duplicate f) (1+n*2)=row t f n.
Proof.
  destruct (row_double t (duplicate f) n) as [E0 E1]; rewrite E0,E1.
  split; apply row_ext; intros; auto using duplicate_even,duplicate_odd.
Qed.
Lemma duplicate_platform d a L :
  (forall j, (a+1)*2<=j+L+1 -> j<=d*2 -> Z d j=true) ->
  forall j, 3+a*4<=j+(L*2+1) -> j<=1+d*4 -> row (d*2) (duplicate morse) j=true.
Proof.
  intros H j Hmin Hmax; destruct (parity_cases j) as [k [-> | ->]].
  - rewrite (proj1 (duplicate_rows morse d k)); apply H; lia.
  - rewrite (proj2 (duplicate_rows morse d k)); apply H; lia.
Qed.
Lemma good_power k : good (4^k)=true /\ k<4^k.
Proof.
  induction k as [|k [IH Hk]]; [split; [reflexivity|lia]|].
  cbn[Nat.pow]; split; [|lia].
  replace (4*4^k) with ((4^k*2)*2) by lia; rewrite !good_double; exact IH.
Qed.

(* A constant platform at the later time protects the whole shrinking
   triangle. This replaces the formal-power-series notation in the note. *)
Lemma plateau f s t lo :
  (forall j, lo<=j<=lo+1+s -> row (t+1+s) f j=true) ->
  row t f (lo+1+s)=false.
Proof.
  gen t lo; induction s as [|s IH]; intros t lo H.
  - replace (lo+1+0) with (S lo) by lia; rewrite local_rule.
    replace (S t) with (t+1+0) by lia; rewrite !H by lia; reflexivity.
  - assert (E0: row (S t) f (lo+1+s)=false).
    { apply IH; intros j Hj.
      replace (S t+1+s) with (t+1+S s) by lia; apply H; lia. }
    assert (E1: row (S t) f (S lo+1+s)=false).
    { apply IH; intros j Hj.
      replace (S t+1+s) with (t+1+S s) by lia; apply H; lia. }
    replace (lo+1+S s) with (S (lo+1+s)) by lia.
    rewrite local_rule, E0.
    replace (S (lo+1+s)) with (S lo+1+s) by lia; rewrite E1; reflexivity.
Qed.
Lemma plateau_before f d m L : L<=m -> L<=d ->
  (forall j, m<=j+L -> j<=m -> row d f j=true) ->
  forall s, 1<=s<=L -> row (d-s) f m=false.
Proof.
  intros Hm Hd H s Hs.
  replace m with (m-s+1+(s-1)) by lia; apply plateau.
  intros j Hj; replace (d-s+1+(s-1)) with d by lia; apply H; lia.
Qed.

Fixpoint window (f:nat->bool) a n :=
  match n with 0 => [] | S n => f a::window f (S a) n end.
Lemma window_length f a n : length (window f a n)=n.
Proof. gen a; induction n; cbn; auto. Qed.
Lemma window_app f a n m : window f a (n+m)=window f a n++window f (a+n) m.
Proof.
  gen a; induction n; intro a; cbn[window Nat.add];
    [rewrite Nat.add_0_r; reflexivity|rewrite IHn,Nat.add_succ_r; reflexivity].
Qed.
Lemma row_zero f t : row t f 0=f 0.
Proof. induction t; cbn[row integral]; auto. Qed.
Lemma window_true f a n :
  (forall j, a<=j<a+n -> f j=true) -> window f a n=repeat true n.
Proof.
  gen a; induction n; cbn; intros a H; [reflexivity|].
  rewrite H by lia; f_equal; apply IHn; intros; apply H; lia.
Qed.
Lemma forward_rule f t n :
  xorb (row (S t) f n) (row t f (S n))=row (S t) f (S n).
Proof. reflexivity. Qed.
End PrefixXor.

(* REST3_20261013, fractal in bouncer TM1. The complete informal
   closure argument is in REST3_FIB1_CLOSURE.txt. *)
Module TM1.
Definition tm := Eval compute in (TM_from_str "1RB0LB_1LC1LB_1RD1LA_0RE0RE_0RA1RF_---1RD").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).

Notation h0 := [((A,<[1;0;0]),(B,[]))].
Notation h1 := [((D,<[0;1;1]),(C,[]))].
Notation h2 := [((F,<[0;1]),(C,[]))].
Notation w0 := [1;1;1].
Notation w1 := [1;0;1].
Notation wm := [0;1].

Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.

Lemma bit00 : segRLs tm h0 h0 w0 w0.
Proof. finite_rule. Qed.
Lemma bit01 : segRLs tm h0 h1 w1 w1.
Proof. finite_rule. Qed.
Lemma bit10 : segRLs tm h1 h1 w0 w1.
Proof. finite_rule. Qed.
Lemma bit11 : segRLs tm h1 h0 w1 w0.
Proof. finite_rule. Qed.

Lemma mark_passive : segRLs tm h0 h1 wm wm.
Proof. finite_rule. Qed.
Lemma mark_active : segRLs tm h1 h2 wm w1.
Proof. finite_rule. Qed.
Lemma clear0 : segRLs tm h2 h2 w0 w1.
Proof. finite_rule. Qed.
Lemma clear1 : segRLs tm h2 h2 w1 w1.
Proof. finite_rule. Qed.

Notation edge := ([1;0] *> 0inf).
Ltac finite_side := repeat rewrite <-Str_app_assoc;
  apply BoundedConfig.sideRLs_c_spec with (T:=100); reflexivity.
Lemma edge0 : sideRLs tm h0 edge (wm *> w0 *> edge).
Proof. finite_side. Qed.
Lemma edge1 : sideRLs tm h1 edge (w1 *> w0 *> edge).
Proof. finite_side. Qed.
Lemma edge2 : sideRLs tm h2 edge (w1 *> w0 *> edge).
Proof. finite_side. Qed.

Definition left := 0inf <* [1].
Lemma left_return : sideRLs (flip tm) [((C,[]),(D,<[0;1;1]))] left left.
Proof. unfold left; finite_side. Qed.
Lemma init : c0 -->* left {{{ ((D,<[0;1;1]),R) }}} edge.
Proof. esx. Qed.

Inductive signal := H0 | H1 | Clear.
Inductive cell := Zero | One | Mark.
Definition head s : list (DH0*DH0) := match s with H0 => h0 | H1 => h1 | Clear => h2 end.
Definition word x : list Sym := match x with Zero => w0 | One => w1 | Mark => wm end.
Definition action s x :=
  match s,x with
  | H0,Zero => Some (H0,Zero) | H0,One => Some (H1,One)
  | H1,Zero => Some (H1,One) | H1,One => Some (H0,Zero)
  | H0,Mark => Some (H1,Mark) | H1,Mark => Some (Clear,One)
  | Clear,Zero | Clear,One => Some (Clear,One)
  | Clear,Mark => None
  end.
Definition edge_step s := match s with H0 => [Mark;Zero] | _ => [One;Zero] end.
Fixpoint next s xs :=
  match xs with
  | [] => Some (edge_step s)
  | x::xs =>
    match action s x with
    | None => None
    | Some (s',y) =>
      match next s' xs with None => None | Some ys => Some (y::ys) end
    end
  end.
Fixpoint tape xs := match xs with [] => edge | x::xs => word x *> tape xs end.

Lemma action_spec s x s' y : action s x = Some (s',y) ->
  segRLs tm (head s) (head s') (word x) (word y).
Proof.
  destruct s,x; cbn; intro H; inverts H;
    auto using bit00,bit01,bit10,bit11,mark_passive,mark_active,clear0,clear1.
Qed.
Lemma next_spec xs s ys : next s xs = Some ys ->
  sideRLs tm (head s) (tape xs) (tape ys).
Proof.
  gen s ys; induction xs as [|x xs IH]; intros s ys H.
  - destruct s; inverts H; cbn; auto using edge0,edge1,edge2.
  - cbn in H; destruct (action s x) as [[s' y]|] eqn:E; try discriminate.
    destruct (next s' xs) as [zs|] eqn:F; inverts H; cbn.
    eapply segRLs_sideRLs_concat; [apply action_spec, E|eauto].
Qed.

Definition config xs := left {{{ ((D,<[0;1;1]),R) }}} tape xs.
Lemma round_spec xs ys : next H1 xs = Some ys -> config xs -->+ config ys.
Proof.
  intro H; unfold config; eapply progress_trans.
  - apply sideRLs_1, (next_spec _ _ _ H).
  - apply sideRLs_1L, left_return.
Qed.

Definition bit (b:bool) := if b then One else Zero.
Definition phase (b:bool) := if b then H1 else H0.
Fixpoint scan (b:bool) xs :=
  match xs with [] => [] | x::xs =>
    let y:=xorb b x in y::scan y xs end.
Fixpoint lastbit (b:bool) xs :=
  match xs with [] => b | x::xs => lastbit (xorb b x) xs end.

Lemma next_prefix xs b tail ys :
  next (phase (lastbit b xs)) tail = Some ys ->
  next (phase b) (map bit xs++tail) = Some (map bit (scan b xs)++ys).
Proof.
  gen b ys; induction xs as [|x xs IH]; intros b ys H; cbn in *.
  - exact H.
  - specialize (IH _ _ H); destruct b,x; cbn in *; rewrite IH; reflexivity.
Qed.
Lemma clear_plain xs :
  next Clear (map bit xs) = Some (repeat One (length xs)++[One;Zero]).
Proof.
  induction xs as [|x xs IH]; [reflexivity|].
  destruct x; cbn in *; rewrite IH; reflexivity.
Qed.

Lemma next_length xs s ys : next s xs=Some ys -> length ys=length xs+2.
Proof.
  gen s ys; induction xs as [|x xs IH]; intros s ys H.
  - destruct s; inverts H; reflexivity.
  - cbn in H; destruct (action s x) as [[s' y]|] eqn:E; try discriminate.
    destruct (next s' xs) as [zs|] eqn:F; inverts H; cbn.
    rewrite (IH _ _ F); reflexivity.
Qed.

Definition normal xs := flat_map (fun b=>word (bit b)) xs.
Lemma plain_block xs b :
  segRLs tm (head (phase b)) (head (phase (lastbit b xs)))
    (normal xs) (normal (scan b xs)).
Proof.
  gen b; induction xs as [|x xs IH]; intro b; cbn[normal flat_map scan lastbit].
  - apply segRLs_nil.
  - destruct b,x; cbn[phase head bit xorb]; eapply segRLs_concat;
      first [apply bit00|apply bit01|apply bit10|apply bit11|
        exact (IH false)|exact (IH true)].
Qed.

Import PrefixXor.
Lemma scan_window f t n a :
  scan (row (S t) f a) (window (row t f) (S a) n)=window (row (S t) f) (S a) n.
Proof.
  gen a; induction n; intro a; [reflexivity|].
  cbn[window scan]; rewrite forward_rule; f_equal; apply IHn.
Qed.
Lemma lastbit_window f t n a :
  lastbit (row (S t) f a) (window (row t f) (S a) n)=row (S t) f (a+n).
Proof.
  gen a; induction n; intro a; [rewrite Nat.add_0_r; reflexivity|].
  cbn[window lastbit]; rewrite forward_rule, IHn; f_equal; lia.
Qed.
Lemma plain_window f t n a :
  segRLs tm (head (phase (row (S t) f a))) (head (phase (row (S t) f (a+n))))
    (normal (window (row t f) (S a) n)) (normal (window (row (S t) f) (S a) n)).
Proof.
  rewrite <-(scan_window f t n a), <-(lastbit_window f t n a); apply plain_block.
Qed.
Fixpoint signals f a t k :=
  match k with O => [] | S k => head (phase (row (S t) f a))++signals f a (S t) k end.
Lemma rectangle f a n k t :
  segRLs tm (signals f a t k) (signals f (a+n) t k)
    (normal (window (row t f) (S a) n)) (normal (window (row (t+k) f) (S a) n)).
Proof.
  gen t; induction k; intro t.
  - rewrite Nat.add_0_r; constructor.
  - cbn[signals]; eapply segRLs_trans; [apply plain_window|].
    applys_eq (IHk (S t)); flia.
Qed.

Local Open Scope nat_scope.
Definition front f t n := map bit (window (row t f) 1 n).
Lemma next_front f t n xs ys : f 0=true ->
  next (phase (row (S t) f n)) xs=Some ys ->
  next H1 (front f t n++xs)=Some (front f (S t) n++ys).
Proof.
  intros Hf H; unfold front.
  rewrite <-(scan_window f t n 0).
  replace H1 with (phase (row (S t) f 0)) by (rewrite row_zero,Hf; reflexivity).
  apply next_prefix; rewrite lastbit_window; exact H.
Qed.
Lemma next_plain f t n : f 0=true -> next H1 (front f t n)=
  Some (front f (S t) n++edge_step (phase (row (S t) f n))).
Proof.
  intro Hf; rewrite <-(app_nil_r (front f t n)); apply next_front; [exact Hf|reflexivity].
Qed.
Lemma front_pad f t n k :
  (forall j, n<j<=n+k+1 -> row t f j=true) -> row t f (n+k+2)=false ->
  front f t (n+k+2)=front f t n++repeat One k++[One;Zero].
Proof.
  intros H H0; unfold front; replace (n+k+2) with (n+(k+2)) by lia.
  rewrite window_app,map_app,window_app,map_app.
  rewrite (window_true (row t f) (1+n) k) by (intros; apply H; lia).
  rewrite map_repeat; cbn[window map bit].
  rewrite H by lia.
  replace (S (1+n+k)) with (n+k+2) by lia; rewrite H0; reflexivity.
Qed.
Lemma before_mark f t n b : row t f (S n)=false ->
  row (S t) f (S n)=b -> row (S t) f n=b.
Proof. intros H <-; rewrite <-forward_rule,H,xorb_false_r; reflexivity. Qed.
Lemma next_passive f t n xs ys : f 0=true ->
  row t f (S n)=false -> row (S t) f (S n)=false ->
  next H1 xs=Some ys ->
  next H1 (front f t n++Mark::xs)=Some (front f (S t) n++Mark::ys).
Proof.
  intros Hf H0 H1 H; apply next_front; [exact Hf|].
  rewrite (before_mark _ _ _ _ H0 H1); cbn[phase next action]; rewrite H; reflexivity.
Qed.
Lemma next_active f t n xs : f 0=true ->
  row t f (S n)=false -> row (S t) f (S n)=true ->
  next H1 (front f t n++Mark::map bit xs)=
    Some (front f (S t) n++One::repeat One (length xs)++[One;Zero]).
Proof.
  intros Hf H0 H1; apply next_front; [exact Hf|].
  rewrite (before_mark _ _ _ _ H0 H1); cbn[phase next action]; rewrite clear_plain; reflexivity.
Qed.

Inductive rounds : nat->list cell->list cell->Prop :=
| rounds_0 xs : rounds 0 xs xs
| rounds_S n xs ys zs : next H1 xs=Some ys -> rounds n ys zs -> rounds (S n) xs zs.
Lemma rounds_trans n m xs ys zs : rounds n xs ys -> rounds m ys zs -> rounds (n+m) xs zs.
Proof. intros H; induction H; intro Hm; cbn; [exact Hm|econstructor; eauto]. Qed.
Lemma rounds_passive f t n k xs ys : f 0=true -> rounds k xs ys ->
  (forall j, t<=j<=t+k -> row j f (S n)=false) ->
  rounds k (front f t n++Mark::xs) (front f (t+k) n++Mark::ys).
Proof.
  intros Hf H; gen t; induction H; intros t Hz.
  - rewrite Nat.add_0_r; constructor.
  - replace (t+S n0) with (S t+n0) by lia.
    econstructor; [apply next_passive; eauto; apply Hz; lia|].
    apply IHrounds; intros; apply Hz; lia.
Qed.
Lemma rounds_length n xs ys : rounds n xs ys -> length ys=length xs+n*2.
Proof. intro H; induction H; [cbn; lia|rewrite IHrounds,(next_length _ _ _ H); lia]. Qed.

(* One mother marker surrounds an independently evolving smaller tail.
   The tail is required to be plain only when the marker activates. *)
Lemma episode f a n k xs : f 0=true ->
  (forall j, a<=j<=a+1+k -> row j f (S n)=false) ->
  row (a+k+2) f (S n)=true -> rounds k [Zero] (map bit xs) ->
  rounds (k+2) (front f a n)
    (front f (a+k+2) n++repeat One (length xs+1)++[One;Zero]).
Proof.
  intros Hf Hz Ha Htail; replace (k+2) with (S (k+1)) by lia.
  eapply rounds_S with (ys:=front f (S a) n++Mark::[Zero]).
  - rewrite next_plain by exact Hf.
    rewrite (before_mark f a n false) by (apply Hz; lia); reflexivity.
  - eapply rounds_trans.
    + apply rounds_passive; [exact Hf|exact Htail|]; intros; apply Hz; lia.
    + replace (a+k+2) with (S (S a+k)) in * by lia.
      replace (length xs+1) with (S (length xs)) by lia; cbn[repeat].
      econstructor; [apply next_active; [exact Hf|apply Hz; lia|exact Ha]|constructor].
Qed.

Lemma clean_step f a n : f 0=true -> row a f (S n)=false ->
  row (S a) f (S n)=true -> row (S a) f (n+2)=false ->
  rounds 1 (front f a n) (front f (S a) (n+2)).
Proof.
  intros Hf H0 H1 H2.
  assert (E: front f (S a) (n+2)=front f (S a) n++[One;Zero]).
  { replace (n+2) with (n+0+2) by lia; apply front_pad; [|now rewrite Nat.add_0_r].
    intros j Hj; replace j with (S n) by lia; exact H1. }
  econstructor; [|constructor]; rewrite E,next_plain by exact Hf.
  rewrite (before_mark _ _ _ _ H0 H1); reflexivity.
Qed.

Definition auxiliary t := front morse t (1+t*2).
Lemma auxiliary_clean d : good d=true -> rounds d [Zero] (auxiliary d).
Proof.
  induction d as [d IH] using lt_wf_ind; intro Hd.
  destruct d as [|d]; [constructor|].
  destruct (good_interval (S d) (ltac:(lia)) Hd)
    as [a [L [Ed [HLa [Ha [HL [HLp HP]]]]]]].
  replace (S d) with (a+(L+1)) by lia.
  eapply rounds_trans; [apply IH; [lia|exact Ha]|].
  destruct L as [|k].
  - unfold auxiliary; replace (a+(0+1)) with (S a) by lia.
    replace (1+S a*2) with ((1+a*2)+2) by lia; apply clean_step.
    + reflexivity.
    + apply (proj2 (proj2 (diagonals a))).
    + change (Z (S a) (S (1+a*2))=true); replace (S a) with (S d) by lia; apply HP; lia.
    + change (Z (S a) (1+a*2+2)=false).
      replace (1+a*2+2) with (1+S a*2) by lia; apply (proj1 (proj2 (diagonals (S a)))).
  - assert (Htail: rounds k [Zero] (auxiliary k)).
    { apply IH; [lia|]; replace k with (S k-1) by lia; apply HLp; lia. }
    unfold auxiliary in *.
    replace (S k+1) with (k+2) by lia.
    replace (a+(k+2)) with (a+k+2) by lia.
    replace (1+(a+k+2)*2) with ((1+a*2)+((1+k*2)+1)+2) by lia.
    rewrite front_pad.
    2: { intros j Hj; change (Z (a+k+2) j=true).
         replace (a+k+2) with (S d) by lia; apply HP; lia. }
    2: { replace (1+a*2+(1+k*2+1)+2) with (1+(a+k+2)*2) by lia.
         apply (proj1 (proj2 (diagonals (a+k+2)))). }
    rewrite <-(window_length (row k morse) 1 (1+k*2)).
    apply episode; [reflexivity| | |exact Htail].
    + intros j Hj; destruct (Nat.eq_dec j a) as [->|Hne].
      * apply (proj2 (proj2 (diagonals a))).
      * replace j with (S d-(S d-j)) by lia.
        apply (plateau_before morse (S d) (S (1+a*2)) (S k)); try lia.
        intros i Hi Hmax; apply HP; lia.
    + change (Z (a+k+2) (S (1+a*2))=true).
      replace (a+k+2) with (S d) by lia; apply HP; lia.
Qed.

(* After the first actual round, the baseline is the doubled Morse word.
   Clean times are twice the auxiliary clean times. *)
Definition actual t := front (duplicate morse) (t*2) (2+t*4).
Lemma actual_clean d : good d=true -> rounds (d*2) [One;Zero] (actual d).
Proof.
  induction d as [d IH] using lt_wf_ind; intro Hd.
  destruct d as [|d]; [constructor|].
  destruct (good_interval (S d) (ltac:(lia)) Hd)
    as [a [L [Ed [HLa [Ha [HL [HLp HP]]]]]]].
  pose proof (duplicate_platform _ _ _ HP) as HP2.
  replace (S d*2) with (a*2+(L*2+2)) by lia.
  eapply rounds_trans with (ys:=actual a); [apply IH; [lia|exact Ha]|].
  assert (Htail: rounds (L*2) [Zero] (auxiliary (L*2))).
  { apply auxiliary_clean; rewrite good_double; exact HL. }
  unfold actual,auxiliary in *.
  replace (2+S d*4) with ((2+a*4)+((1+(L*2)*2)+1)+2) by lia.
  rewrite front_pad.
  2: { intros j Hj; apply HP2; lia. }
  2: { replace (2+a*4+(1+L*2*2+1)+2) with ((1+S d*2)*2) by lia.
       rewrite (proj1 (duplicate_rows morse (S d) (1+S d*2))).
       apply (proj1 (proj2 (diagonals (S d)))). }
  replace (S d*2) with (a*2+L*2+2) by lia.
  rewrite <-(window_length (row (L*2) morse) 1 (1+(L*2)*2)).
  apply episode; [reflexivity| | |exact Htail].
  - intros j Hj; destruct (Nat.eq_dec j (a*2)) as [->|Hne].
    + replace (S (2+a*4)) with (1+(1+a*2)*2) by lia.
      rewrite (proj2 (duplicate_rows morse a (1+a*2))).
      apply (proj1 (proj2 (diagonals a))).
    + replace j with (S d*2-(S d*2-j)) by lia.
      apply (plateau_before (duplicate morse) (S d*2) (S (2+a*4)) (L*2+1)); try lia.
      intros i Hi Hmax; apply HP2; lia.
  - replace (a*2+L*2+2) with (S d*2) by lia; apply HP2; lia.
Qed.

Lemma rounds_spec n xs ys : rounds n xs ys ->
  exists k, n<=k /\ config xs -[tm]->> k / config ys.
Proof.
  intro H; induction H as [xs|n xs ys zs Hnext Hrun [k [Hk Hexec]]].
  - exists 0; split; [lia|constructor].
  - destruct (progress_multistep _ _ _ (round_spec _ _ Hnext)) as [j Hj].
    exists (S j+k); split; [lia|eapply multistep_trans; eauto].
Qed.
Lemma rounds_unbounded xs :
  (forall n, exists k ys, n<=k /\ rounds k xs ys) -> ~halts tm (config xs).
Proof.
  intros H [n Hhalt]; destruct (H (S n)) as [k [ys [Hk Hrun]]].
  destruct (rounds_spec _ _ _ Hrun) as [m [Hm Hexec]].
  eapply exceeds_halt; [exact Hhalt| |exact Hexec]; lia.
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (config [])); apply rounds_unbounded; intro n.
  destruct (good_power n) as [Hg Hn].
  exists (S (4^n*2)),(actual (4^n)); split; [lia|].
  econstructor; [reflexivity|apply actual_clean,Hg].
Qed.

End TM1.

(* TM2 has the same interior transducer. Its different right edge is
   exactly TM1's edge preceded by a virtual Zero cell. Consequently the
   already proved auxiliary orbit, not TM1's actual orbit, applies. *)
Module TM2.
Import TM1.
Definition tm := Eval compute in (TM_from_str "1LB1LA_1RC1LE_0RD0RD_0RE1RF_1RA0LA_---1RC").
Notation h0 := [((E,<[1;0;0]),(A,[]))].
Notation h1 := [((C,<[0;1;1]),(B,[]))].
Notation h2 := [((F,<[0;1]),(B,[]))].
Notation w0 := [1;1;1].
Notation w1 := [1;0;1].
Notation wm := [0;1].
Notation edge := ([1;1;1;1] *> 0inf).
Ltac finite_rule := apply BoundedConfig.segRLs_c_spec with (T:=100); reflexivity.
Ltac finite_side := repeat rewrite <-Str_app_assoc;
  apply BoundedConfig.sideRLs_c_spec with (T:=100); reflexivity.

Lemma bit00 : segRLs tm h0 h0 w0 w0. Proof. finite_rule. Qed.
Lemma bit01 : segRLs tm h0 h1 w1 w1. Proof. finite_rule. Qed.
Lemma bit10 : segRLs tm h1 h1 w0 w1. Proof. finite_rule. Qed.
Lemma bit11 : segRLs tm h1 h0 w1 w0. Proof. finite_rule. Qed.
Lemma mark0 : segRLs tm h0 h1 wm wm. Proof. finite_rule. Qed.
Lemma mark1 : segRLs tm h1 h2 wm w1. Proof. finite_rule. Qed.
Lemma clear0 : segRLs tm h2 h2 w0 w1. Proof. finite_rule. Qed.
Lemma clear1 : segRLs tm h2 h2 w1 w1. Proof. finite_rule. Qed.
Lemma edge0 : sideRLs tm h0 edge (w0 *> wm *> edge). Proof. finite_side. Qed.
Lemma edge1 : sideRLs tm h1 edge (w1 *> w1 *> edge). Proof. finite_side. Qed.
Lemma edge2 : sideRLs tm h2 edge (w1 *> w1 *> edge). Proof. finite_side. Qed.
Definition left := 0inf <* [1].
Lemma left_return : sideRLs (flip tm) [((B,[]),(C,<[0;1;1]))] left left.
Proof. unfold left; finite_side. Qed.
Lemma init : c0 -[tm]->* left {{{ ((C,<[0;1;1]),R) }}} edge.
Proof. esx. Qed.

Definition head s : list (DH0*DH0) := match s with H0=>h0 | H1=>h1 | Clear=>h2 end.
Fixpoint tape xs := match xs with []=>edge | x::xs=>word x *> tape xs end.
Definition config xs := left {{{ ((C,<[0;1;1]),R) }}} tape xs.
Local Open Scope nat_scope.
Definition edge_out s := match s with H0=>[Zero;Mark] | _=>[One;One] end.
Lemma edge_next s : next s [Zero]=Some (edge_out s++[Zero]).
Proof. destruct s; reflexivity. Qed.
Lemma action_spec s x s' y : action s x=Some (s',y) ->
  segRLs tm (head s) (head s') (word x) (word y).
Proof.
  destruct s,x; cbn; intro H; inverts H;
    auto using bit00,bit01,bit10,bit11,mark0,mark1,clear0,clear1.
Qed.
Lemma next_end xs s ys : next s xs=Some ys -> exists zs, ys=zs++[Zero].
Proof.
  gen s ys; induction xs as [|x xs IH]; intros s ys H.
  - destruct s; inverts H; eexists [_]; reflexivity.
  - cbn in H; destruct (action s x) as [[s' y]|] eqn:E; try discriminate.
    destruct (next s' xs) as [zs|] eqn:F; inverts H.
    destruct (IH _ _ F) as [ws ->]; exists (y::ws); reflexivity.
Qed.
Lemma next_spec xs s ys : next s (xs++[Zero])=Some (ys++[Zero]) ->
  sideRLs tm (head s) (tape xs) (tape ys).
Proof.
  gen s ys; induction xs as [|x xs IH]; intros s ys H.
  - rewrite edge_next in H; injection H as H; apply app_inv_tail in H; subst ys.
    destruct s; cbn; auto using edge0,edge1,edge2.
  - cbn[app next] in H; destruct (action s x) as [[s' y]|] eqn:E; try discriminate.
    destruct (next s' (xs++[Zero])) as [zs|] eqn:F; try discriminate.
    destruct ys as [|z ys].
    + inverts H; pose proof (next_length _ _ _ F); cbn in *; lia.
    + inverts H; cbn[tape]; eapply segRLs_sideRLs_concat.
      * apply action_spec,E.
      * apply IH,F.
Qed.
Lemma round_spec xs ys : next H1 (xs++[Zero])=Some (ys++[Zero]) ->
  config xs -[tm]->+ config ys.
Proof.
  intro H; unfold config; eapply progress_trans.
  - apply sideRLs_1, (next_spec _ _ _ H).
  - apply sideRLs_1L,left_return.
Qed.
Lemma rounds_spec n start finish : rounds n start finish -> forall xs, start=xs++[Zero] ->
  exists ys k, finish=ys++[Zero] /\ n<=k /\ config xs -[tm]->> k / config ys.
Proof.
  intro H; induction H as [start|n start mid finish Hnext Hrun IH]; intros xs E; subst start.
  - exists xs,0; repeat split; constructor.
  - destruct (next_end _ _ _ Hnext) as [zs Ez].
    destruct (IH _ Ez) as [ys [k [Ef [Hk Hexec]]]].
    rewrite Ez in Hnext; destruct (progress_multistep _ _ _ (round_spec _ _ Hnext)) as [j Hj].
    exists ys,(S j+k); repeat split; auto; [lia|eapply multistep_trans; eauto].
Qed.

Theorem nonhalt: ~halts tm c0.
Proof.
  eapply multistep_nonhalt; [apply init|].
  change (~halts tm (config [])); intros [n Hhalt].
  destruct (PrefixXor.good_power n) as [Hg Hn].
  destruct (rounds_spec _ _ _ (auxiliary_clean _ Hg) [] eq_refl)
    as [ys [k [_ [Hk Hexec]]]].
  eapply exceeds_halt; [exact Hhalt| |exact Hexec]; lia.
Qed.
End TM2.
