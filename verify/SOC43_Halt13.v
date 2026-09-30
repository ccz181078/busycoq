(* SOC_ex 13 (test_SOC_4_3.TM10): finite halting proof with sparse powers.
   Standalone: only BusyCoq and standard-library dependencies.
   See SOC43_EX13_RUNS.md for the independent simulations. *)
From BusyCoq Require Import Individual62 BinaryCounter_v2 SimplTape ES_v2.
From Coq Require Import NArith ZArith List ZifyNat Lia PeanoNat String.
Import ListNotations.
Open Scope Z_scope.

Module Sparse.
Definition num := list (N*Z).
Definition pow2 (n:N) := 2^Z.of_N n.
Fixpoint value (xs:num) : Z :=
  match xs with [] => 0 | (e,c)::xs => c*pow2 e + value xs end.

Lemma pow2_pos n: 0 < pow2 n.
Proof. unfold pow2; apply Z.pow_pos_nonneg; lia. Qed.
Lemma pow2_add a b: pow2 (a+b) = pow2 a * pow2 b.
Proof. unfold pow2; rewrite N2Z.inj_add, Z.pow_add_r; try lia; reflexivity. Qed.
Lemma pow2_sub a b: (a<=b)%N -> pow2 b = pow2 a * pow2 (b-a).
Proof. intros; rewrite <-pow2_add; f_equal; lia. Qed.

(* Saturate long divisions of small coefficients. Z.shiftr itself iterates
   over the shift in this Coq version, so never call it on huge exponents. *)
Definition divpow (n:N) (c:Z) : option (Z*bool) :=
  if N.leb n 16 then Some (c / pow2 n, Z.eqb (c mod pow2 n) 0)
  else if Z.ltb (Z.abs c) 65536 then
    Some ((if Z.ltb c 0 then -1 else 0), Z.eqb c 0)
  else None.

Lemma divpow_spec n c q zero: divpow n c = Some (q,zero) ->
  exists r, c=pow2 n*q+r /\ 0<=r<pow2 n /\ (zero=true <-> r=0).
Proof.
  unfold divpow; destruct (N.leb n 16) eqn:Hn.
  - intros H; inversion H; subst; exists (c mod pow2 n).
    pose proof (pow2_pos n); split; [apply Z.div_mod; lia|].
    split; [apply Z.mod_pos_bound; lia|apply Z.eqb_eq].
  - destruct (Z.ltb (Z.abs c) 65536) eqn:Hc; [|discriminate].
    apply N.leb_gt in Hn; apply Z.ltb_lt in Hc.
    assert (Hp: 65536<=pow2 n).
    { change (2^16<=2^Z.of_N n); apply Z.pow_le_mono_r; lia. }
    destruct (Z.ltb c 0) eqn:Hsign; intros H; inversion H; subst.
    + apply Z.ltb_lt in Hsign; rewrite Z.abs_neq in Hc by lia.
      exists (c+pow2 n); repeat split; try lia; rewrite Z.eqb_eq; lia.
    + apply Z.ltb_ge in Hsign; rewrite Z.abs_eq in Hc by lia.
      exists c; repeat split; try lia; apply Z.eqb_eq.
Qed.

Definition finish_sign (zero:bool) (s:comparison) :=
  match s with Eq => if zero then Eq else Gt | _ => s end.

Lemma finish_sign_spec p q r zero: 0<p -> 0<=r<p ->
  (zero=true <-> r=0) ->
  (p*q+r ?= 0) = finish_sign zero (q ?= 0).
Proof.
  intros Hp Hr Hz; unfold finish_sign; destruct (Z.compare_spec q 0).
  - subst; destruct zero; cbn; [apply Z.compare_eq_iff|apply Z.compare_gt_iff]; lia.
  - apply Z.compare_lt_iff; nia.
  - apply Z.compare_gt_iff; nia.
Qed.

Fixpoint sign_from (xs:num) (base:N) (carry:Z) : option comparison :=
  match xs with
  | [] => Some (carry ?= 0)
  | (e,c)::xs =>
    if N.leb base e then
      match divpow (e-base) carry with
      | Some (q,zero) =>
        match sign_from xs e (c+q) with
        | Some s => Some (finish_sign zero s)
        | None => None
        end
      | None => None
      end
    else None
  end.

Lemma sign_from_spec xs base carry s: sign_from xs base carry = Some s ->
  exists v, value xs = pow2 base*v /\ (carry+v ?= 0)=s.
Proof.
  revert base carry s; induction xs as [|[e c] xs IH]; cbn; intros base carry s.
  - intros H; inversion H; subst; exists 0; split; [ring|f_equal; ring].
  - destruct (N.leb base e) eqn:He; [|discriminate].
    destruct (divpow (e-base) carry) as [[q zero]|] eqn:Hd; [|discriminate].
    destruct (sign_from xs e (c+q)) as [t|] eqn:Ht; [|discriminate].
    intros H; inversion H; subst; apply N.leb_le in He.
    destruct (divpow_spec _ _ _ _ Hd) as [r [Hr [Hb Hz]]].
    destruct (IH _ _ _ Ht) as [v [Hv Hs]].
    exists (pow2 (e-base)*(c+v)); split.
    + rewrite Hv, (pow2_sub base e He); ring.
    + rewrite <-Hs, <-finish_sign_spec with (p:=pow2 (e-base)) (r:=r);
        try assumption; try apply pow2_pos.
      f_equal; lia.
Qed.

Definition sign xs := sign_from xs 0 0.
Lemma sign_spec xs s: sign xs = Some s -> (value xs ?= 0)=s.
Proof.
  intros H; destruct (sign_from_spec _ _ _ _ H) as [v [Hv Hs]].
  change (value xs=1*v) in Hv; rewrite Z.mul_1_l in Hv; rewrite Hv; exact Hs.
Qed.

(* Insertion orders exponents and joins equal powers. Zero terms may remain;
   sign_from checks ordering and is sound even without a normal-form invariant. *)
Fixpoint insert (e:N) (c:Z) (xs:num) : num :=
  match xs with
  | [] => [(e,c)]
  | (f,d)::xs =>
    match N.compare e f with
    | Lt => (e,c)::(f,d)::xs
    | Eq => (e,c+d)::xs
    | Gt => (f,d)::insert e c xs
    end
  end.
Lemma insert_spec xs e c: value (insert e c xs)=c*pow2 e+value xs.
Proof.
  induction xs as [|[f d] xs IH]; cbn; [ring|].
  destruct (N.compare_spec e f); cbn; subst; rewrite ?IH; ring.
Qed.
Definition add (xs ys:num) := fold_right (fun ec zs => insert (fst ec) (snd ec) zs) ys xs.
Definition neg (xs:num) := map (fun ec => (fst ec,-snd ec)) xs.
Definition sub xs ys := add xs (neg ys).
Definition shift (n:N) (xs:num) := map (fun ec => ((n+fst ec)%N,snd ec)) xs.
Definition power (n:N) : num := [(n,1)].
Definition small (c:Z) : num := [(0%N,c)].
Lemma add_spec xs ys: value (add xs ys)=value xs+value ys.
Proof.
  induction xs as [|[e c] xs IH]; [reflexivity|].
  change (value (insert e c (add xs ys)) = (c*pow2 e+value xs)+value ys).
  rewrite insert_spec, IH; ring.
Qed.
Lemma neg_spec xs: value (neg xs) = -value xs.
Proof.
  induction xs as [|[e c] xs IH]; [reflexivity|].
  change (-c*pow2 e+value (neg xs)= -(c*pow2 e+value xs)); rewrite IH; ring.
Qed.
Lemma sub_spec xs ys: value (sub xs ys)=value xs-value ys.
Proof. unfold sub; rewrite add_spec, neg_spec; ring. Qed.
Lemma shift_spec n xs: value (shift n xs)=pow2 n*value xs.
Proof.
  induction xs as [|[e c] xs IH]; [cbn; ring|].
  change (c*pow2 (n+e)+value (shift n xs)=pow2 n*(c*pow2 e+value xs)).
  rewrite pow2_add, IH; ring.
Qed.
Lemma power_spec n: value (power n)=pow2 n.
Proof. change (1*pow2 n+0=pow2 n); ring. Qed.
Lemma small_spec c: value (small c)=c.
Proof. change (c*1+0=c); ring. Qed.

Definition compare xs ys := sign (sub xs ys).
Lemma compare_spec xs ys s: compare xs ys=Some s -> (value xs ?= value ys)=s.
Proof.
  intros H; apply sign_spec in H; rewrite sub_spec in H.
  rewrite Z.compare_sub; exact H.
Qed.

Fixpoint normalize (fuel:nat) (xs:num) : num :=
  match fuel,xs with
  | O,_ => xs
  | S fuel,[] => []
  | S fuel,(e,c)::xs =>
    if Z.eqb c 0 then normalize fuel xs else
    if Z.eqb c 1 then (e,c)::normalize fuel xs else
    if Z.eqb c (-1) then (e,c)::normalize fuel xs else
    let q := Z.quot c 2 in
    let r := c-q*2 in
    let ys := normalize fuel (insert (e+1)%N q xs) in
    if Z.eqb r 0 then ys else (e,r)::ys
  end.
Lemma normalize_spec fuel xs: value (normalize fuel xs)=value xs.
Proof.
  revert xs; induction fuel; intros [|[e c] xs]; cbn [normalize]; try reflexivity.
  destruct (Z.eqb c 0) eqn:H0; [apply Z.eqb_eq in H0; subst; cbn [value]; rewrite IHfuel; ring|].
  destruct (Z.eqb c 1); [cbn [value]; rewrite IHfuel; reflexivity|].
  destruct (Z.eqb c (-1)); [cbn [value]; rewrite IHfuel; reflexivity|].
  assert (Hp: pow2 (e+1)=pow2 e*2) by (rewrite pow2_add; reflexivity).
  destruct (Z.eqb (c-Z.quot c 2*2) 0) eqn:Hr; cbn [value];
    rewrite IHfuel, insert_spec, Hp;
    [apply Z.eqb_eq in Hr; nia|ring].
Qed.
Definition pack := normalize 128.
Lemma pack_spec xs: value (pack xs)=value xs.
Proof. apply normalize_spec. Qed.

Definition eqb xs ys := match compare xs ys with Some Eq => true | _ => false end.
Definition leb xs ys := match compare xs ys with Some Lt | Some Eq => true | _ => false end.
Lemma eqb_spec xs ys: eqb xs ys=true -> value xs=value ys.
Proof.
  unfold eqb; destruct (compare xs ys) as [[]|] eqn:H; try discriminate.
  intros _; apply compare_spec in H; now apply Z.compare_eq_iff in H.
Qed.
Lemma leb_spec xs ys: leb xs ys=true -> value xs<=value ys.
Proof.
  unfold leb; destruct (compare xs ys) as [[]|] eqn:H; try discriminate.
  - intros _; apply compare_spec in H; apply Z.compare_eq_iff in H; lia.
  - intros _; apply compare_spec in H; apply Z.compare_lt_iff in H.
    apply Z.lt_le_incl; exact H.
Qed.

(* A deliberately untrusted quotient proposal. It is fast on normalized signed
   digits. Every caller validates the required numerical identity below. *)
Fixpoint drop (n:N) (xs:num) (negative:bool) : num :=
  match xs with
  | [] => if negative then small (-1) else []
  | (e,c)::xs =>
    if N.ltb e n then drop n xs (Z.ltb c 0) else
      add (if negative then small (-1) else [])
          (map (fun ec => ((fst ec-n)%N,snd ec)) ((e,c)::xs))
  end.
Definition quotient n xs := pack (drop n (pack xs) false).
Definition nonnegative xs := leb [] xs.
Definition split (xs:num) : option (N*num) :=
  let ys := pack xs in
  match ys with
  | [] => None
  | (e,_)::_ =>
    let u := quotient (e+1)%N ys in
    if nonnegative u then
      if eqb xs (shift e (add (shift 1 u) (small 1))) then Some (e,u) else None
    else None
  end.
Lemma split_spec xs e u: split xs=Some (e,u) ->
  0<=value u /\ value xs=pow2 e*(value u*2+1).
Proof.
  unfold split, nonnegative; destruct (pack xs) as [|[i c] ys]; [discriminate|].
  destruct (leb [] (quotient (i+1) ((i,c)::ys))) eqn:Hn; [|discriminate].
  destruct (eqb xs _) eqn:He; [|discriminate]; intros H; inversion H; subst.
  apply leb_spec in Hn; apply eqb_spec in He.
  rewrite shift_spec, add_spec, shift_spec, small_spec in He.
  change (pow2 1) with 2 in He; cbn [value] in Hn; split; [exact Hn|nia].
Qed.

Definition half xs : option (bool*num) :=
  let u := quotient 1 xs in
  if nonnegative u then
    if eqb xs (shift 1 u) then Some (false,u) else
    if eqb xs (add (shift 1 u) (small 1)) then Some (true,u) else None
  else None.
Lemma half_spec xs odd u: half xs=Some (odd,u) ->
  0<=value u /\ value xs=value u*2+(if odd then 1 else 0).
Proof.
  unfold half, nonnegative; destruct (leb [] (quotient 1 xs)) eqn:Hn; [|discriminate].
  apply leb_spec in Hn; cbn [value] in Hn.
  destruct (eqb xs (shift 1 (quotient 1 xs))) eqn:H0.
  - intros H; inversion H; subst; apply eqb_spec in H0; rewrite shift_spec in H0.
    change (pow2 1) with 2 in H0; split; [exact Hn|lia].
  - destruct (eqb xs (add (shift 1 (quotient 1 xs)) (small 1))) eqn:H1; [|discriminate].
    intros H; inversion H; subst; apply eqb_spec in H1.
    rewrite add_spec, shift_spec, small_spec in H1.
    change (pow2 1) with 2 in H1; split; [exact Hn|lia].
Qed.
End Sparse.

Close Scope Z_scope.
Import Sparse.
Module Forward13.
Open Scope N_scope.
Inductive phase := L | R | T1 | T2 | A.
Record state := State { tag:phase; width:N; budget:num; mark:N; low:num; high:num }.
Definition ordinary p w k m := State p w k 0 [] m.
Definition plus x y := pack (add x y).
Definition minus x y := pack (sub x y).
Definition one := small 1.
Definition twice x := shift 1 x.
Definition full w := minus (power w) one.
Definition iszero x := eqb x [].
Definition lt x y := match compare x y with Some Lt => true | _ => false end.

Definition good x :=
  if N.ltb 0 (width x) then
  if nonnegative (budget x) then
  if lt (budget x) (power (width x)) then
  if nonnegative (high x) then
    match tag x with
    | L => lt (plus (budget x) (high x)) (power (width x+1))
    | R => lt (plus (plus (budget x) (high x)) one) (power (width x+1))
    | A => leb (high x) (budget x)
    | T1 | T2 =>
      if nonnegative (low x) then
      if lt (low x) (power (mark x+1)) then
        leb (plus (low x) (high x)) (budget x)
      else false else false
    end
  else false else false else false else false.

Inductive result := next (x:state) | halted | stuck.
Definition prefix p w k m whole bit :=
  if iszero m then next (ordinary R w k (small bit)) else
  match split m with
  | Some (i,u) =>
    let h := i+whole in next (State p w k h (minus (full (h+1)) (small bit)) u)
  | None => stuck
  end.

Definition step x :=
  let w := width x in let k := budget x in let m := high x in
  match tag x with
  | R => next (ordinary L w [] (plus (plus k m) one))
  | L =>
    let m := plus k m in
    if eqb m (power w) then
      let a := (w-1)/4 in let e := (w-1) mod 4 in
      if N.eqb e 0 then let j:=w+3*a+2 in next (ordinary L j [] (plus (power j) one)) else
      if N.eqb e 1 then next (ordinary L (w+3*a+3) [] (shift (3*a+1) (plus (power (w+1)) one))) else
      if N.eqb e 2 then let j:=w+3*a+4 in next (ordinary L j [] (power j)) else
      next (ordinary L (w+3*a+4) [] (plus (shift (3*a+2) (plus (power (w+1)) one)) one))
    else match half m with
    | Some (true,u) => prefix T1 (w+1) (full (w+1)) u 0 0%Z
    | Some (false,u) => prefix T2 w (full w) u 1 1%Z
    | None => stuck
    end
  | A => match half m with
    | Some (true,_) => halted
    | Some (false,u) => prefix T2 w k u 0 0%Z
    | None => stuck
    end
  | T1 =>
    let a:=mark x/4 in let e:=mark x mod 4 in let b:=minus k (low x) in
    if N.eqb (mark x) 0 then
      match half m with
      | Some (true,_) =>
        match split (plus m one) with
        | Some (t,u) => if N.ltb 0 t then
            next (State T1 (w+t) (full (w+t)) 0 one (twice u)) else stuck
        | None => stuck
        end
      | Some (false,_) => prefix T1 (w+1) (full (w+1)) m 0 0%Z
      | None => stuck
      end
    else
      if N.eqb e 0 then prefix T1 (w+3*a+1) (full (w+3*a+1)) m 0 0%Z else
      if N.eqb e 1 then next (ordinary R (w+3*a+1)
        (minus (shift (3*a) (plus (twice b) one)) one) (plus (twice m) one)) else
      if N.eqb e 2 then next (ordinary R (w+3*a+2) (full (w+3*a+2)) (plus (twice m) one)) else
      prefix T1 (w+3*a+3) (minus (shift (3*a+2) (plus (twice b) one)) one) m 0 0%Z
  | T2 =>
    let a:=mark x/4 in let e:=mark x mod 4 in let b:=minus k (low x) in
    if N.eqb e 0 then prefix T1 (w+3*a+1) (shift (3*a) (plus (twice b) one)) m 0 0%Z else
    if N.eqb e 1 then prefix T1 (w+3*a+2) (full (w+3*a+2)) m 0 1%Z else
    if N.eqb e 2 then next (ordinary A (w+3*a+3) (minus (shift (3*a+2) (plus (twice b) one)) one) m) else
    next (ordinary A (w+3*a+4) (full (w+3*a+4)) m)
  end.

Fixpoint check fuel x :=
  match fuel with
  | O => false
  | S fuel => if good x then
      match step x with next y => check fuel y | halted => true | stuck => false end
    else false
  end.
Definition seed := ordinary L 3 [] (pack (small 9)).

Example numerical_halt: check 256 seed=true.
Proof. vm_compute; reflexivity. Qed.
End Forward13.
Close Scope N_scope.
Open Scope nat_scope.
Open Scope sym.

Module SOC43_Extra.
Import BusyCoq.Individual62 BusyCoq.BinaryCounter_v2 BusyCoq.SimplTape BusyCoq.ES_v2.
Import ZifyNat Lia PeanoNat.


Notation ld0 := <[1;1;1;0].
Notation ld1 := <[1;1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].

Module Counter.
Section Counter.
Variables (tm:TM) (QL QR QA:Q) (Erase:side->side->Prop).
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{QL}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{QR}}> r) (at level 30).
Notation "l |2> r" := (l <* ld0 {{QA}}> r) (at level 30).
Hypothesis Erase_O: Erase ldh ldh.
Hypothesis Erase_S0: forall l l', Erase l l' -> Erase (l<*ld0) (l'<*ld0).
Hypothesis Erase_S1: forall l l', Erase l l' -> Erase (l<*ld1) (l'<*ld0).
Hypothesis LInc: forall l r n,
  l <* ld0 <* ld1^^n <| r -->+ l <* ld1 <* ld0^^n |> r.
Hypothesis RInc: forall l r n,
  l |> rd1^^n *> [0] *> r -->+ l <| rd0^^n *> [1] *> r.
Hypothesis LOv_0: forall r n,
  ldh <* ld1^^n <| rd0 *> r -->+ ldh <* ld0^^n |> rd1 *> [0;0] *> r.
Hypothesis LOv_1: forall r n,
  ldh <* ld1^^n <| rd1 *> r -->+ ldh <* ld0^^(1+n) |> [0] *> r.
Hypothesis ROv1_0: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;0] *> r -->+ l' <* ld0^^(n*3+1) |> [0] *> r.
Hypothesis ROv1_1: forall l r n,
  l |> rd1^^(n*4+1) *> [1;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Hypothesis ROv1_2: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;0] *> r -->+ l' <* ld0^^(n*3+2) |> rd1 *> r.
Hypothesis ROv1_3: forall l r n,
  l |> rd1^^(n*4+3) *> [1;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Hypothesis ROv2_0: forall l r n,
  l |> rd1^^(n*4) *> [1;0;1;0;0] *> r -->+ l <* ld0 <* ld1^^(n*3) |> [0] *> r.
Hypothesis ROv2_1: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+1) *> [1;0;1;0;0] *> r -->+ l' <* ld0^^(n*3+2) |> [1] *> r.
Hypothesis ROv2_2: forall l r n,
  l |> rd1^^(n*4+2) *> [1;0;1;0;0] *> r -->+ l <* ld1 <* ld0^^(n*3+2) |2> r.
Hypothesis ROv2_3: forall l r n l', Erase l l' ->
  l |> rd1^^(n*4+3) *> [1;0;1;0;0] *> r -->+ l' <* ld0^^(n*3+4) |2> r.
Hypothesis Aux0: forall l r, l |2> rd0 *> r -->+ l |> [0;0] *> r.
Hypothesis Blank0: forall l l' n, Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;1] *> 0inf -->* l' <* ld0^^(n*3+1) |> rd1 *> 0inf.
Hypothesis Blank1: forall l n,
  l |> rd1^^(n*4+1) *> [1;1;0;1] *> 0inf -->* l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Hypothesis Blank2: forall l l' n, Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;1] *> 0inf -->* l' <* ld0^^(n*3+3) |> 0inf.
Hypothesis Blank3: forall l n,
  l |> rd1^^(n*4+3) *> [1;1;0;1] *> 0inf -->* l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.

Definition LC len k := BinDec ld0 ld1 len k ldh.
Definition RC m := BinInc rd1 m.
Definition MC h n r := BinDec2 [0] [1] [0;0] h n r.
Definition RC1 h n m := MC h n (rd1 *> RC m).
Definition RC2 h n m := MC h n ([0] *> rd1 *> RC m).
Definition RC' h n := MC h n ([1;0;1] *> 0inf).
Lemma RC_one_prefix: [1] *> RC 0 = RC 1.
Proof.
  unfold RC; rw_Bin; change ([1] *> 0inf = [1;0;0] *> 0inf).
  cbn; do 2 rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Lemma RC_zero_prefix: [0;0] *> RC 0 = RC 0.
Proof.
  unfold RC; rw_Bin; change ([0;0] *> 0inf = 0inf).
  cbn; do 2 rewrite <-(const_unfold _ 0); reflexivity.
Qed.
Ltac arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac follow_rule H := intros; epose proof H as HX; cbn [Str_app] in *;
  repeat rewrite <-(const_unfold _ 0) in *; first [follow10 HX|follow HX];
  repeat (simpl_rotate || simpl_tape); finish; repeat rewrite lpow_add'; flia.
Ltac solve_rule H := intros; unfold LC, RC1, RC2, RC', MC, RC in *;
  repeat rewrite BinDec_full in *;
  rw_Bin; try solve[solve_pow2_lt]; try solve[arith]; follow_rule H.

Lemma LC_Erase len k: k<2^len -> Erase (LC len k) (LC len (2^len-1)).
Proof.
  unfold LC; rewrite BinDec_full; gen k; induction len; intros.
  - replace k with 0%nat by (cbn in *; lia); rewrite BinDec_O; apply Erase_O.
  - replace (S len) with (len+1) in * by lia; divmod2_cases k;
      rw_Bin; try solve[arith]; simpl_tape;
      [apply Erase_S1|apply Erase_S0]; apply IHlen; arith.
Qed.
Lemma LC_Inc len k r: 1+k<2^len -> LC len (1+k) <| r -->+ LC len k |> r.
Proof. intros; apply LBinDec_spec; try lia; follow_rule LInc. Qed.
Lemma RC_Inc m l: l |> RC m -->+ l <| RC (1+m).
Proof. apply RBinInc_spec; follow_rule RInc. Qed.
Lemma MC_Inc h n l r: 1+n<2^(h+1) -> l |> MC h (1+n) r -->+ l <| MC h n r.
Proof. intros; apply RBinDec2_spec; try lia; follow_rule RInc. Qed.

Lemma LC_Ov_odd len m:
  LC len 0 <| RC (m*2+1) -->+ LC (len+1) (2^(len+1)-1) |> [0] *> RC m.
Proof. solve_rule LOv_1. Qed.
Lemma LC_Ov_even len m i:
  LC len 0 <| RC ((m*2+1)*2^(i+1)) -->+
  LC len (2^len-1) |> RC2 (i+1) ((2^(i+1)-1)*2) m.
Proof. unfold LC,RC2,MC,RC; rw_Bin; try solve[arith]; simpl_tape; follow_rule LOv_0. Qed.

Lemma RC1_Ov0 len k a m: k<2^len ->
  LC len k |> RC1 (a*4) 0 m -->+
  LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> [0] *> RC m.
Proof. intros Hk; pose proof (ROv1_0 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC1_Ov1 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+1) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> RC (m*2+1).
Proof. solve_rule ROv1_1. Qed.
Lemma RC1_Ov2 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+2) 0 m -->+
  LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> RC (m*2+1).
Proof. intros Hk; pose proof (ROv1_2 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC1_Ov3 len k a m: k<2^len ->
  LC len k |> RC1 (a*4+3) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0] *> RC m.
Proof. solve_rule ROv1_3. Qed.
Lemma RC2_Ov0 len k a m: k<2^len ->
  LC len k |> RC2 (a*4) 0 m -->+
  LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> [0] *> RC m.
Proof. solve_rule ROv2_0. Qed.
Lemma RC2_Ov1 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+1) 0 m -->+
  LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> [1] *> RC m.
Proof. intros Hk; pose proof (ROv2_1 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC2_Ov2 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+2) 0 m -->+
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |2> RC m.
Proof. solve_rule ROv2_2. Qed.
Lemma RC2_Ov3 len k a m: k<2^len ->
  LC len k |> RC2 (a*4+3) 0 m -->+
  LC (len+(a*3+4)) (2^(len+(a*3+4))-1) |2> RC m.
Proof. intros Hk; pose proof (ROv2_3 _ (RC m) a _ (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma Aux_even len k m:
  LC len k |2> RC (m*2) -->+ LC len k |> [0;0] *> RC m.
Proof. solve_rule Aux0. Qed.

Ltac follow_inc H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma MC_finish len k h n r: k<2^len -> n+k+1<2^(h+1) ->
  LC len k |> MC h (n+k+1) r -->* LC len 0 <| MC h n r.
Proof.
  induction k; intros.
  - replace (n+0+1) with (1+n) by lia; follow_inc MC_Inc; finish.
  - replace (n+S k+1) with (1+(n+k+1)) by lia.
    follow_inc MC_Inc; follow_inc LC_Inc; follow IHk; try lia; finish.
Qed.
Lemma MC_Incs len k h n r: k+n<2^len -> n<2^(h+1) ->
  LC len (k+n) |> MC h n r -->* LC len k |> MC h 0 r.
Proof.
  gen k; induction n; intros; [finish|].
  follow_inc MC_Inc; rewrite Nat.add_succ_r; follow_inc LC_Inc.
  follow IHn; try lia; finish.
Qed.
Lemma LC_Ov' len h:
  LC len 0 <| RC2 (h+1) (((0*2+1)*2^h-1)*2) 0 -->+
  LC (len+1) (2^(len+1)-1) |> RC' h (2^(h+1)-1).
Proof.
  rewrite (Nat.add_comm h 1) at 1.
  unfold LC,RC2,RC',MC,RC; rw_Bin; try solve[arith].
  cbn [app lpow Str_app]; do 2 (rewrite (lpow_rotate [0;0] 0); cbn [app]); follow_rule LOv_1.
Qed.
Lemma corner_case h:
  LC (h+1) 0 <| RC (2^(h+1)) -->+
  LC (h+1+1) (2^(h+1)) |> RC' h 0.
Proof.
  replace (2^(h+1)) with ((0*2+1)*2^(h+1)) at 1 by arith.
  follow10 LC_Ov_even.
  replace ((2^(h+1)-1)*2) with
    (((0*2+1)*2^h-1)*2+(2^(h+1)-1)+1) by arith.
  unfold RC2; follow MC_finish; [arith|arith|].
  fold RC2; follow100 LC_Ov'.
  replace (2^(h+1+1)-1) with (2^(h+1)+(2^(h+1)-1)) by arith.
  unfold RC'; follow MC_Incs; [arith|arith|finish].
Qed.
Lemma RC'_Ov0 len k a: k<2^len ->
  LC len k |> RC' (a*4) 0 -->*
  LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> RC 1.
Proof. intros Hk; pose proof (Blank0 _ _ a (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC'_Ov1 len k a: k<2^len ->
  LC len k |> RC' (a*4+1) 0 -->*
  LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| RC 0.
Proof. solve_rule Blank1. Qed.
Lemma RC'_Ov2 len k a: k<2^len ->
  LC len k |> RC' (a*4+2) 0 -->*
  LC (len+(a*3+3)) (2^(len+(a*3+3))-1) |> RC 0.
Proof. intros Hk; pose proof (Blank2 _ _ a (LC_Erase len k Hk)); solve_rule H. Qed.
Lemma RC'_Ov3 len k a: k<2^len ->
  LC len k |> RC' (a*4+3) 0 -->*
  LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| RC 1.
Proof. solve_rule Blank3. Qed.

Close Scope sym.
Inductive Config := cfgL (len k m:nat) | cfgR (len k m:nat)
  | cfgR1 (len k h n m:nat) | cfgR2 (len k h n m:nat) | cfgA (len k m:nat).
Definition to_config x := match x with
| cfgL len k m => LC len k <| RC m
| cfgR len k m => LC len k |> RC m
| cfgR1 len k h n m => LC len k |> RC1 h n m
| cfgR2 len k h n m => LC len k |> RC2 h n m
| cfgA len k m => LC len k |2> RC m
end.
Definition P x := match x with
| cfgL len k m => 1<=len /\ k<2^len /\ k+m<2^len*2
| cfgR len k m => 1<=len /\ k<2^len /\ k+m+1<2^len*2
| cfgR1 len k h n m | cfgR2 len k h n m =>
    1<=len /\ n+m<=k<2^len /\ n<2^(h+1)
| cfgA len k m => 1<=len /\ m<=k<2^len
end.
End Counter.
End Counter.
Open Scope sym.

Lemma lpow_unrotate_12 n (a a0 a1 a2 a3 a4 a5 a6 a7 a8 a9 a10:Sym) r:
  a >> [a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10;a]^^n *> r =
  [a;a0;a1;a2;a3;a4;a5;a6;a7;a8;a9;a10]^^n *> a >> r.
Proof. simpl_rotate; reflexivity. Qed.
Ltac rw_unrotate_0 ::=
  rewrite lpow_unrotate_1 || rewrite lpow_unrotate_2 ||
  rewrite lpow_unrotate_3 || rewrite lpow_unrotate_4 ||
  rewrite lpow_unrotate_5 || rewrite lpow_unrotate_6 ||
  rewrite lpow_unrotate_12.
End SOC43_Extra.

Module TM10.
Import SOC43_Extra.
Notation ld0 := <[1;1;1;0].
Notation ld1 := <[1;1;1;1].
Notation ldh := (0inf <* <[1]).
Notation rd0 := [0;0;0].
Notation rd1 := [1;0;0].
Definition tm := Eval compute in (TM_from_str "1RB0RF_1LC1RE_1LD0LC_0LE0RE_1RA1LD_1RB---").
Notation "c -->* c'" := (c -[tm]->* c') (at level 40).
Notation "c -->+ c'" := (c -[tm]->+ c') (at level 40).
Notation "l <| r" := (l <{{E}} [0;1;0;1;0] *> r) (at level 30).
Notation "l |> r" := (l <* [1;0;1;1;1] {{B}}> r) (at level 30).
(* Canonical entry after the fixed prefix of the archive's LOv'. *)
Lemma LInc l r n:
  l <* ld0 <* ld1^^n <| r -->+
  l <* ld1 <* ld0^^n |> r.
Proof. es. Qed.

Lemma RInc l r n:
  l |> rd1^^n *> [0] *> r -->+
  l <| rd0^^n *> [1] *> r.
Proof. es. Qed.

Lemma LOv_0 r n:
  ldh <* ld1^^n <| rd0 *> r -->+
  ldh <* ld0^^n |> rd1 *> [0;0] *> r.
Proof. es. Qed.

Lemma LOv_1 r n:
  ldh <* ld1^^n <| rd1 *> r -->+
  ldh <* ld0^^(1+n) |> [0] *> r.
Proof. es. Qed.

Lemma ROv1_1 l r n:
  l |> rd1^^(n*4+1) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3) |> rd1 *> r.
Proof. es. Qed.

Lemma ROv1_3 l r n:
  l |> rd1^^(n*4+3) *> [1;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |> [0] *> r.
Proof. es. Qed.

Definition LOv' l l' :=
  (forall r, l <* [1] <| r -->* l' |> [1;0] *> r).

Lemma ROv1_0 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+0) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+1) |> [0] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv1_2 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> rd1 *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv2_0 l r n:
  l |> rd1^^(n*4+0) *> [1;0;1;0;0] *> r -->+
  l <* ld0 <* ld1^^(n*3) |> [0] *> r.
Proof. es. Qed.

Lemma ROv2_1 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+1) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+2) |> [1] *> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Notation "l |2> r" := (l <* ld0 {{F}}> r) (at level 30).

Lemma ROv2_2 l r n:
  l |> rd1^^(n*4+2) *> [1;0;1;0;0] *> r -->+
  l <* ld1 <* ld0^^(n*3+2) |2> r.
Proof. st. repeat (er||sr). Qed.

Lemma ROv2_3 l r n l':
  LOv' l l' ->
  l |> rd1^^(n*4+3) *> [1;0;1;0;0] *> r -->+
  l' <* ld0^^(n*3+4) |2> r.
Proof. unfold LOv'. intros HP. st. repeat (follow HP || es1). Qed.

Lemma ROv'_1 l r:
  halts tm (l |2> rd1 *> r).
Proof. esx. Qed.

Lemma ROv'_0 l r:
  l |2> rd0 *> r -->+
  l |> [0;0] *> r.
Proof. es. Qed.


Definition Erase l l' := forall r, l <{{D}} [1;0;1;0;1;0] *> r -->* l' |> [1;0] *> r.
Lemma Erase_S0 l l': Erase l l' -> Erase (l<*ld0) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_S1 l l': Erase l l' -> Erase (l<*ld1) (l'<*ld0).
Proof. unfold Erase; intros HP r; repeat (follow HP || es1). Qed.
Lemma Erase_O: Erase ldh ldh.
Proof. unfold Erase; es. Qed.
Lemma Blank0 l l' n: Erase l l' ->
  l |> rd1^^(n*4) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+1) |> rd1 *> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank1 l n:
  l |> rd1^^(n*4+1) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+1) <| 0inf.
Proof. st; repeat (er || sr). Qed.
Lemma Blank2 l l' n: Erase l l' ->
  l |> rd1^^(n*4+2) *> [1;1;0;1] *> 0inf -->*
  l' <* ld0^^(n*3+3) |> 0inf.
Proof. unfold Erase; intros HP; es; follow HP; es. Qed.
Lemma Blank3 l n:
  l |> rd1^^(n*4+3) *> [1;1;0;1] *> 0inf -->*
  l <* ld0 <* ld1^^(n*3+2) <| rd1 *> 0inf.
Proof. st; repeat (er || sr). Qed.

Lemma Erase_LOv l l': Erase l l' ->
  forall r, l <* [1] <| r -->* l' |> [1;0] *> r.
Proof. unfold Erase; intros HP r; es; follow HP; es. Qed.
Lemma init: c0 -->* ldh <* ld1^^3 <| [1;0;0;0;0;0;0;0;0;1;0;0] *> 0inf.
Proof. esx. Qed.

Module C := SOC43_Extra.Counter.
Lemma marked_calls len k h n r: k+n<2^len -> n<2^(h+1) ->
  C.LC len (k+n) |> C.MC h n r -->* C.LC len k |> C.MC h 0 r.
Proof.
  apply C.MC_Incs with (QL:=E) (Erase:=Erase); auto using LInc,RInc,Blank0,Blank1,Blank3.
Qed.
Lemma marked_zero len k a m: k<2^len ->
  C.LC len k |> C.RC1 (a*4) 0 m -->+
  C.LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> [0] *> C.RC m.
Proof.
  apply C.RC1_Ov0 with (QL:=E) (Erase:=Erase);
    auto using Erase_O,Erase_S0,Erase_S1,Blank0,Blank1,Blank3.
  intros; applys_eq ROv1_0; try flia; unfold LOv'; intro; apply Erase_LOv; assumption.
Qed.
Lemma zero_prefix m: C.RC1 0 1 m = [0] *> C.RC (m*2+1).
Proof. unfold C.RC1,C.MC,C.RC; rw_Bin; reflexivity. Qed.
Lemma zero_once len k n m: k<2^len -> n<=k -> n<2 ->
  C.LC len k |> C.RC1 0 n (m*2+1) -->*
  C.LC (len+1) (2^(len+1)-1) |> C.RC1 0 1 m.
Proof.
  intros Hk Hn Hsmall; rewrite zero_prefix.
  replace k with ((k-n)+n) at 1 by lia; unfold C.RC1 at 1.
  follow marked_calls; try lia; fold C.RC1.
  apply progress_evstep; apply (marked_zero len (k-n) 0 (m*2+1)); lia.
Qed.
Lemma zero_loop t len k n m: k<2^len -> n<=k -> n<2 ->
  C.LC len k |> C.RC1 0 n ((m+1)*2^(1+t)-1) -->*
  C.LC (len+(1+t)) (2^(len+(1+t))-1) |> C.RC1 0 1 m.
Proof.
  revert len k n; induction t; intros len k n Hk Hn Hsmall.
  - applys_eq (zero_once len k n m); flia.
  - replace ((m+1)*2^(1+S t)-1) with (((m+1)*2^(1+t)-1)*2+1)
      by (repeat rewrite Nat.pow_add_r; cbn [Nat.pow]; nia).
    follow zero_once; try lia.
    applys_eq IHt; try flia.
    all: assert (2<=2^(len+1)) by (rewrite Nat.pow_add_r; cbn; lia); lia.
Qed.

Module S := Forward13.
Open Scope nat_scope.

Module Decode.
Definition number (x:Sparse.num) := Z.to_nat (Sparse.value x).
Lemma number_spec x: (0<=Sparse.value x)%Z -> Z.of_nat (number x)=Sparse.value x.
Proof. unfold number; apply Z2Nat.id. Qed.
Lemma power_spec w: Sparse.pow2 w = Z.of_nat (2^N.to_nat w).
Proof. unfold Sparse.pow2; rewrite Nat2Z.inj_pow; f_equal; lia. Qed.
Lemma plus_value x y: Sparse.value (S.plus x y)=(Sparse.value x+Sparse.value y)%Z.
Proof. unfold S.plus; rewrite Sparse.pack_spec, Sparse.add_spec; reflexivity. Qed.
Lemma minus_value x y: Sparse.value (S.minus x y)=(Sparse.value x-Sparse.value y)%Z.
Proof. unfold S.minus; rewrite Sparse.pack_spec, Sparse.sub_spec; reflexivity. Qed.
Lemma full_value w: Sparse.value (S.full w)=(Sparse.pow2 w-1)%Z.
Proof. unfold S.full, S.one; rewrite minus_value, Sparse.power_spec, Sparse.small_spec; reflexivity. Qed.
Lemma plus_spec x y: (0<=Sparse.value x)%Z -> (0<=Sparse.value y)%Z ->
  number (S.plus x y)=number x+number y.
Proof. unfold number; rewrite plus_value; apply Z2Nat.inj_add. Qed.
Lemma minus_spec x y: (0<=Sparse.value x)%Z -> (0<=Sparse.value y)%Z ->
  number (S.minus x y)=number x-number y.
Proof. unfold number; rewrite minus_value; intros; apply Z2Nat.inj_sub; assumption. Qed.
Lemma shift_spec w x: (0<=Sparse.value x)%Z ->
  number (Sparse.shift w x)=2^N.to_nat w*number x.
Proof.
  unfold number; intros; pose proof (Sparse.pow2_pos w).
  rewrite Sparse.shift_spec, Z2Nat.inj_mul; try lia.
  rewrite power_spec, Nat2Z.id; reflexivity.
Qed.

Lemma full_spec w: number (S.full w)=2^N.to_nat w-1.
Proof.
  unfold number; rewrite full_value, Z2Nat.inj_sub; try (pose proof (Sparse.pow2_pos w); lia).
  rewrite power_spec, Nat2Z.id; reflexivity.
Qed.
Lemma small_spec n: number (Sparse.small (Z.of_nat n))=n.
Proof. unfold number; rewrite Sparse.small_spec, Nat2Z.id; reflexivity. Qed.
Lemma lt_spec x y: S.lt x y=true -> (Sparse.value x<Sparse.value y)%Z.
Proof.
  unfold S.lt; destruct (Sparse.compare x y) as [[]|] eqn:H; try discriminate.
  intros _; apply Sparse.compare_spec in H; now apply Z.compare_lt_iff in H.
Qed.
Lemma nonnegative_spec x: Sparse.nonnegative x=true -> (0<=Sparse.value x)%Z.
Proof. apply Sparse.leb_spec. Qed.
Lemma full_nonnegative w: (0<=Sparse.value (S.full w))%Z.
Proof. rewrite full_value; pose proof (Sparse.pow2_pos w); lia. Qed.
Lemma split_nat m i u: Sparse.split m=Some (i,u) ->
  (0<=Sparse.value u)%Z /\ number m=(number u*2+1)*2^N.to_nat i.
Proof.
  intro H; apply Sparse.split_spec in H; destruct H as [Hu Hm]; split; [exact Hu|].
  assert (Hpos: (0<=Sparse.value m)%Z) by (rewrite Hm; pose proof (Sparse.pow2_pos i); nia).
  apply Nat2Z.inj; repeat rewrite Nat2Z.inj_mul; rewrite Nat2Z.inj_add, Nat2Z.inj_mul.
  rewrite (number_spec _ Hpos), (number_spec _ Hu), <-power_spec; cbn [Z.of_nat]; nia.
Qed.
Lemma half_nat m b u: Sparse.half m=Some (b,u) ->
  (0<=Sparse.value u)%Z /\ number m=number u*2+(if b then 1 else 0).
Proof.
  intro H; apply Sparse.half_spec in H; destruct H as [Hu Hm]; split; [exact Hu|].
  destruct b; assert (Hpos: (0<=Sparse.value m)%Z) by lia;
    apply Nat2Z.inj; rewrite Nat2Z.inj_add, Nat2Z.inj_mul;
    rewrite (number_spec _ Hpos), (number_spec _ Hu); cbn [Z.of_nat]; lia.
Qed.

Definition decode (x:S.state) :=
  let w:=N.to_nat (S.width x) in let k:=number (S.budget x) in let m:=number (S.high x) in
  match S.tag x with
  | S.L => C.cfgL w k m | S.R => C.cfgR w k m | S.A => C.cfgA w k m
  | S.T1 => C.cfgR1 w k (N.to_nat (S.mark x)) (number (S.low x)) m
  | S.T2 => C.cfgR2 w k (N.to_nat (S.mark x)) (number (S.low x)) m
  end.
Definition meaning x := C.to_config E B F (decode x).

Lemma good_base p w k h n m: S.good (S.State p w k h n m)=true ->
  (0<w)%N /\ (0<=Sparse.value k<Sparse.pow2 w)%Z /\ (0<=Sparse.value m)%Z.
Proof.
  unfold S.good, S.width, S.budget, S.high, S.tag, S.mark, S.low;
  destruct (N.ltb 0 w) eqn:Hw; [|discriminate];
  destruct (Sparse.nonnegative k) eqn:Hk; [|discriminate];
  destruct (S.lt k (Sparse.power w)) eqn:Hcap; [|discriminate];
  destruct (Sparse.nonnegative m) eqn:Hm; [|discriminate]; intros _.
  apply N.ltb_lt in Hw; apply nonnegative_spec in Hk,Hm; apply lt_spec in Hcap.
  rewrite Sparse.power_spec in Hcap; auto.
Qed.
Lemma good_spec x: S.good x=true -> C.P (decode x).
Proof.
  destruct x as [p w k h n m]; destruct p; intro H;
    unfold S.good,S.width,S.budget,S.high,S.tag,S.mark,S.low in H;
    repeat match type of H with
    | (if ?b then _ else false)=true => let Hb:=fresh "Hb" in destruct b eqn:Hb; [|discriminate]
    end;
    repeat match goal with
    | H: Sparse.nonnegative _=true |- _ => apply nonnegative_spec in H
    | H: S.lt _ _=true |- _ => apply lt_spec in H
    | H: Sparse.leb _ _=true |- _ => apply Sparse.leb_spec in H
    | H: N.ltb _ _=true |- _ => apply N.ltb_lt in H
    end;
    cbn [decode S.tag S.width S.budget S.high S.mark S.low C.P];
    unfold S.one in *; repeat rewrite plus_value in *;
    repeat rewrite Sparse.power_spec in *; rewrite ?Sparse.small_spec in *;
    pose proof (number_spec k ltac:(lia)); pose proof (number_spec m ltac:(lia));
    try pose proof (number_spec n ltac:(lia));
    try rewrite Sparse.pow2_add in H;
    try change (Sparse.pow2 1) with 2%Z in H;
    repeat rewrite power_spec in *; repeat rewrite N2Nat.inj_add in *;
    cbn [N.to_nat Pos.to_nat] in *; lia.
  Opaque Sparse.pack.
Qed.
Transparent Sparse.pack.
End Decode.
Open Scope sym.

Ltac local_rules := auto using LInc,RInc,LOv_0,LOv_1,Erase_O,Erase_S0,Erase_S1,
  Blank0,Blank1,Blank2,Blank3,ROv1_1,ROv1_3,ROv2_2,ROv'_0.
Ltac counter_arith := repeat rewrite Nat.pow_add_r in *; cbn [Nat.pow] in *; nia.
Ltac advance H := eapply evstep_trans; [apply progress_evstep; apply H; lia|].
Lemma left_inc len k r: 1+k<2^len -> C.LC len (1+k) <| r -->+ C.LC len k |> r.
Proof. apply C.LC_Inc with (Erase:=Erase); local_rules. Qed.
Lemma right_inc m l: l |> C.RC m -->+ l <| C.RC (1+m).
Proof. apply C.RC_Inc with (Erase:=Erase); local_rules. Qed.
Lemma left_finish len k m: k<2^len ->
  C.LC len k <| C.RC m -->* C.LC len 0 <| C.RC (k+m).
Proof.
  gen m; induction k; intros; [finish|].
  advance left_inc; advance right_inc.
  applys_eq IHk; flia.
Qed.
Lemma right_finish len k m: k<2^len ->
  C.LC len k |> C.RC m -->* C.LC len 0 <| C.RC (k+m+1).
Proof. intros; advance right_inc; applys_eq left_finish; flia. Qed.

Lemma prefix10 i m: [0] *> C.RC ((m*2+1)*2^i)=C.RC1 i (2^(i+1)-1) m.
Proof.
  replace (2^(i+1)-1) with ((2^i-1)*2+1) by counter_arith.
  unfold C.RC,C.RC1,C.MC; rw_Bin; try solve[counter_arith]; simpl_rotate; reflexivity.
Qed.
Lemma prefix11 i m: [1] *> C.RC ((m*2+1)*2^i)=C.RC1 i (2^(i+1)-1-1) m.
Proof.
  replace (2^(i+1)-1-1) with ((2^i-1)*2) by counter_arith.
  unfold C.RC,C.RC1,C.MC; rw_Bin; try solve[counter_arith]; simpl_rotate; reflexivity.
Qed.
Lemma prefix20 i m: [0;0] *> C.RC ((m*2+1)*2^i)=C.RC2 i (2^(i+1)-1) m.
Proof.
  replace (2^(i+1)-1) with ((2^i-1)*2+1) by counter_arith.
  unfold C.RC,C.RC2,C.MC; rw_Bin; try solve[counter_arith]; simpl_rotate; reflexivity.
Qed.
Lemma prefix21 i m: [1;0;0;0;0] *> C.RC ((m*2+1)*2^i)=C.RC2 (i+1) (2^(i+1+1)-1-1) m.
Proof.
  replace (2^(i+1+1)-1-1) with ((2^(i+1)-1)*2) by counter_arith.
  unfold C.RC,C.RC2,C.MC; rw_Bin; try solve[counter_arith]; simpl_rotate.
  rewrite (Nat.add_comm i 1); cbn [lpow Str_app app]; reflexivity.
Qed.

Import Decode.
Lemma prefix_zero0: [0] *> C.RC 0=C.RC 0.
Proof. unfold C.RC; rw_Bin; cbn; symmetry; apply const_unfold. Qed.
Lemma prefix_zero4: [1;0;0;0;0] *> C.RC 0=C.RC 1.
Proof.
  rewrite <-C.RC_one_prefix.
  change ([1] *> [0;0] *> [0;0] *> C.RC 0=[1] *> C.RC 0).
  rewrite !C.RC_zero_prefix; reflexivity.
Qed.
Ltac solve_prefix m rule :=
  unfold S.prefix,S.iszero; let Hz:=fresh "Hz" in
  destruct (Sparse.eqb m []) eqn:Hz;
  [intros H; inversion H; subst; apply Sparse.eqb_spec in Hz;
    let Hm:=fresh "Hm" in
    assert (Hm: number m=0%nat) by (unfold number; rewrite Hz; reflexivity);
    cbn [meaning decode S.ordinary S.tag S.width S.budget S.high C.to_config];
    rewrite Hm; unfold number at 2; cbn [Sparse.value Sparse.small Z.to_nat];
    rewrite ?prefix_zero0, ?C.RC_one_prefix, ?C.RC_zero_prefix, ?prefix_zero4; reflexivity
  | let Hs:=fresh "Hs" in let i:=fresh "i" in let u:=fresh "u" in
    destruct (Sparse.split m) as [[i u]|] eqn:Hs; [|discriminate];
    intros H; inversion H; subst; apply split_nat in Hs;
    let Hu:=fresh "Hu" in let Hm:=fresh "Hm" in destruct Hs as [Hu Hm];
    cbn [meaning decode S.tag S.width S.budget S.mark S.low S.high C.to_config];
    rewrite minus_spec by (try apply full_nonnegative; rewrite Sparse.small_spec; lia);
    rewrite full_spec;
    change (number (Sparse.small 0)) with 0%nat || change (number (Sparse.small 1)) with 1%nat;
    rewrite ?Nat.sub_0_r, !N2Nat.inj_add; cbn [N.to_nat]; rewrite ?Nat.add_0_r;
    rewrite Hm, rule; reflexivity].
Lemma prefix10_sound w k m y: S.prefix S.T1 w k m 0 0%Z=S.next y ->
  meaning y=C.LC (N.to_nat w) (number k) |> [0] *> C.RC (number m).
Proof. solve_prefix m prefix10. Qed.
Lemma prefix11_sound w k m y: S.prefix S.T1 w k m 0 1%Z=S.next y ->
  meaning y=C.LC (N.to_nat w) (number k) |> [1] *> C.RC (number m).
Proof. solve_prefix m prefix11. Qed.
Lemma prefix20_sound w k m y: S.prefix S.T2 w k m 0 0%Z=S.next y ->
  meaning y=C.LC (N.to_nat w) (number k) |> [0;0] *> C.RC (number m).
Proof. solve_prefix m prefix20. Qed.
Lemma prefix21_sound w k m y: S.prefix S.T2 w k m 1 1%Z=S.next y ->
  meaning y=C.LC (N.to_nat w) (number k) |> [1;0;0;0;0] *> C.RC (number m).
Proof. solve_prefix m prefix21. Qed.

Lemma left_odd len m:
  C.LC len 0 <| C.RC (m*2+1) -->+ C.LC (len+1) (2^(len+1)-1) |> [0] *> C.RC m.
Proof. apply C.LC_Ov_odd with (Erase:=Erase); local_rules. Qed.
Lemma left_even len m:
  C.LC len 0 <| C.RC (m*2) -->+ C.LC len (2^len-1) |> [1;0;0;0;0] *> C.RC m.
Proof.
  unfold C.LC,C.RC; rewrite BinDec_full; rw_Bin; simpl_tape.
  applys_eq LOv_0; flia.
Qed.
Lemma auxiliary_even len k m:
  C.LC len k |2> C.RC (m*2) -->+ C.LC len k |> [0;0] *> C.RC m.
Proof. apply C.Aux_even with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma auxiliary_halt len k m: halts tm (C.LC len k |2> C.RC (m*2+1)).
Proof. unfold C.RC; rewrite BinInc_mul2add1; apply ROv'_1. Qed.

Ltac erase_rule H := intros; applys_eq H; try flia;
  unfold LOv'; intro; apply Erase_LOv; assumption.
Lemma exit11 len k a m: k<2^len ->
  C.LC len k |> C.RC1 (a*4+1) 0 m -->+
  C.LC (len+1+a*3) ((k*2+1)*2^(a*3)-1) |> C.RC (m*2+1).
Proof. apply C.RC1_Ov1 with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma exit12 len k a m: k<2^len ->
  C.LC len k |> C.RC1 (a*4+2) 0 m -->+
  C.LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> C.RC (m*2+1).
Proof. apply C.RC1_Ov2 with (QL:=E) (Erase:=Erase); local_rules; erase_rule ROv1_2. Qed.
Lemma exit13 len k a m: k<2^len ->
  C.LC len k |> C.RC1 (a*4+3) 0 m -->+
  C.LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |> [0] *> C.RC m.
Proof. apply C.RC1_Ov3 with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma exit20 len k a m: k<2^len ->
  C.LC len k |> C.RC2 (a*4) 0 m -->+
  C.LC (len+1+a*3) ((k*2+1)*2^(a*3)) |> [0] *> C.RC m.
Proof.
  apply C.RC2_Ov0 with (QL:=E) (Erase:=Erase); local_rules.
  intros; applys_eq ROv2_0; flia.
Qed.
Lemma exit21 len k a m: k<2^len ->
  C.LC len k |> C.RC2 (a*4+1) 0 m -->+
  C.LC (len+(a*3+2)) (2^(len+(a*3+2))-1) |> [1] *> C.RC m.
Proof. apply C.RC2_Ov1 with (QL:=E) (Erase:=Erase); local_rules; erase_rule ROv2_1. Qed.
Lemma exit22 len k a m: k<2^len ->
  C.LC len k |> C.RC2 (a*4+2) 0 m -->+
  C.LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)-1) |2> C.RC m.
Proof. apply C.RC2_Ov2 with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma exit23 len k a m: k<2^len ->
  C.LC len k |> C.RC2 (a*4+3) 0 m -->+
  C.LC (len+(a*3+4)) (2^(len+(a*3+4))-1) |2> C.RC m.
Proof. apply C.RC2_Ov3 with (QL:=E) (Erase:=Erase); local_rules; erase_rule ROv2_3. Qed.

Lemma corner_start h:
  C.LC (h+1) 0 <| C.RC (2^(h+1)) -->* C.LC (h+1+1) (2^(h+1)) |> C.RC' h 0.
Proof. apply progress_evstep; apply C.corner_case with (Erase:=Erase); local_rules. Qed.
Lemma blank0 len k a: k<2^len ->
  C.LC len k |> C.RC' (a*4) 0 -->*
  C.LC (len+(a*3+1)) (2^(len+(a*3+1))-1) |> C.RC 1.
Proof. apply C.RC'_Ov0 with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma blank1 len k a: k<2^len ->
  C.LC len k |> C.RC' (a*4+1) 0 -->*
  C.LC (len+1+(a*3+1)) ((k*2+1)*2^(a*3+1)) <| C.RC 0.
Proof. apply C.RC'_Ov1 with (QR:=B) (Erase:=Erase); local_rules. Qed.
Lemma blank2 len k a: k<2^len ->
  C.LC len k |> C.RC' (a*4+2) 0 -->*
  C.LC (len+(a*3+3)) (2^(len+(a*3+3))-1) |> C.RC 0.
Proof. apply C.RC'_Ov2 with (QL:=E) (Erase:=Erase); local_rules. Qed.
Lemma blank3 len k a: k<2^len ->
  C.LC len k |> C.RC' (a*4+3) 0 -->*
  C.LC (len+1+(a*3+2)) ((k*2+1)*2^(a*3+2)) <| C.RC 1.
Proof. apply C.RC'_Ov3 with (QR:=B) (Erase:=Erase); local_rules. Qed.

Lemma corner0 len a: len=a*4+1 ->
  C.LC len 0 <| C.RC (2^len) -->*
  C.LC (len+a*3+2) 0 <| C.RC (2^(len+a*3+2)+1).
Proof.
  intros ->; follow corner_start; follow blank0; [counter_arith|].
  replace (a*4+1+1+(a*3+1)) with (a*4+1+a*3+2) by lia.
  replace (2^(a*4+1+a*3+2)+1) with ((2^(a*4+1+a*3+2)-1)+1+1) by lia.
  apply right_finish; lia.
Qed.
Lemma corner1 len a: len=a*4+2 ->
  C.LC len 0 <| C.RC (2^len) -->*
  C.LC (len+a*3+3) 0 <| C.RC ((2^len*2+1)*2^(a*3+1)).
Proof.
  intros H; replace len with (a*4+1+1) by lia.
  follow corner_start; follow blank1; [counter_arith|].
  applys_eq (left_finish (a*4+1+1+1+1+(a*3+1))
    ((2^(a*4+1+1)*2+1)*2^(a*3+1)) 0); flia.
  counter_arith.
Qed.
Lemma corner2 len a: len=a*4+3 ->
  C.LC len 0 <| C.RC (2^len) -->*
  C.LC (len+a*3+4) 0 <| C.RC (2^(len+a*3+4)).
Proof.
  intros H; replace len with (a*4+2+1) by lia.
  follow corner_start; follow blank2; [counter_arith|].
  replace (a*4+2+1+1+(a*3+3)) with (a*4+2+1+a*3+4) by lia.
  replace (2^(a*4+2+1+a*3+4)) with ((2^(a*4+2+1+a*3+4)-1)+0+1) at 2 by lia.
  apply right_finish; lia.
Qed.
Lemma corner3 len a: len=a*4+4 ->
  C.LC len 0 <| C.RC (2^len) -->*
  C.LC (len+a*3+4) 0 <| C.RC ((2^len*2+1)*2^(a*3+2)+1).
Proof.
  intros H; replace len with (a*4+3+1) by lia.
  follow corner_start; follow blank3; [counter_arith|].
  applys_eq (left_finish (a*4+3+1+1+1+(a*3+2))
    ((2^(a*4+3+1)*2+1)*2^(a*3+2)) 1); flia.
  counter_arith.
Qed.

Lemma number_power w: number (Sparse.power w)=2^N.to_nat w.
Proof. unfold number; rewrite Sparse.power_spec,power_spec,Nat2Z.id; reflexivity. Qed.
Lemma good_low p w k h n m: p=S.T1 \/ p=S.T2 ->
  S.good (S.State p w k h n m)=true -> (0<=Sparse.value n)%Z.
Proof.
  intros [H|H]; subst p; unfold S.good,S.width,S.budget,S.high,S.tag,S.mark,S.low;
    repeat match goal with |- (if ?b then _ else false)=true -> _ =>
      destruct b eqn:?; [|discriminate] end;
    intros; eapply nonnegative_spec; eassumption.
Qed.
Ltac positive_values :=
  unfold S.one,S.twice;
  repeat match goal with |- context [Sparse.value ?x] => lazymatch x with
    | S.full ?w => rewrite (full_value w)
    | S.minus ?a ?b => rewrite (minus_value a b)
    | S.plus ?a ?b => rewrite (plus_value a b)
    | Sparse.shift ?w ?a => rewrite (Sparse.shift_spec w a)
    | Sparse.power ?w => rewrite (Sparse.power_spec w)
    | Sparse.small ?z => rewrite (Sparse.small_spec z)
    end end;
  repeat apply Z.mul_nonneg_nonneg;
  try solve [apply Z.lt_le_incl; apply Sparse.pow2_pos];
  repeat match goal with |- context [Sparse.pow2 ?w] =>
    let p:=fresh "p" in let Hp:=fresh "Hp" in let He:=fresh "He" in
    remember (Sparse.pow2 w) as p eqn:He in *;
    assert (Hp: (0<p)%Z) by (subst p; apply Sparse.pow2_pos); clear He end; nia.
Ltac numbers :=
  unfold S.one,S.twice;
  repeat match goal with |- context [number ?x] => lazymatch x with
    | S.full ?w => rewrite (full_spec w)
    | S.minus ?a ?b => rewrite (minus_spec a b) by positive_values
    | S.plus ?a ?b => rewrite (plus_spec a b) by positive_values
    | Sparse.shift ?w ?a => rewrite (shift_spec w a) by positive_values
    | Sparse.power ?w => rewrite (number_power w)
    end end;
  repeat first [rewrite N2Nat.inj_add | rewrite N2Nat.inj_mul | rewrite N2Nat.inj_sub];
  cbn [N.to_nat Pos.to_nat];
  try change (Pos.to_nat 1) with 1%nat;
  try change (Pos.to_nat 2) with 2%nat;
  try change (Pos.to_nat 3) with 3%nat;
  try change (Pos.to_nat 4) with 4%nat;
  change (number []) with 0%nat || idtac;
  change (number (Sparse.small 1)) with 1%nat || idtac;
  change (number (Sparse.small 0)) with 0%nat || idtac.
Ltac decode_state := cbn [meaning decode S.ordinary S.tag S.width S.budget S.high S.mark S.low C.to_config].
Ltac initial_facts Hg :=
  let HW:=fresh "HW" in let HK:=fresh "HK" in let HM:=fresh "HM" in
  destruct (good_base _ _ _ _ _ _ Hg) as [HW [HK HM]];
  let HP:=fresh "HP" in pose proof (good_spec _ Hg) as HP;
  cbn [decode S.tag S.width S.budget S.high S.mark S.low C.P] in HP.

Opaque S.plus S.minus S.full Sparse.pack.
Lemma step_R w k h n m y: S.good (S.State S.R w k h n m)=true ->
  S.step (S.State S.R w k h n m)=S.next y ->
  meaning (S.State S.R w k h n m) -->* meaning y.
Proof.
  intros Hg H; initial_facts Hg; inversion H; subst; decode_state; numbers.
  apply right_finish; lia.
Qed.
Lemma step_A w k h n m y: S.good (S.State S.A w k h n m)=true ->
  S.step (S.State S.A w k h n m)=S.next y ->
  meaning (S.State S.A w k h n m) -->* meaning y.
Proof.
  intros Hg; initial_facts Hg; unfold S.step,S.tag,S.width,S.budget,S.high.
  destruct (Sparse.half m) as [[b u]|] eqn:Hh; [destruct b|]; try discriminate; intro H.
  apply prefix20_sound in H; rewrite H; decode_state.
  apply half_nat in Hh; destruct Hh as [Hu Hm]; rewrite Hm; cbn.
  replace (number u*2+0) with (number u*2) by lia.
  apply progress_evstep; apply auxiliary_even; lia.
Qed.

Lemma div4 w: N.to_nat w=N.to_nat (w/4)*4+N.to_nat (w mod 4) /\ N.to_nat (w mod 4)<4.
Proof.
  pose proof (N.div_mod w 4 ltac:(discriminate)).
  pose proof (N.mod_lt w 4 ltac:(discriminate)); split; lia.
Qed.
Lemma eqb_number x y: Sparse.eqb x y=true -> number x=number y.
Proof. intro H; apply Sparse.eqb_spec in H; unfold number; now rewrite H. Qed.

Opaque N.mul Sparse.pack.
Lemma step_L w k h n m y: S.good (S.State S.L w k h n m)=true ->
  S.step (S.State S.L w k h n m)=S.next y ->
  meaning (S.State S.L w k h n m) -->* meaning y.
Proof.
  intros Hg; initial_facts Hg.
  unfold S.step,S.tag,S.width,S.budget,S.high.
  set (v:=S.plus k m).
  assert (Hv: number v=number k+number m) by (unfold v; numbers; reflexivity).
  intro Hstep.
  eapply evstep_trans with (c':=C.LC (N.to_nat w) 0 <| C.RC (number v)).
  - decode_state; rewrite Hv; apply left_finish; lia.
  - revert Hstep; destruct (Sparse.eqb v (Sparse.power w)) eqn:He.
    + apply eqb_number in He; rewrite number_power in He; rewrite He.
      destruct (div4 (w-1)) as [Hd Hr].
      remember ((w-1)/4)%N as a; remember ((w-1) mod 4)%N as e.
      destruct (N.eqb e 0) eqn:E0; [apply N.eqb_eq in E0; subst e|];
      [|destruct (N.eqb e 1) eqn:E1; [apply N.eqb_eq in E1; subst e|]];
      [| |destruct (N.eqb e 2) eqn:E2; [apply N.eqb_eq in E2; subst e|]].
      all: intro H; injection H as <-; decode_state; numbers;
        replace (3*N.to_nat a) with (N.to_nat a*3) by lia.
      * applys_eq (corner0 (N.to_nat w) (N.to_nat a)); flia.
      * rewrite (Nat.pow_add_r 2 (N.to_nat w) 1); cbn [Nat.pow].
        applys_eq (corner1 (N.to_nat w) (N.to_nat a)); flia.
      * applys_eq (corner2 (N.to_nat w) (N.to_nat a)); flia.
      * apply N.eqb_neq in E0,E1,E2.
        rewrite (Nat.pow_add_r 2 (N.to_nat w) 1); cbn [Nat.pow].
        applys_eq (corner3 (N.to_nat w) (N.to_nat a)); flia.
    + destruct (Sparse.half v) as [[b u]|] eqn:Hh; [destruct b|]; try discriminate; intro H.
      * apply prefix10_sound in H; rewrite H; numbers.
        apply half_nat in Hh; destruct Hh as [Hu Hm]; rewrite Hm.
        apply progress_evstep; apply left_odd.
      * apply prefix21_sound in H; rewrite H; numbers.
        apply half_nat in Hh; destruct Hh as [Hu Hm]; rewrite Hm, Nat.add_0_r.
        apply progress_evstep; apply left_even.
Qed.

Lemma step_T2 w k h n m y: S.good (S.State S.T2 w k h n m)=true ->
  S.step (S.State S.T2 w k h n m)=S.next y ->
  meaning (S.State S.T2 w k h n m) -->* meaning y.
Proof.
  intros Hg Hstep; initial_facts Hg.
  pose proof (good_low S.T2 w k h n m ltac:(auto) Hg) as Hn.
  pose proof (number_spec n Hn); pose proof (number_spec k ltac:(lia)).
  assert (Hb: (0<=Sparse.value (S.minus k n))%Z) by (rewrite minus_value; lia).
  decode_state.
  replace (number k) with ((number k-number n)+number n) at 1 by lia.
  unfold C.RC2 at 1; follow marked_calls; try lia; fold (C.RC2 (N.to_nat h) 0 (number m)).
  unfold S.step,S.tag,S.width,S.budget,S.high,S.mark,S.low in Hstep.
  destruct (div4 h) as [Hd Hr].
  remember (h/4)%N as a; remember (h mod 4)%N as e.
  destruct (N.eqb e 0) eqn:E0; [apply N.eqb_eq in E0; subst e|];
  [|destruct (N.eqb e 1) eqn:E1; [apply N.eqb_eq in E1; subst e|]];
  [| |destruct (N.eqb e 2) eqn:E2; [apply N.eqb_eq in E2; subst e|]].
  - apply prefix10_sound in Hstep; rewrite Hstep.
    numbers; replace (3*N.to_nat a) with (N.to_nat a*3) by lia; change (2^1) with 2%nat.
    replace (N.to_nat h) with (N.to_nat a*4) by lia.
    apply progress_evstep; applys_eq (exit20 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
  - apply prefix11_sound in Hstep; rewrite Hstep; numbers.
    apply progress_evstep; applys_eq (exit21 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
  - injection Hstep as <-; decode_state; numbers.
    replace (3*N.to_nat a) with (N.to_nat a*3) by lia; change (2^1) with 2%nat.
    apply progress_evstep; applys_eq (exit22 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
  - injection Hstep as <-; decode_state; numbers; apply N.eqb_neq in E0,E1,E2.
    apply progress_evstep; applys_eq (exit23 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
Qed.

Lemma zero_batch t len k m: 0<t -> k<2^len ->
  C.LC len k |> C.RC1 0 0 ((m+1)*2^t-1) -->*
  C.LC (len+t) (2^(len+t)-1) |> C.RC1 0 1 m.
Proof. destruct t; [lia|]; intros; apply zero_loop; lia. Qed.

Lemma step_T1 w k h n m y: S.good (S.State S.T1 w k h n m)=true ->
  S.step (S.State S.T1 w k h n m)=S.next y ->
  meaning (S.State S.T1 w k h n m) -->* meaning y.
Proof.
  intros Hg Hstep; initial_facts Hg.
  pose proof (good_low S.T1 w k h n m ltac:(auto) Hg) as Hn.
  pose proof (number_spec n Hn); pose proof (number_spec k ltac:(lia)).
  assert (Hb: (0<=Sparse.value (S.minus k n))%Z) by (rewrite minus_value; lia).
  decode_state.
  replace (number k) with ((number k-number n)+number n) at 1 by lia.
  unfold C.RC1 at 1; follow marked_calls; try lia; fold (C.RC1 (N.to_nat h) 0 (number m)).
  unfold S.step,S.tag,S.width,S.budget,S.high,S.mark,S.low in Hstep.
  destruct (N.eqb h 0) eqn:Hh.
  - apply N.eqb_eq in Hh; subst h; cbn [N.to_nat] in *.
    destruct (Sparse.half m) as [[b v]|] eqn:Hhalf; [destruct b|]; try discriminate.
    + destruct (Sparse.split (S.plus m S.one)) as [[t u]|] eqn:Hsplit; [|discriminate].
      destruct (N.ltb 0 t) eqn:Ht; [|discriminate]; apply N.ltb_lt in Ht.
      injection Hstep as <-; decode_state.
      apply split_nat in Hsplit; destruct Hsplit as [Hu Hm].
      rewrite plus_spec in Hm by (unfold S.one; positive_values).
      change (number S.one) with 1%nat in Hm.
      numbers; change (2^1) with 2%nat.
      replace (number m) with ((2*number u+1)*2^N.to_nat t-1) by nia.
      apply zero_batch; lia.
    + apply prefix10_sound in Hstep; rewrite Hstep; numbers.
      apply progress_evstep; applys_eq (marked_zero (N.to_nat w) (number k-number n) 0 (number m)); flia.
  - destruct (div4 h) as [Hd Hr].
    remember (h/4)%N as a; remember (h mod 4)%N as e.
    destruct (N.eqb e 0) eqn:E0; [apply N.eqb_eq in E0; subst e|];
    [|destruct (N.eqb e 1) eqn:E1; [apply N.eqb_eq in E1; subst e|]];
    [| |destruct (N.eqb e 2) eqn:E2; [apply N.eqb_eq in E2; subst e|]].
    + apply prefix10_sound in Hstep; rewrite Hstep; numbers.
      apply progress_evstep; applys_eq (marked_zero (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
    + injection Hstep as <-; decode_state; numbers.
      replace (3*N.to_nat a) with (N.to_nat a*3) by lia; change (2^1) with 2%nat.
      apply progress_evstep; applys_eq (exit11 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
    + injection Hstep as <-; decode_state; numbers; change (2^1) with 2%nat.
      apply progress_evstep; applys_eq (exit12 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
    + apply prefix10_sound in Hstep; rewrite Hstep; numbers; apply N.eqb_neq in E0,E1,E2.
      replace (3*N.to_nat a) with (N.to_nat a*3) by lia; change (2^1) with 2%nat.
      apply progress_evstep; applys_eq (exit13 (N.to_nat w) (number k-number n) (N.to_nat a) (number m)); flia.
Qed.

Lemma step_sound x y: S.good x=true -> S.step x=S.next y -> meaning x -->* meaning y.
Proof. destruct x as [[] w k h n m]; eauto using step_L,step_R,step_T1,step_T2,step_A. Qed.
Lemma prefix_not_halted p w k m a b: S.prefix p w k m a b<>S.halted.
Proof.
  unfold S.prefix; destruct (S.iszero m); [discriminate|].
  destruct (Sparse.split m) as [[i u]|]; discriminate.
Qed.
Lemma halted_sound x: S.good x=true -> S.step x=S.halted -> halts tm (meaning x).
Proof.
  destruct x as [p w k h n m]; destruct p; intros Hg Hstep;
    unfold S.step,S.tag,S.width,S.budget,S.high,S.mark,S.low in Hstep.
  all: repeat match type of Hstep with
    | (if ?b then _ else _)=S.halted => destruct b eqn:?; try discriminate
    | S.prefix _ _ _ _ _ _=S.halted => exfalso; eapply prefix_not_halted; exact Hstep
    | context [Sparse.half ?v] =>
      let E:=fresh "Ehalf" in let b:=fresh "b" in let u:=fresh "u" in
      destruct (Sparse.half v) as [[b u]|] eqn:E; [destruct b|]; try discriminate
    | context [Sparse.split ?v] =>
      let E:=fresh "Esplit" in let i:=fresh "i" in let u:=fresh "u" in
      destruct (Sparse.split v) as [[i u]|] eqn:E; try discriminate
    end; try discriminate.
  apply half_nat in Ehalf; destruct Ehalf as [Hu Hm]; decode_state; rewrite Hm.
  apply auxiliary_halt.
Qed.
Lemma check_sound fuel x: S.check fuel x=true -> halts tm (meaning x).
Proof.
  revert x; induction fuel as [|fuel IH]; [discriminate|]; intros x.
  cbn [S.check]; destruct (S.good x) eqn:Hg; [|discriminate].
  destruct (S.step x) as [y| |] eqn:Hs; [|intros _; apply halted_sound; assumption|discriminate].
  intro H; eapply halts_evstep; [apply IH; exact H|eapply step_sound; eassumption].
Qed.

Lemma seed_init: c0 -->* meaning S.seed.
Proof.
  unfold S.seed; decode_state; change (number []) with 0%nat.
  unfold number; rewrite Sparse.pack_spec,Sparse.small_spec.
  change (Z.to_nat 9) with 9%nat; change (N.to_nat 3) with 3%nat.
  unfold C.LC,C.RC; rw_Bin; simpl_tape; apply init.
Qed.
Theorem halt: halts tm c0.
Proof.
  eapply halts_evstep; [apply (check_sound 256); exact S.numerical_halt|apply seed_init].
Qed.

End TM10.
