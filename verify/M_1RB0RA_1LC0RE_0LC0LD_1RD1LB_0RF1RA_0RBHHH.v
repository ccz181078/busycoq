(* 1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB--- never halts. *)

From BusyCoq Require Import Individual62.
From Coq Require Import Lia ZifyNat PeanoNat String List.
Import ListNotations.

Open Scope list.
Open Scope sym.

Definition tm := Eval compute in
  (TM_from_str "1RB0RA_1LC0RE_0LC0LD_1RD1LB_0RF1RA_0RB---").

Notation "c --> c'" := (c -[ tm ]-> c')   (at level 40).
Notation "c -->* c'" := (c -[ tm ]->* c') (at level 40).
Notation "c -->+ c'" := (c -[ tm ]->+ c') (at level 40).

Definition ld : list Sym := [1; 1; 0]%sym.
Definition d0 : list Sym := [0; 0; 0]%sym.
Definition d1 : list Sym := [1; 0; 0]%sym.
Definition w1ld : list Sym := [1; 1; 1; 0]%sym.
Definition w1d0 : list Sym := [1; 0; 0; 0]%sym.
Definition w1d1 : list Sym := [1; 1; 0; 0]%sym.
Definition lh : side := [1]%sym *> 0inf%sym.

Open Scope nat_scope.

Lemma zDd : d0 *> 0inf%sym = 0inf%sym.
Proof. unfold d0. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Lemma z1_eq : [1]%sym *> (d1 *> 0inf%sym) = ld *> 0inf%sym.
Proof. unfold d1, ld. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Lemma z0_eq : [1]%sym *> (d0 *> 0inf%sym) = d1 *> 0inf%sym.
Proof. unfold d0, d1. cbn [Str_app]. repeat rewrite <- const_unfold. reflexivity. Qed.

Inductive Call : Type :=
  | ch
  | ch'.

Definition zCs (c : Call) : Q :=
  match c with
  | ch => B
  | ch' => D
  end.

Definition zCw (c : Call) : list Sym :=
  match c with
  | ch => []
  | ch' => [1]%sym
  end.

Definition zCR (l : side) (c : Call) (r : side) : Q * tape :=
  (zCw c *> l) {{zCs c}}> r.

Definition zCL (l : side) (r : side) : Q * tape :=
  l <{{C}} r.

Definition z04 (c : Call) (r1 r2 : side) : Prop :=
  forall l : side, zCR l c r1 -->+ zCL l r2.

Inductive Side : list Call -> side -> side -> Prop :=
  | Side_nil (r : side) : Side [] r r
  | Side_cons (c : Call) (ls : list Call) (r1 r2 r3 : side) :
      z04 c r1 r2 -> Side ls r2 r3 -> Side (c :: ls) r1 r3.

Definition Seg (ls_in ls_out : list Call) (w1 w2 : list Sym) : Prop :=
  forall r1 r2 : side, Side ls_out r1 r2 -> Side ls_in (w1 *> r1) (w2 *> r2).

Lemma z07 {A : Type} (l : list A) (m n : nat) : l ^^ (m + n) = l ^^ m ++ l ^^ n.
Proof. apply lpow_add. Qed.

Lemma z08 {ls1 ls2 : list Call} {r1 r2 r3 : side}
    (h1 : Side ls1 r1 r2) (h2 : Side ls2 r2 r3) : Side (ls1 ++ ls2) r1 r3.
Proof.
  induction h1 as [r | c ls ra rb rc hc _ ih].
  - exact h2.
  - exact (Side_cons c (ls ++ ls2) ra rb _ hc (ih h2)).
Qed.

Lemma z09 {ls1 ls2 : list Call} {r1 r3 : side}
    (h : Side (ls1 ++ ls2) r1 r3) : exists r2 : side, Side ls1 r1 r2 /\ Side ls2 r2 r3.
Proof.
  revert r1 h.
  induction ls1 as [| c ls1 ih]; intros r1 h.
  - exists r1. split; [exact (Side_nil r1) | exact h].
  - cbn [app] in h. inverts h as hc hrest.
    destruct (ih _ hrest) as [rmid [ha hb]].
    exists rmid. split; [exact (Side_cons c ls1 r1 _ rmid hc ha) | exact hb].
Qed.

Lemma z0a (w : list Sym) : Seg [] [] w w.
Proof.
  intros r1 r2 h. inverts h. exact (Side_nil (w *> r2)).
Qed.

Lemma zSc {ls1 ls2 : list Call} {w1 w2 : list Sym} {r1 r2 : side}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Side ls2 r1 r2) :
    Side ls1 (w1 *> r1) (w2 *> r2).
Proof. exact (h1 r1 r2 h2). Qed.

Lemma zSg {ls1 ls2 ls3 ls4 : list Call} {w1 w2 w3 : list Sym}
    (h1 : Seg ls1 ls2 w1 w2) (h2 : Seg ls3 ls4 w2 w3) :
    Seg (ls1 ++ ls3) (ls2 ++ ls4) w1 w3.
Proof.
  intros r1 r3 h.
  destruct (z09 h) as [r2 [ha hb]].
  exact (z08 (h1 r1 r2 ha) (h2 r2 r3 hb)).
Qed.

Lemma zS4 {c : Call} {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c (w1 *> r) -->+ zCL l (w2 *> r)) :
    Seg [c] [] w1 w2.
Proof.
  intros r1 r2 h. inverts h.
  exact (Side_cons c [] (w1 *> r2) (w2 *> r2) (w2 *> r2) (fun l => h1 l r2) (Side_nil _)).
Qed.

Lemma zS2 {c_in c_out : Call} (mid : list Sym) {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c_in (w1 *> r) -->+ zCR (mid *> l) c_out r)
    (h2 : forall l r : side, zCL (mid *> l) r -->+ zCL l (w2 *> r)) :
    Seg [c_in] [c_out] w1 w2.
Proof.
  intros r1 r2 h. inverts h as hc hnil. inverts hnil.
  apply Side_cons with (r2 := w2 *> r2); [| apply Side_nil].
  intro l.
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc (mid *> l)) | exact (h2 l r2)].
Qed.

Lemma zS5 {c_in c1 c2 : Call} (mid1 mid2 : list Sym) {w1 w2 : list Sym}
    (h1 : forall l r : side, zCR l c_in (w1 *> r) -->+ zCR (mid1 *> l) c1 r)
    (h2 : forall l r : side, zCL (mid1 *> l) r -->+ zCR (mid2 *> l) c2 r)
    (h3 : forall l r : side, zCL (mid2 *> l) r -->+ zCL l (w2 *> r)) :
    Seg [c_in] [c1; c2] w1 w2.
Proof.
  intros r1 r3 h. inverts h as hc1 hrest. inverts hrest as hc2 hnil. inverts hnil.
  apply Side_cons with (r2 := w2 *> r3); [| apply Side_nil].
  intro l.
  eapply progress_trans; [exact (h1 l r1) |].
  eapply progress_trans; [exact (hc1 (mid1 *> l)) |].
  eapply progress_trans; [exact (h2 l _) |].
  eapply progress_trans; [exact (hc2 (mid2 *> l)) | exact (h3 l r3)].
Qed.

Lemma seg_ch_d0 : Seg [ch] [] d0 d1.
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d0, d1; es. Qed.

Lemma seg_ch_d1 : Seg [ch] [ch] d1 d0.
Proof.
  apply (zS2 [0; 0; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, d1, d0; es.
Qed.

Lemma seg_ch_ld : Seg [ch] [ch] ld ld.
Proof.
  apply (zS2 [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, ld; es.
Qed.

Lemma seg_ch'_ld_atom : Seg [ch'] [ch; ch'] ld ld.
Proof.
  apply (zS5 [1; 0; 1; 0]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, ld; es.
Qed.

Lemma seg_ch_w1ld_atom : Seg [ch] [ch; ch'] w1ld ld.
Proof.
  apply (zS5 [1; 0; 1; 0]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, w1ld, ld; es.
Qed.

Lemma seg_ch'_d1 : Seg [ch'] [] d1 (ld ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d1, ld; cbn [app]; es. Qed.

Lemma seg_ch'_d0_atom : Seg [ch'] [ch'; ch] d0 ld.
Proof.
  apply (zS5 [1; 1; 1]%sym [1; 1; 0]%sym); intros l r;
    unfold zCR, zCL, zCw, zCs, d0, ld; es.
Qed.

Lemma seg_ch_1d1 : Seg [ch] [] ([1]%sym ++ d1) (ld ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d1, ld; cbn [app]; es. Qed.

Lemma seg_ch_1d0 : Seg [ch] [] ([1]%sym ++ d0) (d0 ++ [1]%sym).
Proof. apply zS4; intros l r; unfold zCR, zCL, zCw, zCs, d0; cbn [app]; es. Qed.

Lemma seg_wall_ld (k : nat) : Seg ([ch] ^^ k) ([ch] ^^ k) ld ld.
Proof.
  induction k as [| k ih].
  - exact (z0a ld).
  - cbn [lpow app]. exact (zSg seg_ch_ld ih).
Qed.

Lemma zSa {w2 : list Sym} (hw : Seg [ch; ch] [ch] w2 w2) (n : nat) :
    Seg ([ch] ^^ (n * 2)) ([ch] ^^ n) w2 w2.
Proof.
  induction n as [| n ih].
  - exact (z0a w2).
  - replace (S n * 2) with (2 + n * 2) by lia.
    rewrite z07. cbn [lpow app].
    exact (zSg hw ih).
Qed.

Lemma seg_ch2_d0 : Seg [ch; ch] [ch] d0 d0.
Proof. exact (zSg seg_ch_d0 seg_ch_d1). Qed.

Lemma seg_ch2_d1 : Seg [ch; ch] [ch] d1 d1.
Proof. exact (zSg seg_ch_d1 seg_ch_d0). Qed.

Lemma seg_d0_even (k : nat) : Seg ([ch] ^^ (k * 2)) ([ch] ^^ k) d0 d0.
Proof. exact (zSa seg_ch2_d0 k). Qed.

Lemma seg_d1_even (k : nat) : Seg ([ch] ^^ (k * 2)) ([ch] ^^ k) d1 d1.
Proof. exact (zSa seg_ch2_d1 k). Qed.

Lemma seg_d0_odd (k : nat) : Seg ([ch] ^^ (1 + k * 2)) ([ch] ^^ k) d0 d1.
Proof.
  change ([ch] ^^ (1 + k * 2)) with ([ch] ++ [ch] ^^ (k * 2)).
  change ([ch] ^^ k) with ([] ++ [ch] ^^ k).
  exact (zSg seg_ch_d0 (seg_d1_even k)).
Qed.

Lemma seg_hx_ld (k : nat) : Seg ([ch'] ++ [ch] ^^ k) ([ch] ++ ([ch'] ++ [ch] ^^ k)) ld ld.
Proof.
  change ([ch] ++ ([ch'] ++ [ch] ^^ k)) with ([ch; ch'] ++ [ch] ^^ k).
  exact (zSg seg_ch'_ld_atom (seg_wall_ld k)).
Qed.

Lemma seg_h1_ld (k : nat) : Seg ([ch] ^^ (1 + k)) ([ch] ++ ([ch'] ++ [ch] ^^ k)) w1ld ld.
Proof.
  change ([ch] ^^ (1 + k)) with ([ch] ++ [ch] ^^ k).
  change ([ch] ++ ([ch'] ++ [ch] ^^ k)) with ([ch; ch'] ++ [ch] ^^ k).
  exact (zSg seg_ch_w1ld_atom (seg_wall_ld k)).
Qed.

Lemma seg_hx_d0 (k : nat) : Seg ([ch'] ++ [ch] ^^ k) ([ch'] ++ [ch] ^^ (1 + k)) d0 ld.
Proof.
  change ([ch'] ++ [ch] ^^ (1 + k)) with ([ch'; ch] ++ [ch] ^^ k).
  exact (zSg seg_ch'_d0_atom (seg_wall_ld k)).
Qed.

Inductive RD : Type :=
  | LD
  | D0
  | D1
  | W1LD
  | W1D0
  | W1D1.

Inductive H : Type :=
  | hi
  | hx
  | h1.

Fixpoint toRC (ls : list RD) : side :=
  match ls with
  | [] => 0inf%sym
  | LD :: ls' => ld *> toRC ls'
  | D0 :: ls' => d0 *> toRC ls'
  | D1 :: ls' => d1 *> toRC ls'
  | W1LD :: ls' => w1ld *> toRC ls'
  | W1D0 :: ls' => w1d0 *> toRC ls'
  | W1D1 :: ls' => w1d1 *> toRC ls'
  end.

Definition toH' (tp : H) : list Sym :=
  match tp with
  | hi => []
  | hx => []
  | h1 => [1]%sym
  end.

Definition toH (tp : H) : list Call :=
  match tp with
  | hi => [ch]
  | hx => [ch']
  | h1 => []
  end.

Inductive RIncs : H -> nat -> list RD -> list RD -> Prop :=
  | hi_nil : RIncs hi 0 [] [D1]
  | hi_d0 (r : list RD) : RIncs hi 0 (D0 :: r) (D1 :: r)
  | hi_d1 {r r' : list RD} : RIncs hi 0 r r' -> RIncs hi 0 (D1 :: r) (D0 :: r')
  | hi_ld {r r' : list RD} : RIncs hi 0 r r' -> RIncs hi 0 (LD :: r) (LD :: r')
  | hi_w1d0 {r r' : list RD} : RIncs h1 0 r r' -> RIncs hi 0 (W1D0 :: r) (D0 :: r')
  | hi_w1d1 {r r' : list RD} : RIncs h1 0 r r' -> RIncs hi 0 (W1D1 :: r) (LD :: r')
  | hi_w1ld {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx 0 r1 r' -> RIncs hi 0 (W1LD :: r) (LD :: r')
  | hx_ld {k : nat} {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx k r1 r' -> RIncs hx k (LD :: r) (LD :: r')
  | hx_d1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs hx k (D1 :: r) (LD :: r')
  | hx_d0 {k : nat} {r r' : list RD} :
      RIncs hx (1 + k) r r' -> RIncs hx k (D0 :: r) (LD :: r')
  | h1_ld {k : nat} {r r1 r' : list RD} :
      RIncs hi 0 r r1 -> RIncs hx k r1 r' -> RIncs h1 (1 + k) (LD :: r) (LD :: r')
  | h1_d1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k) (D1 :: r) (LD :: r')
  | h1_d0_0 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (1 + k * 2) (D0 :: r) (D0 :: r')
  | h1_d0_1 {k : nat} {r r' : list RD} :
      RIncs h1 k r r' -> RIncs h1 (2 + k * 2) (D0 :: r) (D1 :: r')
  | h1_rh_0 :
      RIncs h1 0 [] [D1]
  | h1_rh_1 {k : nat} {r' : list RD} :
      RIncs h1 k [] r' -> RIncs h1 (1 + k * 2) [] (D0 :: r')
  | h1_rh_2 {k : nat} {r' : list RD} :
      RIncs h1 k [] r' -> RIncs h1 (2 + k * 2) [] (D1 :: r')
  | h1_z1 :
      RIncs h1 0 [D1] [LD]
  | h1_z0 :
      RIncs h1 0 [D0] [D1]
  | h1_z_ld {r r1 r2 : list RD} :
      RIncs hi 0 r r1 -> RIncs hx 0 r1 r2 -> RIncs h1 0 (LD :: r) (W1LD :: r)
  | h1_z_d1 {r r1 : list RD} :
      r <> [] -> RIncs h1 0 r r1 -> RIncs h1 0 (D1 :: r) (W1D1 :: r)
  | h1_z_d0 {r r1 : list RD} :
      r <> [] -> RIncs h1 0 r r1 -> RIncs h1 0 (D0 :: r) (W1D0 :: r).

Lemma side_nil_eq {r1 r2 : side} (h : Side [] r1 r2) : r1 = r2.
Proof. inverts h; reflexivity. Qed.

Lemma RIncs_spec {tp : H} {k : nat} {r r' : list RD} (h : RIncs tp k r r') :
    Side (toH tp ++ [ch] ^^ k) (toH' tp *> toRC r) (toRC r').
Proof.
  induction h.
  - cbn [toH toH' toRC lpow app Str_app].
    rewrite <- zDd at 1.
    exact (zSc seg_ch_d0 (Side_nil 0inf%sym)).
  - cbn [toH toH' toRC lpow app Str_app].
    exact (zSc seg_ch_d0 (Side_nil (toRC r))).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_d1 IHh).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_ld IHh).
  - cbn [toH toH' toRC lpow app] in *.
    rewrite <- (side_nil_eq IHh).
    exact (zSc seg_ch_1d0 (Side_nil _)).
  - cbn [toH toH' toRC lpow app] in *.
    rewrite <- (side_nil_eq IHh).
    exact (zSc seg_ch_1d1 (Side_nil _)).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc seg_ch_w1ld_atom (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC lpow app Str_app] in *.
    exact (zSc (seg_hx_ld k) (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC Str_app] in *.
    exact (z08 (zSc seg_ch'_d1 (Side_nil _)) (zSc (seg_wall_ld k) IHh)).
  - cbn [toH toH' toRC Str_app] in *.
    exact (zSc (seg_hx_d0 k) IHh).
  - cbn [toH toH' toRC lpow app] in *.
    exact (zSc (seg_h1_ld k) (z08 IHh1 IHh2)).
  - cbn [toH toH' toRC app] in *.
    exact (z08 (zSc seg_ch_1d1 (Side_nil _)) (zSc (seg_wall_ld k) IHh)).
  - cbn [toH toH' toRC app] in *.
    exact (z08 (zSc seg_ch_1d0 (Side_nil _)) (zSc (seg_d0_even k) IHh)).
  - cbn [toH toH' toRC app] in *.
    change (ch :: ch :: [ch] ^^ (k * 2)) with ([ch] ++ [ch] ^^ (1 + k * 2)).
    exact (z08 (zSc seg_ch_1d0 (Side_nil _)) (zSc (seg_d0_odd k) IHh)).
  - cbn [toH toH' toRC lpow app].
    rewrite <- z0_eq, zDd.
    exact (Side_nil ([1]%sym *> 0inf%sym)).
  - cbn [toH toH' toRC app] in *.
    rewrite <- zDd at 1.
    exact (z08 (zSc seg_ch_1d0 (Side_nil 0inf%sym)) (zSc (seg_d0_even k) IHh)).
  - cbn [toH toH' toRC app] in *.
    change (ch :: ch :: [ch] ^^ (k * 2)) with ([ch] ++ [ch] ^^ (1 + k * 2)).
    rewrite <- zDd at 1.
    exact (z08 (zSc seg_ch_1d0 (Side_nil 0inf%sym)) (zSc (seg_d0_odd k) IHh)).
  - assert (heq : toH' h1 *> toRC [D1] = toRC [LD]) by exact z1_eq.
    cbn [toH lpow app]. rewrite heq. exact (Side_nil _).
  - assert (heq : toH' h1 *> toRC [D0] = toRC [D1]) by exact z0_eq.
    cbn [toH lpow app]. rewrite heq. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
  - cbn [toH lpow app]. exact (Side_nil _).
Qed.

Lemma RIncs_eqk {tp : H} {k k' : nat} {r r' : list RD}
    (h : RIncs tp k r r') (hk : k = k') : RIncs tp k' r r'.
Proof. subst k'; exact h. Qed.

Lemma RIncs_fun {tp : H} {k : nat} {r r1 r2 : list RD}
    (h1 : RIncs tp k r r1) (h_other : RIncs tp k r r2) : r1 = r2.
Proof.
  revert r2 h_other.
  induction h1; intros r_out h_other.
  - inverts h_other. reflexivity.
  - inverts h_other. reflexivity.
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2a h2b. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2a h2b. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2a h2b; try lia. rewrite <- (IHh1_1 _ h2a) in h2b. f_equal. exact (IHh1_2 _ h2b).
  - inverts h_other as h2'; try lia. f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other; try lia; reflexivity.
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other as h2'; try lia.
    assert (k0 = k) by lia; subst k0.
    f_equal. exact (IHh1 _ h2').
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
  - inverts h_other; try lia; try contradiction; reflexivity.
Qed.

Lemma RIncs_step {tp : H} {k : nat} {r r' : list RD}
    (h : RIncs tp k r r') (htp : tp <> hi) :
    exists r'', RIncs hi 0 r' r'' /\ RIncs tp (1 + k) r r''.
Proof.
  induction h; try (exfalso; apply htp; reflexivity).
  - destruct (IHh2 ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_ld h2 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_d1 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (hx_d0 h_ri')].
  - destruct (IHh2 ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (h1_ld h2 h_ri')].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (LD :: r''). split; [exact (hi_ld hJ) | exact (h1_d1 h_ri')].
  - exists (D1 :: r'). split; [exact (hi_d0 r') | eapply RIncs_eqk; [exact (h1_d0_1 h) | lia]].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (D0 :: r''). split; [exact (hi_d1 hJ) | eapply RIncs_eqk; [exact (h1_d0_0 h_ri') | lia]].
  - exists [D0; D1]. split; [exact (hi_d1 hi_nil) | exact (h1_rh_1 h1_rh_0)].
  - exists (D1 :: r'). split; [exact (hi_d0 r') | eapply RIncs_eqk; [exact (h1_rh_2 h) | lia]].
  - destruct (IHh ltac:(discriminate)) as [r'' [hJ h_ri']].
    exists (D0 :: r''). split; [exact (hi_d1 hJ) | eapply RIncs_eqk; [exact (h1_rh_1 h_ri') | lia]].
  - exists [LD; D1]. split; [exact (hi_ld hi_nil) | exact (h1_d1 h1_rh_0)].
  - exists [D0; D1]. split; [exact (hi_d1 hi_nil) | exact (h1_d0_0 h1_rh_0)].
  - exists (LD :: r2). split; [exact (hi_w1ld h2 h3) | exact (h1_ld h2 h3)].
  - exists (LD :: r1). split; [exact (hi_w1d1 h) | exact (h1_d1 h)].
  - exists (D0 :: r1). split; [exact (hi_w1d0 h) | exact (h1_d0_0 h)].
Qed.

Lemma mod2 (n : nat) : (exists b, n = b * 2) \/ (exists b, n = 1 + b * 2).
Proof.
  induction n as [| n ih].
  - left. exists 0. lia.
  - destruct ih as [[b ->] | [b ->]].
     + right. exists b. lia.
     + left. exists (b + 1). lia.
Qed.

Inductive Good : H -> nat -> list RD -> Prop :=
  | Good_hx_ld {k : nat} {r r1 : list RD} :
      RIncs hi 0 r r1 -> Good hx (1 + k) r1 -> Good hx k (LD :: r)
  | Good_hx_d1 {k : nat} {r : list RD} :
      Good h1 (1 + k) r -> Good hx k (D1 :: r)
  | Good_hx_d0 {k : nat} {r : list RD} :
      Good hx (1 + k) r -> Good hx k (D0 :: r)
  | Good_h1_ld {k : nat} {r r1 : list RD} :
      RIncs hi 0 r r1 -> Good hx (1 + k) r1 -> Good h1 (1 + k) (LD :: r)
  | Good_h1_d1 {k : nat} {r : list RD} :
      Good h1 (1 + k) r -> Good h1 (1 + k) (D1 :: r)
  | Good_h1_d0_0 {a : nat} {r : list RD} :
      Good h1 a r -> Good h1 (1 + a * 2) (D0 :: r)
  | Good_h1_d0_1 {a : nat} {r : list RD} :
      Good h1 a r -> Good h1 (2 + a * 2) (D0 :: r)
  | Good_h1_z1 :
      Good h1 0 [D1]
  | Good_h1_nil (k : nat) :
      Good h1 k [].

Lemma RIncs_nxt_1_aux (m : nat) : forall k, k <= m -> exists r, RIncs h1 k [] r.
Proof.
  induction m as [| m ih]; intros k hk.
  - assert (k = 0) by lia; subst k. exists [D1]. exact h1_rh_0.
  - destruct k as [| k0].
    + exists [D1]. exact h1_rh_0.
    + destruct (mod2 k0) as [[b ->] | [b ->]].
      * destruct (ih b ltac:(lia)) as [r hI].
        exists (D0 :: r). eapply RIncs_eqk; [exact (h1_rh_1 hI) | lia].
      * destruct (ih b ltac:(lia)) as [r hI].
        exists (D1 :: r). eapply RIncs_eqk; [exact (h1_rh_2 hI) | lia].
Qed.

Lemma RIncs_nxt_1 (k : nat) : exists r, RIncs h1 k [] r.
Proof. exact (RIncs_nxt_1_aux k k (Nat.le_refl k)). Qed.

Lemma rK_nonnil {k : nat} {r rK : list RD} (h : RIncs h1 k r rK) : rK <> [].
Proof.
  inverts h; discriminate.
Qed.

Lemma inv_hx_ld {k : nat} {r rK : list RD} (h : RIncs hx k (LD :: r) rK) :
    exists r1 rK', RIncs hi 0 r r1 /\ RIncs hx k r1 rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_inc h_ri. exists r1, r'. repeat split; try reflexivity; assumption.
Qed.

Lemma inv_hx_d1 {k : nat} {r rK : list RD} (h : RIncs hx k (D1 :: r) rK) :
    exists rK', RIncs h1 k r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_hx_d0 {k : nat} {r rK : list RD} (h : RIncs hx k (D0 :: r) rK) :
    exists rK', RIncs hx (1 + k) r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_h1_ld {k : nat} {r rK : list RD} (h : RIncs h1 (1 + k) (LD :: r) rK) :
    exists r1 rK', RIncs hi 0 r r1 /\ RIncs hx k r1 rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_inc h_ri; try lia. exists r1, r'. repeat split; try reflexivity; assumption.
Qed.

Lemma inv_h1_d1 {k : nat} {r rK : list RD} (h : RIncs h1 (1 + k) (D1 :: r) rK) :
    exists rK', RIncs h1 k r rK' /\ rK = LD :: rK'.
Proof.
  inverts h as h_ri; try lia. exists r'. split; [exact h_ri | reflexivity].
Qed.

Lemma inv_h1_d0 {K : nat} {r rK : list RD} (h : RIncs h1 K (D0 :: r) rK) (hK : 1 <= K) :
    (exists A rK', K = 1 + A * 2 /\ RIncs h1 A r rK' /\ rK = D0 :: rK') \/
    (exists A rK', K = 2 + A * 2 /\ RIncs h1 A r rK' /\ rK = D1 :: rK').
Proof.
  inverts h as h_ri; try lia.
  - left. exists k, r'. repeat split; try reflexivity; exact h_ri.
  - right. exists k, r'. repeat split; try reflexivity; exact h_ri.
Qed.

Lemma inv_z1 {K : nat} {rK : list RD} (h : RIncs h1 K [D1] rK) :
    (K = 0 /\ rK = [LD]) \/
    (exists K0 rK', K = 1 + K0 /\ RIncs h1 K0 [] rK' /\ rK = LD :: rK').
Proof.
  inverts h as h_ri; try contradiction.
  - right. exists k, r'. repeat split; try reflexivity; exact h_ri.
  - left. split; reflexivity.
Qed.

Lemma End_step {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall tq q, (tq = hx \/ tq = h1) -> exists w', RIncs tq q w w'.
Proof.
  induction h; try discriminate htp; try discriminate he; intros tq q htq.
  - destruct htq as [-> | ->].
    + destruct (RIncs_nxt_1 q) as [w' hI].
      exists (LD :: w'). exact (hx_d1 hI).
    + destruct q as [| q0].
      * exists [LD]. exact h1_z1.
      * destruct (RIncs_nxt_1 q0) as [w' hI].
        exists (LD :: w'). eapply RIncs_eqk; [exact (h1_d1 hI) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct htq as [-> | ->].
    + destruct (IHh hx (1 + q) (or_introl eq_refl)) as [w' hI2].
      exists (LD :: w'). exact (hx_d0 hI2).
    + destruct q as [| m0].
      * destruct (IHh h1 0 (or_intror eq_refl)) as [w' hI2].
        exists (W1D0 :: r'). exact (h1_z_d0 (rK_nonnil h) hI2).
      * destruct (mod2 m0) as [[b ->] | [b ->]].
        -- destruct (IHh h1 b (or_intror eq_refl)) as [w' hI2].
           exists (D0 :: w'). eapply RIncs_eqk; [exact (h1_d0_0 hI2) | lia].
        -- destruct (IHh h1 b (or_intror eq_refl)) as [w' hI2].
           exists (D1 :: w'). eapply RIncs_eqk; [exact (h1_d0_1 hI2) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct htq as [-> | ->].
    + destruct (IHh h1 q (or_intror eq_refl)) as [w' hI2].
      exists (LD :: w'). exact (hx_d1 hI2).
    + destruct q as [| q0].
      * destruct (IHh h1 0 (or_intror eq_refl)) as [w' hI2].
        exists (W1D1 :: r'). exact (h1_z_d1 (rK_nonnil h) hI2).
      * destruct (IHh h1 q0 (or_intror eq_refl)) as [w' hI2].
        exists (LD :: w'). eapply RIncs_eqk; [exact (h1_d1 hI2) | lia].
Qed.

Lemma Good_eqk {tp : H} {k k' : nat} {r : list RD}
    (h : Good tp k r) (hk : k = k') : Good tp k' r.
Proof. subst k'; exact h. Qed.

Lemma Good_step {tp : H} {k : nat} {r : list RD} (hG : Good tp k r) :
    forall j rK tq q, RIncs tp (k + j) r rK ->
    (tq = hx \/ (tq = h1 /\ tp = h1)) -> exists r2, RIncs tq q rK r2.
Proof.
  induction hG; intros j rK tq q E htq.
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_ld E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_d1 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (htq_hx : tq = hx) by (destruct htq as [-> | [_ Hc]]; [reflexivity | discriminate]).
    subst tq.
    destruct (inv_hx_d0 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + (1 + j)) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct (IHhG (1 + j) rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
    exists (LD :: r2). exact (hx_ld J I2).
  - assert (E0 : RIncs h1 (1 + (k + j)) (LD :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_ld E0) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct htq as [-> | [-> _]].
    + destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
      exists (LD :: r2). exact (hx_ld J I2).
    + destruct q as [| q0].
      * destruct (IHhG j rK'' hx 0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (W1LD :: rK'). exact (h1_z_ld J I2).
      * destruct (IHhG j rK'' hx q0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - assert (E0 : RIncs h1 (1 + (k + j)) (D1 :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_d1 E0) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct htq as [-> | [-> _]].
    + destruct (IHhG j rK'' hx q E3 (or_introl eq_refl)) as [r2 I2].
      exists (LD :: r2). exact (hx_ld J I2).
    + destruct q as [| q0].
      * destruct (IHhG j rK'' hx 0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (W1LD :: rK'). exact (h1_z_ld J I2).
      * destruct (IHhG j rK'' hx q0 E3 (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' hx (1 + q) hE' (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_d0 I2).
      * destruct q as [| m0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D0 :: rK'). exact (h1_z_d0 (rK_nonnil E') I2).
        -- destruct (mod2 m0) as [[b ->] | [b ->]].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D0 :: r2). eapply RIncs_eqk; [exact (h1_d0_0 I2) | lia].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D1 :: r2). eapply RIncs_eqk; [exact (h1_d0_1 I2) | lia].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' h1 q hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
        exists (LD :: r2). exact (hx_d1 I2).
      * destruct q as [| q0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D1 :: rK'). exact (h1_z_d1 (rK_nonnil E') I2).
        -- destruct (IHhG (A - a) rK' h1 q0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_d1 I2) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' hx (1 + q) hE' (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_d0 I2).
      * destruct q as [| m0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D0 :: rK'). exact (h1_z_d0 (rK_nonnil E') I2).
        -- destruct (mod2 m0) as [[b ->] | [b ->]].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D0 :: r2). eapply RIncs_eqk; [exact (h1_d0_0 I2) | lia].
           ++ destruct (IHhG (A - a) rK' h1 b hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
              exists (D1 :: r2). eapply RIncs_eqk; [exact (h1_d0_1 I2) | lia].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct htq as [-> | [-> _]].
      * destruct (IHhG (A - a) rK' h1 q hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
        exists (LD :: r2). exact (hx_d1 I2).
      * destruct q as [| q0].
        -- destruct (IHhG (A - a) rK' h1 0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (W1D1 :: rK'). exact (h1_z_d1 (rK_nonnil E') I2).
        -- destruct (IHhG (A - a) rK' h1 q0 hE' (or_intror (conj eq_refl eq_refl))) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_d1 I2) | lia].
  - destruct (inv_z1 E) as [[HK ->] | [K0 [rK' [HK [E' ->]]]]].
    + destruct htq as [-> | [-> _]].
      * destruct (RIncs_nxt_1 q) as [w hI].
        exists (LD :: LD :: w). exact (hx_ld hi_nil (hx_d1 hI)).
      * destruct q as [| q0].
        -- exists [W1LD]. exact (h1_z_ld hi_nil (hx_d1 h1_rh_0)).
        -- destruct (RIncs_nxt_1 q0) as [w hI].
           exists (LD :: LD :: w). eapply RIncs_eqk; [exact (h1_ld hi_nil (hx_d1 hI)) | lia].
    + destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
      destruct htq as [-> | [-> _]].
      * destruct (End_step E'' eq_refl eq_refl hx q (or_introl eq_refl)) as [r2 I2].
        exists (LD :: r2). exact (hx_ld J I2).
      * destruct q as [| q0].
        -- destruct (End_step E'' eq_refl eq_refl hx 0 (or_introl eq_refl)) as [r2 I2].
           exists (W1LD :: rK'). exact (h1_z_ld J I2).
        -- destruct (End_step E'' eq_refl eq_refl hx q0 (or_introl eq_refl)) as [r2 I2].
           exists (LD :: r2). eapply RIncs_eqk; [exact (h1_ld J I2) | lia].
  - destruct htq as [-> | [-> _]].
    + exact (End_step E eq_refl eq_refl hx q (or_introl eq_refl)).
    + exact (End_step E eq_refl eq_refl h1 q (or_intror eq_refl)).
Qed.

Lemma End_good_1 {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall q, m <= q -> Good h1 q w.
Proof.
  induction h; try discriminate htp; try discriminate he; intros q hq.
  - destruct q as [| q0].
    + exact Good_h1_z1.
    + eapply Good_eqk; [exact (Good_h1_d1 (Good_h1_nil (1 + q0))) | lia].
  - specialize (IHh eq_refl eq_refl).
    destruct (mod2 q) as [[c ->] | [c ->]].
    + destruct c as [| c]; [lia |].
      eapply Good_eqk; [exact (Good_h1_d0_1 (IHh c ltac:(lia))) | lia].
    + exact (Good_h1_d0_0 (IHh c ltac:(lia))).
  - specialize (IHh eq_refl eq_refl).
    destruct q as [| q0]; [lia |].
    eapply Good_eqk; [exact (Good_h1_d1 (IHh (1 + q0) ltac:(lia))) | lia].
Qed.

Lemma End_good_x {tp : H} {m : nat} {e w : list RD} (h : RIncs tp m e w)
    (htp : tp = h1) (he : e = []) :
    forall q, m <= 2 * q + 2 -> Good hx q w.
Proof.
  induction h; try discriminate htp; try discriminate he; intros q hq.
  - exact (Good_hx_d1 (Good_h1_nil (1 + q))).
  - exact (Good_hx_d0 (IHh eq_refl eq_refl (1 + q) ltac:(lia))).
  - exact (Good_hx_d1 (End_good_1 h eq_refl eq_refl (1 + q) ltac:(lia))).
Qed.

Definition Inv (tp : H) (k j : nat) (tq : H) (q : nat) : Prop :=
  match tp, tq with
  | hx, hx => k <= q /\ j <= q
  | h1, hx => k <= q /\ j <= q
  | h1, h1 => (j = 0 /\ 2 * k + 1 <= q) \/ (1 <= j /\ k + j <= q /\ 1 <= q)
  | _, _ => False
  end.

Lemma Good_pres {tp : H} {k : nat} {r : list RD} (hG : Good tp k r) :
    forall j rK tq q, RIncs tp (k + j) r rK ->
    Inv tp k j tq q -> Good tq q rK.
Proof.
  induction hG; intros j rK tq q E HI.
  - destruct tq; try contradiction.
    destruct (inv_hx_ld E) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - destruct tq; try contradiction.
    destruct (inv_hx_d1 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - destruct tq; try contradiction.
    destruct (inv_hx_d0 E) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + (1 + j)) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    exact (Good_hx_ld J (IHhG (1 + j) rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
  - assert (E0 : RIncs h1 (1 + (k + j)) (LD :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_ld E0) as [r1' [rK' [Hi' [E' ->]]]].
    rewrite (RIncs_fun Hi' H0) in E'.
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs hx ((1 + k) + j) r1 rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct tq; try contradiction.
    + exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
    + destruct q as [| q0]; [cbn [Inv] in HI; lia |].
      eapply Good_eqk; [exact (Good_h1_ld J (IHhG j rK'' hx (1 + q0) E3 ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - assert (E0 : RIncs h1 (1 + (k + j)) (D1 :: r) rK) by (eapply RIncs_eqk; [exact E | lia]).
    destruct (inv_h1_d1 E0) as [rK' [E' ->]].
    destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
    assert (E3 : RIncs h1 ((1 + k) + j) r rK'') by (eapply RIncs_eqk; [exact E'' | lia]).
    destruct tq; try contradiction.
    + exact (Good_hx_ld J (IHhG j rK'' hx (1 + q) E3 ltac:(cbn [Inv] in HI |- *; lia))).
    + destruct q as [| q0]; [cbn [Inv] in HI; lia |].
      eapply Good_eqk; [exact (Good_h1_ld J (IHhG j rK'' hx (1 + q0) E3 ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d0 (IHhG (A - a) rK' hx (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct (mod2 q) as [[b ->] | [b ->]].
        -- destruct b as [| b0]; [cbn [Inv] in HI; lia |].
           eapply Good_eqk; [exact (Good_h1_d0_1 (IHhG (A - a) rK' h1 b0 hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
        -- exact (Good_h1_d0_0 (IHhG (A - a) rK' h1 b hE' ltac:(cbn [Inv] in HI |- *; lia))).
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d1 (IHhG (A - a) rK' h1 (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_d1 (IHhG (A - a) rK' h1 (1 + q0) hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_h1_d0 E ltac:(lia)) as [[A [rK' [hKA [E' ->]]]] | [A [rK' [hKA [E' ->]]]]].
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d0 (IHhG (A - a) rK' hx (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct (mod2 q) as [[b ->] | [b ->]].
        -- destruct b as [| b0]; [cbn [Inv] in HI; lia |].
           eapply Good_eqk; [exact (Good_h1_d0_1 (IHhG (A - a) rK' h1 b0 hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
        -- exact (Good_h1_d0_0 (IHhG (A - a) rK' h1 b hE' ltac:(cbn [Inv] in HI |- *; lia))).
    + assert (hE' : RIncs h1 (a + (A - a)) r rK') by (eapply RIncs_eqk; [exact E' | lia]).
      destruct tq; try contradiction.
      * exact (Good_hx_d1 (IHhG (A - a) rK' h1 (1 + q) hE' ltac:(cbn [Inv] in HI |- *; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_d1 (IHhG (A - a) rK' h1 (1 + q0) hE' ltac:(cbn [Inv] in HI |- *; lia))) | lia].
  - destruct (inv_z1 E) as [[HK ->] | [K0 [rK' [HK [E' ->]]]]].
    + destruct tq; try contradiction.
      * exact (Good_hx_ld hi_nil (Good_hx_d1 (Good_h1_nil _))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_ld hi_nil (Good_hx_d1 (Good_h1_nil (1 + (1 + q0))))) | lia].
    + destruct (RIncs_step E' ltac:(discriminate)) as [rK'' [J E'']].
      destruct tq; try contradiction.
      * exact (Good_hx_ld J (End_good_x E'' eq_refl eq_refl (1 + q) ltac:(cbn [Inv] in HI; lia))).
      * destruct q as [| q0]; [cbn [Inv] in HI; lia |].
        eapply Good_eqk; [exact (Good_h1_ld J (End_good_x E'' eq_refl eq_refl (1 + q0) ltac:(cbn [Inv] in HI; lia))) | lia].
  - destruct tq; try contradiction.
    + exact (End_good_x E eq_refl eq_refl q ltac:(cbn [Inv] in HI; lia)).
    + exact (End_good_1 E eq_refl eq_refl q ltac:(cbn [Inv] in HI; lia)).
Qed.

Lemma domain {r r1 : list RD} (hG : Good hx 0 r) (hE : RIncs hx 0 r r1) :
    exists r2, RIncs hx 0 r1 r2 /\ Good hx 0 r1.
Proof.
  destruct (Good_step hG 0 r1 hx 0 hE (or_introl eq_refl)) as [r2 hR2].
  exists r2. split; [exact hR2 | exact (Good_pres hG 0 r1 hx 0 hE ltac:(cbn [Inv]; lia))].
Qed.

Definition S' (r : list RD) : Q * tape :=
  zCR lh ch' (toRC r).

Lemma turn_lh (r : list RD) : zCL lh (toRC r) -->+ S' r.
Proof.
  unfold zCL, S', zCR, lh, zCw, zCs. es.
Qed.

Lemma BigStep {r r' : list RD} (h : RIncs hx 0 r r') : S' r -->+ S' r'.
Proof.
  pose proof (RIncs_spec h) as hS.
  cbn [toH toH' lpow app Str_app] in hS.
  inverts hS as hc hnil. inverts hnil.
  eapply progress_trans; [exact (hc lh) | exact (turn_lh r')].
Qed.

Lemma start_to_S' : c0 -->* S' [D1].
Proof.
  unfold S', zCR, lh, zCw, zCs, toRC, d1.
  solve_init.
Qed.

Lemma nonhalt : ~ halts tm c0.
Proof.
  eapply multistep_nonhalt with (c' := S' [D1]).
  - exact start_to_S'.
  - eapply progress_nonhalt_cond with
      (C := S')
      (P := fun r => (exists r1, RIncs hx 0 r r1) /\ Good hx 0 r)
      (i0 := [D1]).
    + intros r [[r1 hE] hG].
      destruct (domain hG hE) as [r2 [hE2 hG2]].
      exists r1. split; [exact (BigStep hE) | split; [exists r2; exact hE2 | exact hG2]].
    + split.
      * exists [LD; D1]. exact (hx_d1 h1_rh_0).
      * exact (Good_hx_d1 (Good_h1_nil 1)).
Qed.

Print Assumptions nonhalt.
