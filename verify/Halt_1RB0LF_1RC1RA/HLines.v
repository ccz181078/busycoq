(** Region lines: exact inequalities in the state (b,S,g), and how they pull back through two letters. No approximation here. *)
From Coq Require Import ZArith Lia.
From BusyCoq.Halt_1RB0LF_1RC1RA Require Import Ints.
Local Open Scope Z_scope.

Definition lo_z (t V r b S g : Z) : Prop := t * (PP * S - r * g) <= TT * (PP * b - V * g).
Definition hi_z (t V r b S g : Z) : Prop := TT * (PP * b - V * g) <= t * (PP * S - r * g).

(** What a line with slope e/4 says about X = b + g y. *)
Lemma lo_guard e V r y M b S g : lo_z (e * (TT / 4)) V r b S g -> 0 <= g ->
  e * r - 4 * y * PP + 4 * M <= 4 * V ->
  4 * M * g <= PP * (4 * (b + g * y) - e * S).
Proof.
  unfold lo_z. change (TT / 4) with 268435456. intros H G V4.
  assert (A : g * (e * r - 4 * y * PP + 4 * M) <= g * (4 * V)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.
Lemma hi_guard e V r y M b S g : hi_z (e * (TT / 4)) V r b S g -> 0 <= g ->
  4 * V <= e * r - 4 * y * PP - 4 * M ->
  4 * M * g <= PP * (e * S - 4 * (b + g * y)).
Proof.
  unfold hi_z. change (TT / 4) with 268435456. intros H G V4.
  assert (A : g * (4 * V) <= g * (e * r - 4 * y * PP - 4 * M)) by (apply Z.mul_le_mono_nonneg_l; lia).
  lia.
Qed.

(** Pull back through b' = 4X - eZ - K, S' = Z + K', g' = 4g - e with X = b + g y, Z = S + y. *)
Section Pull.
Variables (t' V' r' t V r y e K K2 Wq f rho b S g W1 W2 : Z).
Hypotheses (Ht' : 0 <= t' <= TT) (Ht : 0 <= t <= TT) (Hrho : 4 * t + rho = t' + e * TT) (Hrho0 : 0 <= rho <= 3)
  (He : 0 <= e <= 3) (Hy : 0 <= y) (HK : 0 <= K) (HK2 : 0 <= K2)
  (Hq : 4 * Wq <= r <= 4 * Wq + 3) (Hg : 1 <= g).

Let b1 := 4 * (b + g * y) - e * (S + y) - K.
Let S1 := S + y + K2.
Let g1 := 4 * g - e.

Lemma pull_id : TT * (PP * b1 - V' * g1) - t' * (PP * S1 - r' * g1) =
  4 * (TT * (PP * b - V * g) - t * (PP * S - r * g))
  + g * (4 * TT * V - 4 * t * r + 4 * TT * PP * y - 4 * TT * V' + 4 * t' * r')
  - rho * PP * S
  + (- TT * PP * (e * y + K) + TT * V' * e - t' * PP * (y + K2) - t' * r' * e).
Proof.
  unfold b1, S1, g1.
  assert (Ee : t' = 4 * t + rho - e * TT) by lia. rewrite Ee. ring.
Qed.

Lemma pull_lo :
  t' * (Wq - r') < TT * (f + 1) ->
  V = V' + f + 1 + 8 + e * Wq - y * PP ->
  PP * S <= W2 * g -> W2 <= r + 2147483648 ->
  (Z.abs V' + Z.abs r') * 3 + PP * (4 * y + K + K2) <= 13 * g ->
  lo_z t V r b S g -> lo_z t' V' r' b1 S1 g1.
Proof.
  intros Hf HV HS HW Hb Hl. unfold lo_z in *.
  pose proof pull_id as Id.
  set (L := TT * (PP * b - V * g) - t * (PP * S - r * g)) in *.
  assert (L0 : 0 <= L) by (unfold L; lia).
  set (E := 4 * TT * V - 4 * t * r + 4 * TT * PP * y - 4 * TT * V' + 4 * t' * r') in *.
  assert (X : Wq * (4 * t + rho) = Wq * (t' + e * TT)) by (rewrite Hrho; reflexivity).
  assert (E1 : 4 * (Wq * (4 * t + rho)) + 4 * TT * 8 - 4 * t * r < E).
  { unfold E. rewrite HV, X. lia. }
  assert (T1 : t * (r - 4 * Wq) <= t * 3) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (E2 : - 12 * TT + 4 * (rho * Wq) + 4 * TT * 8 <= E) by lia.
  assert (G1 : g * (- 12 * TT + 4 * (rho * Wq) + 4 * TT * 8) <= g * E) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (R1 : rho * (PP * S) <= rho * (W2 * g)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (R2 : (W2 * g) * rho <= ((r + 2147483648) * g) * rho).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.mul_le_mono_nonneg_r; lia. }
  assert (R3 : (r - 4 * Wq) * (g * rho) <= 3 * (g * rho)).
  { apply Z.mul_le_mono_nonneg_r; [|lia]. apply Z.mul_nonneg_nonneg; lia. }
  assert (R4 : g * rho * 2147483651 <= g * 3 * 2147483651) by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.mul_le_mono_nonneg_l; lia).
  assert (A1 : t' * (PP * (y + K2)) <= TT * (PP * (y + K2))).
  { apply Z.mul_le_mono_nonneg_r; [apply Z.mul_nonneg_nonneg; lia|lia]. }
  assert (A2 : e * y <= 3 * y) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (A3 : - (TT * (Z.abs V' * 3)) <= TT * V' * e).
  { destruct (Z.abs_spec V') as [[? ->]|[? ->]].
    - assert (0 <= V' * e) by (apply Z.mul_nonneg_nonneg; lia). lia.
    - assert ((-V') * e <= (-V') * 3) by (apply Z.mul_le_mono_nonneg_l; lia). lia. }
  assert (A4 : t' * r' * e <= TT * (Z.abs r' * 3)).
  { assert (Hr : r' <= Z.abs r') by lia.
    assert (Hz : 0 <= Z.abs r') by apply Z.abs_nonneg.
    assert (P1 : (t' * e) * r' <= (t' * e) * Z.abs r') by (apply Z.mul_le_mono_nonneg_l; [apply Z.mul_nonneg_nonneg; lia|lia]).
    assert (P2 : (t' * e) * Z.abs r' <= (TT * 3) * Z.abs r').
    { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.mul_le_mono_nonneg; lia. }
    lia. }
  assert (T : TT * ((Z.abs V' + Z.abs r') * 3 + PP * (4 * y + K + K2)) <= TT * (13 * g)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M : 0 <= 4 * L + g * E - rho * PP * S + (- TT * PP * (e * y + K) + TT * V' * e - t' * PP * (y + K2) - t' * r' * e)) by lia.
  rewrite <- Id in M. lia.
Qed.

Lemma pull_hi :
  TT * f <= t' * (Wq - r') ->
  V = V' + f - 8 + e * Wq - y * PP ->
  W1 * g <= PP * S -> r - 2147483648 <= W1 ->
  (Z.abs V' + Z.abs r') * 3 <= 13 * g ->
  hi_z t V r b S g -> hi_z t' V' r' b1 S1 g1.
Proof.
  intros Hf HV HS HW Hb Hl. unfold hi_z in *.
  pose proof pull_id as Id.
  set (L := TT * (PP * b - V * g) - t * (PP * S - r * g)) in *.
  assert (L0 : L <= 0) by (unfold L; lia).
  set (E := 4 * TT * V - 4 * t * r + 4 * TT * PP * y - 4 * TT * V' + 4 * t' * r') in *.
  assert (X : Wq * (4 * t + rho) = Wq * (t' + e * TT)) by (rewrite Hrho; reflexivity).
  assert (E1 : E <= 4 * (Wq * (4 * t + rho)) - 4 * TT * 8 - 4 * t * r).
  { unfold E. rewrite HV, X. lia. }
  assert (T1 : 0 <= t * (r - 4 * Wq)) by (apply Z.mul_nonneg_nonneg; lia).
  assert (E2 : E <= 4 * (rho * Wq) - 4 * TT * 8) by lia.
  assert (G1 : g * E <= g * (4 * (rho * Wq) - 4 * TT * 8)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (R1 : rho * (W1 * g) <= rho * (PP * S)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (R2 : ((r - 2147483648) * g) * rho <= (W1 * g) * rho).
  { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.mul_le_mono_nonneg_r; lia. }
  assert (R3 : 0 <= (r - 4 * Wq) * (g * rho)).
  { apply Z.mul_nonneg_nonneg; [lia|]. apply Z.mul_nonneg_nonneg; lia. }
  assert (R4 : g * rho * 2147483648 <= g * 3 * 2147483648) by (apply Z.mul_le_mono_nonneg_r; [lia|]; apply Z.mul_le_mono_nonneg_l; lia).
  assert (A1 : 0 <= t' * (PP * (y + K2))).
  { apply Z.mul_nonneg_nonneg; [lia|]. apply Z.mul_nonneg_nonneg; lia. }
  assert (A2 : 0 <= PP * (e * y + K)).
  { apply Z.mul_nonneg_nonneg; [lia|]. assert (0 <= e * y) by (apply Z.mul_nonneg_nonneg; lia). lia. }
  assert (A3 : TT * V' * e <= TT * (Z.abs V' * 3)).
  { assert (Hr : V' <= Z.abs V') by lia.
    assert (Hz : 0 <= Z.abs V') by apply Z.abs_nonneg.
    assert (P1 : e * V' <= e * Z.abs V') by (apply Z.mul_le_mono_nonneg_l; lia).
    assert (P2 : e * Z.abs V' <= 3 * Z.abs V') by (apply Z.mul_le_mono_nonneg_r; lia).
    lia. }
  assert (A4 : - (t' * r' * e) <= TT * (Z.abs r' * 3)).
  { assert (Hr : - r' <= Z.abs r') by lia.
    assert (Hz : 0 <= Z.abs r') by apply Z.abs_nonneg.
    assert (P1 : (t' * e) * (- r') <= (t' * e) * Z.abs r') by (apply Z.mul_le_mono_nonneg_l; [apply Z.mul_nonneg_nonneg; lia|lia]).
    assert (P2 : (t' * e) * Z.abs r' <= (TT * 3) * Z.abs r').
    { apply Z.mul_le_mono_nonneg_r; [lia|]. apply Z.mul_le_mono_nonneg; lia. }
    lia. }
  assert (T : TT * ((Z.abs V' + Z.abs r') * 3) <= TT * (13 * g)) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (M : 4 * L + g * E - rho * PP * S + (- TT * PP * (e * y + K) + TT * V' * e - t' * PP * (y + K2) - t' * r' * e) <= 0) by lia.
  rewrite <- Id in M. lia.
Qed.

End Pull.

(** The W range of a child. *)
Lemma range_lo W1c W1 S y K2 g e : 0 <= W1c -> 4 * W1c <= W1 -> W1 * g <= PP * S -> 0 <= y -> 0 <= K2 -> 1 <= g -> 0 <= e ->
  W1c * (4 * g - e) <= PP * (S + y + K2).
Proof.
  intros H0 H1 H2 Hy HK Hg He.
  assert (A : W1c * e >= 0) by (apply Z.le_ge, Z.mul_nonneg_nonneg; lia).
  assert (B : (4 * W1c) * g <= W1 * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  assert (C : 0 <= PP * (y + K2)) by (apply Z.mul_nonneg_nonneg; lia). lia.
Qed.
Lemma range_hi W2c W2 S y K2 g e : 0 <= W2c -> W2 + 64 <= 4 * W2c -> PP * S <= W2 * g -> 0 <= e <= 3 -> 1 <= g ->
  PP * (y + K2) + 3 * W2c <= 64 * g ->
  PP * (S + y + K2) <= W2c * (4 * g - e).
Proof.
  intros H0 H1 H2 He Hg H3.
  assert (A : W2c * e <= W2c * 3) by (apply Z.mul_le_mono_nonneg_l; lia).
  assert (B : (W2 + 64) * g <= (4 * W2c) * g) by (apply Z.mul_le_mono_nonneg_r; lia).
  lia.
Qed.

(** Dominance on a W range: a kept line at both ends dominates a raw line inside. *)
Lemma dom_lo tk Vk W1 W2 t V r f1 f2 fk b S g :
  0 <= t -> 0 <= tk -> 1 <= g ->
  t * (r - W1) < TT * (f1 + 1) -> TT * f1 <= t * (r - W1) ->
  t * (W2 - r) < TT * (f2 + 1) -> TT * fk <= tk * (W2 - W1) ->
  V - f1 <= Vk -> V + f2 + 1 <= Vk + fk ->
  W1 * g <= PP * S -> PP * S <= W2 * g ->
  lo_z tk Vk W1 b S g -> lo_z t V r b S g.
Proof.
  unfold lo_z. intros Ht Htk Hg F1 F1' F2 Fk H1 H2 S1 S2 Hk.
  set (s := PP * S) in *.
  assert (A1 : 0 <= TT * Vk - TT * V + t * (r - W1)) by lia.
  assert (A2 : 0 <= TT * Vk + tk * (W2 - W1) - TT * V - t * (W2 - r)) by lia.
  assert (F : 0 <= TT * (Vk - V) * g + tk * (s - W1 * g) - t * (s - r * g)).
  { destruct (Z.le_gt_cases t tk) as [L|L].
    - assert (B : 0 <= (tk - t) * (s - W1 * g)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (C : 0 <= g * (TT * Vk - TT * V + t * (r - W1))) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
    - assert (B : 0 <= (t - tk) * (W2 * g - s)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (C : 0 <= g * (TT * Vk + tk * (W2 - W1) - TT * V - t * (W2 - r))) by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
  lia.
Qed.
Lemma dom_hi tk Vk W1 W2 t V r f1 f2 fk b S g :
  0 <= t -> 0 <= tk -> 1 <= g ->
  t * (r - W1) < TT * (f1 + 1) -> TT * f2 <= t * (W2 - r) -> tk * (W2 - W1) < TT * (fk + 1) ->
  Vk <= V - f1 - 1 -> Vk + fk + 1 <= V + f2 ->
  W1 * g <= PP * S -> PP * S <= W2 * g ->
  hi_z tk Vk W1 b S g -> hi_z t V r b S g.
Proof.
  unfold hi_z. intros Ht Htk Hg F1 F2 Fk H1 H2 S1 S2 Hk.
  set (s := PP * S) in *.
  assert (A1 : 0 <= TT * V - t * (r - W1) - TT * Vk) by lia.
  assert (A2 : 0 <= TT * V + t * (W2 - r) - TT * Vk - tk * (W2 - W1)) by lia.
  assert (F : 0 <= TT * (V - Vk) * g + t * (s - r * g) - tk * (s - W1 * g)).
  { destruct (Z.le_gt_cases t tk) as [L|L].
    - assert (B : 0 <= (tk - t) * (W2 * g - s)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (C : 0 <= g * (TT * V + t * (W2 - r) - TT * Vk - tk * (W2 - W1))) by (apply Z.mul_nonneg_nonneg; lia).
      lia.
    - assert (B : 0 <= (t - tk) * (s - W1 * g)) by (apply Z.mul_nonneg_nonneg; lia).
      assert (C : 0 <= g * (TT * V - t * (r - W1) - TT * Vk)) by (apply Z.mul_nonneg_nonneg; lia).
      lia. }
  lia.
Qed.
