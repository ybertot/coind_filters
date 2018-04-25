Require Export Omega.
Require Export ZArithRing.
Require Export ZArith.
Require Export Zwf.
Open Scope Z_scope.

Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.
 
Lemma simpl_int_prop:
 forall m x d n n', n' + (m + 1) <= x -> 0 < d -> x < n ->  ( x - d < x < n ).
intros; omega.
Qed.
 
Lemma simpl_int_prop2:
 forall p x m n, 0 <= n -> 1 < p < m -> ( n+(m+1) <= x  ) ->  ( 1 < p < x ).
intros; omega.
Qed.
 
Lemma simpl_int_prop3:
 forall x n d , (x - d < n) -> (x - n < d).
intros; omega.
Qed.
 
Lemma simpl_int_prop4: forall x n,  0 <= n <= x -> (x - (x - n) <= x).
intros; omega.
Qed.
 
Definition not_mult (n m : Z) : Prop := forall p,  (m <> p * n).
 
Definition partial_prime (m n : Z) : Prop :=
   forall p, ( 1 < p < m ) ->  not_mult p n.
 
Definition pre_prime (n : Z) : Prop := partial_prime n n.
 
Theorem Zwf_m_1 : forall x, x > 0 -> Zwf 0 (x-1) x.
intros; unfold Zwf; omega.
Qed.

Definition fact_F :=
  fun x:Z =>
  fun f:(forall y, Zwf 0 y x -> Z) =>
  match Z_le_gt_dec x 0 with
    left h => 1 
  | right h' => x*(f (x - 1) (Zwf_m_1 x h'))
  end.

Definition fact := 
  Fix (Zwf_well_founded 0) (fun _ => Z) fact_F.
 
Definition fact_ex_F :=
  fun x y:Z =>
  fun f:forall z, Zwf 0 z y -> Z =>
  match Z_le_gt_dec y 0 with
    left h => 1
  | right h' =>
      match Z_eq_dec x y with
        left heq => fact (y-1)
      | right hn => y*f(y-1)(Zwf_m_1 y h')
      end
  end.

Definition fact_ex (x:Z) :=
  Fix (Zwf_well_founded 0) (fun _ => Z) (fact_ex_F x).
 
Theorem fact_equation :
  forall x, 
  fact x = if Z_le_gt_dec x 0 then 1 else x*fact(x-1).
intros x; unfold fact.
rewrite Fix_eq; unfold fact_F.
auto.
intros x' f g heq; case (Z_le_gt_dec x' 0); auto.
intros; rewrite heq;auto.
Qed.

Theorem fact_ex_equation :
  forall x y,
  fact_ex x y = 
    if Z_le_gt_dec y 0 then 1 else
      if Z_eq_dec x y then fact(y-1) else y*fact_ex x (y-1).
intros x y; unfold fact_ex.
rewrite Fix_eq; unfold fact_ex_F.
auto.
intros y' f g heq; case (Z_le_gt_dec y' 0); auto.
intros; case (Z_eq_dec x y'); auto.
intros; rewrite heq;auto.
Qed.

Theorem fact_ex_eq: forall m n, ( 1 < m <= n ) ->  fact n = m * fact_ex m n.
induction n using (well_founded_ind (Zwf_well_founded 0)).
rewrite fact_equation; rewrite fact_ex_equation; case (Z_le_gt_dec n 0).
intros; omega.
intros; case (Z_eq_dec m n).
intros; subst m; auto.
intros; rewrite H.
ring.
unfold Zwf; omega.
omega.
Qed.
 
Theorem le_1_fact: forall n,  (1 <= fact n).
induction n using (well_founded_ind (Zwf_well_founded 0)).
rewrite fact_equation.
case (Z_le_gt_dec n 0).
auto with zarith.
intros.
assert (H':1<= fact(n-1)).
apply H.
unfold Zwf; omega.
pattern n at 1; replace n with ((n - 1) + 1).
rewrite Zmult_plus_distr_l.
cut (0 <= (n-1)*fact (n-1)).
generalize ((n-1)*fact (n-1));intros; omega.
apply Zmult_le_0_compat;omega.
ring.
Qed.

Theorem le_fact: forall n,  (n <= fact n).
induction n using (well_founded_ind (Zwf_well_founded 0)).
rewrite fact_equation.
case (Z_le_gt_dec n 0).
intros; omega.
intros; pattern n at 1; replace n with (n * 1).
apply Zmult_le_compat_l.
apply le_1_fact.
omega.
ring.
Qed.


Definition mult_dec : forall m, m > 0 ->
  forall n, {not_mult m n}+{~not_mult m n}.
intros m H n.
case (Z_eq_dec 0 (n mod m)).
right.
unfold not_mult.
intros H'; apply (H' (n / m)).
pattern n at 1; rewrite (Z_div_mod_eq n m).
rewrite <- e;ring.
auto.
intros Hn;left; intros q H'.
apply Hn; rewrite H'.
apply sym_equal.
apply Z_div_exact_1.
auto.
rewrite (Zmult_comm m).
rewrite Z_div_mult;auto.
Defined.
 
Theorem pre_prime_multiple_diff :
 forall m n d x, 0<=d ->
 ( 1 < m < x ) -> n = x - d -> ~ not_mult m (x - d) -> pre_prime x ->  (0 < d).
 intros m n d x Hdpos Hint Heq Hm Hpr.
 elim (Zle_lt_or_eq 0 d);trivial.
 intros; subst d.
 elim Hm; ring (x-0); apply Hpr;auto.
Qed.

Theorem partial_prime_step:
 forall m n, partial_prime m n -> not_mult m n ->  partial_prime (m+1) n.
intros m n Hppr Hnm p Hint.
elim (Zle_lt_or_eq p m).
intros Hlt.
apply Hppr.
omega.
intros; subst p; assumption.
omega.
Qed.
 
Theorem partial_prime_rev:
 forall m n, partial_prime (m + 1) n ->  partial_prime m n.
intros n m Hppr p Hint; apply Hppr.
omega.
Qed.
 
Theorem partial_prime_le:
 forall m m' n, 0 <= m <= m' -> partial_prime m' n ->  partial_prime m n.
intros m m'; 
 elim m' using (well_founded_ind (Zwf_well_founded m)).
clear m'.
intros m' Hrec n Hle Hppr.
elim (Zle_lt_or_eq m m'); auto.
intros Hlt; apply (Hrec (m'-1)).
unfold Zwf; omega.
omega.
apply partial_prime_rev.
replace (m'-1+1) with m';auto;ring.
intros; subst m'; auto.
omega.
Qed.
 
Theorem partial_prime_revstep:
 forall m n, 1 < m -> partial_prime (m+1) n ->  not_mult m n.
intros n m Hlt Hppr.
apply Hppr.
omega.
Qed.
 
Definition partial_prime_dec:
 forall n m,  0 <= m -> { partial_prime m n } + { ~ partial_prime m n }.
intros n m; elim (Z_eq_dec 0 m).
left.
unfold partial_prime.
intros; assert (H':False).
omega.
elim H'.
elim (Z_eq_dec 1 m).
left; unfold partial_prime; intros; assert (H':False).
omega.
elim H'.
elim m using (well_founded_induction (Zwf_well_founded 0)).
clear m.
intros m Hrec H0 H1 H2;elim (Z_eq_dec 2 m); intros Hm2.
left; unfold partial_prime; intros; assert (H':False).
omega.
elim H'.
elim (Hrec (m-1)).
intros Hppr; elim (fun h => mult_dec (m-1) h n).
intros Hnm; left.
replace m with ((m-1)+1).
apply partial_prime_step; trivial.
ring.
intros Hm; right; intros Hpr.
elim Hm.
apply Hpr; (try omega).
omega.
intros Hnpr; right; intros Hpr; elim Hnpr;
 apply partial_prime_le with m; auto with arith.
omega.
unfold Zwf; omega.
omega.
omega.
omega.
Defined.
 
Definition pre_prime_dec (n : Z) : 0 <= n -> {pre_prime n}+{~ pre_prime n} :=
   partial_prime_dec n n.
 
Theorem pre_prime2: pre_prime 2.
intros p Hint; assert False; [omega | elim H].
Qed.
 
Definition find_divisor:
 forall n m,
 ( 1 < n < m ) ->
 ~ not_mult n m ->
 forall p, 0 <= p ->
 (forall k, ( p < k < m ) ->  (m <> n * k)) ->  ({z : Z | m = n * z}).
intros n m Hlt Hm p;
  elim p using (well_founded_induction (Zwf_well_founded 0)).
clear p; intros p; case (Z_eq_dec p 0).
intros Heqp _; subst p.
intros _ Hn.
elim Hm.
intros k Hint.
elim (Zle_or_lt k 0).
intros Hk0; assert (Hk0': k = 0).
assert (m <= 0).
subst m.
replace 0 with (0 * n).
apply Zmult_le_compat_r; auto.
omega.
ring.
omega.
subst k; omega.
intros H0ltk.
elim (Zle_or_lt m k).
intros Hmk.
assert (n <= 1).
apply Zmult_lt_0_le_reg_r with k.
auto.
rewrite Zmult_comm; rewrite <- Hint.
omega.
omega.
intros Hkm.
apply (Hn k).
omega.
rewrite Hint; ring_nat.
intros Hpn0 Hind Hppos Hnfound.
elim (Z_eq_dec m (n * p)).
intros Heq; exists p; assumption.
intros Hn; apply Hind with (p-1).
unfold Zwf; omega.
omega.
intros k Hint; elim (Zle_lt_or_eq p k).
intros; apply Hnfound; omega.
intros; subst k; assumption.
omega.
Qed.
 
Theorem pre_prime_decompose:
 forall x, 0 <= x ->
 ~ pre_prime x ->
  (exists y , pre_prime y /\ (( 1 < y < x ) /\ (exists z , x = y * z )) ).
intros x; elim x  using (well_founded_ind (Zwf_well_founded 0)).
clear x; intros x Hind1 Hxpos.
cut (x <= x).
assert (forall p, ( x <= p < x ) ->  not_mult p x).
intros; assert False.
omega.
elim H0.
generalize Hxpos H; clear H.
 pattern x at 1 2 5; elim x using 
   (well_founded_ind (Zwf_well_founded 0)).
intros x' Hind2 Hx'pos.
case (Z_eq_dec x' 0).
intros Heqx'; subst x'.
intros H H0 H1.
elim H1.
intros p Hint.
apply H.
omega.
intros Hx'n0 Hint Hle Hnpp.
case (Z_eq_dec x' 1).
intros Heqx1; subst x'.
elim Hnpp; unfold pre_prime, partial_prime.
intros; apply Hint;omega.
intros Hx'n1.
elim (fun h => mult_dec (x'-1) h x).
intros Hn; apply Hind2 with (x'-1).
unfold Zwf; omega.
omega.
intros p' Hint'.
elim (Zle_lt_or_eq (x'-1) p').
intros Hlt.
apply Hint.
omega.
intros; subst p'; assumption.
omega.
omega.
assumption.
intros Hm.
case (Z_eq_dec x' 2).
intros Heqx'2.
elim Hnpp.
intros k Hint'; apply (Hint k).
omega.
intros Hx'n2.
elim (find_divisor (x'-1) x) with x.
intros z Heq.
elim (pre_prime_dec (x'-1)).
intros Hpr.
exists (x'-1).
split; auto.
split.
split.
omega.
intros;omega.
exists z; assumption.
intros Hnpr.
elim (Hind1 (x'-1)).
intros p' [Hpr' [Hint' [z' Heq']]].
exists p'.
split.
assumption.
split.
omega.
exists (z * z').
rewrite Heq; rewrite Heq'; ring_nat.
unfold Zwf; omega.
omega.
assumption.
omega.
omega.
assumption.
omega.
intros;omega.
omega.
omega.
Qed.
 
Theorem plus_one_not_mult: forall p q r, 1 < p -> p*q+1<>p*r.
intros p q r Hlt Heq.
assert (H:p*(q-r)+1=0).
replace 0 with (p*r-p*r).
pattern (p*r) at 1; rewrite <- Heq;ring.
ring.
case (Z_eq_dec (q-r) 0).
intros Heq'; rewrite Heq' in H; omega.
intros Hne; case (Z_le_gt_dec (q - r) 0).
intros Hle; assert (H0:p*(q-r) <= p*(-1)).
apply Zmult_le_compat_l;try omega.
omega.
intros Hgt; assert (H0:p*1 <= p*(q-r)).
apply Zmult_le_compat_l;try omega.
omega.
Qed.
 
Theorem infinite_primes: forall n,  (exists m, n <= m /\ pre_prime m ).
intros n; elim (pre_prime_dec (fact n + 1)).
intros H; exists (fact n + 1); split; trivial.
apply Zle_trans with (fact n).
apply le_fact.
auto with zarith.
intros Hnpr; elim pre_prime_decompose with (2:= Hnpr).
intros p [Hpr [Hint [z Heq]]].
exists p.
split.
elim (Zle_or_lt n p); auto.
intros Hlt.
rewrite (fact_ex_eq p) in Heq.
elim (plus_one_not_mult p (fact_ex p n) z).
omega.
trivial.
omega.
assumption.
generalize (le_1_fact n); intros;omega.
generalize (le_1_fact n); intros;omega.
Qed.
 
Theorem partial_prime_next:
 forall x m m',
 partial_prime m x ->
 (forall p, ( m <= p < m' ) ->  ~ pre_prime p) ->  partial_prime m' x.
intros x m m' Hppr Hsm p Hint.
intros y Heq.
elim (pre_prime_dec p).
intros Hpr.
assert (Hintp:  1 < p < m ).
split.
omega.
elim (Zle_or_lt m p).
intros Hle; elim (Hsm p); (trivial; (try omega)).
trivial.
elim Hppr with p y; auto.
intros Hnpr.
elim pre_prime_decompose with (2:= Hnpr).
intros p' [Hpr' [Hintp' [z Heq']]].
assert (Hint':  1 < p' < m ).
split.
omega.
elim (Zle_or_lt m p').
intros Hle; elim (Hsm p'); (trivial; (try omega)).
trivial.
elim Hppr with p' (y * z); auto.
rewrite Heq.
rewrite Heq'.
ring.
omega.
omega.
Qed.
