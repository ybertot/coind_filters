Require Export Omega.
Require Export ArithRing.
 
Ltac caseEq f := generalize (refl_equal f); pattern f at -1; case f.
 
Theorem minus_S: forall x y, y <= x ->  S x - y = S (x - y).
induction x.
intros y; case y; simpl; auto.
intros y' Hlt; omega.
intros y; case y; auto.
intros y' Hlt; simpl; rewrite <- IHx.
case y'; simpl; auto.
omega.
Qed.
 
Theorem minus_minus: forall x y, x <= y ->  y - (y - x) = x.
induction x.
intros y _; rewrite <- minus_n_O; auto with arith.
intros y Hle; elim Hle.
simpl; rewrite <- minus_n_n; auto.
intros y' Hle' Heq; simpl (S y' - S x).
rewrite minus_S.
rewrite IHx.
auto.
omega.
omega.
Qed.
 
Lemma simpl_int_prop:
 forall m x d n n', n' + (m + 1) <= x -> 0 < d -> x < n ->  ( x - d < x < n ).
intros; omega.
Qed.
 
Lemma simpl_int_prop2:
 forall p x m n, ( 1 < p < m ) -> ( n+(m+1) <= x  ) ->  ( 1 < p < x ).
intros; omega.
Qed.
 
Lemma simpl_int_prop3:
 forall x n d m n', n <= x -> ( n'+(m+1) <= x ) ->  (x - d < n) -> (x - n < d).
intros; omega.
Qed.
 
Lemma simpl_int_prop4: forall x n,  (x - (x - n) <= x).
intros; omega.
Qed.
 
Definition not_mult (n m : nat) : Prop := forall p,  (m <> p * n).
 
Definition partial_prime (m n : nat) : Prop :=
   forall p, ( 1 < p < m ) ->  not_mult p n.
 
Definition pre_prime (n : nat) : Prop := partial_prime n n.
 
Fixpoint fact (n : nat) : nat :=
 match n with 0 => 1 | S p => S p * fact p end.
 
Fixpoint fact_ex (m n : nat) {struct n} : nat :=
 match n with
   O => 1
  | S p => if eq_nat_dec (S p) m then fact p else S p * fact_ex m p
 end.
 
Theorem fact_ex_eq: forall m n, ( 1 < m <= n ) ->  fact n = m * fact_ex m n.
induction n.
intros; omega.
intros Hint; lazy zeta iota beta delta [fact fact_ex]; fold fact fact_ex.
case (eq_nat_dec (S n) m).
intros; subst m; auto.
intros; rewrite IHn.
ring.
omega.
Qed.
 
Theorem le_1_fact: forall n,  (1 <= fact n).
induction n.
auto with arith.
simpl.
generalize (n * fact n); intros; omega.
Qed.
 
Theorem le_fact: forall n,  (n <= fact n).
induction n.
auto with arith.
lazy zeta iota beta delta [fact]; fold fact.
pattern (S n) at 1; replace (S n) with (S n * 1).
apply mult_le_compat_l.
apply le_1_fact.
ring.
Qed.
 
Definition mult_dec_aux:
 forall m n m', n < m' ->  ({ not_mult m n }) + ({ ~ not_mult m n }).
intros m n m'; generalize m n; clear m n; elim m'.
intros m n H; assert False.
omega.
elim H0.
intros m'' f m n Hlt.
elim (le_gt_dec m n).
intros Hle.
destruct m.
destruct n.
right; unfold not_mult.
intros H; apply (H 1); ring.
left; intros p.
rewrite <- mult_n_O.
discriminate.
elim (f (S m) (minus n (S m))).
unfold not_mult; intros Hn; left.
intros p Heq; apply (Hn (p - 1)).
rewrite Heq; rewrite mult_minus_distr_r.
replace (1 * S m) with (S m); ring.
intros Hm; right; intros Hn; apply Hm.
intros p Heq.
apply (Hn (p + 1)).
rewrite (le_plus_minus (S m) n).
rewrite Heq.
ring.
assumption.
omega.
destruct n.
intros _; right; intros Hn; apply (Hn 0).
ring.
intros Hgt; left; intros p Heq.
destruct p.
simpl in Heq |-; discriminate Heq.
simpl in Heq |-.
rewrite Heq in Hgt.
generalize Hgt; case (p * m).
rewrite <- plus_n_O.
exact (lt_irrefl m).
intros; omega.
Defined.
 
Definition mult_dec := fun m n => mult_dec_aux m n (S n) (le_n (S n)).
 
Theorem pre_prime_multiple_diff:
 forall m n d x,
 ( 1 < m < x ) -> n = x - d -> ~ not_mult m (x - d) -> pre_prime x ->  (0 < d).
intros m n d x Hint Heq Hm Hpr.
elim (le_lt_or_eq 0 d); trivial.
intros; subst d.
elim Hm; rewrite <- minus_n_O; apply Hpr.
omega.
auto with arith.
Qed.
 
Theorem partial_prime_step:
 forall m n, partial_prime m n -> not_mult m n ->  partial_prime (S m) n.
intros m n Hppr Hnm p Hint.
elim (Lt.le_lt_or_eq p m).
intros Hlt.
apply Hppr.
omega.
intros; subst p; assumption.
omega.
Qed.
 
Theorem partial_prime_rev:
 forall m n, partial_prime (S m) n ->  partial_prime m n.
intros n m Hppr p Hint; apply Hppr.
omega.
Qed.
 
Theorem partial_prime_le:
 forall m m' n, m <= m' -> partial_prime m' n ->  partial_prime m n.
intros m m' n Hle; elim Hle; clear Hle m'.
trivial.
intros m' Hle Hind Hppr; apply Hind; apply partial_prime_rev; auto.
Qed.
 
Theorem partial_prime_revstep:
 forall m n, 1 < m -> partial_prime (S m) n ->  not_mult m n.
intros n m Hlt Hppr.
apply Hppr.
omega.
Qed.
 
Definition partial_prime_dec:
 forall n m,  ({ partial_prime m n }) + ({ ~ partial_prime m n }).
intros n m; destruct m.
left.
unfold partial_prime.
intros; assert False.
omega.
elim H0.
destruct m.
left; unfold partial_prime; intros; assert False.
omega.
elim H0.
induction m.
left; unfold partial_prime; intros; assert False.
omega.
elim H0.
elim IHm.
intros Hppr; elim (mult_dec (S (S m)) n).
intros Hnm; left; apply partial_prime_step; trivial.
intros Hm; right; intros Hpr.
elim Hm.
apply Hpr; (try omega).
intros Hnpr; right; intros Hpr; elim Hnpr;
 apply partial_prime_le with (S (S (S m))); auto with arith.
Defined.
 
Definition pre_prime_dec (n : nat) : ({ pre_prime n }) + ({ ~ pre_prime n }) :=
   partial_prime_dec n n.
 
Theorem pre_prime2: pre_prime 2.
intros p Hint; assert False; [omega | elim H].
Qed.
 
Definition find_divisor:
 forall n m,
 ( 1 < n < m ) ->
 ~ not_mult n m ->
 forall p,
 (forall k, ( p < k < m ) ->  (m <> n * k)) ->  ({z : nat | m = n * z}).
intros n m Hlt Hm p; elim p.
intros Hn.
elim Hm.
intros k Hint.
elim (le_or_lt k 0).
intros Hk0; assert (Hk0': k = 0).
omega.
subst k; omega.
intros H0ltk.
elim (le_or_lt m k).
intros Hmk.
destruct n.
omega.
destruct n.
omega.
repeat rewrite <- mult_n_Sm in Hint.
generalize Hint; generalize (k * n); intros; omega.
intros Hkm.
apply (Hn k).
omega.
rewrite Hint; ring.
intros p' Hind Hnfound.
elim (eq_nat_dec m (n * S p')).
intros Heq; exists (S p'); assumption.
intros Hn; apply Hind.
intros k Hint; elim (le_lt_or_eq (S p') k).
intros; apply Hnfound; omega.
intros; subst k; assumption.
omega.
Qed.
 
Theorem pre_prime_decompose:
 forall x,
 ~ pre_prime x ->
  (exists y , pre_prime y /\ (( 1 < y < x ) /\ (exists z , x = y * z )) ).
intros x; elim x  using (well_founded_ind Wf_nat.lt_wf).
clear x; intros x Hind1.
generalize (le_n x).
assert (forall p, ( x <= p < x ) ->  not_mult p x).
intros; assert False.
omega.
elim H0.
generalize H; clear H; pattern x at 1 4; elim x.
intros H H0 H1.
elim H1.
intros p Hint.
apply H.
omega.
intros y Hind p Hint Hle.
elim (mult_dec y x).
intros Hn; apply Hind.
intros p' Hint'.
elim (le_lt_or_eq y p').
intros Hlt.
apply p.
omega.
intros; subst p'; assumption.
omega.
omega.
assumption.
intros Hm.
destruct y.
elim Hm.
unfold not_mult.
intros k Heq.
rewrite <- mult_n_O in Heq.
subst x.
omega.
destruct y.
elim Hle.
intros k Hint'; apply (p k).
omega.
elim (find_divisor (S (S y)) x) with x.
intros z Heq.
elim (pre_prime_dec (S (S y))).
intros Hpr.
exists (S (S y)).
split; auto.
split.
omega.
exists z; assumption.
intros Hnpr.
elim (Hind1 (S (S y))).
intros p' [Hpr' [Hint' [z' Heq']]].
exists p'.
split.
assumption.
split.
omega.
exists (z * z').
rewrite Heq; rewrite Heq'; ring.
omega.
assumption.
omega.
assumption.
intros; omega.
Qed.
 
Theorem plus_one_not_mult: forall p q r, 1 < p ->  (p * q + 1 <> p * r).
intros p q; elim q.
intros r; destruct r.
intros; omega.
replace (p * S r) with (p + p * r).
generalize (p * r); intros; omega.
ring.
intros q' Hind r.
destruct r.
generalize (p * S q'); intros; omega.
replace (p * S q' + 1) with (p + (p * q' + 1)).
replace (p * S r) with (p + p * r).
intros Hlt Heq.
apply (Hind r).
trivial.
apply plus_reg_l with p.
trivial.
ring.
ring.
Qed.
 
Theorem infinite_primes: forall n,  (exists m : nat , n <= m /\ pre_prime m ).
intros n; elim (pre_prime_dec (fact n + 1)).
intros H; exists (fact n + 1); split; trivial.
apply le_trans with (fact n).
apply le_fact.
auto with arith.
intros Hnpr; elim (pre_prime_decompose _ Hnpr).
intros p [Hpr [Hint [z Heq]]].
exists p.
split.
elim (le_or_lt n p); auto.
intros Hlt.
rewrite (fact_ex_eq p) in Heq.
elim (plus_one_not_mult p (fact_ex p n) z).
omega.
trivial.
omega.
assumption.
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
elim (Lt.le_or_lt m p).
intros Hle; elim (Hsm p); (trivial; (try omega)).
trivial.
elim Hppr with p y; auto.
intros Hnpr.
elim (pre_prime_decompose _ Hnpr); intros p' [Hpr' [Hintp' [z Heq']]].
assert (Hint':  1 < p' < m ).
split.
omega.
elim (Lt.le_or_lt m p').
intros Hle; elim (Hsm p'); (trivial; (try omega)).
trivial.
elim Hppr with p' (y * z); auto.
rewrite Heq.
rewrite Heq'.
ring.
Qed.
