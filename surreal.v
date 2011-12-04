Inductive empty: Type := .

Inductive step (orig: Type): Type :=
  | compose: (orig -> Prop) -> (orig -> Prop) -> step orig
  | inherit: orig -> step orig
.

Fixpoint game (m: nat): Type :=
  match m with
   | O => empty
   | S m' => step (game m')
  end.

Definition sg: forall m, (step (game m)) -> game (S m) := (fun _ x => x).
    
Inductive gle: forall m n, game m -> game n -> bool -> Prop :=
| gle_Il: forall m n x y b,
  gle m n x y b ->
  gle _ _ (sg _ (inherit _ x)) y b
| gle_Ir: forall m n x y b,
  gle m n x y b ->
  gle _ _ x (sg _ (inherit _ y)) b
| gle_St: forall m n (xL: game m -> Prop) xR yL (yR: game n -> Prop),
  (forall xl, xL xl -> gle (S n) _ (compose (game n) yL yR) xl false) ->
  (forall yr, yR yr -> gle _ (S m) yr (compose (game m) xL xR) false) ->
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) true
| gle_Sfl: forall m n (xL: game m -> Prop) xR y,
  (exists xl, xL xl /\ gle n _ y xl true) ->
  gle (S m) n (compose (game m) xL xR) y false
| gle_Sfr: forall m n x yL (yR: game n -> Prop),
  (exists yr, yR yr /\ gle _ m yr x true) ->
  gle m (S n) x (compose (game n) yL yR) false
.

Ltac inv H := inversion H; subst; clear H.
Ltac gen H a :=
    generalize (H a); clear H; intro H.


Lemma refl: forall m (g: game m), gle _ _ g g true.
induction m.
intro g.
destruct g.

intro g.
destruct g; fold game in *.

rename P into L.
rename P0 into R.
apply gle_St.

intros.
apply gle_Sfl.
exists xl.
intuition.

intros.
apply gle_Sfr.
exists yr.
intuition.

apply gle_Il.
apply gle_Ir.
apply IHm.
Qed.


Definition charm: game 0 -> Prop.
intro.
destruct X.
Defined.



Definition zero: game 1 := compose _ charm charm.
Definition one : game 2 := compose _ (fun _ => True) (fun _ => False).
Definition half: game 3 := compose _ (fun x => x = inherit _ zero) (fun y => y = one).

Lemma zero_one: gle _ _ zero one true.
  apply gle_St.
  intro.
  inv xl.
  intro yr.
  intros.
  apply False_ind.
  assumption.
Qed.

Lemma one_zero: gle _ _ one zero false.
  apply gle_Sfl.
  exists zero.
  split; auto.
  apply refl.
Qed.

Lemma zero_half: gle _ _ zero half true.
  apply gle_St.
  intro xl.
  inv xl.

  intro yr.
  intro o.
  subst.

  apply gle_Sfl.
  exists zero.
  split; auto.
  apply refl.
Qed.
  
