Inductive step (orig: Type): Type :=
  | inherit: orig -> step orig
  | compose: (orig -> Prop) -> (orig -> Prop) -> step orig
.

Inductive empty: Type := .

Fixpoint game (m: nat): Type :=
  match m with
   | O => empty
   | S m' => step (game m')
  end.

Definition sg: forall m, (step (game m)) -> game (S m) := (fun _ x => x).
    
Ltac inv H := inversion H; subst; clear H.
Ltac gen H a :=
    generalize (H a); clear H; intro H.

(* are they needed ?

Axiom ex_bool: forall {A} (f g: A -> bool),
  (forall (a: A), f a = g a) -> f = g.

Lemma empty_uniq: forall
  (x y: empty -> bool),
  x = y.
  intros.
  apply ex_bool.
  intros.
  inv a.
Qed.

*)

Definition gle: forall m n, game m -> game n -> Prop.
intros m n.
remember (m + n) as s. 
assert (m + n <= s).
rewrite Heqs.
auto.
clear Heqs.
generalize m n H.
clear m n H.
induction s.

intros.
destruct m.
inv X.
exact (False). (* never reached *)

intros m n.
intro small.

intros x y.
destruct m.
inv x.

destruct n.
inv y.

case_eq x; fold game in *.
intro x_content.
intro x_eq.
clear x_eq x.

gen IHs m.
gen IHs (S n).
refine (IHs _ x_content y).
Require Import Omega.
omega.

idtac.
intros xL xR.
intro x_eq.

case_eq y; fold game in *.
intro y_content.
intro y_eq.
clear y y_eq.
clear xL xR x_eq.
refine (IHs _ _ _ x y_content).
omega.

intros yL yR.
intro y_eq.
clear x_eq y_eq.
refine (_ /\ _).
gen IHs (S n).
gen IHs m.
assert (S n + m <= s).
omega.
exact (forall (xl: game m), xL xl -> IHs H y xl -> False).

clear xL xR y y yL.
gen IHs n.
gen IHs (S m).
assert (n + S m <= s).
omega.
exact (forall (yr: game n), yR yr -> IHs H yr x -> False).
Defined.

Check gle.

Definition charm: game 0 -> Prop.
intro.
inv X.
Defined.

Definition zero: game 1 := compose _ charm charm.
Definition one : game 2 := compose _ (fun _ => True) (fun _ => False).
Definition half: game 3 := compose _ (fun x => x = inherit _ zero) (fun y => y = one).

Lemma zero_one: gle _ _ zero one.
  compute.
  intuition.
Qed.

Lemma one_zero: gle _ _ one zero -> False.
  compute.
  intuition.
  clear H1.
  gen H0 zero.
  apply H0.
  auto.
  compute.
  intuition.
Qed.

Lemma zero_zero: gle _ _ zero zero.
  compute.
  intuition.
Qed.

Lemma one_one: gle _ _ one one.
  compute.
  intuition.
  destruct xl.
  inv e.
  intuition.
  clear H2.
  apply H1 with zero.
  auto.
  compute.
  intuition.
Qed.

Lemma zero_half: gle _ _ zero half.
  compute.
  intuition.
  subst.
  intuition.
  clear H1.
  gen H zero.
  intuition.
  apply H0.
  compute.
  intuition.
Qed.
  
(* next, reflexivity of gle *)
Lemma refl: forall m g, gle m m g g.
  induction m.
  intros.
  inv g.

  intros.
  destruct g; fold game in *.

  unfold gle.
  simpl.


(* one nice way 
Inductive gle: forall m n, game m -> game n -> bool -> Prop :=
| gle_Sli: forall m n g g' b,
  gle m n g g' b ->
  gle (S m) n (inherit _ g) g' b
| gle_Sri: forall m n g g' b,
  gle m n g g' b ->
  gle _ (S n) g (inherit _ g') b
| gle_St: forall m n (xL: game m -> Prop) xR yL (yR: game n -> Prop),
  (forall xl, xL xl -> gle (S n) _ (compose (game n) yL yR) xl false) ->
  (forall yr, yR yr -> gle _ (S m) yr (compose (game m) xL xR) false) ->
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) true
| gle_Sfl: forall m n (xL: game m -> Prop) xR yL (yR: game n -> Prop),
  (exists xl, xL xl /\ gle (S n) _ (compose (game n) yL yR) xl true) ->
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) false
| gle_Sfr: forall m n (xL: game m -> Prop) xR yL (yR: game n -> Prop),
  (exists yr, yR yr /\ gle _ (S m) yr (compose (game m) xL xR) false) ->
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) false
.
*)


Lemma refl: forall m (g: game m), gle _ _ g g true.
induction m.
intro g.
destruct g.

intro g.
destruct g; fold game in *.
apply gle_Sli.
apply gle_Sri.
apply IHm.

rename P into L.
rename P0 into R.
