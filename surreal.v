Inductive step (orig: Set): Set :=
  | inherit: orig -> step orig
  | compose: (orig -> bool) -> (orig -> bool) -> step orig
.

Inductive empty: Set := .

Fixpoint game (m: nat): Set :=
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
  

Inductive gle: forall m n, game m -> game n -> bool -> Prop :=
| gle_Sli: forall m n g g' b,
  gle m n g g' b ->
  gle (S m) n (inherit _ g) g' b
| gle_Sri: forall m n g g' b,
  gle m n g g' b ->
  gle _ (S n) g (inherit _ g') b
| gle_S: forall m n xL xR yL yR,
  (forall xl, xL xl = true -> gle (S n) _ (compose (game n) yL yR) xl false) ->
  (* add the other condition *)
  gle (S m) (S n) (compose (game m) xL xR) (compose (game n) yL yR) true
.












Definition _gle: forall s, forall m n, m + n <= s -> game m -> game n -> bool.
induction s.
intros.
exact (true).

intros m n H x y.
destruct m; destruct n.
exact (true).

case_eq y.
fold game.
intro y_content.
intro y_eq.
refine (IHs 0 n _ x y_content).
Require Omega.
omega.

fold game.
intros L R.
intro y_eq.
clear y_eq.
clear L.
rename R into yR.
gen IHs n.
gen IHs O.
assert (n + 0 <= s).
omega.
gen IHs H0.
clear H0.
generalize ok_yRx.
intro ok.
gen ok (game O).
gen ok (game n).
exact (ok x yR IHs).

case_eq x.
fold game.
intro x_content.
intro x_eq.
gen IHs m.
gen IHs O.
apply IHs.
omega.
exact x_content.
exact y.
fold game.
intros xL xR.
intro x_eq.
generalize ok_yxL.
intro ok.
gen ok (game m).
gen ok (game O).
refine (ok xL y _ ).
gen IHs O.
gen IHs m.
apply IHs.
omega.

case_eq x; fold game; case_eq y; fold game.
intro y_content.
intro y_eq.
clear y y_eq.
intro x_content.
intro x_eq.
clear x_eq x.
gen IHs m.
gen IHs n.
apply IHs.
omega.
exact x_content.
exact y_content.


intros yL yR.
intro y_eq.
clear yL yR y_eq.
intro x_content.
intro x_eq.
clear x x_eq.
gen IHs m.
gen IHs (S n).
apply IHs.
omega.
exact x_content.
exact y.

intro y_content.
intro y_eq.
clear y_eq y.
intros _ _ _.
gen IHs (S m).
gen IHs n.
apply IHs.
omega.
exact x.
exact y_content.

intros yL yR.
intro y_eq.
intros xL xR.
intro x_eq.

refine (andb _ _); [ generalize ok_yxL | generalize ok_yRx ].
intro ok.
clear x_eq y_eq xR x yL yR.
gen ok (game m).
gen ok (game (S n)).
apply ok.
apply xL.
apply y.
apply IHs.
omega.

clear x_eq xL xR.
clear y_eq y yL.
intro ok.
gen ok (game (S m)).
gen ok (game n).
apply ok.
apply x.
apply yR.
apply IHs.
omega.
Defined.

Lemma plpl: forall m n,
  m + n <= m + n.
  intros.
  omega.
Qed.

Definition gle { m n } (g: game m) (g' :game n): bool :=
  _gle (m + n) m n (plpl m n) g g'.

Definition zero : game O := tt.

Definition one : game (S O) := compose unit (zero :: nil) nil.
Definition neg_one : game (S O) := compose unit nil (zero :: nil).

Eval compute in (gle one zero). (* false *)
Eval compute in (gle zero zero). (* true *)
Eval compute in (gle neg_one zero). (* true *)
Eval compute in (gle one zero). (* false *)

Print _gle.

Lemma inhL: forall m n (Sg: game (S n)) (g: game n) (g': game m),
  gle (sg n (inherit (game n) g)) g' = gle g g'.
intros.
unfold sg.
unfold gle.
destruct m.
destruct g'.



Lemma refl: forall m (g: game m), gle g g = true.
induction m.

(* base case *)
intro g.
destruct g.
reflexivity.

(* S *)
intro g.
destruct g.
fold game in *.
