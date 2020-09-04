(* 2019 Maciej Piróg

A solution to Exercise 4.7 from the HoTT book <https://homotopytypetheory.org/book/>,
which I find quite non-trivial.
*)

(* -------------------------- *)
(*  General HoTT definitions  *)
(* -------------------------- *)

(* paths *)

Definition Ω {A : Type} (x : A) := x = x.

Ltac path_induction p := refine match p with eq_refl => _ end.

Definition rev {A : Type} {x y : A} (p : x = y) : y = x :=
  match p with
  |eq_refl => eq_refl
  end.

Definition concat {A : Type} {x y z : A} (p : x = y) (q : y = z) : x = z :=
  match q with eq_refl =>
    match p with eq_refl => eq_refl
    end
  end.

Notation " p ▪ q " := (concat p q) (at level 44, left associativity).

Lemma concat_rev : forall (A : Type) (x y : A) (p : x = y), p ▪ rev p = eq_refl.
Proof.
intros.
path_induction p.
simpl.
reflexivity.
Qed.

Lemma rev_concat : forall (A : Type) (x y : A) (p : x = y), rev p ▪ p = eq_refl.
Proof.
intros.
path_induction p.
simpl.
reflexivity.
Qed.

Lemma concat_assoc : forall (A : Type) (x y z t : A) (p : x = y) (q : y = z) (r : z = t),
  (p ▪ q) ▪ r = p ▪ (q ▪ r).
Proof.
intros.
path_induction r.
path_induction q.
path_induction p.
simpl.
reflexivity.
Qed.

Lemma concat_refl : forall (A : Type) (x y : A) (p : x = y), p ▪ eq_refl = p.
Proof.
intros.
path_induction p.
simpl.
reflexivity.
Qed.

(* functions *)

Definition id {A : Type} (x : A) := x.

Definition comp {A B C : Type} (g : B -> C) (f : A -> B) (x : A) := g (f x).

Notation " f ∘ g " := (comp f g) (at level 40).

Definition ap {A B : Type} (f : A -> B) {x y} (p : x = y) : f x = f y :=
  match p with
  | eq_refl => eq_refl
  end.

Lemma ap_concat {A B : Type} (f : A -> B) {x y z} (p : x = y) (q : y = z) :
  ap f p ▪ ap f q = ap f (p ▪ q).
Proof.
path_induction q.
destruct p.
simpl.
reflexivity.
Qed.

Lemma ap_refl {A B : Type} (f : A -> B) x : ap f (x:=x)(y:=x) eq_refl = eq_refl.
Proof.
unfold ap.
reflexivity.
Qed.

Definition homotopy {A B : Type} (f g : A -> B) := forall x, f x = g x.

Notation " f ~ g " := (homotopy f g) (at level 65, no associativity).

Definition cancellative {A B : Type} (f : A -> B) := forall x y, f x = f y -> x = y.

(* equivalences *)

Inductive is_equiv {A B : Type} (f : A -> B) : Type :=
| Is_equiv : forall (linv : B -> A) (lambda : linv ∘ f ~ id)
                    (rinv : B -> A) (rho    : f ∘ rinv ~ id), is_equiv f.

Ltac exact_inverse f := refine (Is_equiv _ f _ f _).

Lemma inverses_homotopy {A B : Type} (f : A -> B) (e : is_equiv f) :
  match e with
  | Is_equiv _ l _ r _ => l ~ r
  end.
Proof.
destruct e.
unfold comp, homotopy, id in *.
intro.
replace (linv x) with (linv (f (rinv x))).
- rewrite lambda. reflexivity.
- rewrite rho. reflexivity.
Qed.

Inductive equiv (A B : Type) :=
| Equiv : forall (e : A -> B) (EQUIV : is_equiv e), equiv A B.

Notation " A ≅ B " := (equiv A B) (at level 66, no associativity).

Ltac exact_equivalence f g := refine (Equiv _ _ f (Is_equiv _ g _ g _)).

(* -------------------------- *)
(*  Solution to Exercise 4.7  *)
(* -------------------------- *)

Section Ex4_7.

Variable A B : Type.
Variable f : A -> B.
Variable canc : cancellative f.

Definition ap_Omega x : Ω x -> Ω (f x) := ap f.

Variable loops_equiv : forall x, is_equiv (ap_Omega x).
Variable ap_Omega_refl : forall x, ap_Omega x eq_refl = eq_refl.

Definition ap_Omega_inv x : Ω (f x) -> Ω x :=
  match loops_equiv x with
  | Is_equiv _ l _ _ _ => l
  end.

Definition ap_f_inv {x y} (p : f x = f y) : x = y :=
  let r := canc x y p
  in  ap_Omega_inv x (p ▪ ap f (rev r)) ▪ r.

Lemma loop_linv {x : A} (p : x = x) : ap_Omega_inv x (ap f p) = p.
Proof.
unfold ap_Omega_inv.
destruct loops_equiv.
unfold ap_Omega in lambda.
apply lambda.
Qed.

Lemma loop_rinv {x : A} (p : f x = f x) : ap f (ap_Omega_inv x p) = p.
Proof.
unfold ap_Omega_inv.
assert (h := inverses_homotopy (ap_Omega x) (loops_equiv x)).
destruct loops_equiv.
rewrite h.
unfold ap_Omega in rho.
apply rho.
Qed.

Theorem exercise4_7 : forall x y, is_equiv (ap(x:=x)(y:=y) f).
Proof.
intros x y.
refine (Is_equiv _ ap_f_inv _ ap_f_inv _).
- unfold comp, homotopy, id.
  intro p.
  unfold ap_f_inv.
  rewrite ap_concat.
  rewrite loop_linv.
  rewrite concat_assoc.
  rewrite rev_concat.
  rewrite concat_refl.
  reflexivity.
- unfold comp, homotopy, id.
  intro p.
  unfold ap_f_inv.
  rewrite <- ap_concat.
  rewrite loop_rinv.
  rewrite concat_assoc.
  rewrite ap_concat.
  rewrite rev_concat.
  rewrite ap_refl.
  rewrite concat_refl.
  reflexivity.
Qed.

End Ex4_7.

