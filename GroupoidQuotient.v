(* -*- mode: coq; mode: visual-line -*-  *)
Require Import HoTT.Basics.
Require Import Groupoid.
Require Import Types.Prod.


(** * Quotient of a Type by a groupoid

We aim to model:
<<
Inductive quotient1 : Type :=
   | point : A -> quotient1
   | cell : forall x y, morphism x y -> point x = point y
   | cell_compose : forall x y z (f : morphism x y) (g : morphism y z),
                    cell (g o f) = cell f @ cell g
   | quotient1_trunc : IsTrunc 1 quotient1
>>
*)

Module Export Quotient1.
Section Domain.
  Variable A : Type.
  Variable R : A -> A -> Type.
  Context {R_HSet : forall x y, IsHSet (R x y)}
          {R_refl : Reflexive R}
          {R_trans : Transitive R}
          {R_symm : Symmetric R}.
  Variable G : groupoid A R.

  Local Open Scope groupoid_scope.

  Private Inductive quotient1 (R : A -> A -> Type)
                    (*`{IsHSet A}*) `{R_HSet : forall x y, IsHSet (R x y)}
                    `{Reflexive _ R} `{Transitive _ R} `{Symmetric _ R}
                     (G : groupoid A R) : Type :=
  | point : A -> quotient1 R G
  .
  Axiom cell : forall {x y}, R x y -> point R G x = point R G y.
  Axiom cell_compose : forall {x y z} (f : R x y) (g : R y z),
        cell (g o f)%groupoid = cell f @ cell g.
  Axiom quotient1_trunc : IsTrunc 1 (quotient1 R G).
  Global Existing Instance quotient1_trunc.

  (* The induction principle for groupoid quotients *)
  Section quotient1_ind.

    Variable P : quotient1 R G -> Type.
    Context {P_1Type : forall a, IsTrunc 1 (P a)}.
    Variable P_point : forall x, P (point R G x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.
    Variable P_compose : forall x y z (f : R x y) (g : R y z),
             P_cell _ _ (g o f)
           = transport2 P (cell_compose f g) (P_point x)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell _ _ f)
           @ P_cell _ _ g).

    Definition quotient1_ind (a : quotient1 R G) : P a :=
      ( match a with
        | point x => fun _ _ _ => P_point x
        end ) P_1Type P_cell P_compose.

    Axiom quotient1_ind_cell : forall {x y} (f : R x y),
          apD quotient1_ind (cell f) = P_cell _ _ f.

    Let quotient1_ind_compose' : forall {x y z} (f : R x y) (g : R y z),
        apD quotient1_ind (cell (g o f))
      = transport2 P (cell_compose f g) (quotient1_ind (point R G x))
      @ apD quotient1_ind (cell f @ cell g).
    Proof.
      intros.
      refine (quotient1_ind_cell (g o f) @ _).
      refine (P_compose _ _ _ f g @ _).
      refine (1 @@ _).
      refine (1 @@ ap _ (quotient1_ind_cell f)^ @@ (quotient1_ind_cell g)^ @ _).
      refine (apD_pp _ _ _)^.
    Defined.


    Axiom quotient1_ind_compose : forall x y z (f : R x y) (g : R y z),
          apD02 quotient1_ind (cell_compose f g)
        = quotient1_ind_compose' f g.


  End quotient1_ind.

Lemma transport_const_pp : forall {A B} {x1 x2 x3 : A} (p : x1 = x2) (q : x2 = x3) (y : B),
      transport_const (p @ q) y
    = transport_pp (fun _ => B) p q y
    @ (ap _ (transport_const p y)
    @ transport_const q y).
Proof.
  destruct p. destruct q. intros.
  auto.
Qed.

Lemma transport_const_inv : forall {A B} {x1 x2 : A}
                                   (p : x1 = x2) {y1 y2 : B} (q : y1 = y2),
      transport_const p y1 @ q
    = ap (transport (fun _ => B) p) q
    @ transport_const p y2.
Proof.
  destruct p; destruct q; auto.
Qed.

Lemma apD_const' : forall {A B} {x y : A} (f : A -> B) (p : x = y),
      ap f p = (transport_const p (f x))^ @ apD f p.
Proof. intros.
       apply moveL_Vp.
       apply (apD_const _ _)^.
Defined.



  (** The recursion principle for groupoid quotients *)
  Section quotient1_rec.

    Variable C : Type.
    Variable C_point : A -> C.
    Variable C_cell : forall {x y}, R x y -> C_point x = C_point y.
    Variable C_compose : forall {x y z} (f : R x y) (g : R y z),
      C_cell _ _ (g o f) = C_cell _ _ f @ C_cell _ _ g.
    Context {C_1Type : IsTrunc 1 C}.

    Let C_cell' : forall {x y} (f : R x y),
      cell f # C_point x = C_point y.
    Proof.
      intros.
      refine (transport_const (cell f) (C_point x) @ C_cell _ _ f).
    Defined.

    Let C_compose' : forall {x y z} (f : R x y) (g : R y z),
        C_cell' (g o f)
      = transport2 (fun _ => C) (cell_compose f g) (C_point x)
      @ ((transport_pp (fun _ => C) (cell f) (cell g) (C_point x)
      @ ap (transport (fun _ => C) (cell g)) (C_cell' f))
      @ C_cell' g).
    Proof.
      intros.
      unfold C_cell'.
        refine (transport2_const (cell_compose f g) _ @@ 1 @ _).
        refine (concat_pp_p _ _ _ @ _).
        refine (1 @@ _).
        refine (1 @@ C_compose _ _ _ f g @ _).
        refine (transport_const_pp _ _ _ @@ 1 @ _).
        set (p := transport_pp (fun _ => C) (cell f) (cell g) (C_point x)).
        set (q := C_cell y z g).
        set (r := C_cell x y f).
        refine (_ @ ((1 @@ (ap_pp _ _ _)^) @@ 1)).
        set (s := ap (transport (fun _ => C) (cell g)) (transport_const (cell f) (C_point x))).
        refine (concat_pp_p _ _ _ @ (1 @@ _) @ concat_p_pp _ _ _).
        refine (concat_pp_p _ _ _ @ (1 @@ _) @ concat_p_pp _ _ _).
        refine (concat_p_pp _ _ _ @ (_ @@ 1) @ concat_pp_p _ _ _).
        apply transport_const_inv.
    Defined.


    Definition quotient1_rec : quotient1 R G -> C.
    Proof.
      apply quotient1_ind with (P_point := C_point) (P_cell := @C_cell'); intros.
      - exact C_1Type.
      - apply C_compose'.
     Defined.

    Lemma quotient1_rec_cell : forall {x y} (f : R x y),
        ap quotient1_rec (cell f) = C_cell _ _ f.
    Proof.
      intros.
      refine (apD_const' _ _ @ _).
      refine (1 @@ quotient1_ind_cell _ _ _ _ _ @ _).
      unfold C_cell'.
      refine (concat_p_pp _ _ _ @ _).
      refine (concat_Vp _ @@ 1 @ _).
      apply concat_1p.
    Qed.

    Let quotient1_rec_compose' : forall {x y z} (f : R x y) (g : R y z),
        ap quotient1_rec (cell (g o f)) = ap quotient1_rec (cell f @ cell g).
    Proof.
      intros.
      refine (_ @ (ap_pp _ _ _)^).
      refine ( quotient1_rec_cell (g o f)
             @ _
             @ ((quotient1_rec_cell f)^ @@ (quotient1_rec_cell g)^)).
      apply C_compose.
    Defined.

    Let quotient1_rec_compose'' : forall {x y z} (f : R x y) (g : R y z),
        apD quotient1_rec (cell (g o f))
      = transport2 (fun _ => C) (cell_compose f g) (quotient1_rec (point R G x))
      @ apD quotient1_rec (cell f @ cell g).
    Proof.
      intros.
      refine (quotient1_ind_cell _ _ _ _ (g o f) @ _).
      refine (C_compose' f g @ _).
      refine (1 @@ _).
      refine (1 @@ ap _ (quotient1_ind_cell _ _ _ _ f)^ @@ (quotient1_ind_cell _ _ _ _ g)^ @ _).
      refine (apD_pp _ _ _)^.
    Defined.

    Lemma quotient1_rec_compose : forall {x y z} (f : R x y) (g : R y z),
        apD02 quotient1_rec (cell_compose f g) = quotient1_rec_compose'' f g.
    Proof.
      intros.
      apply quotient1_ind_compose.
    Qed.

  End quotient1_rec.

  (* The recursion principle can be simplified when the property is a set *)
  Section quotient1_rec_set.

    Variable C : Type.
    Variable C_point : A -> C.
    Variable C_cell : forall {x y}, R x y -> C_point x = C_point y.
    Context {C_set : IsHSet C}.

    Definition quotient1_rec_set : quotient1 R G -> C.
    Proof.
      apply quotient1_rec with (C_point := C_point) (C_cell := C_cell);
      intros.
      - apply C_set.
      - apply trunc_succ.
    Defined.
  End quotient1_rec_set.

  (* The induction principle can be simplified when the property is a set *)
  Section quotient1_ind_set.

    Variable P : quotient1 R G -> Type.
    Context {P_set : forall a, IsHSet (P a)}.
    Variable P_point : forall x, P (point R G x).
    Variable P_cell : forall {x y} (f : R x y),
                      cell f # P_point x = P_point y.

    Definition quotient1_ind_set : forall (q : quotient1 R G), P q.
    Proof.
      apply quotient1_ind with (P_point := P_point) (P_cell := P_cell); intros.
      - apply trunc_succ.
      - apply P_set.
    Defined.
  End quotient1_ind_set.


  (** Inversion principles on paths and quotient types. *)
  Section quotient1_inv.

    Lemma concat_Vp_inversion : forall {A} {x y : A} (p : x = y) (q : y = x),
          p @ q = 1 ->
          p^ = q.
    Proof.
      intros B x y p q H.
      set (H' := moveR_Vp _ _ _ H^).
      rewrite concat_p1 in H'.
      exact H'.
    Qed.


    Lemma concat_V_idempotent : forall {A} {x : A} (p : x = x),
          p @ p^ = p -> p = 1.
    Proof.
      intros B x p H.
      refine (H^ @ _).
      apply concat_pV.
    Qed.

    Lemma concat_p_p : forall {A} {x : A} (p : x = x),
        p @ p = p -> p = 1.
    Proof.
      intros B x p H.
      apply concat_V_idempotent.
      refine ((H^ @@ 1) @ _).
      refine (concat_pp_p _ _ _ @ _).
      refine (1 @@ concat_pV _ @ _).
      apply concat_p1.
    Qed.


    Lemma quotient1_1 : forall x, cell 1 = (1 : point _ _ x = point _ _ x).
    Proof.
      intros x.
      apply concat_p_p.
      rewrite <- cell_compose.
      apply ap.
      apply (g_1_l G 1).
    Qed.

    Lemma quotient1_inv : forall x y (f : R x y),
                                     (cell f)^%path = cell (f^)%groupoid.
    Proof.
      intros x y f.
      apply concat_Vp_inversion.
      rewrite <- cell_compose.
      rewrite g_V_l; auto.
      apply quotient1_1.
    Qed.

  End quotient1_inv.



End Domain.

Arguments quotient1 {A} {R} (*{IsHSet}*) {R_HSet} {reflR transR symmR} G : rename.
Arguments point {A} {R} (*{IsHSet}*) {R_HSet} {reflR transR symmR} G : rename.
Arguments cell {A} {R} (*{IsHSet}*) {R_HSet} {reflR transR symmR} G {x y} : rename.
Arguments cell_compose {A} {R} (*{IsHSet}*) {R_HSet} {reflR transR symmR} G {x y z} : rename.
Arguments quotient1_ind {A R (*A_set*) R_HSet R_refl R_trans R_symm G} P {P_1Type}.
Arguments quotient1_rec {A R (*A_set*) R_HSet R_refl R_trans R_symm G}.
Arguments quotient1_ind_set {A R (*A_set*) R_HSet R_refl R_trans R_symm G} P {P_set}.
Arguments quotient1_rec_set {A R (*A_set*) R_HSet R_refl R_trans R_symm G}.

End Quotient1.


(******************************)

(* We establish several specialized inducition principles for pairs of
groupoids.*)
Section Quotient1_multi.
  Open Scope groupoid_scope.

  Variable A : Type.
  Variable R_A : A -> A -> Type.
  Context (*{A_set : IsHSet A} *)
          {R_A_HSet : forall x y, IsHSet (R_A x y)}
          {R_A_refl : Reflexive R_A}
          {R_A_trans : Transitive R_A}
          {R_A_symm : Symmetric R_A}.
  Variable G_A : groupoid A R_A.

  Variable B : Type.
  Variable R_B : B -> B -> Type.
  Context (*{B_set : IsHSet B} *)
          {R_B_HSet : forall x y, IsHSet (R_B x y)}
          {R_B_refl : Reflexive R_B}
          {R_B_trans : Transitive R_B}
          {R_B_symm : Symmetric R_B}.
  Variable G_B : groupoid B R_B.


  (* Induction over a pair of quotient types *)
  Section quotient1_ind2.
    Variable P : quotient1 G_A -> quotient1 G_B -> Type.
    Context {P_1Type : forall q r, IsTrunc 1 (P q r)}.
    Variable P_point : forall x y, P (point G_A x) (point G_B y).


    Let P_HSet : forall {x y} (pf1 pf2 : P x y), IsHSet (pf1 = pf2).
    Proof.
      intros x y pf1 pf2. do 2 intro. simpl.
      apply P_1Type.
    Qed.


    Variable P_cell_l : forall {x x' y} (f : R_A x x'),
                        transport (fun r => P r (point G_B y)) (cell G_A f) (P_point x y)
                      = P_point x' y.

    Variable P_cell_r : forall x {y y'} (f : R_B y y'),
                        transport (P (point G_A x)) (cell G_B f) (P_point x y)
                      = P_point x y'.

    Variable P_compose_l : forall {x1 x2 x3 y} (f : R_A x1 x2) (g : R_A x2 x3),
             P_cell_l x1 x3 y (g o f)
           = transport2 _ (cell_compose G_A f g) (P_point x1 y)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell_l _ _ y f)
           @ P_cell_l _ _ y g).

    Variable P_compose_r : forall {x y1 y2 y3} (f : R_B y1 y2) (g : R_B y2 y3),
             P_cell_r x _ _ (g o f)
           = transport2 _ (cell_compose G_B f g) (P_point x y1)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell_r x _ _ f)
           @ P_cell_r x _ _ g).


    Let P_point' (q : quotient1 G_A) : forall y, P q (point G_B y).
    Proof.
      intros y.
      generalize dependent q.
      set (Q := fun r => P r (point G_B y)).
      transparent assert (P_point0 : (forall x, P (point G_A x) (point G_B y))).
      { intros x. exact (P_point x y). }
      transparent assert (P_cell0 : (forall {x x'} (f : R_A x x'),
                 transport Q (cell _ f) (P_point0 x) = P_point0 x')).
      { intros x x' f. unfold Q, P_point0.
        apply P_cell_l.
      }
      apply quotient1_ind with (P_point1 := P_point0) (P_cell := P_cell0);
        unfold Q; auto.
      intros x1 x2 x3 f g.
      unfold P_cell0.
      apply P_compose_l.
    Defined.

    (* It might be possible to get rid of this hypothesis? *)
    Variable P_cell_r_eq : forall {x x' y y'} (f : R_A x x') (g : R_B y y'),
        transport (fun r => transport (P r) (cell _ g) (P_point' r y) = P_point' r y')
                  (cell _ f) (P_cell_r x y y' g)
      = P_cell_r x' y y' g.


    Let P_cell_r' q : forall {y y'} (g : R_B y y'),
                      transport (P q) (cell _ g) (P_point' q y)
                    = P_point' q y'.
    Proof.
      intros.
      generalize dependent q.
      set (Q := fun r => transport (P r) (cell _ g) (P_point' r y) = P_point' r y').
      transparent assert (Q_point : (forall x, Q (point G_A x))).
      { intros; unfold Q. simpl.
        apply P_cell_r.
      }
      apply quotient1_ind_set with (P_point0 := Q_point).
      - unfold Q. intros. apply P_HSet.
      - intros. apply P_cell_r_eq.
    Defined.

    Let P_cell' : forall (q : quotient1 G_A) {x' y'} (f : R_B x' y'),
                  cell _ f # P_point' q x' = P_point' q y'.
    Proof.
      intros.
      generalize dependent q.
      set (P0 := fun r => transport (P r) (cell _ f) (P_point' r x') = P_point' r y').
      transparent assert (P_point0 : (forall x, P0 (point _ x))).
      { intros x. apply P_cell_r. }
      apply quotient1_ind_set with (P_point1 := P_point0); intros; unfold P0; auto.
      unfold P_point0.
      apply P_cell_r_eq.
    Defined.


    Let Q {x y z} (f : R_B x y) (g : R_B y z) q :=
                    P_cell' q (g o f)
                   = transport2 (P q) (cell_compose _ f g) (P_point' q x)
                   @ ((transport_pp (P q) (cell _ f) (cell _ g) (P_point' q x)
                   @ ap (transport (P q) (cell _ g)) (P_cell' q f))
                   @ P_cell' q g).

    Let Q_point : forall {y1 y2 y3} (f : R_B y1 y2) (g : R_B y2 y3) x,
                  Q f g (point G_A x).
    Proof.
      intros; unfold Q.
      simpl.
      apply P_compose_r.
    Defined.

    Let P_compose' : forall {x y z} (f : R_B x y) (g : R_B y z) q,
                     Q f g q.
    Proof.
      intros.
      generalize dependent q.
      apply quotient1_ind_set with (P_point0 := Q_point f g); intros.
      - apply trunc_succ.
      - unfold Q_point.
        set (X := P_compose_r y0 x y z f g).
        set (H := P_HSet _ _ (P_cell_r y0 x z (g o f))).
        simpl in H.
        apply H.
    Defined.

    Definition quotient1_ind2 : forall q r, P q r.
    Proof.
      intros q.
      apply quotient1_ind with (P_point0 := P_point' q) (P_cell := @P_cell' q);
        intros; auto.
      apply P_compose'.
    Defined.
  End quotient1_ind2.

  (* Induction principle over a pair of quotient types whith a set-valued property *)
  Section quotient1_ind2_set.
    Variable P : quotient1 G_A -> quotient1 G_B -> Type.
    Context {P_set : forall q r, IsHSet (P q r)}.
    Variable P_point : forall x y, P (point G_A x) (point G_B y).

    Variable P_cell_l : forall {x x' y} (f : R_A x x'),
                        transport (fun r => P r (point G_B y)) (cell G_A f) (P_point x y)
                      = P_point x' y.

    Variable P_cell_r : forall x {y y'} (f : R_B y y'),
                        transport (P (point G_A x)) (cell G_B f) (P_point x y)
                      = P_point x y'.

    Let P_compose_l : forall {x1 x2 x3 y} (f : R_A x1 x2) (g : R_A x2 x3),
             P_cell_l x1 x3 y (g o f)
           = transport2 _ (cell_compose G_A f g) (P_point x1 y)
           @ (transport_pp _ _ _ _
           @ ap _ (P_cell_l _ _ y f)
           @ P_cell_l _ _ y g).
    Proof.
      intros.
      apply P_set.
    Qed.

    Let P_1Type : forall q r, IsTrunc 1 (P q r).
    Proof.  intros q r. exact _. Qed.

    Definition quotient1_ind2_set : forall q r, P q r.
    Proof.
      apply quotient1_ind2 with (P_1Type := P_1Type)
                                (P_point := P_point)
                                (P_cell_l := P_cell_l)
                                (P_cell_r := P_cell_r)
                                (P_compose_l := @P_compose_l).
      * intros. apply P_set.
      * intros. apply P_set.
    Defined.

  End quotient1_ind2_set.

  (* Quotients are functors *)
  Section quotient1_map.

    Variable f : A -> B.
    (* Want: quotient f G_A G_B : (A/G_A) (B/G_B) *)



    Variable map_cell : forall {x y}, R_A x y -> R_B (f x) (f y).
    Variable map_1 : forall x, map_cell x x 1 = 1.
    Variable map_compose : forall {x y z} (f : R_A x y) (g : R_A y z),
             map_cell x z (g o f) = map_cell _ _ g o map_cell _ _ f.


    Definition quotient1_map : quotient1 G_A -> quotient1 G_B.
    Proof.
      apply quotient1_rec
        with (C_point := fun a => point G_B (f a))
             (C_cell := fun x y pf => cell G_B (map_cell _ _ pf)).
      * intros.
        simpl.
        fold (g o f0).
        refine (ap (cell G_B) (map_compose _ _ _ _ _) @ cell_compose _ _ _).
      * apply quotient1_trunc.
    Defined.

    Lemma quotient1_map_point : forall a,
          quotient1_map (point G_A a) = point G_B (f a).
    Proof.
      intros a. reflexivity.
    Qed.

  End quotient1_map.


  Instance R_pair_HSet {A1 A2} (R_A1 : A1 -> A1 -> Type) (R_A2 : A2 -> A2 -> Type)
                            `{forall x y, IsHSet (R_A1 x y)}
                            `{forall x y, IsHSet (R_A2 x y)}
           : forall x y, IsHSet (R_pair R_A1 R_A2 x y).
  Proof.
    intros [a b] [a' b'].
    unfold R_pair.
    apply trunc_prod; auto.
  Qed.


  (* Map a pair of quotient types to a quotient of the pair of the underlying
  groupoids *)
  Section quotient1_curry.

    Let C_point_a_b (a : A) (b : B) : quotient1 (g_pair G_A G_B) :=
      point (g_pair G_A G_B) (a,b).
    Let C_cell_a (b : B) : forall a a', R_A a a' ->
          point (g_pair G_A G_B) (a,b) = point (g_pair G_A G_B) (a',b).
    Proof.
      intros a a' f.
      apply cell.
      split; [exact f | exact 1].
    Defined.

    Let C_compose_a b : forall x y z (f : R_A x y) (g : R_A y z),
        C_cell_a b x z (g o f) = C_cell_a b x y f @ C_cell_a b y z g.
    Proof.
      intros x y z f g.
      unfold C_cell_a.
      set (k := (g o f, 1) : R_pair R_A R_B (x,b) (z,b)).
      set (k2 := (g,1) : R_pair R_A R_B (y,b) (z,b)).
      set (k1 := (f,1) : R_pair R_A R_B (x,b) (y,b)).
      assert (pf : k = k2 o k1).
      { unfold k, k1, k2.
        simpl.
        unfold R_trans.
        fold (1 : R_B b b).
        fold (1 o 1 : R_B b b).
        rewrite (g_1_l G_B).
        reflexivity.
      }
      rewrite pf.
      apply cell_compose.
    Qed.


    Let C_point_b : quotient1 G_A -> B -> quotient1 (g_pair G_A G_B).
    Proof.
      intros q_a b.
      generalize dependent q_a.
      apply quotient1_rec
        with (C_point := fun a => point (g_pair G_A G_B) (a,b))
             (C_cell := C_cell_a b);
        [ | apply quotient1_trunc].
      apply (C_compose_a b).
    Defined.

    Let P0 {b1 b2} (f : R_B b1 b2) (q_a : quotient1 G_A) : Type :=
                                   C_point_b q_a b1 = C_point_b q_a b2.
    Let P_point0 {b1 b2} (f : R_B b1 b2) : forall a, P0 f (point G_A a).
    Proof.
      intros.
      unfold P0. simpl.
      apply cell.
      split; [exact 1 | exact f].
    Defined.


    Lemma transport_path : forall {A B} (P0 P1 : A -> B) {a b} (p : a = b)
                                  (p' : P0 a = P1 a),
      transport (fun x => P0 x = P1 x) p p' = ap P0 p^ @ p' @ ap P1 p.
    Proof.
      destruct p. intros. simpl.
      refine ((concat_1p _)^ @ (concat_p1 _)^).
    Defined.


    Let P_cell0 {b b'} (g : R_B b b') : forall a a' (f : R_A a a'),
        transport (P0 g) (cell _ f) (P_point0 g a) = (P_point0 g a').
    Proof.
      intros a a' f.
      unfold P0.
      set (Q0 := fun q_a => C_point_b q_a b).
      set (Q1 := fun q_a => C_point_b q_a b').
      rewrite (transport_path Q0 Q1).
      rewrite ap_V.

      unfold Q0.
      rewrite quotient1_rec_cell.
      unfold Q1.
      rewrite quotient1_rec_cell.
      unfold C_cell_a, P_point0.
      rewrite quotient1_inv.
      repeat rewrite <- cell_compose.
      apply ap.


      Opaque transitivity reflexivity symmetry.
      rewrite g_pair_sym.
      repeat rewrite g_pair_trans.
      simpl.
      repeat rewrite (g_1_l G_B).
      repeat rewrite (g_1_l G_A).
      rewrite (g_V_r G_A).
      rewrite (g_1_v _ _ G_B).
      rewrite (g_1_r G_B).
      Transparent transitivity reflexivity symmetry.
      reflexivity.
    Defined.

    Let C_cell_curry q_a : forall y y', R_B y y' ->
        C_point_b q_a y = C_point_b q_a y'.
    Proof.
      intros y y' g.
      generalize dependent q_a.
      apply quotient1_ind with (P := P0 g)
                               (P_point := P_point0 g)
                               (P_cell := P_cell0 g).
      * intros q_a. unfold P0.
        apply trunc_succ.
      * intros. apply quotient1_trunc.
    Defined.

    Let C_compose_curry q_a : forall x y z (f : R_B x y) (g : R_B y z),
        C_cell_curry q_a x z (g o f)
      = C_cell_curry q_a x y f @ C_cell_curry q_a y z g.
    Proof.
      intros.
      generalize dependent q_a.

      set (P1 q_a :=
        C_cell_curry q_a x z (g o f)
      = C_cell_curry q_a x y f @ C_cell_curry q_a y z g).

      assert (P_point1 : forall a, P1 (point _ a)).
      { intros. unfold P1. simpl.
        fold (g o f).
        unfold P_point0.
        refine (_ @ cell_compose _ _ _).
        apply ap.
        simpl. unfold R_trans.
        fold (g o f).
        apply (ap (fun h => (h,g o f))).
        fold (1 : R_A a a). fold ((1 : R_A a a) o 1).
        apply (g_1_l G_A _)^.
      }


      apply quotient1_ind_set with (P := P1)
                                   (P_point := P_point1).
      * intros q_a. apply trunc_succ.
      * intros. apply quotient1_trunc.
    Defined.


    Definition quotient1_curry
             : quotient1 G_A -> quotient1 G_B -> quotient1 (g_pair G_A G_B).
    Proof.
      intros q_a.
      apply quotient1_rec
        with (C_point := C_point_b q_a)
             (C_cell := C_cell_curry q_a);
      [ apply C_compose_curry | apply quotient1_trunc].
    Defined.

    Lemma quotient1_curry_point : forall a b,
      quotient1_curry (point G_A a) (point G_B b) = C_point_a_b a b.
    Proof.
      intros. reflexivity.
    Qed.


    Lemma ap2_ap_ap : forall {A B C} (P : A -> B -> C)
                             {a a' : A} {b b' : B} (p : a = a') (q : b = b'),
      ap2 P p q = ap (fun x => P x b) p @ ap (fun y => P a' y) q.
    Proof.
      destruct p; destruct q; reflexivity.
    Qed.
    Lemma ap2_sym : forall {A B C} (P : A -> B -> C)
                           {a a' : A} {b b' : B} (p : a = a') (q : b = b'),
      ap2 P p q = ap2 (fun y x => P x y) q p.
    Proof.
      destruct p; destruct q; reflexivity.
    Qed.

    Lemma quotient1_curry_cell : forall a a' b b' (f : R_A a a') (g : R_B b b'),
      ap2 quotient1_curry (cell G_A f) (cell G_B g)
    = cell (g_pair G_A G_B) ((f,g) : R_pair R_A R_B (a,b) (a',b')).
    Proof.
      intros.
      unfold quotient1_curry.
      rewrite ap2_ap_ap.
      rewrite quotient1_rec_cell. simpl.
      unfold C_point_b.
      rewrite quotient1_rec_cell.
      unfold C_cell_a, P_point0.
      rewrite <- cell_compose.
      apply ap.
      rewrite g_pair_trans.
      rewrite (g_1_l G_A).
      rewrite (g_1_r G_B).
      reflexivity.
    Qed.

  End quotient1_curry.



  (* A recursion principle over a pair of groupoid quotients, which
  significantly simplifies the assumptions of the corresponding induction
  principle. *)
  Section quotient1_rec2.


    Variable C : Type.
    Context {C_1Type : IsTrunc 1 C}.
    Variable C_point : A -> B -> C.
    Variable C_cell : forall {x x' y y'} (f : R_A x x') (g : R_B y y'),
             C_point x y = C_point x' y'.

    Variable C_compose : forall {x1 x2 x3 y1 y2 y3}
                                (f1 : R_A x1 x2) (f2 : R_A x2 x3)
                                (g1 : R_B y1 y2) (g2 : R_B y2 y3),
             C_cell _ _ _ _ (f2 o f1) (g2 o g1)
           = C_cell _ _ _ _ f1 g1 @ C_cell _ _ _ _ f2 g2.


    Let C_HSet : forall (pf1 pf2 : C), IsHSet (pf1 = pf2).
    Proof.
      intros.
      intros x y. simpl.
      apply C_1Type.
    Qed.


    Let C_point' (z : A * B) : C :=
      let (a,b) := z in C_point a b.
    Let C_cell' (z z' : A*B) : R_pair R_A R_B z z' -> C_point' z = C_point' z'.
    Proof.
      destruct z as [a b], z' as [a' b'].
      intros [pf_a pf_b]; simpl in *.
      unfold C_point'.
      apply (C_cell _ _ _ _ pf_a pf_b).
    Defined.

    Let quotient1_rec2_curry : quotient1 (g_pair G_A G_B) -> C.
    Proof.
      apply quotient1_rec
        with (C_point0 := C_point')
             (C_cell0 := C_cell'); auto.
      intros [a1 b1] [a2 b2] [a3 b3] [a12 b12] [a13 b13].
      unfold C_cell'. simpl.
      fold (a13 o a12).
      fold (b13 o b12).
      apply C_compose.
    Defined.

    Lemma ap2_curry : forall {A1 A2 C} (P : A1 -> A2 -> C) {x1 y1 : A1} {x2 y2 : A2}
                            (p1 : x1 = y1) (p2 : x2 = y2),
        ap2 P p1 p2
      = ap (fun (z : A1 * A2) => let (z1,z2) := z in P z1 z2) (ap2 pair p1 p2).
    Proof.
      destruct p1, p2.
      reflexivity.
    Qed.

    Definition quotient1_rec2 : quotient1 G_A -> quotient1 G_B -> C.
    Proof.
      intros a b.
      apply quotient1_rec2_curry.
      apply (quotient1_curry a b).
    Defined.

    Lemma quotient1_rec2_point : forall a b,
        quotient1_rec2 (point G_A a) (point G_B b) = C_point a b.
    Proof.
      intros. reflexivity.
    Qed.

    Lemma quotient1_rec2_cell : forall a a' b b' (f : R_A a a') (g : R_B b b'),
      ap2 quotient1_rec2 (cell G_A f) (cell G_B g)
    = C_cell _ _ _ _ f g.
    Proof.
      intros.
      rewrite ap2_curry.
      unfold quotient1_rec2.
      rewrite ap_compose.

      rewrite <- ap2_curry.
      rewrite quotient1_curry_cell.


      unfold quotient1_rec2_curry.
      rewrite quotient1_rec_cell.

      unfold C_cell'.
      reflexivity.
    Qed.


  End quotient1_rec2.

  (* A map of type A -> B -> C can be lifted to a map of type
     quotient1 A -> quotient1 B -> quotient1 C *)
  Section quotient1_map2.

    Variable C : Type.
    Variable R_C : C -> C -> Type.
    Context (*{C_set : IsHSet C} *)
            {R_C_HSet : forall x y, IsHSet (R_C x y)}
            {R_C_refl : Reflexive R_C}
            {R_C_trans : Transitive R_C}
            {R_C_symm : Symmetric R_C}.
    Variable G_C : groupoid C R_C.

    Variable f : A -> B -> C.
    (* Want: quotient G_A G_B G_C f : A/G_A -> B/G_B -> C/G_C *)
    Variable map_cell : forall {a a' b b'},
             R_A a a' -> R_B b b' -> R_C (f a b) (f a' b').

    Variable map_compose : forall {a1 a2 a3 b1 b2 b3}
                                  (a12 : R_A a1 a2) (a23 : R_A a2 a3)
                                  (b12 : R_B b1 b2) (b23 : R_B b2 b3),
        map_cell _ _ _ _ (a23 o a12) (b23 o b12)
     = (map_cell _ _ _ _ a23 b23) o (map_cell _ _ _ _ a12 b12).

    Let C_point0 := fun a b => point G_C (f a b).
    Let C_cell0 : forall x x' y y', R_A x x' -> R_B y y' ->
                  point G_C (f x y) = point G_C (f x' y').
    Proof.
      intros. apply cell. apply map_cell; auto.
    Defined.

    Let C_compose0 : forall (x1 x2 x3 : A) (y1 y2 y3 : B) (f1 : R_A x1 x2)
                            (f2 : R_A x2 x3) (g1 : R_B y1 y2) (g2 : R_B y2 y3),
        C_cell0 x1 x3 y1 y3 (f2 o f1) (g2 o g1) =
        C_cell0 x1 x2 y1 y2 f1 g1 @ C_cell0 x2 x3 y2 y3 f2 g2.
    Proof.
      intros.
      unfold C_cell0.
      refine (ap (cell G_C) _ @ cell_compose _ _ _).
      apply map_compose.
    Defined.

    Definition quotient1_map2 : quotient1 G_A -> quotient1 G_B -> quotient1 G_C.
    Proof.
      apply quotient1_rec2 with (C_point := C_point0)
                                (C_cell := C_cell0);
        [ apply quotient1_trunc | apply C_compose0 ].
    Defined.

    Lemma quotient1_map2_point : forall a b,
        quotient1_map2 (point G_A a) (point G_B b) = point G_C (f a b).
    Proof.
      intros.
      reflexivity.
    Qed.

    Lemma quotient1_map2_cell : forall a a' b b' (f : R_A a a') (g : R_B b b'),
      ap2 quotient1_map2 (cell G_A f) (cell G_B g)
    = cell G_C (map_cell _ _ _ _ f g).
    Proof.
      intros.
      unfold quotient1_map2.
      apply quotient1_rec2_cell.
    Qed.

  End quotient1_map2.


End Quotient1_multi.
