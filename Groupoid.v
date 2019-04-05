Require Import HoTT.Basics.

Delimit Scope groupoid_scope with groupoid.

Local Open Scope groupoid_scope.

(* A groupoid is a category where every morphism is invertible. The definition
in this file is stand-alone, in that it does not rely on an underlying
definition of categories. Later work could integrate this with existing
developments of category theory in this library. *)
Section groupoid.
  Variable A : Type.
  Variable (R : A -> A -> Type).
  Context {A_set : IsHSet A}
          {R_HSet : forall x y, IsHSet (R x y)}
          {R_refl : Reflexive R}
          {R_trans : Transitive R}
          {R_symm : Symmetric R}.


  Local Notation "g 'o' f" := (transitivity f g) : groupoid_scope.
  Local Notation "1" := (reflexivity _) : groupoid_scope.
  Local Notation "f ^" := (symmetry _ _ f) : groupoid_scope.

  Record groupoid := { g_1_l : forall {x y} (f : R x y), 1 o f = f
                     ; g_1_r : forall {x y} (f : R x y), f o 1 = f
                     ; g_assoc : forall {x y z w} (f : R x y) (g : R y z) (h : R z w),
                                 h o (g o f) = (h o g) o f
                     ; g_V_r : forall {x y} (f : R x y), f o f^ = 1
                     ; g_V_l : forall {x y} (f : R x y), f^ o f = 1
                     }.

  Lemma g_V_V : forall (G : groupoid) x y (f : R x y), f^^ = f.
  Proof.
    intros.
    transitivity (f^^ o (f^ o f)).
    - transitivity (f^^ o 1).
      * apply (g_1_r G _)^.
      * apply (ap (fun z => f^^ o z)).
        refine (g_V_l G _)^.
    - refine (_ o g_assoc G _ _ _).
      transitivity (1 o f); [ | apply (g_1_l G)].
      apply (ap (fun z => z o f)).
      apply (g_V_l G f^).
  Qed.

  Lemma inv_eq : forall (G : groupoid) x y (f : R x y) (g : R y x),
        f o g = 1 <-> f^ = g.
  Proof.
    intros.
    split; intros eq.
    - transitivity (f^ o 1); [ apply (g_1_r G _)^ | ].
      rewrite <- eq.
      rewrite (g_assoc G).
      rewrite (g_V_l G).
      apply (g_1_l G).
    - rewrite <- eq.
      apply (g_V_r G).
  Qed.

  Definition cmp_eq : forall {x1 x2 x3} {f f' : R x1 x2} {g g' : R x2 x3},
             f = f' -> g = g' -> g o f = g' o f'.
  Proof.
    intros x1 x2 x3 f f' g g' H_f H_g.
    rewrite H_f.
    rewrite H_g.
    reflexivity.
  Defined.

  Lemma inv_compose : forall (G : groupoid) {x y z} (f : R x y) (g : R y z),
        (g o f)^ = f^ o g^.
  Proof.
    intros.
    apply (inv_eq G).
    refine (_ o (g_assoc G _ _ _)^).
    rewrite (g_assoc G g^ f^ f).
    rewrite (g_V_r G).
    rewrite (g_1_l G).
    apply (g_V_r G).
  Qed.

  Lemma g_1_v : forall (G : groupoid) {x}, (1 : R x x)^ = 1.
  Proof.
    intros G x.
    refine ((g_1_l G _)^ @ _).
    apply (g_V_r G).
  Qed.

End groupoid.

Close Scope groupoid_scope.

Module Export GroupoidNotations.
  Notation "g 'o' f" := (transitivity f g) : groupoid_scope.
  Notation "1" := (reflexivity _) : groupoid_scope.
  Notation "f ^" := (symmetry _ _ f) : groupoid_scope.
End GroupoidNotations.



Arguments g_1_l {A} {R R_refl R_trans R_symm} G {x y} : rename.
Arguments g_1_r {A} {R R_refl R_trans R_symm} G {x y} : rename.
Arguments g_assoc {A} {R R_refl R_trans R_symm} G {x y z w} : rename.
Arguments g_V_l {A} {R R_refl R_trans R_symm} G {x y} : rename.
Arguments g_V_r {A} {R R_refl R_trans R_symm} G {x y} : rename.
Arguments g_V_V {A} {R R_refl R_trans R_symm} G {x y} : rename.



Section GroupoidPair.
  Variable A B : Type.
  Variable (R_A : A -> A -> Type).
  Variable (R_B : B -> B -> Type).

  Context {R_A_refl  : Reflexive R_A}
          {R_A_trans : Transitive R_A}
          {R_A_sym   : Symmetric R_A}.
  Context {R_B_refl  : Reflexive R_B}
          {R_B_trans : Transitive R_B}
          {R_B_sym   : Symmetric R_B}.

  Variable g_A : groupoid A R_A.
  Variable g_B : groupoid B R_B.

  Definition R_pair (z : A * B) (z' : A * B) : Type :=
    let (a,b) := z in
    let (a',b') := z' in
    R_A a a' * R_B b b'.
  Global Instance R_refl : Reflexive R_pair.
  Proof.
    intros [a b]. split; auto.
  Defined.
  Global Instance R_trans : Transitive R_pair.
  Proof.
    intros [a b] [a' b'] [a'' b''] [pf_a pf_b] [pf_a' pf_b'].
    split; [apply (R_A_trans _ _ _ pf_a pf_a') | apply (R_B_trans _ _ _ pf_b pf_b')].
  Defined.
  Global Instance R_sym : Symmetric R_pair.
  Proof.
    intros [a b] [a' b'] [pf_a pf_b]. split; auto.
  Defined.

  Open Scope groupoid_scope.

  Definition g_pair : @groupoid (A * B) R_pair R_refl R_trans R_sym.
  Proof.
    split.
    * intros [a b] [a' b'] [pf_a pf_b].
      simpl. unfold R_trans. simpl.
      fold (1 : R_A a' a').
      fold (1 : R_B b' b').
      fold (transitivity pf_a 1).
      fold (transitivity pf_b 1).
      rewrite (g_1_l g_A).
      rewrite (g_1_l g_B).
      reflexivity.
    * intros [a b] [a' b'] [pf_a pf_b].
      simpl. unfold R_trans. simpl.
      fold (1 : R_A a a).
      fold (1 : R_B b b).
      fold (transitivity 1 pf_a).
      fold (transitivity 1 pf_b).
      rewrite (g_1_r g_A).
      rewrite (g_1_r g_B).
      reflexivity.
    * intros [a1 b1] [a2 b2] [a3 b3] [a4 b4] [a12 b12] [a23 b23] [a34 b34].
      simpl. unfold R_trans.
      fold (a23 o a12). fold (a34 o (a23 o a12)).
      fold (b23 o b12). fold (b34 o (b23 o b12)).
      fold (a34 o a23). fold ((a34 o a23) o a12).
      fold (b34 o b23). fold ((b34 o b23) o b12).
      rewrite (g_assoc g_A).
      rewrite (g_assoc g_B).
      reflexivity.
    * intros [a b] [a' b'] [pf_a pf_b].
      simpl. unfold R_trans, R_refl; simpl.
      fold (pf_a ^). fold (pf_b ^).
      fold (pf_a o pf_a^).
      fold (pf_b o pf_b^).
      rewrite (g_V_r g_A).
      rewrite (g_V_r g_B).
      reflexivity.
    * intros [a b] [a' b'] [pf_a pf_b].
      simpl. unfold R_trans, R_refl; simpl.
      fold (pf_a ^). fold (pf_b ^).
      fold (pf_a^ o pf_a).
      fold (pf_b^ o pf_b).
      rewrite (g_V_l g_A).
      rewrite (g_V_l g_B).
      reflexivity.
  Defined.

  Lemma g_pair_refl : forall a b, (1 : R_pair (a,b) (a,b)) = (1,1).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma g_pair_sym : forall a a' b b' (f : R_A a a') (g : R_B b b'),
    (f,g)^ = ((f^,g^) : R_pair (a',b') (a,b)).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma g_pair_trans : forall a1 a2 a3 b1 b2 b3
                              (f : R_A a1 a2) (f' : R_A a2 a3)
                              (g : R_B b1 b2) (g' : R_B b2 b3),
      ((f',g') : R_pair (a2,b2) (a3,b3)) o ((f,g) : R_pair (a1,b1) (a2,b2))
    = ((f' o f, g' o g) : R_pair (a1,b1) (a3,b3)).
  Proof.
    reflexivity.
  Qed.


End GroupoidPair.

Arguments R_pair {A B} R_A R_B.
Arguments g_pair {A B R_A R_B R_A_refl R_A_trans R_A_sym R_B_refl R_B_trans R_B_sym}.

