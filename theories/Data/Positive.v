Require Import BinPos.
Require Import ExtLib.Programming.Show.
Require Import ExtLib.Structures.CoMonad.
Require Import ExtLib.Structures.CoMonadLaws.

Global Instance Show_positive : Show positive :=
{ show p := show (Pos.to_nat p) }.

Section iter.
  Context {m : Type -> Type}.
  Context {CM : CoMonad m}.
  Context {T : Type}.

  Fixpoint Piter (f : m T -> T) (p : positive) : m T -> T :=
    match p with 
      | xH => f
      | xI p => fun x => Piter (fun y => coret (cobind (cobind y f) f)) p (cobind x f)
      | xO p => fun x => Piter (fun y => coret (cobind (cobind y f) f)) p x
    end.

  Context {CML : CoMonadLaws _ CM}.

  Ltac cm := 
    repeat (rewrite cobind_assoc by eauto with typeclass_instances ||
            rewrite coret_cobind by eauto with typeclass_instances ||
            rewrite cobind_coret by eauto with typeclass_instances).

      
  Require Import FunctionalExtensionality.


  Theorem Piter_cobind : forall p f g x,
    (forall x, g (cobind x f) = f (cobind x g)) ->
    Piter f p (cobind x g) = g (cobind x (Piter f p)).
  Proof.
    induction p; simpl; intros; auto.
    { cutrewrite (cobind (cobind x g) f = cobind (cobind x f) g).
      { cm. rewrite IHp. cm.
        f_equal. f_equal. apply functional_extensionality; intros.
        clear H g. rewrite IHp; auto. intros.
        erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
        cm. f_equal. f_equal. apply functional_extensionality; intros.
        f_equal. cm. f_equal. apply functional_extensionality; intros.
        erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
        reflexivity.
        { intros. rewrite H.
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          cm. f_equal. f_equal. apply functional_extensionality; intros.
          f_equal. cm. f_equal. apply functional_extensionality; intros.
          rewrite <- cobind_assoc by auto with typeclass_instances.
          rewrite <- H. f_equal. cm. f_equal. apply functional_extensionality; intros.
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          auto. }  }
      { cm. f_equal. apply functional_extensionality; intros. auto. } }
    { rewrite <- IHp. reflexivity.
      intros. cm. 
      erewrite <- coret_cobind with (f := g) by eauto with typeclass_instances.
      cm. f_equal. f_equal. apply functional_extensionality; intros.
      cutrewrite (cobind (cobind x1 g) f = cobind (cobind x1 f) g).
      rewrite <- H. f_equal. cm. f_equal. apply functional_extensionality; intros.
      erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
      reflexivity.
      
      { cm. f_equal. apply functional_extensionality; intros. auto. } }
  Qed.

  Theorem Piter_unroll : forall p f x,
    Piter f p x = match p with
                    | xH => f x
                    | xI p => 
                      coret (cobind (cobind (cobind x f) (Piter f p)) (Piter f p))
                    | xO p => 
                      coret (cobind (cobind x (Piter f p)) (Piter f p))
                  end.
  Proof.
    induction p; simpl; try reflexivity; intros; try rewrite IHp; simpl.
    { destruct p; try reflexivity.
      simpl.
      cm.
      f_equal. f_equal.
      apply functional_extensionality; intros.
      f_equal.
      cm. 
      f_equal.
      apply functional_extensionality; intros.
      simpl in *.
      rewrite Piter_cobind. 
      { cm. rewrite coret_cobind by eauto with typeclass_instances.
        f_equal. cm. f_equal. apply functional_extensionality; intros.
        rewrite Piter_cobind; try reflexivity.
        { intros. clear - IHp CML. 
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          cm. f_equal; f_equal. apply functional_extensionality; intros.
          f_equal. cm. f_equal. apply functional_extensionality; intros.
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          reflexivity. } }
      { intros. cm. reflexivity. } }
    { destruct p; try reflexivity. simpl in *.
      cm. f_equal. f_equal. apply functional_extensionality; intros.
      f_equal. cm. f_equal. apply functional_extensionality; intros.
      rewrite Piter_cobind.
      { cm. rewrite coret_cobind by eauto with typeclass_instances.
        f_equal. cm. f_equal. apply functional_extensionality; intros.
        rewrite Piter_cobind. reflexivity.
        { intros. cm.
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          cm. f_equal. f_equal. apply functional_extensionality; intros.
          f_equal. cm. f_equal. apply functional_extensionality; intros.
          erewrite <- coret_cobind with (f := f) by eauto with typeclass_instances.
          reflexivity. } }
      { intros. reflexivity. } } 
  Qed.

End iter.
