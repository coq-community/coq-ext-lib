Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive order := Less | Equal | Greater.

Section tree.
  Variable A:Type.
  Variable A_eq : A -> A -> Prop.
  Variable A_eq_dec : A -> A -> bool.
  Variable A_lt : A -> A -> Prop.
  Variable A_lt_dec : A -> A -> bool.

  Definition compareo (a1:A) (a2:A) : order :=
  if A_eq_dec a1 a2 then Equal
  else if A_lt_dec a1 a2 then Less
  else Greater.

  (* a two-three tree *)
  Inductive tree :=
  (* Null_t = _ *)
  | Null_t : tree
  (*                [a]
   * Two_t X a y =  / \
   *               X   Y
   * Invariant: x in X => x < a; y in Y => y > a
   *)
  | Two_t : tree -> A -> tree -> tree
  (*                       [a][b]
   * Three_t X a Y b Z =  /  |  \
   *                     X   Y   Z
   * Invariant: x in X => x < a; y in Y => a < y < b; z in Z => z > b
   *)
  | Three_t : tree -> A -> tree -> A -> tree -> tree
  .

  Fixpoint in_t (a:A) (t:tree) : Prop :=
  match t with
  | Null_t => False
  | Two_t tl a' tr => A_eq a a' \/ in_t a tl \/ in_t a tr
  | Three_t tl al tm ar tr => A_eq a al \/ A_eq a ar \/ in_t a tl \/ in_t a tm \/ in_t a tr
  end.

  Fixpoint height_t (t:tree) : nat :=
  match t with
  | Null_t => O
  | Two_t tl _ tr => max (height_t tl) (height_t tr)
  | Three_t tl _ tm _ tr => max (max (height_t tl) (height_t tm)) (height_t tr)
  end.

  Fixpoint tree_wf (t:tree) : Prop :=
  match t with
  | Null_t => True
  | Two_t tl a tr =>
         (forall x:A, (in_t x tl -> A_lt x a)
                   /\ (in_t x tr -> A_lt a x))
      /\ (height_t tl = height_t tr)
  | Three_t tl al tm ar tr =>
          (forall x:A, (in_t x tl -> A_lt x al)
                    /\ (in_t x tm -> A_lt al x /\ A_lt x ar)
                    /\ (in_t x tr -> A_lt ar x))
      /\ (height_t tl = height_t tm)
      /\ (height_t tm = height_t tr)
  end.

  (* a context of a two-three tree. this is the type of taking a tree and
   * replacing a sub-tree with a hole.
   *)
  Inductive context :=
  (* Top_c = _ *)
  | Top_c : context
  (*                         C
   * TwoLeftHole_c a Y C =   |
   *                        [a]
   *                        / \
   *                       ?   Y
   *)
  | TwoLeftHole_c : A -> tree -> context -> context
  (*                          C
   * TwoRightHole_c X a C =   |
   *                         [a]
   *                         / \
   *                        X   ?
   *)
  | TwoRightHole_c : tree -> A -> context -> context
  (*                             C
   * ThreeLeftHole a Y b Z C =   |
   *                           [a][b]
   *                          /  |  \
   *                         ?   Y   Z
   *)
  | ThreeLeftHole23 : A -> tree -> A -> tree -> context -> context 
  (*                               C
   * ThreeMiddleHole X a b Z C =   |
   *                             [a][b]
   *                            /  |  \
   *                           X   ?   Z
   *)
  | ThreeMiddleHole23 : tree -> A -> A -> tree -> context -> context
  (*                              C
   * ThreeRightHole X a Y b C =   |
   *                            [a][b]
   *                           /  |  \
   *                          X   Y   ?
   *)
  | ThreeRightHole23 : tree -> A -> tree -> A -> context -> context
  .

  (* zip takes a context (which can be thought of as a tree with a hole), and a
   * subtree, and fills the hole with the subtree
   *)
  Fixpoint zip23 (t:tree) (c:context) : tree :=
  match c with
  | Top_c => t
  | TwoLeftHole_c p r c' => zip23 (Two_t t p r) c'
  | TwoRightHole_c l p c' => zip23 (Two_t l p t) c'
  | ThreeLeftHole23 lp m rp r c' => zip23 (Three_t t lp m rp r) c'
  | ThreeMiddleHole23 l lp rp r c' => zip23 (Three_t l lp t rp r) c'
  | ThreeRightHole23 l lp m rp c' => zip23 (Three_t l lp m rp t) c'
  end.

  Fixpoint context_wf (c:context) : Prop :=
  exists n:nat, forall t:tree, tree_wf t -> height_t t = n -> tree_wf (zip23 t c).

  (* if insertion results in a subtree which is too tall, propegate it up into
   * its context.
   *)
  Fixpoint insertUp23 (tpt:tree * A * tree) (c:context) : tree :=
  let '(l,p,r) := tpt in
  match c with
  (*       _              [p]
   *       |              / \
   *      [p]      =>    l   r
   *     // \\
   *     l   r
   *)
  | Top_c => Two_t l p r
  (*           c'             c'
   *           |              |
   *          [p']    =>    [p][p']
   *          /  \          /  |  \
   *        [p]   r'       l   r   r'
   *       // \\
   *       l   r
   *)
  | TwoLeftHole_c  p' r' c' => zip23 (Three_t l p r p' r') c'
  (*           c'             c'
   *           |              |
   *          [p']    =>    [p'][p]
   *          /  \          /  |  \
   *         l'  [p]       l'  l   r
   *            // \\
   *            l   r
   *)
  | TwoRightHole_c  l' p' c' => zip23 (Three_t  l' p' l p r ) c'
  (*           c'               c'
   *           |                |
   *        [lp][rp]    =>    [lp]
   *        /  |  \          //  \\
   *      [p]  m   r'      [p]    [rp]
   *     // \\             / \     / \
   *     l   r            l   r   m   r'
   *)
  | ThreeLeftHole23 lp m rp r' c' => insertUp23 (Two_t l p r, lp, Two_t m rp r') c'
  (*           c'               c'
   *           |                |
   *        [lp][rp]    =>     [p]
   *        /  |  \           //  \\
   *       l' [p]  r'       [lp]   [rp]
   *         // \\          / \     / \
   *         l   r         l'  l   r   r'
   *)
  | ThreeMiddleHole23 l' lp rp r' c' => insertUp23 (Two_t l' lp l, p, Two_t r rp r') c'
  (*           c'               c'
   *           |                |
   *        [lp][rp]    =>    [rp]
   *        /  |  \          //  \\
   *       l'  m  [p]      [lp]   [p]
   *             // \\     / \    / \
   *             l   r    l'  m  l   r
   *)
  | ThreeRightHole23 l' lp m rp c' => insertUp23 (Two_t l' lp m, rp, Two_t l p r) c'
  end.

  (* insert an element into the two-three tree *)
  Fixpoint insert23 (k:A) (t:tree) (c:context) : tree :=
  match t with
  | Null_t => insertUp23 (Null_t, k, Null_t) c
  | Two_t l k' r =>
      match compareo k k' with
      | Less => insert23 k l (TwoLeftHole_c k' r c)
      | Equal => zip23 (Two_t l k' r) c
      | Greater => insert23 k r (TwoRightHole_c l k' c)
      end
  | Three_t l lk m rk r =>
      match compareo k lk, compareo k rk with
      | Less, _ => insert23 k l (ThreeLeftHole23 lk m rk r c)
      | Equal, _ => zip23 (Three_t l lk m rk r) c
      | Greater, Less => insert23 k m (ThreeMiddleHole23 l lk rk r c)
      | _, Equal => zip23 (Three_t l lk m rk r) c
      | _, Greater => insert23 k r (ThreeRightHole23 l lk m rk c)
      end
  end.

  (* if remove results in a tree which is too short, propegate the gap into the
   * context *)
  Fixpoint removeUp23 (t:tree) (c:context) : option tree :=
  match c with
  | Top_c => Some t
  | TwoLeftHole_c _ Null_t _ => None
  | TwoLeftHole_c p (Two_t l' p' r') c' =>
      removeUp23 (Three_t t p l' p' r') c'
  | TwoLeftHole_c p (Three_t l' lp' m' rp' r') c' =>
      Some (zip23 (Two_t (Two_t t p l') lp' (Two_t m' rp' r')) c')
  | TwoRightHole_c (Two_t l' p' r') p c' =>
      removeUp23 (Three_t l' p' r' p t) c'
  | TwoRightHole_c (Three_t l' lp' m' rp' r') p c' =>
      Some (zip23 (Two_t (Two_t  l' lp' m') rp' (Two_t r' p t)) c')
  | ThreeLeftHole23  lp (Two_t l' p' r') rp r c' =>
      Some (zip23 (Two_t (Three_t t lp l' p' r') rp r) c')
  | ThreeMiddleHole23 (Two_t l' p' r') lp rp r c' =>
      Some (zip23 (Two_t (Three_t l' p' r' lp t) rp r) c')
  | ThreeMiddleHole23 l lp rp (Two_t l' p' r') c' =>
      Some (zip23 (Two_t l lp (Three_t t rp l' p' r')) c')
  | ThreeRightHole23 l lp (Two_t l' p' r') rp c' =>
      Some (zip23 (Two_t l lp (Three_t l' p' r' rp t)) c')
  | ThreeLeftHole23  lp (Three_t l' lp' m' rp' r') rp r c' =>
      Some (zip23 (Three_t (Two_t t lp l') lp' (Two_t m' rp' r') rp r) c')
  | ThreeMiddleHole23 (Three_t l' lp' m' rp' r') lp rp r c' =>
      Some (zip23 (Three_t (Two_t l' lp' m') rp' (Two_t r' lp t) rp r) c')
  | ThreeMiddleHole23 l lp rp (Three_t l' lp' m' rp' r') c' =>
      Some (zip23 (Three_t l lp (Two_t t rp l') lp' (Two_t m' rp' r')) c')
  | ThreeRightHole23 l lp (Three_t l' lp' m' rp' r') rp c' =>
      Some (zip23 (Three_t l lp (Two_t l' lp' m') rp' (Two_t r' rp t)) c')
  | TwoRightHole_c Null_t _ _ => None
  | ThreeLeftHole23 _ Null_t _ _ _ => None
  | ThreeMiddleHole23 Null_t _ _ _ _ => None
  | ThreeRightHole23 _ _ Null_t _ _ => None
  end.

  (* remove an element from the two-three tree *)
  Fixpoint remove23 (k:A) (t:tree) (c:context) : option tree :=
  (* removes the greatest element in a tree and if it results in a tree which is
   * too short it propegats the gap into a provided context
   *)
  let removeGreatest23 :=
  fix removeGreatest23 (t:tree) (k:A -> context) : option tree :=
    match t with
    | Two_t l p r  => 
        match l with
        | Null_t => (* (assert (r = Null_t) ; *) removeUp23 Null_t (k p)
        | _ => removeGreatest23 r (fun p' => TwoRightHole_c l p (k p'))
        end
    | Three_t l lp m rp r =>
        match l with
        | Null_t => (* (assert (m = Null_t) ; assert (r = Null_t) ; *)
            Some (zip23 (Two_t Null_t lp Null_t) (k rp))
        | _ => removeGreatest23 r (fun p' => ThreeRightHole23 l lp m rp (k p'))
        end
    | Null_t => None
    end
  in
  match t with
  | Null_t => Some (zip23 Null_t c)
  | Two_t l k' r =>
      match compareo k k' with
      | Less => remove23 k l (TwoLeftHole_c k' r c )
      | Equal =>
          match removeGreatest23 l (fun p => TwoLeftHole_c p r c) with
          | None => (* assert (r = Null_t) ; *) removeUp23 Null_t c
          | Some t => Some t
          end
      | Greater => remove23 k r (TwoRightHole_c l k' c)
      end
  | Three_t l lk m rk r =>
    match compareo k lk,compareo k rk with
    | Less, _ => remove23 k l (ThreeLeftHole23 lk m rk r c)
    | Equal, _ =>
        match removeGreatest23 l (fun p => ThreeLeftHole23 p m rk r c) with
        | None => (* assert (m = Null_t) ; assert (r = Null_t) ; *) Some (zip23 (Two_t Null_t rk Null_t) c)
        | Some t => Some t
        end
    | Greater, Less => remove23 k m (ThreeMiddleHole23 l lk rk r c)
    | _, Equal =>
        match removeGreatest23 m (fun p => ThreeMiddleHole23 l lk p r c) with
        | None => (* assert (l = Null_t) ; assert (r = Null_t) ; *) Some (zip23 (Two_t Null_t lk Null_t) c)
        | Some t => Some (t)
        end
    | _, Greater => remove23 k r (ThreeRightHole23 l lk m rk c)
    end
  end.

End tree.

