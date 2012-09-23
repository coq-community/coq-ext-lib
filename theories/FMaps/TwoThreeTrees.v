Set Implicit Arguments.
Set Maximal Implicit Insertion.

Inductive order := Less | Equal | Greater.

(* a two-three tree *)
Inductive tree23 K V :=
| Null23 : tree23 K V
| Two23 : tree23 K V -> K * V -> tree23 K V -> tree23 K V
| Three23 : tree23 K V -> K * V -> tree23 K V -> K * V -> tree23 K V -> tree23 K V
.
Arguments Null23 {K} {V}.

(* a context of a two-three tree. this is the type of taking a tree and
 * replacing a sub-tree with a hole.
 *)
Inductive context23 K V :=
| Top23 : context23 K V
| TwoLeftHole23 : K * V -> tree23 K V -> context23 K V -> context23 K V
| TwoRightHole23 : tree23 K V -> K * V -> context23 K V -> context23 K V
| ThreeLeftHole23 : K * V -> tree23 K V -> K * V -> tree23 K V -> context23 K V -> context23 K V
| ThreeMiddleHole23 : tree23 K V -> K * V -> K * V -> tree23 K V -> context23 K V -> context23 K V
| ThreeRightHole23 : tree23 K V -> K * V -> tree23 K V -> K * V -> context23 K V -> context23 K V
.

(* zip takes a context (which can be thought of as a tree with a hole), and a
 * subtree, and fills the hole with the subtree
 *)
Fixpoint zip23 {K V} (t:tree23 K V) (c:context23 K V) : tree23 K V :=
match c with
| Top23 => t
| TwoLeftHole23 p r c' => zip23 (Two23 t p r) c'
| TwoRightHole23 l p c' => zip23 (Two23 l p t) c'
| ThreeLeftHole23 lp m rp r c' => zip23 (Three23 t lp m rp r) c'
| ThreeMiddleHole23 l lp rp r c' => zip23 (Three23 l lp t rp r) c'
| ThreeRightHole23 l lp m rp c' => zip23 (Three23 l lp m rp t) c'
end.


Section ordered.
  Variable (K:Type) (V:Type).
  Variable compareo : K -> K -> order.

  (* insert an element into the two-three tree *)
  Fixpoint insert23 (p:K * V) (t:tree23 K V) (c:context23 K V) : tree23 K V :=
  (* if insertion results in a subtree which is too tall, propegate it up into
   * its context
   *)
  let insertUp23 :=
    fix insertUp23
        (tpt:tree23 K V * (K * V) * tree23 K V) (c:context23 K V) : tree23 K V:=
      let '(l,p,r) := tpt in
      match c with
      | Top23 => Two23 l p r
      | TwoLeftHole23  p' r' c' => zip23 (Three23 l p r p' r') c'
      | TwoRightHole23  l' p' c' => zip23 (Three23  l' p' l p r ) c'
      | ThreeLeftHole23 lp m rp r' c' =>
          insertUp23 (Two23 l p r, lp, Two23 m rp r') c'
      | ThreeMiddleHole23 l' lp rp r' c' =>
          insertUp23 (Two23 l' lp l, p, Two23 r rp r') c'
      | ThreeRightHole23 l' lp m rp c' =>
          insertUp23 (Two23 l' lp m, rp, Two23 l p r) c'
      end
  in
  let (k,v) := p in
  match t with
  | Null23 => insertUp23 (Null23, p, Null23) c
  | Two23 l p' r =>
      let (k',v') := p' in
      match compareo k k' with
      | Less => insert23 p l (TwoLeftHole23 p' r c)
      | Equal => zip23 (Two23 l (k',v) r) c
      | Greater => insert23 p r (TwoRightHole23 l p' c)
      end
  | Three23 l lp m rp r =>
      let '((lk,lv),(rk,rv)) := (lp,rp) in
      match compareo k lk, compareo k rk with
      | Less, _ => insert23 p l (ThreeLeftHole23 lp m rp r c)
      | Equal, _ => zip23 (Three23 l (lk,v) m rp r) c
      | Greater, Less => insert23 p m (ThreeMiddleHole23 l lp rp r c)
      | _, Equal => zip23 (Three23 l lp m (rk,v) r) c
      | _, Greater => insert23 p r (ThreeRightHole23 l lp m rp c)
      end
  end.

  Axiom impossible : forall {A}, A.

  (* remove an element from the two-three tree *)
  Fixpoint remove23 (k:K) (t:tree23 K V) (c:context23 K V) : tree23 K V :=
  (* if remove results in a tree which is too short, propegate the gap into the
   * context *)
  let removeUp23 :=
    fix removeUp23 (t:tree23 K V) (c:context23 K V) : tree23 K V :=
    match c with
    | Top23 => t
    | TwoLeftHole23 p (Two23 l' p' r') c' =>
        removeUp23 (Three23 t p l' p' r') c'
    | TwoRightHole23 (Two23 l' p' r') p c' =>
        removeUp23 (Three23 l' p' r' p t) c'
    | TwoLeftHole23 p (Three23 l' lp' m' rp' r') c' =>
        zip23 (Two23 (Two23 t p l') lp' (Two23 m' rp' r')) c'
    | TwoRightHole23 (Three23 l' lp' m' rp' r') p c' =>
        zip23 (Two23 (Two23  l' lp' m') rp' (Two23 r' p t)) c'
    | ThreeLeftHole23  lp (Two23 l' p' r') rp r c' =>
        zip23 (Two23 (Three23 t lp l' p' r') rp r) c'
    | ThreeMiddleHole23 (Two23 l' p' r') lp rp r c' =>
        zip23 (Two23 (Three23 l' p' r' lp t) rp r) c'
    | ThreeMiddleHole23 l lp rp (Two23 l' p' r') c' =>
        zip23 (Two23 l lp (Three23 t rp l' p' r')) c'
    | ThreeRightHole23 l lp (Two23 l' p' r') rp c' =>
        zip23 (Two23 l lp (Three23 l' p' r' rp t)) c'
    | ThreeLeftHole23  lp (Three23 l' lp' m' rp' r') rp r c' =>
        zip23 (Three23 (Two23 t lp l') lp' (Two23 m' rp' r') rp r) c'
    | ThreeMiddleHole23 (Three23 l' lp' m' rp' r') lp rp r c' =>
        zip23 (Three23 (Two23 l' lp' m') rp' (Two23 r' lp t) rp r) c'
    | ThreeMiddleHole23 l lp rp (Three23 l' lp' m' rp' r') c' =>
        zip23 (Three23 l lp (Two23 t rp l') lp' (Two23 m' rp' r')) c'
    | ThreeRightHole23 l lp (Three23 l' lp' m' rp' r') rp c' =>
        zip23 (Three23 l lp (Two23 l' lp' m') rp' (Two23 r' rp t)) c'
    | TwoLeftHole23 _ Null23 _ => impossible
    | TwoRightHole23 Null23 _ _ => impossible
    | ThreeLeftHole23 _ Null23 _ _ _ => impossible
    | ThreeMiddleHole23 Null23 _ _ _ _ => impossible
    | ThreeRightHole23 _ _ Null23 _ _ => impossible
    end
  in
  (* removes the greatest element in a tree and if it results in a tree which is
   * too short it propegats the gap into a provided context
   *)
  let removeGreatest23 :=
    fix removeGreatest23
      (t:tree23 K V) (k:(K * V) -> context23 K V) : option (tree23 K V) :=
    match t with
    | Two23 l p r  => 
        match l with
        | Null23 => (* (assert (r = Null) ; *)
            Some (removeUp23 Null23 (k p))
        | _ => removeGreatest23 r (fun p' => TwoRightHole23 l p (k p'))
        end
    | Three23 l lp m rp r =>
        match l with
        | Null23 => (* (assert (m = Null) ; assert (r = Null) ; *)
            Some (zip23 (Two23 Null23 lp Null23) (k rp))
        | _ => removeGreatest23 r (fun p' => ThreeRightHole23 l lp m rp (k p'))
        end
    | Null23 => None
    end
  in
  match t with
  | Null23 => zip23 Null23 c
  | Two23 l (k',v) r =>
      match compareo k k' with
      | Less => remove23 k l (TwoLeftHole23 (k',v) r c )
      | Equal =>
          match removeGreatest23 l (fun p => TwoLeftHole23 p r c) with
          | None => (* assert (r = Null) ; *) removeUp23 Null23 c
          | Some t => t
          end
      | Greater => remove23 k r (TwoRightHole23 l (k',v) c)
      end
  | Three23 l (lk,lv) m (rk,rv) r =>
    match compareo k lk,compareo k rk with
    | Less, _ => remove23 k l (ThreeLeftHole23 (lk,lv) m (rk,rv) r c)
    | Equal, _ =>
        match removeGreatest23 l (fun p => ThreeLeftHole23 p m (rk,rv) r c) with
        | None => (* assert (m = Null) ; assert (r = Null) ; *)
            zip23 (Two23 Null23 (rk,rv) Null23) c
        | Some t => t
        end
    | Greater, Less => remove23 k m (ThreeMiddleHole23 l (lk,lv) (rk,rv) r c)
    | _, Equal =>
        match removeGreatest23 m (fun p => ThreeMiddleHole23 l (lk, lv) p r c) with
        | None => (* assert (l = Null) ; assert (r = Null) ; *)
            zip23 (Two23 Null23 (lk,lv) Null23) c
        | Some t => t
        end
    | _, Greater => remove23 k r (ThreeRightHole23 l (lk,lv) m (rk,rv) c)
    end
  end.
  
End ordered.

