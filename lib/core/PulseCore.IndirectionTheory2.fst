module PulseCore.IndirectionTheory2
open FStar.FunctionalExtensionality

let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = on_dom a (fun x -> x)

class functor (f: Type u#(a+1) -> Type u#(a+1)) = {
  fmap: (#a:Type -> #b:Type -> (a -> b) -> f a -> f b);
  fmap_id: (a:Type -> x:f a -> squash (fmap (id #a) == id #(f a)));
  fmap_comp: (a:Type -> b:Type -> c:Type -> b2c:(b -> c) -> a2b:(a -> b) ->
    squash (compose (fmap b2c) (fmap a2b) == fmap (compose b2c a2b)));
}

let pred_t #f (ff: functor u#a f) (n: nat) (pred_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  restricted_t (m:nat {m<n}) fun m -> f (pred_t m) ^-> prop

let f_ext #t #s (f g: restricted_t t s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x; extensionality _ _ f g

let f_ext2 #t #s (#r: (x:t -> s x -> Type))
    (f g: restricted_t t (fun x -> restricted_t (s x) (r x)))
    (h: (x:t -> y:s x -> squash (f x y == g x y))) :
    squash (f == g) =
  f_ext f g fun x -> f_ext (f x) (g x) (h x)

let p_ext2 #t #s
    (f g: restricted_t t (fun x -> (s x) ^-> prop))
    (h: (x:t -> y:s x -> squash (f x y <==> g x y))) :
    squash (f == g) =
  f_ext2 f g fun x y -> h x y; PropositionalExtensionality.apply (f x y) (g x y)

unfold
let on_dom2 (a: Type) (b: a -> Type) (#c: (x:a -> b x -> Type)) (f: (x:a -> y:b x -> c x y)) :
    restricted_t a (fun y -> restricted_t (b y) (c y)) =
  on_dom a fun x -> on_dom (b x) fun y -> f x y

irreducible let irred_true : b:bool{b} = true // gadget to control unfolding

let rec pred' #f (ff: functor u#a f) : nat -> Type u#(a+1) =
  fun n -> if irred_true then pred_t ff n (pred' ff) else (assert False; Type u#a)

let pred'_eq #f (ff: functor u#a f) (n: nat) : squash (pred' ff n == pred_t ff n (pred' ff)) = ()

let pred'_unfold #f (#ff: functor u#a f) (#n: nat) (x: pred' ff n) : (pred_t ff n (pred' ff)) =
  pred'_eq ff n; x

let pred'_fold #f (#ff: functor u#a f) (#n: nat) (x: pred_t ff n (pred' ff)) : pred' ff n =
  pred'_eq ff n; x

type predicate #f (ff: functor u#a f) =
  restricted_t nat fun m -> f (pred' ff m) ^-> prop
type knot_t #f (ff: functor u#a f) =
  f (predicate ff)

let pack2 #f (#ff: functor f) n : (pred' ff n ^-> predicate ff) =
  on_dom (pred' ff n) fun p ->
  on_dom2 nat _ fun m x -> (if m < n then pred'_unfold p m x else False <: prop)

let unpack2 #f (#ff: functor f) n : (predicate ff ^-> pred' ff n) =
  on_dom (predicate ff) fun p -> pred'_fold <| on_dom2 (m:nat {m < n}) _ fun m x -> p m x

let unpack2_pack2 #f (#ff: functor f) n (p: pred' ff n) : squash (unpack2 n (pack2 n p) == p) =
  p_ext2 (pred'_unfold (unpack2 n (pack2 n p))) (pred'_unfold p) fun m x ->
    assert_norm (pred'_unfold (unpack2 n (pack2 n p)) m x <==>
      (if m < n then pred'_unfold p m x else False))

let pack #f (#ff: functor f) (p: nat -> knot_t ff -> prop) : predicate ff =
  on_dom2 nat _ fun m x -> p m (ff.fmap (pack2 m) x)

let unpack #f (#ff: functor f) (p: predicate ff) : (nat ^-> knot_t ff ^-> prop) =
  on_dom2 nat _ fun n x -> p n (ff.fmap (unpack2 n) x)

let pack_unpack #f (#ff: functor f) (p: predicate ff) : squash (pack (unpack p) == p) =
  p_ext2 (pack (unpack p)) p fun n x ->
  ff.fmap_id _ x; ff.fmap_comp _ _ _ (unpack2 n) (pack2 #f #ff n);
  assert (pack (unpack p) n x == p n (ff.fmap (compose (unpack2 n) (pack2 #f #ff n)) x));
  f_ext (compose (unpack2 n) (pack2 #f #ff n)) id fun q -> unpack2_pack2 n q

let approx #f (#ff: functor f) (n: nat) : (predicate ff ^-> predicate ff) =
  admit ()

let unpack_pack #f (#ff: functor f) (p: nat -> knot_t ff -> prop) n x :
    squash (unpack (pack p) n x <==> p n (ff.fmap (approx n) x)) =
  admit ()