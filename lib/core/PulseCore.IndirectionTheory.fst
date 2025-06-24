(*
   Copyright 2024 Microsoft Research

   Licensed under the Apache License, Version 2.0 (the "License");
   you may not use this file except in compliance with the License.
   You may obtain a copy of the License at

       http://www.apache.org/licenses/LICENSE-2.0

   Unless required by applicable law or agreed to in writing, software
   distributed under the License is distributed on an "AS IS" BASIS,
   WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
   See the License for the specific language governing permissions and
   limitations under the License.
*)

module PulseCore.IndirectionTheory

let pred' #f (ff: functor u#a f) (n: nat) (knot_t: (m:nat {m<n} -> Type u#(a+1))) : Type u#(a+1) =
  restricted_t (m:nat {m<n}) fun m -> knot_t m ^-> prop

let f_ext #t #s (f g: restricted_t t s) (h: (x:t -> squash (f x == g x))) : squash (f == g) =
  introduce forall x. f x == g x with h x; extensionality _ _ f g

irreducible let irred_true : b:bool{b} = true // gadget to control unfolding

let rec k' #f (ff: functor u#a f) : nat -> Type u#(a+1) =
  fun n -> if irred_true then f (pred' ff n (k' ff)) else (assert False; Type u#a)

let k'_eq #f (ff: functor u#a f) (n: nat) : squash (k' ff n == f (pred' ff n (k' ff))) = ()

let k'_unfold #f (#ff: functor u#a f) (#n: Ghost.erased nat) (x: k' ff n) : f (pred' ff n (k' ff)) =
  k'_eq ff n; x

let k'_fold #f (#ff: functor u#a f) (#n: Ghost.erased nat) (x: f (pred' ff n (k' ff))) : k' ff n =
  k'_eq ff n; x

type punit : Type u#a = | PUnit
let const #a #b (x: b) : (a ^-> b) = on_dom _ fun _ -> x
let shape #f (ff: functor f) #a (x: f a) : f punit =
  ff.fmap (const PUnit) x

type pred'' #f (ff: functor u#a f) =
  restricted_t nat fun m -> k' ff m ^-> prop
type knot_t #f (ff: functor u#a f) =
  f (pred'' ff)

let approx_pred' #f (#ff: functor u#a f) n : (pred'' ff ^-> pred' ff n (k' ff)) =
  on_dom (pred'' ff) fun p -> on_dom (m:nat { m < n }) fun m -> on_dom _ fun x -> p m x

let extend_pred' #f (#ff: functor u#a f) n : (pred' ff n (k' ff) ^-> pred'' ff) =
  on_dom (pred' ff n (k' ff)) #(fun _ -> pred'' ff) fun p ->
  on_dom nat #(fun m -> k' ff m ^-> prop) fun m ->
  on_dom (k' ff m) #(fun _ -> prop) fun y ->
  if m < n then p m y else False

let approx_extend_pred' #f (#ff: functor f) n (p: pred' ff n (k' ff)) =
  f_ext (approx_pred' n (extend_pred' n p)) p fun m ->
  f_ext (approx_pred' n (extend_pred' n p) m) (p m) fun x ->
  assert_norm (approx_pred' n (extend_pred' n p) m x == (if m < n then p m x else False))

let extend' #f (#ff: functor u#a f) n (x: k' ff n) : knot_t ff =
  ff.fmap (extend_pred' n) (k'_unfold x)

let approx' #f (#ff: functor u#a f) n (k: knot_t ff) : k' ff n =
  k'_fold (ff.fmap (approx_pred' n) k)

let approx_extend' #f (#ff: functor u#a f) n (x: k' ff n) : Lemma (approx' n (extend' n x) == x) =
  let x = k'_unfold x in
  ff.fmap_id _ x;
  ff.fmap_comp _ _ _ (approx_pred' #f #ff n) (extend_pred' #f #ff n);
  assert approx' n (extend' #f #ff n x) ==
    ff.fmap (compose (approx_pred' #f #ff n) (extend_pred' #f #ff n)) x;
  f_ext (compose (approx_pred' #f #ff n) (extend_pred' n)) id (approx_extend_pred' n)

let extend_approx_pred' #f (#ff: functor u#a f) (n: nat) : (pred'' ff ^-> pred'' ff) =
  on_dom (pred'' ff) #(fun _ -> pred'' ff) fun p ->
  on_dom nat #(fun m -> k' ff m ^-> prop) fun m ->
  on_dom (k' ff m) #(fun _ -> prop) fun y ->
  if m < n then p m y else False

let approx_knot #f (#ff: functor u#a f) (n: nat) (x: knot_t ff) : knot_t ff =
  ff.fmap (extend_approx_pred' n) x

let extend_approx' #f (#ff: functor u#a f) n (x: knot_t ff) :
    Lemma (extend' n (approx' n x) == approx_knot n x) =
  ff.fmap_id _ x;
  ff.fmap_comp _ _ _ (extend_pred' #f #ff n) (approx_pred' #f #ff n);
  assert extend' n (approx' #f #ff n x) ==
    ff.fmap (compose (extend_pred' #f #ff n) (approx_pred' #f #ff n)) x;
  f_ext (compose (extend_pred' #f #ff n) (approx_pred' n)) (extend_approx_pred' n) fun p ->
  f_ext (extend_pred' n (approx_pred' n p)) (extend_approx_pred' n p) fun m ->
  f_ext (extend_pred' n (approx_pred' n p) m) (extend_approx_pred' n p m) fun x ->
  ()

let pack_pred #f (#ff: functor u#a f) : (predicate ff ^-> pred'' ff) =
  on_dom (predicate ff) fun p -> on_dom nat fun m ->
    on_dom (k' ff m) #(fun _ -> prop) fun x -> p m (extend' m x)

let unpack_pred #f (#ff: functor u#a f) : (pred'' ff ^-> predicate ff) =
  on_dom (pred'' ff) fun p -> on_dom nat fun i -> on_dom (knot_t ff) fun y -> p i (approx' i y)

let pack_unpack_pred #f (ff: functor u#a f) (x: pred'' ff) =
  f_ext (pack_pred (unpack_pred x)) x fun m ->
  f_ext (pack_pred (unpack_pred x) m) (x m) fun x ->
  approx_extend' m x

let pack #f #ff = ff.fmap pack_pred
let unpack #f #ff = ff.fmap unpack_pred

// let unpack_pack_pred #f (#ff: functor u#a f) (n:nat) (x: predicate ff) =
//   f_ext ((unpack_pred n (pack_pred n x))) (approx n x) fun _ -> ()

let pack_unpack #f #ff x =
  ff.fmap_comp (pred'' ff) _ (pred'' ff) pack_pred unpack_pred;
  f_ext (compose pack_pred (unpack_pred #f #ff)) id (pack_unpack_pred ff);
  ff.fmap_id _ x;
  assert ff.fmap id x == x

// let unpack_pack #f #ff n h =
//   ff.fmap_comp _ _ _ (unpack_pred n) (pack_pred #f #ff n);
//   f_ext (compose (unpack_pred n) (pack_pred #f #ff n)) (approx n) fun x -> unpack_pack_pred n x
