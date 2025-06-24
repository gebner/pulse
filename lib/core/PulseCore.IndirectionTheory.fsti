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
open FStar.FunctionalExtensionality

let compose #a #b #c (f:b -> c) (g:a -> b) : (a ^-> c) = on_dom a (fun x -> f (g x))
let id #a : (a ^-> a) = on_dom a (fun x -> x)

class functor (f: Type u#(a+1) -> Type u#(a+1)) = {
  fmap: (#a:Type -> #b:Type -> (a -> b) -> f a -> f b);
  fmap_id: (a:Type -> x:f a -> squash (fmap (id #a) == id #(f a)));
  fmap_comp: (a:Type -> b:Type -> c:Type -> b2c:(b -> c) -> a2b:(a -> b) ->
    squash (compose (fmap b2c) (fmap a2b) == fmap (compose b2c a2b)));
}

val knot_t #f (ff: functor u#a f) : Type u#(a+1)
let predicate #f (ff: functor u#a f) = nat ^-> knot_t ff ^-> prop
val pack #f (#ff: functor f) : f (predicate ff) -> knot_t ff
val unpack #f (#ff: functor f) : knot_t ff -> f (predicate ff)

let approx_predicate #f (#ff: functor u#a f) (n: nat) : (predicate ff ^-> predicate ff) =
  on_dom (predicate ff) #(fun _ -> predicate ff) fun p ->
  on_dom nat #(fun _ -> knot_t ff ^-> prop) fun i ->
  on_dom _ #(fun _ -> prop) fun w ->
  if i >= n then False else p i w

let approx #f (#ff: functor u#a f) : (predicate ff ^-> predicate ff) =
  on_dom (predicate ff) #(fun _ -> predicate ff) fun p ->
  on_dom nat #(fun _ -> knot_t ff ^-> prop) fun i ->
  on_dom _ #(fun _ -> prop) fun w ->
  p i (pack (ff.fmap (approx_predicate i) (unpack w)))

val pack_unpack #f (#ff: functor f) : x:knot_t ff -> squash (pack (unpack x) == x)
val unpack_pack #f (#ff: functor f) (x: f (predicate ff)) :
  squash (unpack #f (pack x) == fmap #f (approx #f) x)
