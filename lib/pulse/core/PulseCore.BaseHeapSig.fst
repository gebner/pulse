module PulseCore.BaseHeapSig
module H = PulseCore.Heap
module H2 = PulseCore.Heap2
open PulseCore.HeapSig

noeq
type mem : Type u#(a + 1) = {
    heap: H2.heap u#a;
    ctr: nat;
    ghost_ctr: erased nat
}

let lens_core : lens (mem u#a) (H2.heap u#a) = {
    get = (fun s -> s.heap);
    put = (fun v s -> {s with heap = v});
    get_put = (fun m -> ());
    put_get = (fun c m -> ());
    put_put = (fun c1 c2 m -> ())
}

let sep : separable (mem u#a) = {
    core = H2.heap u#a;
    lens_core = lens_core;
    empty = H2.empty_heap;
    disjoint = H2.disjoint;
    join = H2.join;
    disjoint_sym = H2.disjoint_sym;
    join_commutative = (fun h0 h1 -> H2.join_commutative h0 h1); 
    disjoint_join = H2.disjoint_join;
    join_associative = (fun h0 h1 h2 -> H2.join_associative h0 h1 h2);
    join_empty = H2.join_empty;
}

let full_mem_pred m = H2.full_heap_pred m.heap

let is_ghost_action m0 m1 : prop =
  m0.ctr == m1.ctr /\
  H2.concrete m0.heap == H2.concrete m1.heap

let slprop = H2.slprop
let interp (p:H2.slprop) : affine_mem_prop sep =
  H2.interp_depends_only_on p;
  fun h -> H2.interp p h
let as_slprop (p:affine_mem_prop sep)
: H2.slprop
= assert (forall m0 m1. H2.disjoint m0 m1 == sep.disjoint m0 m1);
  H2.as_slprop p

[@@erasable]
noeq
type uunit : Type u#a = | UU
let bprop : Type u#a = uunit
let up (b:bprop) = H2.emp
let down (p:slprop) : bprop = UU
let up_down (p:bprop) : Lemma (down (up p) == p) = ()

let emp : slprop = H2.emp
let pure (p:prop) : slprop = H2.pure p
let star (p1:slprop) (p2:slprop) : slprop = H2.star p1 p2
let star_equiv (p q:H2.slprop) (m:H2.heap)
: Lemma (
    interp (p `H2.star` q) m <==> 
        (exists m0 m1. 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  )
= introduce  
    interp (p `H2.star` q) m ==> 
        (exists m0 m1. {:pattern (H2.disjoint m0 m1)} 
          sep.disjoint m0 m1 /\
          m == sep.join m0 m1 /\
          interp p m0 /\
          interp q m1)
  with _ . (
    H2.elim_star p q m
  );
  introduce
        (exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1) ==>
    H2.interp (p `H2.star` q) m
  with _ . (
      eliminate exists m0 m1. 
          H2.disjoint m0 m1 /\
          m == H2.join m0 m1 /\
          H2.interp p m0 /\
          H2.interp q m1
      returns _ 
      with _ . (
          H2.intro_star p q m0 m1
      )
  )

let slprop_extensionality (p q:H2.slprop)
: Lemma ((forall c. interp p c <==> interp q c) ==> p == q)
        [SMTPat (H2.equiv p q)]
= introduce (forall c. interp p c <==> interp q c) ==> p == q
  with _ . (
    assert (forall p c. interp p c == H2.interp p c);
    H2.slprop_extensionality p q
  )

let interp_as (p:affine_mem_prop sep)
: Lemma (forall c. interp (as_slprop p) c == p c)
= introduce forall c. interp (as_slprop p) c == p c
  with (
    assert (forall m0 m1. H2.disjoint m0 m1 == sep.disjoint m0 m1);
    assert (interp (as_slprop p) c <==> H2.interp (H2.as_slprop p) c);
    assert (H2.interp (H2.as_slprop p) c <==> p c);
    FStar.PropositionalExtensionality.apply (interp (as_slprop p) c) (p c)
  )

let free_above (m:mem u#a) = forall i. i >= m.ghost_ctr ==> None? (H2.select_ghost i m.heap)
let mem_invariant (is:eset unit) (m:mem u#a)
: slprop u#a
= pure (free_above m)

let dup_pure (p:prop)
: Lemma (pure p == pure p `H2.star` pure p)
= FStar.Classical.forall_intro (star_equiv (pure p) (pure p));
  FStar.Classical.forall_intro (H2.pure_interp p);
  FStar.Classical.forall_intro sep.join_empty ;
  slprop_extensionality (pure p) (pure p `star` pure p)

let iname_of (i:unit) = i
let inv (i:unit) (p:slprop) = pure (p == H2.emp)
let inv_extract (i:unit) (p:slprop)
: Lemma (inv i p == p `star` inv i p)
= introduce forall m. interp (inv i p) m ==> interp (p `star` inv i p) m
  with introduce _ ==> _
  with _ . ( 
    H2.pure_interp (p == H2.emp) m;
    H2.emp_unit (inv i p);
    H2.star_commutative p (inv i p)
  );
  introduce forall m. interp (p `star` inv i p) m ==> interp (inv i p) m
  with introduce _ ==> _
  with _ . (
    H2.affine_star p (inv i p) m
  );
  assert (H2.equiv (inv i p) (p `star` inv i p))
  
let mem_invariant_equiv (e:eset unit) (m:mem u#a) (i:unit) (p:slprop u#a)
: Lemma 
  (requires
    not (iname_of i `Set.mem` e))
  (ensures
    mem_invariant e m `star` inv i p ==
    mem_invariant (Set.add (iname_of i) e) m `star` p `star` inv i p)
= calc (==) {
    mem_invariant e m `star` inv i p;
  (==) { inv_extract i p }
   mem_invariant (Set.add (iname_of i) e) m `star` (p `star` inv i p);
  (==) { H2.star_associative (mem_invariant (Set.add (iname_of i) e) m) p (inv i p) }
   mem_invariant (Set.add (iname_of i) e) m `star` p `star` inv i p;
  }

let dup_inv_equiv (i:unit) (p:slprop)
: Lemma (inv i p == inv i p `H2.star` inv i p)
= dup_pure (p == H2.emp)

let base_heap : heap_sig u#a =
  {
    mem;
    sep;
    full_mem_pred;
    is_ghost_action;
    is_ghost_action_preorder= (fun _ -> ());
    slprop;
    interp;
    as_slprop;
    interp_as;
    slprop_extensionality;
    non_info_slprop = (fun x -> reveal x);
    bprop;
    non_info_bprop = (fun x -> reveal x);
    up;
    down;
    up_down;
    emp=H2.emp;
    pure=H2.pure;
    star=H2.star;
    intro_emp=H2.intro_emp;
    pure_interp=(fun p c -> H2.pure_interp p c; FStar.PropositionalExtensionality.apply (interp (pure p) c) p);
    pure_true_emp = (fun () -> 
      FStar.Classical.forall_intro (H2.pure_interp True);
      FStar.Classical.forall_intro H2.intro_emp;
      assert (H2.equiv (H2.pure True) H2.emp));
    emp_unit=(fun p -> H2.emp_unit p);
    star_commutative=H2.star_commutative;
    star_associative=H2.star_associative;
    star_equiv;
    pts_to=H2.pts_to;
    ghost_pts_to=H2.ghost_pts_to;
    iname = unit;
    iref = unit;
    iref_erasable = (fun x -> reveal x);
    iname_of = (fun x -> ());
    inv;
    iname_ok = (fun _ _ -> True);
    dup_inv_equiv;
    mem_invariant;
    inv_iname_ok = (fun _ _ _ -> ());
    mem_invariant_equiv;
}

let core_ghost_ref_as_addr (r:core_ghost_ref)
: GTot nat
= H2.core_ghost_ref_as_addr r

let select_ghost i m = H2.select_ghost i m
let ghost_ctr m = m.ghost_ctr
let mem_invariant_interp (ex:inames base_heap) (h:base_heap.mem)
: Lemma (interpret (base_heap.mem_invariant ex h) h <==>
         (forall addr.
            addr >= ghost_ctr h ==>
            None? (select_ghost addr (core_of h))))
= base_heap.pure_interp (free_above h) h.heap
let inames_ok_trivial (ex:inames base_heap) (h:base_heap.mem)
: Lemma (inames_ok ex h)
= ()
let interp_ghost_pts_to i #meta #a #pcm v h0 = H2.interp_ghost_pts_to i #meta #a #pcm v h0.heap
let ghost_pts_to_compatible_equiv = H2.ghost_pts_to_compatible_equiv

(* Lifting H2 actions *)
let mg_of_mut (m:Tags.mutability) =
  match m with
  | Tags.MUTABLE -> false
  | _ -> true

assume
val lift_heap_action
      (#fp:H2.slprop u#a)
      (#a:Type u#b)
      (#fp':a -> H2.slprop u#a)
      (#mut:_)
      (e:inames base_heap)
      ($f:H2.action #mut #None fp a fp')
: _action_except base_heap a (mg_of_mut mut) e fp fp'

let ghost_extend meta #ex #a #pcm x = admit()
let ghost_extend_spec
      (#meta:bool)
      (#ex:inames base_heap)
      #a #pcm (x:a { pcm.refine x })
      (frame:base_heap.slprop)
      (h:full_mem base_heap { 
        inames_ok ex h /\
        interpret (base_heap.emp `base_heap.star`
                   frame `base_heap.star`
                   base_heap.mem_invariant ex h) h })      
= admit()

let ghost_read #ex #meta #a #p r x f = lift_heap_action ex (H2.ghost_read #meta #a #p r x f)
let ghost_write #ex #meta #a #p r x y f = lift_heap_action ex (H2.ghost_write #meta #a #p r x y f)
let ghost_share #ex #meta #a #p r x y = lift_heap_action ex (H2.ghost_share #meta #a #p r x y)
let ghost_gather #ex #meta #a #p r x y = lift_heap_action ex (H2.ghost_gather #meta #a #p r x y)

let extend #ex #a #pcm x = admit()
let read #ex #a #p r x f = lift_heap_action ex (H2.select_refine #a #p r x f)
let write #ex #a #p r x y f = lift_heap_action ex (H2.upd_gen_action #a #p r x y f)
let share #ex #a #p r x y = lift_heap_action ex (H2.split_action #a #p r x y)
let gather #ex #a #p r x y = lift_heap_action ex (H2.gather_action #a #p r x y)
let pts_to_not_null_action #ex #a #p r x = lift_heap_action ex (H2.pts_to_not_null_action #a #p r x)