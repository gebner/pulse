module Steel.SteelAtomic.Basics
open Steel.Effect
open Steel.Effect.Atomic
open Steel.Memory
open Steel.Reference
open Steel.Permissions

assume
val return_atomic (#a:Type) (#uses:Set.set lock_addr) (#p:a -> hprop) (x:a)
  : SteelAtomic a uses true (p x) p

val h_admit_atomic (#a:_) (#uses:Set.set lock_addr) (p:hprop) (q:a -> hprop)
  : SteelAtomic a uses true p q
let h_admit_atomic #a #uses p q =
  steel_admit a uses p q

val h_assert_atomic (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> p)
let h_assert_atomic #uses p = steel_assert uses p

val h_intro_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true p (fun _ -> emp `star` p)
let h_intro_emp_l #uses p =
  change_hprop p (emp `star` p) (fun m -> emp_unit p; star_commutative p emp)

val h_elim_emp_l (#uses:Set.set lock_addr) (p:hprop)
  : SteelAtomic unit uses true (emp `star` p) (fun _ -> p)
let h_elim_emp_l #uses p =
  change_hprop (emp `star` p) p (fun m -> emp_unit p; star_commutative p emp)

val h_commute (#uses:Set.set lock_addr) (p q:hprop)
  : SteelAtomic unit uses true (p `star` q) (fun _ -> q `star` p)
let h_commute #uses p q =
   change_hprop (p `star` q) (q `star` p) (fun m -> star_commutative p q)

val intro_h_exists (#a:Type) (#uses:Set.set lock_addr) (x:a) (p:a -> hprop)
  : SteelAtomic unit uses true (p x) (fun _ -> h_exists p)
let intro_h_exists #a #uses x p =
  change_hprop (p x) (h_exists p) (fun m -> intro_exists x p m)

val h_affine (#uses:Set.set lock_addr) (p q:hprop)
  : SteelAtomic unit uses true (p `star` q) (fun _ -> p)
let h_affine #uses p q =
  change_hprop (p `star` q) p (fun m -> affine_star p q m)

assume
val lift_atomic_to_steelT
  (#a:Type) (#is_ghost:bool) (#fp:hprop) (#fp':a -> hprop)
  ($f:unit -> SteelAtomic a Set.empty is_ghost fp fp')
  : SteelT a fp fp'


assume
val atomic_frame (#a:Type) (#pre:pre_t) (#post:post_t a)
          (#uses:Set.set lock_addr) (#is_ghost:bool)
          (frame:hprop)
          ($f:unit -> SteelAtomic a uses is_ghost pre post)
  : SteelAtomic a
    uses is_ghost
    (pre `star` frame)
    (fun x -> post x `star` frame)


assume
val ghost_read (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (#v:Ghost.erased a) (r:ref a)
  : SteelAtomic a uses true
    (pts_to r p v)
    (fun x -> pts_to r p x)


/// A specialized version of get_ref_refine. It should be derivable from h_exists
assume
val ghost_read_refine (#a:Type) (#uses:Set.set lock_addr) (#p:perm) (r:ref a)
  (q:a -> hprop)
  : SteelAtomic a uses true
    (h_exists (fun (v:a) -> pts_to r p v `star` q v))
    (fun v -> pts_to r p v `star` q v)

assume
val cas
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_permission v)
    (fun b -> if b then pts_to r full_permission v_new else pts_to r full_permission v)

assume
val cas_frame
  (#t:eqtype)
  (#uses:Set.set lock_addr)
  (r:ref t)
  (v:Ghost.erased t)
  (v_old:t)
  (v_new:t)
  (frame:hprop)
  : SteelAtomic
    (b:bool{b <==> (Ghost.reveal v == v_old)})
    uses
    false
    (pts_to r full_permission v `star` frame)
    (fun b -> (if b then pts_to r full_permission v_new else pts_to r full_permission v) `star` frame)
