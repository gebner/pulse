(*
   Copyright 2023 Microsoft Research

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

module L0Types

open Pulse.Lib.Pervasives

module V = Pulse.Lib.Vec
module A = Pulse.Lib.Array
module U8 = FStar.UInt8
module U32 = FStar.UInt32
module I32 = FStar.Int32

noeq
type character_string_t = {
  fst : U32.t;
  snd : A.array FStar.Char.char;
}

noeq
type octet_string_t = {
  len : U32.t;
  s : A.array FStar.Char.char;
}

noeq
type deviceIDCSR_ingredients_t = {
  ku        : I32.t;
  version   : I32.t;
  s_common  : character_string_t;
  s_org     : character_string_t;
  s_country : character_string_t;
}

noeq
type aliasKeyCRT_ingredients_t = {
  version       : I32.t;
  serialNumber  : octet_string_t;
  i_common      : character_string_t;
  i_org         : character_string_t;
  i_country     : character_string_t;
  notBefore     : A.array FStar.Char.char;
  notAfter      : A.array FStar.Char.char;
  s_common      : character_string_t;
  s_org         : character_string_t;
  s_country     : character_string_t;
  ku            : I32.t;
  l0_version    : I32.t;
}

val valid_hkdf_lbl_len (n:U32.t) : prop
val valid_deviceIDCSR_ingredients
  (deviceIDCSR_ingredients:deviceIDCSR_ingredients_t)
  (deviceIDCSR_len:U32.t) : prop
val valid_aliasKeyCRT_ingredients
  (aliasKeyCRT_ingredients:aliasKeyCRT_ingredients_t)
  (aliasKeyCRT_len:U32.t) : prop

noeq
type l0_record_t = {
  fwid : V.lvec U8.t 32;
  deviceID_label_len : (n:U32.t { valid_hkdf_lbl_len n });
  deviceID_label : V.lvec U8.t (U32.v deviceID_label_len);
  aliasKey_label_len : (n:U32.t { valid_hkdf_lbl_len n });
  aliasKey_label : V.lvec U8.t (U32.v aliasKey_label_len);
  deviceIDCSR_ingredients : deviceIDCSR_ingredients_t;
  aliasKeyCRT_ingredients : aliasKeyCRT_ingredients_t;
  deviceIDCSR_len : (n:U32.t { valid_deviceIDCSR_ingredients deviceIDCSR_ingredients n });
  aliasKeyCRT_len : (n:U32.t { valid_aliasKeyCRT_ingredients aliasKeyCRT_ingredients n });
}

noeq
type l0_record_repr_t = {
  fwid: Seq.seq U8.t;
  deviceID_label: Seq.seq U8.t;
  aliasKey_label: Seq.seq U8.t;
}

let mk_l0_repr fwid deviceID_label aliasKey_label
  = {fwid; deviceID_label; aliasKey_label}

let l0_record_perm (record:l0_record_t) (p:perm) (repr:l0_record_repr_t) : vprop =
  V.pts_to record.fwid #p repr.fwid **
  V.pts_to record.deviceID_label #p repr.deviceID_label **
  V.pts_to record.aliasKey_label #p repr.aliasKey_label
