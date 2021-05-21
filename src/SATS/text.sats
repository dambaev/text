#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text"
#include "share/atspre_staload.hats" // include template definitions

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"
staload "{$LIBS}/result/src/SATS/result.sats"

(* text datatype defines UTF-8 encoded string with backing store as bytestring 
*)
vtypedef
  Text_vtype
  ( len: int (* codepoints count *)
  , bs_len: int (* bytes count *)
  , bs_offset: int
  , bs_cap: int
  , bs_ucap: int
  , bs_refcnt: int
  , bs_dynamically_allocated: bool
  , bs_base: addr
  ) =
  ( size_t(len) (* codepoints count*)
  , uint8 (* Unicode type *)
  , $BS.Bytestring_vtype
    ( bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , bs_refcnt
    , bs_dynamically_allocated
    , bs_base
    )
  )

vtypedef
  Text0 =
  [len, bs_len, offset, cap, ucap, refcnt: nat][dynamic:bool][l:addr]
  Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  Text1 =
  [len, bs_len: pos][offset, cap, ucap, refcnt: nat][dynamic:bool][l:agz]
  Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  TextSH(len:int) =
  {len, bs_len: nat}[offset, cap, ucap, refcnt: nat][dynamic:bool][l:agz]
  Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  TextNSH(len:int) =
  {len, bs_len: nat}[offset, cap, ucap, refcnt: nat][dynamic:bool][l:addr]
  Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, l)

prfun
  lemma_text_param
  {len,bs_len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}
  ( v: !Text_vtype(len, bs_len, offset,cap,ucap,refcnt,dynamic,l)
  ):
  [ (bs_len >= len)
  ; ( len > 0 && l > null)
  ; ( bs_len > 0 && cap > 0)
  ; (cap > 0 && l > null)
  ; (l > null && bs_len >= 0); bs_len+offset <= cap
  ; offset+bs_len+ucap == cap
  ; (ucap == cap - offset - bs_len || ucap == 0)
  ] (* bs_len should not exceed capacity *)
  void

absview
  Text_v
  ( len: int (* codepoints count *)
  , bs_len: int (* bytes count *)
  , bs_offset: int
  , bs_cap: int
  , bs_ucap: int
  , bs_refcnt: int
  , bs_dynamically_allocated: bool
  , bs_base: addr
  )

(* this is non-consuming version of function, meaning, that i's refcnt will be increamented in case of success *)
(* time: O(n), space: O(1) *)
fn
  decode_utf80
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base) >> result_vtb
       ( result
       (* in case of success, we borrow original bytestring *)
       , $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt + 1, bs_dynamic, bs_base)
       (* otherwise, we will keep original bytestring *)
       , $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
       )
  , result: &Text0? >> result_vtb
       ( result
       ,  [len:nat]
          Text_vtype
            ( len
            , bs_len
            , bs_offset
            , bs_cap
            , bs_ucap
            , 1
            , bs_dynamic
            , bs_base
            )
       , Text0?
       )
  ):
  #[result:bool]
  bool(result)

(* this is consuming version of function, meaning, i have to be non-shared *)
(* time: O(n), space: O(1) *)
fn
  decode_utf80C
  {bs_len, bs_offset, bs_cap, bs_ucap: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, 0, bs_dynamic, bs_base)
  , result: &Text0? >> result_vtb
       ( result
       ,  [len:nat]
          Text_vtype
            ( len
            , bs_len
            , bs_offset
            , bs_cap
            , bs_ucap
            , 0
            , bs_dynamic
            , bs_base
            )
       , Text0?
       )
  ):
  #[result:bool]
  bool(result)

(* this is non-consuming version, will increase refcnt of i*)
(* time: O(n), space: O(1) *)
fn
  decode_utf81
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base) >> result_vtb
       ( result
       (* in case of success, we borrow original bytestring *)
       , $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt + 1, bs_dynamic, bs_base)
       (* otherwise, we will keep original bytestring *)
       , $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
       )
  ):
  #[result:bool]
  option_vt
    ( [len:nat]
      Text_vtype
      ( len
      , bs_len
      , bs_offset
      , bs_cap
      , bs_ucap
      , 1
      , bs_dynamic
      , bs_base
      )
    , result
    )

(* this is consuming version, which require Bytestring to be non-shared.
  In case of failure, will free the Bytestring, otherwise, it will not be able to have consume type spec.
*)
(* time: O(n), space: O(1) *)
fn
  decode_utf81C
  {bs_len, bs_offset, bs_cap, bs_ucap: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, 0, bs_dynamic, bs_base)
  ):
  Option_vt
    ( [len:nat]
      Text_vtype
      ( len
      , bs_len
      , bs_offset
      , bs_cap
      , bs_ucap
      , 0
      , bs_dynamic
      , bs_base
      )
    )

(* O(1) *)
fn
  length
  {len:int}{bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat }{bs_dynamic:bool}{bs_base:addr}
  ( i: !Text_vtype
    ( len
    , bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , bs_refcnt
    , bs_dynamic
    , bs_base
    )
  ):
  size_t( len)

(* O(1) *)
fn
  free_shared
  {len:int}{ bs_len, bs_offset, bs_cap, bs_ucap: nat}{bs_dynamic:bool}{bs_base:addr}
  {bs_len1, bs_offset1, bs_ucap1, bs_refcnt: nat | bs_refcnt > 0 }
  ( consume: Text_vtype
    ( len
    , bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , 1
    , bs_dynamic
    , bs_base
    )
  , preserve: !$BS.Bytestring_vtype
    ( bs_len1
    , bs_offset1
    , bs_cap
    , bs_ucap1
    , bs_refcnt
    , bs_dynamic
    , bs_base
    ) >> $BS.Bytestring_vtype
    ( bs_len1
    , bs_offset1
    , bs_cap
    , bs_ucap1
    , bs_refcnt - 1
    , bs_dynamic
    , bs_base
    )
  ):
  void
(* O(1) *)
fn
  free
  {len, bs_len, bs_offset, bs_cap, bs_ucap: nat}{bs_dynamic:bool}{bs_base:addr}
  ( i: Text_vtype
    ( len
    , bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , 0
    , bs_dynamic
    , bs_base
    )
  ):<!wrt>
  void

(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_t_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null]
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )

(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_tC_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null]
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_t_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null]
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_tC_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  ( l: Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null]
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )

(* returns a Text value, which is the result of appending r to the end of l into the unused memory of l's buffer. Such that, l is required to be heap allocated, otherwise SIGSEGV can be thrown *)
(* O(r_bs_len) *)
fn
  grow_tC_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  { l_ucap >= r_bs_len} (* l should have enough unused capacity to store r *)
  ( l: Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, true, l_p)
  , r: !Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , l_offset
    , l_cap
    , l_ucap - r_bs_len
    , l_refcnt (* refcnt*)
    , true
    , l_p
    )
(* returns a Text value, which is the result of appending r to the end of l into the unused memory of l's buffer. *)
(* O(r_bs_len) *)
fn
  grow_tC_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_p:agz}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}
  { l_ucap >= r_bs_len} (* l should have enough unused capacity to store r *)
  ( l: Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, true, l_p)
  , r: Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  Text_vtype
    ( l_len + r_len
    , l_bs_len + r_bs_len
    , l_offset
    , l_cap
    , l_ucap - r_bs_len
    , l_refcnt
    , true
    , l_p
    )

(* returns an empty Text value *)
(* see test5 for usage example *)
(* O(1) *)
fn
  empty
  (
  ):<>
  Text_vtype( 0, 0, 0, 0, 0, 0, false, null)

(* allocates in heap an empty Text value with given 'unused capacity', which can be used later with grow* functions
*)
(* see test4 for usage reference *)
(* O(ucap) *)
fn
  create
  {cap: pos}
  ( capacity: size_t(cap)
  ):<!wrt>
  [l:agz]
  Text_vtype( 0, 0, 0, cap, cap, 0, true, l)

(* returns true if given Text is empty *)
(* O(1) *)
fn
  is_empty
  {len, bs_len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}
  ( i: !Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, p)
  ):<>
  bool( len == 0)

(* returns true if given Text is not empty *)
(* O(1) *)
fn
  is_not_empty
  {len, bs_len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}
  ( i: !Text_vtype( len, bs_len, offset, cap, ucap, refcnt, dynamic, p)
  ):<>
  bool( len > 0)

(* returns true only if given Text values are the same.
   In case if given Text values are ASCII encoded, then it will compare byte-to-byte.
   WARNING: In case if given Text values are non-normalized UTF-8 values, it will perform NKD normalization before comparison, which require memory allocation. If that is an issue, you should use decoding function with normalization.
*)
(* see test5 for usage example and HATS/text_operator.hats for operator overloading *)
(* O(l_bs_len + r_bs_len) *)
fn
  eq_t_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [ r:bool | (l_len == r_len && r) || r == false]
  bool( r)
(* returns true only if given Text values are NOT the same.
   In case if given Text values are ASCII encoded, then it will compare byte-to-byte.
   WARNING: In case if given Text values are non-normalized UTF-8 values, it will perform NKD normalization before comparison, which require memory allocation. If that is an issue, you should use decoding function with normalization.
*)
(* O(l_bs_len + r_bs_len) *)
fn
  not_eq_t_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [ r:bool | (l_len == r_len && not r) || not r == false ]
  bool( r)

(* returns true only if given Text values are the same.
   In case if given Text values are ASCII encoded, then it will compare byte-to-byte.
   WARNING: In case if given Text values are non-normalized UTF-8 values, it will perform NKD normalization before comparison, which require memory allocation. If that is an issue, you should use decoding function with normalization.
*)
(* see test5 for usage example and HATS/text_operator.hats for operator overloading *)
(* O(l_bs_len + r_bs_len) *)
fn
  eq_t_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [ r:bool | (l_len == r_len && r) || r == false]
  bool( r)
(* returns true only if given Text values are NOT the same.
   In case if given Text values are ASCII encoded, then it will compare byte-to-byte.
   WARNING: In case if given Text values are non-normalized UTF-8 values, it will perform NKD normalization before comparison, which require memory allocation. If that is an issue, you should use decoding function with normalization.
*)
(* O(l_bs_len + r_bs_len) *)
fn
  not_eq_t_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}
  ( l: !Text_vtype( l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [ r:bool | (l_len == r_len && not r) || not r == false ]
  bool( r)

(* this function returns how many bytes occupies the first codepoint of bytestring *)
(* time: O(1), space: O(1) *)
fn
  bs_mb_head_bytes
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  ):
  int

