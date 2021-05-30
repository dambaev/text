#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text"
#include "share/atspre_staload.hats" // include template definitions

#define LIBS_targetloc "../libs" (* search path for external libs *)
staload BS="{$LIBS}/ats-bytestring/SATS/bytestring.sats"
staload "{$LIBS}/result/src/SATS/result.sats"

(* we are working with 3 different types of values in Text*)
#define ASCII 0 (* contains just ASCII text *)
#define UTF8_NFD 1 (* NFD normalized UTF8 sequence *)
#define UTF8 2 (* encoded as non-normalized UTF8 sequence*)
#define TEXT_TYPE_MAX 2

(* this data prop describes the rules of getting text type from the append operations
*)
dataprop TEXT_APPEND( l:int, r:int, t:int) =
  | TEXT_APPEND_ASCII(ASCII, ASCII, ASCII) (* if all the operands are ASCII then the result is ASCII *)
  | { l,r,t: int | max( l,r) == UTF8_NFD} (* if max(l,r) is UTF8_NFD then it's a UTF8_NFD *)
    TEXT_APPEND_UTF8_NFD(l, r, UTF8_NFD)
  | TEXT_APPEND_UTF8(l, r, UTF8) (* otherwise, we have got non-normalized UT8*)

(* text datatype defines UTF-8 encoded string with backing store as bytestring 
*)
vtypedef
  Text_vtype
  ( len: int (* codepoints count *)
  , text_type: int
  , bs_len: int (* bytes count *)
  , bs_offset: int
  , bs_cap: int
  , bs_ucap: int
  , bs_refcnt: int
  , bs_dynamically_allocated: bool
  , bs_base: addr
  ) =
  ( size_t(len) (* codepoints count*)
  , uint8(text_type)
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
  [len, t, bs_len, offset, cap, ucap, refcnt: nat][dynamic:bool][l:addr]
  Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  Text1 =
  [len, bs_len: pos][offset, cap, ucap, refcnt: nat][dynamic:bool][l:agz][t:nat | t <= TEXT_TYPE_MAX]
  Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  TextSH(len:int) =
  {len, bs_len: nat}[offset, cap, ucap, refcnt: nat][dynamic:bool][l:agz][t:nat | t <= TEXT_TYPE_MAX]
  Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l)

vtypedef
  TextNSH(len:int) =
  {len, bs_len: nat}[offset, cap, ucap, refcnt: nat][dynamic:bool][l:addr][t:nat | t <= TEXT_TYPE_MAX]
  Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l)

prfun
  lemma_text_param
  {len,bs_len,offset,cap,ucap,refcnt:nat}{dynamic:bool}{l:addr}{t:nat}
  ( v: !Text_vtype(len, t, bs_len, offset,cap,ucap,refcnt,dynamic,l)
  ):<>
  [ (bs_len >= len)
  ; ( len > 0 && l > null)
  ; ( bs_len > 0 && cap > 0)
  ; (cap > 0 && l > null)
  ; (l > null && bs_len >= 0); bs_len+offset <= cap
  ; offset+bs_len+ucap == cap
  ; (ucap == cap - offset - bs_len || ucap == 0)
  ; t <= TEXT_TYPE_MAX
  ; (t == ASCII && bs_len == len) || (t != ASCII && bs_len != len)
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
       ,  [len:nat][t:nat | t <= TEXT_TYPE_MAX]
          Text_vtype
            ( len
            , t
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
  ):<!wrt>
  #[result:bool]
  bool(result)

(* this is non-consuming version of function, meaning, that i's refcnt will be increamented in case of success.
  This function will allocate new bytestring for purpose of canonical decomposing to be able to normalize bytestring into NFD form.
*)
(* time: O(n), space: O(n*4) *)
fn
  decode_utf80_normalize
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  , result: &Text0? >> result_vtb
       ( result
       ,  [len, bs_len1, cap, ucap:nat][base:agz]
          Text_vtype
            ( len
            , UTF8_NFD
            , bs_len1
            , 0
            , cap
            , ucap
            , 0
            , true
            , base
            )
       , Text0?
       )
  ):<!wrt>
  #[result:bool]
  bool(result)

(* this is non-consuming version of function, meaning, that i's refcnt will be increamented in case of success.
  This function will allocate new bytestring for purpose of canonical decomposing to be able to normalize bytestring into NFD form.
  This is consuming version of this function.
*)
(* time: O(n), space: O(n*4) *)
fn
  decode_utf80_normalizeC
  {bs_len, bs_offset, bs_cap, bs_ucap: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, 0, bs_dynamic, bs_base)
  , result: &Text0? >> result_vtb
       ( result
       ,  [len, bs_len1, cap, ucap:nat][base:agz]
          Text_vtype
            ( len
            , UTF8_NFD
            , bs_len1
            , 0
            , cap
            , ucap
            , 0
            , true
            , base
            )
       , Text0?
       )
  ):<!wrt>
  #[result:bool]
  bool(result)

(* this is non-consuming version of function, meaning, that i's refcnt will be increamented in case of success.
  This function will allocate new bytestring for purpose of canonical decomposing to be able to normalize bytestring into NFD form.
  This version is consuming and might throw exception
*)
(* time: O(n), space: O(n*4) *)
fn
  decode_utf80_normalizeC_exn
  {bs_len, bs_offset, bs_cap, bs_ucap: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, 0, bs_dynamic, bs_base)
  ):<!wrt,!exn>
  [len, bs_len1, cap, ucap:nat][base:agz]
  Text_vtype
    ( len
    , UTF8_NFD
    , bs_len1
    , 0
    , cap
    , ucap
    , 0
    , true
    , base
    )

(* this is consuming version of function, meaning, i have to be non-shared *)
(* time: O(n), space: O(1) *)
fn
  decode_utf80C
  {bs_len, bs_offset, bs_cap, bs_ucap: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, 0, bs_dynamic, bs_base)
  , result: &Text0? >> result_vtb
       ( result
       ,  [len:nat][t:nat | t <= TEXT_TYPE_MAX]
          Text_vtype
            ( len
            , t
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
  ):<!wrt>
  #[result:bool]
  bool(result)

(* this is consuming version of function, meaning, i have to be non-shared *)
(* see test10 for usage example *)
(* time: O(n), space: O(1) *)
fn
  decode_utf80C_exn
  {bs_len, offset, cap, ucap: nat | bs_len > 0; cap > 0}{dynamic:bool}{base:agz}
  ( i: $BS.Bytestring_vtype( bs_len, offset, cap, ucap, 0, dynamic, base)
  ):<!wrt,!exn>
  [len:nat][t:nat | t <= TEXT_TYPE_MAX]
  Text_vtype
    ( len
    , t
    , bs_len
    , offset
    , cap
    , ucap
    , 0
    , dynamic
    , base
    )

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
  ):<!wrt>
  #[result:bool]
  option_vt
    ( [len:nat][t:nat | t <= TEXT_TYPE_MAX]
      Text_vtype
      ( len
      , t
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
  ):<!wrt>
  Option_vt
    ( [len:nat][t:nat | t <= TEXT_TYPE_MAX]
      Text_vtype
      ( len
      , t
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
  {len:int}{bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat }{bs_dynamic:bool}{bs_base:addr}{t:nat | t <= TEXT_TYPE_MAX}
  ( i: !Text_vtype
    ( len
    , t
    , bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , bs_refcnt
    , bs_dynamic
    , bs_base
    )
  ):<>
  size_t( len)

(* O(1) *)
fn
  free_shared_t_bs
  {len:int}{ bs_len, bs_offset, bs_cap, bs_ucap: nat}{bs_dynamic:bool}{bs_base:addr}{t:nat | t <= TEXT_TYPE_MAX}
  {bs_len1, bs_offset1, bs_ucap1, bs_refcnt: nat | bs_refcnt > 0 }
  ( pf: !void (* we need to use this void proof to distinguish operator overloading resolution with free_shared() *)
  | consume: Text_vtype
    ( len
    , t
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
  ):<!wrt>
  void
(* O(1) *)
fn
  free_shared_bs_t
  {len, bs_len, offset, cap, ucap, refcnt:nat | refcnt > 0}{dynamic:bool}{l:addr}{t:nat | t <= TEXT_TYPE_MAX}
  {bs_len1, bs_offset, bs_ucap, bs_refcnt: nat | bs_refcnt > 0}
  ( pf: !void (* we need to use this void proof to distinguish operator overloading resolution with free_shared() *)
  , pf1: !void
  | consume: $BS.Bytestring_vtype
    ( bs_len1
    , bs_offset
    , cap
    , bs_ucap
    , bs_refcnt
    , dynamic
    , l
    )
  , preserve: !Text_vtype
    ( len
    , t
    , bs_len
    , offset
    , cap
    , ucap
    , refcnt
    , dynamic
    , l
    ) >> Text_vtype
    ( len
    , t
    , bs_len
    , offset
    , cap
    , ucap
    , refcnt + bs_refcnt - 2
    , dynamic
    , l
    )
  ):<!wrt>
  void
(* O(1) *)
fn
  free_shared
  {len,len1:int}{ bs_len, bs_offset, bs_cap, bs_ucap, c_refcnt: nat | c_refcnt > 0}{bs_dynamic:bool}{bs_base:addr}{t:nat | t <= TEXT_TYPE_MAX}
  {bs_len1, bs_offset1, bs_ucap1, bs_refcnt: nat | bs_refcnt > 0 }{t1:nat | t <= TEXT_TYPE_MAX}
  ( consume: Text_vtype
    ( len
    , t
    , bs_len
    , bs_offset
    , bs_cap
    , bs_ucap
    , c_refcnt
    , bs_dynamic
    , bs_base
    )
  , preserve: !Text_vtype
    ( len1
    , t1
    , bs_len1
    , bs_offset1
    , bs_cap
    , bs_ucap1
    , bs_refcnt
    , bs_dynamic
    , bs_base
    ) >> Text_vtype
    ( len1
    , t1
    , bs_len1
    , bs_offset1
    , bs_cap
    , bs_ucap1
    , bs_refcnt + c_refcnt - 2
    , bs_dynamic
    , bs_base
    )
  ):<!wrt>
  void

(* O(1) *)
fn
  free
  {len, bs_len, bs_offset, bs_cap, bs_ucap: nat}{bs_dynamic:bool}{bs_base:addr}{t:nat | t <= TEXT_TYPE_MAX}
  ( i: Text_vtype
    ( len
    , t
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
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null][t:nat | t <= TEXT_TYPE_MAX ]
  ( TEXT_APPEND( l_t, r_t, t)
  | Text_vtype
    ( l_len + r_len
    , t
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
  )

(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_tC_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null][t:nat | t <= TEXT_TYPE_MAX]
  ( TEXT_APPEND(l_t, r_t, t)
  | Text_vtype
    ( l_len + r_len
    , t
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
  )
(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_t_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null][t:nat | t <= TEXT_TYPE_MAX]
  ( TEXT_APPEND(l_t, r_t, t)
  | Text_vtype
    ( l_len + r_len
    , t
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
  )
(* returns a Text value, which is the result of appending r to the end of l
  see test3 for reference
*)
(* O(l_bs_len + r_bs_len) *)
fn
  append_tC_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap: nat | l_len > 0; l_bs_len > 0}{l_dynamic:bool}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, 0, l_dynamic, l_p )
  , r: !Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [l:addr | l > null][t:nat | t <= TEXT_TYPE_MAX]
  ( TEXT_APPEND( l_t, r_t, t)
  | Text_vtype
    ( l_len + r_len
    , t
    , l_bs_len + r_bs_len
    , 0 (* offset *)
    , l_bs_len + r_bs_len
    , 0 (* ucap *)
    , 0 (* refcnt*)
    , true
    , l
    )
  )



  (* returns a Text value, which is the result of appending r to the end of l into the unused memory of l's buffer. Such that, l is required to be heap allocated, otherwise SIGSEGV can be thrown *)
(* O(r_bs_len) *)
fn
  grow_tC_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  { l_ucap >= r_bs_len} (* l should have enough unused capacity to store r *)
  ( l: Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, true, l_p)
  , r: !Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
  ):<!wrt>
  [t:nat | t <= TEXT_TYPE_MAX]
  ( TEXT_APPEND( l_t, r_t, t)
  | Text_vtype
      ( l_len + r_len
      , t
      , l_bs_len + r_bs_len
      , l_offset
      , l_cap
      , l_ucap - r_bs_len
      , l_refcnt (* refcnt*)
      , true
      , l_p
      )
  )
(* returns a Text value, which is the result of appending r to the end of l into the unused memory of l's buffer. *)
(* O(r_bs_len) *)
fn
  grow_tC_tC
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_p:agz}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat | r_len > 0; r_bs_len > 0}{r_dynamic:bool}{r_p:agz}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  { l_ucap >= r_bs_len} (* l should have enough unused capacity to store r *)
  ( l: Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, true, l_p)
  , r: Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [t:nat | t <= TEXT_TYPE_MAX]
  ( TEXT_APPEND( l_t ,r_t, t)
  | Text_vtype
      ( l_len + r_len
      , t
      , l_bs_len + r_bs_len
      , l_offset
      , l_cap
      , l_ucap - r_bs_len
      , l_refcnt
      , true
      , l_p
      )
  )

(* returns an empty Text value *)
(* see test5 for usage example *)
(* O(1) *)
fn
  empty
  (
  ):<>
  Text_vtype( 0, ASCII, 0, 0, 0, 0, 0, false, null)

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
  Text_vtype( 0, ASCII, 0, 0, cap, cap, 0, true, l)

(* returns true if given Text is empty *)
(* O(1) *)
fn
  is_empty
  {len, bs_len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}{t: nat | t <= TEXT_TYPE_MAX}
  ( i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, p)
  ):<>
  bool( len == 0)

(* returns true if given Text is not empty *)
(* O(1) *)
fn
  is_not_empty
  {len, bs_len, offset, cap, ucap, refcnt: nat}{dynamic:bool}{p:addr}{t: nat | t <= TEXT_TYPE_MAX}
  ( i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, p)
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
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}{l_t: nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}{r_t: nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
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
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}{l_t: nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt: nat}{r_dynamic:bool}{r_p:addr}{r_t: nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: !Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt, r_dynamic, r_p)
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
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}{l_t: nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
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
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt: nat}{l_dynamic:bool}{l_p:addr}{l_t:nat | l_t <= TEXT_TYPE_MAX}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap: nat}{r_dynamic:bool}{r_p:addr}{r_t:nat | r_t <= TEXT_TYPE_MAX}
  ( l: !Text_vtype( l_len, l_t, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt, l_dynamic, l_p)
  , r: Text_vtype( r_len, r_t, r_bs_len, r_offset, r_cap, r_ucap, 0, r_dynamic, r_p)
  ):<!wrt>
  [ r:bool | (l_len == r_len && not r) || not r == false ]
  bool( r)

(* this function returns how many bytes occupies the first codepoint of bytestring *)
(* time: O(1), space: O(1) *)
fn
  bs_mb_head_bytes
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  ):<!wrt>
  int

(* returns first n units of the Text value
*)
(* time: O(n), space: O(1) *)
fn
  take
  {n, len, bs_len, offset, cap, ucap,refcnt:nat | n <= len}{dynamic:bool}{l:addr}{t:nat | t <= TEXT_TYPE_MAX}
  ( n: size_t(n)
  , i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l) >> Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  [obs_len:nat][ot:nat | t <= TEXT_TYPE_MAX]
  Text_vtype( n, ot, obs_len, offset, cap, 0, 1, dynamic, l)

(* returns Text value without first n units
*)
(* see test8 for usage example *)
(* time: O(n), space: O(1) *)
fn
  drop
  {n, len, bs_len, offset, cap, ucap,refcnt:nat | n <= len}{dynamic:bool}{l:addr}{t:nat | t <= TEXT_TYPE_MAX}
  ( n: size_t(n)
  , i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l) >> Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt + 1, dynamic, l)
  ):<!wrt>
  [obs_len, ooffset:nat ][ot:nat | t <= TEXT_TYPE_MAX]
  Text_vtype( len - n, ot, obs_len, ooffset, cap, 0, 1, dynamic, l)

(* gets bytestring, representing the n'th unit of the text (possibly, multibyte) *)
(* see test9 for usage example *)
(* O(n) *)
fn
  get_at_uint
  {n, len, bs_len, offset, cap, ucap,refcnt:nat | n < len}{dynamic:bool}{l:addr}{t:nat | t <= TEXT_TYPE_MAX}
  ( i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l) >> Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt + 1, dynamic, l)
  , n: size_t(n)
  ):<!wrt>
  [olen, ooffset: nat]
  $BS.Bytestring_vtype( olen, ooffset, cap, 0, 1, dynamic, l)
(* gets bytestring, representing the n'th unit of the text (possibly, multibyte) *)
(* see test9 for usage example *)
(* O(n) *)
fn
  get_at_int
  {n, len, bs_len, offset, cap, ucap,refcnt:nat | n < len}{dynamic:bool}{l:addr}{t: nat | t <= TEXT_TYPE_MAX}
  ( i: !Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt, dynamic, l) >> Text_vtype( len, t, bs_len, offset, cap, ucap, refcnt + 1, dynamic, l)
  , n: int(n)
  ):<!wrt>
  [olen, ooffset: nat]
  $BS.Bytestring_vtype( olen, ooffset, cap, 0, 1, dynamic, l)
