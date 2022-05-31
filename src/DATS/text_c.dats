#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text_"

#define LIBS_targetloc "../libs" (* search path for external libs *)


#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
#include "./../HATS/text.hats"
staload "./../SATS/text.sats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload "{$LIBS}/foldable/src/SATS/foldable.sats"
staload UN = "prelude/SATS/unsafe.sats"

implement free( i) = free bs where {
  val (_, _, bs) = i
}

implement free_shared( consume, preserve) = {
  val (_, _, bs) = consume
  val () = free( bs, preserve.2)
}

implement free_shared_t_bs( pf | consume, preserve) = {
  val (_, _, bs) = consume
  val () = free( bs, preserve)
}
implement free_shared_bs_t( pf0, pf1 | consume, preserve) = {
  val () = free( consume, preserve.2)
}

implement length( i) = i.0

extern fn
  u8_mblen
  {sz:nat}{l:agz}
  ( !array_v( uchar, l, sz)
  | ptr l
  , size_t sz
  ):<>
  int = "ext#"

implement bs_mb_head_bytes( i ) = result where {
  val (pf | i_p, i_sz) = $BS.bs2bytes_ro i
  prval () = to_bytes pf  where {
    extern prfn
      to_bytes
      {l:addr}{sz:nat}
      ( !array_v(char, l, sz) >> array_v( uchar, l, sz)
      ):<> void
  }
  val result = g1ofg0( u8_mblen( pf | i_p, i_sz)) (* now get the size of the first codepoint (head) in bytes *)
  prval () = to_char pf  where {
    extern prfn
      to_char
      {l:addr}{sz:nat}
      ( !array_v(uchar, l, sz) >> array_v( char, l, sz)
      ):<> void
  }
  prval () = $BS.bytes_addback( pf | i)
}

(* time: O(n), space: O(1) *)
fn
  bs_mb_length
  {bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt: nat | bs_len > 0; bs_cap > 0}{bs_dynamic:bool}{bs_base:agz}
  ( i: !$BS.Bytestring_vtype( bs_len, bs_offset, bs_cap, bs_ucap, bs_refcnt, bs_dynamic, bs_base)
  , result: &size_t? >> opt( size_t, b)
  ):<!wrt>
  #[b:bool]
  bool(b) =
let
  fun
    loop
    {len, offset: nat}
    .<len>.
    ( t: &$BS.Bytestring_vtype( len, offset, bs_cap, 0, 1, bs_dynamic, bs_base) >> [olen, ooffset: nat] $BS.Bytestring_vtype( olen, ooffset, bs_cap, 0, 1, bs_dynamic, bs_base)
    , acc: size_t
    , acc_result: &size_t? >> opt( size_t, b)
    ):<!wrt>
    #[b:bool]
    bool(b) =
    let
      val t_sz = length t
    in
      if t_sz = 0
      then true where {
        val () = acc_result := acc
        prval () = opt_some( acc_result)
      }
      else 
      let
        val mblen = g1ofg0( bs_mb_head_bytes t)
      in
        if mblen <= 0
        then false where {
          prval () = opt_none( acc_result)
        }
        else
        let
          val mblen_sz = i2sz mblen (* cast to size_t *)
        in
          if mblen_sz > t_sz
          then false where {
            prval () = opt_none( acc_result)
          }
          else loop( t, acc + 1, acc_result) where {
            val () = t := $BS.dropC( mblen_sz, t)
          }
        end
      end
    end
  var tmp: $BS.Bytestring0
  val () = tmp := $BS.ref_bs_parent i
  var acc: size_t?
  val flag = loop( tmp, i2sz 0, acc)
  val () = free( tmp, i)
in
  if flag
  then flag where {
    prval () = opt_unsome( acc)
    val () = result := acc
    prval () = opt_some( result)
  }
  else flag where {
    prval () = opt_unnone( acc)
    prval () = opt_none( result)
  }
end


implement decode_utf80( i, result) =
let
  val i_sz = length i
  var i_mb_sz: size_t?
in
  if bs_mb_length (i, i_mb_sz) 
  then
  let
    prval () = opt_unsome( i_mb_sz)
  in
    ifcase
    | i_mb_sz < 0 => false where {
      prval () = result_vt_failure( result)
      prval () = result_vt_failure( i)
    }
    | i_mb_sz = i_sz => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uchar} 0u, $BS.ref_bs_parent i)
      prval () = result_vt_success( result)
      prval () = result_vt_success( i)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uchar} 1u, $BS.ref_bs_parent i)
      prval () = result_vt_success( result)
      prval () = result_vt_success( i)
    }
  end
  else false where {
    prval () = opt_unnone( i_mb_sz)
    prval () = result_vt_failure( result)
    prval () = result_vt_failure( i)
  }
end

implement decode_utf80C( i, result) =
let
  val i_sz = length i
  var i_mb_sz: size_t?
in
  if bs_mb_length (i, i_mb_sz) 
  then
  let
    prval () = opt_unsome( i_mb_sz)
  in
    ifcase
    | i_mb_sz < 0 => false where {
      prval () = result_vt_failure( result)
      val () = free i
    }
    | i_mb_sz = i_sz => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uchar} 0u, i)
      prval () = result_vt_success( result)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uchar} 1u, i)
      prval () = result_vt_success( result)
    }
  end
  else false where {
    prval () = opt_unnone( i_mb_sz)
    prval () = result_vt_failure( result)
    val () = free i
  }
end

implement decode_utf80C_exn( i) = result where {
  var result: Text0?
  val code = decode_utf80C( i, result)
  val () = assertlocmsg( code = true, "given bytestring contains invalid UTF8 sequence")
  prval () = result_vt_unsuccess( result)
}

%{^
#include "uninorm.h"
%}
typedef uninorm_t = $extype"uninorm_t"
macdef UNINORM_NFD = $extval( uninorm_t, "UNINORM_NFD")

fn
  u8_normalize
  {s_p, o_p, o_sz_p: agz}{s_sz, o_sz:pos}
  ( pf0: !array_v( uchar, s_p, s_sz)
  , pf1: !array_v( uchar, o_p, o_sz)
  , pf2: !(size_t( o_sz) @ o_sz_p) >>
    result_vb( r_p > null
             , [o_osz: pos | o_osz <= o_sz] size_t( o_osz) @ o_sz_p
             , size_t( o_sz) @ o_sz_p
             )
  | t: uninorm_t
  , s: ptr s_p
  , s_sz: size_t( s_sz)
  , p: ptr o_p
  , p_sz: ptr o_sz_p
  ):<!wrt>
  #[r_p:agez]
  ptr r_p =
let
  val ret = g1ofg0( $extfcall( ptr, "u8_normalize", t, s, s_sz, p, p_sz))
in
  if ptr_is_null ret
  then ret where {
    prval () = result_v_failure( pf2)
  }
  else ret where {
    prval () = result_v_success( pf2)
  }
end

implement decode_utf80_normalize( i, result) =
let
  val (i_pf | i_p, i_sz) = $BS.bs2bytes_ro i
  var o: $BS.Bytestring0?
  val () = o := $BS.create( i_sz * 4)
  val (o_pf | o_p, o_sz) = $BS.bs2unused_bytes_rw o
  var o_sz1: size_t? with o_sz1_pf
  val () = o_sz1 := o_sz

  extern prfn
    to_bytes
    {l:addr}{sz:nat}
    ( !array_v(char, l, sz) >> array_v( uchar, l, sz)
    ):<> void
  extern prfn
    to_char
    {l:addr}{sz:nat}
    ( !array_v(uchar, l, sz) >> array_v( char, l, sz)
    ):<> void

  prval () = to_bytes i_pf
  prval () = to_bytes o_pf
  val o_ptr = u8_normalize( i_pf, o_pf, o_sz1_pf | UNINORM_NFD, i_p, i_sz, o_p, addr@o_sz1)
  prval () = to_char i_pf
  prval () = to_char o_pf
  prval () = $BS.bytes_addback( i_pf | i)
in
  if ptr_is_null o_ptr
  then false where {
    prval () = result_v_unfailure( o_sz1_pf)
    val () = $BS.unused_bytes_addback( o_pf | o, i2sz 0)
    val () = free o
    prval () = result_vt_failure( result)
  }
  else true where {
    prval () = result_v_unsuccess( o_sz1_pf)
    val () = $BS.unused_bytes_addback( o_pf | o, o_sz1)
    val-true = decode_utf80( o, result) (* I don't think, that we should have this check, because I hope, that u8_normalize should have return NULL on error, but it is undefined for u8_normalize *)
    prval () = result_vt_unsuccess( o)
    prval () = result_vt_unsuccess( result)
    val () = free( (), () | o, result)
    prval () = result_vt_success( result)
  }
end

implement decode_utf80_normalizeC( i, result) = res where {
  val res = decode_utf80_normalize( i, result)
  val () = free i
}

implement decode_utf80_normalizeC_exn( i) =
let
   var result: Text0?
   val res = decode_utf80_normalizeC( i, result)
   val () = assertlocmsg( res, "decode_utf80_normalizeC_exn: given bytestring contains invalid UTF8 sequence")
  prval () = result_vt_unsuccess( result)
in
  result
end

implement decode_utf81( i) =
let
  var result: Text0?
in
  if decode_utf80( i, result)
  then Some_vt( result) where {
    prval () = result_vt_unsuccess( result)
  }
  else None_vt() where {
    prval () = result_vt_unfailure( result)
  }
end

implement decode_utf81C( i) =
let
  var result: Text0?
in
  if decode_utf80C( i, result)
  then Some_vt( result) where {
    prval () = result_vt_unsuccess( result)
  }
  else None_vt() where {
    prval () = result_vt_unfailure( result)
  }
end

implement append_tC_tC( l, r) = result where {
  val result = append_t_t( l, r)
  val () = free l
  val () = free r
}
implement append_t_tC( l, r) = result where {
  val result = append_t_t( l, r)
  val () = free r
}
implement append_tC_t( l, r) = result where {
  val result = append_t_t( l, r)
  val () = free l
}

implement append_t_t
  {l_len, l_bs_len, l_offset, l_cap, l_ucap, l_refcnt}{l_dynamic}{l_p}{l_t}
  {r_len, r_bs_len, r_offset, r_cap, r_ucap, r_refcnt}{r_dynamic}{r_p}{r_t}
  ( l, r) =
let
  prval _ = lemma_text_param( l)
  prval _ = lemma_text_param( r)
  val maxl1r1 = max1( l.1, r.1) where {
    fn
      max1
      {l,r:nat}
      ( l: uchar(l)
      , r: uchar(r)
      ):<>
      uchar( max( l, r)) =
      if l > r
      then l
      else r
  }
in
  ifcase
  | maxl1r1 = $UN.cast{uchar(0)} 0 =>
    ( TEXT_APPEND_ASCII()
    | ( l.0 + r.0 (* the result's length is the sum of both *)
      , maxl1r1 (* if any of l or r is actually utf-8 string, then the result is utf8 as well *)
      , l.2 !+! r.2 (* append bytestrings *)
      )
    )
  | maxl1r1 = $UN.cast{uchar(1)} 1 =>
    ( TEXT_APPEND_UTF8_NFD()
    | ( l.0 + r.0 (* the result's length is the sum of both *)
      , maxl1r1 (* if any of l or r is actually utf-8 string, then the result is utf8 as well *)
      , l.2 !+! r.2 (* append bytestrings *)
      )
    )
  | _ =>
    ( TEXT_APPEND_UTF8()
    | ( l.0 + r.0 (* the result's length is the sum of both *)
      , maxl1r1 (* if any of l or r is actually utf-8 string, then the result is utf8 as well *)
      , l.2 !+! r.2 (* append bytestrings *)
      )
    )
end

(* ASCII + ASCII = ASCII
   ASCII + UTF8 = UTF8
   ASCII + UTF8_NFD = UTF8_NFD
   UTF8 + ASCII = UTF8
   UTF8 + UTF8 = UTF8
   UTF8 + UTF8_NFD = UTF8
   UTF8_NFD + ASCII = UTF8_NFD
   UTF8_NFD + UTF8 = UTF8
   UTF8_NFD + UTF8_NFD = UTF8_NFD
*)
implement grow_tC_t( l, r) =
let
  val (len, l1, l_bs) = l
  val maxl1r1 = max1( l1, r.1) where {
    fn
      max1
      {l,r:nat}
      ( l: uchar(l)
      , r: uchar(r)
      ):<>
      uchar( max( l, r)) =
      if l > r
      then l
      else r
  }
in
  ifcase
  | maxl1r1 = $UN.cast{uchar(0)} 0 =>
    ( TEXT_APPEND_ASCII()
    | ( len + r.0
      , maxl1r1
      , l_bs ++! r.2
      )
    )
  | maxl1r1 = $UN.cast{uchar(1)} 1 =>
    ( TEXT_APPEND_UTF8_NFD()
    | ( len + r.0
      , maxl1r1
      , l_bs ++! r.2
      )
    )
  | _ =>
    ( TEXT_APPEND_UTF8()
    | ( len + r.0
      , maxl1r1
      , l_bs ++! r.2
      )
    )
end

implement grow_tC_tC( l, r) = result where {
  val result = grow_tC_t( l, r)
  val () = free r
}

implement is_empty( i) = i.0 = 0

implement is_not_empty( i) = not (is_empty i)

implement empty() = ( i2sz 0, $UN.cast{uchar(0)} 0, $BS.empty())

implement create( capacity) = ( i2sz 0, $UN.cast{uchar(0)} 0, result) where {
  val result = $BS.create( capacity)
}

fn
  u8_normcmp
  {n1, n2: nat}
  {s1_p, s2_p, result_p: agz}
  ( s1_pf: !array_v( uchar, s1_p, n1)
  , s2_pf: !array_v( uchar, s2_p, n2)
  , result_pf: !(int? @ result_p) >>
      result_vb( result == 0
              , int @ result_p
              , int? @ result_p
              )
  | s1: ptr s1_p
  , n1: size_t n1
  , s2: ptr s2_p
  , n2: size_t n2
  , nf: uninorm_t
  , result_p: ptr result_p
  ):<!wrt>
  #[result: int]
  int(result) =
let
  val result = g1ofg0( $extfcall( int, "u8_normcmp", s1, n1, s2, n2, nf, result_p))
in
  if result = 0
  then result where {
    prval () = result_v_success( result_pf)
  }
  else result where {
    prval () = result_v_failure( result_pf)
  }
end

implement eq_t_t( l, r) =
let
  prval _ = $BS.lemma_bytestring_param l.2
  prval _ = $BS.lemma_bytestring_param r.2
in
  ifcase
  | l.0 <> r.0 => false
  (* if both strings are ascii, then just byte-compare *)
  | l.1 = r.1 => l.2 = r.2
  (* if both are multibyte, then we need to normalize both and compare *)
  | _ =>
  let
    extern prfn
      to_bytes
      {l:addr}{sz:nat}
      ( !array_v(char, l, sz) >> array_v( uchar, l, sz)
      ):<> void
    extern prfn
      to_char
      {l:addr}{sz:nat}
      ( !array_v(uchar, l, sz) >> array_v( char, l, sz)
      ):<> void
    var result: int? with result_pf
    val (l_pf | l_p, l_sz) = $BS.bs2bytes_ro l.2
    val (r_pf | r_p, r_sz) = $BS.bs2bytes_ro r.2
    prval () = to_bytes( l_pf)
    prval () = to_bytes( r_pf)
    val zero = u8_normcmp( l_pf, r_pf, result_pf | l_p, l_sz, r_p, r_sz, UNINORM_NFD, addr@ result)
    prval () = to_char( l_pf)
    prval () = to_char( r_pf)
    prval () = $BS.bytes_addback( l_pf | l.2)
    prval () = $BS.bytes_addback( r_pf | r.2)
  in
    if zero = 0
    then
    let
      prval () = result_v_unsuccess( result_pf)
    in
       if result = 0
       then true
       else false
    end
    else false where {
      prval () = result_v_unfailure( result_pf)
    }
  end
end

implement not_eq_t_t( l, r) = not( l == r)

implement eq_t_tC( l, r) = result where {
  val result = l == r
  val () = free r
}

implement not_eq_t_tC( l, r) = result where {
  val result = l != r
  val () = free r
}

implement take( n, i) =
let
  val env = ifold_left<$T.Text0><$BS.Bytestring1>{effwrt}
    ( ($UN.cast{size_t} 0, n)
    , i
    , lam (idx, env, element) =<>
      if idx = env.1
      then (env, false)
      else ( (env.0 + length element, env.1), true)
    )
  val bs_sz = g1ofg0 env.0
in
  if bs_sz > length i.2 (* have to ensure, that result size is within range *)
  then (* this case should not actually happen, but to be total, we have to prove, that we are handling it *)
    ( n
    , i.1 (* we reuse original i here, so no check needed *)
    , $BS.ref_bs_parent i.2
    )
  else
    if bs_sz = n
    then (* we took ASCII-only part, so mark it accordingly *)
      ( n
      , $UN.cast{uchar(0)} 0
      , $BS.take( bs_sz, i.2)
      )
    else
      ( n
      , i.1 (* result is still multibyte text *)
      , $BS.take( bs_sz, i.2)
      )
end

implement drop( n, i) =
let
  val env = ifold_left<$T.Text0><$BS.Bytestring1>{effwrt}
    ( ($UN.cast{size_t} 0, n)
    , i
    , lam (idx, env, element) =<>
      if idx = env.1
      then (env, false)
      else ( (env.0 + length element, env.1), true)
    )
  val bs_sz = g1ofg0 env.0
in
  if bs_sz >= length i.2 (* have to ensure, that result size is within range *)
  then (* this case should not actually happen, but to be total, we have to prove, that we are handling it *)
    ( length i - n
    , $UN.cast{uchar(0)} 0
    , $BS.drop( length i.2, i.2)
    )
  else
  let
    val dropped = $BS.drop( bs_sz, i.2)
    val dropped_len = length i - n
  in
    if dropped_len = length dropped
    then (* we took ASCII-only part, so mark it accordingly *)
      ( dropped_len
      , $UN.cast{uchar(0)} 0
      , dropped
      )
    else
      ( dropped_len
      , i.1 (* result is still multibyte text *)
      , dropped
      )
  end
end

implement get_at_uint( i, n) =
let
  prval () = lemma_text_param i
  val head0 = drop( n, i)
  prval () = lemma_text_param head0
  val head1 = take( i2sz 1, head0)
  val () = free_shared( head0, i)
  val (_, _, bs) = head1 (* disassemble the text value *)
in
  bs
end

implement get_at_int( i, n) = get_at_uint( i, i2sz n)
