#include "share/atspre_staload.hats"

#define ATS_DYNLOADFLAG 0
#define ATS_PACKNAME "text"
#define ATS_EXTERN_PREFIX "text_"

#define LIBS_targetloc "../libs" (* search path for external libs *)


#include "{$LIBS}/ats-bytestring/HATS/bytestring.hats"
#include "./../HATS/text.hats"
staload "./../SATS/text.sats"
staload "{$LIBS}/result/src/SATS/result.sats"
staload UN = "prelude/SATS/unsafe.sats"

implement free( i) = free bs where {
  val (_, _, bs) = i
}

implement free_shared( consume, preserve) = {
  val (_, _, bs) = consume
  val () = free( bs, preserve)
}

implement length( i) = i.0

extern fn
  u8_mblen
  {sz:nat}{l:agz}
  ( !array_v( uint8, l, sz)
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
      ( !array_v(char, l, sz) >> array_v( uint8, l, sz)
      ):<> void
  }
  val result = g1ofg0( u8_mblen( pf | i_p, i_sz)) (* now get the size of the first codepoint (head) in bytes *)
  prval () = to_char pf  where {
    extern prfn
      to_char
      {l:addr}{sz:nat}
      ( !array_v(uint8, l, sz) >> array_v( char, l, sz)
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
  ):
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
    ):
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
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 0u, $BS.ref_bs_parent i)
      prval () = result_vt_success( result)
      prval () = result_vt_success( i)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 1u, $BS.ref_bs_parent i)
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
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 0u, i)
      prval () = result_vt_success( result)
    }
    | _ => true where {
      val () = result := @(g1ofg0 i_mb_sz, $UN.cast{uint8} 1u, i)
      prval () = result_vt_success( result)
    }
  end
  else false where {
    prval () = opt_unnone( i_mb_sz)
    prval () = result_vt_failure( result)
    val () = free i
  }
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

implement append_t_t( l, r) =
  ( l.0 + r.0 (* the result's length is the sum of both *)
  , max( l.1, r.1) (* if any of l or r is actually utf-8 string, then the result is utf8 as well *)
  , l.2 !+! r.2 (* append bytestrings *)
  )

implement grow_tC_t( l, r) =
  ( l.0 + r.0
  , max(l.1, r.1)
  , l.2 ++! r.2
  ) where {
}

implement grow_tC_tC( l, r) = result where {
  val result = grow_tC_t( l, r)
  val () = free r
}

implement is_empty( i) = i.0 = 0

implement is_not_empty( i) = not (is_empty i)

implement empty() = ( i2sz 0, $UN.cast{uint8} 0, $BS.empty())

implement create( capacity) = ( i2sz 0, $UN.cast{uint8} 0, result) where {
  val result = $BS.create( capacity)
}

%{^
#include "uninorm.h"
%}
typedef uninorm_t = $extype"uninorm_t"
macdef UNINORM_NFD = $extval( uninorm_t, "UNINORM_NFD")

fn
  u8_normcmp
  {n1, n2: nat}
  {s1_p, s2_p, result_p: agz}
  ( s1_pf: !array_v( uint8, s1_p, n1)
  , s2_pf: !array_v( uint8, s2_p, n2)
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
  | max( l.1, r.1) = $UN.cast{uint8} 0 => l.2 = r.2
  (* if one is ascii and another is multibyte, then there is no way they will match *)
  | l.1 <> r.1 => false
  (* if both are multibyte, then we need to normalize both and compare *)
  | _ =>
  let
    extern prfn
      to_bytes
      {l:addr}{sz:nat}
      ( !array_v(char, l, sz) >> array_v( uint8, l, sz)
      ):<> void
    extern prfn
      to_char
      {l:addr}{sz:nat}
      ( !array_v(uint8, l, sz) >> array_v( char, l, sz)
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
